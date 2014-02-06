#
# provided by wmspanel.com team
# Author: Alex Pokotilo
# Contact: support@wmspanel.com
#

require 'socket'

def getBSLBFBit(byte, offset)
  (byte & (1 << (7-offset))) != 0 ? 1 : 0
end

def getInteger(byte, offset, size)
  result = byte >> (8 - offset - size)
  case size
    when 1
      result = result & 0b1
    when 2
      result = result & 0b11
    when 3
      result = result & 0b111
    when 4
      result = result & 0b1111
    when 5
      result = result & 0b11111
    when 6
      result = result & 0b111111
    when 7
      result = result & 0b1111111
  end
end

MPEG_STREAM_TYPES_AVC = 0x1B
MPEG_STREAM_TYPES_13818_7 = 0x0F

PES_VIDEO_STREAM_BEGIN = 0b1110_0000
PES_VIDEO_STREAM_END   = 0b1110_1111

PES_AUDIO_STREAM_BEGIN = 0b1100_0000
PES_AUDIO_STREAM_END   = 0b1101_1111

DECIRED_CHUNK_DURATION = 6 # seconds  . should be configurable in production per stream
MAX_CACHED_CHUNKS = 10 # should be configurable in production per stream

class Mpeg2tsStream
  def initialize
    @pat = nil
    @pmt = nil
    @currentblock = []
    @es_info = {}
    @stream_cc = {}
    @pcr_pid = -1
    @program_map_pid = -1
    @chunks = []
    @chunks_durations = []
    @last_cur_chunk = @cur_chunk = []

    @cur_chunk_pts = 0
    @cur_chunk_start_pts = -1
    @skip_chunk_write = true
    @chunks_processed = 0
    @slave_stream_pts  = 0
    @combined_chunks = File.open ("combined_chunks.ts") , 'wb'
  end

  def shiftBufferToNextPossibleStartMark
    if @cur_chunk_start_pts > 0 && @cur_chunk_pts > @cur_chunk_start_pts && @cur_chunk.size != 0
      dumpCurrentChunk()
      @chunks << @cur_chunk
      @chunks_durations <<  @cur_chunk_pts - @cur_chunk_start_pts

      if MAX_CACHED_CHUNKS < @chunks.size
        p "chunk discarded #{@chunks.delete_at(0).size}"
        @chunks_durations.delete_at(0)
      end
    end

    @cur_chunk_pts = 0
    @cur_chunk_start_pts = -1
    @last_cur_chunk = @cur_chunk = []
    @slave_stream_pts = -1
    @stream_cc = {}

    @pat = nil
    @pmt = nil
    @es_info = {}
    @pcr_pid = -1
    @program_map_pid = -1
    @skip_chunk_write = true

    newCurrentblock = []

    @currentblock.delete_at(0) # lets exclude first element from processing

    @currentblock.each do |b|
      if newCurrentblock.size == 0 &&  b != 0x47
        next
      end
      newCurrentblock <<  b
    end
    @currentblock = newCurrentblock

    p "reset"
  end

  def isMpeg2tsblock
    b = @currentblock
    return false unless b[0] == 0x47

    transport_error_indicator    =  getBSLBFBit b[1], 0
    @payload_unit_start_indicator = getBSLBFBit(b[1], 1) == 0x01
    transport_priority           = getBSLBFBit b[1], 2
    @cur_pid                     = getInteger(b[1], 3, 5) << 8
    @cur_pid+= b[2]
    scrambling_control           = getInteger(b[3], 0, 2)
    @adaptation_field_control    = getInteger(b[3], 2, 2) > 0x01
    continuity_counter           = getInteger(b[3], 4, 4)

    if (transport_error_indicator + transport_priority + scrambling_control) != 0
      return false
    end

    return true

  end

  def checkPAT
    shiftBufferToNextPossibleStartMark() and return false unless isMpeg2tsblock()
    return false unless @cur_pid == 0 # PAT pid is 0. it's not a PAT

    if @pat && @pat.slice(5..-1) == @currentblock.slice(5..-1)
      return true
    end


    if @adaptation_field_control || !@payload_unit_start_indicator
      shiftBufferToNextPossibleStartMark() # previous check checked this is a PAT. but it's not let's reset current buffer
      return false
    end

    buffer = @currentblock

    table_id = buffer[5]
    unless table_id == 0 && getBSLBFBit(buffer[6], 0) == 0x1 && getBSLBFBit(buffer[6], 1) == 0x0 && getInteger(buffer[6], 2,2) == 0b11 && getInteger(buffer[6], 4, 2) == 0x00
      shiftBufferToNextPossibleStartMark() # previous check checked this is a PAT. but it's not let's reset current buffer
      return false
    end

    section_length = getInteger(buffer[6], 6, 2) << 8
    section_length+= buffer[7]
    section_number = buffer[11]
    last_section_number = buffer[12]

    unless (section_number+last_section_number) == 0
      shiftBufferToNextPossibleStartMark() # previous check checked this is a PAT. but it's not let's reset current buffer
      return false
    end

    programs_length = section_length - 9 # here means all unnecessary fields sizes after section_length field including CRC32
                                      # field

    unless programs_length % 4 == 0
      shiftBufferToNextPossibleStartMark() # previous check checked this is a PAT. but it's not let's reset current buffer
      return false
    end

    programs_count = programs_length / 4
    unless programs_count == 1
      shiftBufferToNextPossibleStartMark() # previous check checked this is a PAT. but it's not let's reset current buffer
      return false
    end

    program_number = (buffer[13] << 8) + (buffer[14])

    unless program_number == 1
      shiftBufferToNextPossibleStartMark() # previous check checked this is a PAT. but it's not let's reset current buffer
      return false
    end

    @program_map_pid = getInteger(buffer[15], 3, 5) << 8
    @program_map_pid += buffer[16]

    @pat = @currentblock
    p "PAT"
  end

  def checkPMT
    shiftBufferToNextPossibleStartMark() and return false unless isMpeg2tsblock()
    return false unless @cur_pid == @program_map_pid # it's not a PMT

    if @pmt && @pmt.slice(5..-1) == @currentblock.slice(5..-1)
      return true
    end

    unless @payload_unit_start_indicator
      shiftBufferToNextPossibleStartMark() # previous check checked this is a PMT. but it's not let's reset current buffer
      return false
    end

    buffer = @currentblock
    table_id = buffer[5]

    unless table_id == 2
      shiftBufferToNextPossibleStartMark() # previous check checked this is a PMT. but it's not let's reset current buffer
      return false
    end

    section_syntax_indicator = getBSLBFBit(buffer[6], 0)

    section_length = getInteger(buffer[6], 6, 2) << 8
    section_length+= buffer[7]

    @pcr_pid = getInteger(buffer[13], 3, 5) << 8
    @pcr_pid+= buffer[14]

    max_offset = section_length + 3 - 4 + 5 # + 2 is offset of section_length -4 CRC size + 5(is 4 byte of mpegts header + 1 pointer offset byte)
    program_info_length = getInteger(buffer[15], 6, 2) << 8
    program_info_length+= buffer[16]
    offset = 17

    if program_info_length > 0
      initial_offset = offset
      descriptor_tag = buffer[offset];    offset+=1
      descriptor_length = buffer[offset];    offset+=1
      metadata_application_format = buffer[offset] * 0x100 + buffer[offset +1]; offset+=2

      unless metadata_application_format== 0xFFFF
        shiftBufferToNextPossibleStartMark() # previous check checked this is a PMT. but it's not let's reset current buffer
        return false
      end

      metadata_application_format_identifier = buffer[offset] * 0x1000000 + buffer[offset+1] * 0x10000 + buffer[offset+2] * 0x100 + buffer[offset+3]; offset+=4


      offset= initial_offset + program_info_length
    end

    while offset + 5 <= max_offset # 5 is minimum-size program description section(without description)
      stream_type = buffer[offset]; offset+=1
      elementary_pid = getInteger(buffer[offset], 3, 5) << 8; offset+=1
      elementary_pid += buffer[offset]; offset+=1
      es_info_length = getInteger(buffer[offset], 6, 2) << 8; offset+=1
      es_info_length+= buffer[offset]; offset+=1

      if stream_type == MPEG_STREAM_TYPES_AVC || stream_type == MPEG_STREAM_TYPES_13818_7
        @es_info[elementary_pid] = stream_type
      end

      offset+= es_info_length
    end

    @pmt = @currentblock
    p "PMT"
    return true
  end
  def dumpCurrentChunk
    hls_chunk = (@pat + @pmt + @last_cur_chunk).flatten.pack('C*')
    File.open ("c_#{@chunks_processed}.ts") , 'wb' do |file|
      file.write(hls_chunk)
    end
    @combined_chunks.write(hls_chunk)
    @chunks_processed+=1
  end
  def cacheBuffer(pts, random_access_indicator)
    if @skip_chunk_write
      unless random_access_indicator && @payload_unit_start_indicator && @cur_pid == @pcr_pid
        return
      end
      @skip_chunk_write = false
      @cur_chunk_start_pts = pts
    end

    if @cur_pid != @pcr_pid && pts != -1
      @slave_stream_pts = pts
    end

    if random_access_indicator && @payload_unit_start_indicator && @cur_pid == @pcr_pid
      delta = pts - @cur_chunk_start_pts
      if delta < 0
        shiftBufferToNextPossibleStartMark
        return
      end

      chunk_duration = delta / 90000

      if chunk_duration >= DECIRED_CHUNK_DURATION
        p "chunk created, packets=#{@cur_chunk.size}, duration=#{((pts - @cur_chunk_start_pts)* 1.0)/90000}"
        @chunks << @cur_chunk
        @chunks_durations <<  pts - @cur_chunk_start_pts
        @last_cur_chunk = @cur_chunk

        @stream_cc[@pcr_pid] = 0

        if @es_info.size == 1
          @stream_cc[0] = 0 # 0 i pid for PAT
          @stream_cc[@program_map_pid] = 0
          dumpCurrentChunk()
        end
        @cur_chunk = []

        if MAX_CACHED_CHUNKS < @chunks.size
          p "chunk discarded #{@chunks.delete_at(0).size}"
          @chunks_durations.delete_at(0)
        end

        @cur_chunk_start_pts = pts
      end
    end

    if @es_info.size == 2 && @cur_pid != @pcr_pid && !@last_cur_chunk.equal?(@cur_chunk) && @slave_stream_pts >= @cur_chunk_start_pts && @payload_unit_start_indicator && random_access_indicator
      dumpCurrentChunk()
      @stream_cc[0] = 0 # 0 i pid for PAT
      @stream_cc[@cur_pid] = 0
      @stream_cc[@program_map_pid] = 0

      @last_cur_chunk = @cur_chunk
    end

    @stream_cc[@cur_pid] = 0 unless @stream_cc[@cur_pid]

    cc = @currentblock[3]
    cc = (cc & 0xF0) | @stream_cc[@cur_pid]
    @currentblock[3] = cc


    @stream_cc[@cur_pid]+= 1
    @stream_cc[@cur_pid] = 0 if @stream_cc[@cur_pid] == 16

    if @cur_pid != @pcr_pid && !@last_cur_chunk.equal?(@cur_chunk)
      @last_cur_chunk << @currentblock   # need to decide what to do in case we cannot split this chunk but there are too many blocks already there
    else
      @cur_chunk << @currentblock   # need to decide what to do in case we cannot split this chunk but there are too many blocks already there
    end

    @cur_chunk_pts = pts if pts >= 0 && @cur_chunk_pts < pts
  end

  def processCurrentBlock
    shiftBufferToNextPossibleStartMark() and return false unless isMpeg2tsblock()

    if !@es_info[@cur_pid]
      return false# I don't know what's this. let's skip it
    end

    offset = 4
    b = @currentblock

    random_access_indicator = false
    pts = -1

    pcr_program_clock_reference_base = 0

    if @adaptation_field_control
      adaptation_field_length = b[offset]
      offset+=1

      if adaptation_field_length != 0
        discontinuity_indicator = getBSLBFBit(b[offset], 0)  > 0
        random_access_indicator = getBSLBFBit(b[offset], 1)  > 0
        elementary_stream_priority_indicator = getBSLBFBit(b[offset], 2) > 0
        pcr_flag = getBSLBFBit(b[offset], 3)  > 0
        opcr_flag = getBSLBFBit(b[offset], 4)  > 0
        splicing_point_flag =getBSLBFBit(b[offset], 5)  > 0
        transport_private_data_flag = getBSLBFBit(b[offset], 6)  > 0
        adaptation_field_extension_flag = getBSLBFBit(b[offset], 7)  > 0

        if pcr_flag
          pcr_program_clock_reference_base = b[offset + 1] * 0x1000000 + b[offset + 2] * 0x10000 + b[offset + 3] * 0x100 + b[offset + 4]
          pcr_program_clock_reference_base = pcr_program_clock_reference_base << 1
          pcr_program_clock_reference_base+= getBSLBFBit(b[offset + 5], 0)
          pcr_program_clock_reference_extension = ((getBSLBFBit b[offset + 5], 7) << 8) + b[offset + 6]
        end
      end
      offset+= adaptation_field_length
    end
    if offset > 188
      shiftBufferToNextPossibleStartMark()
      return false
    end

    if offset == 188 && @payload_unit_start_indicator
      shiftBufferToNextPossibleStartMark()
      return false
    end

    if @payload_unit_start_indicator
      packet_start_code_prefix = b[offset] * 0x10000 + b[offset + 1] * 0x100 + b[offset + 2]

      unless packet_start_code_prefix == 0x1
        shiftBufferToNextPossibleStartMark()
        return false
      end

      stream_id = b[offset + 3]

      unless ( (stream_id>= PES_VIDEO_STREAM_BEGIN && stream_id<= PES_VIDEO_STREAM_END) || (stream_id>= PES_AUDIO_STREAM_BEGIN && stream_id<= PES_AUDIO_STREAM_END))
        shiftBufferToNextPossibleStartMark()
        return false
      end

      # see Table 2-21 – PES packet
      #'10' 2 bslbf
      unless 0b10 == getInteger(b[offset + 6], 0, 2)
        shiftBufferToNextPossibleStartMark()
        return false
      end

      #copyright 1 bslbf                      ====IGNORED=====
      #original_or_copy 1 bslbf               ====IGNORED=====
      #PTS_DTS_flags 2 bslbf
      pts_dts_flags = getInteger(b[offset + 7], 0, 2)

      #PTS_DTS flag value  == 1is forbidet
      if 0x01 == pts_dts_flags
        shiftBufferToNextPossibleStartMark()
        return false
      end

      # pes_header_data_length = b[offset + 8]

      if pts_dts_flags > 0
        #    '0011' 4 bslbf
        unless pts_dts_flags == getInteger(b[offset + 9], 0, 4)
          shiftBufferToNextPossibleStartMark()
          return false
        end

        #    PTS [32..30] 3 bslbf
        pts = getInteger(b[offset + 9], 4, 3) << 29
        #    marker_bit 1 bslbf
        #    PTS [29..15] 15 bslbf
        pts = pts | (b[offset + 10] * 0x100 + (getInteger(b[offset + 11], 0, 7) << 1) )  << 14
        #    marker_bit 1 bslbf
        #    PTS [14..0] 15 bslbf
        pts = pts | ((b[offset + 12] * 0x100 + (getInteger(b[offset + 13], 0, 7) << 1)) >> 1)
        #    marker_bit 1 bslbf
        # we can ignore DTS as we use pts only
      else
        shiftBufferToNextPossibleStartMark()
        return false
      end
    end
    cacheBuffer(pts, random_access_indicator)
  end

  def process buffer
    buffer.each do |b|

     @currentblock << b

     if @currentblock.size == 188
      if !@pat
        checkPAT()
      elsif
        if !@pmt
          checkPMT()
        elsif
          # even though we have PAT and PMT table there tables may be presented in the stream and we should not add them to the resulting stream
          if !checkPAT() && !checkPMT
            processCurrentBlock()
          end
        end
      end
     end

     if @currentblock.size == 188
       @currentblock = []
     end
    end
  end
end


stream = Mpeg2tsStream.new

u2 = UDPSocket.new
#just call to start testing
#ffmpeg -re -i D:\home\mpeg4dumper\samples\sample_video.mp4 -an -vcodec copy -bsf h264_mp4toannexb -f mpegts udp://127.0.0.1:2000

u2.bind("127.0.0.1", 2000)

File.open (ARGV[1] ? ARGV[1] : 'incomming.ts') , 'wb' do |file|
  while(true) do
    buffer = u2.recvfrom(1500)[0]
    file.write buffer
    b = buffer.unpack 'C*'
    stream.process(b)
  end
end