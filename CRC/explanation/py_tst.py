import zlib
print "00 00 00 00", hex(zlib.crc32(b'\x00\x00\x00\x00') & 0xffffffff)
print "00 00 00 01", hex(zlib.crc32(b'\x00\x00\x00\x01') & 0xffffffff)
print "10 00 00 00", hex(zlib.crc32(b'\x10\x00\x00\x00') & 0xffffffff)
print "12 34 56 78", hex(zlib.crc32(b'\x12\x34\x56\x78') & 0xffffffff)
print "ff ff ff ff", hex(zlib.crc32(b'\xff\xff\xff\xff') & 0xffffffff)

