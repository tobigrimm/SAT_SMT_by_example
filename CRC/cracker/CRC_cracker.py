#!/usr/bin/env python

from z3 import *
import struct

# knobs:

# CRC-16 on https://www.lammertbies.nl/comm/info/crc-calculation.html
#width=16
#samples=["\x01", "\x02"]
#must_be=[0xC0C1, 0xC181]
#sample_len=1

# CRC-16 (Modbus) on https://www.lammertbies.nl/comm/info/crc-calculation.html
#width=16
#samples=["\x01", "\x02"]
#must_be=[0x807E, 0x813E]
#sample_len=1

# CRC-16-CCITT, Kermit on https://www.lammertbies.nl/comm/info/crc-calculation.html
#width=16
#samples=["\x01", "\x02"]
#must_be=[0x8911, 0x1223]
#sample_len=1

width=32
samples=["\x01", "\x02"]
must_be=[0xA505DF1B, 0x3C0C8EA1]
sample_len=1

# crc64_1.c:
#width=64
#samples=["\x01", "\x02"]
#must_be=[0x28d250b0f0900abe, 0x6c9fd98969f81a9d]
#sample_len=1

# crc64_2.c (redis):
#width=64
#samples=["\x01", "\x02"]
#must_be=[0x7ad870c830358979, 0xf5b0e190606b12f2]
#sample_len=1

# crc64_3.c:
#width=64
#samples=["\x01", "\x02"]
#must_be=[0xb32e4cbe03a75f6f, 0xf4843657a840a05b]
#sample_len=1

# http://www.unit-conversion.info/texttools/crc/
#width=32
#samples=["0","1"]
#must_be=[0xf4dbdf21, 0x83dcefb7]
#sample_len=1

# recipe-259177-1.py, CRC-64-ISO
#width=64
#samples=["\x01", "\x02"]
#must_be=[0x01B0000000000000, 0x0360000000000000]
#sample_len=1

# recipe-259177-1.py, CRC-64-ISO
#width=64
#samples=["\x01"]
#must_be=[0x01B0000000000000]
#sample_len=1

#width=32
#samples=["12","ab"]
#must_be=[0x4F5344CD, 0x9E83486D]
#sample_len=2

def swap_endianness_16(val):
    return struct.unpack("<H", struct.pack(">H", val))[0]

def swap_endianness_32(val):
    return struct.unpack("<I", struct.pack(">I", val))[0]

def swap_endianness_64(val):
    return struct.unpack("<Q", struct.pack(">Q", val))[0]

def swap_endianness(width, val):
    if width==64:
        return swap_endianness_64(val)
    if width==32:
        return swap_endianness_32(val)
    if width==16:
        return swap_endianness_16(val)
    raise AssertionError

mask=2**width-1
poly=BitVec('poly', width)

# states[sample][0][8] is an initial state
# ...
# states[sample][i][0] is a state where it was already XORed with input bit
# states[sample][i][1] ... where the 1th shift/XOR operation has been done
# states[sample][i][8] ... where the 8th shift/XOR operation has been done
# ...
# states[sample][sample_len][8] - final state

states=[[[BitVec('state_%d_%d_%d' % (sample, i, bit), width) for bit in range(8+1)] for i in range(sample_len+1)] for sample in range(len(samples))]
s=Solver()

def invert(val):
    return ~val & mask

for sample in range(len(samples)):
    # initial state can be either zero or -1:
    s.add(Or(states[sample][0][8]==mask, states[sample][0][8]==0))

    # implement basic CRC algorithm
    for i in range(sample_len):
        s.add(states[sample][i+1][0] == states[sample][i][8] ^ ord(samples[sample][i]))

        for bit in range(8):
            # LShR() is logical shift, while >> is arithmetical shift, we use the first:
            s.add(states[sample][i+1][bit+1] == LShR(states[sample][i+1][bit],1) ^ If(states[sample][i+1][bit]&1==1, poly, 0))

    # final state must be equial to one of these:
    s.add(Or(
	states[sample][sample_len][8]==must_be[sample],
	states[sample][sample_len][8]==invert(must_be[sample]),
	states[sample][sample_len][8]==swap_endianness(width, must_be[sample]),
	states[sample][sample_len][8]==invert(swap_endianness(width, must_be[sample]))))

# get all possible results:
results=[]
while True:
    if s.check() == sat:
        m = s.model()
        # what final state was?
        if m[states[0][sample_len][8]].as_long()==must_be[0]:
            outparams="XORout=0"
        elif invert(m[states[0][sample_len][8]].as_long())==must_be[0]:
            outparams="XORout=-1"
        elif m[states[0][sample_len][8]].as_long()==swap_endianness(width, must_be[0]):
            outparams="XORout==0, ReflectOut=true"
        elif invert(m[states[0][sample_len][8]].as_long())==swap_endianness(width, must_be[0]):
            outparams="XORout=-1, ReflectOut=true"
        else:
            raise AssertionError

        print "poly=0x%x, init=0x%x, %s" % (m[poly].as_long(), m[states[0][0][8]].as_long(), outparams)

        results.append(m)
        block = []
        for d in m:
            c=d()
            block.append(c != m[d])
        s.add(Or(block))
    else:
        print "total results", len(results)
        break

