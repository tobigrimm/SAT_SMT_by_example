#!/usr/bin/env python

from z3 import *
import copy, random

width=32

poly=BitVec('poly', width)

s=Solver()

no_call=0

def CRC(_input, poly):
    # make each variable name unique
    # no_call (number of call) increments at each call to CRC() function
    global no_call
    states=[[BitVec('state_%d_%d_%d' % (no_call, i, bit), width) for bit in range(8+1)] for i in range(len(_input)+1)]
    no_call=no_call+1
    # initial state is always 0:
    s.add(Or(states[0][8]==0))

    for i in range(len(_input)):
        s.add(states[i+1][0] == states[i][8] ^ _input[i])

        for bit in range(8):
            s.add(states[i+1][bit+1] == LShR(states[i+1][bit],1) ^ If(states[i+1][bit]&1==1, poly, 0))

    return states[len(_input)][8]

# generate 32 random samples:
for i in range(32):
    print "pair",i
    # each sample has random size 1..32
    buf1=bytearray(os.urandom(random.randrange(32)+1))
    buf2=copy.deepcopy(buf1)
    # flip 1, 2 or 3 random bits in second sample:
    for bits in range(1,random.randrange(3)+2):
        # get random position and bit to flip:
        pos=random.randrange(0, len(buf2))
        to_flip=1<<random.randrange(8)
        print "  pos=", pos, "bit=",to_flip
        # flip random bit at random position:
        buf2[pos]=buf2[pos]^to_flip

    # original sample and sample with 1..3 random bits flipped.
    # their hashes must be different:
    s.add(CRC(buf1, poly)!=CRC(buf2, poly))

# get all possible results:
results=[]
while True:
    if s.check() == sat:
        m = s.model()
        print "poly=0x%x" % (m[poly].as_long())
        results.append(m)
        block = []
        for d in m:
            c=d()
            block.append(c != m[d])
        s.add(Or(block))
    else:
        print "total results", len(results)
        break

