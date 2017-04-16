#!/usr/bin/env python
import sys

class Expr:
    def __init__(self,s):
        self.s=s
    
    def convert_to_Expr_if_int(self, n):
        if isinstance(n, int):
            return Expr(str(n))
        if isinstance(n, Expr):
            return n
        raise AssertionError # unsupported type

    def __str__(self):
        return self.s

    def __xor__(self, other):
        return Expr("(" + self.s + "^" + self.convert_to_Expr_if_int(other).s + ")")
    
#BYTES=1
BYTES=8

def crc32(buf):
    #state=[Expr("init_%d" % i) for i in range(32)]
    state=[Expr("1") for i in range(32)]
    for byte in buf:
        for n in range(8):
            bit=byte[n]
            to_taps=bit^state[31]
            state[31]=state[30]
            state[30]=state[29]
            state[29]=state[28]
            state[28]=state[27]
            state[27]=state[26]
            state[26]=state[25]^to_taps
            state[25]=state[24]
            state[24]=state[23]
            state[23]=state[22]^to_taps
            state[22]=state[21]^to_taps
            state[21]=state[20]
            state[20]=state[19]
            state[19]=state[18]
            state[18]=state[17]
            state[17]=state[16]
            state[16]=state[15]^to_taps
            state[15]=state[14]
            state[14]=state[13]
            state[13]=state[12]
            state[12]=state[11]^to_taps
            state[11]=state[10]^to_taps
            state[10]=state[9]^to_taps
            state[9]=state[8]
            state[8]=state[7]^to_taps
            state[7]=state[6]^to_taps
            state[6]=state[5]
            state[5]=state[4]^to_taps
            state[4]=state[3]^to_taps
            state[3]=state[2]
            state[2]=state[1]^to_taps
            state[1]=state[0]^to_taps
            state[0]=to_taps

    for i in range(32):
        #print "state %d=%s" % (i, state[31-i])
        sys.stdout.write ("state %02d: " % i)
        for byte in range(BYTES):
            for bit in range(8):
                s="in_%d_%d" % (byte, bit)
                if str(state[31-i]).count(s) & 1:
                    sys.stdout.write ("*")
                else:
                    sys.stdout.write (" ")
        sys.stdout.write ("\n")

buf=[[Expr("in_%d_%d" % (byte, bit)) for bit in range(8)] for byte in range(BYTES)]
crc32(buf)

