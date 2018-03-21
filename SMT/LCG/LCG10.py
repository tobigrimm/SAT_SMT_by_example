#!/usr/bin/python
from z3 import *

state1 = BitVec('state1', 32)
state2 = BitVec('state2', 32)
state3 = BitVec('state3', 32)
state4 = BitVec('state4', 32)
state5 = BitVec('state5', 32)
state6 = BitVec('state6', 32)
state7 = BitVec('state7', 32)
state8 = BitVec('state8', 32)
state9 = BitVec('state9', 32)

s = Solver()

s.add(state2 == state1*214013+2531011)
s.add(state3 == state2*214013+2531011)
s.add(state4 == state3*214013+2531011)
s.add(state5 == state4*214013+2531011)
s.add(state6 == state5*214013+2531011)
s.add(state7 == state6*214013+2531011)
s.add(state8 == state7*214013+2531011)
s.add(state9 == state8*214013+2531011)

s.add(URem((state2>>16)&0x7FFF,10)==0)
s.add(URem((state3>>16)&0x7FFF,10)==0)
s.add(URem((state4>>16)&0x7FFF,10)==0)
s.add(URem((state5>>16)&0x7FFF,10)==0)
s.add(URem((state6>>16)&0x7FFF,10)==0)
s.add(URem((state7>>16)&0x7FFF,10)==0)
s.add(URem((state8>>16)&0x7FFF,10)==0)
s.add(URem((state9>>16)&0x7FFF,10)==0)

print(s.check())
print(s.model())

