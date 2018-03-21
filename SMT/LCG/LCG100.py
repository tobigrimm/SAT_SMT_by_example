#!/usr/bin/python
from z3 import *

state1 = BitVec('state1', 32)
state2 = BitVec('state2', 32)
state3 = BitVec('state3', 32)
state4 = BitVec('state4', 32)
state5 = BitVec('state5', 32)

s = Solver()

s.add(state2 == state1*214013+2531011)
s.add(state3 == state2*214013+2531011)
s.add(state4 == state3*214013+2531011)
s.add(state5 == state4*214013+2531011)

s.add(URem((state2>>16)&0x7FFF,100)==0)
s.add(URem((state3>>16)&0x7FFF,100)==0)
s.add(URem((state4>>16)&0x7FFF,100)==0)
s.add(URem((state5>>16)&0x7FFF,100)==0)

print(s.check())
print(s.model())

