#!/usr/bin/python
from z3 import *

state1 = BitVec('state1', 32)
state2 = BitVec('state2', 32)
state3 = BitVec('state3', 32)

s = Solver()

s.add(state2 == state1*214013+2531011)
s.add(state3 == state2*214013+2531011)

s.add((state2>>16)&0x7FFF==0)
s.add((state3>>16)&0x7FFF==0)

print(s.check())
print(s.model())

