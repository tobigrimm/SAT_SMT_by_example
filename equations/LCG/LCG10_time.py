#!/usr/bin/python
from z3 import *

state1 = BitVec('state1', 32)
state2 = BitVec('state2', 32)
state3 = BitVec('state3', 32)
state4 = BitVec('state4', 32)
state5 = BitVec('state5', 32)
state6 = BitVec('state6', 32)
state7 = BitVec('state7', 32)

s = Solver()

s.add(state1>=1512499124) # Tue Dec  5 20:38:44 EET 2017
s.add(state1<=1513036800) # Tue Dec 12 02:00:00 EET 2017

s.add(state2 == state1*214013+2531011)
s.add(state3 == state2*214013+2531011)
s.add(state4 == state3*214013+2531011)
s.add(state5 == state4*214013+2531011)
s.add(state6 == state5*214013+2531011)
s.add(state7 == state6*214013+2531011)

c = BitVec('c', 32)

s.add(URem((state2>>16)&0x7FFF,10)==c)
s.add(URem((state3>>16)&0x7FFF,10)==c)
s.add(URem((state4>>16)&0x7FFF,10)==c)
s.add(URem((state5>>16)&0x7FFF,10)==c)
s.add(URem((state6>>16)&0x7FFF,10)==c)
s.add(URem((state7>>16)&0x7FFF,10)==c)

print(s.check())
print(s.model())

