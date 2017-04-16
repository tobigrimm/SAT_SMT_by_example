#!/usr/bin/env python
from z3 import *

s=Solver()

x=BitVec("x",32)

a=1103515245
c=12345
s.add((((x*a)+c)>>16)&32767==4583)
s.add((((((x*a)+c)*a)+c)>>16)&32767==16304)
#s.add((((((((x*a)+c)*a)+c)*a)+c)>>16)&32767==14440)
#s.add((((((((((x*a)+c)*a)+c)*a)+c)*a)+c)>>16)&32767==32315)

s.check()
print s.model()

