#!/usr/bin/env python
from z3 import *

s=Solver()

x=Int("x")

dayno=Int("dayno")

s.add(dayno==x/86400)

# 1st constraint:
s.add((dayno+4)%7==5) # must be Friday

# 2nd constraint:
s.add(Or(dayno==13-1,dayno==44-1,dayno==72-1,dayno==103-1,dayno==133-1,dayno==164-1,dayno==194-1,dayno==225-1,dayno==256-1,dayno==286-1,dayno==317-1,dayno==347-1))

s.check()
print s.model()

