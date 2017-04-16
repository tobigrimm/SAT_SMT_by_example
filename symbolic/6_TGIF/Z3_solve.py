#!/usr/bin/env python
from z3 import *

s=Solver()

x=Int("x")

s.add(((x/86400)+4)%7==5)

s.check()
print s.model()

