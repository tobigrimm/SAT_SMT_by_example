from z3 import *

a,b,c = Ints ('a b c')

s=Solver()

s.add(a!=0)
s.add(b!=0)
s.add(c!=0)

# a^3 + b^3 = c^3
s.add(a*a*a + b*b*b == c*c*c)

print s.check()

