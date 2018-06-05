from z3 import *

# for a 8-bit bitvec, to prevent overflow during multiplication/addition, 25 bits must be allocated
# because log2(256)*3 = 8*3 = 24
# and a sum of two 24-bit bitvectors can be 25-bit
a,b,c = BitVecs ('a b c', 25)

s=Solver()

# only 8-bit values are allowed in these 3 bitvectors:
s.add((a&0xfffff00)==0)
s.add((b&0xfffff00)==0)
s.add((c&0xfffff00)==0)

# non-zero values:
s.add(a!=0)
s.add(b!=0)
s.add(c!=0)

# a^3 + b^3 = c^3
s.add(a*a*a + b*b*b == c*c*c)

print s.check()

