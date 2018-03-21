import operator
from z3 import *

INPUT_SIZE=32
OUTPUT_SIZE=INPUT_SIZE*2

a=BitVec('a', INPUT_SIZE)
b=BitVec('b', INPUT_SIZE)

"""
rows with dots are partial products:

     aaaa
b    ....
b   ....
b  ....
b ....

"""

# partial products
p=[BitVec('p_%d' % i, OUTPUT_SIZE) for i in range(INPUT_SIZE)]

s=Solver()

for i in range(INPUT_SIZE):
    # if there is a bit in b[], assign shifted a[] padded with zeroes at left/right
    # if there is no bit in b[], let p[] be zero

    # Concat() is for glueling together bitvectors (of different widths)
    # BitVecVal() is constant of specific width

    if i==0:
        s.add(p[i] == If((b>>i)&1==1, Concat(BitVecVal(0, OUTPUT_SIZE-i-INPUT_SIZE), a), 0))
    else:
        s.add(p[i] == If((b>>i)&1==1, Concat(BitVecVal(0, OUTPUT_SIZE-i-INPUT_SIZE), a, BitVecVal(0, i)), 0))

# tests

# from http://mathworld.wolfram.com/IrreduciblePolynomial.html
#poly=7 # irreducible
#poly=5 # reducible

# from Colbourn, Dinitz - Handbook of Combinatorial Designs (2ed, 2007), p.809:
#poly=0b10000001001 # irreducible
#poly=0b10000001111 # irreducible

# MSB is always 1 in CRC polynomials, and it's omitted
# but we add it here (leading 1 bit):
poly=0x18005 # CRC-16-IBM, reducible
#poly=0x11021 # CRC-16-CCITT, reducible
#poly=0x1C867 # CRC-16-CDMA2000, irreducible
#poly=0x104c11db7 # CRC-32, irreducible
#poly=0x11EDC6F41 # CRC-32C (Castagnoli), CRC32 x86 instruction, reducible
#poly=0x1741B8CD7 # CRC-32K (Koopman {1,3,28}), reducible
#poly=0x132583499 # CRC-32K2 (Koopman {1,1,30}), reducible
#poly=0x1814141AB # CRC-32Q, reducible

# form expression like s.add(p[0] ^ p[1] ^ ... ^ p[OUTPUT_SIZE-1] == poly)
# replace operator.xor to operator.add to factorize numbers:
s.add(reduce (operator.xor, p)==poly)

# we are not interesting in outputs like these:
s.add(a!=1)
s.add(b!=1)

if s.check()==unsat:
    print "unsat"
    exit(0)

m=s.model()
print "sat, a=0x%x, b=0x%x" % (m[a].as_long(), m[b].as_long())

