import math, operator
from z3 import *

#SIZE=4 # unsat
SIZE=5 # OK
#SIZE=6 # unsat
#SIZE=7 # OK
#SIZE=11 # no answer

a=[[BitVec('%d_%d' % (r,c), SIZE) for c in range(SIZE)] for r in range(SIZE)]

# 0b11111 for SIZE=5:
mask=2**SIZE-1

s=Solver()

# all numbers must have form 2^n, like 1, 2, 4, 8, 16, etc.
# we add contraint like Or(a[r][c]==2, a[r][c]==4, ..., a[r][c]==32, ...)
for r in range(SIZE):
    for c in range(SIZE):
        s.add(Or(*[a[r][c]==(2**i) for i in range(SIZE)]))

# all numbers in all rows must be distinct:
for r in range(SIZE):
    # expression like s,add(a[r][0] | a[r][1] | ... | a[r][last] == mask) is formed here:
    s.add(reduce(operator.ior, [a[r][c] for c in range(SIZE)])==mask)

# ... in all columns as well:
for c in range(SIZE):
    # expression like s,add(a[0][c] | a[1][c] | ... | a[last][c] == mask) is formed here:
    s.add(reduce(operator.ior, [a[r][c] for r in range(SIZE)])==mask)

# for all (broken) diagonals:
for r in range(SIZE):
    s.add(reduce(operator.ior, [a[(r+r2) % SIZE][r2 % SIZE] for r2 in range(SIZE)])==mask)
    # this line of code is the same as previous, but the column is "flipped" horizontally (SIZE-1-column):
    s.add(reduce(operator.ior, [a[(r+r2) % SIZE][SIZE-1-(r2 % SIZE)] for r2 in range(SIZE)])==mask)

print s.check()
m=s.model()

for r in range(SIZE):
    for c in range(SIZE):
        print int(math.log(m[a[r][c]].as_long(),2)),
    print ""

