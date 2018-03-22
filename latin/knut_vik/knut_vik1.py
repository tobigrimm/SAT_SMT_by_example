from z3 import *

#SIZE=4 # unsat
#SIZE=5 # OK
#SIZE=6 # unsat
SIZE=7 # OK

a=[[Int('%d_%d' % (r,c)) for c in range(SIZE)] for r in range(SIZE)]

s=Solver()

# all numbers must be in 1..SIZE limits
for r in range(SIZE):
    for c in range(SIZE):
        s.add(And(a[r][c]>=1, a[r][c]<=SIZE))

# all numbers in all rows must be distinct:
for r in range(SIZE):
    # expression like s.add(Distinct(a[r][0], a[r][1], ..., a[r][last])) is formed here:
    s.add(Distinct(*[a[r][c] for c in range(SIZE)]))

# ... in all columns as well:
for c in range(SIZE):
    s.add(Distinct(*[a[r][c] for r in range(SIZE)]))

# all (broken) diagonals must also be distinct:
for r in range(SIZE):
    s.add(Distinct(*[a[(r+r2) % SIZE][r2 % SIZE] for r2 in range(SIZE)]))
    # this line of code is the same as previous, but the column is "flipped" horizontally (SIZE-1-column):
    s.add(Distinct(*[a[(r+r2) % SIZE][SIZE-1-(r2 % SIZE)] for r2 in range(SIZE)]))

print s.check()
m=s.model()

for r in range(SIZE):
    for c in range(SIZE):
        print m[a[r][c]].as_long(),
    print ""

