from z3 import *

COUPLES=3

# a pair each men and women related to:
men=[Int('men_%d' % i) for i in range(COUPLES)]
women=[Int('women_%d' % i) for i in range(COUPLES)]

# men and women are placed around table like this:

# m m m
#  w w w

# i.e., women[0] is placed between men[0] and men[1]
# the last women[COUPLES-1] is between men[COUPLES-1] and men[0] (wrapping)

s=Solver()
s.add(Distinct(men))
s.add(Distinct(women))

[s.add(And(men[i]>=0, men[i]<COUPLES)) for i in range (COUPLES)]
[s.add(And(women[i]>=0, women[i]<COUPLES)) for i in range (COUPLES)]

# a pair, each woman belong to, cannot be the same as men's located at left and right.
# "% COUPLES" is wrapping, so that the last woman is between the last man and the first man.
for i in range(COUPLES):
    s.add(And(women[i]!=men[i], women[i]!=men[(i+1) % COUPLES]))

def print_model(m):
    print "  men",
    for i in range(COUPLES):
        print m[men[i]],
    print ""

    print "women ",

    for i in range(COUPLES):
        print m[women[i]],
    print ""
    print ""

results=[]

# enumerate all possible solutions:
while True:
    if s.check() == sat:
        m = s.model()
        print_model(m)
        results.append(m)
        block = []
        for d in m:
            c=d()
            block.append(c != m[d])
        s.add(Or(block))
    else:
        print "results total=", len(results)
        print "however, according to https://oeis.org/A059375 :", len(results)*2
        break

