from MK85 import *

TOTAL=8

s=MK85()

order=[s.BitVec(("%d" % i), 4) for i in range(TOTAL)]

s.add(s.Distinct(order))

for i in range(TOTAL):
    s.add(And(order[i]>=0, order[i]<TOTAL))

s.add(order[5]<order[1])

s.add(order[3]<order[4])
s.add(order[3]<order[0])

s.add(order[7]<order[0])
s.add(order[7]<order[1])

s.add(order[1]<order[2])
s.add(order[1]<order[4])
s.add(order[1]<order[6])

s.add(order[0]<order[6])

print s.check()

m=s.model()

order_to_print=[None]*(TOTAL)
for i in range(TOTAL):
    order_to_print[m[str(i)]]=i

print order_to_print

