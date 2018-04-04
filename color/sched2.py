from z3 import *

# 16 peoples, 4 groups

PERSONS=16
GROUPS=4

s=Solver()

person=[Int('person_%d' % i) for i in range(PERSONS)]

# each person must belong to some group in 0..GROUPS range:
for i in range(PERSONS):
    s.add(And(person[i]>=0, person[i]<GROUPS))

# each pair of persons can't be in the same group, because they hate each other.
# IOW, we add an edge between vertices.
s.add(person[0] != person[7])
s.add(person[0] != person[8])
s.add(person[0] != person[9])
s.add(person[2] != person[9])
s.add(person[9] != person[14])
s.add(person[11] != person[15])
s.add(person[11] != person[1])
s.add(person[11] != person[2])
s.add(person[11] != person[9])
s.add(person[10] != person[1])

persons_in_group=[Int('persons_in_group_%d' % i) for i in range(GROUPS)]

def count_persons_in_group(g):
    """
    Form expression like:

    If(person_0 == g, 1, 0) +
    If(person_1 == g, 1, 0) +
    If(person_2 == g, 1, 0) +
    ...
    If(person_15 == g, 1, 0)

    """
    return Sum(*[If(person[i]==g, 1, 0) for i in range(PERSONS)])

# each group must have 4 persons:
for g in range(GROUPS):
    s.add(count_persons_in_group(g)==4)

assert s.check()==sat
m=s.model()

groups={}
for i in range(PERSONS):
    g=m[person[i]].as_long()
    if g not in groups:
        groups[g]=[]
    groups[g].append(i)

for g in groups:
    print "group %d, persons:" % g, groups[g]

