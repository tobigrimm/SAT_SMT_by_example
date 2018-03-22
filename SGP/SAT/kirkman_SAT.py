#!/usr/bin/env python3

import SAT_lib
import itertools, math

PERSONS, DAYS, GROUPS = 12, 11, 6

s=SAT_lib.SAT_lib(False)

# each element - group for each person and each day:
tbl=[[s.alloc_BV(GROUPS) for day in range(DAYS)] for person in range(PERSONS)]

def chr_to_n (c):
    return ord(c)-ord('A')

# A must play B on day 1, G on day 3, and H on day 6.
# A/B, day 1:
s.fix_BV_EQ(tbl[chr_to_n('A')][0], tbl[chr_to_n('B')][0])
# A/G, day 3:
s.fix_BV_EQ(tbl[chr_to_n('A')][2], tbl[chr_to_n('G')][2])
# A/H, day 5:
s.fix_BV_EQ(tbl[chr_to_n('A')][4], tbl[chr_to_n('H')][4])

# F must play I on day 2 and J on day 5.
s.fix_BV_EQ(tbl[chr_to_n('F')][1], tbl[chr_to_n('I')][1])
s.fix_BV_EQ(tbl[chr_to_n('F')][4], tbl[chr_to_n('J')][4])

# K must play H on day 9 and E on day 11.
s.fix_BV_EQ(tbl[chr_to_n('K')][8], tbl[chr_to_n('H')][8])
s.fix_BV_EQ(tbl[chr_to_n('K')][10], tbl[chr_to_n('E')][10])

# L must play E on day 8 and B on day 9.
s.fix_BV_EQ(tbl[chr_to_n('L')][7], tbl[chr_to_n('E')][7])
s.fix_BV_EQ(tbl[chr_to_n('L')][8], tbl[chr_to_n('B')][8])

# H must play I on day 10 and L on day 11.
s.fix_BV_EQ(tbl[chr_to_n('H')][9], tbl[chr_to_n('I')][9])
s.fix_BV_EQ(tbl[chr_to_n('H')][10], tbl[chr_to_n('L')][10])

for person in range(PERSONS):
    for day in range(DAYS):
        s.make_one_hot(tbl[person][day])

# enumerate all variables
# we add Or(pair1!=0, pair2!=0) constraint, so two non-zero variables couldn't be present,
# but both zero variables in pair is OK, one non-zero and one zero variable is also OK:
def only_one_must_be_zero(lst):
    for pair in itertools.combinations(lst, r=2):
        s.OR_always([s.BV_not_zero(pair[0]), s.BV_not_zero(pair[1])])
    # at least one variable must be zero:
    s.OR_always([s.BV_zero(l) for l in lst])

# get two arrays of variables XORed. one element of this new array must be zero:
def only_one_in_pair_can_be_equal(l1, l2):
    assert len(l1)==len(l2)
    only_one_must_be_zero([s.BV_XOR(l1[i], l2[i]) for i in range(len(l1))])

# enumerate all possible pairs:
for pair in itertools.combinations(range(PERSONS), r=2):
    only_one_in_pair_can_be_equal (tbl[pair[0]], tbl[pair[1]])

assert s.solve()

print ("group for each person:")
print ("person: "+"".join([chr(ord('A')+i)+" " for i in range(PERSONS)]))
for day in range(DAYS):
    t=("day=%2d: " % day)
    for person in range(PERSONS):
        t=t+str(int(math.log(s.get_val_from_solution(tbl[person][day]),2)))+" "
    print (t)

def persons_in_group(day, group):
    rt=""
    for person in range(PERSONS):
        if int(math.log(s.get_val_from_solution(tbl[person][day]),2))==group:
            rt=rt+chr(ord('A')+person)
    return rt

print ("")
print ("persons grouped:")
for day in range(DAYS):
    t=("day=%2d: " % day)
    for group in range(GROUPS):
        t=t+persons_in_group(day, group)+" "
    print (t)

