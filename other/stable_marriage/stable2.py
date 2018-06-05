#!/usr/bin/env python

from z3 import *

SIZE=10

# names and preferences has been copypasted from https://rosettacode.org/wiki/Stable_marriage_problem

# males:
abe, bob, col, dan, ed, fred, gav, hal, ian, jon = 0,1,2,3,4,5,6,7,8,9
MenStr=["abe", "bob", "col", "dan", "ed", "fred", "gav", "hal", "ian", "jon"]
# females:
abi, bea, cath, dee, eve, fay, gay, hope, ivy, jan = 0,1,2,3,4,5,6,7,8,9
WomenStr=["abi", "bea", "cath", "dee", "eve", "fay", "gay", "hope", "ivy", "jan"]

# men's preferences. better is at left (at first):
ManPrefer={}
ManPrefer[abe]=[abi, eve, cath, ivy, jan, dee, fay, bea, hope, gay]
ManPrefer[bob]=[cath, hope, abi, dee, eve, fay, bea, jan, ivy, gay]
ManPrefer[col]=[hope, eve, abi, dee, bea, fay, ivy, gay, cath, jan]
ManPrefer[dan]=[ivy, fay, dee, gay, hope, eve, jan, bea, cath, abi]
ManPrefer[ed]=[jan, dee, bea, cath, fay, eve, abi, ivy, hope, gay]
ManPrefer[fred]=[bea, abi, dee, gay, eve, ivy, cath, jan, hope, fay]
ManPrefer[gav]=[gay, eve, ivy, bea, cath, abi, dee, hope, jan, fay]
ManPrefer[hal]=[abi, eve, hope, fay, ivy, cath, jan, bea, gay, dee]
ManPrefer[ian]=[hope, cath, dee, gay, bea, abi, fay, ivy, jan, eve]
ManPrefer[jon]=[abi, fay, jan, gay, eve, bea, dee, cath, ivy, hope]

# women's preferences:
WomanPrefer={}
WomanPrefer[abi]=[bob, fred, jon, gav, ian, abe, dan, ed, col, hal]
WomanPrefer[bea]=[bob, abe, col, fred, gav, dan, ian, ed, jon, hal]
WomanPrefer[cath]=[fred, bob, ed, gav, hal, col, ian, abe, dan, jon]
WomanPrefer[dee]=[fred, jon, col, abe, ian, hal, gav, dan, bob, ed]
WomanPrefer[eve]=[jon, hal, fred, dan, abe, gav, col, ed, ian, bob]
WomanPrefer[fay]=[bob, abe, ed, ian, jon, dan, fred, gav, col, hal]
WomanPrefer[gay]=[jon, gav, hal, fred, bob, abe, col, ed, dan, ian]
WomanPrefer[hope]=[gav, jon, bob, abe, ian, dan, hal, ed, col, fred]
WomanPrefer[ivy]=[ian, col, hal, gav, fred, bob, abe, ed, jon, dan]
WomanPrefer[jan]=[ed, hal, gav, abe, bob, jon, col, ian, fred, dan]

s=Solver()

ManChoice=[Int('ManChoice_%d' % i) for  i in range(SIZE)]
WomanChoice=[Int('WomanChoice_%d' % i) for  i in range(SIZE)]

# all values in ManChoice[]/WomanChoice[] are in 0..9 range:
for i in range(SIZE):
    s.add(And(ManChoice[i]>=0, ManChoice[i]<=9))
    s.add(And(WomanChoice[i]>=0, WomanChoice[i]<=9))

s.add(Distinct(ManChoice))

# "inverted index", make sure all men and women are "connected" to each other, i.e., form pairs.
# FIXME: only work for SIZE=10
for i in range(SIZE):
    s.add(WomanChoice[i]==
        If(ManChoice[0]==i, 0,
        If(ManChoice[1]==i, 1,
        If(ManChoice[2]==i, 2,
        If(ManChoice[3]==i, 3,
        If(ManChoice[4]==i, 4,
        If(ManChoice[5]==i, 5,
        If(ManChoice[6]==i, 6,
        If(ManChoice[7]==i, 7,
        If(ManChoice[8]==i, 8,
        If(ManChoice[9]==i, 9, -1)))))))))))

# this is like ManChoice[] value, but "inverted index". it reflects wife's rating in man's own rating system.
# 0 if he married best women, 1 if there is 1 women who he would prefer (if there is a chance):
ManChoiceInOwnRating=[Int('ManChoiceInOwnRating_%d' % i) for  i in range(SIZE)]
# same for all women:
WomanChoiceInOwnRating=[Int('WomanChoiceInOwnRating_%d' % i) for  i in range(SIZE)]

# set values in "inverted" indices according to values in ManPrefer[]/WomenPrefer[].
# FIXME: only work for SIZE=10
for m in range(SIZE):
    s.add (ManChoiceInOwnRating[m]== 
       If(ManChoice[m]==ManPrefer[m][0],0,
       If(ManChoice[m]==ManPrefer[m][1],1,
       If(ManChoice[m]==ManPrefer[m][2],2,
       If(ManChoice[m]==ManPrefer[m][3],3,
       If(ManChoice[m]==ManPrefer[m][4],4,
       If(ManChoice[m]==ManPrefer[m][5],5,
       If(ManChoice[m]==ManPrefer[m][6],6,
       If(ManChoice[m]==ManPrefer[m][7],7,
       If(ManChoice[m]==ManPrefer[m][8],8,
       If(ManChoice[m]==ManPrefer[m][9],9, -1)))))))))))

for w in range(SIZE):
    s.add (WomanChoiceInOwnRating[w]== 
       If(WomanChoice[w]==WomanPrefer[w][0],0,
       If(WomanChoice[w]==WomanPrefer[w][1],1,
       If(WomanChoice[w]==WomanPrefer[w][2],2,
       If(WomanChoice[w]==WomanPrefer[w][3],3,
       If(WomanChoice[w]==WomanPrefer[w][4],4,
       If(WomanChoice[w]==WomanPrefer[w][5],5,
       If(WomanChoice[w]==WomanPrefer[w][6],6,
       If(WomanChoice[w]==WomanPrefer[w][7],7,
       If(WomanChoice[w]==WomanPrefer[w][8],8,
       If(WomanChoice[w]==WomanPrefer[w][9],9, -1)))))))))))

# the last part is the essence of this script:

# this is 2D bool array. "true" if a (married or already connected) man would prefer another women over his wife.
ManWouldPrefer=[[Bool('ManWouldPrefer_%d_%d' % (m, w)) for w in range(SIZE)] for m in range(SIZE)]
# same for all women:
WomanWouldPrefer=[[Bool('WomanWouldPrefer_%d_%d' % (w, m)) for m in range(SIZE)] for w in range(SIZE)]

# set "true" in ManWouldPrefer[][] table for all women who are better than the wife a man currently has.
# all others can be "false"
# if the man married best women, all entries would be "false"
for m in range(SIZE):
    for w in range(SIZE):
        s.add(ManWouldPrefer[m][w] == (ManPrefer[m].index(w) < ManChoiceInOwnRating[m]))

# do the same for WomanWouldPrefer[][]:
for w in range(SIZE):
    for m in range(SIZE):
        s.add(WomanWouldPrefer[w][m] == (WomanPrefer[w].index(m) < WomanChoiceInOwnRating[w]))

# this is the most important constraint.
# enumerate all possible man/woman pairs
# no pair can exist with both "true" in "mirrored" entries of ManWouldPrefer[][]/WomanWouldPrefer[][].
# we block this by the following constraint: Not(And(x,y)): all x/y values are allowed, except if both are set to 1/true:
for m in range(SIZE):
    for w in range(SIZE):
        s.add(Not(And(ManWouldPrefer[m][w], WomanWouldPrefer[w][m])))

results=[]

# enumerate all possible solutions:
while True:
    if s.check() == sat:
        m = s.model()
        #print m
        results.append(m)
        block = []
        for d in m:
            c=d()
            block.append(c != m[d])
        s.add(Or(block))
    else:
        print "results total=", len(results)
        break

