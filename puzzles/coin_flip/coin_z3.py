from z3 import *
import math, random

SIZE=8
    
# initial state:
total=0
initial=[]
print "initial (random):"
for i in range(SIZE):
    t=random.randint(0,255)
    total=total+bin(t).count("1")
    initial.append(t)
    print "{0:b}".format(t).zfill(SIZE)
print "total=", total
print ""

# population count AKA hamming weight.
# it counts bits:
# FIXME, works only for SIZE=8
def popcnt(a):
    rt=0
    rt=rt+If(a&0x01!=0, 1, 0)
    rt=rt+If(a&0x02!=0, 1, 0)
    rt=rt+If(a&0x04!=0, 1, 0)
    rt=rt+If(a&0x08!=0, 1, 0)
    rt=rt+If(a&0x10!=0, 1, 0)
    rt=rt+If(a&0x20!=0, 1, 0)
    rt=rt+If(a&0x40!=0, 1, 0)
    rt=rt+If(a&0x80!=0, 1, 0)
    return rt

def do_all(STEPS):

    STATES=STEPS+1

    states=[[BitVec('state_%d_row_%d' % (s, r), SIZE) for r in range(SIZE)] for s in range(STATES)]

    # False - horizontal, True - vertical:
    H_or_V=[Bool('H_or_V_%d' % i) for i in range(STEPS)]

    # this is "shared" variable, can hold both and or column:
    row_col=[BitVec('row_col_%d' % i, SIZE) for i in range(STEPS)]

    s=Optimize()

    for i in range(SIZE):
        s.add(states[0][i]==BitVecVal(initial[i], 8))

    # row_col can only have 0b1, 0b01, etc, in 2^n form:    
    for st in range(STEPS):
        s.add(Or(*[row_col[st]==(2**i) for i in range(SIZE)]))

    # this is the most essential part
    for st in range(STEPS):
        # if H_or_V[]==False, all rows are flipped with a value in 2^n form, i.e., a column is flipped
        # column is set by row_col[]:
        t=[]
        for r in range(SIZE):
            t.append(states[st][r] ^ If(H_or_V[st], row_col[st], BitVecVal(0, SIZE)))

        # if H_or_V[]==True, a row is flipped (by XORing by 0xff), and row is choosen by row_cal[]'s value.
        # otherwise, row is XORed by 0, i.e., idle operation.
        for r in range(SIZE):
            s.add(states[st+1][r] == t[r] ^ If(And(Not(H_or_V[st]), row_col[st]==2**r), BitVecVal(0xff, SIZE), BitVecVal(0, SIZE)))

    # find such a solution, for which population count of all rows as small as possible,
    # i.e., there are as many zero bits, as possible:
    # FIXME, works only for SIZE=8
    s.minimize(popcnt(states[STEPS][0])+
        popcnt(states[STEPS][1])+
        popcnt(states[STEPS][2])+
        popcnt(states[STEPS][3])+
        popcnt(states[STEPS][4])+
        popcnt(states[STEPS][5])+
        popcnt(states[STEPS][6])+
        popcnt(states[STEPS][7]))

    if s.check()==unsat:
        return
    m=s.model()

    # print solution:
    for st in range(STATES):
        if st<STEPS:
            if str(m[H_or_V[st]])=="True":
                print "vertical, ", 
            else:
                print "horizontal, ",
            print int(math.log(m[row_col[st]].as_long(), 2))
        if st==STEPS-1:
            total=0
            for r in range(SIZE):
                v=m[states[st][r]].as_long()
                total=total+bin(v).count("1")
                print "{0:b}".format(v).zfill(SIZE)
            print "total=", total
            print ""

for s in range(1, 4+1):
    print "trying %d steps" % s
    #set_option(timeout=3)
    do_all(s)

