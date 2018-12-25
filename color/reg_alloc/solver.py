from z3 import *

def attempt(colors):

    v=[Int('v%d' % i) for i in range(18)]

    s=Solver()

    for i in range(18):
        s.add(And(v[i]>=0, v[i]<colors))

    # a bit redundant, but that is not an issue:
    s.add(Distinct(v[1], v[2], v[3], v[4]))
    s.add(Distinct(v[1], v[2], v[3], v[4], v[7]))
    s.add(Distinct(v[1], v[2], v[3], v[4], v[5], v[7]))
    s.add(Distinct(v[1], v[2], v[3], v[4], v[5], v[7], v[9]))
    s.add(Distinct(v[1], v[2], v[3], v[4], v[5], v[7], v[8], v[9]))
    s.add(Distinct(v[1], v[2], v[3], v[4], v[5], v[7], v[8], v[9], v[14]))
    s.add(Distinct(v[1], v[2], v[3], v[4], v[5], v[7], v[8], v[9], v[11], v[14]))
    s.add(Distinct(v[1], v[2], v[3], v[4], v[5], v[7], v[8], v[9], v[12], v[14]))
    s.add(Distinct(v[1], v[2], v[3], v[4], v[5], v[7], v[8], v[9], v[14], v[15]))
    s.add(Distinct(v[1], v[2], v[3], v[4], v[5], v[7], v[9], v[14], v[15]))
    s.add(Distinct(v[1], v[2], v[3], v[4], v[5], v[7], v[9], v[14]))
    s.add(Distinct(v[1], v[2], v[3], v[4], v[5], v[7], v[14]))
    s.add(Distinct(v[1], v[2], v[3], v[4]))
    s.add(Distinct(v[1], v[2], v[3], v[4], v[6]))
    s.add(Distinct(v[1], v[2], v[3], v[4], v[6], v[16]))
    s.add(Distinct(v[1], v[2], v[3], v[4], v[6], v[10], v[16]))
    s.add(Distinct(v[1], v[2], v[3], v[4], v[6], v[10], v[13], v[16]))
    s.add(Distinct(v[1], v[2], v[4], v[6], v[10], v[13], v[16]))
    s.add(Distinct(v[1], v[2], v[4], v[6], v[10], v[16]))
    s.add(Distinct(v[1], v[4], v[6], v[10], v[16]))
    s.add(Distinct(v[1], v[4], v[10], v[16]))
    s.add(Distinct(v[1], v[4], v[10]))
    s.add(Distinct(v[1], v[10]))

    registers=["RDI", "RSI", "RDX", "RCX", "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15"]
    # first 4 variables are function arguments and they are always linked to rdi/rsi/rdx/rcx:
    s.add(v[1]==0)
    s.add(v[2]==1)
    s.add(v[3]==2)
    s.add(v[4]==3)

    if s.check()==sat:
        print "* colors=", colors
        m=s.model()
        for i in range(1, 17):
            print "v%d=%s" % (i, registers[m[v[i]].as_long()])

for colors in range(12, 0, -1):
    attempt(colors)

