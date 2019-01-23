from z3 import *

# 5 inputs, so 1<<5=32 posible combinations:
TOTAL_TESTS=1<<5

# number of gates and/or gates' outputs:
OUTPUTS_TOTAL=15

OUT_Z1, OUT_Z2, OUT_Z3, OUT_Z4, OUT_Z5, OUT_A2, OUT_A3, OUT_B1, OUT_B2, OUT_B3, OUT_C1, OUT_C2, OUT_P, OUT_Q, OUT_S = range(OUTPUTS_TOTAL)

out_false_if={}
out_true_if={}

# enumerate all possible inputs
for i in range(1<<5):
    x1=i&1
    x2=(i>>1)&1
    y1=(i>>2)&1
    y2=(i>>3)&1
    y3=(i>>4)&1

    outs={}

    # simulate the circuit:
    outs[OUT_Z1]=y1&x1
    outs[OUT_B1]=y1&x2
    outs[OUT_A2]=x1&y2
    outs[OUT_B2]=y2&x2
    outs[OUT_A3]=x1&y3
    outs[OUT_B3]=y3&x2

    outs[OUT_P]=outs[OUT_A3] & outs[OUT_B2]
    outs[OUT_S]=outs[OUT_A3] ^ outs[OUT_B2]
    outs[OUT_C1]=outs[OUT_A2] & outs[OUT_B1]
    outs[OUT_Z2]=outs[OUT_A2] ^ outs[OUT_B1]

    outs[OUT_Q]=outs[OUT_S] & outs[OUT_C1]
    outs[OUT_Z3]=outs[OUT_S] ^ outs[OUT_C1]

    outs[OUT_C2]=outs[OUT_P] | outs[OUT_Q]

    outs[OUT_Z5]=outs[OUT_B3] & outs[OUT_C2]
    outs[OUT_Z4]=outs[OUT_B3] ^ outs[OUT_C2]

    inputs=(y3, y2, y1, x2, x1)
    print "inputs:", inputs, "outputs of all gates:", outs

    for o in range(OUTPUTS_TOTAL):
        if outs[o]==0:
            if o not in out_false_if:
                out_false_if[o]=[]
            out_false_if[o].append(i)
        else:
            if o not in out_true_if:
                out_true_if[o]=[]
            out_true_if[o].append(i)

for o in range(OUTPUTS_TOTAL):
    print "output #%d" % o
    print "    false if:", out_false_if[o]
    print "    true if:", out_true_if[o]

s=Solver()

# if the test will be picked or not:
tests=[Int('test_%d' % (t)) for t in range(TOTAL_TESTS)]

# this is optimization problem:
opt = Optimize()

# a test may be picked (1) or not (0):
for t in tests:
    opt.add(Or(t==0, t==1))

# this generates expression like (tests[0]==1 OR tests[1]==1 OR tests[X]==1):
for o in range(OUTPUTS_TOTAL):
    opt.add(Or(*[tests[i]==1 for i in out_false_if[o]]))
    opt.add(Or(*[tests[i]==1 for i in out_true_if[o]]))

# minimize number of tests:
opt.minimize(Sum(*tests))

print (opt.check())
m=opt.model()

for i in range(TOTAL_TESTS):
    t=m[tests[i]].as_long()
    if t==1:
        print format(i, '05b')

