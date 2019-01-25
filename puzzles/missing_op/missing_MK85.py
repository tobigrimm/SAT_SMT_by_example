from MK85 import *

n=-1

CONST=13

#TOTAL=9
TOTAL=7

BIT_WIDTH=8

s=MK85(verbose=0)

input_values=[]
for i in range(TOTAL):
    input_values.append((s.BitVecConst(i+1, BIT_WIDTH), str(i+1)))

OPS=TOTAL-1

ops=[s.BitVec('op_%d' % i,2) for i in range(OPS)]

for i in range(OPS):
    s.add(And(ops[i]>=0, ops[i]<=2))

def op(l, r, n):
    return s.If(ops[n]==s.BitVecConst(0, 2), l+r,
        s.If(ops[n]==s.BitVecConst(1, 2), l-r,
        s.If(ops[n]==s.BitVecConst(2, 2), l*r,
            s.BitVecConst(0, BIT_WIDTH))))

def enum_ordered(labels):
    global n
    if len(labels) == 1:
        yield (labels[0][0], labels[0][1])
    else:
        for i in range(1, len(labels)):
            for left in enum_ordered(labels[:i]):
                for right in enum_ordered(labels[i:]):
                    n=n+1
                    yield (op(left[0], right[0], n), "("+left[1]+" op"+str(n)+" "+right[1]+")")

for tree in enum_ordered(input_values):
    s.add(tree[0]==CONST)

    for i in range(OPS):
        s.add(ops[i]!=3)

    if s.check():
        m=s.model()
        #print "sat", tree[1]
        tmp=tree[1]
        for i in range(OPS):
            op_s=["+", "-", "*"][m['op_%d' % i]]
            tmp=tmp.replace("op"+str(i), op_s)
        print tmp, "=", eval(tmp)
        # show only first solution...
        exit(0)

