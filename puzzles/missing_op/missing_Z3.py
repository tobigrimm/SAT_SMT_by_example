from z3 import *

CONST=1234
TOTAL=9

# prepare a list in form: [(1,"1"),(2,"2"),(3,"3")...]
# rationale: enum_ordered() yields both expression tree and expression as a string...
input_values=[]
for i in range(TOTAL):
    input_values.append((i+1, str(i+1)))

OPS=TOTAL-1

ops=[Int('op_%d' % i) for i in range(OPS)]

# this is a hack... operation number. resetting after each tree:
n=-1

# select operation...
def op(l, r, n):
    return If(ops[n]==0, l+r,
        If(ops[n]==1, l-r,
        If(ops[n]==2, l*r,
        0))) # default

# enumerate all possible ordered binary search trees
# copypasted from https://stackoverflow.com/questions/14900693/enumerate-all-full-labeled-binary-tree
# this generator yields both expression and string

# expression may have form like (please note, many constants are optimized/folded):

# If(op_1 == 0,
#    1 +
#    If(op_0 == 0, 5, If(op_0 == 1, -1, If(op_0 == 2, 6, 0))),
#    If(op_1 == 1,
#       1 -
#       If(op_0 == 0,
#          5,
#          If(op_0 == 1, -1, If(op_0 == 2, 6, 0))),
#       If(op_1 == 2,
#          1*
#          If(op_0 == 0,
#             5,
#             If(op_0 == 1, -1, If(op_0 == 2, 6, 0))),
#          0)))

# string is like "(1 op1 (2 op0 3))", opX substring will be replaced by operation name after (-, +, *)

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
    s=Solver()
    # operations in 0..2 range...
    for i in range(OPS):
        s.add(And(ops[i]>=0, ops[i]<=2))
    s.add(tree[0]==CONST)
    if s.check()==sat:
        m=s.model()
        tmp=tree[1]
        for i in range(OPS):
            op_s=["+", "-", "*"][m[ops[i]].as_long()]
            tmp=tmp.replace("op"+str(i), op_s)
        print tmp, "=", eval(tmp)
    n=-1

