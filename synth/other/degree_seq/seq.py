# "The degree sequence problem is the problem of finding some or all graphs with 
# the degree sequence being a given non-increasing sequence of positive integers."
# ( https://en.wikipedia.org/wiki/Degree_(graph_theory) )

from z3 import *
import subprocess

BV_WIDTH=8

# from https://en.wikipedia.org/wiki/Degree_(graph_theory)
#seq=[3, 2, 2, 2, 2, 1, 1, 1]

# from "Pearls in Graph Theory":
#seq=[6,5,5,4,3,3,2,2,2]
#seq=[6,6,6,6,4,3,3,0] # not graphical
#seq=[3,2,1,1,1,1,1]

seq=[8,8,7,7,6,6,4,3,2,1,1,1] # https://math.stackexchange.com/questions/1074651/check-if-sequence-is-graphic-8-8-7-7-6-6-4-3-2-1-1-1

#seq=[1,1]
#seq=[2,2,2]

vertices=len(seq)

if (sum(seq) & 1) == 1:
    print "not a graphical sequence"
    exit(0)

edges=sum(seq)/2
print "edges=", edges

# for each edge, edges_begin[] and edges_end[] pair defines a vertex numbers, which they connect:
edges_begin=[BitVec('edges_begin_%d' % i, BV_WIDTH) for i in range(edges)]
edges_end=[BitVec('edges_end_%d' % i, BV_WIDTH) for i in range(edges)]

# how many times an element encountered in array[]?
def count_elements (array, e):
    rt=[]
    for a in array:
        rt.append(If(a==e, 1, 0))
    return Sum(rt)

s=Solver()

for v in range(vertices):
    #print "vertex %d must be present %d times" % (v, seq[v])
    s.add(count_elements(edges_begin+edges_end, v)==seq[v])

for i in range(edges):
    # no loops must be present
    s.add(edges_begin[i]!=edges_end[i])

    # this is not a multiple graph
    # probably, this is hackish... we say here that each pair of elements (edges_begin[].edges_end[])
    # (where dot is concatenation operation) must not repeat in the arrays, nor in a swapped way
    # this is why edges_[] variables has BitVec type...
    # this can be implemented in other way: a value of edges_begin[]*100+edges_end[] must not appear twice...
    for j in range(edges):
        if i==j:
            continue
        s.add(Concat(edges_begin[i], edges_end[i]) != Concat(edges_begin[j], edges_end[j]))
        s.add(Concat(edges_begin[i], edges_end[i]) != Concat(edges_end[j], edges_begin[j]))

gv_no=0

def print_model(m):
    global gv_no
    gv_no=gv_no+1

    print "edges_begin/edges_end:"
    for i in range(edges):
        print "%d - %d" % (m[edges_begin[i]].as_long(), m[edges_end[i]].as_long())

    f=open(str(gv_no)+".gv", "w")
    f.write("graph G {\n")
    for i in range(edges):
        f.write ("\t%d -- %d;\n" % (m[edges_begin[i]].as_long(), m[edges_end[i]].as_long()))
    f.write("}\n")
    f.close()
    # run graphviz:
    cmd='dot -Tpng '+str(gv_no)+'.gv -o '+str(gv_no)+'.png'
    print "running", cmd
    os.system(cmd)

# enumerate all possible solutions:
results=[]
#while True:
for i in range(10): # 10 results
    if s.check() == sat:
        m = s.model()
        print_model(m)
        #exit(0)
        results.append(m)
        block = []
        for d in m:
            c=d()
            block.append(c != m[d])
        s.add(Or(block))
    else:
        print "results total=", len(results)
        if len(results)==0:
            print "not a graphical sequence"
        break

