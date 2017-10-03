from z3 import *

# my own SMT- and Z3-related functions

# dennis(a)yurichev, 2017

# G=list of tuples. each tuple is edge between two vertices
# each number is vertex
# total=number of vertices
# limit=colors limit
# return: list, color for each vertex
def color_graph_using_Z3(G, total, limit):
    colors=[Int('colors_%d' % p) for p in range(total)]

    s=Solver()

    for i in G:
        s.add(colors[i[0]]!=colors[i[1]])

    # limit:
    for i in range(total):
        s.add(And(colors[i]>=0, colors[i]<limit))

    assert s.check()==sat
    m=s.model()
    # get solution and return it:
    return [m[colors[p]].as_long() for p in range(total)]

