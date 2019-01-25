from z3 import *

# https://ocaml.org/learn/tutorials/99problems.html
#rows=[[3],[2,1],[3,2],[2,2],[6],[1,5],[6],[1],[2]]
#cols=[[1,2],[3,1],[1,5],[7,1],[5],[3],[4],[3]]

# https://ocaml.org/learn/tutorials/99problems.html
#rows= [[14], [1,1], [7,1], [3,3], [2,3,2], [2,3,2], [1,3,6,1,1], [1,8,2,1], [1,4,6,1], [1,3,2,5,1,1], [1,5,1], [2,2], [2,1,1,1,2], [6,5,3], [12]]
#cols= [[7], [2,2], [2,2], [2,1,1,1,1], [1,2,4,2], [1,1,4,2], [1,1,2,3], [1,1,3,2], [1,1,1,2,2,1], [1,1,5,1,2], [1,1,7,2], [1,6,3], [1,1,3,2], [1,4,3], [1,3,1], [1,2,2], [2,1,1,1,1], [2,2], [2,2], [7]]

# https://en.wikipedia.org/wiki/File:Nonogram_wiki.svg
rows=[[8,7,5,7], [5,4,3,3], [3,3,2,3], [4,3,2,2], [3,3,2,2], [3,4,2,2], [4,5,2], [3,5,1], [4,3,2], [3,4,2], [4,4,2], [3,6,2], [3,2,3,1], [4,3,4,2], [3,2,3,2], [6,5], [4,5], [3,3], [3,3], [1,1]]
cols=[[1], [1], [2], [4], [7], [9], [2,8], [1,8], [8], [1,9], [2,7], [3,4], [6,4], [8,5], [1,11], [1,7], [8], [1,4,8], [6,8], [4,7], [2,4], [1,4], [5], [1,4], [1,5], [7], [5], [3], [1], [1]]

# http://puzzlygame.com/nonogram/11/
#rows=[[12], [1,2,1,2], [6,6], [1,1,1,2], [6,6], [3,2,1,2], [5,2,6], [2,3,2,1,2], [3,3,2,1,2], [3,4,2,1,2], [3,2,2,1,2], [7,2,1,2], [7,2,1,2], [5,2,6], [5,2,1,2], [3,2,6], [6,1,2], [1,1,6], [6,1,2], [12]]
#cols=[[5], [9], [11], [4,7], [2,6,6,1], [1,1,1,4,4,1,2], [1,1,2,6,2,2], [1,1,3,2,4,2], [1,3,3,4,4], [3,6,2], [2,2,1], [1,1], [3,3], [1,4,4,1], [1,1,1,8,1,1,1], [1,1,1,1,1,1,1,1], [3,1,1,1,1,3], [6,6], [14], [8]]

# http://puzzlygame.com/nonogram/24/
#rows=[[4], [1,8,1], [3,11,3], [3,14,4], [4,22], [1,4,22], [28], [27], [3,11,8], [9,9], [8,8], [7,8], [2,1,7], [2,6], [3,5], [2,4], [4], [2], [2], [2], [2], [2], [2], [2], [2]]
#cols=[[2], [3], [4], [1,2], [4], [5], [7], [3,5], [1,5], [7], [7], [9], [11], [10,2], [11,2], [12,2,2], [9,3], [8,4,2], [15,2], [17,2], [19], [18], [15], [12], [9], [7], [4], [3], [3], [2], [3], [2], [3], [2], [2]]

# http://puzzlygame.com/nonogram/792/
#rows=[[2],[4],[2,2],[2,1],[1,1,2,2],[1,4,2,2],[2,1,1,2],[4,2,2],[1,3,2,2,2,4,4], [1,1,1,2,4,2,1,1,1,1],[1,1,5,2,2,2,1,1,1,1],[2,2,1,1,2,2,2,4,4], [1,2,3,2,3],[2,1,2,26],[2,1,2,2,1],[4,2,1,4,1,4],[1,2,1,1,1,1,1,5,4], [2,1,6,1,1,1,1,4],[2,1,2,2,1,5,4],[2,1,1,1,1,1,1,1,1,1,1,2],[2,1,1,1,1,5,4], [2,1,8,1,4],[2,1,1,1,1,4],[2,1,1,1,1,4],[35]]
#cols=[[1,2,3,1,1,1],[1,2,1,1,3,1],[4,1,2,10],[2,3,2,11], [2,1,2,1,1,1],[1,1,2,1,1,1,1],[3,6,1],[3,2,1,1], [3,1,1],[12],[2,1],[3,4,1],[2,1,3,4],[2,1,1,1,1,1,1], [2,1,1,1,1,1],[2,1,1,1,1,1],[2,1,1,1,1,1,1],[2,1,3,4],[3,4,1], [2,1],[14],[2,1,1],[2,1,1],[2,1,5,1],[2,1,1,1,1,1],[2,1,5,1], [2,4,1,1,1,1,1],[2,1,1,1,5,1],[2,1,1,1,1], [2,4,1,1],[2,1,1],[2,2,4,1,10],[2,2,1,1,1,4,5],[2,1,1,1,10],[2,4,1,10]]

# http://puzzlygame.com/nonogram/561/
#rows=[[13,1,1,1,13], [1,2,1,1,2,2,2,1,2,1,1,2,1], [1,9,2,2,1,9,1], [35], [1,1,1,1], [1,1,3,3,3,3,3,2,1,1], [5,2,3,3,3,3,4,5], [1,1], [3,3,3,3], [1,3,2,17,2,3,1], [1,2,17,2,1], [1,3,2,1,1,1,1,2,3,1], [1,3,2,1,1,9,1,1,2,3,1], [1,3,2,3,1,1,1,3,2,3,1], [1,3,2,3,1,1,1,3,2,3,1], [1,3,2,2,1,1,1,3,3,1], [1,3,2,2,1,1,10,1], [1,3,1,9,1,3,3,1], [1,3,2,1,2,1,10,1], [1,2,3,1,3,5,4,1], [1,18,4,3,1], [1,20,3,2,1], [1,20,4,3,1], [1,1,1,1,1,1], [4,3,6,3,15]]
#cols=[[7,15,1], [1,1,1,1,1], [1,1,1,2,9,2,1], [1,1,1,1,9,2,1], [7,2,8,3], [4,1,5], [1,2,12,4,1], [4,2,8,7], [1,2,1,6], [4,2,7,1,3,1], [1,2,1,2,3,1,3,1], [4,2,6,2,3,1], [4,1,2,7,1], [1,2,2,4,1,3,1], [4,1,2,1,1,3,1], [3,2,2,1,1,3], [1,1,2,1,8], [4,2,2,5,5,1], [3,1,2,1,6], [1,2,2,1,3], [4,1,2,1,3,1],[1,2,2,7,3,1], [4,1,2,1], [4,2,14,1], [1,2,1,2,10,1], [4,2,14,1], [1,2,1,1,3,3], [4,2,6,1,2,1], [1,2,10,1,1,1], [4,1,1,2,1], [7,2,10,3], [1,1,1,1,12,1], [1,1,1,2,12,1], [1,1,1,1,1], [7,15,1]]
 
WIDTH=len(cols)
HEIGHT=len(rows)

s=Solver()

# part I, for all rows:
row_islands=[[BitVec('row_islands_%d_%d' % (j, i), WIDTH) for i in range(len(rows[j]))] for j in range(HEIGHT)]
row_island_shift=[[BitVec('row_island_shift_%d_%d' % (j, i), WIDTH) for i in range(len(rows[j]))] for j in range(HEIGHT)]
# this is a bitvector representing final image, for all rows:
row_merged_islands=[BitVec('row_merged_islands_%d' % j, WIDTH) for j in range(HEIGHT)]

for j in range(HEIGHT):
    q=rows[j]
    for i in range(len(q)):
        s.add(row_island_shift[j][i] >= 0)
        s.add(row_island_shift[j][i] <= WIDTH-q[i])
        s.add(row_islands[j][i]==(2**q[i]-1) << row_island_shift[j][i])

    # must be an empty cell(s) between islands:
    for i in range(len(q)-1):
        s.add(row_island_shift[j][i+1] > row_island_shift[j][i]+q[i])

    s.add(row_island_shift[j][len(q)-1]<WIDTH)

    # OR all islands into one:
    expr=row_islands[j][0]
    for i in range(len(q)-1):
        expr=expr | row_islands[j][i+1]
    s.add(row_merged_islands[j]==expr)

# similar part, for all columns:
col_islands=[[BitVec('col_islands_%d_%d' % (j, i), HEIGHT) for i in range(len(cols[j]))] for j in range(WIDTH)]
col_island_shift=[[BitVec('col_island_shift_%d_%d' % (j, i), HEIGHT) for i in range(len(cols[j]))] for j in range(WIDTH)]
# this is a bitvector representing final image, for all columns:
col_merged_islands=[BitVec('col_merged_islands_%d' % j, HEIGHT) for j in range(WIDTH)]

for j in range(WIDTH):
    q=cols[j]
    for i in range(len(q)):
        s.add(col_island_shift[j][i] >= 0)
        s.add(col_island_shift[j][i] <= HEIGHT-q[i])
        s.add(col_islands[j][i]==(2**q[i]-1) << col_island_shift[j][i])

    # must be an empty cell(s) between islands:
    for i in range(len(q)-1):
        s.add(col_island_shift[j][i+1] > col_island_shift[j][i]+q[i])

    s.add(col_island_shift[j][len(q)-1]<HEIGHT)

    # OR all islands into one:
    expr=col_islands[j][0]
    for i in range(len(q)-1):
        expr=expr | col_islands[j][i+1]
    s.add(col_merged_islands[j]==expr)

# ------------------------------------------------------------------------------------------------------------------------

# make "merged" vectors equal to each other:
for r in range(HEIGHT):
    for c in range(WIDTH):
        # lowest bits must be equal to each other:
        s.add(Extract(0,0,row_merged_islands[r]>>c) == Extract(0,0,col_merged_islands[c]>>r))

def print_model(m):
    for r in range(HEIGHT):
        rt=""
        for c in range(WIDTH):
            if (m[row_merged_islands[r]].as_long()>>c)&1==1:
                rt=rt+"*"
            else:
                rt=rt+" "
        print rt

print s.check()
m=s.model()
print_model(m)
exit(0)

# ... or ...

# enumerate all solutions (it's usually a single one):
results=[]
while s.check() == sat:
    m = s.model()
    print_model(m)

    results.append(m)
    block = []
    for d in m:
        t=d()
        block.append(t != m[d])
    s.add(Or(block))

print "results total=", len(results)
