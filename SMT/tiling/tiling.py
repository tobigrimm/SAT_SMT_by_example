#-*- coding: utf-8 -*-

from z3 import *
from operator import add
import itertools, frolic, Z3_utils

"""
board=[ "********",
	"********",
	"********",
	"***  ***",
	"***  ***",
	"********",
	"********",
	"********"]

tiles=[
[" **",    # F
 "** ",
 " * "],

["***",    # P
 "** "],

["*****"], # I

["**  ",   # N
 " ***"],

["****",   # L
 "   *"],

["***",    # T
 " * ",
 " * "],

["* *",    # U
 "***"],

["*  ",    # V
 "*  ",
 "***"],

["*  ",    # W
 "** ",
" **"],

[" * ",    # X
 "***",
 " * "],

["  * ",   # Y
 "****"],

["** ",    # Z
 " * ",
 " **"]
]
"""

#"""
board=[ " ***",
	"****",
	"****",
	"*** "]

tiles=[
["* ",
 "**",
 "* "],

["***",
 " **"],

["**",
 " *"],

["*",
 "*"]
]
#"""

board_height=len(board)
board_width=len(board[0])

TILES_TOTAL=len(tiles)

def lists_has_adjacent_cells(l1, l2):
    # enumerate all possible combinations of items from two lists:
    return any([frolic.adjacent_coords(q[0][0], q[0][1], q[1][0], q[1][1]) for q in itertools.product(l1, l2)])

def can_be_placed(into, irow, icol, tile):
    rt=[]
    tile_height=len(tile)
    tile_width=len(tile[0])
    for prow in range(tile_height):
        for pcol in range(tile_width):
            if tile[prow][pcol]=='*':
                # tile cannot be placed if there is a hole on board:
                if into[irow+prow][icol+pcol]==' ':
                    return None
                if into[irow+prow][icol+pcol]=='*':
                    rt.append((irow+prow, icol+pcol))
    return rt

# enumerate all positions on board and try to put tile there:
def find_all_placements(_type, tile):
    tile_height=len(tile)
    tile_width=len(tile[0])
    rt=[]

    for row in range(board_height-tile_height+1):
        for col in range(board_width-tile_width+1):
            tmp=can_be_placed(board, row, col, tile)
            if tmp!=None:
                rt.append((_type, tmp))
# rt is a list of tuples, each has poly type and list of coordinates, like:
#(0, [(0, 1), (1, 1), (1, 2), (2, 1)]),
#(0, [(0, 2), (1, 2), (1, 3), (2, 2)]),
#...
#(1, [(0, 1), (0, 2), (1, 1), (1, 2), (2, 1)]),
#(1, [(0, 2), (0, 3), (1, 2), (1, 3), (2, 2)])

    return rt

def str_to_list_of_chars(lst):
    return [l for l in lst]

def find_all_placements_with_rotations(poly_type, tile):
    # we operate here with tiles encoded as list of lists of chars
    tile=[str_to_list_of_chars(tmp) for tmp in tile]
 
    # rotate tile in 4 ways.
    # also, mirror it horizontally
    # that gives us 8 versions of each tile
    # remove duplicates
    duplicates=[]
    rt=[]
    for a in range(4):

        t1=frolic.rotate_rect_array(tile, a)
        if t1 not in duplicates:
            duplicates.append(t1)
            rt=rt+find_all_placements(poly_type, t1)

        t2=frolic.reflect_horizontally(frolic.rotate_rect_array(tile, a))
        if t2 not in duplicates:
            duplicates.append(t2)
            rt=rt+find_all_placements(poly_type, t2)

    return rt

# input: list of tiles, like:
# [(0, [(2, 1), (3, 0), (3, 1), (3, 2)]), 
# (1, [(0, 1), (0, 2), (0, 3), (1, 1), (1, 2)]),
# (2, [(1, 3), (2, 2), (2, 3)]), 
# (3, [(1, 0), (2, 0)])]
# each tuple has tile type + list of coordinates on board

# output: color for each tile, like: [2, 0, 1, 3]
def color_tiles(solution):
    # make a graph
    G=[]
    # enumerate all possible pair of tiles:
    for pair in itertools.combinations(solution, r=2):
        if lists_has_adjacent_cells(pair[0][1], pair[1][1]):
            # add constraint, if tiles adjacent to each other.
            # it's not a problem to add the same constraint multiple times.
            G.append((pair[0][0], pair[1][0]))

    # this is planar graph anyway, 4 colors enough:
    return Z3_utils.color_graph_using_Z3(G, total=TILES_TOTAL, limit=4)

def print_solution(solution):
    for row in range(board_height):
        s=""
        for col in range(board_width):
            if board[row][col]=='*':
                for a in range(TILES_TOTAL):
                    if (row,col) in solution[a][1]:
                        s=s+"0123456789abcdef"[a]
                        break
            else:
                # skip holes in board:
                s=s+" "
        print s

    print ""

    # print colored solution:

    coloring=color_tiles(solution)

    for row in range(board_height):
        s=""
        for col in range(board_width):
            if board[row][col]=='*':
                for a in range(TILES_TOTAL):
                    if (row,col) in solution[a][1]:
                        s=s+frolic.ANSI_set_normal_color(coloring[a])+"██"
                        break
            else:
                # skip holes in board:
                s=s+"  "
        print s

    print frolic.ANSI_reset()

init_rows=[]
for i in range(TILES_TOTAL):
    init_rows=init_rows+find_all_placements_with_rotations(i,tiles[i])

print "len(init_rows)=", len(init_rows)

# init_rows is a list of tuples
# each tuple has poly type (num) + list of coordinates on board at which it can cover
# like:
#(2, [(1, 1), (2, 1), (2, 2)])
#(2, [(2, 1), (3, 1), (3, 2)])
#(3, [(0, 1), (1, 1)])
#(3, [(0, 3), (1, 3)])

s=Solver()

rows=[Bool('row_%d' % r) for r in range(len(init_rows))]

# make inverse tables:

inv_tbl_board={}
inv_tbl_poly={}

cur_row=0
for t in init_rows:
    poly_type=t[0]
    if poly_type not in inv_tbl_poly:
        inv_tbl_poly[poly_type]=[]
    inv_tbl_poly[poly_type].append(cur_row)
    coords=t[1]
    for coord in coords:
        if coord not in inv_tbl_board:
            inv_tbl_board[coord]=[]
        inv_tbl_board[coord].append(cur_row)
    cur_row=cur_row+1

# at this point, inv_tbl_poly is a dict, it has poly type as a key and list of rows as a value
# these are rows where specific poly type is stored

# inv_tbl_board is also a dict. key=tuple (coordinates). value=list of rows, which can cover this cell on board.

# only one row can be selected from inv_tbl_poly, meaning, each tile can be connected to only one row:
for t in inv_tbl_poly:
    tmp=[rows[q] for q in inv_tbl_poly[t]]

    # only one True must be present in tmp.
    # AtMost()/AtLeast() takes list of arguments + k.
    # we pass here a list + 1 as an arguments to functions:
    s.add(AtMost(*(tmp+[1])))
    s.add(AtLeast(*(tmp+[1])))

# only one row can be selected from inv_tbl_board, meaning, each cell on board can be connected to only one row:
for t in inv_tbl_board:
    tmp=[rows[q] for q in inv_tbl_board[t]]

    # only one True must be present in tmp:
    s.add(AtMost(*(tmp+[1])))
    s.add(AtLeast(*(tmp+[1])))

# enumerate all possible solutions:
results=[]
sol_n=1
while True:
    if s.check() == sat:
        m = s.model()

        # now after solving, we are getting a list of rows.

        solution=[]

        # which rows are True? copy them to solution[]
        for row in range(len(init_rows)):
            if is_true(m[rows[row]]):
                solution.append(init_rows[row])

        # at this point, solution[] may looks like

        #[(0, [(1, 2), (2, 2), (2, 3), (3, 2)]), 
        #(1, [(1, 0), (2, 0), (2, 1), (3, 0), (3, 1)]), 
        #(2, [(0, 2), (0, 3), (1, 3)])
        #(3, [(0, 1), (1, 1)])]

        #These are four tiles with coordinates on board for each tile.

        print "solution number", sol_n
        sol_n=sol_n+1
        print_solution(solution)

        results.append(m)
        block = []
        for d in m:
            c=d()
            block.append(c != m[d])
        s.add(Or(block))
    else:
        print "results total=", len(results)
        break

