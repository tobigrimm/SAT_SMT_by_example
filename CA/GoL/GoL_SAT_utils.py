#!/usr/bin/env python3

import sys, subprocess, os
import SAT_lib, my_utils

def mathematica_to_CNF (s, d):
    for k in d.keys():
        s=s.replace(k, d[k])
    s=s.replace("!", "-").replace("||", " ").replace("(", "").replace(")", "")
    s=s.split ("&&")
    return s

cnt=0
def write_RLE(grid):
    global cnt
    cnt=cnt+1
    fname="%d.rle" % cnt
    f=open(fname, "w")
    HEIGHT=len(grid)
    WIDTH=len(grid[0])
    f.write ("x = %d, y = %d, rule = B3/S23\n" % (WIDTH, HEIGHT))

    for r in range(HEIGHT):
        for c in range(WIDTH):
            f.write("o" if grid[r][c] else "b")
        f.write("!" if r+1==HEIGHT else "$")

    f.close()
    print (fname+" written")

def negate_clause(s):
    rt=[]
    for i in s:
        if i=="0":
            continue
        rt.append(i[1:] if i.startswith("-") else "-"+i)
    return " ".join(rt)

def print_grid(grid):
    for row in grid:
        [sys.stdout.write("*" if col else ".") for col in row]
        sys.stdout.write("\n")
    
def write_CNF(fname, clauses, VARS_TOTAL):
    f=open(fname, "w")
    f.write ("p cnf "+str(VARS_TOTAL)+" "+str(len(clauses))+"\n")
    [f.write(c+" 0\n") for c in clauses]
    f.close()
    
def run_minisat (CNF_fname):
    child = subprocess.Popen(["minisat", CNF_fname, "results.txt"], stdout=subprocess.PIPE)
    child.wait()
    # 10 is SAT, 20 is UNSAT
    if child.returncode==20:
        os.remove ("results.txt")
        return None

    if child.returncode!=10:
        print ("(minisat) unknown retcode: ", child.returncode)
        exit(0)
    
    solution=my_utils.read_lines_from_file("results.txt")[1].split(" ")
    os.remove ("results.txt")

    return solution

def cell_is_false (center, a):
    s="(!a||!b||!c||d||e||f||g||h)&&(!a||!b||c||!d||e||f||g||h)&&(!a||!b||c||d||!e||f||g||h)&&" \
      "(!a||!b||c||d||e||!f||g||h)&&(!a||!b||c||d||e||f||!g||h)&&(!a||!b||c||d||e||f||g||!h)&&" \
      "(!a||!b||!q||d||e||f||g||h)&&(!a||b||!c||!d||e||f||g||h)&&(!a||b||!c||d||!e||f||g||h)&&" \
      "(!a||b||!c||d||e||!f||g||h)&&(!a||b||!c||d||e||f||!g||h)&&(!a||b||!c||d||e||f||g||!h)&&" \
      "(!a||b||c||!d||!e||f||g||h)&&(!a||b||c||!d||e||!f||g||h)&&(!a||b||c||!d||e||f||!g||h)&&" \
      "(!a||b||c||!d||e||f||g||!h)&&(!a||b||c||d||!e||!f||g||h)&&(!a||b||c||d||!e||f||!g||h)&&" \
      "(!a||b||c||d||!e||f||g||!h)&&(!a||b||c||d||e||!f||!g||h)&&(!a||b||c||d||e||!f||g||!h)&&" \
      "(!a||b||c||d||e||f||!g||!h)&&(!a||!c||!q||d||e||f||g||h)&&(!a||c||!q||!d||e||f||g||h)&&" \
      "(!a||c||!q||d||!e||f||g||h)&&(!a||c||!q||d||e||!f||g||h)&&(!a||c||!q||d||e||f||!g||h)&&" \
      "(!a||c||!q||d||e||f||g||!h)&&(a||!b||!c||!d||e||f||g||h)&&(a||!b||!c||d||!e||f||g||h)&&" \
      "(a||!b||!c||d||e||!f||g||h)&&(a||!b||!c||d||e||f||!g||h)&&(a||!b||!c||d||e||f||g||!h)&&" \
      "(a||!b||c||!d||!e||f||g||h)&&(a||!b||c||!d||e||!f||g||h)&&(a||!b||c||!d||e||f||!g||h)&&" \
      "(a||!b||c||!d||e||f||g||!h)&&(a||!b||c||d||!e||!f||g||h)&&(a||!b||c||d||!e||f||!g||h)&&" \
      "(a||!b||c||d||!e||f||g||!h)&&(a||!b||c||d||e||!f||!g||h)&&(a||!b||c||d||e||!f||g||!h)&&" \
      "(a||!b||c||d||e||f||!g||!h)&&(a||b||!c||!d||!e||f||g||h)&&(a||b||!c||!d||e||!f||g||h)&&" \
      "(a||b||!c||!d||e||f||!g||h)&&(a||b||!c||!d||e||f||g||!h)&&(a||b||!c||d||!e||!f||g||h)&&" \
      "(a||b||!c||d||!e||f||!g||h)&&(a||b||!c||d||!e||f||g||!h)&&(a||b||!c||d||e||!f||!g||h)&&" \
      "(a||b||!c||d||e||!f||g||!h)&&(a||b||!c||d||e||f||!g||!h)&&(a||b||c||!d||!e||!f||g||h)&&" \
      "(a||b||c||!d||!e||f||!g||h)&&(a||b||c||!d||!e||f||g||!h)&&(a||b||c||!d||e||!f||!g||h)&&" \
      "(a||b||c||!d||e||!f||g||!h)&&(a||b||c||!d||e||f||!g||!h)&&(a||b||c||d||!e||!f||!g||h)&&" \
      "(a||b||c||d||!e||!f||g||!h)&&(a||b||c||d||!e||f||!g||!h)&&(a||b||c||d||e||!f||!g||!h)&&" \
      "(!b||!c||!q||d||e||f||g||h)&&(!b||c||!q||!d||e||f||g||h)&&(!b||c||!q||d||!e||f||g||h)&&" \
      "(!b||c||!q||d||e||!f||g||h)&&(!b||c||!q||d||e||f||!g||h)&&(!b||c||!q||d||e||f||g||!h)&&" \
      "(b||!c||!q||!d||e||f||g||h)&&(b||!c||!q||d||!e||f||g||h)&&(b||!c||!q||d||e||!f||g||h)&&" \
      "(b||!c||!q||d||e||f||!g||h)&&(b||!c||!q||d||e||f||g||!h)&&(b||c||!q||!d||!e||f||g||h)&&" \
      "(b||c||!q||!d||e||!f||g||h)&&(b||c||!q||!d||e||f||!g||h)&&(b||c||!q||!d||e||f||g||!h)&&" \
      "(b||c||!q||d||!e||!f||g||h)&&(b||c||!q||d||!e||f||!g||h)&&(b||c||!q||d||!e||f||g||!h)&&" \
      "(b||c||!q||d||e||!f||!g||h)&&(b||c||!q||d||e||!f||g||!h)&&(b||c||!q||d||e||f||!g||!h)"

    d={"q":center, "a":a[0], "b":a[1], "c":a[2], "d":a[3], "e":a[4], "f":a[5], "g":a[6], "h":a[7]}
    return mathematica_to_CNF(s, d)

def cell_is_true (center, a):
    s="(!a||!b||!c||!d)&&(!a||!b||!c||!e)&&(!a||!b||!c||!f)&&(!a||!b||!c||!g)&&(!a||!b||!c||!h)&&" \
      "(!a||!b||!d||!e)&&(!a||!b||!d||!f)&&(!a||!b||!d||!g)&&(!a||!b||!d||!h)&&(!a||!b||!e||!f)&&" \
      "(!a||!b||!e||!g)&&(!a||!b||!e||!h)&&(!a||!b||!f||!g)&&(!a||!b||!f||!h)&&(!a||!b||!g||!h)&&" \
      "(!a||!c||!d||!e)&&(!a||!c||!d||!f)&&(!a||!c||!d||!g)&&(!a||!c||!d||!h)&&(!a||!c||!e||!f)&&" \
      "(!a||!c||!e||!g)&&(!a||!c||!e||!h)&&(!a||!c||!f||!g)&&(!a||!c||!f||!h)&&(!a||!c||!g||!h)&&" \
      "(!a||!d||!e||!f)&&(!a||!d||!e||!g)&&(!a||!d||!e||!h)&&(!a||!d||!f||!g)&&(!a||!d||!f||!h)&&" \
      "(!a||!d||!g||!h)&&(!a||!e||!f||!g)&&(!a||!e||!f||!h)&&(!a||!e||!g||!h)&&(!a||!f||!g||!h)&&" \
      "(a||b||c||q||d||e||f)&&(a||b||c||q||d||e||g)&&(a||b||c||q||d||e||h)&&" \
      "(a||b||c||q||d||f||g)&&(a||b||c||q||d||f||h)&&(a||b||c||q||d||g||h)&&" \
      "(a||b||c||q||e||f||g)&&(a||b||c||q||e||f||h)&&(a||b||c||q||e||g||h)&&" \
      "(a||b||c||q||f||g||h)&&(a||b||c||d||e||f||g)&&(a||b||c||d||e||f||h)&&(a||b||c||d||e||g||h)&&" \
      "(a||b||c||d||f||g||h)&&(a||b||c||e||f||g||h)&&(a||b||q||d||e||f||g)&&(a||b||q||d||e||f||h)&&" \
      "(a||b||q||d||e||g||h)&&(a||b||q||d||f||g||h)&&(a||b||q||e||f||g||h)&&(a||b||d||e||f||g||h)&&" \
      "(a||c||q||d||e||f||g)&&(a||c||q||d||e||f||h)&&(a||c||q||d||e||g||h)&&" \
      "(a||c||q||d||f||g||h)&&(a||c||q||e||f||g||h)&&(a||c||d||e||f||g||h)&&(a||q||d||e||f||g||h)&&" \
      "(!b||!c||!d||!e)&&(!b||!c||!d||!f)&&(!b||!c||!d||!g)&&(!b||!c||!d||!h)&&(!b||!c||!e||!f)&&" \
      "(!b||!c||!e||!g)&&(!b||!c||!e||!h)&&(!b||!c||!f||!g)&&(!b||!c||!f||!h)&&(!b||!c||!g||!h)&&" \
      "(!b||!d||!e||!f)&&(!b||!d||!e||!g)&&(!b||!d||!e||!h)&&(!b||!d||!f||!g)&&(!b||!d||!f||!h)&&" \
      "(!b||!d||!g||!h)&&(!b||!e||!f||!g)&&(!b||!e||!f||!h)&&(!b||!e||!g||!h)&&(!b||!f||!g||!h)&&" \
      "(b||c||q||d||e||f||g)&&(b||c||q||d||e||f||h)&&(b||c||q||d||e||g||h)&&" \
      "(b||c||q||d||f||g||h)&&(b||c||q||e||f||g||h)&&(b||c||d||e||f||g||h)&&(b||q||d||e||f||g||h)&&" \
      "(!c||!d||!e||!f)&&(!c||!d||!e||!g)&&(!c||!d||!e||!h)&&(!c||!d||!f||!g)&&(!c||!d||!f||!h)&&" \
      "(!c||!d||!g||!h)&&(!c||!e||!f||!g)&&(!c||!e||!f||!h)&&(!c||!e||!g||!h)&&(!c||!f||!g||!h)&&" \
      "(c||q||d||e||f||g||h)&&(!d||!e||!f||!g)&&(!d||!e||!f||!h)&&(!d||!e||!g||!h)&&(!d||!f||!g||!h)&&" \
      "(!e||!f||!g||!h)"
    
    d={"q":center, "a":a[0], "b":a[1], "c":a[2], "d":a[3], "e":a[4], "f":a[5], "g":a[6], "h":a[7]}
    return mathematica_to_CNF(s, d)

def list_partition(lst, n):
    division = int(len(lst) / float(n))
    return [ lst[int(round(division * i)): int(round(division * (i + 1)))] for i in range(n) ]

# for main part: row=[0...HEIGHT-1]; col=[0...WIDTH-1]
def coords_to_var (row, col, HEIGHT, WIDTH):
    VARS_TOTAL=WIDTH*HEIGHT+1
    VAR_FALSE=str(VARS_TOTAL)

    if row<=-1 or row>=HEIGHT:
        return VAR_FALSE
    if col<=-1 or col>=WIDTH:
        return VAR_FALSE

    assert (col<WIDTH)
    assert (row<HEIGHT)
    # we always use SAT variables as strings, anyway.
    # the 1st variables is 1, not 0
    return str(row*WIDTH+col+1)

# FIXME: slow
def SAT_solution_to_grid(solution, HEIGHT, WIDTH):
    grid=[[False for c in range(WIDTH)] for r in range(HEIGHT)]
    for r in range(HEIGHT):
        for c in range(WIDTH):
            v=coords_to_var(r, c, HEIGHT, WIDTH)
            if "-"+v in solution:
                grid[r][c]=False
            elif v in solution:
                grid[r][c]=True

    return grid

def grid_to_clause(grid, HEIGHT, WIDTH):
    rt=[]
    for r in range(HEIGHT):
        for c in range(WIDTH):
            rt.append(("-" if grid[r][c]==False else "") + str(coords_to_var(r, c, HEIGHT, WIDTH)))
    return rt

def get_neighbours(r, c, H, W):
    return [coords_to_var(r-1, c-1, H, W), coords_to_var(r-1, c, H, W), coords_to_var(r-1, c+1, H, W),
            coords_to_var(r, c-1, H, W), coords_to_var(r, c+1, H, W), coords_to_var(r+1, c-1, H, W),
            coords_to_var(r+1, c, H, W), coords_to_var(r+1, c+1, H, W)]


