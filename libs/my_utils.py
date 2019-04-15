#!/usr/bin/env python3

# Python utils

# dennis(a)yurichev, 2017-2018

def read_lines_from_file (fname):
    f=open(fname)
    new_ar=[item.rstrip() for item in f.readlines()]
    f.close()
    return new_ar

# reverse list:
def rvr(i):
    return i[::-1]

def reflect_vertically(a):
    return [rvr(row) for row in a]

def reflect_horizontally(a):
    return rvr(a)

# N.B. must work on arrays of arrays of objects, not on arrays of strings!
def rotate_rect_array_90_CCW(a_in):
    a=reflect_vertically(a_in)
    rt=[]
    # reflect diagonally:
    for row in range(len(a[0])):
        #rt.append("".join([a[col][row] for col in range(len(a))]))
        rt.append([a[col][row] for col in range(len(a))])

    return rt

# angle: 0 - leave as is; 1 - 90 CCW; 2 - 180 CCW; 3 - 270 CCW
# FIXME: slow
def rotate_rect_array(a, angle):
    if angle==0:
        return a
    assert (angle>=1)
    assert (angle<=3)

    for i in range(angle):
        a=rotate_rect_array_90_CCW(a)
    return a

def adjacent_coords(X1, Y1, X2, Y2):
    # return True if pair of coordinates laying adjacently: vertically/horizontally/diagonally:
    return any([X1==X2   and Y1==Y2+1,
    		X1==X2   and Y1==Y2-1,
    		X1==X2+1 and Y1==Y2,
    		X1==X2-1 and Y1==Y2,
    		X1==X2-1 and Y1==Y2-1,
    		X1==X2-1 and Y1==Y2+1,
    		X1==X2+1 and Y1==Y2-1,
    		X1==X2+1 and Y1==Y2+1])

def ANSI_set_normal_color(color):
    return '\033[%dm' % (color+31)

def ANSI_reset():
    return '\033[0m'

def partition(lst, n):
    division = len(lst) / float(n)
    return [ lst[int(round(division * i)): int(round(division * (i + 1)))] for i in xrange(n) ]

