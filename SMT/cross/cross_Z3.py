#!/usr/bin/env python

from z3 import *
import sys

"""
# https://commons.wikimedia.org/wiki/File:Khachbar-1.jpg
pattern=[
"*****",
"* * *",
"* ***",
"*** *",
"* ***",
"* * *",
"*****"]
"""

"""
# https://commons.wikimedia.org/wiki/File:Khachbar-4.jpg
pattern=[
"*******",
"* * * *",
"*******",
"* * * *",
"*******",
"* * * *",
"*******"]
"""

# https://commons.wikimedia.org/wiki/File:British_crossword.svg
pattern=[
"**** **********",
" * * *  * * * *",
"***************",
" * * *  * * * *",
"********* *****",
" * * * * * *  *",
"****** ********",
"   * * * * *   ",
"******** ******",
"*  * * * * * * ",
"***** *********",
"* * * *  * * * ",
"***************",
"* * * *  * * * ",
"********** ****"]

HEIGHT=len(pattern)
WIDTH=len(pattern[0])

# scan pattern[] and find all "sticks" longer than 1 and collect its coordinates:

horizontal=[]

in_the_middle=False
for r in range(HEIGHT):
    for c in range(WIDTH):
        if pattern[r][c]=='*' and in_the_middle==False:
            in_the_middle=True
            start=(r,c)
        elif pattern[r][c]==' ' and in_the_middle==True:
            if c-start[1]>1:
                horizontal.append ((start, (r, c-1)))
            in_the_middle=False
    if in_the_middle:
        if c-start[1]>1:
            horizontal.append ((start, (r, c)))
        in_the_middle=False

vertical=[]

in_the_middle=False
for c in range(WIDTH):
    for r in range(HEIGHT):
        if pattern[r][c]=='*' and in_the_middle==False:
            in_the_middle=True
            start=(r,c)
        elif pattern[r][c]==' ' and in_the_middle==True:
            if r-start[0]>1:
                vertical.append ((start, (r-1, c)))
            in_the_middle=False
    if in_the_middle:
        if r-start[0]>1:
            vertical.append ((start, (r, c)))
        in_the_middle=False

# for the first simple pattern, we will have such coordinates of "sticks":
# horizontal=[((0, 0), (0, 4)), ((2, 2), (2, 4)), ((3, 0), (3, 2)), ((4, 2), (4, 4)), ((6, 0), (6, 4))]
# vertical=[((0, 0), (6, 0)), ((0, 2), (6, 2)), ((0, 4), (6, 4))]

# the list in this file is assumed to not have duplicates, otherwise duplicates can be present in the final resulting crossword:
with open("words.txt") as f:
    content = f.readlines()
words = [x.strip() for x in content]

# FIXME: slow, called too often
def find_words_len(l):
    rt=[]
    i=0
    for word in words:
        if len(word)==l:
            rt.append ((i, word))
        i=i+1
    return rt

# 2D array of ASCII codes of all characters:
chars=[[Int('chars_%d_%d' % (r, c)) for c in range(WIDTH)] for r in range(HEIGHT)]
# indices of horizontal words:
horizontal_idx=[Int('horizontal_idx_%d' % i) for i in range(len(horizontal))]
# indices of vertical words:
vertical_idx=[Int('vertical_idx_%d' % i) for i in range(len(vertical))]

s=Solver()

# this function takes coordinates, word length and word itself
# for "hello", it returns array like:
# [chars[0][0]==ord('h'), chars[0][1]==ord('e'), chars[0][2]==ord('l'), chars[0][3]==ord('l'), chars[0][4]==ord('o')]
def form_H_expr(r, c, l, w):
    return [chars[r][c+i]==ord(w[i]) for i in range(l)]

# now we find all horizonal "sticks", we find all possible words of corresponding length...
for i in range(len(horizontal)):
    h=horizontal[i]
    _from=h[0]
    _to=h[1]
    l=_to[1]-_from[1]+1
    list_of_ANDs=[]
    for idx, word in find_words_len(l):
        # at this point, we form expression like:
        # And(chars[0][0]==ord('h'), chars[0][1]==ord('e'), chars[0][2]==ord('l'), chars[0][3]==ord('l'), chars[0][4]==ord('o'), horizontal_idx[]==...)
        list_of_ANDs.append(And(form_H_expr(_from[0], _from[1], l, word)+[horizontal_idx[i]==idx]))
    # at this point, we form expression like:
    # Or(And(chars...==word1), And(chars...==word2), And(chars...==word3))
    s.add(Or(*list_of_ANDs))

# same for vertical "sticks":
def form_V_expr(r, c, l, w):
    return [chars[r+i][c]==ord(w[i]) for i in range(l)]

for i in range(len(vertical)):
    v=vertical[i]
    _from=v[0]
    _to=v[1]
    l=_to[0]-_from[0]+1
    list_of_ANDs=[]
    for idx, word in find_words_len(l):
        list_of_ANDs.append(And(form_V_expr(_from[0], _from[1], l, word)+[vertical_idx[i]==idx]))
    s.add(Or(*list_of_ANDs))

# we collected indices of horizonal/vertical words to make sure they will not be duplicated on resulting crossword:
s.add(Distinct(*(horizontal_idx+vertical_idx)))

def print_model (m):
    print ""
    for r in range(HEIGHT):
        for c in range(WIDTH):
            if pattern[r][c]=='*':
                sys.stdout.write(chr(m[chars[r][c]].as_long()))
            else:
                sys.stdout.write(' ')
        print ""
    print ""

    print "horizontal:"
    for i in range(len(horizontal)):
        print horizontal[i], words[m[horizontal_idx[i]].as_long()]

    print "vertical:"
    for i in range(len(vertical)):
        print vertical[i], words[m[vertical_idx[i]].as_long()]

N=10
# get 10 results:
results=[]
for i in range(N):
    if s.check() == sat:
        m = s.model()
        print_model(m)
        results.append(m)
        block = []
        for d in m:
            c=d()
            block.append(c != m[d])
        s.add(Or(block))
    else:
        print "total results", len(results)
        break

