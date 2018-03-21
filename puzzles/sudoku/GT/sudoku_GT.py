import sys
from z3 import *

"""
------------------------------
00 01 02 | 03 04 05 | 06 07 08
10 11 12 | 13 14 15 | 16 17 18
20 21 22 | 23 24 25 | 26 27 28
------------------------------
30 31 32 | 33 34 35 | 36 37 38
40 41 42 | 43 44 45 | 46 47 48
50 51 52 | 53 54 55 | 56 57 58
------------------------------
60 61 62 | 63 64 65 | 66 67 68
70 71 72 | 73 74 75 | 76 77 78
80 81 82 | 83 84 85 | 86 87 88
------------------------------
"""

s=Solver()

# using Python list comprehension, construct array of arrays of BitVec instances:
cells=[[Int('cell%d%d' % (r, c)) for c in range(9)] for r in range(9)]

# this is important, because otherwise, Z3 will report correct solutions with too big and/or negative numbers in cells
for r in range(9):
	for c in range(9):
		s.add(cells[r][c]>=1)
		s.add(cells[r][c]<=9)

# for all 9 rows
for r in range(9):
	s.add(Distinct(cells[r][0],
		cells[r][1],
		cells[r][2],
		cells[r][3],
		cells[r][4],
		cells[r][5],
		cells[r][6],
		cells[r][7],
		cells[r][8]))

# for all 9 columns
for c in range(9):
	s.add(Distinct(cells[0][c],
		cells[1][c],
		cells[2][c],
		cells[3][c],
		cells[4][c],
		cells[5][c],
		cells[6][c],
		cells[7][c],
		cells[8][c]))

# enumerate all 9 squares
for r in range(0, 9, 3):
	for c in range(0, 9, 3):
		# add constraints for each 3*3 square:
			s.add(Distinct(cells[r+0][c+0],
				cells[r+0][c+1],
				cells[r+0][c+2], 
				cells[r+1][c+0], 
				cells[r+1][c+1], 
				cells[r+1][c+2], 
				cells[r+2][c+0], 
				cells[r+2][c+1], 
				cells[r+2][c+2]))

"""
Subsquares:

------------------------------
         |          |         
 1,1     | 1,2      | 1,3     
         |          |         
------------------------------
         |          |         
 2,1     | 2,2      | 2,3     
         |          |         
------------------------------
         |          |         
 3,1     | 3,2      | 3,3     
         |          |         
------------------------------
"""

# from http://www.killersudokuonline.com/puzzles/2017/puzzle-GD4hzi164344.pdf

# subsquare 1,1:
s.add(cells[0][0]>cells[0][1])
s.add(cells[1][0]>cells[1][1])
s.add(cells[2][0]<cells[2][1])

s.add(cells[0][1]<cells[0][2])
s.add(cells[0][2]<cells[1][2])

# subsquare 1,2:
s.add(cells[0][4]>cells[1][4])
s.add(cells[1][3]>cells[2][3])
s.add(cells[1][4]>cells[2][4])
s.add(cells[1][5]>cells[2][5])

# subsquare 1,3:
s.add(cells[0][6]>cells[0][7])
s.add(cells[0][7]<cells[0][8])
s.add(cells[0][6]<cells[1][6])
s.add(cells[1][7]<cells[1][8])
s.add(cells[1][6]>cells[2][6])
s.add(cells[1][7]>cells[2][7])
s.add(cells[1][8]>cells[2][8])

# subsquare 2,1:
s.add(cells[3][0]<cells[4][0])
s.add(cells[4][0]<cells[5][0])
s.add(cells[4][1]<cells[4][2])
s.add(cells[4][0]<cells[5][0])
s.add(cells[4][1]>cells[5][1])
s.add(cells[4][2]<cells[5][2])

# subsquare 2,2:
s.add(cells[3][4]>cells[4][4])
s.add(cells[3][4]<cells[3][5])
s.add(cells[4][3]<cells[4][4])
s.add(cells[4][3]<cells[5][3])

# subsquare 2,3:
s.add(cells[3][6]>cells[3][7])
s.add(cells[3][7]>cells[3][8])
s.add(cells[3][6]>cells[4][6])
s.add(cells[4][6]<cells[4][7])
s.add(cells[4][7]<cells[4][8])
s.add(cells[5][7]<cells[5][8])

# subsquare 3,1:
s.add(cells[6][0]>cells[6][1])
s.add(cells[6][1]<cells[6][2])
s.add(cells[6][1]>cells[7][1])
s.add(cells[7][0]<cells[7][1])
s.add(cells[7][0]>cells[8][0])
s.add(cells[7][2]>cells[8][2])

# subsquare 3,2:
s.add(cells[6][3]>cells[6][4])
s.add(cells[6][4]>cells[6][5])
s.add(cells[7][3]>cells[7][4])
s.add(cells[7][4]<cells[7][5])
s.add(cells[8][3]>cells[8][4])
s.add(cells[8][4]<cells[8][5])
s.add(cells[7][4]>cells[8][4])

# subsquare 3,3:
s.add(cells[6][7]>cells[6][8])
s.add(cells[6][7]>cells[7][7])
s.add(cells[7][7]>cells[8][7])
s.add(cells[8][7]>cells[8][8])


#print s.check()
s.check()
#print s.model()
m=s.model()

for r in range(9):
	for c in range(9):
		sys.stdout.write (str(m[cells[r][c]])+" ")
	print ""

