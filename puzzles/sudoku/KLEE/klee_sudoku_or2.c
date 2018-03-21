#include <stdint.h>

/*
coordinates:
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
*/

uint8_t cells[9][9];

// http://www.norvig.com/sudoku.html
// http://www.mirror.co.uk/news/weird-news/worlds-hardest-sudoku-can-you-242294
char *puzzle="..53.....8......2..7..1.5..4....53...1..7...6..32...8..6.5....9..4....3......97..";

int main()
{
	klee_make_symbolic(cells, sizeof cells, "cells");
	
	// process text line:
	for (int row=0; row<9; row++)
		for (int column=0; column<9; column++)
		{
			char c=puzzle[row*9 + column];
			if (c!='.')
				klee_assume (cells[row][column]==c-'0');
			else
			{
				klee_assume (cells[row][column]>=1);
				klee_assume (cells[row][column]<=9);
			};
		};


	// for all 9 rows
	for (int row=0; row<9; row++)
	{
		
		klee_assume (((1<<cells[row][0]) |
				(1<<cells[row][1]) |
				(1<<cells[row][2]) |
				(1<<cells[row][3]) |
				(1<<cells[row][4]) |
				(1<<cells[row][5]) |
				(1<<cells[row][6]) |
				(1<<cells[row][7]) |
				(1<<cells[row][8]))==0x3FE ); // 11 1111 1110
		
	};

	// for all 9 columns
	for (int c=0; c<9; c++)
	{
		klee_assume (((1<<cells[0][c]) |
				(1<<cells[1][c]) |
				(1<<cells[2][c]) |
				(1<<cells[3][c]) |
				(1<<cells[4][c]) |
				(1<<cells[5][c]) |
				(1<<cells[6][c]) |
				(1<<cells[7][c]) |
				(1<<cells[8][c]))==0x3FE ); // 11 1111 1110
	};


	// enumerate all 9 squares
	for (int r=0; r<9; r+=3)
		for (int c=0; c<9; c+=3)
		{
			// add constraints for each 3*3 square:
			klee_assume ((1<<cells[r+0][c+0] |
					1<<cells[r+0][c+1] |
					1<<cells[r+0][c+2] | 
					1<<cells[r+1][c+0] | 
					1<<cells[r+1][c+1] | 
					1<<cells[r+1][c+2] | 
					1<<cells[r+2][c+0] | 
					1<<cells[r+2][c+1] | 
					1<<cells[r+2][c+2])==0x3FE ); // 11 1111 1110
		};

	// at this point, all constraints must be satisfied
	klee_assert(0);
};

