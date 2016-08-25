#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <time.h>
#include <stdint.h>
#include <assert.h>

// octothorpe
#include "rand.h"
#include "stuff.h"

#define HEIGHT 8
#define WIDTH 16

enum type
{
	type0,
	type_dangling,
	type2a, // ┃, ━         2 rotations possible
	type2b, // ┏, ┓, ┛, ┗   all 4 rotations possible
	type3,  // ┣, ┳, ┫, ┻   all 4 rotations possible
	type4   // ╉            no rotation are possible
};

// bitmask
enum cell_joints
{
	right=	(1<<0),
	left=	(1<<1),
	top=	(1<<2),
	bottom=	(1<<3)
};

// top, right, bottom, left
enum type types[]={
/*0000*/ type0,
/*0001*/ type_dangling,
/*0010*/ type_dangling,
/*0011*/ type2b, // "┓"
/*0100*/ type_dangling,
/*0101*/ type2a, // "━"
/*0110*/ type2b, // "┏"
/*0111*/ type3,  // "┳"
/*1000*/ type_dangling,
/*1001*/ type2b, // "┛"
/*1010*/ type2a, // "┃"
/*1011*/ type3,  // "┫"
/*1100*/ type2b, // "┗"
/*1101*/ type3,  // "┻"
/*1110*/ type3,  // "┣"
/*1111*/ type4,  // "╋"
};

// array of strings instead of string, because pseudo-graphical symbols are encoded in UTF-8
// top, right, bottom, left
char* symbols[]={
/*0000*/ " ",
/*0001*/ "○", // dangling
/*0010*/ "○", // dangling
/*0011*/ "┓",
/*0100*/ "○", // dangling
/*0101*/ "━",
/*0110*/ "┏",
/*0111*/ "┳",
/*1000*/ "○", // dangling
/*1001*/ "┛",
/*1010*/ "┃",
/*1011*/ "┫",
/*1100*/ "┗",
/*1101*/ "┻",
/*1110*/ "┣",
/*1111*/ "╋"
};

// vertical and horizontal joints
bool vjoints[HEIGHT+1][WIDTH];
bool hjoints[HEIGHT][WIDTH+1];

int get_joints_of_cell (int r, int c)
{
	bool top=vjoints[r][c];
	bool bottom=vjoints[r+1][c];
	bool left=hjoints[r][c];
	bool right=hjoints[r][c+1];
	return (top<<3) | (right<<2) | (bottom<<1) | left;
};

int count_empty_cells()
{
	int empty_cells=0;

	// enumerate cells
	for (int r=0; r<HEIGHT; r++)
		for (int c=0; c<WIDTH; c++)
			if (get_joints_of_cell(r, c)==0)
				empty_cells++;
	
	return empty_cells;
};

void remove_danglings()
{
	bool removed_something=false;

	// enumerate cells
	for (int r=0; r<HEIGHT; r++)
		for (int c=0; c<WIDTH; c++)
			if (popcnt32(get_joints_of_cell(r,c))==1)
			{
				// this cell has only one joint
				// but we don't know which
				// so remove all
				vjoints[r][c]=false;
				vjoints[r+1][c]=false;
				hjoints[r][c]=false;
				hjoints[r][c+1]=false;
				removed_something=true;
			};
	
	// handle all subsequent cells recursively
	if (removed_something)
		remove_danglings();
};

// array of strings instead of string, because pseudo-graphical symbols are encoded in UTF-8
char* type2a_str[]={"┃", "━"};
char* type2b_str[]={"┏", "┓", "┛", "┗"};
char* type3_str[]={"┣", "┳", "┫", "┻"};

char *cell_to_string (int idx, bool shuffle_rotations)
{
	if (shuffle_rotations==false)
		return symbols[idx];

	// visual randomness is also to be added (rotate each cell randomly)
	switch (types[idx])
	{
		case type0:
			return " ";
		case type_dangling:
			assert(0); // we shouldn't be here
		case type2a:
			return type2a_str[rand_reg(0,1)];
		case type2b:
			return type2b_str[rand_reg(0,3)];
		case type3:
			return type3_str[rand_reg(0,3)];
		case type4:
			return "╉";
		default:
			assert(0);
	};
};

void print_cells(bool shuffle_rotations)
{
#define ANSI_turn_light_green "\033[1;32m"
#define ANSI_turn_light_black "\033[1;30m"
#define ANSI_turn_off "\033[0m"

	// header:
	printf (ANSI_turn_light_black);
	printf ("┌");
	for (int c=0; c<WIDTH; c++)
		printf (c+1==WIDTH ? "─┐\n" : "─┬");

	// enumerate rows:
	for (int r=0; r<HEIGHT; r++)
	{
		// enumerate columns:
		for (int c=0; c<WIDTH; c++)
		{
			int idx=get_joints_of_cell(r,c);
			printf ("│%s%s%s",
					ANSI_turn_light_green,
					cell_to_string(idx, shuffle_rotations),
					ANSI_turn_light_black);
		};
		printf ("│\n");

		// separator between rows or footer:
		if (r+1==HEIGHT)
		{
			// footer:
			printf ("└");
			for (int c=0; c<WIDTH; c++)
				printf (c+1==WIDTH ? "─┘\n" : "─┴");
		}
		else
		{
			// separator between rows:
			printf ("├");
			for (int c=0; c<WIDTH; c++)
				printf (c+1==WIDTH ? "─┤\n" : "─┼");
		};
	};
	printf (ANSI_turn_off);
};

void print_cell_types()
{
	printf ("[\n");
	// enumerate rows:
	for (int r=0; r<HEIGHT; r++)
	{
		printf ("[");
		// enumerate columns:
		for (int c=0; c<WIDTH; c++)
		{
			switch (types[get_joints_of_cell(r,c)])
			{
				case type0:
					printf ("\"0\"");
					break;
				case type2a:
					printf ("\"2a\"");
					break;
				case type2b:
					printf ("\"2b\"");
					break;
				case type3:
					printf ("\"3\"");
					break;
				case type4:
					printf ("\"4\"");
					break;
				case type_dangling:
					assert(0); // we shouldn't be here
					break;
			};
			printf (c+1==WIDTH ? "],\n" : ", ");
		};
	};
	printf ("]\n");
};

// let joints be slightly more denser
#define PROBABILITY 0.65

void gen_puzzle()
{
	int empty_cells;
	do
	{
		memset(vjoints, 0, sizeof(vjoints));
		memset(hjoints, 0, sizeof(hjoints));

		// fill joints randomly:
		for (int r=1; r<HEIGHT; r++)
			for (int c=0; c<WIDTH; c++)
				vjoints[r][c]=rand_bernoulli_distribution(PROBABILITY);

		for (int r=0; r<HEIGHT; r++)
			for (int c=1; c<WIDTH; c++)
				hjoints[r][c]=rand_bernoulli_distribution(PROBABILITY);

		remove_danglings();

		empty_cells=count_empty_cells();
	}
	while (empty_cells>20); // make it slighlty more denser
	
	//printf ("empty_cells=%d\n", empty_cells);

	print_cells(/* shuffle_rotations */ false);
	print_cells(/* shuffle_rotations */ true);
	print_cell_types();
};

int main()
{
	sgenrand (time(NULL));

	gen_puzzle();
};

