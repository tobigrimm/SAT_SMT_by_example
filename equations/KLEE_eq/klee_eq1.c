int main()
{
	int circle, square, triangle;
	
	klee_make_symbolic(&circle, sizeof circle, "circle");
	klee_make_symbolic(&square, sizeof square, "square");
	klee_make_symbolic(&triangle, sizeof triangle, "triangle");

	if (circle+circle!=10) return 0;
	if (circle*square+square!=12) return 0;
	if (circle*square-triangle*circle!=circle) return 0;

	// all constraints should be satisfied at this point
	// force KLEE to produce .err file:
	klee_assert(0);
};

