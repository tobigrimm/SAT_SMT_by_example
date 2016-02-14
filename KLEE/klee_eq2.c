int main()
{
	int circle, square, triangle;
	
	klee_make_symbolic(&circle, sizeof circle, "circle");
	klee_make_symbolic(&square, sizeof square, "square");
	klee_make_symbolic(&triangle, sizeof triangle, "triangle");

	klee_assume (circle+circle==10);
	klee_assume (circle*square+square==12);
	klee_assume (circle*square-triangle*circle==circle);

	// all constraints should be satisfied at this point
	// force KLEE to produce .err file:
	klee_assert(0);
};

