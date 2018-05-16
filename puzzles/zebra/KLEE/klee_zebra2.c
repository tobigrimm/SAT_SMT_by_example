int main()
{
	int Yellow, Blue, Red, Ivory, Green;
	int Norwegian, Ukrainian, Englishman, Spaniard, Japanese;
	int Water, Tea, Milk, OrangeJuice, Coffee;
	int Kools, Chesterfield, OldGold, LuckyStrike, Parliament;
	int Fox, Horse, Snails, Dog, Zebra;
	
	klee_make_symbolic(&Yellow, sizeof(int), "Yellow");
	klee_make_symbolic(&Blue, sizeof(int), "Blue");
	klee_make_symbolic(&Red, sizeof(int), "Red");
	klee_make_symbolic(&Ivory, sizeof(int), "Ivory");
	klee_make_symbolic(&Green, sizeof(int), "Green");
	
	klee_make_symbolic(&Norwegian, sizeof(int), "Norwegian");
	klee_make_symbolic(&Ukrainian, sizeof(int), "Ukrainian");
	klee_make_symbolic(&Englishman, sizeof(int), "Englishman");
	klee_make_symbolic(&Spaniard, sizeof(int), "Spaniard");
	klee_make_symbolic(&Japanese, sizeof(int), "Japanese");
	
	klee_make_symbolic(&Water, sizeof(int), "Water");
	klee_make_symbolic(&Tea, sizeof(int), "Tea");
	klee_make_symbolic(&Milk, sizeof(int), "Milk");
	klee_make_symbolic(&OrangeJuice, sizeof(int), "OrangeJuice");
	klee_make_symbolic(&Coffee, sizeof(int), "Coffee");
	
	klee_make_symbolic(&Kools, sizeof(int), "Kools");
	klee_make_symbolic(&Chesterfield, sizeof(int), "Chesterfield");
	klee_make_symbolic(&OldGold, sizeof(int), "OldGold");
	klee_make_symbolic(&LuckyStrike, sizeof(int), "LuckyStrike");
	klee_make_symbolic(&Parliament, sizeof(int), "Parliament");
	
	klee_make_symbolic(&Fox, sizeof(int), "Fox");
	klee_make_symbolic(&Horse, sizeof(int), "Horse");
	klee_make_symbolic(&Snails, sizeof(int), "Snails");
	klee_make_symbolic(&Dog, sizeof(int), "Dog");
	klee_make_symbolic(&Zebra, sizeof(int), "Zebra");

	// limits. 
	klee_assume (Yellow>=1 && Yellow<=5);
	klee_assume (Blue>=1 && Blue<=5);
	klee_assume (Red>=1 && Red<=5);
	klee_assume (Ivory>=1 && Ivory<=5);
	klee_assume (Green>=1 && Green<=5);

	klee_assume (Norwegian>=1 && Norwegian<=5);
	klee_assume (Ukrainian>=1 && Ukrainian<=5);
	klee_assume (Englishman>=1 && Englishman<=5);
	klee_assume (Spaniard>=1 && Spaniard<=5);
	klee_assume (Japanese>=1 && Japanese<=5);

	klee_assume (Water>=1 && Water<=5);
	klee_assume (Tea>=1 && Tea<=5);
	klee_assume (Milk>=1 && Milk<=5);
	klee_assume (OrangeJuice>=1 && OrangeJuice<=5);
	klee_assume (Coffee>=1 && Coffee<=5);

	klee_assume (Kools>=1 && Kools<=5);
	klee_assume (Chesterfield>=1 && Chesterfield<=5);
	klee_assume (OldGold>=1 && OldGold<=5);
	klee_assume (LuckyStrike>=1 && LuckyStrike<=5);
	klee_assume (Parliament>=1 && Parliament<=5);

	klee_assume (Fox>=1 && Fox<=5);
	klee_assume (Horse>=1 && Horse<=5);
	klee_assume (Snails>=1 && Snails<=5);
	klee_assume (Dog>=1 && Dog<=5);
	klee_assume (Zebra>=1 && Zebra<=5);
	
	// colors are distinct for all 5 houses:
	klee_assume (((1<<Yellow) | (1<<Blue) | (1<<Red) | (1<<Ivory) | (1<<Green))==0x3E); // 111110

	// all nationalities are living in different houses:
	klee_assume (((1<<Norwegian) | (1<<Ukrainian) | (1<<Englishman) | (1<<Spaniard) | (1<<Japanese))==0x3E); // 111110

	// so are beverages:
	klee_assume (((1<<Water) | (1<<Tea) | (1<<Milk) | (1<<OrangeJuice) | (1<<Coffee))==0x3E); // 111110

	// so are cigarettes:
	klee_assume (((1<<Kools) | (1<<Chesterfield) | (1<<OldGold) | (1<<LuckyStrike) | (1<<Parliament))==0x3E); // 111110

	// so are pets:
	klee_assume (((1<<Fox) | (1<<Horse) | (1<<Snails) | (1<<Dog) | (1<<Zebra))==0x3E); // 111110

	// main constraints of the puzzle:

	// 2.The Englishman lives in the red house.
	klee_assume (Englishman==Red);

	// 3.The Spaniard owns the dog.
	klee_assume (Spaniard==Dog);

	// 4.Coffee is drunk in the green house.
	klee_assume (Coffee==Green);

	// 5.The Ukrainian drinks tea.
	klee_assume (Ukrainian==Tea);

	// 6.The green house is immediately to the right of the ivory house.
	klee_assume (Green==Ivory+1);

	// 7.The Old Gold smoker owns snails.
	klee_assume (OldGold==Snails);

	// 8.Kools are smoked in the yellow house.
	klee_assume (Kools==Yellow);

	// 9.Milk is drunk in the middle house.
	klee_assume (Milk==3); // i.e., 3rd house

	// 10.The Norwegian lives in the first house.
	klee_assume (Norwegian==1);

	// 11.The man who smokes Chesterfields lives in the house next to the man with the fox.
	klee_assume (Chesterfield==Fox+1 || Chesterfield==Fox-1); // left or right

	// 12.Kools are smoked in the house next to the house where the horse is kept.
	klee_assume (Kools==Horse+1 || Kools==Horse-1); // left or right

	// 13.The Lucky Strike smoker drinks orange juice.
	klee_assume (LuckyStrike==OrangeJuice);

	// 14.The Japanese smokes Parliaments.
	klee_assume (Japanese==Parliament);

	// 15.The Norwegian lives next to the blue house.
	klee_assume (Norwegian==Blue+1 || Norwegian==Blue-1); // left or right

	// all constraints are satisfied at this point
	// force KLEE to produce .err file:
	klee_assert(0);
};

