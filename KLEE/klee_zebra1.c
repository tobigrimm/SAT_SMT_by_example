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
	if (Yellow<1 || Yellow>5) return 0;
	if (Blue<1 || Blue>5) return 0;
	if (Red<1 || Red>5) return 0;
	if (Ivory<1 || Ivory>5) return 0;
	if (Green<1 || Green>5) return 0;

	if (Norwegian<1 || Norwegian>5) return 0;
	if (Ukrainian<1 || Ukrainian>5) return 0;
	if (Englishman<1 || Englishman>5) return 0;
	if (Spaniard<1 || Spaniard>5) return 0;
	if (Japanese<1 || Japanese>5) return 0;

	if (Water<1 || Water>5) return 0;
	if (Tea<1 || Tea>5) return 0;
	if (Milk<1 || Milk>5) return 0;
	if (OrangeJuice<1 || OrangeJuice>5) return 0;
	if (Coffee<1 || Coffee>5) return 0;

	if (Kools<1 || Kools>5) return 0;
	if (Chesterfield<1 || Chesterfield>5) return 0;
	if (OldGold<1 || OldGold>5) return 0;
	if (LuckyStrike<1 || LuckyStrike>5) return 0;
	if (Parliament<1 || Parliament>5) return 0;

	if (Fox<1 || Fox>5) return 0;
	if (Horse<1 || Horse>5) return 0;
	if (Snails<1 || Snails>5) return 0;
	if (Dog<1 || Dog>5) return 0;
	if (Zebra<1 || Zebra>5) return 0;
	
	// colors are distinct for all 5 houses:
	if (((1<<Yellow) | (1<<Blue) | (1<<Red) | (1<<Ivory) | (1<<Green))!=0x3E) return 0; // 111110

	// all nationalities are living in different houses:
	if (((1<<Norwegian) | (1<<Ukrainian) | (1<<Englishman) | (1<<Spaniard) | (1<<Japanese))!=0x3E) return 0; // 111110

	// so are beverages:
	if (((1<<Water) | (1<<Tea) | (1<<Milk) | (1<<OrangeJuice) | (1<<Coffee))!=0x3E) return 0; // 111110

	// so are cigarettes:
	if (((1<<Kools) | (1<<Chesterfield) | (1<<OldGold) | (1<<LuckyStrike) | (1<<Parliament))!=0x3E) return 0; // 111110

	// so are pets:
	if (((1<<Fox) | (1<<Horse) | (1<<Snails) | (1<<Dog) | (1<<Zebra))!=0x3E) return 0; // 111110

	// main constraints of the puzzle:

	// 2.The Englishman lives in the red house.
	if (Englishman!=Red) return 0;

	// 3.The Spaniard owns the dog.
	if (Spaniard!=Dog) return 0;

	// 4.Coffee is drunk in the green house.
	if (Coffee!=Green) return 0;

	// 5.The Ukrainian drinks tea.
	if (Ukrainian!=Tea) return 0;

	// 6.The green house is immediately to the right of the ivory house.
	if (Green!=Ivory+1) return 0;

	// 7.The Old Gold smoker owns snails.
	if (OldGold!=Snails) return 0;

	// 8.Kools are smoked in the yellow house.
	if (Kools!=Yellow) return 0;

	// 9.Milk is drunk in the middle house.
	if (Milk!=3) return 0; // i.e., 3rd house

	// 10.The Norwegian lives in the first house.
	if (Norwegian!=1) return 0;

	// 11.The man who smokes Chesterfields lives in the house next to the man with the fox.
	if (Chesterfield!=Fox+1 && Chesterfield!=Fox-1) return 0; // left or right

	// 12.Kools are smoked in the house next to the house where the horse is kept.
	if (Kools!=Horse+1 && Kools!=Horse-1) return 0; // left or right

	// 13.The Lucky Strike smoker drinks orange juice.
	if (LuckyStrike!=OrangeJuice) return 0;

	// 14.The Japanese smokes Parliaments.
	if (Japanese!=Parliament) return 0;

	// 15.The Norwegian lives next to the blue house.
	if (Norwegian!=Blue+1 && Norwegian!=Blue-1) return 0; // left or right

	// all constraints are satisfied at this point
	// force KLEE to produce .err file:
	klee_assert(0);

	return 0;
};

