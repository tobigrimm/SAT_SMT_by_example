all: 
	rm -f *.fls
	rm -f *.log
	rm -f *.bbl
	xelatex SAT_SMT
	biber SAT_SMT
	xelatex SAT_SMT
