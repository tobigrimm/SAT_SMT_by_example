all: 
	rm -f *.fls
	rm -f *.log
	rm -f *.bbl
	xelatex SAT_SMT_by_example-EN
	xelatex SAT_SMT_by_example-EN
	xelatex SAT_SMT_by_example-RU
	xelatex SAT_SMT_by_example-RU

