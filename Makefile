all: 
	rm -f *.fls
	rm -f *.log
	rm -f *.bbl
	xelatex SAT_SMT_draft-EN
	xelatex SAT_SMT_draft-EN
	xelatex SAT_SMT_draft-RU
	xelatex SAT_SMT_draft-RU

