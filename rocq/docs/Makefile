all: paper.pdf

lambdaSCE_rules.tex: lambdaSCE.ott
	ott -i lambdaSCE.ott -o lambdaSCE.tex -tex_wrap false

paper.pdf: paper.tex lambdaSCE.tex
	pdflatex paper.tex
	pdflatex paper.tex   # twice for references

clean:
	rm -f *.aux *.log *.out *.pdf