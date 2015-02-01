
all: cem

cem: cem.lhs
	ghc cem.lhs

cem.pdf: cem.lhs annotated.bib
	pdflatex cem.lhs
	bibtex paper
	pdflatex cem.lhs
	pdflatex cem.lhs

clean:
	rm -f cem *.o *.hi
	rm -f paper.pdf
	rm -f paper.aux
	rm -f paper.log
	rm -f paper.bbl
	rm -f paper.blg

view: paper.pdf
	mupdf paper.pdf
