
all: cem CEM.pdf 

cem: CEM.lhs Main.hs
	ghc Main.hs -o cem

CEM.pdf: CEM.lhs annotated.bib
	cp -f CEM.lhs CEM.tex
	pdflatex CEM
	bibtex CEM
	pdflatex CEM
	pdflatex CEM

clean:
	rm -f cem *.o *.hi
	rm -f CEM.tex
	rm -f CEM.pdf
	rm -f CEM.aux
	rm -f CEM.log
	rm -f CEM.bbl
	rm -f CEM.blg
	rm -f CEM.out

view: CEM.pdf
	mupdf CEM.pdf
