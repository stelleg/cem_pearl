
all: cem CEM.pdf 

cem: CEM.lhs Main.hs
	ghc Main.hs -o cem

CEM.pdf: CEM.lhs annotated.bib
	pdflatex CEM.lhs 
	bibtex CEM
	pdflatex CEM.lhs
	pdflatex CEM.lhs 

clean:
	rm -f cem *.o *.hi
	rm -f CEM.pdf
	rm -f CEM.aux
	rm -f CEM.log
	rm -f CEM.bbl
	rm -f CEM.blg
	rm -f CEM.out

view: CEM.pdf
	mupdf CEM.pdf
