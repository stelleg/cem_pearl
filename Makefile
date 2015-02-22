
all: cem.pdf 

cem.pdf: cem.tex annotated.bib
	pdflatex cem
	bibtex cem
	pdflatex cem
	pdflatex cem

clean:
	rm -f cem *.o *.hi
	rm -f cem.pdf
	rm -f cem.aux
	rm -f cem.log
	rm -f cem.bbl
	rm -f cem.blg
	rm -f cem.out

view: cem.pdf
	mupdf cem.pdf
