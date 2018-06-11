PDFLATEX=pdflatex -halt-on-error
BIBTEX=bibtex

async-psi.pdf: async-psi.tex
	${PDFLATEX} async-psi.tex
	${BIBTEX}   async-psi
	${PDFLATEX} async-psi.tex
	${PDFLATEX} async-psi.tex

.PHONY: watch
watch:
	while inotifywait -e close_write async-psi.tex ; do make async-psi.pdf ; done

.PHONY: clean
clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.pdf
