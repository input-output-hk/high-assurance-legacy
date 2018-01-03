async-psi.pdf: async-psi.tex
	pdflatex async-psi.tex
	bibtex async-psi
	pdflatex async-psi.tex
	pdflatex async-psi.tex

.PHONY: watch
watch:
	while inotifywait -e close_write async-psi.tex ; do make async-psi.pdf ; done

.PHONY: clean
clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.pdf
