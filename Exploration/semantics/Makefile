OuroborosSpec.pdf: *.tex *.bib
	pdflatex OuroborosSpec
	bibtex OuroborosSpec
	pdflatex OuroborosSpec
	pdflatex OuroborosSpec

.PHONY: clean
clean:
	rm -f *.aux *.bbl *.blg *.log

# vi:set noexpandtab:
