Praos.pdf: Praos.tex references.bib
	pdflatex Praos.tex
	bibtex Praos
	pdflatex Praos.tex
	pdflatex Praos.tex

Praos.tex: Praos.lhs
	lhs2TeX -o Praos.tex Praos.lhs

.PHONY: clean
clean:
	rm -f *.aux *.bbl *.blg *.log *.ptb *.tex *.pdf *.toc

.PHONY: ghcid
ghcid:
	ghcid --command='cabal new-repl praos'

# watch the .lhs file and call make whenever it changes
.PHONE: watch
watch:
	while inotifywait -e close_write Praos.lhs -e close_write references.bib ; do make ; done
