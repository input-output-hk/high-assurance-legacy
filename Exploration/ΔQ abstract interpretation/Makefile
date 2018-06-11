AbstractDeltaQ.pdf: AbstractDeltaQ.tex
	pdflatex AbstractDeltaQ.tex
	bibtex   AbstractDeltaQ
	pdflatex AbstractDeltaQ.tex
	pdflatex AbstractDeltaQ.tex

AbstractDeltaQ.tex: src/AbstractDeltaQ.lhs src/Util.hs
	lhs2TeX -o AbstractDeltaQ.tex src/AbstractDeltaQ.lhs

.PHONY: watch
watch:
	while inotifywait -e close_write src/AbstractDeltaQ.lhs -e close_write src/Util.hs ; do make ; done
