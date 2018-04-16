theory_files     = $(wildcard *.thy)
document_files   = $(wildcard document/*)
output_directory = output

$(output_directory)/document.pdf: ROOT $(theory_files) $(document_files)
	isabelle build -c -D .

clean:
	rm -rf $(output_directory)
.PHONY: clean

distclean: clean
	rm -f *~
.PHONY: distclean
