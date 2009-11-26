LTXALL := thesis # ...
LTXDEP := # article.sty # ...
LTXDEP_thesis := thesis.bbl thesis.bib polycode.lhs.tex \
	introduction.lhs.tex
	# agda-intro.lagda ...
LTXCLEAN := # ...
all: latex-all
again: latex-again
clean: latex-clean
distclean: latex-distclean
.PHONY: all again clean distclean

.PHONY: rec
rec:
	@if darcs w -ls ; then \
		echo "recording this patch? Ctrl+D to skip" ; \
		read && darcs rec -a -m "$(shell date '+%F %T')" ; \
	fi

include latex.mk
include lhs2TeX.mk

