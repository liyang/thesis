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

RSYNC := rsync --verbose --progress --8-bit-output --human-readable \
	--partial --compress --copy-links --perms --times --modify-window=1

.PHONY: rec upload
upload: all
	@chmod 644 thesis.pdf
	$(RSYNC) --rsync-path=local/bin/rsync thesis.pdf marian.cs.nott.ac.uk:public_html/
rec: upload
	@if darcs w | tee changes ; then \
		echo "recording this patch? Ctrl+D to skip" ; \
		read && darcs rec -a --edit-long-comment -m "$(shell date '+%F %T')" ; \
	fi

include latex.mk
include lhs2TeX.mk

