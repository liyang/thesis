TEXT := thesis.tex introduction.lhs stm.lhs semantics.tex \
	testing.lhs model.lhs agda.lagda nondet.lagda concurrency.lagda \
	verified.lagda conclusion.tex

LTXALL := thesis # ...
LTXDEP := # article.sty # ...
LTXDEP_thesis := thesis.bbl thesis.bib polycode.lhs.tex \
	$(filter-out thesis.tex,$(patsubst %.tex.tex,%.tex,$(TEXT:=.tex)))
LTXCLEAN := # ...
all: now latex-all now.png
again: latex-again
clean: latex-clean
distclean: latex-distclean
.PHONY: all again clean distclean

RSYNC := rsync --verbose --progress --8-bit-output --human-readable \
	--partial --compress --copy-links --perms --times --modify-window=1
DATETIME := $(shell date '+%F %T')

agda.lagda.tex: agda.fmt

# thesis.bib: $(patsubst %.tex.aux,%.aux,$(TEXT:=.aux))
# 	cat $^ | bibtool -s -x > $@

.PHONY: now
now:
	echo "$(DATETIME)" > $@

now.wc: $(TEXT)
	[ wordcount.wc -nt $@ ] && cp wordcount.wc $@ || true
	echo "$(DATETIME) $$(texcount.pl -1 -sum $(TEXT))" >> $@

.PHONY: rec upload
wordcount.wc: $(TEXT)
	echo "$(DATETIME) $$(texcount.pl -1 -sum $(TEXT))" >> $@
%.png: %.wc
	thesisometer $^ 2>/dev/null
upload: thesis.pdf wordcount.png wordcount-recent.png
	@chmod 644 $^
	$(RSYNC) --rsync-path=local/bin/rsync $^ marian.cs.nott.ac.uk:public_html/
rec: wordcount.wc upload
	@if darcs w | tee changes ; then \
		echo "record this patch? Ctrl+D to skip" ; \
		read && darcs rec -a --edit-long-comment -m "$(DATETIME)" && darcs push ; \
	fi

include latex.mk
include lhs2TeX.mk

