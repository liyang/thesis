TEXT := thesis.tex introduction.lhs stm.lhs semantics.tex \
	testing.lhs model.lhs agda.lagda nondet.lagda fork.lagda \
	verified.lagda conclusion.tex

LTXALL := thesis # ...
LTXDEP := # article.sty # ... thesis.bbl
LTXDEP_thesis := now.tex polycode.lhs.tex \
	$(filter-out thesis.tex,$(patsubst %.tex.tex,%.tex,$(TEXT:=.tex)))
LTXCLEAN := # ...
LHS2TEX_DEP := haskell.fmt agda.fmt

LHS2TEX_LHS := --include=haskell.fmt
LHS2TEX_LAGDA := --include=agda.fmt

all: latex-all
again: latex-again
clean: latex-clean
distclean: latex-distclean
.PHONY: all again clean distclean

RSYNC := rsync --verbose --progress --8-bit-output --human-readable \
	--partial --compress --copy-links --perms --times --modify-window=1
DATETIME := $(shell date '+%F %T')

agda.lagda.tex nondet.lagda.tex fork.lagda.tex verified.lagda.tex: agda.fmt
model.lhs.tex testing.lhs.tex: haskell.fmt
nondet.lagda.tex: NonDet/introduction.lagda.tex NonDet/Language.lagda.tex \
	NonDet/Machine.lagda.tex NonDet/justification.lagda.tex \
	NonDet/Combined.lagda.tex NonDet/Bisimilarity.lagda.tex \
	NonDet/ElideTau.lagda.tex

fork.lagda.tex: Fork/Action.lagda.tex Fork/Language.lagda.tex \
	Fork/Combined.lagda.tex Fork/Soup.lagda.tex \
	Fork/Bisimilarity.lagda.tex Fork/ElideTau.lagda.tex \
	Fork/Concat.lagda.tex

verified.lagda.tex: Verified/Heap.lagda.tex Verified/Action.lagda.tex \
	Verified/Language.lagda.tex Verified/Commit.lagda.tex \
	Verified/Lemmas.lagda.tex Verified/InspectExp.lagda.tex \
	Verified/Completeness.lagda.tex Verified/Soundness.lagda.tex

polycode.lhs.tex: LHS2TEX_LHS=

thesis.cites: *.aux
	grep -h '^\\citation{[a-zA-Z0-9-]\{2,\}}$$' $^ | sort | uniq > $@

# thesis.bib: $(patsubst %.tex.aux,%.aux,$(TEXT:=.aux))
# 	cat $^ | bibtool -s -x > $@

.PHONY: now.tex
now.tex:
	/bin/echo -n "\def\rightnow{$(DATETIME)}" > $@

now.wc: $(TEXT)
	[ wordcount.wc -nt $@ ] && cp wordcount.wc $@ || true
	echo "$(DATETIME) $$(texcount.pl -1 -sum $(TEXT))" >> $@

.PHONY: rec upload
wordcount.wc: $(TEXT)
	echo "$(DATETIME) $$(texcount.pl -1 -sum $(TEXT))" >> $@
%.png: %.wc
	thesisometer $^ 2>/dev/null
# wordcount.png wordcount-recent.png
upload: thesis.pdf
	@chmod 644 $^
	$(RSYNC) --rsync-path=local/bin/rsync $^ marian.cs.nott.ac.uk:public_html/
rec: wordcount.wc upload
	@if darcs w | tee changes ; then \
		echo "record this patch? Ctrl+D to skip" ; \
		read && darcs rec -a --edit-long-comment -m "$(DATETIME)" && darcs push ; \
	fi

include latex.mk
include lhs2TeX.mk

