#
# Makefile template
#

#LTXALL := writeup # ...
#LTXDEP := article.sty # ...
#LTXDEP_writeup := appendix.tex # ...
#LTXCLEAN := # ...
#all: latex-all
#again: latex-again
#clean: latex-clean
#distclean: latex-distclean
#.PHONY: all again clean distclean
##
## ... other rules ...
##
#include latex.mk


#
# LaTeX definitions
#
PSLATEX ?= latex --interaction=nonstopmode
PDFLATEX ?= pdflatex --interaction=nonstopmode
BIBTEX ?= bibtex
BIBSHELF ?= ~/Documents/Bookshelf/Bookshelf.bib
DVIPS ?= odvips -t a4
DVIPDF ?= dvipdfm -p a4
LATEX_FORMAT ?= pdf
PDF_VIEWER ?= evince

# compatibility
ifneq ($(LATEX_CLEAN),)
$(warning ********************************)
$(warning **** LATEX_CLEAN deprecated ****)
$(warning ********************************)
LTXCLEAN ?= $(LATEX_CLEAN)
endif
ifneq ($(LATEX_CLEAN_EXTRA),)
$(warning **************************************)
$(warning **** LATEX_CLEAN_EXTRA deprecated ****)
$(warning **************************************)
LTXCLEAN ?= $(LATEX_CLEAN_EXTRA)
endif
ifneq ($(DOCUMENTS),)
$(warning ******************************)
$(warning **** DOCUMENTS deprecated ****)
$(warning ******************************)
LTXALL ?= $(DOCUMENTS)
endif

# fix for make (< 3.80), where $(eval ...) is broken
LATEX_TMP ?= /tmp/latex.mk


#
# LaTeX rules
#

define latex-tmp-begin # 1:program 2:input
	$(eval LATEX_TMP := /tmp/$(notdir $(firstword $(1)))-$(basename $(notdir $(2))))
	@rm -rf "$(LATEX_TMP)"
	@mkdir "$(LATEX_TMP)"
endef

define latex-tmp-end # 1:output ; expects LATEX_TMP to be defined
	@mv -f "$(LATEX_TMP)"/* "$(1)" ; rmdir "$(LATEX_TMP)"
	$(eval LATEX_TMP :=)
endef

# Delete (and so remake next round) the .bbl if citations have changed
# Also keep the current .cites rather than one with a newer timestamp
define latex-typeset # 1:program 2:input
	$(call latex-tmp-begin,$(1),$(2))
	cd "$(dir $(2))" && $(1) -output-directory="$(LATEX_TMP)" "$(notdir $(2))"
	$(call latex-tmp-end,$(dir $(2)))
endef
# This clearly does not work for documents with multiple source files.
#	@if grep '^\\citation{.*}$$' "$(LATEX_TMP)/$(basename $(notdir $(2))).aux" | tee "$(LATEX_TMP)/$(basename $(notdir $(2))).cites" | cmp -s - "$(basename $(2)).cites" ; \
#		then rm -f "$(LATEX_TMP)/$(basename $(notdir $(2)))".{cites,bbl} ; \
#		else echo -e "\n\n*** Citations changed! Redo from start? ***\n" ; rm -f "$(basename $(2)).bbl" ; fi

define latex-postconvert # 1:program 2:input 3:output
	$(call latex-tmp-begin,$(1),$(2))
	$(1) -o "$(LATEX_TMP)/$(notdir $(3))" "$(2)"
	$(call latex-tmp-end,$(dir $(3)))
endef

%.ps: %.dvi
	$(call latex-postconvert,$(DVIPS),$<,$@)

%.eps: %.dvi
	$(call latex-postconvert,$(DVIPS) -E,$<,$@)

%.pdf: %.tex
	$(call latex-typeset,$(PDFLATEX),$<)

%.dvi: %.tex
	$(call latex-typeset,$(PSLATEX),$<)

define latex-sanitise # 1:name
$(shell echo "$(1)" | sed -e "s/[^0-9A-Za-z]/_/g")
endef

define latex-depend # 1:name
$(1).pdf: $$(LTXDEP_$(call latex-sanitise,$(1))) $$(LTXDEP)
$(1).dvi: $$(LTXDEP_$(call latex-sanitise,$(1))) $$(LTXDEP)
endef
$(foreach DOC,$(LTXALL),$(eval $(call latex-depend,$(DOC))))

# Make a dummy .bbl if there is no corresponding .aux file.
# Otherwise if there is no .bbl *or* if the .aux is newer than the .bbl, invoke bibtex.
%.bbl: %.bib
	if [ ! -e "$(@:.bbl=.aux)" ] ; then \
		touch "$@" ; \
	elif [ ! -e "$@" -o "$(@:.bbl=.aux)" -nt "$@" ] ; then \
		$(BIBTEX) "$(@:.bbl=.aux)" ; \
	fi

%.cites:
	@[ -e "$@" ] || touch "$@"

%.bib: %.cites $(BIBSHELF)
	bibtool -s -x $^ > $@


#
# LaTeX targets
#

latex-again:: latex-clean all

LATEX_EMPTY :=
LATEX_SPACE := $(LATEX_EMPTY) $(LATEX_EMPTY)
LATEX_COMMA := ,

define latex-brace # 1:name(s)
$(if $(findstring $(LATEX_SPACE),$(strip $(1))),{$(subst $(LATEX_SPACE),$(LATEX_COMMA),$(strip $(1)))},$(strip $(1)))
endef
LATEX_DOCUMENT_LIST := $(call latex-brace,$(LTXALL))

.PHONY: latex-all latex-clean-output latex-clean-custom latex-clean-intermediate latex-clean latex-distclean
latex-all: $(addsuffix .$(LATEX_FORMAT),$(LTXALL))

latex-reload:
	@case "$$(bash -c 'echo $$OSTYPE')" in \
	(linux-gnu) \
		for doc in $(LTXALL:=.pdf) ; do \
			pgrep -u "$$USER" -fx "$$(echo "$(PDF_VIEWER) $$doc" | quoteregex)" > /dev/null && $(PDF_VIEWER) $$doc ; \
		done || true ;; \
	esac

latex-clean-output:
	rm -f $(LATEX_DOCUMENT_LIST).{dvi,pdf,ps}

latex-clean-custom:
	rm -f $(LTXCLEAN)

latex-clean-intermediate:
	rm -f comment.cut $(LATEX_DOCUMENT_LIST).{ofl,log,aux,toc,bbl,cites,out,blg,nav,ptb,snm,vrb}

latex-clean: latex-clean-output
latex-distclean: latex-clean-output latex-clean-custom latex-clean-intermediate

