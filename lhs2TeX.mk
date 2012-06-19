#LTXALL := writeup
# ... other rules ...
#include lhs2TeX.mk

#\begin{comment}
#%include lhs2TeX.fmt
#%include polycode.fmt
#%include local.fmt
#\end{comment}

LHS2TEX_DEP ?= $(wildcard local.fmt)

# Make sure ~/.lhs2TeX points to ~/.rc/lhs2TeX !!!

%.lhs.tex: %.lhs $(LHS2TEX_DEP)
	lhs2TeX -v --include=polycode.fmt $(LHS2TEX_LHS) --poly $< > $@

%.lagda.tex: %.lagda $(LHS2TEX_DEP)
	lhs2TeX -v --include=polycode.fmt $(LHS2TEX_LAGDA) --agda --poly $< > $@

