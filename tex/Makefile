MAIN := main
RULES := rules
OLD := old
DIFF := diff

LATEX_FLAGS := -jobname=$(MAIN) -shell-escape
LATEXRUN := ./latexrun -Wall --latex-cmd lualatex --latex-args "$(LATEX_FLAGS)"
LATEXDIFF := latexdiff
BIBTEX := bibtex

OTT = ott
OTTFILES = $(MAIN).ott
OTT_FLAGS = -tex_wrap false -tex_show_meta false -merge true $(OTTFILES)

MAKEDEPS  := Makefile
LATEXDEPS := main.bib
MOREDEPS := lipics-v2021.cls lipics-logo-bw.pdf cc-by.pdf orcid.pdf
GENERATED := $(RULES).tex $(MAIN).tex

all: $(MAIN).pdf

$(RULES).tex: $(OTTFILES)
	$(OTT) -o $(RULES).tex $(OTT_FLAGS)

$(MAIN).tex: $(RULES).tex $(MAIN).mng
	$(OTT) -tex_filter $(MAIN).mng $(MAIN).tex $(OTT_FLAGS)

.PHONY: FORCE
$(MAIN).pdf: $(MAIN).tex $(LATEXDEPS)
	$(LATEXRUN) $(MAIN).tex

$(DIFF).pdf: $(RULES).tex $(MAIN).mng
	$(LATEXDIFF) $(OLD).mng $(MAIN).mng > $(DIFF).mng
	$(OTT) -tex_filter $(DIFF).mng $(DIFF).tex $(OTT_FLAGS)
	$(LATEXRUN) -o $(DIFF).pdf $(DIFF).tex
	rm $(DIFF).mng $(DIFF).tex

.PHONY: clean
clean:
	$(LATEXRUN) --clean-all
	rm -f $(GENERATED)