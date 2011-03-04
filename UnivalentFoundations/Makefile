# Edit the following parameters if the Makefile does not succeed The
# directory which contains the Coq executables (leave it empty if coqc
# is in the PATH)
COQBIN=

# Edit below at your own risk

COQLIB:=$(shell $(COQBIN)coqtop -where | sed -e 's/\\/\\\\/g')

COQLIBS:=-I . 

COQC:=$(COQBIN)coqc
COQDEP:=$(COQBIN)coqdep
COQDOC:=$(COQBIN)coqdoc

# The list of files that comprise the library in the order in which
# they should appear in the generated documentation.

VFILES:= Homotopy.v \
  HomotopyDefinitions.v \
  WeakEquivalence.v \
  ExtraPrinciples.v

VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)

.PHONY: all .depend html latex pdf

all: .depend $(VOFILES)

clean:
	/bin/rm -f *.vo *.glob *.~ doc/html/* doc/latex/*

doc: html pdf

html: $(GLOBFILES)
	$(COQDOC) --html --utf8 --charset utf8 --interpolate --no-lib-name -d doc/html $(VFILES)
	/bin/cp -f homotopy.css doc/html/coqdoc.css

latex:
	echo Would generate LaTeX

pdf: latex
	echo Would generate PDF

.depend:
	$(COQDEP) $(COQLIBS) $(VFILES) > .depend

%.vo %.glob: %.v .depend
	$(COQC) $<

include .depend