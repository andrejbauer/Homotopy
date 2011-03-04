# A simple Makefile which helps organize generation of documents and compilation
# of Coq files. This Makefile works only if each Coq file can be compiled independently
# of the others, i.e., we do not import and file from any other file. The coq_makefile
# and coqdep utilities can be used to generate more complex Makefiles.

COQC=coqc
COQDOC=coqdoc
PDFLATEX=pdflatex

# The default target compiles the Coq files and generated the documentation.
default: *.vo doc

# A general rule explaining how to compile a .v file to .vo file.
%.vo: %.v
	$(COQC) $<

doc:
	pdflatex cheatsheet.tex
	coqdoc --latex -s --body-only -o univalence_body.tex univalence.v
	pdflatex univalence.tex
	pdflatex univalence.tex

clean:
	/bin/rm -f *~ *.{aux,log,vo,glob,out,pdf} univalence_body.tex

