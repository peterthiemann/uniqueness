all: build

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject: ;

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf
	rm -rf doc/

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@

VS := $(wildcard base/*.v) $(wildcard theories/*.v)
GLOBS := $(wildcard base/*.glob) $(wildcard theories/*.glob)

doc: build
	mkdir -p doc/html doc/tex
	coqdoc --html -d doc/html --interpolate --no-lib-name --toc `cat _CoqProject`
	coqdoc --latex -d doc/tex --interpolate --no-lib-name --body-only `cat _CoqProject` # $(VS)
	cp template.tex doc/tex/main.tex
	bash -c ' \
		cd doc/tex/; \
		pdflatex main.tex; \
		pdflatex main.tex \
	'
	mv doc/tex/main.pdf doc/doc.pdf
	# ln -s doc/html/toc.html doc/doc.html

.PHONY: all clean doc

