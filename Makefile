all: byte

byte:
	ocamlbuild solver.native -use-ocamlfind

debug:
	ocamlbuild solver.d.byte -use-ocamlfind

check: all exttests.native
	ocamlbuild tests.native -use-ocamlfind
	./tests.native 
	./exttests.native default.test

exttests: all
	ocamlbuild exttests.native -use-ocamlfind

clean:
	rm -rf _build *.native documentation.docdir \
		docs/graph*.svg graph*.svg docs/graph*.pdf graph*.pdf

graph:  
	ocamlbuild -ocamldoc \
	'ocamldoc -hide-warnings -keep-code -dot -dot-include-all -dot-reduce'\
		documentation.docdir/graph.dot -use-ocamlfind
	dot -Tsvg _build/documentation.docdir/graph.dot > \
		docs/graph.svg
	ln -sf docs/graph.svg graph.svg

graphdep:  
	ocamlbuild -ocamldoc 'ocamldoc -hide-warnings -keep-code -dot'\
		documentation.docdir/graphdep.dot -use-ocamlfind
	dot -Tsvg _build/documentation.docdir/graphdep.dot > \
		docs/graphdep.svg
	ln -sf docs/graphdep.svg graphdep.svg


graphpdf:  
	ocamlbuild -ocamldoc \
	'ocamldoc -hide-warnings -keep-code -dot -dot-include-all -dot-reduce'\
		documentation.docdir/graph.dot -use-ocamlfind
	dot -Tpdf _build/documentation.docdir/graph.dot > \
		docs/graph.pdf
	ln -sf docs/graph.pdf graph.pdf

graphdeppdf:  
	ocamlbuild -ocamldoc 'ocamldoc -hide-warnings -keep-code -dot'\
		documentation.docdir/graphdep.dot -use-ocamlfind
	dot -Tpdf _build/documentation.docdir/graphdep.dot > \
		docs/graphdep.pdf
	ln -sf docs/graphdep.pdf graphdep.pdf
