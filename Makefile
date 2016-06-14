all: byte

byte:
	ocamlbuild solver.native -use-ocamlfind

debug:
	ocamlbuild solver.d.byte -use-ocamlfind

tests: all
	ocamlbuild tests.native -use-ocamlfind
	./tests.native -runner sequential

clean:
	rm -rf _build solver.native tests.native documentation.docdir \
		docs/graph*.pdf graph*.pdf

graph:  
	ocamlbuild -ocamldoc \
		'ocamldoc -keep-code -dot -dot-include-all -dot-reduce'\
		documentation.docdir/graph.dot -use-ocamlfind
	dot -Tpdf _build/documentation.docdir/graph.dot > \
		docs/graph.pdf
	ln -sf docs/graph.pdf graph.pdf

graphdep:  
	ocamlbuild -ocamldoc 'ocamldoc -keep-code -dot'\
		documentation.docdir/graphdep.dot -use-ocamlfind
	dot -Tpdf _build/documentation.docdir/graphdep.dot > \
		docs/graphdep.pdf
	ln -sf docs/graphdep.pdf graphdep.pdf
