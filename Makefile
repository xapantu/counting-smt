all: byte

byte:
	ocamlbuild solver.native -use-ocamlfind

tests: all
	ocamlbuild tests.native -use-ocamlfind
	./tests.native -runner sequential

clean:
	rm -r _build solver.native tests.native
