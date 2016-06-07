all: byte

byte:
	ocamlbuild solver.native -use-ocamlfind

tests: all
	ocamlbuild tests.native -use-ocamlfind
	./tests.native -runner sequential

clean:
	rm -rf _build solver.native tests.native
