all: byte

byte:
	ocamlbuild solver.native -use-ocamlfind

debug:
	ocamlbuild solver.d.byte -use-ocamlfind

tests: all
	ocamlbuild tests.native -use-ocamlfind
	./tests.native -runner sequential

clean:
	rm -rf _build solver.native tests.native
