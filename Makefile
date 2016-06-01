all: byte

byte:
	ocamlbuild smtlib.native -use-ocamlfind
