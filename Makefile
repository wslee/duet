all: main
	
main:
#	ocamlbuild -use-ocamlfind -tag debug src/main.byte
	ocamlbuild -use-ocamlfind src/main.native

clean:
	ocamlbuild -clean

.PHONY: main
