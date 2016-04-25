# Build required librairies

all : lib.cmo formulas.cmo prop.cmo Quotexpander.cmo initialization.cmo bdd.cmo


lib.cmo: lib.ml
	ocamlc -c lib.ml

formulas.cmo: formulas.ml lib.cmo
	ocamlc -c lib.cmo formulas.ml

prop.cmo: lib.cmo formulas.cmo prop.ml
	ocamlc -w p -c lib.cmo formulas.cmo prop.ml

initialization.cmo: initialization.ml
	ocamlc -c initialization.ml

Quotexpander.cmo: Quotexpander.ml
	ocamlc -I ~/.opam/4.02.3/lib/camlp5 -c Quotexpander.ml

bdd.cmo: bdd.ml
	ocamlc -c bdd.ml

clean :
	rm -f *.cm[io]
	rm -f *~
