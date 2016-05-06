 # Use camlp5 for versions of OCaml >= 3.12 (5.15 should be ok)
# Download this from http://pauillac.inria.fr/~ddr/camlp5/

NUMS=/usr/local/lib/ocaml/nums.cma 


OCAMLVERSION = $(shell ocaml -version | sed 's/^.* //g' | cut -d"." -f1)
TL = ""
#Détection de la version
ifeq "$(OCAMLVERSION)" "4"
    TL=/usr/local/lib/ocaml/compiler-libs/ocamlcommon.cma /usr/local/lib/ocaml/compiler-libs/ocamlbytecomp.cma /usr/local/lib/ocaml/compiler-libs/ocamltoplevel.cma
else
    TL=/usr/local/lib/ocaml/toplevellib.cma
endif

OFILES= lib.cmo formulas.cmo prop.cmo initialization.cmo bdd.cmo
INCLUDE= -I ./lib 

all: libs toplevel bytecode

# Build librairies
libs: 
	make -C lib

# Build an interactive session
toplevel: init.ml
	echo '#use "init.ml";; #use "lib/initialization.ml" #install_printer print_num ;; #install_printer Lib.print_fpf ;; #install_printer Prop.print_prop_formula;;' >.ocamlinit 

# Build a bytecode executable from main.ml
bytecode:  main.ml 
	ocamlc -pp "camlp5o lib/Quotexpander.cmo" $(INCLUDE) $(NUMS) $(TL) $(OFILES)  -o main main.ml


# Clean up
clean: 	
	make -C lib clean
	rm -f *~ main main.cm[io] 
	rm -f .ocamlinit
