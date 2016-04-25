(* Fichier d'initialisation du top level *)
#load "nums.cma";;                           

Topdirs.dir_directory "+camlp5";
Topdirs.dir_load Format.std_formatter "camlp5o.cma";;
#directory "lib";;

#use "lib/initialization.ml";; 
#use "lib/Quotexpander.ml";; 
#load "lib/lib.cmo";;
#load "lib/formulas.cmo";;
#load "lib/prop.cmo";;
#load "lib/bdd.cmo";;

open Lib ;;  
open Formulas ;;
open Prop ;;
open Bdd ;;
