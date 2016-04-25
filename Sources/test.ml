
(* Example of file when using the toplevel *) 

let taille_table = 10;;

(* initialization of tables*)
let t = init_t taille_table;;
let ht = init_ht taille_table;;

(* Adding a node for variable x_1, with low son 0 and high son 1 *)
let u = add t 1 0 1;;
insert ht 1 0 1 u;;

(* Adding a node for variable x_2, with low son 1 and high son u *)
let v = add t 2 1 u;;
insert ht 2 1 u v;;

member ht 2 1 u;;
lookup ht 2 1 u;;
member ht 1 0 1;;
lookup ht 1 0 1;;
member ht 1 1 1;;

var t v;;
low t v;;
high t v;;

debug_print_t t;;
debug_print_h ht 10 10;;

print_t t v "bla.dot";;


let f = << ( 1 <=> 2 ) /\ ( 3 <=> 4 )>>;;    
satisfiable f;;
