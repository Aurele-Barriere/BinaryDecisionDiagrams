(* Example of file when using the compiles mode *)

open Lib
open Formulas
open Prop
open Bdd

(* Pretty-printer for formulas, to be used with compiled mode *)
let print_formula fm = print_prop_formula fm; print_newline();;

let f = << ( 1 <=> 2 ) /\ ( 3 <=> 4 )>>;;
print_formula f;;

let taille = 100 in
(* initialization of tables*)
let t = init_t taille in
let ht = init_ht taille in
(* Adding a node for variable x_1, with low son 0 and high son 1 *)
let u = add t 1 0 1 in
  insert ht 1 0 1 u;

  (* Adding a node for variable x_2, with low son 1 and high son u *)
  let v = add t 2 1 u in
    insert ht 2 1 u v;
    debug_print_t t;
    debug_print_h ht 10 10;
    print_t t v "bla.dot";;


(** Inserts an new node in tableT with variable i, and the given low and high
    Returns the id of the node if it is added to the tableT or if it already exists.
    Otherwise, it returns either the id of the new node if l != h or l if l == h, according to the utility definition.
    *)
let make (t:tableT) (h:tableH) (i:variable) (low:id) (high:id) =
  try lookup h i low high with
  | CleAbsente(_) ->
      if low != high then
        let u = add t i low high in
        insert h i low high u; u
      else low ;;

let rec apply_neg (t:tableT) (h:tableH) (i:id) =
  let (var, low, high) = (var t i, low t i, high t i) in
  make t h var (apply_neg t h low) (apply_neg t h high) ;;

exception Exception_Different_Vars of (variable * variable) ;;

let rec apply (t:tableT) (h:tableH) (op:op) (i1:id) (i2:id) =
  let (var1, low1, high1) = (var t i1, low t i1, high t i1)
  and (var2, low2, high2) = (var t i2, low t i2, high t i2) in
  if var1 != var2 then raise (Exception_Different_Vars (var1, var2))
  else make t h var1 (apply t h op low1 low2) (apply t h op high1 high2) ;;

let rec build (t:tableT) (h:tableH) (p:prop formula) =
  match p with
  | False -> 0
  | True -> 1
  | Atom (P x) -> make t h x 0 1
  | Not x -> apply_neg t h (build t h x)
  | And (x, y) -> apply t h Et (build t h x) (build t h y)
  | Or (x, y) -> apply t h Ou (build t h x) (build t h y)
  | Iff (x, y) -> apply t h Equiv (build t h x) (build t h y)
  | Imp (x, y) -> apply t h Impl (build t h x) (build t h y)
