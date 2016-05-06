(* Example of file when using the compiles mode *)

open Lib
open Formulas
open Prop
open Bdd


(* Pretty-printer for formulas, to be used with compiled mode *)
let print_formula fm = print_prop_formula fm; print_newline();;

let f = << ( 1 <=> 2 ) /\ ( 3 <=> 4 )>>;;
print_formula f;;

let max a b = if a>b then a else b;;
let min a b = if a<b then a else b;;


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


(* Recursively applying the negation *)
let rec apply_neg (t:tableT) (h:tableH) (i:id) =
  match i with
  | 0 -> 1
  | 1 -> 0
  | _ ->
    let (var, low, high) = (var t i, low t i, high t i) in
    make t h var (apply_neg t h low) (apply_neg t h high) ;;

(* Constructing the resulting ROBDD with an operator and 2 graphs.
   We must use as root the var with the higher label to keep the order.
*)
let rec apply (t:tableT) (h:tableH) (op:op) (i1:id) (i2:id) =
  if (isZero(i1) || isOne(i1)) && (isZero(i2) || isOne(i2)) then
    match op with
    | Et -> min i1 i2
    | Ou -> max i1 i2
    | Impl -> max (1 - i1) i2
    | Equiv -> if i1 = i2 then 1 else 0
  else
    let _ = assert(op <> Impl) in
      let (var1, low1, high1) = (var t i1, low t i1, high t i1)
      and (var2, low2, high2) = (var t i2, low t i2, high t i2) in
      if var1 > var2 then
        make t h var2 (apply t h op i1 low2) (apply t h op i1 high2)
      else if var2 > var1 then
        make t h var1 (apply t h op low1 i2) (apply t h op high1 i2)
      else (* var1 == var2 *)
        make t h var1 (apply t h op low1 low2) (apply t h op high1 high2)
;;
(*
(*Ceci est la fonction de Florestan. Elle fonctionne parfaitement. *)
let apply (tT : tableT) (tH : tableH) (opS : op) (u : id) (uu : id) : id =
  let rec apply_aux tT tH v vv =
    if ((isOne v) && (isOne vv)) || ((isZero v) && (isOne vv))
      || ((isOne v) && (isZero vv)) || ((isZero v) && (isZero vv))
      then match opS with
      | Ou -> if (isOne v) || (isOne vv) then one else zero
      | Et -> if (isOne v) && (isOne vv) then one else zero
      | Impl -> if (isZero v) || (isOne vv) then one else zero
      | Equiv -> if v = vv then one else zero
    else begin
      let a = var tT v and b = var tT vv in
      if a = b
        then make tT tH a
          (apply_aux tT tH (low tT v) (low tT vv))
          (apply_aux tT tH (high tT v) (high tT vv))
      else if a < b
        then make tT tH a
          (apply_aux tT tH (low tT v) vv)
          (apply_aux tT tH (high tT v) vv)
      else make tT tH b
          (apply_aux tT tH v (low tT vv))
          (apply_aux tT tH v (high tT vv))
    end
  in apply_aux tT tH u uu;; *)

(* Creating a ROBDD with a formula.
   Returns the root *)
let rec build (t:tableT) (h:tableH) (p:prop formula) =
  match p with
  | False -> 0
  | True -> 1
  | Atom (P x) -> make t h x 0 1
  | Not x -> apply_neg t h (build t h x)
  | And (x, y) -> apply t h Et (build t h x) (build t h y)
  | Or (x, y) -> apply t h Ou (build t h x) (build t h y)
  | Iff (x, y) -> apply t h Equiv (build t h x) (build t h y)
  | Imp (x, y) -> apply t h Ou (build t h (Not x)) (build t h y)

(* A ROBDD is sat if there is the node 1 somewhere *)
let rec sat (t:tableT) (i:id) =
  match i with
  | 0 -> false
  | 1 -> true
  | _ ->
    let (l, h) = (low t i, high t i) in
    sat t l || sat t h ;;

(* A ROBDD is a tautology if all final nodes are 1s *)
let rec valid (t:tableT) (i:id) =
  match i with
  | 0 -> false
  | 1 -> true
  | _ ->
    let (l, h) = (low t i, high t i) in
    valid t l && valid t h ;;

exception Exception_Not_Satisfiable

(* To return a valuation, we construct it as we go through the graph
   We modify it when we change branches.
   We return it when a 1 is found *)
let anysat (t:tableT) (i:id) =
  let rec f (t:tableT) (i:id) (lst:(variable * bool) list) =
    match i with
    | 0 -> raise Exception_Not_Satisfiable
    | 1 -> lst
    | _ ->
      let (l, h) = (low t i, high t i) in
      try (var t i, false)::(f t l lst) with
      | Exception_Not_Satisfiable -> (var t i, true)::(f t h lst)
  in
  f t i [] ;;

(* For a column i, there must be only one queen *)
let nqueens_column n i =
  let formula = ref False in
  for j = 0 to n-1 do
    let formula_t = ref True in
    for j' = 0 to n-1 do
      formula_t := And(!formula_t, if j=j' then Atom(P(i+n*j)) else Not(Atom(P(i+n*j'))))
    done;
    formula := Or(!formula_t, !formula)
  done;
  !formula ;;

(* For a line j, there must be only one queen *)
let nqueens_line n j =
  let formula = ref False in
  for i = 0 to n-1 do
    let formula_t = ref True in
    for i' = 0 to n-1 do
      formula_t := And(!formula_t, if i=i' then Atom(P(i+n*j)) else Not(Atom(P(i'+n*j))))
    done;
    formula := Or(!formula_t, !formula)
  done;
  !formula ;;

(* For the k rising diagonal, if there is a queen, there are no queen elsewhere on the diagonal *)
let nqueens_diag1 n k =
  let formula = ref True in
  for i = (max 0 (k-n+1)) to (min k (n-1)) do
    let formula_t = ref True in
    for i' = (max 0 (k-n+1)) to (min k (n-1)) do
      let j = k-i' in
      if i<>i' then
      formula_t := And(!formula_t, Not(Atom(P(i'+n*j))))
    done;
    let j = k-i in
    formula_t := Or(!formula_t, Not(Atom(P(i+n*j))));
    formula := And(!formula_t, !formula)
  done;
  !formula ;;

(* For the k receding diagonal, if there is a queen, there are no queen elsewhere on the diagonal *)
let nqueens_diag2 n k =
  let formula = ref True in
  for i = (max 0 (k-n+1)) to (min k (n-1)) do
    let formula_t = ref True in
    for i' = (max 0 (k-n+1)) to (min k (n-1)) do
      let j = i'-k+n-1 in
      if i<>i' then
      formula_t := And(!formula_t, Not(Atom(P(i'+n*j))))
    done;
    let j = i-k+n-1 in
    formula_t := Or(!formula_t, Not(Atom(P(i+n*j))));
    formula := And(!formula_t, !formula)
  done;
  !formula ;;

(* Creating the formula for n queens *)
let nqueens_formula n =
  let formula = ref True in
  for i = 0 to n-1 do
    formula := And(!formula, nqueens_line n i);
    formula := And(!formula, nqueens_column n i)
  done;
  for k = 1 to (2*n)-3 do 
    (*the first ans last diagonals only have one square, thus do not ne    ed to add their formula *)
    formula := And(!formula, nqueens_diag1 n k);
    formula := And(!formula, nqueens_diag2 n k)
  done;
  !formula ;;

(* Creating the formula then resolving it *)
let nqueens n =
  let formula = nqueens_formula n in
  let t = init_t 2000 and h = init_ht 2000 in
  let id = build t h formula in
  anysat t id;;

(* Printing a solution to the nqueens problem *)
let print_sol_nqueens n sol =
  for i = 0 to n-1 do
    for j = 0 to n-1 do
      try
      print_string (if assoc (i+n*j) sol then "1" else "0")
      with
      |Failure("find") -> print_string "?"
    done;
    print_newline ()
  done;
  () ;;


let _ =
  for i = 1 to 8 do
    try
      print_int i; print_string " queens"; print_newline ();
      let result = nqueens i in
      print_sol_nqueens i result
    with
    | Exception_Not_Satisfiable -> print_string "not satisfiable"; print_newline ();
  done;
  () ;;
