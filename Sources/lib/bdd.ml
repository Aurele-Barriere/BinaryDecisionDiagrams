open Formulas
open Prop

(* Les variables sont assimilées à leur position dans l'ordre choisi *)
type variable = int;;

(* Type des identifiants des noeuds *)
type id = int;;

(* Opérateurs binaires *)
type op = Et | Ou | Impl | Equiv ;;

(* Le type des tables t. A un id  u, associe sa variable x, son fils faible l et son fils fort h  *) 
type tableT ={ next_id : id ref; t : ( id, ( variable * id * id ) ) Hashtbl.t } ;;

(* init_t n initialise une table t vide de taille n. Pour des
   performances optimales, n devrait être proche de la taille attendue du
   tableau, mais il grossira si nécessaire. *)
let init_t n = 
  let t = { next_id = ref 2; t = Hashtbl.create n } in 
    Hashtbl.replace t.t 0 (max_int,0,0); 
    Hashtbl.replace t.t 1 (max_int,0,0); 
    t ;;

(* L'id du noeud terminal pour 0 *)
let (zero:id) = 0;;

(* L'id du noeud terminal pour 1 *)
let (one:id) = 1;;

(* test si un id est celui du terminal 0 *)
let isZero x = x=zero;;

(* test si un id est celui du terminal 1 *)
let isOne x = x=one;;

(* add t i l h  retourne un nouvel id, associé dans t à la variable i, le fils failbe l et le fils fort h *)
let add t i l h = 
  Hashtbl.add t.t !(t.next_id) (i,l,h); 
  t.next_id := !(t.next_id) + 1; 
  (!(t.next_id)-1 : id);;


exception CleAbsente of string;;

(* var t b; retourne la variable du noeud d'id b, ou lance une exception CleAbsente *)
let var t u = 
  try match (Hashtbl.find t.t u) with (i,l,h) -> i
  with
      Not_found -> raise (CleAbsente "dans la fonction var");;

(* low t b; retourne l'id du fils faible du noeud d'id b, ou lance une exception CleAbsente *)
let low t u = 
  try match (Hashtbl.find t.t u) with (i,l,h) -> l
  with
      Not_found -> raise (CleAbsente "dans la fonction low");;

(* low t b; retourne l'id du fils fort du noeud d'id b, ou lance une exception CleAbsente *)
let high t u = 
  try match (Hashtbl.find t.t u) with (i,l,h) -> h
  with
      Not_found -> raise (CleAbsente "dans la fonction high");;

(* le type des tables inverses, qui à une variable i, un fils faible l et un fils fort h, associent l'id u du noeud correspondant *)
type tableH = ((variable*id*id),id) Hashtbl.t ;;

(* init_ht n; initialise un tableau ht vide. Pour des
   performances optimales, n devrait être proche de la taille attendue du
   tableau, mais il grossira si nécessaire. *) 
let (init_ht : int -> tableH)  = fun n -> Hashtbl.create n ;; 

(* member ht i l h; retourne true si un id avec variable i, fils faible l et fils fort h existe dans ht *)
let member (h : tableH) i l hi = Hashtbl.mem h (i,l,hi);;

(*  lookup ht i l h; retourne l'id du noeud avec variable i, fils faible l et fils fort h (lance CleAbsente, s'il n'existe pas) *)
let lookup (h : tableH) i l hi = 
  try 
    Hashtbl.find h (i,l,hi)
  with  Not_found -> raise (CleAbsente "dans la fonction lookup");;

(* insert ht i l hi u; associe (i,l,h) à l'id u dans ht *)
let insert (h : tableH) i l hi u = Hashtbl.replace h (i,l,hi) u;; 

let rec aux_print_t t dl u c =
  if not (List.mem u dl)
  then
    if isZero u 
    then 
      (Printf.fprintf c "%d [shape=box,label=\"%d\"];" 0 0;
       zero::dl)
    else 
      if isOne u
      then 
	(Printf.fprintf c "%d [shape=box,label=\"%d\"];" 1 1;
	 one::dl)
      else  
	begin
	  let dl1 = aux_print_t t dl (low t u) c
	  in let dl2 = aux_print_t t dl1 (high t u) c
	  in
	    (try
	       Printf.fprintf c "%d [label=\"x%d\"];" u (var t u); 
	       Printf.fprintf c "%d -> %d;\n" u (high t u); 
	       Printf.fprintf c "%d -> %d [style=\"dashed\"];\n" u (low t u);
	     with Not_found -> ());
	    u::dl2
	end
  else dl;;

(* print_t t file; affiche le bdd de racine u, codé dans t, au format dot dans le fichier file. Ouvrir avec Graphviz. *)
let print_t t u file =  
  let c = open_out file
  in Printf.fprintf c "digraph bdd {\n"; 
    let _ = aux_print_t t [] u c in
      Printf.fprintf c "}."; 
      close_out c;;

(* debug_print_t t; affiche la table t dans stdout *)
let debug_print_t t =
  let s = ref "T:\n0 -> (MAXINT,0,0)\n1 -> (MAXINT,0,0)\n"  in
  for i = 2 to (!(t.next_id)-1) 
  do  
    try
      s := (!s)^(string_of_int i)^" -> ("^(string_of_int (var t i))^","^(string_of_int (low t i))^","^(string_of_int (high t i))^")\n"; 
    with Not_found -> ()
  done; 
  print_endline !s;; 

(* debug_print_h h max_var max_id; affiche la table h dans stdout pour var <= max_var et l,h <= max_id *)
let debug_print_h ht max_var max_id =
  let s = ref "H:\n" in
  for v = 0 to max_var 
  do 
    for l = 0 to max_id
    do
      for h = 0 to max_id
      do
	try
	  s := (!s)^"("^(string_of_int v)^","^(string_of_int l)^","^(string_of_int h)^") -> "^(string_of_int (lookup ht v l h))^"\n"; 
	with CleAbsente s -> ()
      done
    done
  done;
 print_endline !s;; 



