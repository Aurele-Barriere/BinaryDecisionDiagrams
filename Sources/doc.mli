(********************************************************************************************)
(*                                                                                          *)
(*                   Types et fonctions pour manipuler les formules                         *)
(*                                                                                          *)
(********************************************************************************************)

(* Type pour les formules *)
type 'a formula =
    False
  | True
  | Atom of 'a
  | Not of 'a formula
  | And of 'a formula * 'a formula
  | Or of 'a formula * 'a formula
  | Imp of 'a formula * 'a formula
  | Iff of 'a formula * 'a formula

(* Type des variables propositionelles dans les formules *)
type prop = P of int;;

(* Printer pour les variables propositionelles, à ne PAS utiliser en toplevel *)
val print_prop_formula : prop formula -> unit 

(* Renvoie l'ensemble des variables propositionnelles d'une formule *)
val atoms : 'a formula -> 'a list

(* Vérifie si une formule est une tautologie, algorithme naif *)
val tautology : 'a formula -> bool

(* Vérifie si une formule est satisfiable, algorithme naif *)
val satisfiable : 'a formula -> bool

(* Affiche le temps de calcul d'une fonction sur un argument et renvoie le résultat *) 
val time : ('a -> 'b) -> 'a -> 'b


(********************************************************************************************)
(*                                                                                          *)
(*                   Types and functions to represent BDDs with tables                      *)
(*                                                                                          *)
(********************************************************************************************)
  

(* Les variables sont assimilées à leur position dans l'ordre choisi *)
type variable = int

(* Type des identifiants des noeuds *)
type id = int

(* Opérateurs binaires *)
type op = Ou | Et | Impl | Equiv

(* Le type des tables t. A un id  u, associe sa variable x, son fils faible l et son fils fort h  *) 
type tableT


(* exception utilisée lors d'accès incorrects dans les tables T et H *)
exception CleAbsente of string


(* init_t n initialise une table t vide de taille n. Pour des
   performances optimales, n devrait être proche de la taille attendue du
   tableau, mais il grossira si nécessaire. *)
val init_t : int -> tableT

(* L'id du noeud terminal pour 0 *)
val zero : id

(* L'id du noeud terminal pour 1 *)
val one : id

(* test si un id est celui du terminal 0 *)
val isZero : id -> bool

(* test si un id est celui du terminal 1 *)
val isOne : id -> bool

(* add t i l h  retourne un nouvel id, associé dans t à la variable i, le fils failbe l et le fils fort h *)
val add : tableT -> variable -> id -> id -> id

(* var t b; retourne la variable du noeud d'id b *)
val var : tableT -> id -> variable

(* low t b; retourne l'id du fils faible du noeud d'id b *)
val low : tableT -> id -> id

(* high t b; retourne l'id du fils fort du noeud d'id b *)
val high : tableT -> id -> id


(* le type des tables inverses, qui à une variable i, un fils faible l et un fils fort h, associent l'id u du noeud correspondant *)
type tableH


(* init_ht n; initialise un tableau ht vide. Pour des
   performances optimales, n devrait être proche de la taille attendue du
   tableau, mais il grossira si nécessaire. *) 
val init_ht : int -> tableH

(* member ht i l h; retourne true si un id avec variable i, fils faible l et fils fort h existe dans ht *)
val member : tableH -> variable -> id -> id -> bool

(*  lookup ht i l h; retourne l'id du noeud avec variable i, fils faible l et fils fort h (lance CleAbsente, s'il n'existe pas) *)
val lookup : tableH -> variable -> id -> id -> id

(* insert ht i l hi u; associe (i,l,h) à l'id u dans ht *)
val insert: tableH -> variable -> id -> id -> id -> unit

(* print_t t file; affiche le bdd de racine u, codé dans t, au format dot dans le fichier file. Ouvrir avec Graphviz. *)
val print_t : tableT -> id -> string -> unit

(* debug_print_t t; affiche la table t dans stdout *)
val debug_print_t : tableT -> unit

(* debug_print_h h max_var max_id; affiche la table h dans stdout pour var <= max_var et l,h <= max_id *)
val debug_print_h : tableH -> int -> int -> unit
