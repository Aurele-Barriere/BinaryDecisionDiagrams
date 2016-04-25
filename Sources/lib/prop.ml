open Lib
open Formulas

(* ========================================================================= *)
(* Basic stuff for propositional logic: datatype, parsing and printing.      *)
(* ========================================================================= *)

type prop = P of int;;

let pname(P s) = s;;

(* ------------------------------------------------------------------------- *)
(* Parsing of propositional formulas.                                        *)
(* ------------------------------------------------------------------------- *)

let parse_propvar vs inp =
  match inp with
      p::oinp when p <> "(" ->
	(try
	   let var = int_of_string p
	   in
	     (Atom(P(var)),oinp)
	 with
	     Failure(s) -> raise (Failure "Variables must be integers"))
    | _ -> failwith "parse_propvar";;

let parse_prop_formula = make_parser
  (parse_formula ((fun _ _ -> failwith ""),parse_propvar) []);;

(* ------------------------------------------------------------------------- *)
(* Set this up as default for quotations.                                    *)
(* ------------------------------------------------------------------------- *)

let default_parser = parse_prop_formula;;

(* ------------------------------------------------------------------------- *)
(* Printer.                                                                  *)
(* ------------------------------------------------------------------------- *)

let print_propvar prec p = print_int(pname p);;

let print_prop_formula = print_qformula print_propvar;;

(* ------------------------------------------------------------------------- *)
(* Interpretation of formulas.                                               *)
(* ------------------------------------------------------------------------- *)

let rec eval fm v =
  match fm with
    False -> false
  | True -> true
  | Atom(x) -> v(x)
  | Not(p) -> not(eval p v)
  | And(p,q) -> (eval p v) && (eval q v)
  | Or(p,q) -> (eval p v) || (eval q v)
  | Imp(p,q) -> not(eval p v) || (eval q v)
  | Iff(p,q) -> (eval p v) = (eval q v);;

(* ------------------------------------------------------------------------- *)
(* Return the set of propositional variables in a formula.                   *)
(* ------------------------------------------------------------------------- *)

let atoms fm = atom_union (fun a -> [a]) fm;;

(* ------------------------------------------------------------------------- *)
(* Code to print out truth tables.                                           *)
(* ------------------------------------------------------------------------- *)

let rec onallvaluations subfn v ats =
  match ats with
    [] -> subfn v
  | p::ps -> let v' t q = if q = p then t else v(q) in
             onallvaluations subfn (v' false) ps &&
             onallvaluations subfn (v' true) ps;;

(* ------------------------------------------------------------------------- *)
(* Recognizing tautologies.                                                  *)
(* ------------------------------------------------------------------------- *)

let tautology fm =
  onallvaluations (eval fm) (fun s -> false) (atoms fm);;

(* ------------------------------------------------------------------------- *)
(* Related concepts.                                                         *)
(* ------------------------------------------------------------------------- *)

let unsatisfiable fm = tautology(Not fm);;

let satisfiable fm = not(unsatisfiable fm);;

(* ------------------------------------------------------------------------- *)
(* Substitution operation.                                                   *)
(* ------------------------------------------------------------------------- *)

let psubst subfn = onatoms (fun p -> tryapplyd subfn p (Atom p));;

(* ------------------------------------------------------------------------- *)
(* Routine simplification.                                                   *)
(* ------------------------------------------------------------------------- *)

let psimplify1 fm =
  match fm with
    Not False -> True
  | Not True -> False
  | Not(Not p) -> p
  | And(p,False) | And(False,p) -> False
  | And(p,True) | And(True,p) -> p
  | Or(p,False) | Or(False,p) -> p
  | Or(p,True) | Or(True,p) -> True
  | Imp(False,p) | Imp(p,True) -> True
  | Imp(True,p) -> p
  | Imp(p,False) -> Not p
  | Iff(p,True) | Iff(True,p) -> p
  | Iff(p,False) | Iff(False,p) -> Not p
  | _ -> fm;;

let rec psimplify fm =
  match fm with
  | Not p -> psimplify1 (Not(psimplify p))
  | And(p,q) -> psimplify1 (And(psimplify p,psimplify q))
  | Or(p,q) -> psimplify1 (Or(psimplify p,psimplify q))
  | Imp(p,q) -> psimplify1 (Imp(psimplify p,psimplify q))
  | Iff(p,q) -> psimplify1 (Iff(psimplify p,psimplify q))
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Some operations on literals.                                              *)
(* ------------------------------------------------------------------------- *)

let negative = function (Not p) -> true | _ -> false;;

let positive lit = not(negative lit);;

let negate = function (Not p) -> p | p -> Not p;;

(* ------------------------------------------------------------------------- *)
(* Negation normal form.                                                     *)
(* ------------------------------------------------------------------------- *)

let rec nnf fm =
  match fm with
  | And(p,q) -> And(nnf p,nnf q)
  | Or(p,q) -> Or(nnf p,nnf q)
  | Imp(p,q) -> Or(nnf(Not p),nnf q)
  | Iff(p,q) -> Or(And(nnf p,nnf q),And(nnf(Not p),nnf(Not q)))
  | Not(Not p) -> nnf p
  | Not(And(p,q)) -> Or(nnf(Not p),nnf(Not q))
  | Not(Or(p,q)) -> And(nnf(Not p),nnf(Not q))
  | Not(Imp(p,q)) -> And(nnf p,nnf(Not q))
  | Not(Iff(p,q)) -> Or(And(nnf p,nnf(Not q)),And(nnf(Not p),nnf q))
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Roll in simplification.                                                   *)
(* ------------------------------------------------------------------------- *)

let nnf fm = nnf(psimplify fm);;

(* ------------------------------------------------------------------------- *)
(* Simple negation-pushing when we don't care to distinguish occurrences.    *)
(* ------------------------------------------------------------------------- *)

let rec nenf fm =
  match fm with
    Not(Not p) -> nenf p
  | Not(And(p,q)) -> Or(nenf(Not p),nenf(Not q))
  | Not(Or(p,q)) -> And(nenf(Not p),nenf(Not q))
  | Not(Imp(p,q)) -> And(nenf p,nenf(Not q))
  | Not(Iff(p,q)) -> Iff(nenf p,nenf(Not q))
  | And(p,q) -> And(nenf p,nenf q)
  | Or(p,q) -> Or(nenf p,nenf q)
  | Imp(p,q) -> Or(nenf(Not p),nenf q)
  | Iff(p,q) -> Iff(nenf p,nenf q)
  | _ -> fm;;

let nenf fm = nenf(psimplify fm);;

(* ------------------------------------------------------------------------- *)
(* Disjunctive normal form (DNF) via truth tables.                           *)
(* ------------------------------------------------------------------------- *)

let list_conj l = if l = [] then True else end_itlist mk_and l;;

let list_disj l = if l = [] then False else end_itlist mk_or l;;

let mk_lits pvs v =
  list_conj (map (fun p -> if eval p v then p else Not p) pvs);;

let rec allsatvaluations subfn v pvs =
  match pvs with
    [] -> if subfn v then [v] else []
  | p::ps -> let v' t q = if q = p then t else v(q) in
             allsatvaluations subfn (v' false) ps @
             allsatvaluations subfn (v' true) ps;;

let dnf fm =
  let pvs = atoms fm in
  let satvals = allsatvaluations (eval fm) (fun s -> false) pvs in
  list_disj (map (mk_lits (map (fun p -> Atom p) pvs)) satvals);;

(* ------------------------------------------------------------------------- *)
(* DNF via distribution.                                                     *)
(* ------------------------------------------------------------------------- *)

let rec distrib fm =
  match fm with
    And(p,(Or(q,r))) -> Or(distrib(And(p,q)),distrib(And(p,r)))
  | And(Or(p,q),r) -> Or(distrib(And(p,r)),distrib(And(q,r)))
  | _ -> fm;;

let rec rawdnf fm =
  match fm with
    And(p,q) -> distrib(And(rawdnf p,rawdnf q))
  | Or(p,q) -> Or(rawdnf p,rawdnf q)
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* A version using a list representation.                                    *)
(* ------------------------------------------------------------------------- *)

let distrib s1 s2 = setify(allpairs union s1 s2);;

let rec purednf fm =
  match fm with
    And(p,q) -> distrib (purednf p) (purednf q)
  | Or(p,q) -> union (purednf p) (purednf q)
  | _ -> [[fm]];;

(* ------------------------------------------------------------------------- *)
(* Filtering out trivial disjuncts (in this guise, contradictory).           *)
(* ------------------------------------------------------------------------- *)

let trivial lits =
  let pos,neg = partition positive lits in
  intersect pos (image negate neg) <> [];;

(* ------------------------------------------------------------------------- *)
(* With subsumption checking, done very naively (quadratic).                 *)
(* ------------------------------------------------------------------------- *)

let simpdnf fm =
  if fm = False then [] else if fm = True then [[]] else
  let djs = filter (non trivial) (purednf(nnf fm)) in
  filter (fun d -> not(exists (fun d' -> psubset d' d) djs)) djs;;

(* ------------------------------------------------------------------------- *)
(* Mapping back to a formula.                                                *)
(* ------------------------------------------------------------------------- *)

let dnf fm = list_disj(map list_conj (simpdnf fm));;

(* ------------------------------------------------------------------------- *)
(* Conjunctive normal form (CNF) by essentially the same code.               *)
(* ------------------------------------------------------------------------- *)

let purecnf fm = image (image negate) (purednf(nnf(Not fm)));;

let simpcnf fm =
  if fm = False then [[]] else if fm = True then [] else
  let cjs = filter (non trivial) (purecnf fm) in
  filter (fun c -> not(exists (fun c' -> psubset c' c) cjs)) cjs;;

let cnf fm = list_conj(map list_disj (simpcnf fm));;


(* ========================================================================= *)
(* Some propositional formulas to test, and functions to generate classes.   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Half adder.                                                               *)
(* ------------------------------------------------------------------------- *)

let halfsum x y = Iff(x,Not y);;

let halfcarry x y = And(x,y);;

let ha x y s c = And(Iff(s,halfsum x y),Iff(c,halfcarry x y));;

(* ------------------------------------------------------------------------- *)
(* Full adder.                                                               *)
(* ------------------------------------------------------------------------- *)

let carry x y z = Or(And(x,y),And(Or(x,y),z));;

let sum x y z = halfsum (halfsum x y) z;;

let fa x y z s c = And(Iff(s,sum x y z),Iff(c,carry x y z));;

(* ------------------------------------------------------------------------- *)
(* Useful idiom.                                                             *)
(* ------------------------------------------------------------------------- *)

let conjoin f l = list_conj (map f l);;

(* ------------------------------------------------------------------------- *)
(* n-bit ripple carry adder with carry c(0) propagated in and c(n) out.      *)
(* ------------------------------------------------------------------------- *)

let ripplecarry x y c out n =
  conjoin (fun i -> fa (x i) (y i) (c i) (out i) (c(i + 1)))
          (0 -- (n - 1));;
