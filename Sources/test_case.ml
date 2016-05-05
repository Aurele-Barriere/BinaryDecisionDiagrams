(*
 * FOND2 Project : Binary Decision Diagrams
 * 
 * Test_case.ml
 *
 * Copyright 2016 Florestan De Moor - Corentin Ferry
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 * MA 02110-1301, USA.
 * 
 * 
 *)
 
let print_valuation (l : (variable * bool) list) : unit =   
    let val_iter (var, value) =     print_string "x";     
      print_int var;     print_string ": ";     if value then 
          print_int 1 else print_int 0;     print_string " ; ";   in 
    List.iter val_iter l;;



(** Display Sucess of a = b, fail otherwise *)
let result (a : 'a) (b : 'a) : unit =
  if a = b
    then print_string " \027[32m * SUCCESS * \027[0m "
    else print_string " \027[31m * FAIL * \027[0m ";;
    

(** Test if the valuation satisfies the formula *)
let test_valuation (f : prop formula) (l : (variable * bool) list) : unit = 

  let rec max_id f = match f with
  | False -> 0
  | True -> 0
  | Atom(P(n)) -> n
  | Not(f') -> max_id f'
  | And(f1, f2) -> max (max_id f1) (max_id f2)
  | Or(f1, f2) -> max (max_id f1) (max_id f2)
  | Imp(f1, f2) -> max (max_id f1) (max_id f2)
  | Iff(f1, f2) -> max (max_id f1) (max_id f2)
  in
  let max_var_id = max_id f + 1 in
  
  let v = Array.make max_var_id false in
  let val_iter (a, b) = v.(a) <-b in
  List.iter val_iter l;
  
  let rec eval_formula f = match f with
  | False -> false
  | True -> true
  | Atom(P(n)) -> v.(n)
  | Not(f') -> not (eval_formula f')
  | And(f1, f2) -> (eval_formula f1) && (eval_formula f2)
  | Or(f1, f2) -> (eval_formula f1) || (eval_formula f2)
  | Imp(f1, f2) -> not (eval_formula f1) || (eval_formula f2)
  | Iff(f1, f2) -> ((eval_formula f1) && (eval_formula f2)) || (not (eval_formula f1) && not (eval_formula f2))
  in
  let b = eval_formula f
  in result b true;;


(** Perform a test with formula f, debug mode can be activated *)
let test (f : prop formula) (debug : bool) : unit =

  let expect_sat = satisfiable f
  and expect_valid = tautology f in

  print_string "\027[36m***\027[33m TESTING FORMULA ";
  print_formula f;
  print_string "\027[0m";

  let taille = 100 in
  let tT = init_t taille in
  let tH = init_ht taille in
  let u = build tT tH f in
  
  if debug then debug_print_t tT;
  
  print_string "Is Sat? ";
  let b = sat tT u in
  print_bool b;
  print_string " - Expected Sat? ";
  print_bool expect_sat;
  result b expect_sat;
  print_newline();
  
  print_string "Is Valid? ";
  let bb = valid tT u in
  print_bool bb;
  print_string " - Expected Valid? ";
  print_bool expect_valid;
  result bb expect_valid;
  print_newline();
  
  let val_test f l = print_valuation l; test_valuation f l in
  
  print_string "Valuation? ";
  begin try let l = anysat tT u in
  val_test f l;
  with Exception_Not_Satisfiable -> print_string "Not Sat, so no valuation.."; end;
  print_newline();
  
  (*print_string "All valuation? ";
  begin try let ll = allsat tT u in
  List.iter (val_test f) ll;
  with Not_sat -> print_string "Not Sat, so no valuation.."; end;
  print_newline();*)
  
  print_string "\027[36m***********************\027[0m";
  print_newline();
  print_newline();;
  
  
let test_iter (f, debug) =
  test f debug;;

let test_list = ref [];;

(* Tautology *)
let f0 = << 6 ==> 6 >>;;
test_list := (f0, false)::( !test_list);;
let f1 = << ( 1 <=> 2 ) /\ ( 3 <=> 4 ) >>;;
test_list := (f1, false)::( !test_list);;
let f2 = << ( ~ ( 1 /\ 2 ) ) <=> ( ~ 1 \/ 2 ) >>;;
test_list := (f2, false)::( !test_list);;
let f3 = << 1 \/ true >>;;
test_list := (f3, false)::( !test_list);;
let f4 = << true \/ ~ 1 >>;;
test_list := (f4, false)::( !test_list);;

(* Not sat *)
let f5 = << 1 /\ ~ 1 >>;;
test_list := (f5, false)::( !test_list);;
let f6 = << false >>;;
test_list := (f6, false)::( !test_list);;
let f7 = << 1 /\ false >>;;
test_list := (f7, false)::( !test_list);;
let f8 = << false /\ 1 >>;;
test_list := (f8, false)::( !test_list);;
let f9 = << ( 1 /\ ~ 2 ) <=> ( 2 \/ ~ 1 ) >>;;
test_list := (f9, false)::( !test_list);;

(* Sat but not valid *)
let f10 = << 1 \/ ~ 2 >>;;
test_list := (f10, false)::( !test_list);;
let f11 = << ( 1 /\ 2 ) ==> ( 3 \/ ~ 2 ) >>;;
test_list := (f11, false)::( !test_list);;
let f12 = << 1 \/ false >>;;
test_list := (f12, false)::( !test_list);;
let f13 = << 2 \/ 3 /\ 7 >>;;
test_list := (f13, false)::( !test_list);;
let f14 = << ( 1 ==> 2 ) <=> ( 3 \/ ~ 4 /\ 1 ) >>;;
test_list := (f14, false)::( !test_list);;

(* Execute the tests *)
List.iter test_iter ( !test_list);;
