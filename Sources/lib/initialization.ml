open Num;;
open Format;;

Gc.set { (Gc.get()) with Gc.stack_limit = 16777216 };; (* Up the stack size  *)
Format.set_margin 72;;                                 (* Reduce margins     *)
include Format;;                                       (* Open formatting    *) 
include Num;;                                          (* Open bignums       *) 

let print_num n = print_string(string_of_num n);;      (* Avoid range limit  *)


