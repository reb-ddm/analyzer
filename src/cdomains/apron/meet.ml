
(* ==================================================================================================== *)
(* DOMAIN
   In the following, a conjunction of equivalences is represented by an 'optional array'.
   That is, since equivalences can become unsatifsiable, if the wrong equivalences are added to
   the overall conjunction.
   Each equivalence itself consist of the assigned variable, the reference variable and a constant
   offset. The assigned variable is determined by the index of the equivalence in the overall array.
   The Reference variable is the variable to which a constant offset has to be added to obtain the
   value of the assigned variable. The reference variable is stored as the index of the respective
   variable (possibly represented by the value 'None' if no reference variable exists).
   The constant offset is of type 'Z.t', which is defined in the Zarith library and allows to use
   integers of arbitrary size.

   TODO: In the final implementation, the datatype will consist of an apron environment.
   How does it need to be handled in a straightforward translation of the paper's algorithm?
*)
(* ==================================================================================================== *)

type domain = (int option * Z.t) array option;;

(* ==================================================================================================== *)
(* ALGORITHM 
   The follwing algorithm is a direct translation of the paper's algorithm in lemma 3.2.
   It computes the 'meet', the greatest lower bound of two conjunction of equivalences.
   It consists of three parts:
   The bottom-most part (line 79) is run first. 
   First, a copy of the first arguement is made, which will, eventually, store the overall result.
   It iterates over the equivalences in the second argument and adds them one by one to the current
   array of equivalences.
   A single equivalence is added in the middle part in the function 'add_conj'. 
   Here, the form of the new equivalence is analysed, as well as the the form of the assigned 
   variable and reference variable in the current conjunction. This directly follows the algorithm 
   described in the paper. Depending on the new conjunct a variable appearing as reference variable
   in the array might need to be replaced by either a constant value of the combination of another
   reference variable and an offset.
   This is done in the function 'subst_var' in the top of the meet function.
   It iterates over the array and if the desired reference variable is found, the intended 
   substitution is performed.
*)
(* ==================================================================================================== *)

let meet (t1 : domain) (t2 : domain) = 
  let subst_var ts x t = 
    match !ts with
      | None -> ()
      | Some ts' ->
        if Array.length ts' <> 0 then
        for i = 0 to Array.length ts' - 1 do
          match ts'.(i) with
           | (None, _) -> ()
           | (Some x', b') -> if x = x' then
             (match t with 
               | (None, bt) -> ts'.(i) <- (None, Z.(b' + bt))
               | (Some xt, bt) -> ts'.(i) <- (Some xt, Z.(b' + bt)))
        done
  in
  let add_conj ts t i = 
    match !ts with
      | None -> ()
      | Some ts' ->
        (match t with
          | (None, b) -> 
            (match ts'.(i) with
              | (None, b') -> if b <> b' then ts := None;
              | (Some j, b') -> subst_var ts j (None, Z.(b - b')))
          | (Some j, b) ->
             (match ts'.(i) with
              | (None, b1) -> subst_var ts j (None, Z.(b1 - b))
              | (Some h1, b1) -> 
                (match ts'.(j) with
                  | (None, b2) -> subst_var ts i (None, Z.(b2 + b))
                  | (Some h2, b2) -> 
                    if h1 = h2 then 
                      (if Z.(b1 <> (b2 + b)) then ts := None)
                    else if h1 < h2 then subst_var ts h2 (Some h1, Z.(b1 - (b + b2)))
                    else subst_var ts h1 (Some h2, Z.(b + (b2 - b1))))))
  in 
  match t1, t2 with
    | None, _ -> None
    | _, None -> None
    | Some t1', Some t2' -> 
      let ts = ref (Some (Array.copy t1')) in
      if Array.length t2' <> 0 then
      for j = 0 to Array.length t2' - 1 do
        add_conj ts t2'.(j) j
      done; 
      !ts

(* ==================================================================================================== *)
(* TESTS *)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)
(*
  TEST 1: sanity check.
  checks that the function can be executed and trivial conditions are met.
*)

let test_1_domain_1 : domain = None
let test_1_domain_2 : domain = Some [| (Some 0, Z.of_int 3) |]
let test_1_expected_result : domain = None

let _b = print_endline ""; 
  print_endline "TEST 1";
  let r1 = meet test_1_domain_1 test_1_domain_2 in
  print_string "assertion 1: ";
  if r1 = test_1_expected_result then print_endline "true" else print_endline "false";
  
  let r2 = meet test_1_domain_2 test_1_domain_1 in
  print_string "assertion 2: ";
  if r2 = test_1_expected_result then print_endline "true" else print_endline "false"; 
  print_endline "test complete"
  
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(*
  TEST 2: adding a constant equivalence without substitution
  From lemma 3.2 case 1; the additional conjunct is alreaady implied by existing conjunction.
*)

let test_2_domain_1 : domain = Some [| (None, Z.of_int 1); (Some 1, Z.of_int 2); (Some 1, Z.of_int 3)|]
let test_2_domain_2 : domain = Some [| (None, Z.of_int 1) |]
let test_2_expected_result = test_2_domain_1

let _ = print_endline ""; 
  print_endline "TEST 2";
  let r = meet test_2_domain_1 test_2_domain_2 in
  print_string "assertion: ";
  if r = test_2_expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"

(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(*
  TEST 3: Adding a constant unsatisfiable equivalence.
  From lemma 3.2 case 1; both the existing and new conjunct are constant, but different.
  The result cannot be satisfied.
*)

let test_3_domain_1 : domain = Some [| (None, Z.of_int 1); (Some 1, Z.of_int 2); (Some 1, Z.of_int 3)|]
let test_3_domain_2 : domain = Some [| (None, Z.of_int 2) |]
let test_3_expected_result : domain = None

let _ = print_endline ""; 
  print_endline "TEST 3";
  let r = meet test_3_domain_1 test_3_domain_2 in
  print_string "assertion: ";
  if r = test_3_expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"


(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(*
  TEST 4: Constant equivalence is added to non constant array entry.
  From lemma 3.2 case 1; non constant entry in array.
  Reference variable has to be substituted by constant value.
*)

let test_4_domain_1 : domain = Some [| (Some 0, Z.of_int 1)|]
let test_4_domain_2 : domain = Some [| (None, Z.of_int 2) |]
let test_4_expected_result : domain = Some [| (None, Z.of_int 2) |]

let _ = print_endline ""; 
  print_endline "TEST 4";
  let r = meet test_4_domain_1 test_4_domain_2 in
  print_string "assertion: "; 
  if r = test_4_expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"


(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(*
  TEST 5: Non constant conjunct is added, wnile the same variable is constant in the array.
  From lemma 3.2 case 2; the assigned variable in the new conjunct is constant in the array.
  Reference variable in the new conjunct has to be substituted bby a constant value in the conjunction.
*)

let test_5_domain_1 : domain = Some [| (None, Z.of_int 1); (Some 0, Z.of_int 3)|]
let test_5_domain_2 : domain = Some [| (Some 0, Z.of_int 2) |]
let test_5_expected_result : domain = Some [| (None, Z.of_int 1); (None, Z.of_int 2)|]

let _ = print_endline ""; 
  print_endline "TEST 5";
  let r = meet test_5_domain_1 test_5_domain_2 in
  print_string "assertion: "; 
  if r = test_5_expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"


(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(*
  TEST 6: Non constant conjunct is added with constant refrence variable
  From lemma 3.2 case 2; the new conjunct is non constant, while the assigned
  variable in the array is not constant, but the reference variable is.
  The assigned variable in the new conjunct has to be replaced by a constant in all appearances
  in the array.
*)

let test_6_domain_1 : domain = Some [| (Some 0, Z.of_int 1); (None, Z.of_int 2)|]
let test_6_domain_2 : domain = Some [| (Some 1, Z.of_int 3) |]
let test_6_expected_result : domain = Some [| (None, Z.of_int 6); (None, Z.of_int 2)|]

let _ = print_endline ""; 
  print_endline "TEST 6";
  let r = meet test_6_domain_1 test_6_domain_2 in
  print_string "assertion: "; 
  if r = test_6_expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"

(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(*
  TEST 7: Both the assigned and reference variable in the new conjunct are non const, but
  the new equivalence is already implied.
  From lemma 3.2 case 2; Both variables have the same reference variable. Further, their respective
  offsets are such that they agree with the new equivalence. Hence, the new conjunct is
  already implied by the existing conjunction.
*)

let test_7_domain_1 : domain = Some [| (Some 0, Z.of_int 3); (Some 0, Z.of_int 2)|]
let test_7_domain_2 : domain = Some [| (Some 1, Z.of_int 1) |]
let test_7_expected_result : domain = test_7_domain_1

let _ = print_endline ""; 
  print_endline "TEST 7";
  let r = meet test_7_domain_1 test_7_domain_2 in
  print_string "assertion: "; 
  if r = test_7_expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"

(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(*
  TEST 8: Matching reference variables, but offsets cause new conjunct to be unsafisfiable
  From lemma 3.2 case 2; Both, the reference and assigned variable in the new conjunct 
  are defined with respect to the same variable. Similar, to the previous test, the new
  conjunct is strictly implied, if the offsets of both respective variables are set to
  match the new equivalence. If they are not set properly, the new conjunct is, thus,
  unsatisfiable.
*)

let test_8_domain_1 : domain = Some [| (Some 0, Z.of_int 1); (Some 0, Z.of_int 2)|]
let test_8_domain_2 : domain = Some [| (Some 1, Z.of_int 3) |]
let test_8_expected_result : domain = None

let _ = print_endline ""; 
  print_endline "TEST 8";
  let r = meet test_8_domain_1 test_8_domain_2 in
  print_string "assertion: "; 
  if r = test_8_expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"

(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* 
  TEST 9: different reference variables for both variables.
  From lemma 3.2, case 2; When the reference variables of both variables appearing in the
  new conjunct are different, they both belong to different strongly connected components.
  The new equivalence causes both components to become connected.
  Therefore, the variable with smaller index becomes the reference variable
  of all variables, that were defined with respoect to the other one, before.
*)

let test_9_domain_1 : domain = Some [| (Some 0, Z.of_int 1); (Some 1, Z.of_int 2) |]
let test_9_domain_2 : domain = Some [| (Some 1, Z.of_int 3) |]
let test_9_expected_result : domain = Some [| (Some 0, Z.of_int 1); (Some 0, Z.of_int (-2)) |]

let _ = print_endline ""; 
  print_endline "TEST 9";
  let r = meet test_9_domain_1 test_9_domain_2 in
  print_string "assertion: "; 
  if r = test_9_expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"

(* ---------------------------------------------------------------------------------------------------- *)

