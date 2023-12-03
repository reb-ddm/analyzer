(* This file tests the subfunctions of the meet operation.
  To this end, compared to the final implementation, the subfunctions are refactored
  so they can be run independently. To see the final implementation, how it works and tests for the 
  meet function, see the file 'meet.ml'.
  There are test cases for the following to functions:
    * 'subst_var': substitutes an offset and potentially a new reference variable for 
      a specified variable
    * 'add_conj': adds a new conjunct to a conjunction of single variable equivalences.
*)

(* ==================================================================================================== *)
(* IMPLEMENTATION *)
(* ==================================================================================================== *)

type domain = (int option * Z.t) array option;;

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

let _meet (t1 : domain) (t2 : domain) = 
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
(* VARIABLE SUBSTITUTION TESTS *)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that the bottom value does not change from substitutions *)
let subst_test_1_domain : domain ref = ref None
let subst_test_1_var : int = 0
let subst_test_1_replacement : int option * Z.t = (None, Z.of_int 0)
let subst_test_1_expected_result : domain = !subst_test_1_domain

let _ = print_endline "";
  print_endline "SUBSTITUTION TEST 1";
  subst_var subst_test_1_domain subst_test_1_var subst_test_1_replacement;
  print_string "assertion: ";
  if !subst_test_1_domain = subst_test_1_expected_result 
    then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that an array with no entries remains the same after a substitution *)
let subst_test_2_domain : domain ref = ref (Some [||])
let subst_test_2_var : int = 1
let subst_test_2_replacement : int option * Z.t = (Some 3, Z.of_int 2)
let subst_test_2_expected_result : domain = !subst_test_2_domain

let _ = print_endline "";
  print_endline "SUBSTITUTION TEST 2";
  subst_var subst_test_2_domain subst_test_2_var subst_test_2_replacement;
  print_string "assertion: ";
  if !subst_test_2_domain = subst_test_2_expected_result 
    then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that, if no reference variables are contained in the array, then substituting
  a reference variable does not change the array *)
let subst_test_3_domain : domain ref = ref (Some [| (None, Z.of_int 5) |])
let subst_test_3_var : int = 0
let subst_test_3_replacement : int option * Z.t = (Some 3, Z.of_int 2)
let subst_test_3_expected_result : domain = ! subst_test_3_domain

let _ = print_endline "";
  print_endline "SUBSTITUTION TEST 3";
  subst_var subst_test_3_domain subst_test_3_var subst_test_3_replacement;
  print_string "assertion: ";
  if !subst_test_3_domain = subst_test_3_expected_result 
    then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that the array stays the same if it contains reference variables but not the
  one one wants to substitute for *)
let subst_test_4_domain : domain ref = ref (Some [| (Some 1, Z.of_int 5) |])
let subst_test_4_var : int = 0
let subst_test_4_replacement : int option * Z.t = (Some 3, Z.of_int 2)
let subst_test_4_expected_result : domain = !subst_test_4_domain

let _ = print_endline "";
  print_endline "SUBSTITUTION TEST 4";
  subst_var subst_test_4_domain subst_test_4_var subst_test_4_replacement;
  print_string "assertion: ";
  if !subst_test_4_domain = subst_test_4_expected_result 
    then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that, if the reference variable does appear, a substitution takes place *)
let subst_test_5_domain : domain ref = ref (Some [| (Some 0, Z.of_int 5) |])
let subst_test_5_var : int = 0
let subst_test_5_replacement : int option * Z.t = (Some 3, Z.of_int 2)
let subst_test_5_expected_result : domain = Some [| (Some 3, Z.of_int 7) |]

let _ = print_endline "";
  print_endline "SUBSTITUTION TEST 5";
  subst_var subst_test_5_domain subst_test_5_var subst_test_5_replacement;
  print_string "assertion: ";
  if !subst_test_5_domain = subst_test_5_expected_result 
    then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that the right substitutions are performed in a more complex scenario *)
let subst_test_6_domain : domain ref = 
  ref (Some [| (Some 0, Z.of_int 0); (Some 1, Z.of_int 0); (Some 0, Z.of_int 0); (Some 1, Z.of_int 5);
    (Some 0, Z.of_int 5); (Some 0, Z.of_int 3); (Some 0, Z.of_int 2) |])
let subst_test_6_var : int = 0
let subst_test_6_replacement : int option * Z.t = (Some 2, Z.of_int 4)
let subst_test_6_expected_result : domain = 
  Some [| (Some 2, Z.of_int 4); (Some 1, Z.of_int 0); (Some 2, Z.of_int 4); (Some 1, Z.of_int 5);
    (Some 2, Z.of_int 9); (Some 2, Z.of_int 7); (Some 2, Z.of_int 6) |]

let _ = print_endline "";
  print_endline "SUBSTITUTION TEST 6";
  subst_var subst_test_6_domain subst_test_6_var subst_test_6_replacement;
  print_string "assertion: ";
  if !subst_test_6_domain = subst_test_6_expected_result 
    then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ==================================================================================================== *)
(* ADD CONJUNCT TESTS *)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)
(* An unsatisfiable conjunction stays unsatisfiable, when a new conjunct is added. *)
let add_test_1_domain : domain ref = ref None
let add_test_1_new_conj : int option * Z.t = (None, Z.of_int 0)
let add_test_1_index    : int = 0
let add_test_1_expected_result : domain = None

let _ = print_endline "";
  print_endline "ADD TEST 1";
  add_conj add_test_1_domain add_test_1_new_conj add_test_1_index;
  print_string "assertion: ";
  if !add_test_1_domain = add_test_1_expected_result 
    then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* If a constant conjunct is strictly implied, then the original conjunction stays the same. *)
let add_test_2_domain : domain ref = 
  ref (Some [| (Some 0, Z.of_int 2); (None, Z.of_int 0); (Some 1, Z.of_int 4); (Some 3, Z.of_int 1)|])
let add_test_2_new_conj : int option * Z.t = (None, Z.of_int 0)
let add_test_2_index    : int = 1
let add_test_2_expected_result : domain = !add_test_2_domain

let _ = print_endline "";
  print_endline "ADD TEST 2";
  add_conj add_test_2_domain add_test_2_new_conj add_test_2_index;
  print_string "assertion: ";
  if !add_test_2_domain = add_test_2_expected_result 
    then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* If a constant conjunct and the corresponding array entry is constant such that
  both offsets are different, then the final conjunction is unsatisfiable. *)
let add_test_3_domain : domain ref = 
  ref (Some [| (Some 0, Z.of_int 2); (None, Z.of_int 0); (Some 1, Z.of_int 4); (Some 3, Z.of_int 1)|])
let add_test_3_new_conj : int option * Z.t = (None, Z.of_int 1)
let add_test_3_index    : int = 1
let add_test_3_expected_result : domain = None

let _ = print_endline "";
  print_endline "ADD TEST 3";
  add_conj add_test_3_domain add_test_3_new_conj add_test_3_index;
  print_string "assertion: ";
  if !add_test_3_domain = add_test_3_expected_result 
    then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* When a constant conjunct is added but the corresponding array entry has a reference variable, then 
  the reference variable needs to be substituted by the proper constant term. *)
let add_test_4_domain : domain ref = 
  ref (Some [| (Some 0, Z.of_int 2); (Some 1, Z.of_int 1); (Some 1, Z.of_int 4); (Some 3, Z.of_int 1)|])
let add_test_4_new_conj : int option * Z.t = (None, Z.of_int 3)
let add_test_4_index    : int = 1
let add_test_4_expected_result : domain =
  Some [| (Some 0, Z.of_int 2); (None, Z.of_int 3); (None, Z.of_int 6); (Some 3, Z.of_int 1)|]

let _ = print_endline "";
  print_endline "ADD TEST 3";
  add_conj add_test_4_domain add_test_4_new_conj add_test_4_index;
  print_string "assertion: ";
  if !add_test_4_domain = add_test_4_expected_result 
    then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* When a non constant conjunct is added and the corresponding array entry of the assigned variable 
  is constant, then the reference variable from new conjunct needs to be substituted by the proper
  constant term. *)
let add_test_5_domain : domain ref = 
  ref (Some [| (Some 0, Z.of_int 2); (None, Z.of_int 1); (Some 1, Z.of_int 4); (Some 3, Z.of_int 1)|])
let add_test_5_new_conj : int option * Z.t = (Some 0, Z.of_int 4)
let add_test_5_index    : int = 1
let add_test_5_expected_result : domain =
  Some [| (None, Z.of_int (-1)); (None, Z.of_int 1); (Some 1, Z.of_int 4); (Some 3, Z.of_int 1)|]

let _ = print_endline "";
  print_endline "ADD TEST 5";
  add_conj add_test_5_domain add_test_5_new_conj add_test_5_index;
  print_string "assertion: ";
  if !add_test_5_domain = add_test_5_expected_result 
    then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* When a non constant conjunct is added, but the corresponding array entry of the reference variable 
  is constant, then the assigned variable from new conjunct needs to be substituted by the proper term. *)
let add_test_6_domain : domain ref = 
  ref (Some [| (None, Z.of_int 2); (Some 0, Z.of_int 1); (Some 1, Z.of_int 4); (Some 3, Z.of_int 1)|])
let add_test_6_new_conj : int option * Z.t = (Some 0, Z.of_int 3)
let add_test_6_index    : int = 1
let add_test_6_expected_result : domain =
  Some [| (None, Z.of_int 2); (Some 0, Z.of_int 1); (None, Z.of_int 9); (Some 3, Z.of_int 1)|] 

let _ = print_endline "";
  print_endline "ADD TEST 6";
  add_conj add_test_6_domain add_test_6_new_conj add_test_6_index;
  print_string "assertion: ";
  if !add_test_6_domain = add_test_6_expected_result 
    then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* When a non constant conjunct is added and both, the reference and assigned variable, are non 
  constant with the same reference variable, while their respective offsets are set to the right values,
  then the new conjunct is strictly implied by the existing array. *)
let add_test_7_domain : domain ref = 
  ref (Some [| (Some 0, Z.of_int 1); (Some 0, Z.of_int 4); (Some 1, Z.of_int 4); (Some 3, Z.of_int 1)|])
let add_test_7_new_conj : int option * Z.t = (Some 0, Z.of_int 3)
let add_test_7_index    : int = 1
let add_test_7_expected_result : domain = !add_test_7_domain 

let _ = print_endline "";
  print_endline "ADD TEST 7";
  add_conj add_test_7_domain add_test_7_new_conj add_test_7_index;
  print_string "assertion: ";
  if !add_test_7_domain = add_test_7_expected_result 
    then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* When a non constant conjunct added and both, the reference and assigned variable, are non constant 
  with the same reference variable, while their respective offsets are set not satisfying the proper
  relation necessary, then the new conjunct is unsatifiable given the prior conjunction of
  equivalences. *)
let add_test_8_domain : domain ref = 
  ref (Some [| (Some 0, Z.of_int 2); (Some 0, Z.of_int 4); (Some 1, Z.of_int 4); (Some 3, Z.of_int 1)|])
let add_test_8_new_conj : int option * Z.t = (Some 0, Z.of_int 3)
let add_test_8_index    : int = 1
let add_test_8_expected_result : domain = None

let _ = print_endline "";
  print_endline "ADD TEST 8";
  add_conj add_test_8_domain add_test_8_new_conj add_test_8_index;
  print_string "assertion: ";
  if !add_test_8_domain = add_test_8_expected_result 
    then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* When a non constant conjunct is added and both, the reference and assigned variable, are non 
  constant with different reference variables, then two connected components are joint. 
  When h2 < h1 (see paper), x_h2 (in this case the variable with index 0) will become the 
  common reference varaible. *) 
let add_test_9_domain : domain ref = 
  ref (Some [| (Some 0, Z.of_int 2); (Some 1, Z.of_int 4); (Some 1, Z.of_int 3); (Some 3, Z.of_int 1)|])
let add_test_9_new_conj : int option * Z.t = (Some 0, Z.of_int 3)
let add_test_9_index    : int = 1
let add_test_9_expected_result : domain = 
  Some [| (Some 0, Z.of_int 2); (Some 0, Z.of_int 5); (Some 0, Z.of_int 4); (Some 3, Z.of_int 1)|]

let _ = print_endline "";
  print_endline "ADD TEST 9";
  add_conj add_test_9_domain add_test_9_new_conj add_test_9_index;
  print_string "assertion: ";
  if !add_test_9_domain = add_test_9_expected_result 
    then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* When a non constant conjunct is added and both, the reference and assigned variable, are non 
  constant with different reference variables, then two connected components are joint. 
  When h1 < h2 (see paper), x_h1 (in this case the variable with index 0) will become the 
  common reference varaible. *) 
let add_test_10_domain : domain ref = 
  ref (Some [| (Some 0, Z.of_int 2); (Some 1, Z.of_int 4); (Some 1, Z.of_int 3); (Some 3, Z.of_int 1)|])
let add_test_10_new_conj : int option * Z.t = (Some 1, Z.of_int 3)
let add_test_10_index    : int = 0
let add_test_10_expected_result : domain = 
  Some [| (Some 0, Z.of_int 2); (Some 0, Z.of_int (-1)); (Some 0, Z.of_int (-2)); (Some 3, Z.of_int 1)|] 

let _ = print_endline "";
  print_endline "ADD TEST 10";
  add_conj add_test_10_domain add_test_10_new_conj add_test_10_index;
  print_string "assertion: ";
  if !add_test_10_domain = add_test_10_expected_result 
    then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)

