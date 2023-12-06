(* ==================================================================================================== *)
(* IMPLEMENTATION 
   This file implements the less than operation on conjunctions of equalities.
   An conjunction of equalities E' is implied by a conjunction of equalities E (E => E') if and
   only if every individual equality e in E' is implied by E.
   Therefore, the algorithm below iterates over the second argument, representing E', and checks
   if every of its elements is implied by the first one. If so, true is returned, else false.
   There are two possiblities for an equality e to be implied by the conjunction E. First, the
   equality e might be strictly implied by E for all assignments to variables.
   The second one is that e is only implied, if a specific substitution is performed.
   By the definition of implication, we are only interested in the former case and and required
   substitution means that there are other assignments, which will break the implication.
   Hence, in the second case, false is returned.
   The strict implication of an equality e is checked by analysing its structure.
   If e is not defined in terms of a reference variable, then the corresponding equality in E
   must not be defined in terms of a reference variable, aswell. This is, because otherwise it would
   hold that:
     (1): e := x_i = b
     (2): E => x_i = x_j + b'
   Therefore:
     (1), (2) => b = x_j + b' <=> x_j = b - b'
   That is, it is required that the specific assignment to x_j must hold and only then
   the implication is satisfied.

   By similar reasoning, if e defines a variable with respect to a reference variable,
   then it must hold that both the assigned and reference variable must be themselfes defined
   with respect to the same reference variable in the conjunction of equalities and their offsets
   match. Otherwise, either a substitution is necessary or the new equality is simply
   unsatisfiable by the conjunction.
*)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)
type domain_element = int option * Z.t;;
type domain = domain_element array option;;
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
let less (t1 : domain) (t2 : domain) : bool =  
  let implies (ts : domain_element array) (t : domain_element) (i : int) : bool =
    match t with
    | (None, b) -> 
      (match ts.(i) with
       | (None, b') -> Z.equal b b'
       | _ -> false)
    | (Some j, b) -> 
      (match ts.(i), ts.(j) with
       | (None, _), (_, _) -> false
       | (_, _), (None, _) -> false
       | (Some h1, b1), (Some h2, b2) ->
         h1 = h2 && Z.equal b1 (Z.add b2 b))
  in
  match t1, t2 with
  | None, _ -> true
  | _, None -> false
  | Some t1', Some t2' ->
    let result : bool ref = ref true in
    for i = 0 to Array.length t2' - 1 do
      let t = t2'.(i) in
      if not (implies t1' t i) then result := false;
    done;
    !result
(* ---------------------------------------------------------------------------------------------------- *)


(* ==================================================================================================== *)
(* TESTS *)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)
(* Tests that any conjunction implies the trivial conjunction.  *)
let _ = print_endline ""; 
  let t1 : domain = Some [|
    (Some 0, Z.of_int 0); 
    (Some 1, Z.of_int 0); 
    (Some 0, Z.of_int 0); 
    (Some 1, Z.of_int 5); 
    (Some 0, Z.of_int 5); 
    (Some 0, Z.of_int 3); 
    (Some 0, Z.of_int 2)
  |] in
  let t2 : domain = Some [|
    (Some 0, Z.of_int 0); 
    (Some 1, Z.of_int 0); 
    (Some 2, Z.of_int 0); 
    (Some 3, Z.of_int 0); 
    (Some 4, Z.of_int 0); 
    (Some 5, Z.of_int 0); 
    (Some 6, Z.of_int 0)
  |] in
  let expected_result : bool = true in
  print_endline "LESS TEST 1";
  let r = less t1 t2 in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* Tests that an implied conjunction becomes not implied if a single conjunct is unimplied. *)
let _ = print_endline ""; 
  let t1 : domain = Some [|
    (Some 0, Z.of_int 0); 
    (Some 1, Z.of_int 0); 
    (Some 0, Z.of_int 0); 
    (Some 1, Z.of_int 5); 
    (Some 0, Z.of_int 5); 
    (Some 0, Z.of_int 3); 
    (Some 0, Z.of_int 2)
  |] in
  let t2 : domain = Some [|
    (Some 0, Z.of_int 0); 
    (Some 1, Z.of_int 0); 
    (Some 2, Z.of_int 0); 
    (Some 3, Z.of_int 1); 
    (Some 4, Z.of_int 0); 
    (Some 5, Z.of_int 0); 
    (Some 6, Z.of_int 0)
  |] in
  let expected_result : bool = false in
  print_endline "LESS TEST 2";
  let r = less t1 t2 in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* Tests that a more general conjunction does not imply a more concrete conjunction. That is, because
  the more concrete conjunction in general is only implied in case the specific substitution is 
  performed that resulted in the more concrete conjunction. For any other substitution this does 
  in general not hold. *)
let _ = print_endline ""; 
  let t1 : domain = Some [|
    (Some 0, Z.of_int 0); 
    (Some 1, Z.of_int 0); 
    (Some 0, Z.of_int 0); 
    (Some 1, Z.of_int 5); 
    (Some 0, Z.of_int 5); 
    (Some 0, Z.of_int 3); 
    (Some 0, Z.of_int 2)
  |] in
  let t2 : domain = Some [|
    (None, Z.of_int 1); 
    (Some 1, Z.of_int 0); 
    (None, Z.of_int 1); 
    (Some 1, Z.of_int 5); 
    (None, Z.of_int 6); 
    (None, Z.of_int 4); 
    (None, Z.of_int 3)
  |] in
  let expected_result : bool = false in
  print_endline "LESS TEST 3";
  let r = less t1 t2 in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that a more concrete conjunction does not imply a more general one.
  That is, because to obtain the more concrete conjunction a specific substitution
  might have been needed to take place. Therefore, in general this implication does not
  hold since any different assignment to the variable that changed between the more general
  and more concrete conjunction might result in conjuncts that are not implied. *)
let _ = print_endline ""; 
  let t1 : domain = Some [|
    (None, Z.of_int 1); 
    (Some 1, Z.of_int 0); 
    (None, Z.of_int 1); 
    (Some 1, Z.of_int 5); 
    (None, Z.of_int 6); 
    (None, Z.of_int 4); 
    (None, Z.of_int 3)
  |] in
  let t2 : domain = Some [|
    (Some 0, Z.of_int 0); 
    (Some 1, Z.of_int 0); 
    (Some 0, Z.of_int 0); 
    (Some 1, Z.of_int 5); 
    (Some 0, Z.of_int 5); 
    (Some 0, Z.of_int 3); 
    (Some 0, Z.of_int 2)
  |] in
  let expected_result : bool = false in
  print_endline "LESS TEST 4";
  let r = less t1 t2 in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)

