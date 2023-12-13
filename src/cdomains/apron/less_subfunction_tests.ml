(* This file test the subfuction 'implies' of the 'less' function.
  To this end, compared to the final implementation, the subfunction is refactored
  so it can be run independently. To see the final implementation, how it works and tests for the 
  'less' function, see the file 'less.ml'.
*)

(* ==================================================================================================== *)
(* IMPLEMENTATION *)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)
type domain_element = int option * Z.t;;
type domain = domain_element array option;;
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
let implies (ts : domain_element array) (t : domain_element) (i : int) : bool =
  match t with
  | (None, b) -> 
    (match ts.(i) with
     | (None, b') -> Z.equal b b'
     | _ -> false)
  | (Some j, b) -> 
    (match ts.(i), ts.(j) with
     | (None, b1), (None, b2) -> Z.equal b1 (Z.add b2 b)
     | (None, _), (_, _) -> false
     | (_, _), (None, _) -> false
     | (Some h1, b1), (Some h2, b2) ->
       h1 = h2 && Z.equal b1 (Z.add b2 b))
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
let less (t1 : domain) (t2 : domain) : bool =  
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
(* tests that a new constant assignment is not implied when the variable is previously defined
  in reference to another variable. *)
let _ = print_endline "";
  let ts : domain_element array = [|
    (Some 0, Z.of_int 0);
    (Some 1, Z.of_int 0);
    (Some 0, Z.of_int 0);
    (Some 1, Z.of_int 5);
    (Some 0, Z.of_int 5);
    (Some 0, Z.of_int 3);
    (Some 0, Z.of_int 2);
  |] in
  let t : domain_element = (None, Z.of_int 0) in
  let i : int = 2 in
  let expected_result : bool = false in
  print_endline "IMPLIES TEST 1";
  let r = implies ts t i in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that a new constant assignment is implied when the variable is previously defined
  not in reference to another variable and has the same constant offset. *)
let _ = print_endline "";
  let ts : domain_element array = [|
    (Some 0, Z.of_int 0);
    (Some 1, Z.of_int 0);
    (None, Z.of_int 0);
    (Some 1, Z.of_int 5);
    (Some 0, Z.of_int 5);
    (Some 0, Z.of_int 3);
    (Some 0, Z.of_int 2);
  |] in
  let t : domain_element = (None, Z.of_int 0) in
  let i : int = 2 in
  let expected_result : bool = true in
  print_endline "IMPLIES TEST 2";
  let r = implies ts t i in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that a new assignment with respect to a reference variable is not implied when the variable 
  is previously defined in reference to a differentvariable. *)
let _ = print_endline "";
  let ts : domain_element array = [|
    (Some 0, Z.of_int 0);
    (Some 1, Z.of_int 0);
    (Some 0, Z.of_int 0);
    (Some 1, Z.of_int 5);
    (Some 0, Z.of_int 5);
    (Some 0, Z.of_int 3);
    (Some 0, Z.of_int 2);
  |] in
  let t : domain_element = (Some 1, Z.of_int 0) in
  let i : int = 2 in
  let expected_result : bool = false in
  print_endline "IMPLIES TEST 3";
  let r = implies ts t i in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* Tests that an assignment is not implied even if the reference variables are the same, when
  their respective constant offsets are different. *)
let _ = print_endline "";
  let ts : domain_element array = [|
    (Some 0, Z.of_int 0);
    (Some 1, Z.of_int 0);
    (Some 0, Z.of_int 0);
    (Some 1, Z.of_int 5);
    (Some 0, Z.of_int 5);
    (Some 0, Z.of_int 3);
    (Some 0, Z.of_int 2);
  |] in
  let t : domain_element = (Some 1, Z.of_int 0) in
  let i : int = 3 in
  let expected_result : bool = false in
  print_endline "IMPLIES TEST 4";
  let r = implies ts t i in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* Tests that an assignment is implied if the references variables are the same and both
  costant offsets are equivalent. *)
let _ = print_endline "";
  let ts : domain_element array = [|
    (Some 0, Z.of_int 0);
    (Some 1, Z.of_int 0);
    (Some 0, Z.of_int 0);
    (Some 1, Z.of_int 5);
    (Some 0, Z.of_int 5);
    (Some 0, Z.of_int 3);
    (Some 0, Z.of_int 2);
  |] in
  let t : domain_element = (Some 1, Z.of_int 5) in
  let i : int = 3 in
  let expected_result : bool = true in
  print_endline "IMPLIES TEST 5";
  let r = implies ts t i in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
let _ = print_endline "";
  let t1 : domain = Some [|
    (Some 0, Z.of_int 0);
    (Some 1, Z.of_int 0);
    (Some 0, Z.of_int 0);
    (Some 1, Z.of_int 5);
    (Some 0, Z.of_int 5);
    (Some 0, Z.of_int 3);
    (Some 0, Z.of_int 2);
  |] in
  let t2 : domain = Some [|
    (Some 0, Z.of_int 0);
    (Some 1, Z.of_int 0);
    (Some 2, Z.of_int 0);
    (Some 3, Z.of_int 0);
    (Some 4, Z.of_int 0);
    (Some 5, Z.of_int 0);
    (Some 6, Z.of_int 0);
  |] in
  let expected_result : bool = true in
  print_endline "LESS TEST 1";
  let r = less t1 t2 in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)
