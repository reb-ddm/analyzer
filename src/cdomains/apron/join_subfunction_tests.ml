(* This file tests the subfunctions of the join operation.
  To this end, compared to the final implementation, the subfunctions are refactored
  so they can be run independently. To see the final implementation, how it works and tests for the 
  join function, see the file 'join.ml'.
  There are test cases for the following to functions:
    * 'ts_zip': zips two conjunctions of equivalences with the index of the assigned variable,
      so that both assignments can be processed together.
    * 'cmp_z_ref': compares two domain elements by the reference variable.
    * 'cmp_z': compares two zipped elements. First by the reference variable of the first element.
      If they are equal, then they are compared by the reference variable of the second element.
      If they are still equal, then the final comparison result is determined by the 
      constant offsets.
    * 'sort_z_by_expr': sorts zipped elements using the 'cmp_z' function above.
    * 'sort_annotated': sorts an annotated dataset by the value of the annotation.
    * 'size_of_eq_class': determines the size of equivalence classes of an array of zipped elements.
    * 'least_index_var_in_eq_class': determines the smallest variable index in a given equivalence
      class. Further, the constant offset of the first domain element is returned, aswell.
    * 'all_are_const_in_eq_class': determines if all domain elements in an array of zipped
      elements are constant, meaning, if they have no reference variable.
    * 'assign_vars_in_const_eq_class': assigns the values of the final data structure based
      on the values of a zipped array in an equivalence class, where all elements are constant
      as described in the paper.
    * 'assign_vars_in_non_const_eq_class': assigns the values of the final data structure based
      on the values of a zipped array in an equivalence class, where not all elements are constant
      as described in the paper.
    * 'process_eq_classes': iterates over all equivalence classes and, depeding on the number
      of elements and if all elements in the equivalence class are constant, determines the 
      values of the final conjunction, as described in the paper.
    * 'strip_annotation': removes the annotation from the resulting data structure to
      obtain the final result of the join operation.
*)

(* ==================================================================================================== *)
(* TYPES *)
(* ==================================================================================================== *)

type domain_element = int option * Z.t
type domain = domain_element array option
type zipped_element = int * domain_element * domain_element
type zipped_domain = zipped_element array option
type annotated_element = int * domain_element
type annotated_domain = annotated_element array option


(* ==================================================================================================== *)
(* ZIP *)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)
let ts_zip t1 t2 : zipped_domain =
  if Array.length t1 <> Array.length t2 then None else
  let zts = Array.init (Array.length t1) (fun (i : int) -> (i, t1.(i), t2.(i))) in
  Some zts 
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests the zip operation on the dataset given from the paper. *)
let _ = print_endline "";
  let t1 : domain_element array = [|
    (Some 0, Z.of_int 0);
    (Some 1, Z.of_int 0);
    (Some 0, Z.of_int 0);
    (Some 1, Z.of_int 5);
    (Some 0, Z.of_int 5);
    (Some 0, Z.of_int 3);
    (Some 0, Z.of_int 2)
  |] in
  let t2 : domain_element array = [|
    (Some 0, Z.of_int 0);
    (Some 1, Z.of_int 0);
    (Some 1, Z.of_int (-5));
    (Some 1, Z.of_int 5);
    (Some 1, Z.of_int 0);
    (Some 1, Z.of_int 1);
    (Some 1, Z.of_int 0)
  |] in
  let expected_result : zipped_domain = Some [|
    (0, (Some 0, Z.of_int 0), (Some 0, Z.of_int 0));
    (1, (Some 1, Z.of_int 0), (Some 1, Z.of_int 0));
    (2, (Some 0, Z.of_int 0), (Some 1, Z.of_int (-5)));
    (3, (Some 1, Z.of_int 5), (Some 1, Z.of_int 5));
    (4, (Some 0, Z.of_int 5), (Some 1, Z.of_int 0));
    (5, (Some 0, Z.of_int 3), (Some 1, Z.of_int 1));
    (6, (Some 0, Z.of_int 2), (Some 1, Z.of_int 0)) 
  |] in
  print_endline "TS_ZIP TEST 1";
  let r = ts_zip t1 t2 in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ==================================================================================================== *)
(* CONSTANT OFFSET *)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)
let const_offset t = match t with
  | (_, b) -> b 
(* ---------------------------------------------------------------------------------------------------- *)


(* ==================================================================================================== *)
(* DIFFERENCE *)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)
let diff t1 t2 = Z.((const_offset t1) - (const_offset t2))
(* ---------------------------------------------------------------------------------------------------- *)


(* ==================================================================================================== *)
(* COMPARISON OF ZIPPED ELEMENTS *)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)
let cmp_z_ref (x : domain_element) (y : domain_element) : int =
  match x, y with
  | (None, _), (None, _) -> 0
  | (None, _), (Some _, _) -> -1
  | (Some _, _), (None, _) -> 1
  | (Some ii, _), (Some ij, _) -> ii - ij 
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that values without reference variable are always less than values with reference variable *)
let _ = print_endline "";
  let x : domain_element = (None, Z.of_int 1) in
  let y : domain_element = (Some 0, Z.of_int 2) in
  print_endline "CMP_Z_REF TEST 1";
  let r = cmp_z_ref x y in
  print_string "assertion: ";
  if r < 0 then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that values without reference variable are always less than values with reference variable *)
let _ = print_endline "";
  let x : domain_element = (Some 0, Z.of_int 1) in
  let y : domain_element = (None, Z.of_int 2) in
  print_endline "CMP_Z_REF TEST 2";
  let r = cmp_z_ref x y in
  print_string "assertion: ";
  if r > 0 then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that values, where both have a reference variable, are compared by index of the
  reference variable. *)
let _ = print_endline "";
  let x : domain_element = (Some 2, Z.of_int 1) in
  let y : domain_element = (Some 4, Z.of_int 2) in
  print_endline "CMP_Z_REF TEST 3";
  let r = cmp_z_ref x y in
  print_string "assertion: ";
  if r < 0 then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that, when both items have reference variables, the items are only then equal, if
  the indices are equal. *)
let _ = print_endline "";
  let x : domain_element = (Some 2, Z.of_int 1) in
  let y : domain_element = (Some 2, Z.of_int 2) in
  print_endline "CMP_Z_REF TEST 4";
  let r = cmp_z_ref x y in
  print_string "assertion: ";
  if r = 0 then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)
  

(* ---------------------------------------------------------------------------------------------------- *)
let cmp_z (x : zipped_element) (y : zipped_element) = 
  match x, y with
  | (_, t1i, t2i), (_, t1j, t2j) -> 
    let diff_e1 = cmp_z_ref t1i t1j in
    if diff_e1 <> 0 then diff_e1 else
    let diff_e2 = cmp_z_ref t2i t2j in
    if diff_e2 <> 0 then diff_e2 else 
    Z.to_int (Z.((diff t1i t2i) - (diff t1j t2j)))
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that comparing two zipped elements is independent from the annotations *)
let _ = print_endline "";
  let x : zipped_element  = (0, (Some 0, Z.of_int 2), (None, Z.of_int 1)) in
  let x' : zipped_element = (2, (Some 0, Z.of_int 2), (None, Z.of_int 1)) in 
  let y : zipped_element  = (1, (Some 0, Z.of_int 2), (None, Z.of_int 1)) in 
  print_endline "CMP_Z TEST 1";
  let r1 = cmp_z x  y in
  let r2 = cmp_z x' y in
  print_string "assertion: ";
  if r1 = r2 then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that comparing two zipped elements is primarily determined by the first reference variable
  if they are not equal. *)
let _ = print_endline "";
  let x : zipped_element = (0, (Some 0, Z.of_int 1), (Some 2, Z.of_int 2)) in
  let y : zipped_element = (0, (Some 1, Z.of_int 0), (Some 1, Z.of_int 1)) in
  print_endline "CMP_Z TEST 2";
  let r = cmp_z x y in
  print_string "assertion: ";
  if r < 0 then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that the second reference variable determines the result of the comparison if the first
  reference variable is equal in both cases. *)
let _ = print_endline "";
  let x : zipped_element = (0, (Some 0, Z.of_int 0), (Some 2, Z.of_int 1)) in
  let y : zipped_element = (0, (Some 0, Z.of_int 0), (Some 1, Z.of_int 2)) in
  print_endline "CMP_Z TEST 3";
  let r = cmp_z x y in
  print_string "assertion: "; 
  if r > 0 then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that the difference in offsets determines the result of the comparison, if
  both the first and second reference variables are equal.  *)
let _ = print_endline "";
  let x : zipped_element = (0, (Some 0, Z.of_int 2), (Some 1, Z.of_int 1)) in
  let y : zipped_element = (0, (Some 0, Z.of_int 2), (Some 1, Z.of_int 2)) in
  print_endline "CMP_Z TEST 4";
  let r = cmp_z x y in
  print_string "assertion: "; 
  if r > 0 then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ==================================================================================================== *)
(* STABLE SORT OF EQUIVALENCES TO JOIN *)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)  
let sort_z_by_expr zts =
  match zts with
  | None -> ()
  | Some zts' -> Array.stable_sort cmp_z zts'
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that elements get sorted. *)
let _ = print_endline "";
  let zts : zipped_element array = [| (0, (None, Z.of_int 2), (None, Z.of_int 0)); 
    (1, (Some 2, Z.of_int 4), (None, Z.of_int 0)); (2, (Some 1, Z.of_int 3), (None, Z.of_int 0)) |] in
  let expected_result : zipped_element array = [| (0, (None, Z.of_int 2), (None, Z.of_int 0)); 
    (2, (Some 1, Z.of_int 3), (None, Z.of_int 0)); (1, (Some 2, Z.of_int 4), (None, Z.of_int 0))|] in
  print_endline "SORT_Z_BY_EXPR TEST 1";
  sort_z_by_expr (Some zts);
  print_string "assertion: ";
  if zts = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that elements that have the same first reference variable are closer after sorting
  than elements where the first reference variable is different. *)
let _ = print_endline "";
  let zts : zipped_element array = [| (0, (None, Z.of_int 2), (Some 0, Z.of_int 0)); 
    (1, (None, Z.of_int 4), (None, Z.of_int 1)); (2, (Some 1, Z.of_int 3), (None, Z.of_int 0)) |] in
  let expected_result : zipped_element array = [| (1, (None, Z.of_int 4), (None, Z.of_int 1)); 
    (0, (None, Z.of_int 2), (Some 0, Z.of_int 0)); (2, (Some 1, Z.of_int 3), (None, Z.of_int 0)) |] in 
  print_endline "SORT_Z_BY_EXPR TEST 2";
  sort_z_by_expr (Some zts);
  print_string "assertion: ";
  if zts = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that elements that have the same first and second reference variable are closer after sorting
  than elements where the first reference variable is different.. *)
let _ = print_endline "";
  let zts : zipped_element array = [| (0, (None, Z.of_int 2), (Some 0, Z.of_int 0)); 
    (1, (None, Z.of_int 4), (Some 2, Z.of_int 1)); (2, (None, Z.of_int 3), (Some 0, Z.of_int 0)) |] in
  let expected_result : zipped_element array = [| (0, (None, Z.of_int 2), (Some 0, Z.of_int 0)); 
    (2, (None, Z.of_int 3), (Some 0, Z.of_int 0)); (1, (None, Z.of_int 4), (Some 2, Z.of_int 1))|] in 
  print_endline "SORT_Z_BY_EXPR TEST 3";
  sort_z_by_expr (Some zts);
  print_string "assertion: ";
  if zts = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests sorting of a more complex example from the paper. The order of the equivalence classes is 
  different but the equivalence classes are created properly. *) 
let _ = print_endline "";
  let zts : zipped_element array = [|
    (0, (Some 0, Z.of_int 0), (Some 0, Z.of_int 0));
    (1, (Some 1, Z.of_int 0), (Some 1, Z.of_int 0));
    (2, (Some 0, Z.of_int 0), (Some 1, Z.of_int (-5)));
    (3, (Some 1, Z.of_int 5), (Some 1, Z.of_int 5));
    (4, (Some 0, Z.of_int 5), (Some 1, Z.of_int 0));
    (5, (Some 0, Z.of_int 3), (Some 1, Z.of_int 1));
    (6, (Some 0, Z.of_int 2), (Some 1, Z.of_int 0))
  |] in
  let expected_result : zipped_element array = [| 
    (0, (Some 0, Z.of_int 0), (Some 0, Z.of_int 0));
    (5, (Some 0, Z.of_int 3), (Some 1, Z.of_int 1));
    (6, (Some 0, Z.of_int 2), (Some 1, Z.of_int 0));
    (2, (Some 0, Z.of_int 0), (Some 1, Z.of_int (-5)));
    (4, (Some 0, Z.of_int 5), (Some 1, Z.of_int 0));
    (1, (Some 1, Z.of_int 0), (Some 1, Z.of_int 0));
    (3, (Some 1, Z.of_int 5), (Some 1, Z.of_int 5))
  |] in
  print_endline "SORT_Z_BY_EXPR TEST 4";
  sort_z_by_expr (Some zts);
  print_string "assertion: ";
  if zts = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)

 
(* ==================================================================================================== *)
(* SORTING BY ANNOTATION *)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)
let sort_annotated ats = 
  let cmp_annotated (x : annotated_element) (y : annotated_element) : int = 
    match x, y with
    | (i, _), (j, _) -> i - j
  in
  match ats with
  | None -> ()
  | Some ats' -> Array.stable_sort cmp_annotated ats' 
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests sorting of an annotated dataset by the annotation. The tests input is taken from the paper's
  example after processing the equivalence clases. *)
let _ = print_endline "";
  let zts : annotated_element array = [| 
    (0, (Some 0, Z.of_int 0));
    (5, (Some 5, Z.of_int 0));
    (6, (Some 5, Z.of_int (-1)));
    (2, (Some 2, Z.of_int 0));
    (4, (Some 2, Z.of_int 5));
    (1, (Some 1, Z.of_int 0));
    (3, (Some 1, Z.of_int 5))
  |] in
  let expected_result : annotated_element array = [|
    (0, (Some 0, Z.of_int 0));
    (1, (Some 1, Z.of_int 0));
    (2, (Some 2, Z.of_int 0));
    (3, (Some 1, Z.of_int 5));
    (4, (Some 2, Z.of_int 5));
    (5, (Some 5, Z.of_int 0));
    (6, (Some 5, Z.of_int (-1)))
  |] in
  print_endline "SORT_ANNOTATED TEST 1";
  sort_annotated (Some zts);
  print_string "assertion: ";
  if zts = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ==================================================================================================== *)
(* PROCESS EQUIVALENCE CLASSES *)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)
let is_const (x : zipped_element) =
  match x with
  | (_, (None, _), (None, _)) -> true
  | _ -> false 
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
let size_of_eq_class zts (start : int) : int = 
  let ref_elem = zts.(start) in
  let remaining = (Array.length zts) - start - 1 in
  let result = ref 0 in
  for i = 0 to remaining do
    let current_elem = zts.(start + i) in
    if cmp_z ref_elem current_elem = 0 then result := !result + 1
  done;
  !result 
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that the boundary case with one element in the array is correctly processed. *)
let _ = print_endline "";
  let zts = [|
    (0, (Some 0, Z.of_int 0), (Some 0, Z.of_int 0)); 
  |] in
  let start : int = 0 in
  let expected_result = 1 in
  print_endline "SIZE_OF_EQ_CLASS TEST 1";
  let r = size_of_eq_class zts start in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete" 
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that the annotation does not influence the size of the equivalence class. *)
let _ = print_endline "";
  let zts = [|
    (0, (Some 0, Z.of_int 0), (Some 0, Z.of_int 0)); 
    (1, (Some 0, Z.of_int 0), (Some 0, Z.of_int 0)); 
    (2, (Some 0, Z.of_int 0), (Some 0, Z.of_int 0)); 
  |] in
  let start : int = 0 in
  let expected_result = 3 in
  print_endline "SIZE_OF_EQ_CLASS TEST 2";
  let r = size_of_eq_class zts start in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete" 
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that elements in the equivalence class before the start element are ignored  *)
let _ = print_endline "";
  let zts = [|
    (0, (Some 0, Z.of_int 0), (Some 0, Z.of_int 0)); 
    (0, (Some 0, Z.of_int 0), (Some 0, Z.of_int 0)); 
    (0, (Some 0, Z.of_int 0), (Some 0, Z.of_int 0));
  |] in
  let start : int = 1 in
  let expected_result = 2 in
  print_endline "SIZE_OF_EQ_CLASS TEST 3";
  let r = size_of_eq_class zts start in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete" 
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests the size of an equivalence class with the example from the paper. *)
let _ = print_endline "";
  let zts = [|
    (0, (Some 0, Z.of_int 0), (Some 0, Z.of_int 0));
    (5, (Some 0, Z.of_int 3), (Some 1, Z.of_int 1));
    (6, (Some 0, Z.of_int 2), (Some 1, Z.of_int 0));
    (2, (Some 0, Z.of_int 0), (Some 1, Z.of_int (-5)));
    (4, (Some 0, Z.of_int 5), (Some 1, Z.of_int 0));
    (1, (Some 1, Z.of_int 0), (Some 1, Z.of_int 0));
    (3, (Some 1, Z.of_int 5), (Some 1, Z.of_int 5))
  |] in
  let start : int = 3 in
  let expected_result = 2 in
  print_endline "SIZE_OF_EQ_CLASS TEST 4";
  let r = size_of_eq_class zts start in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete" 
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
let least_index_var_in_eq_class zts start size : int * Z.t =
  let result = ref (0, Z.of_int 0) in 
  match zts.(start) with
    | (i, (_, b), (_, _)) -> result := (i, b);
  for i = start + 1 to start + size - 1 do
    match zts.(i) with
    | (j, (_, b), (_, _)) ->
      if j < fst !result then result := (j, b)
  done;
  !result 
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that the boundary case with one element in the array is correctly processed. *)
let _ = print_endline "";
  let zts = [| 
    (0, (Some 0, Z.of_int 0), (Some 0, Z.of_int 0)) 
  |] in
  let start : int = 0 in
  let size : int = 1 in 
  let expected_result =  (0, Z.of_int 0) in
  print_endline "LEAST_INDEX_VAR_IN_EQ_CLASS TEST 1";
  let r = least_index_var_in_eq_class zts start size in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests an equivalence class with multiple entries and the correct elemeent is returned. *)
let _ = print_endline "";
  let zts = [| 
    (2, (Some 0, Z.of_int 3), (Some 0, Z.of_int 0));
    (0, (Some 0, Z.of_int 4), (Some 0, Z.of_int 0));
    (1, (Some 0, Z.of_int 5), (Some 0, Z.of_int 0)) 
  |] in
  let start : int = 0 in
  let size : int = 3 in 
  let expected_result =  (0, Z.of_int 4) in
  print_endline "LEAST_INDEX_VAR_IN_EQ_CLASS TEST 2";
  let r = least_index_var_in_eq_class zts start size in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
let all_are_const_in_eq_class zts start size : bool = 
  let result = ref true in
  for i = start to start + size - 1 do
    if not (is_const zts.(i)) then result := false;
  done;
  !result
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests the boundary case where only one element in the array exists. *)
let _ = print_endline "";
  let zts = [|
    (0, (Some 0, Z.of_int 4), (Some 0, Z.of_int 0)) 
  |] in
  let start : int = 0 in
  let size : int = 1 in 
  let expected_result : bool = false in
  print_endline "ALL_ARE_CONST_IN_EQ_CLASS TEST 2";
  let r = all_are_const_in_eq_class zts start size in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests an equivalence class, where all elements are constant. *)
let _ = print_endline "";
  let zts = [|
    (2, (Some 0, Z.of_int 3), (None, Z.of_int 0));
    (0, (Some 1, Z.of_int 4), (None, Z.of_int 0));
    (2, (None, Z.of_int 3), (None, Z.of_int 0));
    (0, (None, Z.of_int 4), (None, Z.of_int 0));
    (1, (None, Z.of_int 5), (None, Z.of_int 0));
    (2, (None, Z.of_int 3), (None, Z.of_int 0));
    (0, (None, Z.of_int 4), (None, Z.of_int 0))
 
  |] in
  let start : int = 2 in
  let size : int = 3 in 
  let expected_result : bool = true in
  print_endline "ALL_ARE_CONST_IN_EQ_CLASS TEST 3";
  let r = all_are_const_in_eq_class zts start size in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests an equivalence class, where not all elements are constant. *)
let _ = print_endline "";
  let zts = [|
    (2, (Some 0, Z.of_int 3), (None, Z.of_int 0));
    (0, (Some 1, Z.of_int 4), (None, Z.of_int 0));
    (2, (None, Z.of_int 3), (None, Z.of_int 0));
    (0, (None, Z.of_int 4), (Some 0, Z.of_int 0));
    (1, (None, Z.of_int 5), (None, Z.of_int 0));
    (2, (None, Z.of_int 3), (None, Z.of_int 0));
    (0, (None, Z.of_int 4), (None, Z.of_int 0))
 
  |] in
  let start : int = 2 in
  let size : int = 3 in 
  let expected_result : bool = false in
  print_endline "ALL_ARE_CONST_IN_EQ_CLASS TEST 3";
  let r = all_are_const_in_eq_class zts start size in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)

let assign_vars_in_const_eq_class (ats : annotated_element array) (zts : zipped_element array) start size least_i least_b =     
  for i = start to start + size - 1 do
    match zts.(i) with
    | (ai, t1, t2) -> if Z.equal (diff t1 t2) (Z.of_int 0) then ats.(i) <- (ai, t1)
      else
        match t1 with
        | (_, bj) -> ats.(i) <- (ai, (Some least_i, Z.sub bj least_b))
  done
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests the assignment of variables in the annotated domain from a constant equivalence class,
  where once the least index variable is needed and once not.  *)
let _ = print_endline "";
  let ats : annotated_element array = [|
    (1, (None, Z.of_int 0));
    (0, (None, Z.of_int 0))
  |] in
  let zts : zipped_element array = [|
    (1, (None, Z.of_int 0), (None, Z.of_int 0));
    (0, (None, Z.of_int 1), (None, Z.of_int 0))
  |] in
  let start : int = 0 in
  let size : int = 2 in
  let least_i : int = 2 in
  let least_b : Z.t = Z.of_int 2 in
  let expected_result : annotated_element array = [|
    (1, (None, Z.of_int 0));
    (0, (Some 2, Z.of_int (-1)))
  |] in
  print_endline "ASSIGN_VARS_IN_CONST_EQ_CLASS TEST 1";
  assign_vars_in_const_eq_class ats zts start size least_i least_b;
  print_string "assertion: ";
  if ats = expected_result then print_endline "true" else print_endline "false";
  print_endline "test_complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests that the annotated variable index is determined by the zipped domain.
  Hence, the initial annotation, when creating the data structure is not relevant. *) 
let _ = print_endline "";
  let ats : annotated_element array = [|
    (1, (None, Z.of_int 0));
    (0, (None, Z.of_int 0))
  |] in
  let zts : zipped_element array = [|
    (0, (None, Z.of_int 0), (None, Z.of_int 0));
    (1, (None, Z.of_int 1), (None, Z.of_int 0))
  |] in
  let start : int = 0 in
  let size : int = 2 in
  let least_i : int = 2 in
  let least_b : Z.t = Z.of_int 2 in
  let expected_result : annotated_element array = [|
    (0, (None, Z.of_int 0));
    (1, (Some 2, Z.of_int (-1)))
  |] in
  print_endline "ASSIGN_VARS_IN_CONST_EQ_CLASS TEST 2";
  assign_vars_in_const_eq_class ats zts start size least_i least_b;
  print_string "assertion: ";
  if ats = expected_result then print_endline "true" else print_endline "false";
  print_endline "test_complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests a more complicated example inspired by the example from the paper. *)
let _ = print_endline "";
  let ats : annotated_element array = [|
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0))
  |] in
  let zts : zipped_element array = [|
    (0, (Some 0, Z.of_int 0), (Some 0, Z.of_int 0));
    (5, (Some 0, Z.of_int 3), (Some 1, Z.of_int 1));
    (6, (Some 0, Z.of_int 2), (Some 1, Z.of_int 0));
    (2, (None, Z.of_int 0), (None, Z.of_int (-5)));
    (4, (None, Z.of_int 5), (None, Z.of_int 5));
    (1, (Some 1, Z.of_int 0), (Some 1, Z.of_int 0));
    (3, (Some 1, Z.of_int 5), (Some 1, Z.of_int 5)) 
  |] in
  let start : int = 3 in
  let size : int = 2 in
  let least_i : int = 9 in
  let least_b : Z.t = Z.of_int 1 in
  let expected_result : annotated_element array = [|
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (2, (Some 9, Z.of_int (-1)));
    (4, (None, Z.of_int 5));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0)) 
  |] in
  print_endline "ASSIGN_VARS_IN_CONST_EQ_CLASS TEST 3";
  assign_vars_in_const_eq_class ats zts start size least_i least_b;
  print_string "assertion: ";
  if ats = expected_result then print_endline "true" else print_endline "false";
  print_endline "test_complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
let assign_vars_in_non_const_eq_class ats zts start size least_i least_b = 
  for i = start to start + size - 1 do
    match zts.(i) with
    | (ai, t1, _) -> 
      let bj = const_offset t1 in
      ats.(i) <- (ai, (Some least_i, Z.sub bj least_b))
  done 
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests the assignment of variables in a non const equivalence class. In the same way as for a
  constant equivalence class, the initial annotation in the target data structure is irrelevant. *)
let _ = print_endline "";
  let ats : annotated_element array = [|
    (0, (None, Z.of_int 0));
    (1, (None, Z.of_int 0))
  |] in
  let zts : zipped_element array = [|
    (1, (None, Z.of_int 0), (None, Z.of_int 0));
    (0, (Some 0, Z.of_int 1), (None, Z.of_int 0))
  |] in
  let start : int = 0 in
  let size : int = 2 in
  let least_i : int = 7 in
  let least_b : Z.t = Z.of_int 7 in
  let expected_result : annotated_element array = [|
    (1, (Some 7, Z.of_int (-7)));
    (0, (Some 7, Z.of_int (-6)))
  |] in
  print_endline "ASSIGN_VARS_IN_NON_CONST_EQ_CLASS TEST 1";
  assign_vars_in_non_const_eq_class ats zts start size least_i least_b;
  print_string "assertion: ";
  if ats = expected_result then print_endline "true" else print_endline "false";
  print_endline "test_complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests the more complicated example from the paper. *)
let _ = print_endline "";
  let ats : annotated_element array = [|
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0))
  |] in
  let zts : zipped_element array = [|
    (0, (Some 0, Z.of_int 0), (Some 0, Z.of_int 0));
    (5, (Some 0, Z.of_int 3), (Some 1, Z.of_int 1));
    (6, (Some 0, Z.of_int 2), (Some 1, Z.of_int 0));
    (2, (Some 0, Z.of_int 0), (Some 1, Z.of_int (-5)));
    (4, (Some 0, Z.of_int 5), (Some 1, Z.of_int 5));
    (1, (Some 1, Z.of_int 0), (Some 1, Z.of_int 0));
    (3, (Some 1, Z.of_int 5), (Some 1, Z.of_int 5)) 
  |] in
  let start : int = 1 in
  let size : int = 2 in
  let least_i : int = 9 in
  let least_b : Z.t = Z.of_int 1 in
  let expected_result : annotated_element array = [|
    (0, (None, Z.of_int 0));
    (5, (Some 9, Z.of_int 2));
    (6, (Some 9, Z.of_int 1)); 
    (0, (None, Z.of_int 0)); 
    (0, (None, Z.of_int 0)); 
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0));
    (0, (None, Z.of_int 0)) 
  |] in
  print_endline "ASSIGN_VARS_IN_NON_CONST_EQ_CLASS TEST 2";
  assign_vars_in_non_const_eq_class ats zts start size least_i least_b;
  print_string "assertion: ";
  if ats = expected_result then print_endline "true" else print_endline "false";
  print_endline "test_complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
let process_eq_classes (zts : zipped_domain) = 
  match zts with
  | None -> None
  | Some zts' ->
    let result = Array.make (Array.length zts') (0, (None, Z.of_int 0)) in
    let i = ref 0 in
    while !i < Array.length zts' do 
      let n = size_of_eq_class zts' !i in 
      (if n = 1 then
         let ztsi = zts'.(!i) in
         match ztsi with
         | (i', t1, t2) -> if is_const ztsi && Z.equal (diff t1 t2) (Z.of_int 0) then 
             result.(!i) <- (i', (None, const_offset t1))
           else result.(!i) <- (i', (Some i', Z.of_int 0))
       else
        let (least_i, least_b) = least_index_var_in_eq_class zts' !i n in
        (if all_are_const_in_eq_class zts' !i n then
          assign_vars_in_const_eq_class result zts' !i n least_i least_b
        else assign_vars_in_non_const_eq_class result zts' !i n least_i least_b);
      ); 
      i := !i + n;
    done;
    Some result 
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests a non constnat equivalence class with one element. *)
let _ = print_endline "";
  let zts : zipped_domain = Some [|
    (0, (None, Z.of_int 2), (Some 0, Z.of_int 0))
  |] in
  let expected_result : annotated_element array option = Some [|
    (0, (Some 0, Z.of_int 0))
  |] in
  print_endline "PROCESS_EQ_CLASSES TEST 1";
  let r = process_eq_classes zts in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test_complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests a constant equivalence class with one element. *)
let _ = print_endline "";
  let zts : zipped_domain = Some [|
    (0, (None, Z.of_int 2), (None, Z.of_int 2)) 
  |] in
  let expected_result : annotated_element array option = Some [|
    (0, (None, Z.of_int 2))
  |] in
  print_endline "PROCESS_EQ_CLASSES TEST 2";
  let r = process_eq_classes zts in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test_complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests a constant equivalence class with multiple elements. *)
let _ = print_endline "";
  let zts : zipped_domain = Some [|
    (0, (None, Z.of_int 2), (None, Z.of_int 2));
    (1, (None, Z.of_int 3), (None, Z.of_int 3)) 
  |] in
  let expected_result : annotated_element array option = Some [|
    (0, (None, Z.of_int 2));
    (1, (None, Z.of_int 3))
  |] in
  print_endline "PROCESS_EQ_CLASSES TEST 3";
  let r = process_eq_classes zts in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test_complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests two equivalence classes. *)
let _ = print_endline "";
  let zts : zipped_domain = Some [|
    (0, (Some 0, Z.of_int 2), (None, Z.of_int 2));
    (3, (Some 0, Z.of_int 3), (None, Z.of_int 3));
    (1, (None, Z.of_int 2), (None, Z.of_int 2));
    (2, (None, Z.of_int 3), (None, Z.of_int 3)) 
  |] in
  let expected_result : annotated_element array option = Some [|
    (0, (Some 0, Z.of_int 0));
    (3, (Some 0, Z.of_int 1));
    (1, (None, Z.of_int 2));
    (2, (None, Z.of_int 3))
  |] in
  print_endline "PROCESS_EQ_CLASSES TEST 4";
  let r = process_eq_classes zts in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test_complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests the more complicated example from the paper. *)
let _ = print_endline "";
  let zts : zipped_domain = Some [|
    (0, (Some 0, Z.of_int 0), (Some 0, Z.of_int 0));
    (5, (Some 0, Z.of_int 3), (Some 1, Z.of_int 1));
    (6, (Some 0, Z.of_int 2), (Some 1, Z.of_int 0));
    (2, (Some 0, Z.of_int 0), (Some 1, Z.of_int (-5)));
    (4, (Some 0, Z.of_int 5), (Some 1, Z.of_int 0));
    (1, (Some 1, Z.of_int 0), (Some 1, Z.of_int 0));
    (3, (Some 1, Z.of_int 5), (Some 1, Z.of_int 5)) 
  |] in
  let expected_result : annotated_element array option = Some [|
    (0, (Some 0, Z.of_int 0));
    (5, (Some 5, Z.of_int 0));
    (6, (Some 5, Z.of_int (-1))); 
    (2, (Some 2, Z.of_int 0)); 
    (4, (Some 2, Z.of_int 5)); 
    (1, (Some 1, Z.of_int 0));
    (3, (Some 1, Z.of_int 5)) 
  |] in
  print_endline "PROCESS_EQ_CLASSES TEST 5";
  let r = process_eq_classes zts in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test_complete"
(* ---------------------------------------------------------------------------------------------------- *)


(* ==================================================================================================== *)
(* STRIP ANNOTATION *)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)
let strip_annotation (ats : annotated_domain) : domain = 
  match ats with
    | None -> None
    | Some ats' -> Some (Array.map snd ats')
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* tests sorting of an annotated dataset by the annotation. The tests input is taken from the paper's
  example after processing the equivalence clases. *)
let _ = print_endline "";
  let zts : annotated_domain = Some [| 
    (0, (Some 0, Z.of_int 0));
    (1, (Some 1, Z.of_int 0));
    (2, (Some 2, Z.of_int 0));
    (3, (Some 1, Z.of_int 5));
    (4, (Some 2, Z.of_int 5));
    (5, (Some 5, Z.of_int 0));
    (6, (Some 5, Z.of_int (-1)))
  |] in
  let expected_result : domain = Some [|
    (Some 0, Z.of_int 0);
    (Some 1, Z.of_int 0);
    (Some 2, Z.of_int 0);
    (Some 1, Z.of_int 5);
    (Some 2, Z.of_int 5);
    (Some 5, Z.of_int 0);
    (Some 5, Z.of_int (-1))
  |] in
  print_endline "STRIP_ANNOTATION TEST 1";
  let r = strip_annotation zts in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)
 

(* ==================================================================================================== *)
(* JOIN - least upper bound *)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)
let _join (t1 : domain) (t2 : domain) = 
  match t1, t2 with
  | None, t2' -> t2'
  | t1', None -> t1'
  | Some t1', Some t2' -> 
    let zipped = ts_zip t1' t2' in
    sort_z_by_expr zipped;
    let annotated = process_eq_classes zipped in
    sort_annotated annotated;
    let result = strip_annotation annotated in
    result;
(* ---------------------------------------------------------------------------------------------------- *) 


