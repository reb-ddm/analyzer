(*
TODO:
  check if all elements in eq class are constant can be checked in O(1) instead of O(n),
  since only one elemenet has to be checked and the other ones are equivalent.

  The min index and right hand side value can be performed, when calculating
  the size of an equivalence class. Then, only one pass over the dataset is
  necessary.

  rename cmp_z_ref to cmp_ref
*)

(* ==================================================================================================== *)
(* TYPES *)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)
(* This datatype represents equalities that we want to store. Each equality consists of a variable
  that we want to assign a value to. The values that we can assign is either just a constant value
  of the sum of the value of a reference variable plus a constant offset.
  The optional integer in this datatype represents the index of the reference variable in the array
  of equalities. The constant offset is represented by a value of type 'Z.t', which is defined
  in the Zarith library, which allows to create integers of arbitrary size.
*)
type domain_element = int option * Z.t
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* The domain datatype represents a conjunction of variable differences. An individual variable
  difference is determined by the type 'domain_element' above, where the assigned variable is 
  determined by the index of the data element in this array. A 'domain' object has an optional
  quantifier, since a conjunction of assignments can possibly be 'false', represented by the
  value 'None', when the assignment is unsatisfiable for all assignments.
*)
type domain = domain_element array option
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* While computing the join of two conjunctions of equalities, we have to consider the assignments
  of both conjunctions for the same variable as single unit. Furthermore, we will loose the implicit
  knowledge of the assigned variable. Therefore, we consider triples of values, where the first value
  is the explicit statement of the assigned variable. The second and third variable are both
  assignments to that variable.
*)
type zipped_element = int * domain_element * domain_element
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* Analogously to the domain definition, which is an optional array of domain elements, we consider
  arrays of the aforementioned tripes. Therefore, this datatype represents an optional array
  of the previous data type.
*)
type zipped_domain = zipped_element array option
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* When processing the equivalence classes as are defined on the combination of both conjunctions
  considered jointly, we will will determine the resulting assignment to one variable from
  one triple as described above. The resulting variable assignment will be stored in an own array
  that keeps the explicit statement of the variable index that is being assigned to. Therefore
  This data type is a pair of this variable index and the target assignement.
*)
type annotated_element = int * domain_element
(* ---------------------------------------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------------------------------------- *)
(* As in the previous cases above, this data type represents the conjunction of assignements as
  defined by the data type above. In this case the assigned variables will be represented by the
  annotated index in each data element and not by the index of the element in the array itself.
*)
type annotated_domain = annotated_element array option
(* ---------------------------------------------------------------------------------------------------- *)


(* ==================================================================================================== *)
(* ALGORITHM
   The follwing algorithm is a direct translation of the paper's algorithm in lemma 4.4.
   It computes the 'join', the least upper bound, of two conjunctions of equalities.
   The algorithm operates by considering both assignments for each variable and treating them
   as single unit. These elements need to be sorted according to their equivalence classes,
   which depend on both reference variables and the differences in constant offsets. Since 
   this sort operation changes the order of elements and beforehand the index of an element in the 
   array implicitly determined the assigned variable, this information has to be preserved. Hence,
   when building a single unit of two assignments to the same variable, we also have to store
   the index explicitly.
   Depeding on the type of equivalence class, whether it contains a single element, if not, whether
   all elements in the equivalence class do not depend on any other reference variable, the final
   assignments in the result data structure are made. Since ordering the data elements into their
   respective equivalence classes changes their order, the original ordering has to be
   restored.
   Finally, the result has to be expressed in the same data type as the inputs to the join
   function. Since the annotations still remain, the last step is to remove them to obtain the
   value that can be returned and hides all intermediate data structures.
*)
(* ==================================================================================================== *)

(* ---------------------------------------------------------------------------------------------------- *)
let join (t1 : domain) (t2 : domain) =
  let ts_zip t1 t2 : zipped_domain =
    if Array.length t1 <> Array.length t2 then None else
    let zts = Array.init (Array.length t1) (fun (i : int) -> (i, t1.(i), t2.(i))) in
    Some zts
  in
  let const_offset t = match t with
    | (_, b) -> b 
  in
  let diff t1 t2 = Z.((const_offset t1) - (const_offset t2))
  in
  let cmp_z (x : zipped_element) (y : zipped_element) = 
    let cmp_z_ref (x : domain_element) (y : domain_element) : int =
      match x, y with
      | (None, _), (None, _) -> 0
      | (None, _), (Some _, _) -> -1
      | (Some _, _), (None, _) -> 1
      | (Some ii, _), (Some ij, _) -> ii - ij 
    in
    match x, y with
    | (_, t1i, t2i), (_, t1j, t2j) -> 
      let diff_e1 = cmp_z_ref t1i t1j in
      if diff_e1 <> 0 then diff_e1 else
      let diff_e2 = cmp_z_ref t2i t2j in
      if diff_e2 <> 0 then diff_e2 else 
      Z.to_int (Z.((diff t1i t2i) - (diff t1j t2j)))
  in
  let sort_z_by_expr zts =
    match zts with
    | None -> ()
    | Some zts' -> Array.stable_sort cmp_z zts'
  in
  let sort_annotated ats = 
    let cmp_annotated (x : annotated_element) (y : annotated_element) : int = 
      match x, y with
      | (i, _), (j, _) -> i - j
    in
    match ats with
    | None -> ()
    | Some ats' -> Array.stable_sort cmp_annotated ats'
  in
  let process_eq_classes (zts : zipped_domain) = 
    let is_const (x : zipped_element) =
      match x with
      | (_, (None, _), (None, _)) -> true
      | _ -> false
    in
    let size_of_eq_class zts (start : int) : int = 
      let ref_elem = zts.(start) in
      let remaining = (Array.length zts) - start - 1 in
      let result = ref 0 in
      for i = 0 to remaining do
        let current_elem = zts.(start + i) in
        if cmp_z ref_elem current_elem = 0 then result := !result + 1
      done;
      !result
    in
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
    in
    let all_are_const_in_eq_class zts start size : bool = 
      let result = ref true in
      for i = start to start + size - 1 do
        if not (is_const zts.(i)) then result := false;
      done;
      !result
    in
    let assign_vars_in_const_eq_class (ats : annotated_element array) (zts : zipped_element array) start size least_i least_b =     
      for i = start to start + size - 1 do
        match zts.(i) with
        | (ai, t1, t2) -> if Z.equal (diff t1 t2) (Z.of_int 0) then ats.(i) <- (ai, t1)
          else
            match t1 with
            | (_, bj) -> ats.(i) <- (ai, (Some least_i, Z.sub bj least_b))
      done
    in
    let assign_vars_in_non_const_eq_class ats zts start size least_i least_b = 
      for i = start to start + size - 1 do
        match zts.(i) with
        | (ai, t1, _) -> 
          let bj = const_offset t1 in
          ats.(i) <- (ai, (Some least_i, Z.sub bj least_b))
      done
    in
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
  in
  let strip_annotation (ats : annotated_domain) : domain = 
    match ats with
      | None -> None
      | Some ats' -> Some (Array.map snd ats')
  in
  match t1, t2 with
  | None, t2' -> t2'
  | t1', None -> t1'
  | Some t1', Some t2' -> 
    let zipped = ts_zip t1' t2' in
    sort_z_by_expr zipped;
    let annotated = process_eq_classes zipped in
    sort_annotated annotated;
    let result = strip_annotation annotated in
    result
(* ---------------------------------------------------------------------------------------------------- *)


(* ==================================================================================================== *)
(* TESTS *)
(* ==================================================================================================== *)


(* ---------------------------------------------------------------------------------------------------- *)
(* this test tests the overall behavior of the join function. It uses as inputs the conjunctions 
  as in the paper' example. *)
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
    (Some 1, Z.of_int (-5));
    (Some 1, Z.of_int 5);
    (Some 1, Z.of_int 0);
    (Some 1, Z.of_int 1);
    (Some 1, Z.of_int 0)
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
  print_endline "JOIN TEST 1";
  let r = join t1 t2 in
  print_string "assertion: ";
  if r = expected_result then print_endline "true" else print_endline "false";
  print_endline "test complete"
(* ---------------------------------------------------------------------------------------------------- *)

