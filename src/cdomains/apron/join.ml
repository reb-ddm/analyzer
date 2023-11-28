(*
  TODO:
  * finish implementation
    - function 'assign_vars_in_const_eq_class'
    - function 'assign_vars_in_non_const_eq_class'
  * test implementation
  * write documentation
*)

type domain_element = int option * Z.t
type domain = domain_element array option
type zipped_element = int * domain_element * domain_element
type zipped_domain = zipped_element array option
type annotated_element = int * domain_element
type annotated_domain = annotated_element array option

(* least upper bound *)
let _join (t1 : domain) (t2 : domain) =
  let ts_zip t1 t2 : zipped_domain =
    if Array.length t1 <> Array.length t2 then None else
    let zts = Array.init (Array.length t1) (fun (i : int) -> (i, t1.(i), t2.(i))) in
    Some zts
  in
  let cmp_z (x : zipped_element) (y : zipped_element) = 
    let cmp_z_ref (x : domain_element) (y : domain_element) : int =
      match x, y with
      | (None, _), (None, _) -> 0
      | (None, _), (Some ij, _) -> -ij
      | (Some ii, _), (None, _) -> ii
      | (Some ii, _), (Some ij, _) -> ii - ij 
    in
    let const_offset t = match t with
      | (_, b) -> b
    in
    let diff t1 t2 = Z.((const_offset t1) - (const_offset t2)) in
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
      let remaining = (Array.length zts) - start in
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
      for i = start + 1 to start + size do
        match zts.(i) with
        | (j, (_, b), (_, _)) ->
          if j < fst !result then result := (j, b)
      done;
      !result
    in
    let all_are_const_in_eq_class zts start size : bool = 
      let result = ref true in
      for i = start to start + size do
        if not (is_const zts.(i)) then result := false;
      done;
      !result;
    in
    let assign_vars_in_const_eq_class _ats _zts _start _size _least_i _least_b = () in
    let assign_vars_in_non_const_eq_class _ats _zts _start _size _least_i _least_b = () in
    match zts with
    | None -> None
    | Some zts' ->
      let result = Array.make (Array.length zts') (0, (None, Z.of_int 0)) in
      let i = ref 0 in
      while !i < Array.length zts' do 
        let n = size_of_eq_class zts' !i in 
        (if n = 1 then () else
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
  | Some t1', Some t2' -> 
    let zipped = ts_zip t1' t2' in
    sort_z_by_expr zipped;
    let annotated = process_eq_classes zipped in
    sort_annotated annotated;
    let result = strip_annotation annotated in
    Some result;
  | _ -> None









