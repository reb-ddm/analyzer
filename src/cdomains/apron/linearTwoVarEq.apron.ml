(** OCaml implementation of the affine equalities domain.

    @see <https://doi.org/10.1007/BF00268497> Karr, M. Affine relationships among variables of a program. *)

(** Abstract states in the newly added domain are represented by structs containing a matrix and an apron environment.
    Matrices are modeled as proposed by Karr: Each variable is assigned to a column and each row represents a linear 
affine relationship that must hold at the corresponding program point.
    The apron environment is hereby used to organize the order of columns and variables. *)

(*
	For our analysis it suffices to store an array, where for each variable its linear term is stored.
	Similar to the matrix analysis variables have to be organized in an order to be stored in the array.
	To this end, the apron environment may be used, too.
	In contrast to the matrix version, our version does not have a distinct index which determines the
	constant offset of the linear term. Therefore, the array has to not only store the variable
	w.r.t. which it is set equal to, but also the constant offset. Thus, each array index
	stores a pair of a variable name/index and the constant offset.
*)

open Batteries
open GoblintCil
open Pretty
module M = Messages
open Apron
(* open VectorMatrix *)

(* =================================================================================================== *)
(* =================================================================================================== *)

module Mpqf = struct
  include Mpqf
  let compare = cmp
  let zero = of_int 0
  let one = of_int 1
  let mone = of_int (-1)

  let get_den x = Z_mlgmpidl.z_of_mpzf @@ Mpqf.get_den x

  let get_num x = Z_mlgmpidl.z_of_mpzf @@ Mpqf.get_num x
  let hash x = 31 * (Z.hash (get_den x)) + Z.hash (get_num x)
end

(* =================================================================================================== *)
(* =================================================================================================== *)




module Var = SharedFunctions.Var
module V = RelationDomain.V(Var)




(* =================================================================================================== *)
(* =================================================================================================== *)


(** It defines the type t of the affine equality domain (a struct that contains an optional matrix and an apron environment) and 
provides the functions needed for handling variables (which are defined by RelationDomain.D2) such as add_vars remove_vars.
    Furthermore, it provides the function get_coeff_vec that parses an apron expression into a vector of coefficients if the apron 
expression has an affine form. *)

(*
	Our analysis should utilize a struct t containing an optional array and an apron environment.
	The former argument should be optional to represent the bottom value of the lattice.
	Our version should (probably) define the same set of functions as the matrix version.
*)
module VarManagement (Vec: AbstractVector) (* (Mx: AbstractMatrix) *) =
struct
  include SharedFunctions.EnvOps
  (* TODO: In our analysis, each array entry needs to define the reference variable and the const. offset.
     Do we have to change the arguement for the module Vec?
  *)
  module Vector = Vec (Mpqf)
  (* Our vector needs to reference the variables. By which datatype is this supposed to happen? *)
  (* module Vector = Vec (Pair Int Mpqf) *)
  (* module Matrix = Mx(Mpqf) (Vec) *)



(* ---------------------------------------------------------------------------------------------------- *)

  type t = {
    (* TODO: What does the t in Matrix.t stand for? *)

    (* mutable d :  Matrix.t option; *)
    (* mutable d : Array.t option *)
    mutable env : Environment.t
  }
  [@@deriving eq, ord, hash]

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let empty_env = Environment.make [||] [||]

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  (* TODO: Why is the bottom element a struct containing an empty matrix?
     What is the difference between bot and bot_env in terms of their usage?
  *)
  let bot () =
    (* {d = Some (Matrix.empty ()); env = empty_env} *)
    (* {d = Some (Array.empty ()); env = empty_env} *)

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let bot_env = {d = None; env = empty_env}

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let is_bot_env t = t.d = None

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)
 
  let copy t = 
	(* {t with d = Option.map Matrix.copy t.d} *)
	(* {t with d = Option.map Array.copy t.d} *)

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  (* TODO: Add index to the array. *)
  let dim_add (ch: Apron.Dim.change) m =
    Array.iteri (fun i x -> ch.dim.(i) <- x + i) ch.dim;
    (* Matrix.add_empty_columns m ch.dim *)
    (* Array.add_empty_field m ch.dim *)

  let dim_add ch m = timing_wrap "dim add" (dim_add ch) m

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  (* TODO: remove index from array. *)
  let dim_remove (ch: Apron.Dim.change) m del =
    (* if Array.length ch.dim = 0 || Matrix.is_empty m then m else (
      Array.iteri (fun i x-> ch.dim.(i) <- x + i) ch.dim;
      let m' = if not del then let m = Matrix.copy m in Array.fold_left (fun y x -> Matrix.reduce_col_with y x; y) m ch.dim else m in
      Matrix.remove_zero_rows @@ Matrix.del_cols m' ch.dim) *)

  let dim_remove ch m del = timing_wrap "dim remove" (dim_remove ch m) del

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let change_d t new_env add del =
    if Environment.equal t.env new_env then t else
      let dim_change = if add then Environment.dimchange t.env new_env
        else Environment.dimchange new_env t.env
      in match t.d with
      | None -> bot_env
      | Some m -> {d = Some (if add then dim_add dim_change m else dim_remove dim_change m del); env = new_env}

  let change_d t new_env add del = timing_wrap "dimension change" (change_d t new_env add) del

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let add_vars t vars =
    let t = copy t in
    let env' = add_vars t.env vars in
    change_d t env' true false

  let add_vars t vars = timing_wrap "add_vars" (add_vars t) vars

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let drop_vars t vars del =
    let t = copy t in
    let env' = remove_vars t.env vars in
    change_d t env' false del

  let drop_vars t vars = timing_wrap "drop_vars" (drop_vars t) vars

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let remove_vars t vars = drop_vars t vars false

  let remove_vars t vars = timing_wrap "remove_vars" (remove_vars t) vars

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let remove_vars_with t vars =
    let t' = remove_vars t vars in
    t.d <- t'.d;
    t.env <- t'.env

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let remove_filter t f =
    let env' = remove_filter t.env f in
    change_d t env' false false

  let remove_filter t f = timing_wrap "remove_filter" (remove_filter t) f

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let remove_filter_with t f =
    let t' = remove_filter t f in
    t.d <- t'.d;
    t.env <- t'.env

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let keep_filter t f =
    let t = copy t in
    let env' = keep_filter t.env f in
    change_d t env' false false

  let keep_filter t f = timing_wrap "keep_filter" (keep_filter t) f

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let keep_vars t vs =
    let t = copy t in
    let env' = keep_vars t.env vs in
    change_d t env' false false

  let keep_vars t vs = timing_wrap "keep_vars" (keep_vars t) vs

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let vars t = vars t.env

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let mem_var t var = Environment.mem_var t.env var

(* ---------------------------------------------------------------------------------------------------- *)

  include ConvenienceOps(Mpqf)

(* ---------------------------------------------------------------------------------------------------- *)

  let get_c v = match Vector.findi (fun x -> x <>: Mpqf.zero) v with
    | exception Not_found -> Some Mpqf.zero
    | i when Vector.compare_length_with v (i + 1) = 0 -> Some (Vector.nth v i)
    | _ -> None

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)
    
(* Parses a Texpr to obtain a coefficient + const (last entry) vector to repr. an affine relation.
   Returns None if the expression is not affine *)

(*
	In our analysis, we need to parse a vector of reference variables and constant offsets.
	We need to return None if the expression is not linear w.r.t. one other variable.
*)

  let get_coeff_vec (t: t) texp =
(* 
    let open Apron.Texpr1 in
    let exception NotLinear in
    let zero_vec = Vector.zero_vec @@ Environment.size t.env + 1 in
    let neg v = Vector.map_with (fun x -> Mpqf.mone *: x) v; v in
    let is_const_vec v = Vector.compare_length_with (Vector.filteri (fun i x -> (*Inefficient*)
        Vector.compare_length_with v (i + 1) > 0 && x <>: Mpqf.zero) v) 1 = 0
    in
    let rec convert_texpr texp =
      begin match texp with
        (*If x is a constant, replace it with its const. val. immediately*)
        | Cst x -> let of_union union =
                     let open Coeff in
                     match union with
                     | Interval _ -> failwith "Not a constant"
                     | Scalar x -> (match x with
                         | Float x -> Mpqf.of_float x
                         | Mpqf x -> x
                         | Mpfrf x -> Mpfr.to_mpq x) in Vector.set_val zero_vec ((Vector.length zero_vec) - 1) (of_union x)
        | Var x ->
          let zero_vec_cp = Vector.copy zero_vec in
          let entry_only v = Vector.set_val_with v (Environment.dim_of_var t.env x) Mpqf.one; v in
          begin match t.d with
            | Some m -> let row = Matrix.find_opt (fun r -> Vector.nth r (Environment.dim_of_var t.env x) =: Mpqf.one) m in
              begin match row with
                | Some v when is_const_vec v ->
                  Vector.set_val_with zero_vec_cp ((Vector.length zero_vec) - 1) (Vector.nth v (Vector.length v - 1)); zero_vec_cp
                | _ -> entry_only zero_vec_cp end
            | None -> entry_only zero_vec_cp end
        | Unop (u, e, _, _) ->
          begin match u with
            | Neg -> neg @@ convert_texpr e
            | Cast -> convert_texpr e (*Ignore since casts in apron are used for floating point nums and rounding in contrast to CIL casts*)
            | Sqrt -> raise NotLinear end
        | Binop (b, e1, e2, _, _) ->
          begin match b with
            | Add -> let v1 = convert_texpr e1 in Vector.map2_with (+:) v1 (convert_texpr e2); v1
            | Sub -> let v1 = convert_texpr e1 in Vector.map2_with (+:) v1 (neg @@ convert_texpr e2); v1
            | Mul ->
              let x1, x2 = convert_texpr e1, convert_texpr e2 in
              begin match get_c x1, get_c x2 with
                | _, Some c -> Vector.apply_with_c_with ( *:) c x1; x1
                | Some c, _ -> Vector.apply_with_c_with ( *:) c x2; x2
                | _, _ -> raise NotLinear end
            | _ -> raise NotLinear end
      end
    in match convert_texpr texp with
    | exception NotLinear -> None
    | x -> Some(x) *)

  let get_coeff_vec t texp = timing_wrap "coeff_vec" (get_coeff_vec t) texp

(* ---------------------------------------------------------------------------------------------------- *)

end

(* =================================================================================================== *)
(* =================================================================================================== *)










(* =================================================================================================== *)
(* =================================================================================================== *)

(** As it is specifically used for the new affine equality domain, it can only provide bounds if the expression contains known constants only and in that case, min and max are the same. *)

(*
	TODO: Does our domain need similar functionality?
*)

module ExpressionBounds (Vc: AbstractVector) (* (Mx: AbstractMatrix) *): (SharedFunctions.ConvBounds with type t = VarManagement(Vc) (* (Mx) *) .t) =
struct
  include VarManagement (Vc) (Mx)


(* ---------------------------------------------------------------------------------------------------- *)

  let bound_texpr t texpr =
    let texpr = Texpr1.to_expr texpr in
    match get_coeff_vec t texpr  with
    | Some v -> begin match get_c v with
        | Some c when Mpqf.get_den c = IntOps.BigIntOps.one ->
          let int_val = Mpqf.get_num c
          in Some int_val, Some int_val
        | _ -> None, None end
    | _ -> None, None


  let bound_texpr d texpr1 =
    let res = bound_texpr d texpr1 in
    match res with
    | Some min, Some max ->  if M.tracing then M.tracel "bounds" "min: %s max: %s" (IntOps.BigIntOps.to_string min) (IntOps.BigIntOps.to_string max); res
    | _ -> res

  let bound_texpr d texpr1 = timing_wrap "bounds calculation" (bound_texpr d) texpr1

(* ---------------------------------------------------------------------------------------------------- *)

end

(* =================================================================================================== *)
(* =================================================================================================== *)










(* =================================================================================================== *)
(* =================================================================================================== *)

(*
	Here, the lattice operations are defined.
	We (probably) need the same functions for our analysis.
*)

module D(Vc: AbstractVector) (* (Mx: AbstractMatrix) *) =
struct
  include Printable.Std
  include ConvenienceOps (Mpqf)
  include VarManagement (Vc) (* (Mx) *)

  module Bounds = ExpressionBounds (Vc) (* (Mx) *)

  module Convert = SharedFunctions.Convert (V) (Bounds) (struct let allow_global = true end) (SharedFunctions.Tracked)

  type var = V.t


(* ---------------------------------------------------------------------------------------------------- *)

  let show t =
    (*
    let conv_to_ints row =
      let module BI = IntOps.BigIntOps in
      let row = Array.copy @@ Vector.to_array row
      in
      for i = 0 to Array.length row -1 do
        let val_i = Mpqf.of_mpz @@ Z_mlgmpidl.mpzf_of_z @@ Mpqf.get_den row.(i)
        in Array.iteri(fun j x -> row.(j) <- val_i *: x)  row
      done;
      let int_arr = Array.init (Array.length row) (fun i -> Mpqf.get_num row.(i))
      in let div = Mpqf.of_mpz @@ Z_mlgmpidl.mpzf_of_z @@ Array.fold_left BI.gcd int_arr.(0) int_arr
      in Array.iteri (fun i x -> row.(i) <- x /: div) row;
      Vector.of_array @@ row
    in
    let vec_to_constraint vec env =
      let vars, _ = Environment.vars env
      in let dim_to_str var =
           let vl =  Vector.nth vec (Environment.dim_of_var env var)
           in let var_str = Var.to_string var
           in if vl =: Mpqf.one then "+" ^ var_str
           else if vl =: Mpqf.mone then "-" ^ var_str
           else if vl <: Mpqf.mone then Mpqf.to_string vl ^ var_str
           else if vl >: Mpqf.one then Format.asprintf "+%s" (Mpqf.to_string vl) ^ var_str
           else ""
      in
      let c_to_str vl =
        if vl >: Mpqf.zero then "-" ^ Mpqf.to_string vl
        else if vl <: Mpqf.zero then "+" ^ Mpqf.to_string vl
        else ""
      in
      let res = (String.concat "" @@ Array.to_list @@ Array.map dim_to_str vars)
                ^ (c_to_str @@ Vector.nth vec (Vector.length vec - 1)) ^ "=0"
      in if String.starts_with res "+" then String.sub res 1 (String.length res - 1) else res
    in
    match t.d with
    | None -> "Bottom Env"
    | Some m when Matrix.is_empty m -> "⊤"
    | Some m ->
      let constraint_list = List.init (Matrix.num_rows m) (fun i -> vec_to_constraint (conv_to_ints @@ Matrix.get_row m i) t.env)
      in Format.asprintf "%s" ("[|"^ (String.concat "; " constraint_list) ^"|]")
  *)

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let pretty () (x:t) = text (show x)

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let printXml f x = BatPrintf.fprintf f "<value>\n<map>\n<key>\nmatrix\n</key>\n<value>\n%s</value>\n<key>\nenv\n</key>\n<value>\n%s</value>\n</map>\n</value>\n" (XmlUtil.escape (Format.asprintf "%s" (show x) )) (XmlUtil.escape (Format.asprintf "%a" (Environment.print: Format.formatter -> Environment.t -> unit) (x.env)))

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let name () = (* "affeq" *)

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let to_yojson _ = failwith "ToDo Implement in future"

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let is_bot t = equal t (bot ())

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let bot_env = {d = None; env = Environment.make [||] [||]}

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let is_bot_env t = t.d = None

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let top () = failwith "D.top ()"

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let is_top _ = false

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let is_top_env t = (* (not @@ Environment.equal empty_env t.env) && GobOption.exists Matrix.is_empty t.d *)

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

(*
	Calculate the greatest lower bound as described in the paper.

	(* calculates the greatest lower bound of two conjunctions of equivalences.
	   This is done recursively on t2. *)
	let meet bot _ = bot
	    meet t1 [] = t1
	    meet t1 (t#t2) = 
		meet (add_conj t1 t) t2

	(* adds an equivalence t to the normalised conjunction of equivalences ts,
	   as described by lemma 3.2 *)
	let add_conj ts t =
	    match t of
		(i, b) => match ts[i] of
		    b' => of b = b' then ts else bot
	            (h, b') => subst_var ts h (b - b')
		(i, j, b) => match ts[i] of
		    b_1 => subst_var ts j (b_1 - b)
		    (h_1, b_1) => match ts[j] of
			b_2 => subst_var ts i (b_2 + b)
			(h_2, b_2) => 
			    if h_1 = h_2 then
			        if b_1 = b_2 + b then ts else bot
			    else if h_1 < h_2 then 
				subst_var ts h_2 (h_1, b_1 - (b + b_2))
			    else subst_var ts h_1 (h_2, b + b_2 - b_1)
	
	(* substitutes every occurrence of the variable x in the array of equivalences ts by a new term t *)
	let subst_var ts x t = subst_var' ts x t 0

	let subst_var' ts x t i = if i = length ts then ts else
	    match ts[i] of
		b => subst_var' ts x t (i+1)
		(x', b') => if x != x' then subst_var' ts x t (i+1) else
		    match t of
			b'' => subst_var' ts(i := b'' + b') x t (i+1)
			(x'', b'') => subst_var' ts(i := (x'', b'' + b')) x t (i+1)
	    
		
*)

  let meet t1 t2 =
    (*
    let sup_env = Environment.lce t1.env t2.env in
    let t1, t2 = change_d t1 sup_env true false, change_d t2 sup_env true false
    in if is_bot t1 || is_bot t2 then bot() else
      let m1, m2 = Option.get t1.d, Option.get t2.d in
      match m1, m2 with
      | x, y when is_top_env t1-> {d = Some (dim_add (Environment.dimchange t2.env sup_env) y); env = sup_env}
      | x, y when is_top_env t2 -> {d = Some (dim_add (Environment.dimchange t1.env sup_env) x); env = sup_env}
      | x, y ->
        let rref_matr = Matrix.rref_matrix_with (Matrix.copy x) (Matrix.copy y) in
        if Option.is_none rref_matr then bot () else
          {d = rref_matr; env = sup_env}
     *)


  let meet t1 t2 =
    let res = meet t1 t2 in
    if M.tracing then M.tracel "meet" "meet a: %s b: %s -> %s \n" (show t1) (show t2) (show res) ;
    res

  let meet t1 t2 = timing_wrap "meet" (meet t1) t2

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let leq t1 t2 =
    let env_comp = Environment.compare t1.env t2.env in (* Apron's Environment.compare has defined return values. *)
    let implies ts t i : bool =
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
    if env_comp = -2 || env_comp > 0 then false else
    if is_bot t1 || is_top_env t2 then true else
    if is_bot t2 || is_top_env t1 then false else (
      let m1, m2 = Option.get t1.d, Option.get t2.d in
      let m1' = if env_comp = 0 then m1 else dim_add (Environment.dimchange t1.env t2.env) m1 in
      let result : bool ref = ref true in
      for i = 0 to Array.length m2 - 1 do
        let t = m2.(i) in
        if not (implies m1' t i) then result := false;
      done;
      !result) 

  let leq a b = timing_wrap "leq" (leq a) b

  let leq t1 t2 =
    let res = leq t1 t2 in
    if M.tracing then M.tracel "leq" "leq a: %s b: %s -> %b \n" (show t1) (show t2) res ;
    res

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

(*
	Calculate the least upper bound as described in the paper.

	let const_offset ts x = match ts[x] of
		b => b
		(_, b) => b

	let difference t1 t2 x = (const_offset t1 x) - (const_offset t2 x)

	let annotated_exprs n = [(0, 0), (1, 0), ..., (n, 0)]

	let sort_val i j = ...
	let stable_sort at t1 t2 = ...
	let sort_aexprs at = ...

	let reduce_aexprs at = match at of
	    [] => []
	    ((i, e)#ts) => e # reduce_aexprs ts

	let size_of_eq_class_at t1 t2 i = size_of_eq_class_at' t1 t2 i 0
	let size_of_eq_class_at' t1 t2 i offset = if (sort_val t1[i] t2[i]) = (sort_val t1[i + offset] t2[i + offset]) then
	    1 + size_of_eq_class_at t1 t2 at (i+1) else 0

	let join t1 t2 = 
	    let at = annotated_expr (size t1) in (* assumes num vars in t1 and t2 are equal. can we assume that? *)
	    let (at', t1', t2') = stable_sort at t1 t2 in
	    let at'' = process_eq_classes at' t1' t2' in
	    reduce_aexprs (sort_aexprs at'')

	let process_eq_classes at t1 t2 = process_eq_classes' at t1 t2 0 

	let process_eq_classes' at t1 t2 i = if i > size t1 then at else
	    let n = size_of_eq_class_at t1 t2 i in
	    if n = 1 then match at[i] of
		(ix, _) => match (t1[ix], t2[ix]) of
		    (b_1, b_2) => if b_1 = b_2 then process_eq_classes at(i := (ix, b)) t1 t2 (i+1)
			else process_eq_classes at(i := (ix, (ix, 0))) t1 t2 (i+1)
	    else
		let (least_i, least_b)  = least_index_var_in_eq_class at t1 i n in
		if all_are_const_in t1 t2 i n then assign_vars_in_const_eq_class at t1 t2 i n least_i least_b 
		else assign_vars_in_non_const_eq_class at t1 t2 i n least_i least_b

	let all_are_const_in t1 t2 from size = all_are_const_in' t1 t2 from size 0

	let all_are_const_in' t1 t2 from size offset = if offset + 1 = size then true else
	    if is_const t1 (from + offset) && is_const t2 (from + offset)
		then all_are_const_in' t1 t2 from size (offset + 1)
	    else false

	let is_const ts i = match ts[i] of
		b => true
		(_, _) => false

	let least_index_var_in_eq_class at ts from size = match at[from] of
	    (i, b) => least_index_var_in_eq_class' at ts from size 0 (i, b)
	    (i, (_, b)) => least_index_var_in_eq_class' at ts from size 0 (i, b) 

	(* TODO: how exactlyis the constant coefficient on the right hand side defined? *)
	let least_index_var_in_eq_class' at ts from size offset res =  
	    if offset + 1 = size then res else
 	    let (ri, rb) = res in
	    match (at[from + offset], ts[from + offset]) of
		((i, _), b) => if i < ri then least_index_var_in_eq_class' at from size (offset + 1) (i, b)
			  else least_index_var_in_eq_class' at from size (offset + 1) res
		((i, _), (_, b)) => if i < ri then least_index_var_in_eq_class' at from size (offset + 1) (i, b)	
	    
	let assign_vars_in_const_eq_class at t1 t2 from size least_i least_b = 
	    assign_vars_in_const_eq_class' at t1 t2 from size least_i least_b 0

	let assign_vars_in_const_eq_class' at t1 t2 from size least_i least_b offset = 
	    if (offset + 1) = size then at else	
		match at[from + offset] of
		    (i, _) => let b = const_offset t1 (from + offset) in
			if difference t1 t2 (from + offset) = 0 then
		    	    assign_vars_in_const_eq_class' at(from + offset := (i, b)) t1 t2 from size least_i least_b (offset + 1)
			else assign_vars_in_const_eq_class' at(from + offset := (i, (least_i, b - least_b))) from size least_i least_b (offset + 1)

	let assign_var_in_non_const_eq_class at t1 t2 from size least_i least_b =
		assign_var_in_non_const_eq_class' at t1 t2 from size least_i least_b 0

	let assign_var_in_non_const_eq_class' at t1 t2 from size least_i least_b offset =
	    if (offset + 1) = size then at else
		match at[from + offset] of
		    (i, _) => let b = const_offset t1 (from + offset) in
			assign_var_in_non_const_eq_class' at(from + offset := (i,(least_i, b - least_b)))
	
*)
  let join a b =
    (*
    let rec lin_disjunc r s a b =
      if s >= Matrix.num_cols a then a else
        let case_two a r col_b =
          let a_r = Matrix.get_row a r in
          Matrix.map2i_with (fun i x y -> if i < r then
                                Vector.map2_with (fun u j -> u +: y *: j) x a_r; x) a col_b;
          Matrix.remove_row a r
        in
        let case_three a b col_a col_b max =
          let col_a, col_b = Vector.copy col_a, Vector.copy col_b in
          let col_a, col_b = Vector.keep_vals col_a max, Vector.keep_vals col_b max in
          if Vector.equal col_a col_b then (a, b, max) else
            let a_rev, b_rev = (Vector.rev_with col_a; col_a), (Vector.rev_with col_b; col_b) in
            let i = Vector.find2i (fun x y -> x <>: y) a_rev b_rev in
            let (x, y) = Vector.nth a_rev i, Vector.nth b_rev i in
            let r, diff = Vector.length a_rev - (i + 1), x -: y  in
            let a_r, b_r = Matrix.get_row a r, Matrix.get_row b r in
            let sub_col =
              Vector.map2_with (fun x y -> x -: y) a_rev b_rev;
              Vector.rev_with a_rev;
              a_rev
            in
            let multiply_by_t m t =
              Matrix.map2i_with (fun i' x c -> if i' <= max then (let beta = c /: diff in
                                                                  Vector.map2_with (fun u j -> u -: (beta *: j)) x t); x) m sub_col;
              m
            in
            Matrix.remove_row (multiply_by_t a a_r) r, Matrix.remove_row (multiply_by_t b b_r) r, (max - 1)
        in
        let col_a, col_b = Matrix.get_col a s, Matrix.get_col b s in
        let nth_zero v i =  match Vector.nth v i with
          | exception Invalid_argument _ -> Mpqf.zero
          | x -> x
        in
        let a_rs, b_rs = nth_zero col_a r, nth_zero col_b r in
        if not (Z.equal (Mpqf.get_den a_rs) Z.one) || not (Z.equal (Mpqf.get_den b_rs) Z.one) then failwith "Matrix not in rref form" else
          begin match Int.of_float @@ Mpqf.to_float @@ a_rs, Int.of_float @@ Mpqf.to_float @@ b_rs with (* TODO: is it safe to go through floats? *)
            | 1, 1 -> lin_disjunc (r + 1) (s + 1) a b
            | 1, 0 -> lin_disjunc r (s + 1) (case_two a r col_b) b
            | 0, 1 -> lin_disjunc r (s + 1) a (case_two b r col_a)
            | 0, 0 ->  let new_a, new_b, new_r = case_three a b col_a col_b r in
              lin_disjunc new_r (s + 1) new_a new_b
            | _      -> failwith "Matrix not in rref form" end
    in
    if is_bot a then b else if is_bot b then a else
      match Option.get a.d, Option.get b.d with
      | x, y when is_top_env a || is_top_env b -> {d = Some (Matrix.empty ()); env = Environment.lce a.env b.env}
      | x, y when (Environment.compare a.env b.env <> 0) ->
        let sup_env = Environment.lce a.env b.env in
        let mod_x = dim_add (Environment.dimchange a.env sup_env) x in
        let mod_y = dim_add (Environment.dimchange b.env sup_env) y in
        {d = Some (lin_disjunc 0 0 (Matrix.copy mod_x) (Matrix.copy mod_y)); env = sup_env}
      | x, y when Matrix.equal x y -> {d = Some x; env = a.env}
      | x, y  -> {d = Some(lin_disjunc 0 0 (Matrix.copy x) (Matrix.copy y)); env = a.env}
    *)

  let join a b = timing_wrap "join" (join a) b

  let join a b =
    let res = join a b in
    if M.tracing then M.tracel "join" "join a: %s b: %s -> %s \n" (show a) (show b) (show res) ;
    res
  let widen a b =
    let a_env = a.env in
    let b_env = b.env in
    if Environment.equal a_env b_env  then
      join a b
    else b

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let narrow a b = a

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let pretty_diff () (x, y) =
    dprintf "%s: %a not leq %a" (name ()) pretty x pretty y

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let remove_rels_with_var x var env imp =
  (*
    let j0 = Environment.dim_of_var env var in
    if imp then (Matrix.reduce_col_with x j0; x) else Matrix.reduce_col x j0
  *)

  let remove_rels_with_var x var env imp = timing_wrap "remove_rels_with_var" (remove_rels_with_var x var env) imp

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let forget_vars t vars =
  (*
    if is_bot t || is_top_env t then t
    else
      let m = Option.get t.d in
      if List.is_empty vars then t else
        let rec rem_vars m vars' =
          begin match vars' with
            |            [] -> m
            | x :: xs -> rem_vars (remove_rels_with_var m x t.env true) xs end
        in {d = Some (Matrix.remove_zero_rows @@ rem_vars (Matrix.copy m) vars); env = t.env}
  *) 

  let forget_vars t vars =
    let res = forget_vars t vars in
    if M.tracing then M.tracel "ops" "forget_vars %s -> %s\n" (show t) (show res);
    res

  let forget_vars t vars = timing_wrap "forget_vars" (forget_vars t) vars

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let assign_texpr (t: VarManagement(Vc)(Mx).t) var texp =
  (*
    let assign_invertible_rels x var b env =
      let j0 = Environment.dim_of_var env var in
      let a_j0 = Matrix.get_col x j0  in (*Corresponds to Axj0*)
      let b0 = Vector.nth b j0 in
      Vector.apply_with_c_with (/:) b0 a_j0; (*Corresponds to Axj0/Bj0*)
      let recalc_entries m rd_a = Matrix.map2_with (fun x y -> Vector.map2i_with (fun j z d ->
          if j = j0 then y
          else if Vector.compare_length_with b (j + 1) > 0 then z -: y *: d
          else z +: y *: d) x b; x) m rd_a
      in
      recalc_entries x a_j0;
      if Matrix.normalize_with x then {d = Some x; env = env} else bot ()
    in
    let assign_invertible_rels x var b env = timing_wrap "assign_invertible" (assign_invertible_rels x var b) env in
    let assign_uninvertible_rel x var b env =
      let b_length = Vector.length b in
      Vector.mapi_with (fun i z -> if i < b_length - 1 then Mpqf.mone *: z else z) b;
      Vector.set_val_with b (Environment.dim_of_var env var) Mpqf.one;
      let opt_m = Matrix.rref_vec_with x b in
      if Option.is_none opt_m then bot () else
        {d = opt_m; env = env}
    in
    (* let assign_uninvertible_rel x var b env = timing_wrap "assign_uninvertible" (assign_uninvertible_rel x var b) env in *)
    let is_invertible v = Vector.nth v @@ Environment.dim_of_var t.env var <>: Mpqf.zero
    in let affineEq_vec = get_coeff_vec t texp
    in if is_bot t then t else let m = Option.get t.d in
      match affineEq_vec with
      | Some v when is_top_env t -> if is_invertible v then t else assign_uninvertible_rel m var v t.env
      | Some v -> if is_invertible v then let t' = assign_invertible_rels (Matrix.copy m) var v t.env in {d = t'.d; env = t'.env}
        else let new_m = Matrix.remove_zero_rows @@ remove_rels_with_var m var t.env false
          in assign_uninvertible_rel new_m var v t.env
      | None -> {d = Some (Matrix.remove_zero_rows @@ remove_rels_with_var m var t.env false); env = t.env}
  *) 

  let assign_texpr t var texp = timing_wrap "assign_texpr" (assign_texpr t var) texp

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let assign_exp (t: VarManagement(Vc)(Mx).t) var exp (no_ov: bool Lazy.t) =
    let t = if not @@ Environment.mem_var t.env var then add_vars t [var] else t in
    match Convert.texpr1_expr_of_cil_exp t t.env exp (Lazy.force no_ov) with
    | exp -> assign_texpr t var exp
    | exception Convert.Unsupported_CilExp _ ->
      if is_bot t then t else forget_vars t [var]

  let assign_exp t var exp no_ov =
    let res = assign_exp t var exp no_ov in
    if M.tracing then M.tracel "ops" "assign_exp t:\n %s \n var: %s \n exp: %a\n no_ov: %b -> \n %s\n"
        (show t) (Var.to_string var) d_exp exp (Lazy.force no_ov) (show res) ;
    res

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let assign_var (t: VarManagement(Vc)(Mx).t) v v' =
    let t = add_vars t [v; v'] in
    let texpr1 = Texpr1.of_expr (t.env) (Var v') in
    assign_texpr t v (Apron.Texpr1.to_expr texpr1)

  let assign_var t v v' =
    let res = assign_var t v v' in
    if M.tracing then M.tracel "ops" "assign_var t:\n %s \n v: %s \n v': %s\n -> %s\n" (show t) (Var.to_string v) (Var.to_string v') (show res) ;
    res

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let assign_var_parallel t vv's =
  (*
    let assigned_vars = List.map (function (v, _) -> v) vv's in
    let t = add_vars t assigned_vars in
    let primed_vars = List.init (List.length assigned_vars) (fun i -> Var.of_string (Int.to_string i  ^"'")) in (* TODO: we use primed vars in analysis, conflict? *)
    let t_primed = add_vars t primed_vars in
    let multi_t = List.fold_left2 (fun t' v_prime (_,v') -> assign_var t' v_prime v') t_primed primed_vars vv's in
    match multi_t.d with
    | Some m when not @@ is_top_env multi_t -> let replace_col m x y = let dim_x, dim_y = Environment.dim_of_var multi_t.env x, Environment.dim_of_var multi_t.env y in
                                                 let col_x = Matrix.get_col m dim_x in
                                                 Matrix.set_col_with m col_x dim_y in
      let m_cp = Matrix.copy m in
      let switched_m = List.fold_left2 (fun m' x y -> replace_col m' x y) m_cp primed_vars assigned_vars in
      let res = drop_vars {d = Some switched_m; env = multi_t.env} primed_vars true in
      let x = Option.get res.d in
      if Matrix.normalize_with x then {d = Some x; env = res.env} else bot ()
    | _ -> t
  *)

  let assign_var_parallel t vv's =
    let res = assign_var_parallel t vv's in
    if M.tracing then M.tracel "ops" "assign_var parallel: %s -> %s \n" (show t) (show res);
    res

  let assign_var_parallel t vv's = timing_wrap "var_parallel" (assign_var_parallel t) vv's

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let assign_var_parallel_with t vv's =
    let t' = assign_var_parallel t vv's in
    t.d <- t'.d;
    t.env <- t'.env

  let assign_var_parallel_with t vv's =
    if M.tracing then M.tracel "var_parallel" "assign_var parallel'\n";
    assign_var_parallel_with t vv's

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let assign_var_parallel' t vs1 vs2 =
    let vv's = List.combine vs1 vs2 in
    assign_var_parallel t vv's

  let assign_var_parallel' t vv's =
    let res = assign_var_parallel' t vv's in
    if M.tracing then M.tracel "ops" "assign_var parallel'\n";
    res

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let substitute_exp t var exp no_ov =
    let t = if not @@ Environment.mem_var t.env var then add_vars t [var] else t in
    let res = assign_exp t var exp no_ov in
    forget_vars res [var]

  let substitute_exp t var exp ov =
    let res = substitute_exp t var exp ov
    in if M.tracing then M.tracel "ops" "Substitute_expr t: \n %s \n var: %s \n exp: %a \n -> \n %s\n" (show t) (Var.to_string var) d_exp exp (show res);
    res

  let substitute_exp t var exp ov = timing_wrap "substitution" (substitute_exp t var exp) ov

(* ---------------------------------------------------------------------------------------------------- *)


  (** Assert a constraint expression.

      Additionally, we now also refine after positive guards when overflows might occur and there is only one variable inside the expression and the expression is an equality constraint check (==).
      We check after the refinement if the new value of the variable is outside its integer bounds and if that is the case, either revert to the old state or set it to bottom. *)

  exception NotRefinable


(* ---------------------------------------------------------------------------------------------------- *)

  let meet_tcons_one_var_eq res expr =
    let overflow_res res = if IntDomain.should_ignore_overflow (Cilfacade.get_ikind_exp expr) then res else raise NotRefinable in
    match Convert.find_one_var expr with
    | None -> overflow_res res
    | Some v ->
      let ik = Cilfacade.get_ikind v.vtype in
      match Bounds.bound_texpr res (Convert.texpr1_of_cil_exp res res.env (Lval (Cil.var v)) true) with
      | Some _, Some _ when not (Cil.isSigned ik) -> raise NotRefinable (* TODO: unsigned w/o bounds handled differently? *)
      | Some min, Some max ->
        assert (Z.equal min max); (* other bounds impossible in affeq *)
        let (min_ik, max_ik) = IntDomain.Size.range ik in
        if Z.compare min min_ik < 0 || Z.compare max max_ik > 0 then
          if IntDomain.should_ignore_overflow ik then bot () else raise NotRefinable
        else res
      | exception Convert.Unsupported_CilExp _
      | _, _ -> overflow_res res

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let meet_tcons t tcons expr =
  (*
    let check_const cmp c = if cmp c Mpqf.zero then bot_env else t
    in
    let meet_vec e =
      (*Flip the sign of the const. val in coeff vec*)
      Vector.mapi_with (fun i x -> if Vector.compare_length_with e (i + 1) = 0 then Mpqf.mone *: x else x) e;
      let res = if is_bot t then bot () else
          let opt_m = Matrix.rref_vec_with (Matrix.copy @@ Option.get t.d) e
          in if Option.is_none opt_m then bot () else {d = opt_m; env = t.env} in
      meet_tcons_one_var_eq res expr
    in
    match get_coeff_vec t (Texpr1.to_expr @@ Tcons1.get_texpr1 tcons) with
    | Some v ->
      begin match get_c v, Tcons1.get_typ tcons with
        | Some c, DISEQ -> check_const (=:) c
        | Some c, SUP -> check_const (<=:) c
        | Some c, EQ -> check_const (<>:) c
        | Some c, SUPEQ -> check_const (<:) c
        | None, DISEQ
        | None, SUP ->
          begin match meet_vec v with
            | exception NotRefinable -> t
            | res -> if equal res t then bot_env else t
          end
        | None, EQ ->
          begin match meet_vec v with
            | exception NotRefinable -> t
            | res -> if is_bot res then bot_env else res
          end
        | _, _ -> t
      end
    | None -> t
  *)

  let meet_tcons t tcons expr = timing_wrap "meet_tcons" (meet_tcons t tcons) expr

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let unify a b =
    meet a b

  let unify a b =
    let res = unify a b  in
    if M.tracing then M.tracel "ops" "unify: %s %s -> %s\n" (show a) (show b) (show res);
    res

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let assert_cons d e negate no_ov =
    let no_ov = Lazy.force no_ov in
    if M.tracing then M.tracel "assert_cons" "assert_cons with expr: %a %b" d_exp e no_ov;
    match Convert.tcons1_of_cil_exp d d.env e negate no_ov with
    | tcons1 -> meet_tcons d tcons1 e
    | exception Convert.Unsupported_CilExp _ -> d

  let assert_cons d e negate no_ov = timing_wrap "assert_cons" (assert_cons d e negate) no_ov

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let relift t = t

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let invariant t =
  (*
    match t.d with
    | None -> []
    | Some m ->
      let earray = Lincons1.array_make t.env (Matrix.num_rows m) in
      for i = 0 to Lincons1.array_length earray do
        let row = Matrix.get_row m i in
        let coeff_vars = List.map (fun x ->  Coeff.s_of_mpqf @@ Vector.nth row (Environment.dim_of_var t.env x), x) (vars t) in
        let cst = Coeff.s_of_mpqf @@ Vector.nth row (Vector.length row - 1) in
        Lincons1.set_list (Lincons1.array_get earray i) coeff_vars (Some cst)
      done;
      let {lincons0_array; array_env}: Lincons1.earray = earray in
      Array.enum lincons0_array
      |> Enum.map (fun (lincons0: Lincons0.t) ->
          Lincons1.{lincons0; env = array_env}
        )
      |> List.of_enum
  *) 

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let cil_exp_of_lincons1 = Convert.cil_exp_of_lincons1

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let env (t: Bounds.t) = t.env

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  type marshal = Bounds.t

  let marshal t = t

(* ---------------------------------------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------------------------------------- *)

  let unmarshal t = t

(* ---------------------------------------------------------------------------------------------------- *)



end

(* =================================================================================================== *)
(* =================================================================================================== *)










(* =================================================================================================== *)
(* =================================================================================================== *)

module D2(Vc: AbstractVector) (Mx: AbstractMatrix): RelationDomain.S3 with type var = Var.t =
struct
  module D =  D (Vc) (Mx)
  include SharedFunctions.AssertionModule (V) (D)
  include D
end

(* =================================================================================================== *)
(* =================================================================================================== *)

