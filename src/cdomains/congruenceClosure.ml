(** OCaml implementation of a quantitative congruence closure. *)

open Batteries
open GoblintCil
module Var = CilType.Varinfo
module M = Messages

exception Unsat

type ('v, 't) term = Addr of 'v | Aux of 'v * 't | Deref of ('v, 't) term * Z.t * 't [@@deriving eq, ord, hash]
type ('v, 't) prop = Equal of ('v, 't) term * ('v, 't) term * Z.t | Nequal of ('v, 't) term * ('v, 't) term * Z.t
                   | BlNequal of ('v, 't) term * ('v, 't) term
[@@deriving eq, ord, hash]

(** The terms consist of address constants and dereferencing function with sum of an integer.
    The dereferencing function is parametrized by the size of the element in the memory.
    We store the CIL expression of the term in the data type, such that it it easier to find the types of the dereferenced elements.
    Also so that we can easily convert back from term to Cil expression.
*)
module T = struct
  type exp = Cil.exp

  let bitsSizeOfPtr () = Z.of_int @@ bitsSizeOf (TPtr (TVoid [],[]))

  (* equality of terms should not depend on the expression *)
  let compare_exp _ _ = 0
  let equal_exp _ _ = true
  let hash_exp _ = 1


  (* we store the varinfo and the Cil expression corresponding to the term in the data type *)
  type t = (Var.t, exp) term [@@deriving eq, ord, hash]
  type v_prop = (Var.t, exp) prop [@@deriving hash]

  let compare t1 t2 =
    match t1,t2 with
    | Addr v1, Addr v2
    | Aux (v1,_), Aux (v2,_) -> Var.compare v1 v2
    | Deref (t1,z1,_), Deref (t2,z2,_) -> let c = compare t1 t2 in
      if c = 0 then Z.compare z1 z2 else c
    | Addr _, _
    | _, Deref _ -> -1
    | _ -> 1

  let normal_form_prop = function
    | Equal (t1,t2,z) | Nequal (t1,t2,z) ->
      if compare t1 t2 < 0 || (compare t1 t2 = 0 && Z.geq z Z.zero) then (t1,t2,z) else
        (t2,t1,Z.(-z))
    | BlNequal (t1,t2) ->
      if compare t1 t2 < 0 then (t1,t2,Z.zero) else
        (t2,t1,Z.zero)

  (** Two propositions are equal if they are syntactically equal
      or if one is t_1 = z + t_2 and the other t_2 = - z + t_1. *)
  let equal_v_prop p1 p2 =
    match p1, p2 with
    | Equal (a,b,c), Equal (a',b',c') -> Tuple3.eq equal equal Z.equal (normal_form_prop p1) (normal_form_prop p2)
    | Nequal (a,b,c), Nequal (a',b',c') -> Tuple3.eq equal equal Z.equal (normal_form_prop p1) (normal_form_prop p2)
    | BlNequal (a,b), BlNequal (a',b') -> Tuple3.eq equal equal Z.equal (normal_form_prop p1) (normal_form_prop p2)
    | _ -> false

  let compare_v_prop p1 p2 =
    match p1, p2 with
    | Equal (a,b,c), Equal (a',b',c') -> Tuple3.comp compare compare Z.compare (normal_form_prop p1) (normal_form_prop p2)
    | Nequal (a,b,c), Nequal (a',b',c') -> Tuple3.comp compare compare Z.compare (normal_form_prop p1) (normal_form_prop p2)
    | BlNequal (a,b), BlNequal (a',b') -> Tuple3.comp compare compare Z.compare (normal_form_prop p1) (normal_form_prop p2)
    | Equal _, _ -> -1
    | _, Equal _ -> 1
    | _, BlNequal _ -> -1
    | BlNequal _ , _ -> 1

  let props_equal = List.equal equal_v_prop

  let is_addr = function
    | Addr _ -> true
    | _ -> false

  exception UnsupportedCilExpression of string

  let rec get_size_in_bits typ = match typ with
    | TArray (typ, _, _) -> (* we treat arrays like pointers *)
      get_size_in_bits (TPtr (typ,[]))
    (* | TComp (compinfo, _) ->
       if List.is_empty compinfo.cfields then Z.zero else
        get_size_in_bits (List.first compinfo.cfields).ftype *)
    | _ -> match Z.of_int (bitsSizeOf typ) with
      | exception GoblintCil__Cil.SizeOfError (msg,_) -> raise (UnsupportedCilExpression msg)
      | s -> s

  let show_type exp =
    try
      let typ = typeOf exp in
      "[" ^ (match typ with
          | TPtr _ -> "Ptr"
          | TInt _ -> "Int"
          | TArray _ -> "Arr"
          | TVoid _ -> "Voi"
          | TFloat (_, _)-> "Flo"
          | TComp (_, _) -> "TCo"
          | TFun (_, _, _, _)|TNamed (_, _)|TEnum (_, _)|TBuiltin_va_list _ -> "?"
        )^ Z.to_string (get_size_in_bits typ) ^ "]"
    with
    | UnsupportedCilExpression _ -> "[?]"

  let rec show : t -> string = function
    | Addr v -> "&" ^ Var.show v
    | Aux (v,exp) ->  "~" ^ Var.show v ^ show_type exp
    | Deref (Addr v, z, exp) when Z.equal z Z.zero -> Var.show v ^ show_type exp
    | Deref (t, z, exp) when Z.equal z Z.zero -> "*" ^ show t^ show_type exp
    | Deref (t, z, exp) -> "*(" ^ Z.to_string z ^ "+" ^ show t ^ ")"^ show_type exp

  (** Returns true if the first parameter is a subterm of the second one. *)
  let rec is_subterm st term = equal st term || match term with
    | Deref (t, _, _) -> is_subterm st t
    | _ -> false

  let rec get_var = function
    | Addr v | Aux (v,_) -> v
    | Deref (t, _, _) -> get_var t

  (** Returns true if the second parameter contains one of the variables defined in the list "variables". *)
  let contains_variable variables term = List.mem_cmp Var.compare (get_var term) variables

  let eval_int (ask:Queries.ask) exp =
    match Cilfacade.get_ikind_exp exp with
    | exception Invalid_argument _ -> raise (UnsupportedCilExpression "non-constant value")
    | ikind ->
      begin match ask.f (Queries.EvalInt exp) with
        | `Lifted i ->
          begin match IntDomain.IntDomTuple.to_int @@ IntDomain.IntDomTuple.cast_to ikind i
            with
            | Some i -> i
            | None -> raise (UnsupportedCilExpression "non-constant value")
          end
        | _ -> raise (UnsupportedCilExpression "non-constant value")
      end

  let eval_int_opt (ask:Queries.ask) exp =
    match eval_int ask exp with
    | i -> Some i
    | exception (UnsupportedCilExpression _) -> None

  (*returns Some type for a pointer to a type
    and None if the result is not a pointer*)
  let rec type_of_element typ =
    match typ with
    | TArray (typ, _, _) -> type_of_element typ
    | TPtr (typ, _) -> Some typ
    | _ -> None

  (** Returns the size of the type. If typ is a pointer, it returns the
      size of the elements it points to. If typ is an array, it returns the size of the
      elements of the array (even if it is a multidimensional array. Therefore get_element_size_in_bits int\[]\[]\[] = sizeof(int)). *)
  let get_element_size_in_bits typ =
    match type_of_element typ with
    | Some typ -> get_size_in_bits typ
    | None -> Z.one

  let rec is_array_type = function
    | TNamed (typinfo, _) -> is_array_type typinfo.ttype
    | TArray _ -> true
    | _ -> false

  let rec is_struct_type = function
    | TNamed (typinfo, _) -> is_struct_type typinfo.ttype
    | TComp _ -> true
    | _ -> false

  let rec is_struct_ptr_type = function
    | TNamed (typinfo, _) -> is_struct_ptr_type typinfo.ttype
    | TPtr(typ,_) -> is_struct_type typ
    | _ -> false

  let rec is_ptr_type = function
    | TNamed (typinfo, _) -> is_ptr_type typinfo.ttype
    | TPtr _ -> true
    | _ -> false

  let aux_term_of_varinfo vinfo =
    Aux (vinfo, Lval (Var vinfo, NoOffset))

  let term_of_varinfo vinfo =
    if is_struct_type vinfo.vtype || vinfo.vaddrof then
      Deref (Addr vinfo, Z.zero, Lval (Var vinfo, NoOffset))
    else
      aux_term_of_varinfo vinfo

  let cil_offs_to_idx (ask: Queries.ask) offs typ =
    (* TODO: Some duplication with convert_offset in base.ml and cil_offs_to_idx in memOutOfBounds.ml,
       unclear how to immediately get more reuse *)
    let rec convert_offset (ofs: offset) =
      match ofs with
      | NoOffset -> `NoOffset
      | Field (fld, ofs) -> `Field (fld, convert_offset ofs)
      | Index (exp, ofs) when CilType.Exp.equal exp (Lazy.force Offset.Index.Exp.any) -> (* special offset added by convertToQueryLval *)
        `Index (ValueDomain.ID.top_of (Cilfacade.get_ikind_exp exp), convert_offset ofs)
      | Index (exp, ofs) ->
        let i = match ask.f (Queries.EvalInt exp) with
          | `Lifted x -> IntDomain.IntDomTuple.cast_to  (Cilfacade.ptrdiff_ikind ()) @@ x
          | _ -> ValueDomain.ID.top_of @@ Cilfacade.ptrdiff_ikind ()
        in
        `Index (i, convert_offset ofs)
    in
    let to_constant exp = try let z = eval_int ask exp in
        Const (CInt (z, Cilfacade.get_ikind_exp exp, Some (Z.to_string z)))
      with Invalid_argument _ | UnsupportedCilExpression _ -> exp
    in
    let rec convert_type typ = (* compute length of arrays when it is known*)
      match typ with
      | TArray (typ, exp, attr) -> TArray (convert_type typ, Option.map to_constant exp, attr)
      | TPtr (typ, attr) -> TPtr (convert_type typ, attr)
      | TFun (typ, form, var_arg, attr) -> TFun (convert_type typ, form, var_arg, attr)
      | TNamed (typeinfo, attr) -> TNamed ({typeinfo with ttype=convert_type typeinfo.ttype}, attr)
      | TVoid _| TInt (_, _)| TFloat (_, _)| TComp (_, _)| TEnum (_, _)| TBuiltin_va_list _ -> typ
    in
    PreValueDomain.Offs.to_index ?typ:(Some (convert_type typ)) (convert_offset offs)

  let z_of_offset ask offs typ =
    match IntDomain.IntDomTuple.to_int @@ cil_offs_to_idx ask offs typ with
    | Some i -> i
    | None
    | exception (SizeOfError _) -> raise (UnsupportedCilExpression "unknown offset")

  let can_be_dereferenced = function
    | TPtr _| TArray _| TComp _ -> true
    | _ -> false

  let type_of_term =
    function
    | Addr v -> TPtr (v.vtype, [])
    | Aux (_, exp) | Deref (_, _, exp) -> typeOf exp

  let to_cil =
    function
    | (Addr v) -> AddrOf (Var v, NoOffset)
    | Aux (_, exp) | (Deref (_, _, exp)) -> exp

  let default_int_type = ILong
  (** Returns a Cil expression which is the constant z divided by the size of the elements of t.*)
  let to_cil_constant z t =
    let z = if Z.equal z Z.zero then Z.zero else
        let typ_size = match t with
          | Some t -> get_element_size_in_bits t
          | None -> Z.one
        in
        if Z.equal typ_size Z.zero then Z.zero else
          Z.(z /typ_size) in Const (CInt (z, default_int_type, Some (Z.to_string z)))

  let to_cil_sum off cil_t =
    if Z.(equal zero off) then cil_t else
      let typ = typeOf cil_t in
      BinOp (PlusPI, cil_t, to_cil_constant off (Some typ), typ)

  let get_field_offset finfo = match IntDomain.IntDomTuple.to_int (PreValueDomain.Offs.to_index (`Field (finfo, `NoOffset))) with
    | Some i -> i
    | None -> raise (UnsupportedCilExpression "unknown offset")

  let is_field = function
    | Field _ -> true
    | _ -> false

  let rec add_index_to_exp exp index =
    try if is_struct_type (typeOf exp) = (is_field index) then
        begin match exp with
          | Lval (Var v, NoOffset) -> Lval (Var v, index)
          | Lval (Mem v, NoOffset) -> Lval (Mem v, index)
          | BinOp (PlusPI, exp1, Const (CInt (z, _ , _ )), _)when Z.equal z Z.zero ->
            add_index_to_exp exp1 index
          | _ -> raise (UnsupportedCilExpression "not supported yet")
        end
      else if is_struct_ptr_type (typeOf exp) && (is_field index) then
        Lval(Mem (exp), index)
      else raise (UnsupportedCilExpression "Field on a non-compound")
    with | Cilfacade.TypeOfError _ -> raise (UnsupportedCilExpression "typeOf error")

  let is_float = function
    | TFloat _ -> true
    | _ -> false

  let check_valid_pointer term =
    match typeOf term with (* we want to make sure that the expression is valid *)
    | exception GoblintCil__Errormsg.Error -> false
    | typ -> (* we only track equalties between pointers (variable of size 64)*)
      if get_size_in_bits typ <> bitsSizeOfPtr () || is_float typ then false
      else true

  let filter_valid_pointers =
    List.filter (function | Equal(t1,t2,_)| Nequal(t1,t2,_) |BlNequal(t1,t2)-> check_valid_pointer (to_cil t1) && check_valid_pointer (to_cil t2))

  let dereference_exp exp offset =
    if M.tracing then M.trace "wrpointer-deref" "exp: %a, offset: %s" d_exp exp (Z.to_string offset);
    let res =
      let find_field cinfo =
        try
          Field (List.find (fun field -> Z.equal (get_field_offset field) offset) cinfo.cfields, NoOffset)
        with | Not_found -> raise (UnsupportedCilExpression "invalid field offset")
      in
      let res = match exp with
        | AddrOf lval -> Lval lval
        | _ ->
          match typeOf exp with
          | TPtr (TComp (cinfo, _), _) -> add_index_to_exp exp (find_field cinfo)
          | TPtr (typ, _) -> Lval (Mem (to_cil_sum offset exp), NoOffset)
          | TArray (typ, _, _) when not (can_be_dereferenced typ) ->
            let index = Index (to_cil_constant offset (Some typ), NoOffset) in
            begin match exp with
              | Lval (Var v, NoOffset) ->  Lval (Var v, index)
              | Lval (Mem v, NoOffset) -> Lval (Mem v, index)
              | _ -> raise (UnsupportedCilExpression "not supported yet")
            end
          | TComp (cinfo, _) -> add_index_to_exp exp (find_field cinfo)
          | _ ->  Lval (Mem (CastE (TPtr(TVoid[],[]), to_cil_sum offset exp)), NoOffset)
      in if check_valid_pointer res then res else raise (UnsupportedCilExpression "not a pointer variable")
    in if M.tracing then M.trace "wrpointer-deref" "deref result: %a" d_exp res;res

  let get_size = get_size_in_bits % type_of_term

  let of_offset ask t off typ exp =
    if off = NoOffset then t else
      let z = z_of_offset ask off typ in
      Deref (t, z, exp)

  (** Converts a cil expression to Some term, Some offset;
      or None, Some offset is the expression equals an integer,
      or None, None if the expression can't be described by our analysis.*)
  let rec of_cil (ask:Queries.ask) e = match e with
    | Const (CInt (i, _, _)) -> None, i
    | Const _ -> raise (UnsupportedCilExpression "non-integer constant")
    | AlignOf _
    | AlignOfE _ -> raise (UnsupportedCilExpression "unsupported AlignOf")
    | Lval lval -> Some (of_lval ask lval), Z.zero
    | StartOf lval  -> Some (of_lval ask lval), Z.zero
    | AddrOf (Var var, NoOffset) -> Some (Addr var), Z.zero
    | AddrOf (Mem exp, NoOffset) -> of_cil ask exp
    | UnOp (op,exp,typ) -> begin match op with
        | Neg -> let off = eval_int ask exp in None, Z.(-off)
        | _ -> raise (UnsupportedCilExpression "unsupported UnOp")
      end
    | BinOp (binop, exp1, exp2, typ)->
      let typ1_size = get_element_size_in_bits (Cilfacade.typeOf exp1) in
      let typ2_size = get_element_size_in_bits (Cilfacade.typeOf exp2) in
      begin match binop with
        | PlusA
        | PlusPI
        | IndexPI ->
          begin match eval_int_opt ask exp1, eval_int_opt ask exp2 with
            | None, None -> raise (UnsupportedCilExpression "unsupported BinOp +")
            | None, Some off2 -> let term, off1 = of_cil ask exp1 in term, Z.(off1 + typ1_size * off2)
            | Some off1, None -> let term, off2 = of_cil ask exp2 in term, Z.(typ2_size * off1 + off2)
            | Some off1, Some off2 -> None, Z.(off1 + off2)
          end
        | MinusA
        | MinusPI
        | MinusPP -> begin match of_cil ask exp1, eval_int_opt ask exp2 with
            | (Some term, off1), Some off2 -> let typ1_size = get_element_size_in_bits (Cilfacade.typeOf exp1) in
              Some term, Z.(off1 - typ1_size * off2)
            | _ -> raise (UnsupportedCilExpression "unsupported BinOp -")
          end
        | _ -> raise (UnsupportedCilExpression "unsupported BinOp")
      end
    | CastE (typ, exp)-> begin match of_cil ask exp with
        | Some (Addr x), z -> Some (Addr x), z
        | Some (Aux (x, _)), z -> Some (Aux (x, CastE (typ, exp))), z
        | Some (Deref (x, z, _)), z' -> Some (Deref (x, z, CastE (typ, exp))), z'
        | t, z -> t, z
      end
    | _ -> raise (UnsupportedCilExpression "unsupported Cil Expression")
  and of_lval ask lval =
    let res =
      match lval with
      | (Var var, off) -> if is_struct_type var.vtype then of_offset ask (Addr var) off var.vtype (Lval lval)
        else
          of_offset ask (term_of_varinfo var) off var.vtype (Lval lval)
      | (Mem exp, off) ->
        begin match of_cil ask exp with
          | (Some term, offset) ->
            let typ = typeOf exp in
            if is_struct_ptr_type typ then
              match of_offset ask term off typ (Lval lval) with
              | Addr x -> Addr x
              | Aux (v,exp) -> Aux (v,exp)
              | Deref (x, z, exp) -> Deref (x, Z.(z+offset), exp)
            else
              of_offset ask (Deref (term, offset, Lval(Mem exp, NoOffset))) off (typeOfLval (Mem exp, NoOffset)) (Lval lval)
          | _ -> raise (UnsupportedCilExpression "cannot dereference constant")
        end
    in
    (if M.tracing then match res with
        | exception (UnsupportedCilExpression s) -> M.trace "wrpointer-cil-conversion" "unsupported exp: %a\n%s\n" d_plainlval lval s
        | t -> M.trace "wrpointer-cil-conversion" "lval: %a --> %s\n" d_plainlval lval (show t))
  ;res

  (** Converts the negated expresion to a term if neg = true.
      If neg = false then it simply converts the expression to a term. *)
  let rec of_cil_neg ask neg e = match e with
    | UnOp (op,exp,typ)->
      begin match op with
        | Neg -> of_cil_neg ask (not neg) exp
        | _ -> if neg then raise (UnsupportedCilExpression "unsupported UnOp Neg") else of_cil ask e
      end
    | _ -> if neg then raise (UnsupportedCilExpression "unsupported UnOp Neg") else of_cil ask e

  let of_cil_neg ask neg e =
    match is_float (typeOf e) with
    | exception GoblintCil__Errormsg.Error | true -> None, None
    | false ->
      let res = match of_cil_neg ask neg (Cil.constFold false e) with
        | exception (UnsupportedCilExpression s) -> if M.tracing then M.trace "wrpointer-cil-conversion" "unsupported exp: %a\n%s\n" d_plainexp e s;
          None, None
        | t, z -> t, Some z
      in (if M.tracing && not neg then match res with
          | None, Some z ->  M.trace "wrpointer-cil-conversion" "constant exp: %a --> %s\n" d_plainexp e (Z.to_string z)
          | Some t, Some z -> M.trace "wrpointer-cil-conversion" "exp: %a --> %s + %s\n" d_plainexp e (show t) (Z.to_string z);
          | _ -> ()); res

  (** Convert the expression to a term,
      and additionally check that the term is 64 bits.
      If it's not a 64bit pointer, it returns None, None. *)
  let of_cil ask e =
    match of_cil_neg ask false e with
    | Some t, Some z ->
      (* check if t is a valid pointer *)
      let exp = to_cil t in
      if check_valid_pointer exp then
        Some t, Some z
      else (if M.tracing then M.trace "wrpointer-cil-conversion" "invalid exp: %a --> %s + %s\n" d_plainexp e (show t) (Z.to_string z);
            None, None)
    | t, z -> t, z

  let map_z_opt op z = Tuple2.map2 (Option.map (op z))

  (** Converts a cil expression e = "t1 + off1 - (t2 + off2)" to two terms (Some t1, Some off1), (Some t2, Some off2)*)
  let rec two_terms_of_cil ask neg e =
    let pos_t, neg_t = match e with
      | UnOp (Neg,exp,typ) -> two_terms_of_cil ask (not neg) exp
      | BinOp (binop, exp1, exp2, typ)-> begin match binop with
          | PlusA
          | PlusPI
          | IndexPI -> begin match of_cil_neg ask false exp1 with
              | (None, Some off1) -> let pos_t, neg_t = two_terms_of_cil ask true exp2 in
                map_z_opt Z.(+) off1 pos_t, neg_t
              | (Some term, Some off1) -> (Some term, Some off1), of_cil_neg ask true exp2
              | _ -> (None, None), (None, None)
            end
          | MinusA
          | MinusPI
          | MinusPP -> begin match of_cil_neg ask false exp1 with
              | (None, Some off1) -> let pos_t, neg_t = two_terms_of_cil ask false exp2 in
                map_z_opt Z.(+) off1 pos_t, neg_t
              | (Some term, Some off1) -> (Some term, Some off1), of_cil_neg ask false exp2
              | _ -> of_cil_neg ask false e, (None, Some Z.zero)
            end
          | _ -> of_cil_neg ask false e, (None, Some Z.zero)
        end
      | _ -> of_cil_neg ask false e, (None, Some Z.zero)
    in if neg then neg_t, pos_t else pos_t, neg_t

  (** `prop_of_cil e pos` parses the expression `e` (or `not e` if `pos = false`) and
      returns a list of length 1 with the parsed expresion or an empty list if
        the expression can't be expressed with the data type `prop`. *)
  let rec prop_of_cil ask e pos =
    let e = Cil.constFold false e in
    match e with
    | BinOp (r, e1, e2, _) ->
      begin  match two_terms_of_cil ask false (BinOp (MinusPI, e1, e2, TInt (Cilfacade.get_ikind_exp e,[]))) with
        | ((Some t1, Some z1), (Some t2, Some z2)) ->
          begin match r with
            | Eq -> if pos then [Equal (t1, t2, Z.(z2-z1))] else [Nequal (t1, t2, Z.(z2-z1))]
            | Ne -> if pos then [Nequal (t1, t2, Z.(z2-z1))] else [Equal (t1, t2, Z.(z2-z1))]
            | _ -> []
          end
        | _,_ -> []
      end
    | UnOp (LNot, e1, _) -> prop_of_cil ask e1 (not pos)
    | _ -> []
end

module TMap = struct
  include Map.Make(T)
  let hash node_hash y = fold (fun x node acc -> acc + T.hash x + node_hash node) y 0
end

module TSet = struct
  include Set.Make(T)
  let hash x = fold (fun x y -> y + T.hash x) x 0
end

(** Quantitative union find *)
module UnionFind = struct
  module ValMap = TMap

  (** (value * offset) ref * size of equivalence class *)
  type 'v node = ('v * Z.t) * int [@@deriving eq, ord, hash]

  type t = T.t node ValMap.t [@@deriving eq, ord, hash] (** Union Find Map: maps value to a node type *)

  exception UnknownValue of T.t
  exception InvalidUnionFind of string

  let empty = ValMap.empty

  (** create empty union find map, given a list of elements *)
  let init = List.fold_left (fun map v -> ValMap.add v ((v, Z.zero), 1) map) (ValMap.empty)

  (** `parent uf v` returns (p, z) where p is the parent element of
      v in the union find tree and z is the offset.

        Throws "Unknown value" if v is not present in the data structure.*)
  let parent uf v = match fst (ValMap.find v uf) with
    | exception Not_found -> raise (UnknownValue v)
    | x -> x

  (** `parent_opt uf v` returns Some (p, z) where p is the parent element of
      v in the union find tree and z is the offset.
      It returns None if v is not present in the data structure. *)
  let parent_opt uf v = Option.map (fun _ -> parent uf v) (ValMap.find_opt v uf)

  let parent_term uf v = fst (parent uf v)
  let parent_offset uf v = snd (parent uf v)
  let subtree_size uf v = snd (ValMap.find v uf)

  (** Modifies the size of the equivalence class for the current element and
      for the whole path to the root of this element.

      The third parameter `modification` is the function to apply to the sizes. *)
  let rec modify_size t uf modification =
    let (p, old_size) = ValMap.find t uf in
    let uf = ValMap.add t (p, modification old_size) uf in
    let parent = fst p in
    if T.equal parent t then uf else modify_size parent uf modification

  let modify_parent uf v (t, offset) =
    let (_, size) = ValMap.find v uf in
    ValMap.add v ((t, offset), size) uf

  let modify_offset uf v modification =
    let ((t, offset), size) = ValMap.find v uf in
    ValMap.add v ((t, modification offset), size) uf

  (** Returns true if each equivalence class in the data structure contains only one element,
      i.e. every node is a root. *)
  let is_empty uf = List.for_all (fun (v, (t, _)) -> T.equal v (fst t)) (ValMap.bindings uf)

  (** Returns true if v is the representative value of its equivalence class.

      Throws "Unknown value" if v is not present in the data structure. *)
  let is_root uf v = let (parent_t, _) = parent uf v in T.equal v parent_t

  (** The difference between `show_uf` and `show_uf_ugly` is that `show_uf` prints the elements
      grouped by equivalence classes, while this function just prints them in any order.

      Throws "Unknown value" if v is not present in the data structure. *)
  let show_uf_ugly uf =
    List.fold_left (fun s (v, (refv, size)) ->
        s ^ "\t" ^ (if is_root uf v then "Root: " else "") ^ T.show v ^
        "; Parent: " ^ T.show (fst refv) ^ "; offset: " ^ Z.to_string (snd refv) ^ "; size: " ^ string_of_int size ^ "\n")
      "" (ValMap.bindings uf) ^ "\n"

  (**
     For a variable t it returns the reference variable v and the offset r.
     This find performs path compression.
     It returns als the updated union-find tree after the path compression.

     Throws "Unknown value" if t is not present in the data structure.
     Throws "Invalid Union Find" if it finds an element in the data structure that is a root but it has a non-zero distance to itself.
  *)
  let find uf v =
    let (v',r') = parent uf v in
    if T.equal v' v then
      (* v is a root *)
      if Z.equal r' Z.zero then v',r', uf
      else raise (InvalidUnionFind "non-zero self-distance!")
    else if is_root uf v' then
      (* the parent of v is a root *)
      v',r', uf
    else
      let rec search v list =
        let (v',r') = parent uf v in
        if is_root uf v' then
          (* perform path compresion *)
          let (r',uf) = List.fold_left (fun (r0, uf) v ->
              let (parent_v, r''), size_v = ValMap.find v uf in
              let uf = modify_parent uf v (v',Z.(r0+r'')) in
              let uf = modify_size parent_v uf (fun s -> s - size_v) in
              let uf = modify_size v' uf ((+) size_v)
              in Z.(r0+r''),uf) (Z.zero, uf) (v::list)
          in v',r',uf
        else search v' (v :: list)
      in search v' [v]

  (** Returns None if the value v is not present in the datat structure or if the data structure is in an invalid state.*)
  let find_opt uf v = match find uf v with
    | exception (UnknownValue _)
    | exception Not_found
    | exception (InvalidUnionFind _) -> None
    | res -> Some res

  (**
     For a variable t it returns the reference variable v and the offset r.
     This find DOES NOT perform path compression.

     Throws "Unknown value" if t is not present in the data structure.
     Throws "Invalid Union Find" if it finds an element in the data structure that is a root but it has a non-zero distance to itself.
  *)
  let rec find_no_pc uf v =
    let (v',r') = parent uf v in
    if T.equal v' v then
      if Z.equal r' Z.zero then (v',r')
      else raise (InvalidUnionFind "non-zero self-distance!")
    else let (v'', r'') = find_no_pc uf v' in (v'', Z.(r'+r''))

  (** Returns find of v if v is in the union find data structure.
      Otherwise it just returns v. *)
  let find_no_pc_if_possible uf v =
    match find_no_pc uf v with
    | exception (UnknownValue _)
    | exception Not_found
    | exception (InvalidUnionFind _) -> v, Z.zero
    | res -> res

  let compare_repr = Tuple2.compare ~cmp1:T.compare ~cmp2:Z.compare

  (** Compare only first element of the tuples (= the parent term).
      It ignores the offset. *)
  let compare_repr_v (v1, _) (v2, _) = T.compare v1 v2

  (**
     Parameters: uf v1 v2 r

     changes the union find data structure `uf` such that the equivalence classes of `v1` and `v2` are merged and `v1 = v2 + r`

     returns v,uf,b where

     - `v` is the new reference term of the merged equivalence class. It is either the old reference term of v1 or of v2, depending on which equivalence class is bigger.

     - `uf` is the new union find data structure

     - `b` is true iff v = find v1

  *)
  let union uf v'1 v'2 r =
    let v1,r1,uf = find uf v'1 in
    let v2,r2,uf = find uf v'2 in
    if T.equal v1 v2 then
      if Z.(equal r1 (r2 + r)) then v1, uf, true
      else raise (Failure "incomparable union")
    else let (_,s1), (_,s2) = ValMap.find v1 uf, ValMap.find v2 uf in
      if s1 <= s2 then (
        v2, modify_size v2 (modify_parent uf v1 (v2, Z.(r2 - r1 + r))) ((+) s1), false
      ) else (
        v1, modify_size v1 (modify_parent uf v2 (v1, Z.(r1 - r2 - r))) ((+) s2), true
      )

  (** Returns a list of equivalence classes. *)
  let get_eq_classes uf = List.group (fun (el1,_) (el2,_) -> compare_repr_v (find_no_pc uf el1) (find_no_pc uf el2)) (ValMap.bindings uf)

  (** Throws "Unknown value" if the data structure is invalid. *)
  let show_uf uf = List.fold_left (fun s eq_class ->
      s ^ List.fold_left (fun s (v, (t, size)) ->
          s ^ "\t" ^ (if is_root uf v then "R: " else "") ^ "("^T.show v ^ "; P: " ^ T.show (fst t) ^
          "; o: " ^ Z.to_string (snd t) ^ "; s: " ^ string_of_int size ^")\n") "" eq_class
      ^ "----\n") "" (get_eq_classes uf) ^ "\n"

  let get_representatives uf =
    List.filter_map (fun (el,_) -> if is_root uf el then Some el else None) (TMap.bindings uf)
end

module ZMap = struct
  include Map.Make(Z)
  let hash hash_f y = fold (fun x node acc -> acc + Z.hash x + hash_f node) y 0
end

(** For each representative t' of an equivalence class, the LookupMap maps t' to a map that maps z to a term in the data structure that is equal to *(z + t').*)
module LookupMap = struct
  (* map: term -> z -> *(z + t)   *)
  type t = T.t ZMap.t TMap.t [@@deriving eq, ord, hash]

  let bindings = TMap.bindings
  let add = TMap.add
  let remove = TMap.remove
  let empty = TMap.empty
  let find_opt = TMap.find_opt
  let find = TMap.find

  let zmap_bindings = ZMap.bindings
  let zmap_find_opt = ZMap.find_opt
  let zmap_add = ZMap.add

  (** Returns the element to which (v, r) is mapped, or None if (v, r) is mapped to nothing. *)
  let map_find_opt (v,r) (map:t) = match find_opt v map with
    | None -> None
    | Some zmap -> (match zmap_find_opt r zmap with
        | None -> None
        | Some v -> Some v
      )

  let map_add (v,r) v' (map:t) = match find_opt v map with
    | None -> add v (zmap_add r v' ZMap.empty) map
    | Some zmap -> add v (zmap_add r v' zmap) map

  let show_map (map:t) =
    List.fold_left
      (fun s (v, zmap) ->
         s ^ T.show v ^ "\t:\n" ^
         List.fold_left
           (fun s (r, v) ->
              s ^ "\t" ^ Z.to_string r ^ ": " ^ T.show v ^ "; ")
           "" (zmap_bindings zmap) ^ "\n")
      "" (bindings map)

  (** The value at v' is shifted by r and then added for v.
      The old entry for v' is removed. *)
  let shift v r v' map =
    match find_opt v' map with
    | None -> map
    | Some zmap -> let infl = zmap_bindings zmap in
      let zmap = List.fold_left (fun zmap (r', v') ->
          zmap_add Z.(r' + r) v' zmap) ZMap.empty infl in
      remove v' (add v zmap map)

  (** Find all outgoing edges of v in the automata.*)
  let successors v (map:t) =
    match find_opt v map with
    | None -> []
    | Some zmap -> zmap_bindings zmap

  (** Filters elements from the mapped values which fulfil the predicate p. *)
  let filter_if (map:t) p =
    TMap.filter_map (fun _ zmap ->
        let zmap = ZMap.filter (fun key value -> p value) zmap
        in if ZMap.is_empty zmap then None else Some zmap) map

  (** Maps elements from the mapped values by applying the function f to them. *)
  let map_values (map:t) f =
    TMap.map (fun zmap ->
        ZMap.map f zmap) map
end

(** Quantitative congruence closure on terms *)
module CongruenceClosure = struct

  module TUF = UnionFind
  module LMap = LookupMap

  module Disequalities = struct

    (* disequality map:
       if t_1 -> z -> {t_2, t_3}
       then we know that t_1 + z != t_2
       and also that t_1 + z != t_3
    *)
    type t = TSet.t ZMap.t TMap.t [@@deriving eq, ord, hash] (* disequalitites *)
    type arg_t = (T.t * Z.t) ZMap.t TMap.t (* maps each state in the automata to its predecessors *)

    let empty = TMap.empty
    let remove = TMap.remove
    (** Returns a list of tuples, which each represent a disequality *)
    let bindings =
      List.flatten %
      List.concat_map
        (fun (t, smap) ->
           List.map (fun (z, tset) ->
               List.map (fun term ->
                   (t,z,term)) (TSet.elements tset))
             (ZMap.bindings smap)
        ) % TMap.bindings

    let bindings_args =
      List.flatten %
      List.concat_map
        (fun (t, smap) ->
           List.map (fun (z, arglist) ->
               List.map (fun (a,b) ->
                   (t,z,a,b)) arglist)
             (ZMap.bindings smap)
        ) % TMap.bindings

    (** adds a mapping v -> r -> size -> { v' } to the map,
        or if there are already elements
        in v -> r -> {..} then v' is added to the previous set *)
    let map_set_add (v,r) v' (map:t) = match TMap.find_opt v map with
      | None -> TMap.add v (ZMap.add r (TSet.singleton v') ZMap.empty) map
      | Some imap -> TMap.add v (
          match ZMap.find_opt r imap with
          | None -> ZMap.add r (TSet.singleton v') imap
          | Some set -> ZMap.add r (TSet.add v' set) imap) map

    let shift = LMap.shift

    let map_set_mem (v,r) v' (map:t) = match TMap.find_opt v map with
      | None -> false
      | Some imap -> (match ZMap.find_opt r imap with
          | None -> false
          | Some set -> TSet.mem v' set
        )

    (** Map of partition, transform union find to a map
        of type V -> Z -> V set
        with reference variable |-> offset |-> all terms that are in the union find with this ref var and offset. *)
    let comp_map uf = List.fold_left (fun comp (v,_) ->
        map_set_add (TUF.find_no_pc uf v) v comp)
        TMap.empty (TMap.bindings uf)

    (** Find all elements that are in the same equivalence class as t. *)
    let comp_t uf t =
      let (t',z') = TUF.find_no_pc uf t in
      List.fold_left (fun comp (v,((p,z),_)) ->
          let (v', z'') = TUF.find_no_pc uf v in
          if T.equal v' t' then (v, Z.(z'-z''))::comp else comp
        )
        [] (TMap.bindings uf)

    let flatten_map =
      ZMap.map (fun zmap -> List.fold_left
                   (fun set (_,mapped) -> TSet.union set mapped) TSet.empty (ZMap.bindings zmap))

    (** arg:

        maps each representative term t to a map that maps an integer Z to
        a list of representatives t' of v where *(v + z') is
        in the representative class of t.

        It basically maps each state in the automata to its predecessors. *)
    let get_args uf =
      let cmap  = comp_map uf in
      let clist = TMap.bindings cmap in
      let arg =  List.fold_left (fun arg (v, imap) ->
          let ilist = ZMap.bindings imap in
          let iarg = List.fold_left (fun iarg (r,set) ->
              let list = List.filter_map (function
                  | Deref (v', r', _) ->
                    let (v0,r0) = TUF.find_no_pc uf v' in
                    Some (v0,Z.(r0+r'))
                  | _ -> None) (TSet.elements set) in
              ZMap.add r list iarg) ZMap.empty ilist in
          TMap.add v iarg arg) TMap.empty clist in
      (uf,cmap,arg)

    let fold_left2 f acc l1 l2 =
      List.fold_left (
        fun acc x -> List.fold_left (
            fun acc y -> f acc x y) acc l2) acc l1

    let map2 f l1 l2 = List.concat_map (fun x ->
        List.map (fun y -> f x y) l2) l1

    let map_find_opt (v,r) map = match TMap.find_opt v map with
      | None -> None
      | Some imap -> (match ZMap.find_opt r imap with
          | None -> None
          | Some v -> Some v
        )

    let map_find_all t map =
      match TMap.find_opt t map with
      | None -> []
      | Some imap -> List.fold (fun list (z,list2) ->
          list@list2
        ) [] (ZMap.bindings imap)

    let check_neq (_,arg) rest (v,zmap) =
      let zlist = ZMap.bindings zmap in
      fold_left2 (fun rest (r1,_) (r2,_) ->
          if Z.equal r1 r2 then rest
          else (* r1 <> r2 *)
            let l1 = match map_find_opt (v,r1) arg
              with None -> []
                 | Some list -> list in
            (* just take the elements of set1 ? *)
            let l2 = match map_find_opt (v,r2) arg
              with None -> []
                 | Some list -> list in
            fold_left2 (fun rest (v1,r'1) (v2,r'2) ->
                if T.equal v1 v2 then if Z.equal r'1 r'2
                  then raise Unsat
                  else rest
                else (v1,v2,Z.(r'2-r'1))::rest) rest l1 l2
        ) rest zlist zlist

    let check_neq_bl (uf,arg) rest (t1, tset) =
      List.fold (fun rest t2 ->
          if T.equal (fst@@TUF.find_no_pc_if_possible uf t1) (fst@@TUF.find_no_pc_if_possible uf t2)
          then raise Unsat
          else (* r1 <> r2 *)
            let l1 = map_find_all t1 arg in
            let l2 = map_find_all t2 arg in
            fold_left2 (fun rest (v1,r'1) (v2,r'2) ->
                if T.equal v1 v2 then if Z.equal r'1 r'2
                  then raise Unsat
                  else rest
                else (v1,v2,Z.(r'2-r'1))::rest) rest l1 l2
        ) rest (TSet.to_list tset)

    (** Initialize the list of disequalities taking only implicit dis-equalities into account.

        Returns: List of non-trivially implied dis-equalities *)
    let init_neq (uf,cmap,arg) =
      List.fold_left (check_neq (uf,arg)) [] (TMap.bindings cmap)

    let init_neg_block_diseq (uf, bldis, cmap, arg) =
      List.fold_left (check_neq_bl (uf,arg)) [] (TMap.bindings bldis)

    (** Initialize the list of disequalities taking explicit dis-equalities into account.

        Parameters: union-find partition, explicit disequalities.battrs

        Returns: list of normalized provided dis-equalities *)
    let init_list_neq uf neg =
      List.filter_map (fun (v1,v2,r) ->
          let (v1,r1) = TUF.find_no_pc uf v1 in
          let (v2,r2) = TUF.find_no_pc uf v2 in
          if T.equal v1 v2 then if Z.(equal r1 (r2+r)) then raise Unsat
            else None
          else Some (v1,v2,Z.(r2-r1+r))) neg

    (** Parameter: list of disequalities (t1, t2, z), where t1 and t2 are roots.

        Returns: map `neq` where each representative is mapped to a set of representatives it is not equal to.
    *)
    let rec propagate_neq (uf,(cmap: TSet.t ZMap.t TMap.t),arg,neq) = function (* v1, v2 are distinct roots with v1 != v2+r   *)
      | [] -> neq (* uf need not be returned: has been flattened during constr. of cmap *)
      | (v1,v2,r) :: rest ->
        (* we don't want to explicitly store disequalities of the kind &x != &y *)
        if T.is_addr v1 && T.is_addr v2 then
          propagate_neq (uf,cmap,arg,neq) rest else
          (* v1, v2 are roots; v2 -> r,v1 not yet contained in neq *)
        if T.equal v1 v2 then  (* should not happen *)
          if Z.equal r Z.zero then raise Unsat else propagate_neq (uf,cmap,arg,neq) rest
        else (* check whether it is already in neq *)
        if map_set_mem (v1,Z.(-r)) v2 neq then propagate_neq (uf,cmap,arg,neq) rest
        else let neq = map_set_add (v1,Z.(-r)) v2 neq |>
                       map_set_add (v2,r) v1 in
        (*
          search components of v1, v2 for elements at distance r to obtain inferred equalities
          at the same level (not recorded) and then compare their predecessors
        *)
          match TMap.find_opt v1 (cmap:t), TMap.find_opt v2 cmap with
          | None,_ | _,None -> (*should not happen*) propagate_neq (uf,cmap,arg,neq) rest
          | Some imap1, Some imap2 ->
            let ilist1 = ZMap.bindings imap1 in
            let rest = List.fold_left (fun rest (r1,_) ->
                match ZMap.find_opt Z.(r1+r) imap2 with
                | None -> rest
                | Some _ ->
                  let l1 = match map_find_opt (v1,r1) arg
                    with None -> []
                       | Some list -> list in
                  let l2 = match map_find_opt (v2,Z.(r1+r)) arg
                    with None -> []
                       | Some list -> list in
                  fold_left2 (fun rest (v1',r'1) (v2',r'2) ->
                      if T.equal v1' v2' then if Z.equal r'1 r'2 then raise Unsat
                        else rest
                      else
                        (v1',v2',Z.(r'2-r'1))::rest ) rest l1 l2)
                rest ilist1 in
            propagate_neq (uf,cmap,arg,neq) rest
        (*
          collection of disequalities:
                  * disequalities originating from different offsets of same root
                  * stated disequalities
                  * closure by collecting appropriate args
                          for a disequality v1 != v2 +r for distinct roots v1,v2
                          check whether there is some r1, r2 such that r1 = r2 +r
                          then dis-equate the sets at v1,r1 with v2,r2.
        *)

    let show_neq neq =
      let clist = bindings neq in
      List.fold_left (fun s (v,r,v') ->
          s ^ "\t" ^ T.show v ^ ( if Z.equal r Z.zero then "" else if Z.leq r Z.zero then (Z.to_string r) else (" + " ^ Z.to_string r) )^ " != "
          ^ T.show v' ^  "\n") "" clist

    let show_cmap neq =
      let clist = bindings neq in
      List.fold_left (fun s (v,r,v') ->
          s ^ "\t" ^ T.show v ^ ( if Z.equal r Z.zero then "" else if Z.leq r Z.zero then (Z.to_string r) else (" + " ^ Z.to_string r) )^ " = "
          ^ T.show v' ^  "\n") "" clist

    let show_arg arg =
      let clist = bindings_args arg in
      List.fold_left (fun s (v,z,v',r) ->
          s ^ "\t" ^ T.show v' ^ ( if Z.equal r Z.zero then "" else if Z.leq r Z.zero then (Z.to_string r) else (" + " ^ Z.to_string r) )^ " --> "
          ^ T.show v^ "+"^ Z.to_string z ^  "\n") "" clist

    let filter_if map p =
      TMap.filter_map (fun _ zmap ->
          let zmap = ZMap.filter_map
              (fun _ t_set -> let filtered_set = TSet.filter p t_set in
                if TSet.is_empty filtered_set then None else Some filtered_set) zmap
          in if ZMap.is_empty zmap then None else Some zmap) map

    let filter_map f (diseq:t) =
      TMap.filter_map
        (fun _ zmap ->
           let zmap = ZMap.filter_map
               (fun _ s -> let set = TSet.filter_map f s in
                 if TSet.is_empty set then None else Some set)
               zmap in if ZMap.is_empty zmap then None else Some zmap) diseq

    let get_disequalities = List.map
        (fun (t1, z, t2) ->
           Nequal (t1,t2,Z.(-z))
        ) % bindings

    let element_closure diseqs cmap =
      let comp_closure (r1,r2,z) =
        let to_tuple_list =  (*TODO this is not the best solution*)
          List.flatten % List.map
            (fun (z, set) -> List.cartesian_product [z] (TSet.to_list set)) in
        let comp_closure_zmap bindings1 bindings2 =
          List.map (fun ((z1, nt1),(z2, nt2)) ->
              (nt1, nt2, Z.(-z2+z+z1)))
            (List.cartesian_product (to_tuple_list bindings1) (to_tuple_list bindings2))
        in
        let singleton term = [Z.zero, TSet.singleton term] in
        begin match TMap.find_opt r1 cmap,TMap.find_opt r2 cmap with
          | None, None -> [(r1,r2,z)]
          | None, Some zmap2 -> comp_closure_zmap (singleton r1) (ZMap.bindings zmap2)
          | Some zmap1, None -> comp_closure_zmap (ZMap.bindings zmap1) (singleton r2)
          | Some zmap1, Some zmap2 ->
            comp_closure_zmap (ZMap.bindings zmap1) (ZMap.bindings zmap2)
        end
      in
      List.concat_map comp_closure diseqs
  end

  (* block disequalities *)
  module BlDis = struct
    type t = TSet.t TMap.t [@@deriving eq, ord, hash] (* block disequalitites *)

    let bindings = TMap.bindings
    let empty = TMap.empty

    let to_conj bldiseq = List.fold
        (fun list (t1, tset) ->
           TSet.fold (fun t2 bldiseqs -> BlNequal(t1, t2)::bldiseqs) tset [] @ list
        ) [] (bindings bldiseq)

    let add bldiseq t1 t2 =
      match TMap.find_opt t1 bldiseq with
      | None -> TMap.add t1 (TSet.singleton t2) bldiseq
      | Some tset -> TMap.add t1 (TSet.add t2 tset) bldiseq

    let add_block_diseq bldiseq (t1, t2) =
      add (add bldiseq t1 t2) t2 t1

    (**
       params:

       t1-> any term

       tlist: a list of representative terms

       For each term t2 in tlist, it adds the disequality t1' != t2 to diseqs
       where t1' is the representative of t1.
       Except the block disequality t1' = t1' will not be added, even
       if t1' is in tlist.
    *)
    let add_block_diseqs bldiseq uf t1 tlist =
      let t1',_ = t1, t1 in
      (* TODO: not a good idea: TUF.find_no_pc uf t1 in *)
      List.fold (fun bldiseq t2 ->
          if T.equal t1' t2 then bldiseq
          else add_block_diseq bldiseq (t1', t2)) bldiseq tlist

    let element_closure bldis cmap =
      let comp_closure = function
        | BlNequal (r1,r2) ->
          let to_list =  (*TODO this is not the best solution*)
            List.flatten % List.map
              (fun (z, set) -> (TSet.to_list set)) in
          let comp_closure_zmap bindings1 bindings2 =
            List.cartesian_product (to_list bindings1) (to_list bindings2)
          in
          let singleton term = [(Z.zero, TSet.singleton term)] in
          begin match TMap.find_opt r1 cmap,TMap.find_opt r2 cmap with
            | None, None -> [(r1,r2)]
            | None, Some zmap2 -> comp_closure_zmap (singleton r1) (ZMap.bindings zmap2)
            | Some zmap1, None -> comp_closure_zmap (ZMap.bindings zmap1) (singleton r2)
            | Some zmap1, Some zmap2 ->
              comp_closure_zmap (ZMap.bindings zmap1) (ZMap.bindings zmap2)
          end
        | _ -> []
      in
      List.concat_map comp_closure bldis

    let map_set_mem v v' (map:t) = match TMap.find_opt v map with
      | None -> false
      | Some set -> TSet.mem v' set
  end

  (** Set of subterms which are present in the current data structure. *)
  module SSet = struct
    type t = TSet.t [@@deriving eq, ord, hash]

    let elements = TSet.elements
    let mem = TSet.mem
    let add = TSet.add
    let fold = TSet.fold
    let empty = TSet.empty
    let to_list = TSet.to_list
    let inter = TSet.inter
    let find_opt = TSet.find_opt
    let union = TSet.union

    let show_set set = TSet.fold (fun v s ->
        s ^ "\t" ^ T.show v ^ ";\n") set "" ^ "\n"

    (** Adds all subterms of t to the SSet and the LookupMap*)
    let rec subterms_of_term (set,map) t = match t with
      | Addr _ | Aux _ -> (add t set, map)
      | Deref (t',z,_) ->
        let set = add t set in
        let map = LMap.map_add (t',z) t map in
        subterms_of_term (set, map) t'

    (** Adds all subterms of the proposition to the SSet and the LookupMap*)
    let subterms_of_prop (set,map) = function
      |  (t1,t2,_) -> subterms_of_term (subterms_of_term (set,map) t1) t2

    let subterms_of_conj list = List.fold_left subterms_of_prop (TSet.empty, LMap.empty) list

    let fold_atoms f (acc:'a) set:'a =
      let exception AtomsDone in
      let res = ref acc in
      try
        TSet.fold (fun (v:T.t) acc -> match v with
            | Addr _| Aux _ -> f acc v
            | _ -> res := acc; raise AtomsDone) set acc
      with AtomsDone -> !res

    let get_atoms set =
      (* `elements set` returns a sorted list of the elements. The atoms are always smaller that other terms,
         according to our comparison function. Therefore take_while is enough. *)
      BatList.take_while (function Addr _ | Aux _ -> true | _ -> false) (elements set)

    (** We try to find the dereferenced term between the already existing terms, in order to remember the information about the exp. *)
    let deref_term t z set =
      let exp = T.to_cil t in
      match find_opt (Deref (t, z, exp)) set with
      | None -> Deref (t, z, T.dereference_exp exp z)
      | Some t -> t

    let deref_term_even_if_its_not_possible min_term z set =
      match deref_term min_term z set with
      | result -> result
      | exception (T.UnsupportedCilExpression _) ->
        let random_type = (TPtr (TPtr (TInt (ILong,[]),[]),[])) in (*the type is not so important for min_repr and get_normal_form*)
        Deref (min_term, z, Lval (Mem (BinOp (PlusPI, T.to_cil(min_term), T.to_cil_constant z (Some random_type), random_type)), NoOffset))

  end

  (** Minimal representatives map.
      It maps each representative term of an equivalence class to the minimal term of this representative class.
      rep -> (t, z) means that t = rep + z *)
  module MRMap = struct
    type t = (T.t * Z.t) TMap.t [@@deriving eq, ord, hash]

    let bindings = TMap.bindings
    let find = TMap.find
    let find_opt = TMap.find_opt
    let add = TMap.add
    let remove = TMap.remove
    let mem = TMap.mem
    let empty = TMap.empty

    let show_min_rep min_representatives =
      let show_one_rep s (state, (rep, z)) =
        s ^ "\tState: " ^ T.show state ^
        "\n\tMin: (" ^ T.show rep ^ ", " ^ Z.to_string z ^ ")--\n\n"
      in
      List.fold_left show_one_rep "" (bindings min_representatives)

    let rec update_min_repr (uf, set, map) min_representatives = function
      | [] -> min_representatives, uf
      | state::queue -> (* process all outgoing edges in order of ascending edge labels *)
        match LMap.successors state map with
        | edges ->
          let process_edge (min_representatives, queue, uf) (edge_z, next_term) =
            let next_state, next_z, uf = TUF.find uf next_term in
            let (min_term, min_z) = find state min_representatives in
            let next_min =
              (SSet.deref_term_even_if_its_not_possible min_term Z.(edge_z - min_z) set, next_z) in
            match TMap.find_opt next_state min_representatives
            with
            | None ->
              (add next_state next_min min_representatives, queue @ [next_state], uf)
            | Some current_min when T.compare (fst next_min) (fst current_min) < 0 ->
              (add next_state next_min min_representatives, queue @ [next_state], uf)
            | _ -> (min_representatives, queue, uf)
          in
          let (min_representatives, queue, uf) = List.fold_left process_edge (min_representatives, queue, uf) edges
          in update_min_repr (uf, set, map) min_representatives queue

    (** Uses dijkstra algorithm to update the minimal representatives of
          the successor nodes of all edges in the queue
          and if necessary it recursively updates the minimal representatives of the successor nodes.
          The states in the queue must already have an updated min_repr.
          This function visits only the successor nodes of the nodes in queue, not the nodes themselves.
          Before visiting the nodes, it sorts the queue by the size of the current mininmal representative.

          parameters:

        - `(uf, map)` represent the union find data structure and the corresponding lookup map.
        - `min_representatives` maps each representative of the union find data structure to the minimal representative of the equivalence class.
        - `queue` contains the states that need to be processed.
          The states of the automata are the equivalence classes and each state of the automata is represented by the representative term.
          Therefore the queue is a list of representative terms.

        Returns:
        - The map with the minimal representatives
        - The union find tree. This might have changed because of path compression. *)
    let update_min_repr (uf, set, map) min_representatives queue =
      (* order queue by size of the current min representative *)
      let queue =
        List.sort_unique (fun el1 el2 -> let compare_repr = TUF.compare_repr (find el1 min_representatives) (find el2 min_representatives) in
                           if compare_repr = 0 then T.compare el1 el2 else compare_repr) (List.filter (TUF.is_root uf) queue)
      in update_min_repr (uf, set, map) min_representatives queue

    (**
       Computes a map that maps each representative of an equivalence class to the minimal representative of the equivalence class.
       It's used for now when removing elements, then the min_repr map gets recomputed.

       Returns:
       - The map with the minimal representatives
       - The union find tree. This might have changed because of path compression. *)
    let compute_minimal_representatives (uf, set, map) =
      if M.tracing then M.trace "wrpointer" "compute_minimal_representatives\n";
      let atoms = SSet.get_atoms set in
      (* process all atoms in increasing order *)
      let uf_ref = ref uf in
      let atoms =
        List.sort (fun el1 el2 ->
            let v1, z1, new_uf = TUF.find !uf_ref el1 in
            uf_ref := new_uf;
            let v2, z2, new_uf = TUF.find !uf_ref el2 in
            uf_ref := new_uf;
            let repr_compare = TUF.compare_repr (v1, z1) (v2, z2)
            in
            if repr_compare = 0 then T.compare el1 el2 else repr_compare) atoms in
      let add_atom_to_map (min_representatives, queue, uf) a =
        let (rep, offs, uf) = TUF.find uf a in
        if not (mem rep min_representatives) then
          (add rep (a, offs) min_representatives, queue @ [rep], uf)
        else (min_representatives, queue, uf)
      in
      let (min_representatives, queue, uf) = List.fold_left add_atom_to_map (empty, [], uf) atoms
      (* compute the minimal representative of all remaining edges *)
      in update_min_repr (uf, set, map) min_representatives queue

    (** Computes the initial map of minimal representatives.
          It maps each element `e` in the set to `(e, 0)`. *)
    let initial_minimal_representatives set =
      List.fold_left (fun map element -> add element (element, Z.zero) map) empty (SSet.elements set)
  end

  type t = {uf: TUF.t;
            set: SSet.t;
            map: LMap.t;
            min_repr: MRMap.t;
            diseq: Disequalities.t;
            bldis: BlDis.t}
  [@@deriving eq, ord, hash]

  let string_of_prop = function
    | Equal (t1,t2,r) when Z.equal r Z.zero -> T.show t1 ^ " = " ^ T.show t2
    | Equal (t1,t2,r) -> T.show t1 ^ " = " ^ Z.to_string r ^ "+" ^ T.show t2
    | Nequal (t1,t2,r) when Z.equal r Z.zero -> T.show t1 ^ " != " ^ T.show t2
    | Nequal (t1,t2,r) -> T.show t1 ^ " != " ^ Z.to_string r ^ "+" ^ T.show t2
    | BlNequal (t1,t2) -> "bl(" ^ T.show t1 ^ ") != bl(" ^ T.show t2 ^ ")"

  let show_conj list = List.fold_left
      (fun s d -> s ^ "\t" ^ string_of_prop d ^ ";\n") "" list

  (** Returns a list of all the transition that are present in the automata. *)
  let get_transitions (uf, map) =
    List.concat_map (fun (t, zmap) ->
        (List.map (fun (edge_z, res_t) ->
             (edge_z, t, TUF.find_no_pc uf res_t)) @@
         (LMap.zmap_bindings zmap)))
      (LMap.bindings map)

  (* Runtime = O(nr. of atoms) + O(nr. transitions in the automata)
     Basically runtime = O(size of result) if we hadn't removed the trivial conjunctions. *)
  (** Returns the canonical normal form of the data structure in form of a sorted list of conjunctions.  *)
  let get_normal_form cc =
    let normalize_equality (t1, t2, z) =
      if T.equal t1 t2 && Z.(equal z zero) then None else
        Some (Equal (t1, t2, z)) in
    let conjunctions_of_atoms =
      let atoms = SSet.get_atoms cc.set in
      List.filter_map (fun atom ->
          let (rep_state, rep_z) = TUF.find_no_pc cc.uf atom in
          let (min_state, min_z) = MRMap.find rep_state cc.min_repr in
          normalize_equality (atom, min_state, Z.(rep_z - min_z))
        ) atoms
    in
    let conjunctions_of_transitions =
      let transitions = get_transitions (cc.uf, cc.map) in
      List.filter_map (fun (z,s,(s',z')) ->
          let (min_state, min_z) = MRMap.find s cc.min_repr in
          let (min_state', min_z') = MRMap.find s' cc.min_repr in
          normalize_equality (SSet.deref_term_even_if_its_not_possible min_state Z.(z - min_z) cc.set, min_state', Z.(z' - min_z'))
        ) transitions in
    (*disequalities*)
    let disequalities = Disequalities.get_disequalities cc.diseq in
    (* find disequalities between min_repr *)
    let normalize_disequality (t1, t2, z) =
      let (min_state1, min_z1) = MRMap.find t1 cc.min_repr in
      let (min_state2, min_z2) = MRMap.find t2 cc.min_repr in
      let new_offset = Z.(-min_z2 + min_z1 + z) in
      if T.compare min_state1 min_state2 < 0 then Nequal (min_state1, min_state2, new_offset)
      else Nequal (min_state2, min_state1, Z.(-new_offset))
    in
    if M.tracing then M.trace "wrpointer-diseq" "DISEQUALITIES: %s;\nUnion find: %s\nMin repr: %s\nMap: %s\n" (show_conj disequalities) (TUF.show_uf cc.uf) (MRMap.show_min_rep cc.min_repr) (LMap.show_map cc.map);
    let disequalities = List.map (function | Equal (t1,t2,z) | Nequal (t1,t2,z) -> normalize_disequality (t1, t2, z)|BlNequal (t1,t2) -> BlNequal (t1,t2)) disequalities in
    (* block disequalities *)
    let normalize_bldis t = match t with
      | BlNequal (t1,t2) ->
        let min_state1 =
          begin match MRMap.find_opt t1 cc.min_repr with
            | None -> t1
            | Some (a,_) -> a
          end in
        let min_state2 =
          begin match MRMap.find_opt t2 cc.min_repr with
            | None -> t2
            | Some (a,_) -> a
          end in
        if T.compare min_state1 min_state2 < 0 then BlNequal (min_state1, min_state2)
        else BlNequal (min_state2, min_state1)
      | _ -> t
    in
    let conjunctions_of_bl_diseqs = List.map normalize_bldis @@ BlDis.to_conj cc.bldis in
    (* all propositions *)
    BatList.sort_unique (T.compare_v_prop) (conjunctions_of_atoms @ conjunctions_of_transitions @ disequalities @ conjunctions_of_bl_diseqs)

  let show_all x = "Normal form:\n" ^
                   show_conj((get_normal_form x)) ^
                   "Union Find partition:\n" ^
                   (TUF.show_uf x.uf)
                   ^ "\nSubterm set:\n"
                   ^ (SSet.show_set x.set)
                   ^ "\nLookup map/transitions:\n"
                   ^ (LMap.show_map x.map)
                   ^ "\nMinimal representatives:\n"
                   ^ (MRMap.show_min_rep x.min_repr)
                   ^ "\nNeq:\n"
                   ^ (Disequalities.show_neq x.diseq)
                   ^ "\nBlock diseqs:\n"
                   ^ show_conj(BlDis.to_conj x.bldis)

  (** Splits the conjunction into two groups: the first one contains all equality propositions,
      and the second one contains all inequality propositions.  *)
  let split conj = List.fold_left (fun (pos,neg,bld) -> function
      | Equal (t1,t2,r) -> ((t1,t2,r)::pos,neg,bld)
      | Nequal(t1,t2,r) -> (pos,(t1,t2,r)::neg,bld)
      | BlNequal (t1,t2) -> (pos,neg,(t1,t2)::bld)) ([],[],[]) conj

  (**
     returns {uf, set, map, min_repr}, where:

     - `uf` = empty union find structure where the elements are all subterms occuring in the conjunction.

     - `set` = set of all subterms occuring in the conjunction.

     - `map` = for each subterm *(z + t') the map maps t' to a map that maps z to *(z + t').

     - `min_repr` = maps each representative of an equivalence class to the minimal representative of the equivalence class.
  *)
  let init_cc conj =
    let (set, map) = SSet.subterms_of_conj conj in
    let uf = SSet.elements set |>
             TUF.init in
    let min_repr = MRMap.initial_minimal_representatives set in
    {uf; set; map; min_repr; diseq = Disequalities.empty; bldis=BlDis.empty}

  (** closure of disequalities *)
  let congruence_neq cc neg =
    try
      let neg = Tuple3.second (split(Disequalities.get_disequalities cc.diseq)) @ neg in
      (* getting args of dereferences *)
      let uf,cmap,arg = Disequalities.get_args cc.uf in
      (* taking implicit dis-equalities into account *)
      let neq_list = Disequalities.init_neq (uf,cmap,arg) @ Disequalities.init_neg_block_diseq (uf, cc.bldis, cmap,arg) in
      let neq = Disequalities.propagate_neq (uf,cmap,arg,Disequalities.empty) neq_list in
      (* taking explicit dis-equalities into account *)
      let neq_list = Disequalities.init_list_neq uf neg in
      let neq = Disequalities.propagate_neq (uf,cmap,arg,neq) neq_list in
      if M.tracing then M.trace "wrpointer-neq" "congruence_neq: %s\nUnion find: %s\n" (Disequalities.show_neq neq) (TUF.show_uf uf);
      Some {uf; set=cc.set; map=cc.map; min_repr=cc.min_repr;diseq=neq; bldis=cc.bldis}
    with Unsat -> None

  (**
     parameters: (uf, map) equalities.

     returns updated (uf, map, queue), where:

     `uf` is the new union find data structure after having added all equalities.

     `map` maps reference variables v to a map that maps integers z to terms that are equivalent to *(v + z).

     `queue` is a list of equivalence classes (represented by their representative) that have a new representative after the execution of this function.
     It can be given as a parameter to `update_min_repr` in order to update the representatives in the representative map.

     `new_repr` -> maps each representative to its new representative after the union

     Throws "Unsat" if a contradiction is found.
  *)
  let rec closure (uf, map, min_repr, new_repr) queue = function
    | [] -> (uf, map, queue, min_repr, new_repr)
    | (t1, t2, r)::rest ->
      (let v1, r1, uf = TUF.find uf t1 in
       let v2, r2, uf = TUF.find uf t2 in
       let sizet1, sizet2 = T.get_size t1, T.get_size t2 in
       if not (Z.equal sizet1 sizet2) then
         (if M.tracing then M.trace "wrpointer" "ignoring equality because the sizes are not the same: %s = %s + %s" (T.show t1) (Z.to_string r) (T.show t2);
          closure (uf, map, min_repr, new_repr) queue rest) else
       if T.equal v1 v2 then
         (* t1 and t2 are in the same equivalence class *)
         if Z.equal r1 Z.(r2 + r) then closure (uf, map, min_repr, new_repr) queue rest
         else raise Unsat
       else let diff_r = Z.(r2 - r1 + r) in
         let v, uf, b = TUF.union uf v1 v2 diff_r in (* union *)
         (* update new_representative *)
         let new_repr = if T.equal v v1 then TMap.add v2 v new_repr else TMap.add v1 v new_repr in
         (* update map *)
         let map, rest = match LMap.find_opt v1 map, LMap.find_opt v2 map, b with
           | None, _, false -> map, rest
           | None, Some _, true -> LMap.shift v1 Z.(r1-r2-r) v2 map, rest
           | Some _, None,false -> LMap.shift v2 Z.(r2-r1+r) v1 map, rest
           | _,None,true -> map, rest (* either v1 or v2 does not occur inside Deref *)
           | Some imap1, Some imap2, true -> (* v1 is new root *)
             (* zmap describes args of Deref *)
             let r0 = Z.(r2-r1+r) in  (* difference between roots  *)
             (* we move all entries of imap2 to imap1 *)
             let infl2 = List.map (fun (r',v') -> Z.(-r0+r'), v') (LMap.zmap_bindings imap2) in
             let zmap,rest = List.fold_left (fun (zmap,rest) (r',v') ->
                 let rest = match LMap.zmap_find_opt r' zmap with
                   | None -> rest
                   | Some v'' -> (v', v'', Z.zero)::rest
                 in LMap.zmap_add r' v' zmap, rest)
                 (imap1,rest) infl2 in
             LMap.remove v2 (LMap.add v zmap map), rest
           | Some imap1, Some imap2, false -> (* v2 is new root *)
             let r0 = Z.(r1-r2-r) in
             let infl1 = List.map (fun (r',v') -> Z.(-r0+r'),v') (LMap.zmap_bindings imap1) in
             let zmap,rest = List.fold_left (fun (zmap,rest) (r',v') ->
                 let rest =
                   match LMap.zmap_find_opt r' zmap with
                   | None -> rest
                   | Some v'' -> (v', v'',Z.zero)::rest
                 in LMap.zmap_add r' v' zmap, rest) (imap2, rest) infl1 in
             LMap.remove v1 (LMap.add v zmap map), rest
         in
         (* update min_repr *)
         let min_v1, min_v2 = MRMap.find v1 min_repr, MRMap.find v2 min_repr in
         (* 'changed' is true if the new_min is different than the old min *)
         let new_min, changed = if T.compare (fst min_v1) (fst min_v2) < 0 then (min_v1, not b) else (min_v2, b) in
         let new_min = (fst new_min, if b then Z.(snd new_min - diff_r) else Z.(snd new_min + diff_r)) in
         let removed_v = if b then v2 else v1 in
         let min_repr = MRMap.remove removed_v (if changed then MRMap.add v new_min min_repr else min_repr) in
         let queue = v :: queue in
         closure (uf, map, min_repr, new_repr) queue rest
      )

  let update_bldis new_repr bldis =
    (* update block disequalities with the new representatives *)
    let find_new_root t1 = match TMap.find_opt t1 new_repr with
      | None -> t1
      | Some v -> v
    in
    let disequalities = BlDis.to_conj bldis
    in (*TODO maybe optimize?, and maybe use this also for removing terms *)
    let add_bl_dis new_diseq = function
      | BlNequal (t1,t2) ->BlDis.add_block_diseq new_diseq (find_new_root t1,find_new_root t2)
      | _-> new_diseq
    in
    List.fold add_bl_dis BlDis.empty disequalities

  let rec add_normalized_bl_diseqs cc = function
    | [] -> cc
    | (t1,t2)::bl_conjs ->
      match cc with
      | None -> None
      | Some cc ->
        let t1' = fst (TUF.find_no_pc cc.uf t1) in
        let t2' = fst (TUF.find_no_pc cc.uf t2) in
        if T.equal t1' t2' then None (*unsatisfiable*)
        else let bldis = BlDis.add_block_diseq cc.bldis (t1',t2') in
          add_normalized_bl_diseqs (Some {cc with bldis}) bl_conjs

  (**
     Parameters: cc conjunctions.

     returns updated cc, where:

     - `uf` is the new union find data structure after having added all equalities.

     - `set` doesn't change

     - `map` maps reference variables v to a map that maps integers z to terms that are equivalent to *(v + z).

     - `min_repr` maps each equivalence class to its minimal representative.

      Throws "Unsat" if a contradiction is found.
  *)
  let closure cc conjs =
    match cc with
    | None -> None
    | Some cc ->
      let (uf, map, queue, min_repr, new_repr) = closure (cc.uf, cc.map, cc.min_repr, TMap.empty) [] conjs in
      let bldis = update_bldis new_repr cc.bldis in
      (* let min_repr, uf = MRMap.update_min_repr (uf, cc.set, map) min_repr queue in *)
      let min_repr, uf = MRMap.compute_minimal_representatives (uf, cc.set, map) in
      if M.tracing then M.trace "wrpointer" "closure minrepr: %s\n" (MRMap.show_min_rep min_repr);
      congruence_neq {uf; set = cc.set; map; min_repr; diseq=cc.diseq; bldis=bldis} []

  (** Throws Unsat if the congruence is unsatisfiable.*)
  let init_congruence conj =
    let cc = init_cc conj in
    (* propagating equalities through derefs *)
    closure (Some cc) conj

  (** Returns None if the congruence is unsatisfiable.*)
  let init_congruence_opt conj =
    let cc = init_cc conj in
    (* propagating equalities through derefs *)
    match closure (Some cc) conj with
    | exception Unsat -> None
    | x -> Some x

  (** Add a term to the data structure.

      Returns (reference variable, offset), updated (uf, set, map, min_repr),
      and queue, that needs to be passed as a parameter to `update_min_repr`.

      `queue` is a list which contains all atoms that are present as subterms of t and that are not already present in the data structure. *)
  let rec insert_no_min_repr cc t =
    if SSet.mem t cc.set then
      let v,z,uf = TUF.find cc.uf t in
      (v,z), Some {cc with uf}, []
    else
      match t with
      | Addr _ | Aux _ -> let uf = TUF.ValMap.add t ((t, Z.zero),1) cc.uf in
        let min_repr = MRMap.add t (t, Z.zero) cc.min_repr in
        let set = SSet.add t cc.set in
        (t, Z.zero), Some {cc with uf; set; min_repr;}, [t]
      | Deref (t', z, exp) ->
        match insert_no_min_repr cc t' with
        | (v, r), None, queue -> (v, r), None, []
        | (v, r), Some cc, queue ->
          let min_repr = MRMap.add t (t, Z.zero) cc.min_repr in
          let set = SSet.add t cc.set in
          match LMap.map_find_opt (v, Z.(r + z)) cc.map with
          | Some v' -> let v2,z2,uf = TUF.find cc.uf v' in
            let uf = LMap.add t ((t, Z.zero),1) uf in
            (v2,z2), closure (Some {uf; set; map = LMap.map_add (v, Z.(r + z)) t cc.map; min_repr; diseq = cc.diseq; bldis=cc.bldis}) [(t, v', Z.zero)], v::queue
          | None -> let map = LMap.map_add (v, Z.(r + z)) t cc.map in
            let uf = LMap.add t ((t, Z.zero),1) cc.uf in
            (t, Z.zero), Some {uf; set; map; min_repr; diseq = cc.diseq; bldis=cc.bldis}, v::queue

  (** Add a term to the data structure.

        Returns (reference variable, offset), updated (uf, set, map, min_repr) *)
  let insert cc t =
    match cc with
    | None -> (t, Z.zero), None
    | Some cc ->
      match insert_no_min_repr cc t with
      | v, None, queue -> v, None
      | v, Some cc, queue ->
        let min_repr, uf = MRMap.update_min_repr (cc.uf, cc.set, cc.map) cc.min_repr queue in
        v, Some {uf; set = cc.set; map = cc.map; min_repr; diseq = cc.diseq; bldis=cc.bldis}

  (** Add all terms in a specific set to the data structure.

      Returns updated (uf, set, map, min_repr). *)
  let insert_set cc t_set =
    match SSet.fold (fun t (cc, a_queue) -> let _, cc, queue = Option.map_default (fun cc -> insert_no_min_repr cc t) ((t, Z.zero), None, []) cc in (cc, queue @ a_queue) ) t_set (cc, []) with
    | None, queue -> None
    | Some cc, queue ->
      (* update min_repr at the end for more efficiency *)
      let min_repr, uf = MRMap.update_min_repr (cc.uf, cc.set, cc.map) cc.min_repr queue in
      Some {uf; set = cc.set; map = cc.map; min_repr; diseq = cc.diseq; bldis=cc.bldis}

  (**  Returns true if t1 and t2 are equivalent. *)
  let rec eq_query cc (t1,t2,r) =
    let (v1,r1),cc = insert cc t1 in
    let (v2,r2),cc = insert cc t2 in
    if T.equal v1 v2 && Z.equal r1 Z.(r2 + r) then (true, cc)
    else
      (* If the equality is *(t1' + z1) = *(t2' + z2), then we check if the two pointers are equal,
         i.e. if t1' + z1 = t2' + z2.
          This is useful when the dereferenced elements are not pointers. *)
    if Z.equal r Z.zero then
      match t1,t2 with
      | Deref (t1', z1, _),  Deref (t2', z2, _) ->
        eq_query cc (t1', t2', Z.(z2 - z1))
      | _ -> (false, cc)
    else (false,cc)

  let eq_query_opt cc (t1,t2,r) =
    match cc with
    | None -> false
    | Some cc -> fst (eq_query cc (t1,t2,r))

  (*TODO there could be less code duplication *)
  let block_neq_query cc (t1,t2) =
    (* we implicitly assume that &x != &y + z *)
    if T.is_addr t1 && T.is_addr t2 then true else
      let (v1,r1),cc = insert cc t1 in
      let (v2,r2),cc = insert cc t2 in
      match cc with
      | None -> true
      | Some cc -> BlDis.map_set_mem t1 t2 cc.bldis

  (** Returns true if t1 and t2 are not equivalent. *)
  let neq_query cc (t1,t2,r) =
    (* we implicitly assume that &x != &y + z *)
    if T.is_addr t1 && T.is_addr t2 then true else
      let (v1,r1),cc = insert cc t1 in
      let (v2,r2),cc = insert cc t2 in
      (* implicit disequalities following from equalities *)
      if T.equal v1 v2 then
        if Z.(equal r1 (r2 + r)) then false
        else true
      else
        match cc with
        | None -> true
        | Some cc -> (* implicit disequalities following from block disequalities *)
          BlDis.map_set_mem t1 t2 cc.bldis ||
          (*explicit dsequalities*)
          Disequalities.map_set_mem (v2,Z.(r2-r1+r)) v1 cc.diseq

  (** Adds equalities to the data structure.
      Throws "Unsat" if a contradiction is found. *)
  let meet_conjs cc pos_conjs =
    let res = let cc = insert_set cc (fst (SSet.subterms_of_conj pos_conjs)) in
      closure cc pos_conjs
    in if M.tracing then M.trace "wrpointer-meet" "MEET_CONJS RESULT: %s\n" (Option.map_default (fun res -> show_conj (get_normal_form res)) "None" res);res

  let meet_conjs_opt conjs cc =
    let pos_conjs, neg_conjs, bl_conjs = split conjs in
    let terms_to_add = (fst (SSet.subterms_of_conj (neg_conjs @ List.map(fun (t1,t2)->(t1,t2,Z.zero)) bl_conjs))) in
    match insert_set (meet_conjs cc pos_conjs) terms_to_add with
    | exception Unsat -> None
    | Some cc -> let cc = congruence_neq cc neg_conjs in
      add_normalized_bl_diseqs cc bl_conjs
    | None -> None

  (** Add proposition t1 = t2 + r to the data structure. *)
  let add_eq cc (t1, t2, r) =
    let (v1, r1), cc = insert cc t1 in
    let (v2, r2), cc = insert cc t2 in
    let cc = closure cc [v1, v2, Z.(r2 - r1 + r)] in
    cc

  (** adds block disequalities to cc:
      fo each representative t in cc it adds the disequality bl(lterm)!=bl(t)*)
  let add_block_diseqs cc lterm =
    match cc with
    | None -> cc
    | Some cc ->
      let bldis = BlDis.add_block_diseqs cc.bldis cc.uf lterm (TUF.get_representatives cc.uf) in
      Some {cc with bldis}

  (* Remove variables: *)

  let add_to_map_of_children value map term =
    if T.equal term value then map else
      match TMap.find_opt term map with
      | None -> TMap.add term [value] map
      | Some list -> TMap.add term (value::list) map

  let remove_from_map_of_children parent child map =
    match List.remove_if (T.equal child) (TMap.find parent map) with
    | [] -> TMap.remove parent map
    | new_children -> TMap.add parent new_children map

  (* Returns true if any (strict) subterm of t1 is already present in
     the same equivalence class as t2. *)
  let rec detect_cyclic_dependencies t1 t2 cc =
    match t1 with
    | Addr _ | Aux _ -> false
    | Deref (t1, _, _) ->
      let v1, o1 = TUF.find_no_pc cc.uf t1 in
      let v2, o2 = TUF.find_no_pc cc.uf t2 in
      if T.equal v1 v2 then true else
        detect_cyclic_dependencies t1 t2 cc

  let add_successor_terms cc t =
    let add_one_successor (cc, successors) (edge_z, _) =
      let _, uf_offset, uf = TUF.find cc.uf t in
      let cc = {cc with uf = uf} in
      match SSet.deref_term t Z.(edge_z - uf_offset) cc.set with
      | exception (T.UnsupportedCilExpression _) ->
        (cc, successors)
      | successor ->
        let subterm_already_present = SSet.mem successor cc.set || detect_cyclic_dependencies t t cc in
        let _, cc, _ = if subterm_already_present then (t, Z.zero), cc, []
          else (if M.tracing then M.trace "wrpointer" "insert successor: %s. Map: %s\n" (T.show successor) (LMap.show_map cc.map); Tuple3.map2 Option.get (insert_no_min_repr cc successor)) in
        (cc, if subterm_already_present then successors else successor::successors) in
    List.fold_left add_one_successor (cc, []) (LMap.successors (Tuple3.first (TUF.find cc.uf t)) cc.map)

  (** Parameters:
      - `cc`: congruence closure data structure
      - `predicate`: predicate that returns true for terms which need to be removed from the data structure.
        It takes `uf` as a parameter.
        Returns:
      - `new_set`: subset of `set` which contains the terms that do not have to be removed.
      - `removed_terms`: list of all elements of `set` which contains the terms that have to be removed.
      - `map_of_children`: maps each element of union find to its children in the union find tree. It is used in order to later remove these elements from the union find data structure.
      - `cc`: updated congruence closure data structure.
  *)
  let remove_terms_from_set cc predicate =
    let rec remove_terms_recursive (new_set, removed_terms, map_of_children, cc) = function
      | [] -> (new_set, removed_terms, map_of_children, cc)
      | el::rest ->
        let new_set, removed_terms = if predicate cc.uf el then new_set, el::removed_terms else SSet.add el new_set, removed_terms in
        let uf_parent = TUF.parent cc.uf el in
        let map_of_children = add_to_map_of_children el map_of_children (fst uf_parent) in
        (* in order to not lose information by removing some elements, we add dereferences values to the union find.*)
        let cc, successors = add_successor_terms cc el in
        remove_terms_recursive (new_set, removed_terms, map_of_children, cc) (rest @ successors)
    in
    remove_terms_recursive (SSet.empty, [], TMap.empty, cc) (SSet.to_list cc.set)

  let show_map_of_children map_of_children =
    List.fold_left
      (fun s (v, list) ->
         s ^ T.show v ^ "\t:\n" ^
         List.fold_left
           (fun s v ->
              s ^ T.show v ^ "; ")
           "\t" list ^ "\n")
      "" (TMap.bindings map_of_children)

  (** Removes all terms in "removed_terms" from the union find data structure.
      Returns:
      - `uf`: the updated union find tree
      - `new_parents_map`: maps each removed term t to another term which was in the same equivalence class as t at the time when t was deleted.
  *)
  let remove_terms_from_uf uf removed_terms map_of_children predicate =
    let find_not_removed_element set = match List.find (fun el -> not (predicate uf el)) set with
      | exception Not_found -> List.first set
      | t -> t
    in
    let remove_term (uf, new_parents_map, map_of_children) t =
      match LMap.find_opt t map_of_children with
      | None ->
        (* t has no children, so we can safely delete the element from the data structure *)
        (* we just need to update the size on the whole path from here to the root *)
        let new_parents_map = if TUF.is_root uf t then new_parents_map else LMap.add t (TUF.parent uf t) new_parents_map in
        let parent = fst (TUF.parent uf t) in
        let map_of_children = if TUF.is_root uf t then map_of_children else remove_from_map_of_children parent t map_of_children in
        (TUF.ValMap.remove t (TUF.modify_size t uf pred), new_parents_map, map_of_children)
      | Some children ->
        let map_of_children = LMap.remove t map_of_children in
        if TUF.is_root uf t then
          (* t is a root and it has some children:
             1. choose new root.
             The new_root is in any case one of the children of the old root.
             If possible, we choose one of the children that is not going to be deleted.  *)
          let new_root = find_not_removed_element children in
          let remaining_children = List.remove_if (T.equal new_root) children in
          let offset_new_root = TUF.parent_offset uf new_root in
          (* We set the parent of all the other children to the new root and adjust the offset accodingly. *)
          let new_size, map_of_children, uf = List.fold
              (fun (total_size, map_of_children, uf) child ->
                 (* update parent and offset *)
                 let uf = TUF.modify_parent uf child (new_root, Z.(TUF.parent_offset uf child - offset_new_root)) in
                 total_size + TUF.subtree_size uf child, add_to_map_of_children child map_of_children new_root, uf
              ) (0, map_of_children, uf) remaining_children in
          (* Update new root -> set itself as new parent. *)
          let uf = TUF.modify_parent uf new_root (new_root, Z.zero) in
          (* update size of equivalence class *)
          let uf = TUF.modify_size new_root uf ((+) new_size) in
          (TUF.ValMap.remove t uf, LMap.add t (new_root, Z.(-offset_new_root)) new_parents_map, map_of_children)
        else
          (* t is NOT a root -> the old parent of t becomes the new parent of the children of t. *)
          let (new_root, new_offset) = TUF.parent uf t in
          let remaining_children = List.remove_if (T.equal new_root) children in
          (* update all parents of the children of t *)
          let map_of_children, uf = List.fold
              (fun (map_of_children, uf) child ->
                 (* update parent and offset *)
                 add_to_map_of_children child map_of_children new_root,
                 TUF.modify_parent uf child (new_root, Z.(TUF.parent_offset uf t + new_offset))
              ) (map_of_children, uf) remaining_children in
          (* update size of equivalence class *)
          let uf = TUF.modify_size new_root uf pred in
          (TUF.ValMap.remove t uf, LMap.add t (new_root, new_offset) new_parents_map, map_of_children)
    in
    List.fold_left remove_term (uf, LMap.empty, map_of_children) removed_terms

  let show_new_parents_map new_parents_map = List.fold_left
      (fun s (v1, (v2, o2)) ->
         s ^ T.show v1 ^ "\t: " ^ T.show v2 ^ ", " ^ Z.to_string o2 ^"\n")
      "" (TMap.bindings new_parents_map)

  (** Find the representative term of the equivalence classes of an element that has already been deleted from the data structure.
      Returns None if there are no elements in the same equivalence class as t before it was deleted.*)
  let rec find_new_root new_parents_map uf v =
    match LMap.find_opt v new_parents_map with
    | None -> TUF.find_opt uf v
    | Some (new_parent, new_offset) ->
      match find_new_root new_parents_map uf new_parent with
      | None -> None
      | Some (r, o, uf) -> Some (r, Z.(o + new_offset), uf)

  (** Removes all terms from the mapped values of this map,
      for which "predicate" is false. *)
  let remove_terms_from_mapped_values map predicate =
    LMap.filter_if map (not % predicate)

  (** For all the elements in the removed terms set, it moves the mapped value to the new root.
      Returns new map and new union-find. *)
  let remove_terms_from_map (uf, map) removed_terms new_parents_map =
    let remove_from_map (map, uf) term =
      match LMap.find_opt term map with
      | None -> map, uf
      | Some _ -> (* move this entry in the map to the new representative of the equivalence class where term was before. If it still exists. *)
        match find_new_root new_parents_map uf term with
        | None -> LMap.remove term map, uf
        | Some (new_root, new_offset, uf) -> LMap.shift new_root new_offset term map, uf
    in List.fold_left remove_from_map (map, uf) removed_terms

  let remove_terms_from_diseq (diseq: Disequalities.t) removed_terms predicate new_parents_map uf =
    (* modify mapped values
       -> change terms to their new representatives or remove them, if the representative class was completely removed. *)
    let diseq = Disequalities.filter_map (Option.map Tuple3.first % find_new_root new_parents_map uf) (Disequalities.filter_if diseq (not % predicate))  in
    (* modify left hand side of map *)
    let res, uf = remove_terms_from_map (uf, diseq) removed_terms new_parents_map in
    if M.tracing then M.trace "wrpointer-neq" "remove_terms_from_diseq: %s\nUnion find: %s\n" (Disequalities.show_neq res) (TUF.show_uf uf); res, uf

  (** Remove terms from the data structure.
      It removes all terms for which "predicate" is false,
      while maintaining all equalities about variables that are not being removed.*)
  let remove_terms predicate cc =
    let old_cc = cc in
    (* first find all terms that need to be removed *)
    let set, removed_terms, map_of_children, cc =
      remove_terms_from_set cc predicate
    in if M.tracing then M.trace "wrpointer" "REMOVE TERMS: %s\n BEFORE: %s\n" (List.fold_left (fun s t -> s ^ "; " ^ T.show t) "" removed_terms)
        (show_all old_cc);
    let uf, new_parents_map, _ =
      remove_terms_from_uf cc.uf removed_terms map_of_children predicate
    in let map =
         remove_terms_from_mapped_values cc.map (predicate cc.uf)
    in let map, uf =
         remove_terms_from_map (uf, map) removed_terms new_parents_map
    in let diseq, uf =
         remove_terms_from_diseq cc.diseq removed_terms (predicate cc.uf) new_parents_map uf
    in let min_repr, uf = MRMap.compute_minimal_representatives (uf, set, map)
    in if M.tracing then M.trace "wrpointer" "REMOVE TERMS: %s\n BEFORE: %s\nRESULT: %s\n" (List.fold_left (fun s t -> s ^ "; " ^ T.show t) "" removed_terms)
        (show_all old_cc) (show_all {uf; set; map; min_repr; diseq; bldis});
    {uf; set; map; min_repr; diseq; bldis}

  (* join *)

  let show_pmap pmap=
    List.fold_left (fun s ((r1,r2,z1),(t,z2)) ->
        s ^ ";; " ^ "("^T.show r1^","^T.show r2 ^ ","^Z.to_string z1^") --> ("^ T.show t ^ Z.to_string z2 ^ ")") ""(Map.bindings pmap)

  let join_eq cc1 cc2 =
    let atoms = SSet.get_atoms (SSet.inter cc1.set cc2.set) in
    let mappings = List.map
        (fun a -> let r1, off1 = TUF.find_no_pc cc1.uf a in
          let r2, off2 = TUF.find_no_pc cc2.uf a in
          (r1,r2,Z.(off2 - off1)), (a,off1)) atoms in
    let add_term (pmap, cc, new_pairs) (new_element, (new_term, a_off)) =
      match Map.find_opt new_element pmap with
      | None -> Map.add new_element (new_term, a_off) pmap, cc, new_element::new_pairs
      | Some (c, c1_off) ->
        pmap, add_eq cc (new_term, c, Z.(-c1_off + a_off)),new_pairs in
    let pmap,cc,working_set = List.fold_left add_term (Map.empty, Some (init_cc []),[]) mappings in
    (* add equalities that make sure that all atoms that have the same
       representative are equal. *)
    let add_one_edge y t t1_off diff (pmap, cc, new_pairs) (offset, a) =
      let a', a_off = TUF.find_no_pc cc1.uf a in
      match LMap.map_find_opt (y, Z.(diff + offset)) cc2.map with
      | None -> pmap,cc,new_pairs
      | Some b -> let b', b_off = TUF.find_no_pc cc2.uf b in
        match SSet.deref_term t Z.(offset - t1_off) cc1.set with
        | exception (T.UnsupportedCilExpression _) -> pmap,cc,new_pairs
        | new_term ->
          let _ , cc = insert cc new_term in
          let new_element = a',b',Z.(b_off - a_off) in
          add_term (pmap, cc, new_pairs) (new_element, (new_term, a_off))
    in
    let rec add_edges_to_map pmap cc = function
      | [] -> cc, pmap
      | (x,y,diff)::rest ->
        let t,t1_off = Map.find (x,y,diff) pmap in
        let pmap,cc,new_pairs = List.fold_left (add_one_edge y t t1_off diff) (pmap, cc, []) (LMap.successors x cc1.map) in
        add_edges_to_map pmap cc (rest@new_pairs)
    in
    add_edges_to_map pmap cc working_set

  (** Joins the disequalities diseq1 and diseq2, given a congruence closure data structure. *)
  let join_neq diseq1 diseq2 cc1 cc2 cc cmap1 cmap2 =
    let _,diseq1,_ = split (Disequalities.get_disequalities diseq1) in
    let _,diseq2,_ = split (Disequalities.get_disequalities diseq2) in
    (* keep all disequalities from diseq1 that are implied by cc2 and
       those from diseq2 that are implied by cc1 *)
    let diseq1 = List.filter (neq_query (Some cc2)) (Disequalities.element_closure diseq1 cmap1) in
    let diseq2 = List.filter (neq_query (Some cc1)) (Disequalities.element_closure diseq2 cmap2) in
    let cc = Option.get (insert_set cc (fst @@ SSet.subterms_of_conj (diseq1 @ diseq2))) in
    let res = congruence_neq cc (diseq1 @ diseq2)
    in (if M.tracing then match res with | Some r -> M.trace "wrpointer-neq" "join_neq: %s\n\n" (Disequalities.show_neq r.diseq) | None -> ()); res

  (** Joins the block disequalities bldiseq1 and bldiseq2, given a congruence closure data structure. *)
  let join_bldis bldiseq1 bldiseq2 cc1 cc2 cc cmap1 cmap2 =
    let bldiseq1 = BlDis.to_conj bldiseq1 in
    let bldiseq2 = BlDis.to_conj bldiseq2 in
    (* keep all disequalities from diseq1 that are implied by cc2 and
       those from diseq2 that are implied by cc1 *)
    let diseq1 = List.filter (block_neq_query (Some cc2)) (BlDis.element_closure bldiseq1 cmap1) in
    let diseq2 = List.filter (block_neq_query (Some cc1)) (BlDis.element_closure bldiseq2 cmap2) in
    let cc = Option.get (insert_set cc (fst @@ SSet.subterms_of_conj (List.map (fun (a,b) -> (a,b,Z.zero)) (diseq1 @ diseq2)))) in
    let diseqs_ref_terms = List.filter (fun (t1,t2) -> TUF.is_root cc.uf t1 && TUF.is_root cc.uf t2) (diseq1 @ diseq2) in
    let bldis = List.fold BlDis.add_block_diseq BlDis.empty diseqs_ref_terms
    in (if M.tracing then M.trace "wrpointer-neq" "join_bldis: %s\n\n" (show_conj (BlDis.to_conj bldis)));
    {cc with bldis}

end
