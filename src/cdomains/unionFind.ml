(**
   The Union Find is used by the C-2PO Analysis.
   This file contains the code for a quantitative union find and the quantitative finite automata.
   They will be necessary in order to construct the congruence closure of terms.
*)
open Batteries
open GoblintCil
open DuplicateVars
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
  type t = (Var.t, exp[@compare.ignore][@eq.ignore][@hash.ignore]) term [@@deriving eq, ord, hash]
  type v_prop = (Var.t, exp[@hash.ignore]) prop [@@deriving hash]

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
    | _ -> match Z.of_int (bitsSizeOf typ) with
      | exception GoblintCil__Cil.SizeOfError (msg,_) when msg ="abstract type"-> Z.one
      | exception GoblintCil__Cil.SizeOfError (msg,_) ->
        raise (UnsupportedCilExpression msg)
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

  (** Use query EvalInt for an expression. *)
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

  (** Returns Some type for a pointer to a type
      and None if the result is not a pointer. *)
  let rec type_of_element typ =
    match typ with
    | TNamed (typinfo, _) -> type_of_element typinfo.ttype
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

  let rec is_float = function
    | TNamed (typinfo, _) -> is_float typinfo.ttype
    | TFloat _ -> true
    | _ -> false

  let aux_term_of_varinfo vinfo =
    Aux (vinfo, Lval (Var (Var.to_varinfo vinfo), NoOffset))

  let term_of_varinfo vinfo =
    if is_struct_type (Var.to_varinfo vinfo).vtype || (Var.to_varinfo vinfo).vaddrof then
      Deref (Addr vinfo, Z.zero, Lval (Var (Var.to_varinfo vinfo), NoOffset))
    else
      aux_term_of_varinfo vinfo

  (** Convert a Cil offset to an integer offset.
      Copied from memOutOfBounds.ml. *)
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

  (** Convert an offset to an integer of Z, if posible.
      Otherwise, this throws UnsupportedCilExpression. *)
  let z_of_offset ask offs typ =
    match IntDomain.IntDomTuple.to_int @@ cil_offs_to_idx ask offs typ with
    | Some i -> i
    | None
    | exception (SizeOfError _) -> if M.tracing then M.trace "c2po-invalidate" "REASON: unknown offset";
      raise (UnsupportedCilExpression "unknown offset")

  let rec can_be_dereferenced = function
    | TNamed (typinfo, _) -> can_be_dereferenced typinfo.ttype
    | TPtr _| TArray _| TComp _ -> true
    | _ -> false

  let type_of_term =
    function
    | Addr v -> TPtr ((Var.to_varinfo v).vtype, [])
    | Aux (_, exp) | Deref (_, _, exp) -> typeOf exp

  let to_cil =
    function
    | (Addr v) -> AddrOf (Var (Var.to_varinfo v), NoOffset)
    | Aux (_, exp) | (Deref (_, _, exp)) -> exp

  let default_int_type = ILong
  (** Returns a Cil expression which is the constant z divided by the size of the elements of t.*)
  let to_cil_constant z t =
    let z = if Z.equal z Z.zero then Z.zero else
        let typ_size = match t with
          | Some t -> get_element_size_in_bits t
          | None -> Z.one
        in
        if Z.lt (Z.abs z) typ_size && Z.gt (Z.abs z) Z.zero then raise (UnsupportedCilExpression "Cil can't represent something like &(c->d).") else
        if Z.equal typ_size Z.zero then Z.zero else
          Z.(z /typ_size) in
    Const (CInt (z, default_int_type, Some (Z.to_string z)))

  let to_cil_sum off cil_t =
    let res =
      if Z.(equal zero off) then cil_t else
        let typ = typeOf cil_t in
        BinOp (PlusPI, cil_t, to_cil_constant off (Some typ), typ)
    in if M.tracing then M.trace "c2po-2cil" "exp: %a; offset: %s; res: %a" d_exp cil_t (Z.to_string off) d_exp res;res

  (** Returns the integer offset of a field of a struct. *)
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

  (** Returns true if the Cil expression represents a 64 bit data type,
      which is not a float. So it must be either a pointer or an integer
      that has the same size as a pointer.*)
  let check_valid_pointer term =
    match typeOf term with (* we want to make sure that the expression is valid *)
    | exception GoblintCil__Errormsg.Error -> false
    | typ -> (* we only track equalties between pointers (variable of size 64)*)
      if get_size_in_bits typ <> bitsSizeOfPtr () || is_float typ then false
      else true

  (** Only keeps the variables that are actually pointers (or 64-bit integers). *)
  let filter_valid_pointers =
    List.filter (function | Equal(t1,t2,_)| Nequal(t1,t2,_) |BlNequal(t1,t2)-> check_valid_pointer (to_cil t1) && check_valid_pointer (to_cil t2))

  (** Get a Cil expression that is equivalent to *(exp + offset),
      by taking into account type correctness.*)
  let dereference_exp exp offset =
    if M.tracing then M.trace "c2po-deref" "exp: %a, offset: %s" d_exp exp (Z.to_string offset);
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
    in if M.tracing then M.trace "c2po-deref" "deref result: %a" d_exp res;res

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
    | AddrOf (Var var, NoOffset) -> Some (Addr (Var.NormalVar var)), Z.zero
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
      | (Var var, off) -> if is_struct_type var.vtype then of_offset ask (Addr (Var.NormalVar var)) off var.vtype (Lval lval)
        else
          of_offset ask (term_of_varinfo (Var.NormalVar var)) off var.vtype (Lval lval)
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
        | exception (UnsupportedCilExpression s) -> M.trace "c2po-cil-conversion" "unsupported exp: %a\n%s\n" d_plainlval lval s
        | t -> M.trace "c2po-cil-conversion" "lval: %a --> %s\n" d_plainlval lval (show t))
  ;res

  let rec of_cil_neg ask neg e = match e with
    | UnOp (op,exp,typ)->
      begin match op with
        | Neg -> of_cil_neg ask (not neg) exp
        | _ -> if neg then raise (UnsupportedCilExpression "unsupported UnOp Neg") else of_cil ask e
      end
    | _ -> if neg then raise (UnsupportedCilExpression "unsupported UnOp Neg") else of_cil ask e

  (** Converts the negated expression to a term if neg = true.
      If neg = false then it simply converts the expression to a term. *)
  let of_cil_neg ask neg e =
    match is_float (typeOf e) with
    | exception GoblintCil__Errormsg.Error | true -> None, None
    | false ->
      let res = match of_cil_neg ask neg (Cil.constFold false e) with
        | exception (UnsupportedCilExpression s) -> if M.tracing then M.trace "c2po-cil-conversion" "unsupported exp: %a\n%s\n" d_plainexp e s;
          None, None
        | t, z -> t, Some z
      in (if M.tracing && not neg then match res with
          | None, Some z ->  M.trace "c2po-cil-conversion" "constant exp: %a --> %s\n" d_plainexp e (Z.to_string z)
          | Some t, Some z -> M.trace "c2po-cil-conversion" "exp: %a --> %s + %s\n" d_plainexp e (show t) (Z.to_string z);
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
      else (if M.tracing then M.trace "c2po-cil-conversion" "invalid exp: %a --> %s + %s\n" d_plainexp e (show t) (Z.to_string z);
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
        the expression can't be expressed with the type `prop`. *)
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

  let prop_to_cil p =
    let op,t1,t2,z = match p with
      | Equal (t1,t2,z) -> Eq, t1, t2, z
      | Nequal (t1,t2,z) -> Ne, t1, t2, z
      | BlNequal (t1,t2) -> Ne, t1, t2, Z.zero
    in
    BinOp (op, to_cil t1, to_cil_sum z (to_cil t2), TInt (IBool,[]))

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
  let is_root uf v =
    match parent_opt uf v with
    | None -> true
    | Some (parent_t, _) -> T.equal v parent_t

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
      (if M.tracing then M.trace "c2po-find" "find DEEP TREE";
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
       in search v' [v])

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

  (** Returns a list of representative elements.*)
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

  (** Find all elements that are in the same equivalence class as t,
      given the cmap. *)
  let comp_t_cmap_repr cmap t =
    match TMap.find_opt t cmap with
    | None -> [Z.zero, t]
    | Some zmap ->
      List.concat_map
        (fun (z, set) ->
           List.cartesian_product [z] (TSet.to_list set)) (ZMap.bindings zmap)
end
