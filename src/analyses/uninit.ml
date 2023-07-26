(** Analysis of initialized local variables ([uninit]). *)

module M = Messages
module AD = ValueDomain.AD
module IdxDom = ValueDomain.IndexDomain
module Offs = ValueDomain.Offs

open GoblintCil
open Analyses

module Spec =
struct
  include Analyses.DefaultSpec

  module Addr = ValueDomain.Addr

  module D = ValueDomain.AddrSetDomain
  module C = ValueDomain.AddrSetDomain
  module P = IdentityP (D)

  type trans_in  = D.t
  type trans_out = D.t
  type transfer  = trans_in -> trans_out

  let name () = "uninit"

  let startstate v : D.t = D.empty ()
  let threadenter ctx lval f args = [D.empty ()]
  let threadspawn ctx lval f args fctx = ctx.local
  let exitstate  v : D.t = D.empty ()

  (* TODO: Use AddressDomain for queries *)
  let access_address (ask: Queries.ask) write lv =
    match ask.f (Queries.MayPointTo (AddrOf lv)) with
    | a when not (Queries.LS.is_top a) ->
      let to_extra (v,o) xs = (v, Addr.Offs.of_exp o, write) :: xs  in
      Queries.LS.fold to_extra a []
    | _ ->
      M.info ~category:Unsound "Access to unknown address could be global"; []

  let rec access_one_byval a rw (exp:exp) =
    match exp with
    | Const _
    | SizeOf _
    | SizeOfStr _
    | AlignOf _
    | AddrOfLabel _ -> []
    (* Variables and address expressions *)
    | Lval lval -> access_address a rw lval @ (access_lv_byval a lval)
    (* Binary operators *)
    | BinOp (op,arg1,arg2,typ) ->
      let a1 = access_one_byval a rw arg1 in
      let a2 = access_one_byval a rw arg2 in
      a1 @ a2
    | UnOp (_,e,_)
    | Real e
    | Imag e
    | SizeOfE e
    | AlignOfE e ->
      access_one_byval a rw e
    (* The address operators, we just check the accesses under them *)
    | AddrOf lval -> access_lv_byval a lval
    | StartOf lval -> access_lv_byval a lval
    (* Most casts are currently just ignored, that's probably not a good idea! *)
    | CastE  (t, exp) -> access_one_byval a rw exp
    | Question (b, t, f, _) ->
      access_one_byval a rw b @ access_one_byval a rw t @ access_one_byval a rw f
  (* Accesses during the evaluation of an lval, not the lval itself! *)
  and access_lv_byval a (lval:lval) =
    let rec access_offset (ofs: offset) =
      match ofs with
      | NoOffset -> []
      | Field (fld, ofs) -> access_offset ofs
      | Index (exp, ofs) -> access_one_byval a false exp @ access_offset ofs
    in
    match lval with
    | Var x, ofs -> access_offset ofs
    | Mem n, ofs -> access_one_byval a false n @ access_offset ofs

  (* list accessed addresses *)
  let varoffs a (rval:exp) =
    let f vs (v,o,_) = (v,o) :: vs in
    List.fold_left f [] (access_one_byval a false rval)

  let is_prefix_of m1 m2 = Option.is_some (Addr.Mval.prefix m1 m2)

  (* Does it contain non-initialized variables? *)
  let is_expr_initd a (expr:exp) (st:D.t) : bool =
    let mvals = varoffs a expr in
    let will_mval_init (t:bool) mval =
      let f addr =
        GobOption.exists (is_prefix_of mval) (Addr.to_mval addr)
      in
      if D.exists f st then (
        M.error ~category:M.Category.Behavior.Undefined.uninitialized ~tags:[CWE 457] "Uninitialized variable %a accessed." Addr.Mval.pretty mval;
        false
      )
      else
        t
    in
    List.fold_left will_mval_init true mvals

  let remove_if_prefix (pr: Addr.Mval.t) (uis: D.t) : D.t =
    let f ad =
      let vals = Addr.to_mval ad in
      GobOption.for_all (fun a -> not (is_prefix_of pr a)) vals
    in
    D.filter f uis

  type lval_offs = Addr.Offs.t
  type var_offs  = Addr.Mval.t

  (* Call to [get_pfx v cx] returns initialized prefixes ... *)
  let rec get_pfx (v:varinfo) (cx:lval_offs) (ofs:lval_offs) (target:typ) (other:typ) : var_offs list =
    let rec rev lo =
      match lo with
      | `NoOffset -> `NoOffset
      | `Field (f, o) -> Addr.Offs.add_offset (rev o) (`Field (f, `NoOffset))
      | `Index (v, o) -> Addr.Offs.add_offset (rev o) (`Index (v, `NoOffset))
    in
    let rec bothstruct (t:fieldinfo list) (tf:fieldinfo) (o:fieldinfo list) (no:lval_offs)  : var_offs list =
      match t, o with
      | x::xs, y::ys when CilType.Fieldinfo.equal x tf ->
        get_pfx v (`Field (y, cx)) no x.ftype y.ftype
      | x::xs, y::ys when CilType.Typ.equal x.ftype y.ftype -> (* different fields, same type? *)
        bothstruct xs tf ys no
      | x::xs, y::ys ->
        [] (* found a mismatch *)
      | _ ->
        M.info ~category:Unsound "Failed to analyze union at point %a -- did not find %s" Addr.pretty (Addr.of_mval (v,rev cx)) tf.fname;
        []
    in
    let utar, uoth = unrollType target, unrollType other in
    match ofs, utar, uoth with
    |     `NoOffset,              _ ,               _ when utar == uoth  -> [v, rev cx]
    |     `NoOffset,              _ ,    TComp (c2,_) when not c2.cstruct ->
      (* unroll other (union) *)
      List.concat (List.rev_map (fun oth_f -> get_pfx v (`Field (oth_f, cx)) ofs utar oth_f.ftype) c2.cfields)
    |     `NoOffset,              _ ,               _ ->
      (* types not same and other is not a struct *)
      []
    | `Index (i, o), TArray (t1,_,_), TArray (t2,_,_) -> (* todo: other might be a union*)
      (* step into both indexed *)
      get_pfx v (`Index (i, cx)) o t1 t2
    | `Index (i, o),    _ ,    TComp (c2,_) when not c2.cstruct ->
      (* step into all other fields *)
      List.concat (List.rev_map (fun oth_f -> get_pfx v (`Field (oth_f, cx)) ofs utar oth_f.ftype) c2.cfields)
    | `Field (f, o),    TComp (c1,_),    TComp (c2,_) when c1.cstruct && c2.cstruct ->
      (* step into both, but check that types of prefixes match*)
      bothstruct c1.cfields f c2.cfields o
    | `Field (f, o),    TComp (c1,_),              _  when not c1.cstruct  ->
      (* step into target but not other (don't care about other) *)
      get_pfx v cx o f.ftype uoth
    | `Field (f, o),    TComp (c1,_),    TComp (c2,_) when c1.cstruct && not c2.cstruct ->
      (* step into all other fields *)
      List.concat (List.rev_map (fun oth_f -> get_pfx v (`Field (oth_f, cx)) ofs utar oth_f.ftype) c2.cfields)
    | _ ->
      M.info ~category:Unsound "Failed to analyze union at point %a" Addr.pretty (Addr.of_mval (v,rev cx));
      []


  (* Call to [init_lval lv st] results in state [st] where the variable evaluated form [lv] is initialized. *)
  let init_lval (a: Queries.ask) (lv: lval) (st: D.t) : D.t =
    let init_vo (v: varinfo) (ofs: lval_offs) : D.t =
      List.fold_right remove_if_prefix (get_pfx v `NoOffset ofs v.vtype v.vtype) st
    in
    match a.f (Queries.MayPointTo (AddrOf lv)) with
    | a when Queries.LS.cardinal a = 1 ->  begin
        let var, ofs = Queries.LS.choose a in
        init_vo var (Addr.Offs.of_exp ofs)
      end
    | _ -> st

  let to_addrs (v:varinfo) : Addr.t list =
    let make_offs = List.fold_left (fun o f -> `Field (f, o)) `NoOffset in
    let rec add_fields (base: fieldinfo list) fs acc =
      match fs with
      | [] -> acc
      | f :: fs ->
        match unrollType f.ftype with
        | TComp ({cfields=ffs; _},_) -> add_fields base fs (List.rev_append (add_fields (f::base) ffs []) acc)
        | _                       -> add_fields base fs ((Addr.of_mval (v,make_offs (f::base))) :: acc)

    in
    match unrollType v.vtype with
    | TComp ({cfields=fs; _},_) -> add_fields [] fs []
    | _ -> [Addr.of_var v]


  let remove_unreachable (ask: Queries.ask) (args: exp list) (st: D.t) : D.t =
    let reachable =
      let do_exp e =
        match ask.f (Queries.ReachableFrom e) with
        | a when not (Queries.LS.is_top a) ->
          let to_extra (v,o) xs = AD.of_mval (v, Addr.Offs.of_exp o) :: xs  in
          Queries.LS.fold to_extra (Queries.LS.remove (dummyFunDec.svar, `NoOffset) a) []
        (* Ignore soundness warnings, as invalidation proper will raise them. *)
        | _ -> []
      in
      List.concat_map do_exp args
    in
    let add_exploded_struct (one: AD.t) (many: AD.t) : AD.t =
      let vars = AD.to_var_may one in
      List.fold_right AD.add (List.concat_map to_addrs vars) many
    in
    let vars = List.fold_right add_exploded_struct reachable (AD.empty ()) in
    if D.is_top st
    then D.top ()
    else D.filter (fun x -> AD.mem x vars) st

  (*
    Transfer functions
  *)
  let assign ctx (lval:lval) (rval:exp) : trans_out =
    ignore (is_expr_initd (Analyses.ask_of_ctx ctx) rval ctx.local);
    init_lval (Analyses.ask_of_ctx ctx) lval ctx.local

  let branch ctx (exp:exp) (tv:bool) : trans_out =
    ignore (is_expr_initd (Analyses.ask_of_ctx ctx) exp ctx.local);
    ctx.local

  let body ctx (f:fundec) : trans_out =
    let add_var st v = List.fold_right D.add (to_addrs v) st in
    List.fold_left add_var ctx.local f.slocals

  let return ctx (exp:exp option) (f:fundec) : trans_out =
    let remove_var x v =
      List.fold_right D.remove (to_addrs v) x in
    let nst = List.fold_left remove_var ctx.local (f.slocals @ f.sformals) in
    match exp with
    | Some exp -> ignore (is_expr_initd (Analyses.ask_of_ctx ctx) exp ctx.local); nst
    | _ -> nst


  let enter ctx (lval: lval option) (f:fundec) (args:exp list) : (D.t * D.t) list =
    let nst = remove_unreachable (Analyses.ask_of_ctx ctx) args ctx.local in
    [ctx.local, nst]

  let combine_env ctx lval fexp f args fc au f_ask =
    ignore (List.map (fun x -> is_expr_initd (Analyses.ask_of_ctx ctx) x ctx.local) args);
    let cal_st = remove_unreachable (Analyses.ask_of_ctx ctx) args ctx.local in
    D.union au (D.diff ctx.local cal_st)

  let combine_assign ctx (lval:lval option) fexp (f:fundec) (args:exp list) fc (au:D.t) (f_ask: Queries.ask) : trans_out =
    match lval with
    | None -> ctx.local
    | Some lv -> init_lval (Analyses.ask_of_ctx ctx) lv ctx.local


  let special ctx (lval: lval option) (f:varinfo) (arglist:exp list) : D.t =
    match lval with
    | Some lv -> init_lval (Analyses.ask_of_ctx ctx) lv ctx.local
    | _ -> ctx.local

  (*  let fork ctx (lval: lval option) (f : varinfo) (args : exp list) : (varinfo * D.t) list =
      [] (* thats wrong: should be [None, top ()] *)*)

end

let _ =
  MCP.register_analysis (module Spec : MCPSpec)
