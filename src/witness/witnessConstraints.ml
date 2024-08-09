(** Analysis specification transformation for ARG construction. *)

open Batteries
open Analyses


(** Add path sensitivity to a analysis *)
module PathSensitive3 (Spec:Spec)
  : Spec
  (* with type D.t = SetDomain.ToppedSet(Spec.D)(N).t
     and module G = Spec.G
     and module C = Spec.C *)
=
struct
  (* module I = IntDomain.Integers *)
  module I =
  struct
    include Spec.D
    (* assumes Hashcons inside PathSensitive *)
    let to_int = tag
    let name () = "D"
    let printXml f d = BatPrintf.fprintf f "<value>%a</value>" printXml d
  end
  module CC =
  struct
    include Spec.C
    let name () = "C"
    let printXml f c = BatPrintf.fprintf f "<value>%a</value>" printXml c
  end
  module VI = Printable.Prod3 (Node) (CC) (I)
  module VIE = Printable.Prod (VI) (MyARG.InlineEdgePrintable)
  module VIES = SetDomain.Make (VIE)
  (* even though R is just a set and in solver's [widen old (join old new)] would join the sets of predecessors
     instead of keeping just the last, we are saved by set's narrow bringing that back down to the latest predecessors *)
  module R =
  struct
    include VIES
    (* new predecessors are always the right ones for the latest evaluation *)
    let widen x y = y
    let narrow x y = y
  end

  module SpecDMap (V: Lattice.S) =
  struct
    module R =
    struct
      include Spec.P
      type elt = Spec.D.t
    end
    module J = MapDomain.Joined (Spec.D) (V)
    include DisjointDomain.ProjectiveMap (Spec.D) (V) (J) (R)
  end

  module Dom =
  struct
    module V = R
    include SpecDMap (R)

    let name () = "PathSensitive (" ^ name () ^ ")"

    let printXml f x =
      let print_one x r =
        (* BatPrintf.fprintf f "\n<path>%a</path>" Spec.D.printXml x *)
        BatPrintf.fprintf f "\n<path>%a<analysis name=\"witness\">%a</analysis></path>" Spec.D.printXml x V.printXml r
      in
      iter print_one x

    let map_keys f m =
      fold (fun e r acc ->
          add (f e) r acc
        ) m (empty ())
    let choose_key m = fst (choose m)
    let fold_keys f m a = fold (fun e _ acc -> f e acc) m a
  end

  (* Additional dependencies component between values before and after sync.
     This is required because some analyses (e.g. region) do sideg through local domain diff and sync.
     sync is automatically applied in FromSpec before any transition, so previous values may change (diff is flushed).
     We now use Sync for every tf such that threadspawn after tf could look up state before tf. *)
  module SyncSet =
  struct
    include SetDomain.Make (Spec.D)
    (* new predecessors are always the right ones for the latest evaluation *)
    let widen x y = y
    let narrow x y = y
  end
  module Sync = SpecDMap (SyncSet)
  module D =
  struct
    include Lattice.Prod (Dom) (Sync)

    let printXml f (d, _) = Dom.printXml f d
  end

  module G = Spec.G
  module C = Spec.C
  module V = Spec.V
  module P = UnitP

  let name () = "PathSensitive3("^Spec.name ()^")"

  type marshal = Spec.marshal
  let init = Spec.init
  let finalize = Spec.finalize

  let exitstate  v = (Dom.singleton (Spec.exitstate  v) (R.bot ()), Sync.bot ())
  let startstate v = (Dom.singleton (Spec.startstate v) (R.bot ()), Sync.bot ())
  let morphstate v (d, _) = (Dom.map_keys (Spec.morphstate v) d, Sync.bot ())

  let step n c i e = R.singleton ((n, c, i), e)
  let step n c i e sync =
    match Sync.find i sync with
    | syncs ->
      SyncSet.fold (fun xsync acc ->
          R.join acc (step n c xsync e)
        ) syncs (R.bot ())
    | exception Not_found ->
      M.debug ~category:Witness ~tags:[Category Analyzer] "PathSensitive3 sync predecessor not found";
      R.bot ()
  let step_ctx ctx x e =
    try
      step ctx.prev_node (ctx.context ()) x e (snd ctx.local)
    with Ctx_failure _ ->
      R.bot ()
  let step_ctx_edge ctx x = step_ctx ctx x (CFGEdge ctx.edge)
  let step_ctx_inlined_edge ctx x = step_ctx ctx x (InlinedEdge ctx.edge)

  let nosync x = Sync.singleton x (SyncSet.singleton x)

  let conv ctx x =
    let rec ctx' =
      { ctx with
        local = x;
        ask = (fun (type a) (q: a Queries.t) -> Spec.query ctx' q);
        split;
      }
    and split y es =
      let yr = step_ctx_edge ctx x in
      ctx.split (Dom.singleton y yr, Sync.bot ()) es
    in
    ctx'

  let context ctx fd (l, _) =
    if Dom.cardinal l <> 1 then
      failwith "PathSensitive3.context must be called with a singleton set."
    else
      let x = Dom.choose_key l in
      Spec.context (conv ctx x) fd @@ x

  let startcontext = Spec.startcontext

  let map ctx f g =
    (* we now use Sync for every tf such that threadspawn after tf could look up state before tf *)
    let h x (xs, sync) =
      try
        let x' = g (f (conv ctx x)) in
        (Dom.add x' (step_ctx_edge ctx x) xs, Sync.add x' (SyncSet.singleton x) sync)
      with Deadcode -> (xs, sync)
    in
    let d = Dom.fold_keys h (fst ctx.local) (Dom.empty (), Sync.bot ()) in
    if Dom.is_bot (fst d) then raise Deadcode else d

  (* TODO???? *)
  let map_event ctx e =
    (* we now use Sync for every tf such that threadspawn after tf could look up state before tf *)
    let h x (xs, sync) =
      try
        let x' = Spec.event (conv ctx x) e (conv ctx x) in
        (Dom.add x' (step_ctx_edge ctx x) xs, Sync.add x' (SyncSet.singleton x) sync)
      with Deadcode -> (xs, sync)
    in
    let d = Dom.fold_keys h (fst ctx.local) (Dom.empty (), Sync.bot ()) in
    if Dom.is_bot (fst d) then raise Deadcode else d


  let fold' ctx f g h a =
    let k x a =
      try h a x @@ g @@ f @@ conv ctx x
      with Deadcode -> a
    in
    Dom.fold_keys k (fst ctx.local) a

  let fold'' ctx f g h a =
    let k x r a =
      try h a x r @@ g @@ f @@ conv ctx x
      with Deadcode -> a
    in
    Dom.fold k (fst ctx.local) a

  let assign ctx l e    = map ctx Spec.assign  (fun h -> h l e )
  let vdecl ctx v       = map ctx Spec.vdecl   (fun h -> h v)
  let body   ctx f      = map ctx Spec.body    (fun h -> h f   )
  let return ctx e f    = map ctx Spec.return  (fun h -> h e f )
  let branch ctx e tv   = map ctx Spec.branch  (fun h -> h e tv)
  let asm ctx           = map ctx Spec.asm     identity
  let skip ctx          = map ctx Spec.skip    identity
  let special ctx l f a = map ctx Spec.special (fun h -> h l f a)
  let event ctx e octx = map_event ctx e (* TODO: ???? *)

  let paths_as_set ctx =
    let (a,b) = ctx.local in
    let r = Dom.bindings a in
    List.map (fun (x,v) -> (Dom.singleton x v, b)) r

  let threadenter ctx ~multiple lval f args =
    let g xs x' ys =
      let ys' = List.map (fun y ->
          let yr = step ctx.prev_node (ctx.context ()) x' (ThreadEntry (lval, f, args)) (nosync x') in (* threadenter called on before-sync state *)
          (Dom.singleton y yr, Sync.bot ())
        ) ys
      in
      ys' @ xs
    in
    fold' ctx (Spec.threadenter ~multiple) (fun h -> h lval f args) g []
  let threadspawn ctx ~multiple lval f args fctx =
    let fd1 = Dom.choose_key (fst fctx.local) in
    map ctx (Spec.threadspawn ~multiple) (fun h -> h lval f args (conv fctx fd1))

  let sync ctx reason =
    fold'' ctx Spec.sync (fun h -> h reason) (fun (a, async) x r a' ->
        (Dom.add a' r a, Sync.add a' (SyncSet.singleton x) async)
      ) (Dom.empty (), Sync.bot ())

  let query ctx (type a) (q: a Queries.t): a Queries.result =
    match q with
    | Queries.IterPrevVars f ->
      if M.tracing then M.tracei "witness" "IterPrevVars";
      Dom.iter (fun x r ->
          if M.tracing then M.tracei "witness" "x = %a" Spec.D.pretty x;
          R.iter (function ((n, c, j), e) ->
              if M.tracing then M.tracec "witness" "n = %a" Node.pretty_plain n;
              if M.tracing then M.tracec "witness" "c = %a" Spec.C.pretty c;
              if M.tracing then M.tracec "witness" "j = %a" Spec.D.pretty j;
              f (I.to_int x) (n, Obj.repr c, I.to_int j) e
            ) r;
          if M.tracing then M.traceu "witness" "" (* unindent! *)
        ) (fst ctx.local);
      (* check that sync mappings don't leak into solution (except Function) *)
      (* TODO: disabled because we now use and leave Sync for every tf,
         such that threadspawn after tf could look up state before tf *)
      (* begin match ctx.node with
           | Function _ -> () (* returns post-sync in FromSpec *)
           | _ -> assert (Sync.is_bot (snd ctx.local));
         end; *)
      if M.tracing then M.traceu "witness" "";
      ()
    | Queries.IterVars f ->
      Dom.iter (fun x r ->
          f (I.to_int x)
        ) (fst ctx.local);
      ()
    | Queries.PathQuery (i, q) ->
      (* TODO: optimize indexing, using inner hashcons somehow? *)
      (* let (d, _) = List.at (S.elements s) i in *)
      let (d, _) = List.find (fun (x, _) -> I.to_int x = i) (Dom.bindings (fst ctx.local)) in
      Spec.query (conv ctx d) q
    | Queries.Invariant ({path=Some i; _} as c) -> Invariant.top()
    (* TODO: optimize indexing, using inner hashcons somehow? *)
    (* let (d, _) = List.at (S.elements s) i in *)
    (* let (d, _) = List.find (fun (x, _) -> I.to_int x = i) (Dom.bindings (fst ctx.local)) in
       Spec.query (conv ctx d) (Invariant c) *)
    | _ ->
      (* join results so that they are sound for all paths *)
      let module Result = (val Queries.Result.lattice q) in
      fold' ctx Spec.query identity (fun x _ f -> Result.join x (f q)) (Result.bot ())

  let should_inline f =
    (* (* inline __VERIFIER_error because Control requires the corresponding FunctionEntry node *)
       not (Svcomp.is_special_function f) || Svcomp.is_error_function f *)
    (* TODO: don't inline __VERIFIER functions for CPAchecker, but inlining needed for WP *)
    true

  let enter ctx l f a =
    let g xs x' ys =
      let ys' = List.map (fun (x,y) ->
          (* R.bot () isn't right here? doesn't actually matter? *)
          let yr =
            if should_inline f then
              step_ctx ctx x' (InlineEntry (l, f, a))
            else
              R.bot ()
          in
          (* keep left syncs so combine gets them for no-inline case *)
          (* must lookup and short-circuit because enter may modify first in pair (e.g. abortUnless) *)
          let syncs =
            match Sync.find x' (snd ctx.local) with
            | syncs -> syncs
            | exception Not_found ->
              M.debug ~category:Witness ~tags:[Category Analyzer] "PathSensitive3 sync predecessor not found";
              SyncSet.bot ()
          in
          ((Dom.singleton x (R.bot ()), Sync.singleton x syncs), (Dom.singleton y yr, Sync.bot ()))
        ) ys
      in
      ys' @ xs
    in
    fold' ctx Spec.enter (fun h -> h l f a) g []

  let combine_env ctx l fe f a fc d  f_ask =
    (* Don't yet consider call edge done before assign. *)
    assert (Dom.cardinal (fst ctx.local) = 1);
    let (cd, cdr) = Dom.choose (fst ctx.local) in
    let k x (y, sync) =
      try
        let x' = Spec.combine_env (conv ctx cd) l fe f a fc x f_ask in
        (Dom.add x' cdr y, Sync.add x' (Sync.find cd (snd ctx.local)) sync) (* keep predecessors and sync from ctx, sync required for step_ctx_inlined_edge in combine_assign *)
      with Deadcode -> (y, sync)
    in
    let d = Dom.fold_keys k (fst d) (Dom.bot (), Sync.bot ()) in
    if Dom.is_bot (fst d) then raise Deadcode else d

  let combine_assign ctx l fe f a fc d  f_ask =
    (* Consider call edge done after entire call-assign. *)
    assert (Dom.cardinal (fst ctx.local) = 1);
    let cd = Dom.choose_key (fst ctx.local) in
    let k x (y, sync) =
      let r =
        if should_inline f then
          (* returns already post-sync in FromSpec *)
          let returnr = step (Function f) (Option.get fc) x (InlineReturn (l, f, a)) (nosync x) in (* fc should be Some outside of MCP *)
          let procr = step_ctx_inlined_edge ctx cd in
          R.join procr returnr
        else
          step_ctx_edge ctx cd
      in
      try
        let x' = Spec.combine_assign (conv ctx cd) l fe f a fc x f_ask in
        (Dom.add x' r y, Sync.add x' (SyncSet.singleton x) sync)
      with Deadcode -> (y, sync)
    in
    let d = Dom.fold_keys k (fst d) (Dom.bot (), Sync.bot ()) in
    if Dom.is_bot (fst d) then raise Deadcode else d
end
