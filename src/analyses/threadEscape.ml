(** Escape analysis for thread-local variables ([escape]). *)

open GoblintCil
open Analyses

module M = Messages

let has_escaped (ask: Queries.ask) (v: varinfo): bool =
  assert (not v.vglob);
  if not v.vaddrof then
    false (* Cannot have escaped without taking address. Override provides extra precision for degenerate ask in base eval_exp used for partitioned arrays. *)
  else
    ask.f (Queries.MayEscape v)

module Spec =
struct
  include Analyses.IdentitySpec

  module ThreadIdSet = SetDomain.Make (ThreadIdDomain.ThreadLifted)

  let name () = "escape"
  module D = EscapeDomain.EscapedVars
  module C = EscapeDomain.EscapedVars
  module V = VarinfoV
  module G = ThreadIdSet

  let reachable (ask: Queries.ask) e: D.t =
    match ask.f (Queries.ReachableFrom e) with
    | a when not (Queries.LS.is_top a) ->
      let to_extra (v,o) set = D.add v set in
      Queries.LS.fold to_extra (Queries.LS.remove (dummyFunDec.svar, `NoOffset) a) (D.empty ())
    (* Ignore soundness warnings, as invalidation proper will raise them. *)
    | a ->
      if M.tracing then M.tracel "escape" "reachable %a: %a\n" d_exp e Queries.LS.pretty a;
      D.empty ()

  let mpt (ask: Queries.ask) e: D.t =
    match ask.f (Queries.MayPointTo e) with
    | a when not (Queries.LS.is_top a) ->
      let to_extra (v,o) set = D.add v set in
      Queries.LS.fold to_extra (Queries.LS.remove (dummyFunDec.svar, `NoOffset) a) (D.empty ())
    (* Ignore soundness warnings, as invalidation proper will raise them. *)
    | a ->
      if M.tracing then M.tracel "escape" "mpt %a: %a\n" d_exp e Queries.LS.pretty a;
      D.empty ()

  let escape ctx escaped =
    let threadid = ctx.ask Queries.CurrentThreadId in
    let threadid = G.singleton threadid in

    (* avoid emitting unnecessary event *)
    if not (D.is_empty escaped) then begin
      ctx.emit (Events.Escape escaped);
      M.tracel "escape" "escaping: %a\n" D.pretty escaped;
      D.iter (fun v ->
        ctx.sideg v threadid) escaped
    end

  (* queries *)
  let query ctx (type a) (q: a Queries.t): a Queries.result =
    match q with
    | Queries.MayEscape v ->
      let threads = ctx.global v in
      if ThreadIdSet.is_empty threads then
        false
      else if not (ThreadFlag.has_ever_been_multi (Analyses.ask_of_ctx ctx)) then
        false
      else begin
        let possibly_started current = function
          | `Lifted tid ->
            let not_started = MHP.definitely_not_started (current, ctx.ask Queries.CreatedThreads) tid in
            let possibly_started = not not_started in
            M.tracel "escape" "possibly_started: %a %a -> %b\n" ThreadIdDomain.Thread.pretty tid  ThreadIdDomain.Thread.pretty current possibly_started;
            possibly_started
          | `Top
          | `Bot -> false
        in
        match ctx.ask Queries.CurrentThreadId with
        | `Lifted current ->
          let possibly_started = ThreadIdSet.exists (possibly_started current) threads in
          possibly_started || D.mem v ctx.local
        | `Top ->
          true
        | `Bot ->
          M.warn ~category:MessageCategory.Analyzer "CurrentThreadId is bottom.";
          false
        end
    | _ -> Queries.Result.top q

  (* transfer functions *)
  let assign ctx (lval:lval) (rval:exp) : D.t =
    let ask = Analyses.ask_of_ctx ctx in
    let vs = mpt ask (AddrOf lval) in
    if M.tracing then M.tracel "escape" "assign vs: %a\n" D.pretty vs;
    if D.exists (fun v -> v.vglob || has_escaped ask v) vs then (
      let escaped = reachable ask rval in
      let escaped = D.filter (fun v -> not v.vglob) escaped in
      if M.tracing then M.tracel "escape" "assign vs: %a | %a\n" D.pretty vs D.pretty escaped;
      if ThreadFlag.has_ever_been_multi ask then (* avoid emitting unnecessary event *)
        escape ctx escaped;
      D.join ctx.local escaped
    ) else begin
      M.tracel "escape" "nothing in rval: %a was escaped\n" D.pretty vs;
      ctx.local
    end

  let special ctx (lval: lval option) (f:varinfo) (args:exp list) : D.t =
    let desc = LibraryFunctions.find f in
    match desc.special args, f.vname, args with
    | _, "pthread_setspecific" , [key; pt_value] ->
      (* TODO: handle *)
      ctx.local
    | _ -> ctx.local

  let startstate v = D.bot ()
  let exitstate  v = D.bot ()

  let threadenter ctx lval f args =
    match args with
    | [ptc_arg] ->
      [ctx.local]
    | _ -> [ctx.local]

  let threadspawn ctx lval f args fctx =
    D.join ctx.local @@
      match args with
      | [ptc_arg] ->
        (* not reusing fctx.local to avoid unnecessarily early join of extra *)
        let escaped = reachable (Analyses.ask_of_ctx ctx) ptc_arg in
        let escaped = D.filter (fun v -> not v.vglob) escaped in
        if M.tracing then M.tracel "escape" "%a: %a\n" d_exp ptc_arg D.pretty escaped;
        escape ctx escaped;
        escaped
      | _ -> D.bot ()

  let event ctx e octx =
    match e with
    | Events.EnterMultiThreaded ->
      let escaped = ctx.local in
      escape ctx escaped;
      ctx.local
    | _ -> ctx.local
end

let _ =
  MCP.register_analysis (module Spec : MCPSpec)
