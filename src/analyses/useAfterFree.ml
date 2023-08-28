(** An analysis for the detection of use-after-free vulnerabilities ([useAfterFree]). *)

open GoblintCil
open Analyses
open MessageCategory

module ToppedVarInfoSet = SetDomain.ToppedSet(CilType.Varinfo)(struct let topname = "All Heap Variables" end)
module ThreadIdToJoinedThreadsMap = MapDomain.MapBot(ThreadIdDomain.ThreadLifted)(ConcDomain.MustThreadSet)

module Spec : Analyses.MCPSpec =
struct
  include Analyses.DefaultSpec

  let name () = "useAfterFree"

  module D = ToppedVarInfoSet
  module C = Lattice.Unit
  module G = ThreadIdToJoinedThreadsMap
  module V = VarinfoV

  (** TODO: Try out later in benchmarks to see how we perform with and without context-sensititivty *)
  let context _ _ = ()


  (* HELPER FUNCTIONS *)

  let set_global_svcomp_var is_double_free =
    if is_double_free then
      AnalysisState.svcomp_may_invalid_free := true
    else
      AnalysisState.svcomp_may_invalid_deref := true

  let get_current_threadid ctx =
    ctx.ask Queries.CurrentThreadId

  let get_joined_threads ctx =
    ctx.ask Queries.MustJoinedThreads

  let warn_for_multi_threaded_access ctx ?(is_double_free = false) (heap_var:varinfo) behavior cwe_number =
    let freeing_threads = ctx.global heap_var in
    (* If we're single-threaded or there are no threads freeing the memory, we have nothing to WARN about *)
    if ctx.ask (Queries.MustBeSingleThreaded { since_start = true }) || G.is_empty freeing_threads then ()
    else begin
      let possibly_started current tid joined_threads =
        match tid with
        | `Lifted tid ->
          let created_threads = ctx.ask Queries.CreatedThreads in
          let not_started = MHP.definitely_not_started (current, created_threads) tid in
          let possibly_started = not not_started in
          (* If [current] is possibly running together with [tid], but is also joined before the free() in [tid], then no need to WARN *)
          let current_joined_before_free = ConcDomain.MustThreadSet.mem current joined_threads in
          possibly_started && not current_joined_before_free
        | `Top -> true
        | `Bot -> false
      in
      let equal_current current tid joined_threads =
        match tid with
        | `Lifted tid ->
          ThreadId.Thread.equal current tid
        | `Top -> true
        | `Bot -> false
      in
      let bug_name = if is_double_free then "Double Free" else "Use After Free" in
      match get_current_threadid ctx with
      | `Lifted current ->
        let possibly_started = G.exists (possibly_started current) freeing_threads in
        if possibly_started then begin
          set_global_svcomp_var is_double_free;
          M.warn ~category:(Behavior behavior) ~tags:[CWE cwe_number] "There's a thread that's been started in parallel with the memory-freeing threads for heap variable %a. %s might occur" CilType.Varinfo.pretty heap_var bug_name
        end
        else begin
          let current_is_unique = ThreadId.Thread.is_unique current in
          let any_equal_current threads = G.exists (equal_current current) threads in
          if not current_is_unique && any_equal_current freeing_threads then begin
            set_global_svcomp_var is_double_free;
            M.warn ~category:(Behavior behavior) ~tags:[CWE cwe_number] "Current thread is not unique and a %s might occur for heap variable %a" bug_name CilType.Varinfo.pretty heap_var
          end
          else if D.mem heap_var ctx.local then begin
            set_global_svcomp_var is_double_free;
            M.warn ~category:(Behavior behavior) ~tags:[CWE cwe_number] "%s might occur in current unique thread %a for heap variable %a" bug_name ThreadIdDomain.FlagConfiguredTID.pretty current CilType.Varinfo.pretty heap_var
          end
        end
      | `Top ->
        set_global_svcomp_var is_double_free;
        M.warn ~category:(Behavior behavior) ~tags:[CWE cwe_number] "CurrentThreadId is top. %s might occur for heap variable %a" bug_name CilType.Varinfo.pretty heap_var
      | `Bot ->
        M.warn ~category:MessageCategory.Analyzer "CurrentThreadId is bottom"
    end

  let rec warn_lval_might_contain_freed ?(is_implicitly_derefed = false) ?(is_double_free = false) (transfer_fn_name:string) ctx (lval:lval) =
    match is_implicitly_derefed, is_double_free, lval with
    (* If we're not checking for a double-free and there's no deref happening, then there's no need to check for an invalid deref or an invalid free *)
    | false, false, (Var _, NoOffset) -> ()
    | _ ->
      let state = ctx.local in
      let undefined_behavior = if is_double_free then Undefined DoubleFree else Undefined UseAfterFree in
      let cwe_number = if is_double_free then 415 else 416 in
      let rec offset_might_contain_freed = function
        | NoOffset -> ()
        | Field (f, o) -> offset_might_contain_freed o
        | Index (e, o) -> warn_exp_might_contain_freed transfer_fn_name ctx e; offset_might_contain_freed o
      in
      let (lval_host, o) = lval in offset_might_contain_freed o; (* Check the lval's offset *)
      let lval_to_query =
        match lval_host with
        | Var _ -> Lval lval
        | Mem _ -> mkAddrOf lval (* Take the lval's address if its lhost is of the form *p, where p is a ptr *)
      in
      begin match ctx.ask (Queries.MayPointTo lval_to_query) with
        | a when not (Queries.LS.is_top a) && not (Queries.LS.mem (dummyFunDec.svar, `NoOffset) a) ->
          let warn_for_heap_var var =
            if D.mem var state then begin
              set_global_svcomp_var is_double_free;
              M.warn ~category:(Behavior undefined_behavior) ~tags:[CWE cwe_number] "lval (%s) in \"%s\" points to a maybe freed memory region" var.vname transfer_fn_name
            end
          in
          let pointed_to_heap_vars =
            Queries.LS.elements a
            |> List.map fst
            |> List.filter (fun var -> ctx.ask (Queries.IsHeapVar var))
          in
          (* Warn for all heap vars that the lval possibly points to *)
          List.iter warn_for_heap_var pointed_to_heap_vars;
          (* Warn for a potential multi-threaded UAF for all heap vars that the lval possibly points to *)
          List.iter (fun heap_var -> warn_for_multi_threaded_access ctx ~is_double_free heap_var undefined_behavior cwe_number) pointed_to_heap_vars
        | _ -> ()
      end

  and warn_exp_might_contain_freed ?(is_implicitly_derefed = false) ?(is_double_free = false) (transfer_fn_name:string) ctx (exp:exp) =
    match exp with
    (* Base recursion cases *)
    | Const _
    | SizeOf _
    | SizeOfStr _
    | AlignOf _
    | AddrOfLabel _ -> ()
    (* Non-base cases *)
    | Real e
    | Imag e
    | SizeOfE e
    | AlignOfE e
    | UnOp (_, e, _)
    | CastE (_, e) -> warn_exp_might_contain_freed ~is_implicitly_derefed ~is_double_free transfer_fn_name ctx e
    | BinOp (_, e1, e2, _) ->
      warn_exp_might_contain_freed ~is_implicitly_derefed ~is_double_free transfer_fn_name ctx e1;
      warn_exp_might_contain_freed ~is_implicitly_derefed ~is_double_free transfer_fn_name ctx e2
    | Question (e1, e2, e3, _) ->
      warn_exp_might_contain_freed ~is_implicitly_derefed ~is_double_free transfer_fn_name ctx e1;
      warn_exp_might_contain_freed ~is_implicitly_derefed ~is_double_free transfer_fn_name ctx e2;
      warn_exp_might_contain_freed ~is_implicitly_derefed ~is_double_free transfer_fn_name ctx e3
    (* Lval cases (need [warn_lval_might_contain_freed] for them) *)
    | Lval lval
    | StartOf lval
    | AddrOf lval -> warn_lval_might_contain_freed ~is_implicitly_derefed ~is_double_free transfer_fn_name ctx lval

  let side_effect_mem_free ctx freed_heap_vars threadid joined_threads =
    let side_effect_globals_to_heap_var heap_var =
      let current_globals = ctx.global heap_var in
      let globals_to_side_effect = G.add threadid joined_threads current_globals in
      ctx.sideg heap_var globals_to_side_effect
    in
    D.iter side_effect_globals_to_heap_var freed_heap_vars



  (* TRANSFER FUNCTIONS *)

  let assign ctx (lval:lval) (rval:exp) : D.t =
    warn_lval_might_contain_freed "assign" ctx lval;
    warn_exp_might_contain_freed "assign" ctx rval;
    ctx.local

  let branch ctx (exp:exp) (tv:bool) : D.t =
    warn_exp_might_contain_freed "branch" ctx exp;
    ctx.local

  let body ctx (f:fundec) : D.t =
    ctx.local

  let return ctx (exp:exp option) (f:fundec) : D.t =
    Option.iter (fun x -> warn_exp_might_contain_freed "return" ctx x) exp;
    ctx.local

  let enter ctx (lval:lval option) (f:fundec) (args:exp list) : (D.t * D.t) list =
    let caller_state = ctx.local in
    List.iter (fun arg -> warn_exp_might_contain_freed "enter" ctx arg) args;
    if D.is_empty caller_state then
      [caller_state, caller_state]
    else (
      let reachable_from_args = List.fold_left (fun acc arg -> Queries.LS.join acc (ctx.ask (ReachableFrom arg))) (Queries.LS.empty ()) args in
      if Queries.LS.is_top reachable_from_args || D.is_top caller_state then
        [caller_state, caller_state]
      else
        let reachable_vars = List.map fst (Queries.LS.elements reachable_from_args) in
        let callee_state = D.filter (fun var -> List.mem var reachable_vars) caller_state in
        [caller_state, callee_state]
    )

  let combine_env ctx (lval:lval option) fexp (f:fundec) (args:exp list) fc (callee_local:D.t) (f_ask:Queries.ask) : D.t =
    let caller_state = ctx.local in
    D.join caller_state callee_local

  let combine_assign ctx (lval:lval option) fexp (f:fundec) (args:exp list) fc (callee_local:D.t) (f_ask: Queries.ask): D.t =
    Option.iter (fun x -> warn_lval_might_contain_freed "enter" ctx x) lval;
    ctx.local

  let special ctx (lval:lval option) (f:varinfo) (arglist:exp list) : D.t =
    let state = ctx.local in
    let desc = LibraryFunctions.find f in
    let is_arg_implicitly_derefed arg =
      let read_shallow_args = LibraryDesc.Accesses.find desc.accs { kind = Read; deep = false } arglist in
      let read_deep_args = LibraryDesc.Accesses.find desc.accs { kind = Read; deep = true } arglist in
      let write_shallow_args = LibraryDesc.Accesses.find desc.accs { kind = Write; deep = false } arglist in
      let write_deep_args = LibraryDesc.Accesses.find desc.accs { kind = Write; deep = true } arglist in
      List.mem arg read_shallow_args || List.mem arg read_deep_args || List.mem arg write_shallow_args || List.mem arg write_deep_args
    in
    Option.iter (fun x -> warn_lval_might_contain_freed ("special: " ^ f.vname) ctx x) lval;
    List.iter (fun arg -> warn_exp_might_contain_freed ~is_implicitly_derefed:(is_arg_implicitly_derefed arg) ~is_double_free:(f.vname = "free") ("special: " ^ f.vname) ctx arg) arglist;
    match desc.special arglist with
    | Free ptr ->
      begin match ctx.ask (Queries.MayPointTo ptr) with
        | a when not (Queries.LS.is_top a) && not (Queries.LS.mem (dummyFunDec.svar, `NoOffset) a) ->
          let pointed_to_heap_vars =
            Queries.LS.elements a
            |> List.map fst
            |> List.filter (fun var -> ctx.ask (Queries.IsHeapVar var))
            |> D.of_list
          in
          (* Side-effect the tid that's freeing all the heap vars collected here *)
          side_effect_mem_free ctx pointed_to_heap_vars (get_current_threadid ctx) (get_joined_threads ctx);
          (* Add all heap vars, which ptr points to, to the state *)
          D.join state (pointed_to_heap_vars)
        | _ -> state
      end
    | _ -> state

  let threadenter ctx lval f args = [ctx.local]
  let threadspawn ctx lval f args fctx = ctx.local

  let startstate v = D.bot ()
  let exitstate v = D.top ()

end

let _ =
  MCP.register_analysis (module Spec : MCPSpec)