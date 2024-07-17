(** OCaml implementation of a quantitative congruence closure. *)
include UnionFind
open Batteries
open GoblintCil
module Var = CilType.Varinfo
module M = Messages

(** Quantitative congruence closure on terms *)
module CongruenceClosure = struct

  module TUF = UnionFind
  module LMap = LookupMap


  (* block disequalities *)
  module BlDis = struct
    (** Block disequalities:
        a term t1 is mapped to a set of terms that have a different block than t1.
        It is allowed to contain terms that are not present in the data structure,
        so we shouldn't assume that all terms in bldis are present in the union find!
    *)
    type t = TSet.t TMap.t [@@deriving eq, ord, hash]

    let bindings = TMap.bindings
    let empty = TMap.empty
    let is_empty = TMap.is_empty

    let to_conj bldiseq = List.fold
        (fun list (t1, tset) ->
           TSet.fold (fun t2 bldiseqs -> BlNequal(t1, t2)::bldiseqs) tset [] @ list
        ) [] (bindings bldiseq)

    let add bldiseq t1 t2 =
      match TMap.find_opt t1 bldiseq with
      | None -> TMap.add t1 (TSet.singleton t2) bldiseq
      | Some tset -> TMap.add t1 (TSet.add t2 tset) bldiseq

    (** Add disequalities bl(t1) != bl(t2) and bl(t2) != bl(t1). *)
    let add_block_diseq bldiseq (t1, t2) =
      add (add bldiseq t1 t2) t2 t1

    (**
       params:

       t1-> a term that is NOT present in the data structure

       tlist: a list of representative terms

       For each term t2 in tlist, it adds the disequality t1 != t2 to diseqs.
    *)
    let add_block_diseqs bldiseq uf t1 tlist =
      List.fold (fun bldiseq t2 ->
          add_block_diseq bldiseq (t1, t2)) bldiseq tlist

    (** Find all elements that are in the same equivalence class as t,
        given the cmap, but only those that are now representatives in the union find uf. *)
    let comp_t_cmap_repr cmap t uf =
      match TMap.find_opt t cmap with
      | None -> [Z.zero, t]
      | Some zmap ->
        List.flatten @@ List.map
          (fun (z, set) ->
             List.cartesian_product [z] (TSet.to_list (*TSet.filter (TUF.is_root uf*) set)) (ZMap.bindings zmap)

    (** For each block disequality bl(t1) != bl(t2) we add all disequalities
        that follow from equalities. I.e., if t1 = z1 + t1' and t2 = z2 + t2',
        then we add the disequaity  bl(t1') != bl(t2').
    *)
    let element_closure bldis cmap uf =
      let comp_closure = function
        | BlNequal (r1,r2) ->
          let eq_class1, eq_class2 = comp_t_cmap_repr cmap r1 uf, comp_t_cmap_repr cmap r2 uf in
          List.cartesian_product (List.map snd eq_class1) (List.map snd eq_class2)
        | _ -> []
      in
      List.concat_map comp_closure bldis

    let map_set_mem v v' (map:t) = match TMap.find_opt v map with
      | None -> false
      | Some set -> TSet.mem v' set

    let filter_if (map:t) p =
      TMap.filter_map (fun _ t_set ->
          let filtered_set = TSet.filter p t_set in
          if TSet.is_empty filtered_set then None else Some filtered_set) map

    let filter_map f (diseq:t) =
      TMap.filter_map
        (fun _ s -> let set = TSet.filter_map f s in
          if TSet.is_empty set then None else Some set) diseq

    let shift v r v' (map:t) =
      match TMap.find_opt v' map with
      | None -> map
      | Some tset ->
        TMap.remove v' (TMap.add v tset map)

    let term_set bldis =
      TSet.of_enum (TMap.keys bldis)
  end

  module Disequalities = struct

    (* disequality map:
       if t_1 -> z -> {t_2, t_3}
       then we know that t_1 + z != t_2
       and also that t_1 + z != t_3
    *)
    type t = TSet.t ZMap.t TMap.t [@@deriving eq, ord, hash] (* disequalitites *)
    type arg_t = (T.t * Z.t) ZMap.t TMap.t (* maps each state in the automata to its predecessors *)

    let empty = TMap.empty
    let is_empty = TMap.is_empty
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

    (** Find all disequalities of the form t1 != z2-z1 + t2
        that can be inferred from equalities of the form *(z1 + t1) = *(z2 + t2).
    *)
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

    (** Find all disequalities of the form t1 != z2-z1 + t2
        that can be inferred from block equalities of the form bl( *(z1 + t1) ) = bl( *(z2 + t2) ).
    *)
    let check_neq_bl (uf,arg) rest (t1, tset) =
      List.fold (fun rest t2 ->
          (* We know that r1 <> r2, otherwise it would be Unsat. *)
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
    let rec propagate_neq (uf,(cmap: TSet.t ZMap.t TMap.t),arg,neq) bldis = function (* v1, v2 are distinct roots with v1 != v2+r   *)
      | [] -> neq (* uf need not be returned: has been flattened during constr. of cmap *)
      | (v1,v2,r) :: rest ->
        (* we don't want to explicitly store disequalities of the kind &x != &y *)
        if T.is_addr v1 && T.is_addr v2 || BlDis.map_set_mem v1 v2 bldis then
          propagate_neq (uf,cmap,arg,neq) bldis rest else
          (* v1, v2 are roots; v2 -> r,v1 not yet contained in neq *)
        if T.equal v1 v2 then
          if Z.equal r Z.zero then raise Unsat else propagate_neq (uf,cmap,arg,neq) bldis rest
        else (* check whether it is already in neq *)
        if map_set_mem (v1,Z.(-r)) v2 neq then propagate_neq (uf,cmap,arg,neq) bldis rest
        else let neq = map_set_add (v1,Z.(-r)) v2 neq |>
                       map_set_add (v2,r) v1 in
        (*
          search components of v1, v2 for elements at distance r to obtain inferred equalities
          at the same level (not recorded) and then compare their predecessors
        *)
          match TMap.find_opt v1 (cmap:t), TMap.find_opt v2 cmap with
          | None,_ | _,None -> (*should not happen*) propagate_neq (uf,cmap,arg,neq) bldis rest
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
            propagate_neq (uf,cmap,arg,neq) bldis rest
        (*
          collection of disequalities:
                  * disequalities originating from different offsets of same root
                  * disequalities originating from block disequalities
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

    (** For each disequality t1 != z + t2 we add all disequalities
        that follow from equalities. I.e., if t1 = z1 + t1' and t2 = z2 + t2',
        then we add the disequaity  t1' != z + z2 - z1 + t2'.
    *)
    let element_closure diseqs cmap uf =
      let comp_closure (r1,r2,z) =
        let eq_class1, eq_class2 = BlDis.comp_t_cmap_repr cmap r1 uf, BlDis.comp_t_cmap_repr cmap r2 uf in
        List.map (fun ((z1, nt1),(z2, nt2)) ->
            (nt1, nt2, Z.(-z2+z+z1)))
          (List.cartesian_product eq_class1 eq_class2)
      in
      List.concat_map comp_closure diseqs
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

    (** Sometimes it's important to keep the dereferenced term,
        even if it's not technically possible to dereference it from a point of view of the C types.
        We still need the dereferenced term for he correctness of some algorithms,
        and the resulting expression will never be used, so it doesn't need to be a
        C expression hat makes sense. *)
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

    let show_min_rep_opt min_repr_opt =
      match min_repr_opt with
      | None -> "None"
      | Some min_repr -> show_min_rep min_repr

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
      if M.tracing then M.trace "c2po" "compute_minimal_representatives\n";
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
            min_repr: MRMap.t option;
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

  let compute_min_repr_if_necessary cc =
    match cc.min_repr with
    | None -> let min_repr, uf =
                MRMap.compute_minimal_representatives (cc.uf, cc.set, cc.map) in
      {cc with min_repr = Some min_repr; uf}, min_repr
    | Some min_repr -> cc, min_repr

  let remove_min_repr = function
    | None -> None
    | Some cc -> Some {cc with min_repr=None}

  let exactly_equal cc1 cc2 =
    cc1.uf == cc2.uf && cc1.map == cc2.map && cc1.diseq == cc2.diseq && cc1.bldis == cc2.bldis

  (* Runtime = O(nr. of atoms) + O(nr. transitions in the automata)
     Basically runtime = O(size of result) if we hadn't removed the trivial conjunctions. *)
  (** Returns the canonical normal form of the data structure in form of a sorted list of conjunctions.  *)
  let get_normal_form cc =
    let cc, min_repr = compute_min_repr_if_necessary cc in
    let normalize_equality (t1, t2, z) =
      if T.equal t1 t2 && Z.(equal z zero) then None else
        Some (Equal (t1, t2, z)) in
    let conjunctions_of_atoms =
      let atoms = SSet.get_atoms cc.set in
      List.filter_map (fun atom ->
          let (rep_state, rep_z) = TUF.find_no_pc cc.uf atom in
          let (min_state, min_z) = MRMap.find rep_state min_repr in
          normalize_equality (atom, min_state, Z.(rep_z - min_z))
        ) atoms
    in
    let conjunctions_of_transitions =
      let transitions = get_transitions (cc.uf, cc.map) in
      List.filter_map (fun (z,s,(s',z')) ->
          let (min_state, min_z) = MRMap.find s min_repr in
          let (min_state', min_z') = MRMap.find s' min_repr in
          normalize_equality (SSet.deref_term_even_if_its_not_possible min_state Z.(z - min_z) cc.set, min_state', Z.(z' - min_z'))
        ) transitions in
    (*disequalities*)
    let disequalities = Disequalities.get_disequalities cc.diseq in
    (* find disequalities between min_repr *)
    let normalize_disequality (t1, t2, z) =
      let (min_state1, min_z1) = MRMap.find t1 min_repr in
      let (min_state2, min_z2) = MRMap.find t2 min_repr in
      let new_offset = Z.(-min_z2 + min_z1 + z) in
      if T.compare min_state1 min_state2 < 0 then Nequal (min_state1, min_state2, new_offset)
      else Nequal (min_state2, min_state1, Z.(-new_offset))
    in
    if M.tracing then M.trace "c2po-diseq" "DISEQUALITIES: %s;\nUnion find: %s\nMin repr: %s\nMap: %s\n" (show_conj disequalities) (TUF.show_uf cc.uf) (MRMap.show_min_rep min_repr) (LMap.show_map cc.map);
    let disequalities = List.map (function | Equal (t1,t2,z) | Nequal (t1,t2,z) -> normalize_disequality (t1, t2, z)|BlNequal (t1,t2) -> BlNequal (t1,t2)) disequalities in
    (* block disequalities *)
    let normalize_bldis t = match t with
      | BlNequal (t1,t2) ->
        let min_state1 =
          begin match MRMap.find_opt t1 min_repr with
            | None -> t1
            | Some (a,_) -> a
          end in
        let min_state2 =
          begin match MRMap.find_opt t2 min_repr with
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

  (* Runtime = O(nr. of atoms) + O(nr. transitions in the automata)
       Basically runtime = O(size of result if we hadn't removed the trivial conjunctions). *)
  (** Returns a list of conjunctions that follow from the data structure in form of a sorted list of conjunctions.  *)
  let get_conjunction cc =
    let normalize_equality (t1, t2, z) =
      if T.equal t1 t2 && Z.(equal z zero) then None else
        Some (Equal (t1, t2, z)) in
    let conjunctions_of_atoms =
      let atoms = SSet.get_atoms cc.set in
      List.filter_map (fun atom ->
          let (rep_state, rep_z) = TUF.find_no_pc cc.uf atom in
          normalize_equality (atom, rep_state, rep_z)
        ) atoms
    in
    let conjunctions_of_transitions =
      let transitions = get_transitions (cc.uf, cc.map) in
      List.filter_map (fun (z,s,(s',z')) ->
          normalize_equality (SSet.deref_term_even_if_its_not_possible s z cc.set, s', z')
        ) transitions in
    (*disequalities*)
    let disequalities = Disequalities.get_disequalities cc.diseq in
    (* find disequalities between min_repr *)
    let normalize_disequality (t1, t2, z) =
      if T.compare t1 t2 < 0 then Nequal (t1, t2, z)
      else Nequal (t2, t1, Z.(-z))
    in
    if M.tracing then M.trace "c2po-diseq" "DISEQUALITIES: %s;\nUnion find: %s\nMap: %s\n" (show_conj disequalities) (TUF.show_uf cc.uf) (LMap.show_map cc.map);
    let disequalities = List.map (function | Equal (t1,t2,z) | Nequal (t1,t2,z) -> normalize_disequality (t1, t2, z)|BlNequal (t1,t2) -> BlNequal (t1,t2)) disequalities in
    (* block disequalities *)
    let normalize_bldis t = match t with
      | BlNequal (t1,t2) ->
        if T.compare t1 t2 < 0 then BlNequal (t1, t2)
        else BlNequal (t2, t1)
      | _ -> t
    in
    let conjunctions_of_bl_diseqs = List.map normalize_bldis @@ BlDis.to_conj cc.bldis in
    (* all propositions *)
    BatList.sort_unique (T.compare_v_prop) (conjunctions_of_atoms @ conjunctions_of_transitions @ disequalities @ conjunctions_of_bl_diseqs)

  let show_all x = "Normal form:\n" ^
                   show_conj((get_conjunction x)) ^
                   "Union Find partition:\n" ^
                   (TUF.show_uf x.uf)
                   ^ "\nSubterm set:\n"
                   ^ (SSet.show_set x.set)
                   ^ "\nLookup map/transitions:\n"
                   ^ (LMap.show_map x.map)
                   ^ "\nNeq:\n"
                   ^ (Disequalities.show_neq x.diseq)
                   ^ "\nBlock diseqs:\n"
                   ^ show_conj(BlDis.to_conj x.bldis)
                   ^ "\nMin repr:\n"
                   ^ MRMap.show_min_rep_opt x.min_repr

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
  let init_cc =
    {uf = TUF.empty; set = SSet.empty; map = LMap.empty; min_repr = None; diseq = Disequalities.empty; bldis = BlDis.empty}

  (** closure of disequalities *)
  let congruence_neq cc neg =
    try
      let neg = Tuple3.second (split(Disequalities.get_disequalities cc.diseq)) @ neg in
      (* getting args of dereferences *)
      let uf,cmap,arg = Disequalities.get_args cc.uf in
      (* taking implicit dis-equalities into account *)
      let neq_list = Disequalities.init_neq (uf,cmap,arg) @ Disequalities.init_neg_block_diseq (uf, cc.bldis, cmap, arg) in
      let neq = Disequalities.propagate_neq (uf,cmap,arg,Disequalities.empty) cc.bldis neq_list in
      (* taking explicit dis-equalities into account *)
      let neq_list = Disequalities.init_list_neq uf neg in
      let neq = Disequalities.propagate_neq (uf,cmap,arg,neq) cc.bldis neq_list in
      if M.tracing then M.trace "c2po-neq" "congruence_neq: %s\nUnion find: %s\n" (Disequalities.show_neq neq) (TUF.show_uf uf);
      Some {uf; set=cc.set; map=cc.map; min_repr=cc.min_repr;diseq=neq; bldis=cc.bldis}
    with Unsat -> None

  let congruence_neq_opt cc neq = match cc with
    | None -> None
    | Some cc -> congruence_neq cc neq

  (**
     parameters: (uf, map, new_repr) equalities.

     returns updated (uf, map, new_repr), where:

     `uf` is the new union find data structure after having added all equalities.

     `map` maps reference variables v to a map that maps integers z to terms that are equivalent to *(v + z).

     `new_repr` maps each term that changed its representative term to the new representative.
     It can be given as a parameter to `update_bldis` in order to update the representatives in the block disequalities.

     Throws "Unsat" if a contradiction is found.
  *)
  let rec closure (uf, map, new_repr) = function
    | [] -> (uf, map, new_repr)
    | (t1, t2, r)::rest ->
      (let v1, r1, uf = TUF.find uf t1 in
       let v2, r2, uf = TUF.find uf t2 in
       let sizet1, sizet2 = T.get_size t1, T.get_size t2 in
       if not (Z.equal sizet1 sizet2) then
         (if M.tracing then M.trace "c2po" "ignoring equality because the sizes are not the same: %s = %s + %s" (T.show t1) (Z.to_string r) (T.show t2);
          closure (uf, map, new_repr) rest) else
       if T.equal v1 v2 then
         (* t1 and t2 are in the same equivalence class *)
         if Z.equal r1 Z.(r2 + r) then closure (uf, map, new_repr) rest
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
         closure (uf, map, new_repr) rest
      )

  (** Update block disequalities with the new representatives, *)
  let update_bldis new_repr bldis =
    (* update block disequalities with the new representatives *)
    let find_new_root t1 = match TMap.find_opt t1 new_repr with
      | None -> t1
      | Some v -> v
    in
    let disequalities = BlDis.to_conj bldis
    in (*TODO maybe optimize?, and maybe use this also for removing terms *)
    let add_bl_dis new_diseq = function
      | BlNequal (t1,t2) -> BlDis.add_block_diseq new_diseq (find_new_root t1,find_new_root t2)
      | _-> new_diseq
    in
    List.fold add_bl_dis BlDis.empty disequalities

  (**
     Parameters: cc conjunctions.

     returns updated cc, where:

     - `uf` is the new union find data structure after having added all equalities.

     - `set` doesn't change

     - `map` maps reference variables v to a map that maps integers z to terms that are equivalent to *(v + z).

     - `diseq` are the disequalities between the new representatives.

     - `bldis` are the block disequalities between the new representatives.

      Throws "Unsat" if a contradiction is found.
      This does NOT update the disequalities.
      They need to be updated with `congruence_neq`.
  *)
  let closure cc conjs =
    match cc with
    | None -> None
    | Some cc ->
      let (uf, map, new_repr) = closure (cc.uf, cc.map, TMap.empty) conjs in
      let bldis = update_bldis new_repr cc.bldis in
      Some {uf; set = cc.set; map; min_repr=cc.min_repr; diseq=cc.diseq; bldis=bldis}

  (** Adds the block disequalities to the cc, but first rewrites them such that
      they are disequalities between representatives. The cc should already contain
      all the terms that are present in those block disequalities.
  *)
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

  (** Add a term to the data structure.

      Returns (reference variable, offset), updated congruence closure *)
  let rec insert cc t =
    if SSet.mem t cc.set then
      let v,z,uf = TUF.find cc.uf t in
      (v,z), Some {cc with uf}
    else
      match t with
      | Addr _ | Aux _ -> let uf = TUF.ValMap.add t ((t, Z.zero),1) cc.uf in
        let set = SSet.add t cc.set in
        (t, Z.zero), Some {cc with uf; set;}
      | Deref (t', z, exp) ->
        match insert cc t' with
        | (v, r), None -> (v, r), None
        | (v, r), Some cc ->
          let set = SSet.add t cc.set in
          match LMap.map_find_opt (v, Z.(r + z)) cc.map with
          | Some v' -> let v2,z2,uf = TUF.find cc.uf v' in
            let uf = LMap.add t ((t, Z.zero),1) uf in
            (v2,z2), closure (Some {uf; set; map = LMap.map_add (v, Z.(r + z)) t cc.map;min_repr=cc.min_repr; diseq = cc.diseq; bldis=cc.bldis}) [(t, v', Z.zero)]
          | None -> let map = LMap.map_add (v, Z.(r + z)) t cc.map in
            let uf = LMap.add t ((t, Z.zero),1) cc.uf in
            (t, Z.zero), Some {uf; set; map; min_repr=cc.min_repr; diseq = cc.diseq; bldis=cc.bldis}

  (** Add a term to the data structure.

        Returns (reference variable, offset), updated congruence closure *)
  let insert cc t =
    match cc with
    | None -> (t, Z.zero), None
    | Some cc -> let (r, z), cc = insert cc t in
      (r, z), congruence_neq_opt cc []

  (** Add all terms in a specific set to the data structure.

      Returns updated cc. *)
  let insert_set cc t_set =
    SSet.fold (fun t cc -> snd (insert cc t)) t_set cc

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

  let block_neq_query cc (t1,t2) =
    (* we implicitly assume that &x != &y + z *)
    let (v1,r1),cc = insert cc t1 in
    let (v2,r2),cc = insert cc t2 in
    match cc with
    | None -> true
    | Some cc -> BlDis.map_set_mem v1 v2 cc.bldis

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
          BlDis.map_set_mem v1 v2 cc.bldis ||
          (*explicit dsequalities*)
          Disequalities.map_set_mem (v2,Z.(r2-r1+r)) v1 cc.diseq

  (** Adds equalities to the data structure.
      Throws "Unsat" if a contradiction is found.
      Does not update disequalities. *)
  let meet_pos_conjs cc pos_conjs =
    let res = let cc = insert_set cc (fst (SSet.subterms_of_conj pos_conjs)) in
      closure cc pos_conjs
    in if M.tracing then M.trace "c2po-meet" "MEET_CONJS RESULT: %s\n" (Option.map_default (fun res -> show_conj (get_conjunction res)) "None" res);res

  (** Adds propositions to the data structure.
      Returns None if a contradiction is found. *)
  let meet_conjs_opt conjs cc =
    let pos_conjs, neg_conjs, bl_conjs = split conjs in
    let terms_to_add = (fst (SSet.subterms_of_conj (neg_conjs @ List.map(fun (t1,t2)->(t1,t2,Z.zero)) bl_conjs))) in
    match add_normalized_bl_diseqs (insert_set (meet_pos_conjs cc pos_conjs) terms_to_add) bl_conjs with
    | exception Unsat -> None
    | Some cc -> congruence_neq cc neg_conjs
    | None -> None

  (** Add proposition t1 = t2 + r to the data structure.
      Does not update the disequalities. *)
  let add_eq cc (t1, t2, r) =
    let (v1, r1), cc = insert cc t1 in
    let (v2, r2), cc = insert cc t2 in
    let cc = closure cc [v1, v2, Z.(r2 - r1 + r)] in
    cc

  (** adds block disequalities to cc:
      fo each representative t in cc it adds the disequality bl(lterm) != bl(t)*)
  let add_block_diseqs cc lterm =
    match cc with
    | None -> cc
    | Some cc ->
      let bldis = BlDis.add_block_diseqs cc.bldis cc.uf lterm (TUF.get_representatives cc.uf) in
      Some {cc with bldis}

  (* Remove variables: *)
  let remove_terms_from_eq predicate cc =
    let insert_terms cc = List.fold (fun cc t -> snd (insert cc t)) cc in
    (* start from all initial states that are still valid and find new representatives if necessary *)
    (* new_reps maps each representative term to the new representative of the equivalence class *)
    (*but new_reps contains an element but not necessarily the representative!!*)
    let find_new_repr state old_rep old_z new_reps =
      match LMap.find_opt old_rep new_reps with
      | Some (new_rep,z) -> new_rep, Z.(old_z - z), new_reps
      | None -> if not @@ predicate old_rep then
          old_rep, old_z, TMap.add old_rep (old_rep, Z.zero) new_reps else (*we keep the same representative as before*)
          (* the representative need to be removed from the data structure: state is the new repr.*)
          state, Z.zero, TMap.add old_rep (state, old_z) new_reps in
    let add_atom (new_reps, new_cc, reachable_old_reps) state =
      let old_rep, old_z = TUF.find_no_pc cc.uf state in
      let new_rep, new_z, new_reps = find_new_repr state old_rep old_z new_reps in
      let new_cc = insert_terms new_cc [state; new_rep] in
      let new_cc = closure new_cc [(state, new_rep, new_z)] in
      (new_reps, new_cc, (old_rep, new_rep, Z.(old_z - new_z))::reachable_old_reps)
    in
    let new_reps, new_cc, reachable_old_reps =
      SSet.fold_atoms (fun acc x -> if (not (predicate x)) then add_atom acc x else acc) (TMap.empty, (Some init_cc),[]) cc.set in
    let cmap = Disequalities.comp_map cc.uf in
    (* breadth-first search of reachable states *)
    let add_transition (old_rep, new_rep, z1) (new_reps, new_cc, reachable_old_reps) (s_z,s_t) =
      let old_rep_s, old_z_s = TUF.find_no_pc cc.uf s_t in
      let find_successor_in_set (z, term_set) =
        let exception Found in
        let res = ref None in
        try
          TSet.iter (fun t ->
              match SSet.deref_term t Z.(s_z-z) cc.set with
              | exception (T.UnsupportedCilExpression _) -> ()
              | successor -> if (not @@ predicate successor) then
                  (res := Some successor; raise Found)
                else
                  ()
            ) term_set; !res
        with Found -> !res
      in
      (* find successor term -> find any  element in equivalence class that can be dereferenced *)
      match List.find_map_opt find_successor_in_set (ZMap.bindings @@ TMap.find old_rep cmap) with
      | Some successor_term -> if (not @@ predicate successor_term && T.check_valid_pointer (T.to_cil successor_term)) then
          let new_cc = insert_terms new_cc [successor_term] in
          match LMap.find_opt old_rep_s new_reps with
          | Some (new_rep_s,z2) -> (* the successor already has a new representative, therefore we can just add it to the lookup map*)
            new_reps, closure new_cc [(successor_term, new_rep_s, Z.(old_z_s-z2))], reachable_old_reps
          | None -> (* the successor state was not visited yet, therefore we need to find the new representative of the state.
                       -> we choose a successor term *(t+z) for any
                       -> we need add the successor state to the list of states that still need to be visited
                    *)
            TMap.add old_rep_s (successor_term, old_z_s) new_reps, new_cc, (old_rep_s, successor_term, old_z_s)::reachable_old_reps
        else
          (new_reps, new_cc, reachable_old_reps)
      | None ->
        (* the term cannot be dereferenced, so we won't add this transition. *)
        (new_reps, new_cc, reachable_old_reps)
    in
    (* find all successors that are still reachable *)
    let rec add_transitions new_reps new_cc = function
      | [] -> new_reps, new_cc
      | (old_rep, new_rep, z)::rest ->
        let successors = LMap.successors old_rep cc.map in
        let new_reps, new_cc, reachable_old_reps =
          List.fold (add_transition (old_rep, new_rep,z)) (new_reps, new_cc, []) successors in
        add_transitions new_reps new_cc (rest@reachable_old_reps)
    in add_transitions new_reps new_cc
      (List.unique_cmp ~cmp:(Tuple3.compare ~cmp1:(T.compare) ~cmp2:(T.compare) ~cmp3:(Z.compare)) reachable_old_reps)

  (** Find the representative term of the equivalence classes of an element that has already been deleted from the data structure.
      Returns None if there are no elements in the same equivalence class as t before it was deleted.*)
  let find_new_root new_reps uf v =
    match TMap.find_opt v new_reps with
    | None -> None
    | Some (new_t, z1) ->
      let t_rep, z2 = TUF.find_no_pc uf new_t in
      Some (t_rep, Z.(z2-z1))

  let remove_terms_from_diseq diseq new_reps cc =
    let disequalities = Disequalities.get_disequalities diseq
    in
    let add_disequality new_diseq = function
      | Nequal(t1,t2,z) ->
        begin match find_new_root new_reps cc.uf t1,find_new_root new_reps cc.uf t2 with
          | Some (t1',z1'), Some (t2', z2') -> (t1', t2', Z.(z2'+z-z1'))::new_diseq
          | _ -> new_diseq
        end
      | _-> new_diseq
    in
    let new_diseq = List.fold add_disequality [] disequalities
    in congruence_neq cc new_diseq

  let remove_terms_from_bldis bldis new_reps cc =
    let disequalities = BlDis.to_conj bldis
    in
    let add_bl_dis new_diseq = function
      | BlNequal (t1,t2) ->
        begin match find_new_root new_reps cc.uf t1,find_new_root new_reps cc.uf t2 with
          | Some (t1',z1'), Some (t2', z2') -> BlDis.add_block_diseq new_diseq (t1', t2')
          | _ -> new_diseq
        end
      | _-> new_diseq
    in
    List.fold add_bl_dis BlDis.empty disequalities

  (** Remove terms from the data structure.
      It removes all terms for which "predicate" is false,
      while maintaining all equalities about variables that are not being removed.*)
  let remove_terms predicate cc =
    let old_cc = cc in
    match remove_terms_from_eq predicate {cc with min_repr=None} with
    | new_reps, Some cc ->
      let bldis = remove_terms_from_bldis old_cc.bldis new_reps cc in
      remove_terms_from_diseq old_cc.diseq new_reps {cc with bldis}
    | _,None -> None

  (* join version 1: by using the automaton *)

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
    let pmap,cc,working_set = List.fold_left add_term (Map.empty, Some init_cc,[]) mappings in
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

  (* join version 2: just look at equivalence classes and not the automaton. *)

  let product_no_automata_over_terms cc1 cc2 terms =
    let cc1, cc2 = Option.get (insert_set (Some cc1) terms), Option.get (insert_set (Some cc2) terms) in
    let mappings = List.map
        (fun a -> let r1, off1 = TUF.find_no_pc cc1.uf a in
          let r2, off2 = TUF.find_no_pc cc2.uf a in
          (r1,r2,Z.(off2 - off1)), (a,off1)) (SSet.to_list terms) in
    let add_term (cc, pmap) (new_element, (new_term, a_off)) =
      match Map.find_opt new_element pmap with
      | None -> cc, Map.add new_element (new_term, a_off) pmap
      | Some (c, c1_off) ->
        add_eq cc (new_term, c, Z.(-c1_off + a_off)), pmap in
    List.fold_left add_term (Some init_cc, Map.empty) mappings

  (** Here we do the join without using the automata, because apparently
      we don't want to describe the automaton in the paper...

      We construct a new cc that contains the elements of cc1.set U cc2.set
      and two elements are in the same equivalence class iff they are in the same eq. class
      both in cc1 and in cc2. *)
  let join_eq_no_automata cc1 cc2 =
    let terms = SSet.union cc1.set cc2.set in
    product_no_automata_over_terms cc1 cc2 terms

  (** Same as join, but we only take the terms from the left argument. *)
  let widen_eq_no_automata cc1 cc2 =
    product_no_automata_over_terms cc1 cc2 cc1.set

  (** Joins the disequalities diseq1 and diseq2, given a congruence closure data structure.

      This is done by checking for each disequality if it is implied by both cc. *)
  let join_neq diseq1 diseq2 cc1 cc2 cc cmap1 cmap2 =
    let _,diseq1,_ = split (Disequalities.get_disequalities diseq1) in
    let _,diseq2,_ = split (Disequalities.get_disequalities diseq2) in
    (* keep all disequalities from diseq1 that are implied by cc2 and
       those from diseq2 that are implied by cc1 *)
    let diseq1 = List.filter (neq_query (Some cc2)) (Disequalities.element_closure diseq1 cmap1 cc.uf) in
    let diseq2 = List.filter (neq_query (Some cc1)) (Disequalities.element_closure diseq2 cmap2 cc.uf) in
    let cc = Option.get (insert_set (Some cc) (fst @@ SSet.subterms_of_conj (diseq1 @ diseq2))) in
    let res = congruence_neq cc (diseq1 @ diseq2)
    in (if M.tracing then match res with | Some r -> M.trace "c2po-neq" "join_neq: %s\n\n" (Disequalities.show_neq r.diseq) | None -> ()); res

  (** Joins the block disequalities bldiseq1 and bldiseq2, given a congruence closure data structure.

      This is done by checing for each block disequality if it is implied by both cc. *)
  let join_bldis bldiseq1 bldiseq2 cc1 cc2 cc cmap1 cmap2 =
    let bldiseq1 = BlDis.to_conj bldiseq1 in
    let bldiseq2 = BlDis.to_conj bldiseq2 in
    (* keep all disequalities from diseq1 that are implied by cc2 and
       those from diseq2 that are implied by cc1 *)
    let diseq1 = List.filter (block_neq_query (Some cc2)) (BlDis.element_closure bldiseq1 cmap1 cc.uf) in
    let diseq2 = List.filter (block_neq_query (Some cc1)) (BlDis.element_closure bldiseq2 cmap2 cc.uf) in
    let cc = Option.get (insert_set (Some cc) (fst @@ SSet.subterms_of_conj (List.map (fun (a,b) -> (a,b,Z.zero)) (diseq1 @ diseq2)))) in
    let diseqs_ref_terms = List.filter (fun (t1,t2) -> TUF.is_root cc.uf t1 && TUF.is_root cc.uf t2) (diseq1 @ diseq2) in
    let bldis = List.fold BlDis.add_block_diseq BlDis.empty diseqs_ref_terms
    in (if M.tracing then M.trace "c2po-neq" "join_bldis: %s\n\n" (show_conj (BlDis.to_conj bldis)));
    {cc with bldis}

  (* Check for equality of two congruence closures,
     by comparing the equivalence classes instead of computing the minimal_representative. *)

  (** Compares the equivalence classes of cc1 and those of cc2. *)
  let equal_eq_classes cc1 cc2 =
    let comp1, comp2 = Disequalities.comp_map cc1.uf, Disequalities.comp_map cc2.uf in
    (* they should have the same number of equivalence classes *)
    if TMap.cardinal comp1 <> TMap.cardinal comp2 then false else
      (* compare each equivalence class of cc1 with the corresponding eq. class of cc2 *)
      let compare_zmap_entry offset zmap2 (z, tset1) =
        match ZMap.find_opt Z.(z+offset) zmap2 with
        | None -> false
        | Some tset2 -> SSet.equal tset1 tset2
      in
      let compare_with_cc2_eq_class (rep1, zmap1) =
        let rep2, offset = TUF.find_no_pc cc2.uf rep1 in
        let zmap2 = TMap.find rep2 comp2 in
        if ZMap.cardinal zmap2 <> ZMap.cardinal zmap1 then false else
          List.for_all (compare_zmap_entry offset zmap2) (ZMap.bindings zmap1)
      in
      List.for_all compare_with_cc2_eq_class (TMap.bindings comp1)

  let equal_diseqs cc1 cc2 =
    let normalize_diseqs (min_state1, min_state2, new_offset) =
      if T.compare min_state1 min_state2 < 0 then Nequal (min_state1, min_state2, new_offset)
      else Nequal (min_state2, min_state1, Z.(-new_offset)) in
    let rename_diseqs dis = match dis with
      | Nequal (t1,t2,z) ->
        let (min_state1, min_z1) = TUF.find_no_pc cc2.uf t1 in
        let (min_state2, min_z2) = TUF.find_no_pc cc2.uf t2 in
        let new_offset = Z.(min_z2 - min_z1 + z) in
        normalize_diseqs (min_state1, min_state2, new_offset)
      | _ -> dis in
    let renamed_diseqs = BatList.sort_unique (T.compare_v_prop) @@
      List.map rename_diseqs (Disequalities.get_disequalities cc1.diseq) in
    let normalized_diseqs = BatList.sort_unique (T.compare_v_prop) @@
      List.filter_map (function | Nequal (t1,t2,z) -> Some (normalize_diseqs(t1,t2,z))
                                | _ -> None) (Disequalities.get_disequalities cc2.diseq) in
    List.equal T.equal_v_prop renamed_diseqs normalized_diseqs

  let equal_bldis cc1 cc2 =
    let normalize_bldis (min_state1, min_state2) =
      if T.compare min_state1 min_state2 < 0 then BlNequal (min_state1, min_state2)
      else BlNequal (min_state2, min_state1) in
    let rename_bldis dis = match dis with
      | BlNequal (t1,t2) ->
        let min_state1, _ = TUF.find_no_pc cc2.uf t1 in
        let min_state2, _ = TUF.find_no_pc cc2.uf t2 in
        normalize_bldis (min_state1, min_state2)
      | _ -> dis in
    let renamed_diseqs = BatList.sort_unique (T.compare_v_prop) @@
      List.map rename_bldis (BlDis.to_conj cc1.bldis) in
    let normalized_diseqs = BatList.sort_unique (T.compare_v_prop) @@
      List.map (function | Nequal (t1,t2,_) | Equal(t1,t2,_) | BlNequal (t1,t2)
          -> (normalize_bldis(t1,t2))) (BlDis.to_conj cc2.bldis) in
    List.equal T.equal_v_prop renamed_diseqs normalized_diseqs
end


(**Find out if two addresses are not equal by using the MayPointTo query*)
module MayBeEqual = struct
  open CongruenceClosure

  module AD = Queries.AD
  let dummy_varinfo typ: varinfo = {dummyFunDec.svar with vid=(-1);vtype=typ;vname="c2po__@dummy"}
  let dummy_var var = T.aux_term_of_varinfo (dummy_varinfo var)
  let dummy_lval var = Lval (Var (dummy_varinfo var), NoOffset)

  let return_varinfo typ = {dummyFunDec.svar with vtype=typ;vid=(-2);vname="c2po__@return"}
  let return_var var = T.aux_term_of_varinfo (return_varinfo var)
  let return_lval var = Lval (Var (return_varinfo var), NoOffset)

  let ask_may_point_to (ask: Queries.ask) exp =
    match ask.f (MayPointTo exp) with
    | exception (IntDomain.ArithmeticOnIntegerBot _) -> AD.top ()
    | res -> res

  let may_point_to_all_equal_terms ask exp cc term offset =
    let equal_terms = if TMap.mem term cc.uf then
        let comp = Disequalities.comp_t cc.uf term in
        let valid_term (t,z) =
          T.is_ptr_type (T.type_of_term t) && (T.get_var t).vid > 0 in
        List.filter valid_term comp
      else [(term,Z.zero)]
    in
    if M.tracing then M.trace "c2po-query" "may-point-to %a -> equal terms: %s"
        d_exp exp (List.fold (fun s (t,z) -> s ^ "(" ^ T.show t ^","^ Z.to_string Z.(z + offset) ^")") "" equal_terms);
    let intersect_query_result res (term,z) =
      let next_query =
        match ask_may_point_to ask (T.to_cil_sum Z.(z + offset) (T.to_cil term)) with
        | exception (T.UnsupportedCilExpression _) -> AD.top()
        | res -> if AD.is_bot res then AD.top() else res
      in
      match AD.meet res next_query with
      | exception (IntDomain.ArithmeticOnIntegerBot _) -> res
      | result -> result
    in
    List.fold intersect_query_result (AD.top()) equal_terms

  (**Find out if two addresses are possibly equal by using the MayPointTo query. *)
  let may_point_to_address (ask:Queries.ask) adresses t2 off cc =
    match T.to_cil_sum off (T.to_cil t2) with
    | exception (T.UnsupportedCilExpression _) -> true
    | exp2 ->
      let mpt1 = adresses in
      let mpt2 = may_point_to_all_equal_terms ask exp2 cc t2 off in
      let res = try not (AD.is_bot (AD.meet mpt1 mpt2))
        with IntDomain.ArithmeticOnIntegerBot _ -> true
      in
      if M.tracing then M.tracel "c2po-maypointto2" "QUERY MayPointTo. \nres: %a;\nt2: %s; exp2: %a; res: %a; \nmeet: %a; result: %s\n"
          AD.pretty mpt1 (T.show t2) d_plainexp exp2 AD.pretty mpt2 AD.pretty (try AD.meet mpt1 mpt2 with IntDomain.ArithmeticOnIntegerBot _ -> AD.bot ()) (string_of_bool res); res

  let may_point_to_same_address (ask:Queries.ask) t1 t2 off cc =
    if T.equal t1 t2 then true else
      let exp1 = T.to_cil t1 in
      let mpt1 = may_point_to_all_equal_terms ask exp1 cc t1 Z.zero in
      let res = may_point_to_address ask mpt1 t2 off cc in
      if M.tracing && res then M.tracel "c2po-maypointto2" "QUERY MayPointTo. \nres: %a;\nt1: %s; exp1: %a;\n"
          AD.pretty mpt1 (T.show t1) d_plainexp exp1; res

  let rec may_be_equal ask cc s t1 t2 =
    let there_is_an_overlap s s' diff =
      if Z.(gt diff zero) then Z.(lt diff s') else Z.(lt (-diff) s)
    in
    match t1, t2 with
    | Deref (t, z,_), Deref (v, z',_) ->
      let (q', z1') = TUF.find_no_pc cc.uf v in
      let (q, z1) = TUF.find_no_pc cc.uf t in
      let s' = T.get_size t2 in
      let diff = Z.(-z' - z1 + z1' + z) in
      (* If they are in the same equivalence class and they overlap, then they are equal *)
      (if T.equal q' q && there_is_an_overlap s s' diff then true
       else
         (* If we have a disequality, then they are not equal *)
       if neq_query (Some cc) (t,v,Z.(z'-z)) then false else
         (* or if we know that they are not equal according to the query MayPointTo*)
       if GobConfig.get_bool "ana.c2po.askbase" then (may_point_to_same_address ask t v Z.(z' - z) cc)
       else true)
      || (may_be_equal ask cc s t1 v)
    | Deref _, _ -> false (* The value of addresses or auxiliaries never change when we overwrite the memory*)
    | Addr _ , _ | Aux _, _ -> T.is_subterm t1 t2

  (**Returns true iff by assigning to t1, the value of t2 could change.
     The parameter s is the size in bits of the variable t1 we are assigning to. *)
  let may_be_equal ask cc s t1 t2 =
    match cc with
    | None -> false
    | Some cc ->
      let res = (may_be_equal ask cc s t1 t2) in
      if M.tracing then M.tracel "c2po-maypointto" "MAY BE EQUAL: %s %s: %b\n" (T.show t1) (T.show t2) res;
      res

  let rec may_point_to_one_of_these_adresses ask adresses cc t2 =
    match t2 with
    |  Deref (v, z',_) ->
      (may_point_to_address ask adresses v z' cc)
      || (may_point_to_one_of_these_adresses ask adresses cc v)
    | Addr _ -> false
    | Aux (v,e) -> may_point_to_address ask adresses (Addr v) Z.zero cc

end
