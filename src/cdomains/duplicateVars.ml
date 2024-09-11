(** Used by C2poDomain and StartStateAnalysis.
    Contains functions to duplicate variables in order to have shadow variables for each function parameter,
    that can be used to remeber the initial value of these parameters.
    It uses RichVarinfo to create the duplicated variables. *)
open CilType
open GoblintCil
open Batteries
open GoblintCil
module M = Messages

(** Variable Type used by the C-2PO  Analysis.
    It contains normal variables with a varinfo as well as auxiliary variables for
    assignment and return and duplicated variables for remembering the value of variables at the beginning of a function. *)
module VarType = struct
  (* the hash/compare values should not depend on the type.
     But they have to be defined even though they are not used, for some reason.*)
  let equal_typ a b = Stdlib.compare a b = 0
  let hash_typ x = Hashtbl.hash x
  let compare_typ a b = Stdlib.compare a b

  type t = AssignAux of typ
         | ReturnAux of typ
         | NormalVar of Varinfo.t
         | DuplicVar of Varinfo.t [@@deriving eq,ord,hash]

  let from_varinfo normal duplicated =
    List.map (fun v -> NormalVar v) normal @ List.map (fun v -> DuplicVar v) duplicated

  let show v = match v with
    | AssignAux t -> "AuxAssign"
    | ReturnAux t -> "AuxReturn"
    | NormalVar v -> v.vname
    | DuplicVar v -> "c2po__" ^ v.vname ^ "'"

  let get_type v = match v with
    | AssignAux t | ReturnAux t -> t
    | NormalVar v | DuplicVar v -> v.vtype

  let is_assign_aux = function | AssignAux _ -> true | _ -> false
  let is_return_aux = function | ReturnAux _ -> true | _ -> false

  let varinfo_attributes v =
    let open RichVarinfo.VarinfoDescription in
    match v with
    | AssignAux t -> ({(empty "AuxAssign") with vtype_=Some t})
    | ReturnAux t -> ({(empty "AuxReturn") with vtype_=Some t})
    | NormalVar v -> from_varinfo v
    | DuplicVar v -> ({(from_varinfo v) with vname_="c2po__" ^ string_of_int v.vid ^ "'"})

  (* Description that gets appended to the varinfo-name in user output. *)
  let describe_varinfo (var: varinfo) v =
    show v
end

module VarVarinfoMap = RichVarinfo.BiVarinfoMap.Make(VarType)

module Var =
struct
  include VarType
  let dummy_varinfo typ: varinfo = VarVarinfoMap.to_varinfo (AssignAux typ)
  let return_varinfo typ = VarVarinfoMap.to_varinfo (ReturnAux typ)
  let to_varinfo v =
    let res = VarVarinfoMap.to_varinfo v in
    if M.tracing then M.trace "c2po-varinfo" "to_varinfo: %a -> %a" d_type (get_type v) d_type res.vtype;
    res


end
