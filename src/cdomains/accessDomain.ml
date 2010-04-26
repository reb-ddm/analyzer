open Cil
open Lval
open Pretty


type pth = Base  of (varinfo * (fieldinfo, int64) offs) option
         | Deref of pth * (fieldinfo, int64) offs
         | Star  of pth


module Path = 
struct
  type t = pth option

  include Lattice.StdCousot
  
  let name () = "Path"
  
  let rec eq_offs x y = 
    match x, y with
      | `NoOffset, `NoOffset -> true
      | `Index (i,o), `Index (j,u) when i=j -> eq_offs o u
      | `Field (f1,o), `Field (f2,u) when f1.fcomp.ckey=f2.fcomp.ckey && f1.fname = f2.fname -> eq_offs o u
      | _ -> false
  
  let rec equal' x y = 
    match x, y with
      | Base     b1, Base  b2    -> b1 = b2
      | Deref (x,o), Deref (y,i) -> eq_offs o i && equal' x y
      | Star x     , Star y      ->          equal' x y
      | _ -> false
 
  let rec equal x y =
    match x, y with
      | None  , None   -> true
      | Some x, Some y -> equal' x y
      | _ -> false
    
  let hash (x:t) = Hashtbl.hash x
  let compare (x:t) (y:t) = Pervasives.compare x y
  
  let isSimple _ = true
  let short n x =
    let rec offs_short tt x = 
      match x with 
        | `NoOffset -> ""
        | `Index (x,o) -> "[" ^ (Int64.to_string x) ^ "]" ^ (offs_short true o) 
        | `Field (x,o) -> (if tt then "." else "") ^ (x.fname) ^ (offs_short true o) 
    in
    let rec to_str x =
      match x with 
        | Base (Some (x, o)) -> x.vname  ^ offs_short true o
        | Base None          -> "*" 
        | Deref (x,o)        -> to_str x ^ "->" ^ offs_short false o
        | Star x             -> to_str x ^ "->*"
    in
    match x with
      | None -> ".L"
      | Some x -> to_str x
   
  let pretty_f sf () x = Pretty.text (sf 80 x)
  let pretty = pretty_f short
  
  let toXML_f sf x = Xml.Element ("Leaf", [("text", sf 80 x)],[]) 
  let toXML = toXML_f short
  
  let why_not_leq () (x,y) = 
    Pretty.dprintf "%s: %a not leq %a" (name ()) pretty x pretty y
    
  let top ()   = Some (Base None)
  let is_top x = Some (Base None) = x
  
  let bot ()   = None 
  let is_bot x = None = x
  
  
  let rec leq' x y =
    match x, y with
      | Base (Some (x,o)), Base (Some (y,i)) -> x.vid=y.vid&& eq_offs o i 
      | _        , Base None -> true   
      | Base None, _         -> false
      | _        , Base _    -> false
      | Base (Some _), Deref (x,i) -> false
      | Base (Some x), Star y    -> leq' (Base (Some x)) y      
      | Deref (x,o)  , Deref (y,i) -> eq_offs i o && leq' x y
      | Star x       , Star y      -> List.exists (fun (x,y) -> leq' x y) [x,y;x,Star y]   
      | Star x       , Deref (y,i) -> false
      | Deref (x,o)  , Star y      -> List.exists (fun (x,y) -> leq' x y) [x,y;x,Star y]

  let leq x y =
    match x, y with
      | Some x, Some y -> leq' x y
      | None  , _      -> true
      | _     , None   -> false 
       
  let rec min x =
    match x with
      | [] -> failwith "incorrect use of PathDomain.min --- argument must be longer than one" 
      | [x] -> x
      | x::y::ys -> if leq' x y then min (x::ys) else min  (y::ys) 
  
  let join x y =
    let add_star x =
      match x with
        | Base None -> Base None
        | Star x -> Star x
        | x      -> Star x
    in
    let rec join' x y =
      match x, y with
        | Base (Some (x,o)), Base (Some (y,i)) 
          when eq_offs o i&&x.vid=y.vid -> Base (Some (x,o))
        | Base x, Deref (y,_) -> add_star (join' (Base x) y)
        | Deref (x,_), Base y -> add_star (join' x (Base y))
        | Base x, Star y -> add_star (join' (Base x) y)
        | Star x, Base y -> add_star (join' x (Base y))
        | Deref (x,o) , Deref (y,i) when eq_offs i o -> add_star (join' x y)
        | Deref (x,_), Star y -> add_star (min [join' x y; join' x (Star y)])
        | Star  x, Deref (y,_)-> add_star (min [join' x y; join' x (Star y)])
        | Star  x, Star y -> min [join' x y; join' x (Star y); join' (Star x) y]
        | _ -> Base None
    in
    let r = 
    match x, y with
      | Some x, Some y -> Some (join' x y)
      | None  , y      -> y
      | x     , None   -> x
    in
    (*Messages.report (short 80 x ^ " `join` " ^ short 80 y ^ " = " ^ short 80 r ); *)r

  
  let meet' x y = failwith "PathDomain not implemented"

  let meet x y =
    match x, y with
      | Some x, Some y -> Some (meet' x y)
      | _ -> None
      
  let from_lval (lv:lval) : t =
    let rec offs_from_cil o =
      match o with
        | NoOffset    -> `NoOffset
        | Field (f,o) -> `Field (f,offs_from_cil o)
        | Index (i,o) -> `Index (0L, offs_from_cil o)
    in 
    match lv with
      | Var x, o -> Some (Base (Some (x,offs_from_cil o)))
      | Mem e, o -> bot ()
  
  (*todo: deal with offsets*)
  let rec subst_base_var x (v,o) y =
    let rec subst_base_var' x y =
      match x with
        | Base (Some (v',o')) when v.vid = v'.vid && eq_offs o o' -> y  
        | Base x -> Base x
        | Deref (x,o) -> Deref (subst_base_var' x y, o)
        | Star x -> Star (subst_base_var' x y)      
    in
    match x, y with
      | Some x, Some y -> Some (subst_base_var' x y) 
      | _ -> None 

  
  let rec from_exp (e:exp) : t =
    let rec offs_from_cil o =
      match o with
        | NoOffset    -> `NoOffset
        | Field (f,o) -> `Field (f,offs_from_cil o)
        | Index (i,o) -> `Index (0L, offs_from_cil o)
    in 
    match e with
      | Cil.SizeOf _
      | Cil.SizeOfE _
      | Cil.SizeOfStr _
      | Cil.AlignOf _  
      | Cil.AlignOfE _
      | Cil.UnOp  _    
      | Cil.BinOp _ 
      | Cil.Const _ -> top ()
      | Cil.AddrOf  (Cil.Var v,o) 
      | Cil.StartOf (Cil.Var v,o) 
      | Cil.Lval    (Cil.Var v,o) -> Some (Base (Some (v,offs_from_cil o)))
      | Cil.AddrOf  (Cil.Mem e,o) 
      | Cil.StartOf (Cil.Mem e,o) 
      | Cil.Lval    (Cil.Mem e,o) ->
          begin match from_exp e with
            | None -> Some (Deref (Base None,offs_from_cil o))
            | Some x -> Some (Deref (x,offs_from_cil o))
          end
      | Cil.CastE (_,e)           -> from_exp e 
end


module Access =
struct 
  module Lvals = Lval.Normal (IntDomain.Integers)
  module Map  = MapDomain.MapTop (Lval.Normal (IntDomain.Integers)) (Path)
  module Accs = SetDomain.ToppedSet (Path) (struct let topname = "totally unsound" end)
  include Lattice.LiftBot (Lattice.Prod3 (Map) (Accs) (Accs))
  
  let startstate () : t = `Lifted (Map.top (), Accs.bot (), Accs.bot ())
  
  let lift_fun (f:Map.t -> Map.t) (mp:t) : t = 
    match mp with
    | `Bot -> `Bot
    | `Lifted (mp,a,b) ->  `Lifted (f mp,a,b)

  let rec const_equal c1 c2 =
    match c1, c2 with
      | CStr s1  , CStr s2   -> s1 = s2
      | CWStr is1, CWStr is2 -> is1 = is2
      | CChr c1  , CChr c2   -> c1 = c2
      | CInt64 (v1,k1,_), CInt64 (v2,k2,_) -> v1 = v2 && k1 = k2
      | CReal (f1,k1,_) , CReal (f2,k2,_)  -> f1 = f2 && k1 = k2
      | CEnum (_,n1,e1), CEnum (_,n2,e2) -> n1 = n2 && e1.ename = e2.ename  
      | _ -> false

  let option_eq f x y =
    match x, y with
      | Some x, Some y -> f x y
      | None, None -> true
      | _ -> false 
  
  let rec typ_equal t1 t2 =
    let args_eq (s1,t1,_) (s2,t2,_) = s1 = s2 && typ_equal t1 t2 in
    let eitem_eq (s1,e1,l1) (s2,e2,l2) = s1 = s2 && l1 = l2 && exp_equal e1 e2 in
    match t1, t2 with
      | TVoid _, TVoid _ -> true
      | TInt (k1,_), TInt (k2,_) -> k1 = k2
      | TFloat (k1,_), TFloat (k2,_) -> k1 = k2
      | TPtr (t1,_), TPtr (t2,_) -> typ_equal t1 t2
      | TArray (t1,d1,_), TArray (t2,d2,_) -> option_eq exp_equal d1 d2 && typ_equal t1 t2
      | TFun (rt1, arg1, _,  b1), TFun (rt2, arg2, _, b2) -> b1 = b2 && typ_equal rt1 rt2 && option_eq (List.for_all2 args_eq) arg1 arg2
      | TNamed (ti1, _), TNamed (ti2, _) -> ti1.tname = ti2.tname && typ_equal ti1.ttype ti2.ttype
      | TComp (c1,_), TComp (c2,_) -> c1.ckey = c2.ckey
      | TEnum (e1,_), TEnum (e2,_) -> e1.ename = e2.ename & List.for_all2 eitem_eq e1.eitems e2.eitems 
      | TBuiltin_va_list _, TBuiltin_va_list _ -> true
      | _ -> false

  and lval_equal (l1,o1) (l2,o2) =
    let rec offs_equal o1 o2 =
      match o1, o2 with
        | NoOffset, NoOffset -> true
        | Field (f1, o1), Field (f2,o2) -> f1.fcomp.ckey = f2.fcomp.ckey && f1.fname = f2.fname && offs_equal o1 o2
        | Index (i1,o1), Index (i2,o2) -> exp_equal i1 i2 && offs_equal o1 o2   
        | _ -> false     
    in
       offs_equal o1 o2 
    && match l1, l2 with
         | Var v1, Var v2 -> v1.vid = v2.vid
         | Mem m1, Mem m2 -> exp_equal m1 m2
         | _ -> false
  
  and exp_equal e1 e2 =
    match e1, e2 with
      | Const c1, Const c2 -> const_equal c1 c2
      | AddrOf l1,  AddrOf l2   
      | StartOf l1, StartOf l2 
      | Lval l1 , Lval  l2 -> lval_equal l1 l2
      | SizeOf t1,  SizeOf t2 -> typ_equal t1 t2
      | SizeOfE e1, SizeOfE e2 -> exp_equal e1 e2  
      | SizeOfStr s1, SizeOfStr s2 -> s1 = s2
      | AlignOf t1, AlignOf t2 -> typ_equal t1 t2
      | AlignOfE e1,  AlignOfE e2 -> exp_equal e1 e2
      | UnOp (o1,e1,t1),  UnOp (o2,e2,t2) -> o1 = o2 && typ_equal t1 t2 && exp_equal e1 e2
      | BinOp (o1,e11,e21,t1),  BinOp(o2,e12,e22,t2) -> o1 = o2 && typ_equal t1 t2 && exp_equal e11 e12 && exp_equal e21 e22     
      | CastE (t1,e1),  CastE (t2,e2) -> typ_equal t1 t2 && exp_equal e1 e2
      | _ -> false
      
  (* kill predicate for must-equality kind of analyses*)
  let may_change_t (b:exp) (a:exp) : bool =
    let rec type_may_change_t a bt =
      let rec may_change_t_offset o =
        match o with  
          | NoOffset -> false
          | Index (e,o) -> type_may_change_t e bt || may_change_t_offset o
          | Field (_,o) -> may_change_t_offset o
      in
      let at = typeOf a in
      (isIntegralType at && isIntegralType bt) || (typ_equal at bt) ||
      match a with
        | Cil.Const _ 
        | Cil.SizeOf _
        | Cil.SizeOfE _
        | Cil.SizeOfStr _
        | Cil.AlignOf _  
        | Cil.AlignOfE _ -> false
        | Cil.UnOp (_,e,_) -> type_may_change_t e bt      
        | Cil.BinOp (_,e1,e2,_) -> type_may_change_t e1 bt || type_may_change_t e2 bt
        | Cil.Lval (Cil.Var _,o) 
        | Cil.AddrOf (Cil.Var _,o)              
        | Cil.StartOf (Cil.Var _,o) -> may_change_t_offset o
        | Cil.Lval (Cil.Mem e,o)    
        | Cil.AddrOf (Cil.Mem e,o)  
        | Cil.StartOf (Cil.Mem e,o) -> may_change_t_offset o || type_may_change_t e bt
        | Cil.CastE (t,e) -> type_may_change_t e bt
    in
    let bt =  unrollTypeDeep (typeOf b) in
    type_may_change_t a bt
    
  let may_change_pt ask (b:exp) (a:exp) : bool =
    let pt e = 
      match ask (Queries.MayPointTo e) with
        | `LvalSet ls -> ls
        | _ -> Queries.LS.top ()
    in
    let rec lval_may_change_pt a bl : bool =
      let rec may_change_pt_offset o =
        match o with  
          | NoOffset -> false
          | Index (e,o) -> lval_may_change_pt e bl || may_change_pt_offset o
          | Field (_,o) -> may_change_pt_offset o
      in
      let als = pt a in
      Queries.LS.is_top als || Queries.LS.mem bl als ||
      match a with
        | Cil.Const _ 
        | Cil.SizeOf _
        | Cil.SizeOfE _
        | Cil.SizeOfStr _
        | Cil.AlignOf _  
        | Cil.AlignOfE _ -> false
        | Cil.UnOp (_,e,_) -> lval_may_change_pt e bl      
        | Cil.BinOp (_,e1,e2,_) -> lval_may_change_pt e1 bl || lval_may_change_pt e2 bl
        | Cil.Lval (Cil.Var _,o) 
        | Cil.AddrOf (Cil.Var _,o)              
        | Cil.StartOf (Cil.Var _,o) -> may_change_pt_offset o
        | Cil.Lval (Cil.Mem e,o)    
        | Cil.AddrOf (Cil.Mem e,o)  
        | Cil.StartOf (Cil.Mem e,o) -> may_change_pt_offset o || lval_may_change_pt e bl 
        | Cil.CastE (t,e) -> lval_may_change_pt e bl
    in 
    let bls = pt b in
    if Queries.LS.is_top bls
    then true
    else Queries.LS.exists (lval_may_change_pt a) bls
  
  let may_change ask (b:exp) (a:exp) : bool =
    (*b should be an address of something that changes*)
    let pt e = 
      match ask (Queries.MayPointTo e) with
        | `LvalSet ls -> ls
        | _ -> Queries.LS.top ()
    in
    let bls = pt b in
    let bt = 
      match unrollTypeDeep (typeOf b) with
        | TPtr (t,_) -> t
        | _ -> voidType
    in (* type of thing that changed: typeof( *b ) *)
    let rec type_may_change_apt a = 
      (* With abstract points-to (like in type invariants in accesses). 
         Here we implement it in part --- minimum to protect local integers. *)
       match a, b with
         | Cil.Lval (Cil.Var _,NoOffset), Cil.AddrOf (Cil.Mem(Cil.Lval _),Field(_, NoOffset)) -> 
            (* lval *.field changes -> local var stays the same *)
            false
         | _ -> 
            type_may_change_t false a
    and type_may_change_t deref a =
      let rec may_change_t_offset o =
        match o with  
          | NoOffset -> false
          | Index (e,o) -> type_may_change_apt e || may_change_t_offset o
          | Field (_,o) -> may_change_t_offset o
      in
      let at = 
        match unrollTypeDeep (typeOf a) with
          | TPtr (t,a) -> t
          | at -> at 
      in
(*      Messages.report 
        ( sprint 80 (d_type () at)
        ^ " : "
        ^ sprint 80 (d_type () bt)
        ^ (if bt = voidType || (isIntegralType at && isIntegralType bt) || (deref && typ_equal (TPtr (at,[]) ) bt) || typ_equal at bt then ": yes" else ": no"));
*)      bt = voidType || (isIntegralType at && isIntegralType bt) || (deref && typ_equal (TPtr (at,[]) ) bt) || typ_equal at bt ||
      match a with
        | Cil.Const _ 
        | Cil.SizeOf _
        | Cil.SizeOfE _
        | Cil.SizeOfStr _
        | Cil.AlignOf _  
        | Cil.AlignOfE _ -> false
        | Cil.UnOp (_,e,_) -> type_may_change_t deref e      
        | Cil.BinOp (_,e1,e2,_) -> type_may_change_t deref e1 || type_may_change_t deref e2
        | Cil.Lval (Cil.Var _,o) 
        | Cil.AddrOf (Cil.Var _,o)              
        | Cil.StartOf (Cil.Var _,o) -> may_change_t_offset o
        | Cil.Lval (Cil.Mem e,o)    -> (*Messages.report "Lval" ;*) may_change_t_offset o || type_may_change_t true e    
        | Cil.AddrOf (Cil.Mem e,o)  -> (*Messages.report "Addr" ;*) may_change_t_offset o || type_may_change_t false e  
        | Cil.StartOf (Cil.Mem e,o) -> (*Messages.report "Start";*) may_change_t_offset o || type_may_change_t false e
        | Cil.CastE (t,e) -> type_may_change_t deref e 
    
    and lval_may_change_pt a bl : bool =
      let rec may_change_pt_offset o =
        match o with  
          | NoOffset -> false
          | Index (e,o) -> lval_may_change_pt e bl || may_change_pt_offset o
          | Field (_,o) -> may_change_pt_offset o
      in
      let rec addrOfExp e = 
        match e with
          | Cil.Lval    (Cil.Var v,o) -> Some (AddrOf (Var v,o)) 
          | Cil.AddrOf  (Cil.Var _,_) -> None              
          | Cil.StartOf (Cil.Var _,_) -> None
          | Cil.Lval    (Cil.Mem e,o) -> Some (AddrOf (Mem e, o)) 
          | Cil.AddrOf  (Cil.Mem e,o) -> (match addrOfExp e with Some e -> Some (AddrOf (Mem e, o)) | x -> x)
          | Cil.StartOf (Cil.Mem e,o) -> (match addrOfExp e with Some e -> Some (AddrOf (Mem e, o)) | x -> x)
          | Cil.CastE   (t,e) -> addrOfExp e
          | _ -> None
      in      
      let lval_is_not_disjoint (v,o) als = 
        let rec oleq o s = 
          match o, s with
            | `NoOffset, _ -> true
            | `Field (f1,o), `Field (f2,s) when f1.fname = f2.fname -> oleq o s
            | `Index (i1,o), `Index (i2,s) when exp_equal i1 i2     -> oleq o s
            | _ -> false
        in
        if Queries.LS.is_top als
        then false
        else Queries.LS.exists (fun (u,s) ->  v.vid = u.vid && oleq o s) als
      in
      let (als, test) = 
      match addrOfExp a with
        | None -> (Queries.LS.bot (), false)
        | Some e -> 
            let als = pt e in 
            (als, lval_is_not_disjoint bl als)   
      in
(*      Messages.report 
        ( sprint 80 (Lval.CilLval.pretty () bl)
        ^ " in PT("
        ^ sprint 80 (d_exp () a)
        ^ ") = "
        ^ sprint 80 (Queries.LS.pretty () als)
        ^ (if Queries.LS.is_top als || test then ": yes" else ": no"));
*)      if (Queries.LS.is_top als) 
      then type_may_change_apt a 
      else test ||
      match a with
        | Cil.Const _ 
        | Cil.SizeOf _
        | Cil.SizeOfE _
        | Cil.SizeOfStr _
        | Cil.AlignOf _  
        | Cil.AlignOfE _ -> false
        | Cil.UnOp (_,e,_) -> lval_may_change_pt e bl      
        | Cil.BinOp (_,e1,e2,_) -> lval_may_change_pt e1 bl || lval_may_change_pt e2 bl
        | Cil.Lval (Cil.Var _,o) 
        | Cil.AddrOf (Cil.Var _,o)              
        | Cil.StartOf (Cil.Var _,o) -> may_change_pt_offset o
        | Cil.Lval (Cil.Mem e,o)    
        | Cil.AddrOf (Cil.Mem e,o)  
        | Cil.StartOf (Cil.Mem e,o) -> may_change_pt_offset o || lval_may_change_pt e bl 
        | Cil.CastE (t,e) -> lval_may_change_pt e bl
    in 
    let r =
    if Queries.LS.is_top bls
    then ((*Messages.report "No PT-set: switching to types ";*) type_may_change_apt a)
    else Queries.LS.exists (lval_may_change_pt a) bls
    in
(*    if r 
    then (Messages.report ("Kill " ^sprint 80 (Exp.pretty () a)^" because of "^sprint 80 (Exp.pretty () b)); r)
    else (Messages.report ("Keep " ^sprint 80 (Exp.pretty () a)^" because of "^sprint 80 (Exp.pretty () b)); r) 
    Messages.report (sprint 80 (Exp.pretty () b) ^" changed lvalues: "^sprint 80 (Queries.LS.pretty () bls)); 
*)    r
  
  let toXML_f sf x = 
    match toXML x with
      | Xml.Element (node, _, 
          [ Xml.Element (_, _, elems)
          ; Xml.Element (sn, _, ss)
          ; Xml.Element (tn, _, ts)]) 
        -> 
            Xml.Element (node, ["text", "Accesses"], 
              [ Xml.Element (sn, ["text", "Reads"], ss)
              ; Xml.Element (tn, ["text", "Writes"], ts)]
              @ elems)
      | x -> x
      
  let toXML s = toXML_f short s 
  
  exception AccPathBot
  (* extend the Base as long as possible *)
  let max_path (p : Path.t) mp : Path.t =
    let rec max_path' p mp =
      match p with
        | Base None          -> Base  None 
        | Deref (x,o)        -> Deref (max_path' x mp, o)
        | Star x             -> Star  (max_path' x mp)
        | Base (Some (x, o)) -> 
            match Map.find (Lvals.from_var_offset (x,o)) mp with
              | Some (Base None) -> Base (Some (x,o))
              | Some xp -> max_path' xp mp
              | None -> raise AccPathBot
    in
    try match p with
      | Some p -> Some (max_path' p mp)
      | None   -> None
    with AccPathBot -> None
    
  (*todo: kill when prefix matches*)
  let kill' v mp = Map.remove v mp
  let kill v = lift_fun (kill' v)

  (* Remove elements, that would change if the given lval would change.*)
  let remove_exp' ask (e:exp) (st:Map.t) : Map.t =
    let filter_key fn mp =
      let takeNotFn k v xs =
        if fn k
        then kill' k xs
        else xs
      in
      Map.fold takeNotFn mp mp
    in
    filter_key (fun x -> may_change ask e (Lvals.to_exp (kinteger64 IInt) x)) st

  let remove_exp ask e = lift_fun (remove_exp' ask e)

  (* remove *-s from right hand sides in the map *)
  let kill_tops' mp =
    let rem_top k v m =
      if Path.is_top v
      then m
      else Map.add k v m
    in
    Map.fold rem_top mp (Map.top ())
  let kill_tops = lift_fun kill_tops'

  (* normalize --- remove *-s from right hand sides *)
  let join x y = 
(*    print_endline (Pretty.sprint 80 (Pretty.dprintf "join: \n%a U\n%a\n\n" pretty  x pretty  y));*)
    kill_tops (join x y)

  (* Modifies path-map to set lhs = rhs.  If lhs \in rhs then then lhs is replaced  
     in rhs with its(lhs) previous value.*)
  let assign' ask (lhs:lval) (rhs:exp) (mp:Map.t) : Map.t =
    let rec offs_from_cil o =
      match o with
        | NoOffset    -> `NoOffset
        | Field (f,o) -> `Field (f,offs_from_cil o)
        | Index (i,o) -> `Index (0L, offs_from_cil o)
    in 
    let get_val lv mp : pth option =
      try Map.find lv mp
      with Not_found -> Path.top ()
    in
    match lhs with
      | (Var v,o) when v.vglob -> 
        let rlv = (v, offs_from_cil o) in
        let lv = Lvals.from_var_offset rlv in 
        kill' lv mp
      | (Var v,o) -> 
        begin
          let rlv = (v, offs_from_cil o) in
          let lv = Lvals.from_var_offset rlv in 
          let new_val = Path.subst_base_var (Path.from_exp rhs) rlv (get_val lv mp) in
          let r = 
            if Path.is_top new_val
            then kill' lv mp
            else Map.add lv new_val mp
          in
(*           print_endline (Pretty.sprint 80 (Pretty.dprintf "assign %s <- %a \n%a \n = \n%a\n" v.vname Path.pretty new_val Map.pretty mp Map.pretty r)); *)
          r
        end
      | (Mem e, o) -> 
        let v = remove_exp' ask (mkAddrOf lhs) mp in
(*         print_endline (Pretty.sprint 80 (Pretty.dprintf "assign %a \n %a \n = \n%a\n" d_lval lhs Map.pretty mp Map.pretty v)); *)
        v
    
  let assign ask (lhs:lval) (rhs:exp) : t -> t = lift_fun (assign' ask lhs rhs)
  
  (* set access sets to empty *)
  let reset_accs (x : t) : t =
    match x with
      | `Bot -> `Bot
      | `Lifted (m,_,_) -> `Lifted (m,Accs.empty (),Accs.empty ())
  
  (* recursively add accesses to state *)
  let rec add_accsess exp read st : t =
    let exp = stripCasts exp in
    let f (mp:Map.t) (st:Accs.t) : Accs.t =
      let acc = Path.from_exp exp in
      let typ = if read then "Read access from " else "Write access to " in
      Messages.report (":: "^typ^Path.short 80 (max_path acc mp));
      Accs.add acc st
    in
    let rec add_idx o st =
      match o with
        | NoOffset -> st
        | Field (_,o) -> add_idx o st
        | Index (i,o) -> add_idx o (add_accsess i true st)
    in
    let add_next st =
      match exp with
        | Cil.UnOp  (_,e,_) -> add_accsess e true st
        | Cil.BinOp (_,e1,e2,_) -> add_accsess e1 true (add_accsess e2 true st)
        | Cil.AddrOf  (Cil.Var v2,o) 
        | Cil.StartOf (Cil.Var v2,o) 
        | Cil.Lval    (Cil.Var v2,o) -> add_idx o st
        | Cil.AddrOf  (Cil.Mem e,o) 
        | Cil.StartOf (Cil.Mem e,o) 
        | Cil.Lval    (Cil.Mem e,o) -> add_idx o (add_accsess e true st)
        | _ -> st
    in
    if isConstant exp 
    then st
    else match st, read with
      | `Bot, _ -> `Bot
      | `Lifted (m,a,b), true  -> add_next (`Lifted (m,f m a,b)) 
      | `Lifted (m,a,b), false -> add_next (`Lifted (m,a,f m b))    
    
end
