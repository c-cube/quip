
(** {1 Kernel of trust} *)

open Common

module H = CCHash
module Log = (val Logs.src_log (Logs.Src.create "quip.kernel"))

let ctx_id_bits = 5
let ctx_id_mask = (1 lsl ctx_id_bits) - 1

type location = Loc.t

module Name : sig
  type t = private string
  val make : string -> t
  val equal_str : t -> string -> bool
  include EQ with type t := t
  include COMPARE with type t := t
  include HASH with type t := t
  include PP with type t := t
end = struct
  type t = string
  let equal = String.equal
  let equal_str = equal
  let compare = String.compare
  let hash = H.string
  let pp = Fmt.string
  let make s = s
  let to_string s = s
end


type expr_view =
  | E_kind
  | E_type
  | E_var of var
  | E_bound_var of bvar
  | E_const of const * expr list
  | E_app of expr * expr
  | E_lam of string * expr * expr
  | E_not of expr
  | E_arrow of expr * expr

and expr = {
  e_view: expr_view;
  e_ty: expr option lazy_t;
  mutable e_id: int;
  mutable e_flags: int; (* ̵contains: [higher DB var | 1:has free vars | 5:ctx uid] *)
}

and var = {
  v_name: string;
  v_ty: ty;
}
and ty_var = var

and bvar = {
  bv_idx: int;
  bv_ty: ty;
}

and ty = expr

and name = Name.t

and const = {
  c_name: name;
  c_args: const_args;
  c_ty: ty; (* free vars = c_ty_vars *)
  c_def_id: const_def_id;
  c_def_loc: location option;
}
and ty_const = const

and const_def_id =
  | C_def_gen of int (* generative *)
  | C_in_theory of name (* theory name *)

and const_args =
  | C_ty_vars of ty_var list
  | C_arity of int (* for type constants *)

let[@inline] expr_eq (e1:expr) e2 : bool = e1 == e2
let[@inline] expr_hash (e:expr) = H.int e.e_id
let[@inline] expr_compare (e1:expr) e2 : int = CCInt.compare e1.e_id e2.e_id
let[@inline] expr_db_depth e = e.e_flags lsr (1+ctx_id_bits)
let[@inline] expr_has_fvars e = ((e.e_flags lsr ctx_id_bits) land 1) == 1
let[@inline] expr_ctx_uid e : int = e.e_flags land ctx_id_mask

let[@inline] var_eq v1 v2 = v1.v_name = v2.v_name && expr_eq v1.v_ty v2.v_ty
let[@inline] var_hash v1 = H.combine3 5 (H.string v1.v_name) (expr_hash v1.v_ty)
let[@inline] var_pp out v1 = Fmt.string out v1.v_name

let const_def_eq a b =
  match a, b with
  | C_def_gen i, C_def_gen j -> i=j
  | C_in_theory n1, C_in_theory n2 -> Name.equal n1 n2
  | (C_def_gen _ | C_in_theory _), _ -> false

let[@inline] const_eq (c1:const) c2 : bool =
  Name.equal c1.c_name c2.c_name &&
  const_def_eq c1.c_def_id c2.c_def_id

let const_hash c =
  let h_def =
    match c.c_def_id with
    | C_def_gen id -> H.(combine2 12 (int id))
    | C_in_theory n -> H.(combine2 25 (Name.hash n))
  in
  H.combine3 129 (Name.hash c.c_name) h_def

module Const_hashcons = Hashcons.Make(struct
    type t = const
    let equal = const_eq
    let hash = const_hash
    let set_id _ _ = ()
    let on_new _ = ()
  end)

module Expr_set = CCSet.Make(struct
    type t = expr
    let compare = expr_compare
    end)

(* open an application *)
let unfold_app (e:expr) : expr * expr list =
  let rec aux acc e =
    match e.e_view with
    | E_app (f, a) -> aux (a::acc) f
    | _ -> e, acc
  in
  aux [] e

let __pp_ids = ref false

(* debug printer *)
let expr_pp_with_ ~max_depth out (e:expr) : unit =
  let rec loop k ~depth names out e =
    let pp = loop k ~depth:(depth+1) names in
    let pp' = loop' k ~depth:(depth+1) names in
    (match e.e_view with
    | E_kind -> Fmt.string out "kind"
    | E_type -> Fmt.string out "type"
    | E_var v -> Fmt.string out v.v_name
    (* | E_var v -> Fmt.fprintf out "(@[%s : %a@])" v.v_name pp v.v_ty *)
    | E_bound_var v ->
      let idx = v.bv_idx in
      begin match CCList.nth_opt names idx with
        | Some n when n<>"" -> Fmt.string out n
        | _ ->
          if idx<k then Fmt.fprintf out "x_%d" (k-idx-1)
          else Fmt.fprintf out "%%db_%d" (idx-k)
      end
    | E_const (c,[]) -> Name.pp out c.c_name
    | E_const (c,args) ->
      Fmt.fprintf out "(@[%a@ %a@])" Name.pp c.c_name (pp_l pp') args
    | (E_app _ | E_lam _ | E_arrow _) when depth > max_depth ->
      Fmt.fprintf out "@<1>…/%d" e.e_id
    | E_app _ ->
      let f, args = unfold_app e in
      begin match f.e_view, args with
        | E_const (c, [_]), [a;b] when Name.equal_str c.c_name "=" ->
          Fmt.fprintf out "@[@[%a@]@ = @[%a@]@]" pp' a pp' b
        | _ ->
          Fmt.fprintf out "%a@ %a" pp' f (pp_l pp') args
      end
    | E_not u -> Fmt.fprintf out "(@[not@ %a@])" pp' u
    | E_lam ("", _ty, bod) ->
      Fmt.fprintf out "(@[\\x_%d:@[%a@].@ %a@])" k pp' _ty
        (loop (k+1) ~depth:(depth+1) (""::names)) bod
    | E_lam (n, _ty, bod) ->
      Fmt.fprintf out "(@[\\%s:@[%a@].@ %a@])" n pp' _ty
        (loop (k+1) ~depth:(depth+1) (n::names)) bod
    | E_arrow(a,b) ->
      Fmt.fprintf out "@[@[%a@]@ -> %a@]" pp' a pp b
    );
    if !__pp_ids then Fmt.fprintf out "/%d" e.e_id;

  and loop' k ~depth names out e = match e.e_view with
    | E_kind | E_type | E_var _ | E_bound_var _ | E_const (_, []) ->
      loop k ~depth names out e (* atomic expr *)
    | _ -> Fmt.fprintf out "(%a)" (loop k ~depth names) e
  in
  Fmt.fprintf out "@[%a@]" (loop 0 ~depth:0 []) e

let expr_pp_ = expr_pp_with_ ~max_depth:max_int

module Expr_hashcons = Hashcons.Make(struct
    type t = expr

    let equal a b =
      begin match a.e_view, b.e_view with
        | E_kind, E_kind
        | E_type, E_type -> true
        | E_const (c1,l1), E_const (c2,l2) ->
          Name.equal c1.c_name c2.c_name && CCList.equal expr_eq l1 l2
        | E_var v1, E_var v2 -> var_eq v1 v2
        | E_bound_var v1, E_bound_var v2 ->
          v1.bv_idx = v2.bv_idx && expr_eq v1.bv_ty v2.bv_ty
        | E_app (f1,a1), E_app (f2,a2) ->
          expr_eq f1 f2 && expr_eq a1 a2
        | E_lam (_,ty1,bod1), E_lam (_,ty2,bod2) ->
          expr_eq ty1 ty2 && expr_eq bod1 bod2
        | E_arrow(a1,b1), E_arrow(a2,b2) ->
          expr_eq a1 a2 && expr_eq b1 b2
        | E_not u1, E_not u2 -> expr_eq u1 u2
        | (E_kind | E_type | E_const _ | E_var _ | E_bound_var _
          | E_app _ | E_lam _ | E_arrow _ | E_not _), _ -> false
      end

    let hash e : int =
      match e.e_view with
      | E_kind -> 11
      | E_type -> 12
      | E_const (c,l) ->
        H.combine4 20 (Name.hash c.c_name) (expr_hash c.c_ty) (H.list expr_hash l)
      | E_var v -> H.combine2 30 (var_hash v)
      | E_bound_var v -> H.combine3 40 (H.int v.bv_idx) (expr_hash v.bv_ty)
      | E_app (f,a) -> H.combine3 50 (expr_hash f) (expr_hash a)
      | E_lam (_,ty,bod) ->
        H.combine3 60 (expr_hash ty) (expr_hash bod)
      | E_arrow (a,b) -> H.combine3 80 (expr_hash a) (expr_hash b)
      | E_not u -> H.combine2 90 (expr_hash u)

    let set_id t id =
      assert (t.e_id == -1);
      t.e_id <- id

    let on_new e = ignore (Lazy.force e.e_ty : _ option)
    end)

type const_kind = C_ty | C_term

(* special map for indexing constants, differentiating type and term constants *)
module Str_k_map = CCMap.Make(struct
    type t = const_kind * string
    let compare (k1,c1)(k2,c2) =
      if k1=k2 then String.compare c1 c2 else CCOrd.poly k1 k2
  end)

type thm = {
  th_concl: expr;
  th_hyps: Expr_set.t;
  mutable th_flags: int; (* [bool flags|ctx uid] *)
  mutable th_theory: theory option;
}
(* TODO:
   - store set of axioms used
   *)

and theory = {
  theory_name: Name.t;
  theory_ctx: ctx;
  mutable theory_in_constants: const Str_k_map.t;
  mutable theory_in_theorems: thm list;
  mutable theory_defined_constants: const Str_k_map.t;
  mutable theory_defined_theorems: thm list;
}

and ctx = {
  ctx_uid: int;
  ctx_exprs: Expr_hashcons.t;
  ctx_consts: Const_hashcons.t;
  ctx_kind: expr lazy_t;
  ctx_type: expr lazy_t;
  ctx_bool: expr lazy_t;
  ctx_bool_c: const lazy_t;
  ctx_eq_c: const lazy_t;
  ctx_select_c : const lazy_t;
  mutable ctx_axioms: thm list;
  mutable ctx_axioms_allowed: bool;
}
(* TODO: derived rules and named rules/theorems *)

let[@inline] thm_ctx_uid th : int = th.th_flags land ctx_id_mask

let[@inline] ctx_check_e_uid ctx (e:expr) = assert (ctx.ctx_uid == expr_ctx_uid e)
let[@inline] ctx_check_th_uid ctx (th:thm) = assert (ctx.ctx_uid == thm_ctx_uid th)

let id_bool = Name.make "bool"
let id_eq = Name.make "="
let id_select = Name.make "select"

module Const = struct
  type t = const
  let[@inline] pp out c = Name.pp out c.c_name
  let[@inline] to_string c = Fmt.to_string pp c
  let[@inline] def_loc c = c.c_def_loc
  let[@inline] name c = c.c_name
  let[@inline] equal c1 c2 = Name.equal c1.c_name c2.c_name

  type args = const_args =
    | C_ty_vars of ty_var list
    | C_arity of int
  let[@inline] args c = c.c_args
  let[@inline] ty c = c.c_ty

  let pp_args out = function
    | C_arity n -> Fmt.fprintf out "/%d" n
    | C_ty_vars vs -> Fmt.fprintf out " %a" (Fmt.Dump.list var_pp) vs

  let pp_with_ty out c =
    Fmt.fprintf out "`@[%a%a@ : %a@]`"
      Name.pp c.c_name pp_args c.c_args expr_pp_ c.c_ty

  let[@inline] eq ctx = Lazy.force ctx.ctx_eq_c
  let[@inline] bool ctx = Lazy.force ctx.ctx_bool_c
  let[@inline] select ctx = Lazy.force ctx.ctx_select_c
  let is_eq_to_bool c = Name.equal c.c_name id_bool
  let is_eq_to_eq c = Name.equal c.c_name id_bool

  let[@inline] make_ ctx (c:t) : t =
    Const_hashcons.hashcons ctx.ctx_consts c
end

module Var = struct
  type t = var

  let[@inline] name v = v.v_name
  let[@inline] ty v = v.v_ty
  let[@inline] map_ty v ~f = {v with v_ty=f v.v_ty}
  let make v_name v_ty : t = {v_name; v_ty}
  let makef fmt ty = Fmt.kasprintf (fun s->make s ty) fmt
  let equal = var_eq
  let hash = var_hash
  let pp = var_pp
  let pp_with_ty out v =
    Fmt.fprintf out "(@[%s :@ %a@])" v.v_name expr_pp_ v.v_ty
  let to_string = Fmt.to_string pp
  let compare a b : int =
    if expr_eq a.v_ty b.v_ty
    then String.compare a.v_name b.v_name
    else expr_compare a.v_ty b.v_ty

  module AsKey = struct
    type nonrec t = t
    let equal = equal
    let compare = compare
    let hash = hash
  end

  module Map = CCMap.Make(AsKey)
  module Set = CCSet.Make(AsKey)
  module Tbl = CCHashtbl.Make(AsKey)
end

type subst = {
  ty: expr Var.Map.t; (* ty subst *)
  m: expr Var.Map.t; (* term subst *)
}

module BVar = struct
  type t = bvar
  let make i ty : t = {bv_idx=i; bv_ty=ty}
  let pp out v = Fmt.fprintf out "db_%d" v.bv_idx
  let to_string = Fmt.to_string pp
end

module type EXPR = sig
  type t = expr

  type view = expr_view =
    | E_kind
    | E_type
    | E_var of var
    | E_bound_var of bvar
    | E_const of const * t list
    | E_app of t * t
    | E_lam of string * expr * expr
    | E_not of expr
    | E_arrow of expr * expr

  include EQ with type t := t
  include HASH with type t := t
  include COMPARE with type t := t
  include PP with type t := t

  val pp_depth : max_depth:int -> t Fmt.printer
  (** Print the term and insert ellipsis in subterms above given depth.
      Useful to print very deep terms *)

  val view : t -> view
  val ty : t -> ty option
  val ty_exn : t -> ty
  val is_closed : t -> bool
  val is_eq_to_type : t -> bool
  val is_eq_to_bool : t -> bool
  val is_a_bool : t -> bool
  val is_a_type : t -> bool
  (** Is the type of [e] equal to [Type]? *)

  val iter : f:(bool -> t -> unit) -> t -> unit
  val exists : f:(bool -> t -> bool) -> t -> bool
  val for_all : f:(bool -> t -> bool) -> t -> bool

  val contains : t -> sub:t -> bool
  val free_vars : ?init:Var.Set.t -> t -> Var.Set.t
  val free_vars_iter : t -> var Iter.t

  val unfold_app : t -> t * t list
  val unfold_eq : t -> (t * t) option
  val unfold_arrow : t -> t list * t
  val unfold_not : t -> t option

  val return_ty : t -> t
  val as_const : t -> (Const.t * ty list) option
  val as_const_exn : t -> Const.t * ty list

  module Set : CCSet.S with type elt = t
  module Map : CCMap.S with type key = t
  module Tbl : CCHashtbl.S with type key = t

  val iter_dag : f:(t -> unit) -> t -> unit

  type 'a with_ctx

  val subst : (recursive:bool -> t -> subst -> t) with_ctx

  val type_ : (t) with_ctx
  val bool : (t) with_ctx
  val eq : (ty -> t) with_ctx
  val select : (ty -> t) with_ctx
  val var : (var -> t) with_ctx
  val const : (const -> ty list -> t) with_ctx
  val new_const : (?def_loc:location -> string -> ty_var list -> ty -> const) with_ctx
  val new_ty_const : (?def_loc:location -> string -> int -> const) with_ctx
  val var_name : (string -> ty -> t) with_ctx
  val bvar : (int -> ty -> t) with_ctx
  val app : (t -> t -> t) with_ctx
  val app_l : (t -> t list -> t) with_ctx
  val app_eq : (t -> t -> t) with_ctx
  val lambda : (var -> t -> t) with_ctx
  val lambda_l : (var list -> t -> t) with_ctx
  val lambda_db : (name:string -> ty_v:ty -> t -> t) with_ctx
  val arrow : (t -> t -> t) with_ctx
  val arrow_l : (t list -> t -> t) with_ctx
  val not_ : (t -> t) with_ctx

  val map : (f:(bool -> t -> t) -> t -> t) with_ctx

  val db_shift: (t -> int -> t) with_ctx
  val open_lambda : (t -> (var * t) option) with_ctx
  val open_lambda_exn : (t -> var * t) with_ctx
end

module Expr = struct
  type t = expr

  type view = expr_view =
    | E_kind
    | E_type
    | E_var of var
    | E_bound_var of bvar
    | E_const of const * expr list
    | E_app of t * t
    | E_lam of string * t * t
    | E_not of expr
    | E_arrow of t * t

  let[@inline] ty e = Lazy.force e.e_ty
  let[@inline] view e = e.e_view
  let[@inline] ty_exn e = match e.e_ty with
    | lazy None -> assert false
    | lazy (Some ty) -> ty

  let equal = expr_eq
  let hash = expr_hash

  let pp = expr_pp_
  let to_string = Fmt.to_string pp
  let pp_depth = expr_pp_with_

  let compare = expr_compare
  let db_depth = expr_db_depth
  let has_fvars = expr_has_fvars

  let[@inline] iter ~f (e:t) : unit =
    match view e with
    | E_kind | E_type | E_const _ -> ()
    | _ ->
      CCOpt.iter (f false) (ty e);
      match view e with
      | E_kind | E_type | E_const _ -> assert false
      | E_var v -> f false v.v_ty
      | E_bound_var v -> f false v.bv_ty
      | E_app (hd,a) -> f false hd; f false a
      | E_lam (_, tyv, bod) -> f false tyv; f true bod
      | E_not u -> f false u
      | E_arrow (a,b) -> f false a; f false b

  exception E_exit

  let[@inline] exists ~f e : bool =
    try
      iter e ~f:(fun b x -> if f b x then raise_notrace E_exit); false
    with E_exit -> true

  let[@inline] for_all ~f e : bool =
    try
      iter e ~f:(fun b x -> if not (f b x) then raise_notrace E_exit); true
    with E_exit -> false

  let[@inline] is_closed e : bool = db_depth e == 0

  let compute_db_depth_ e : int =
    let d1 = match ty e with
      | None -> 0
      | Some d -> db_depth d
    in
    let d2 = match view e with
      | E_kind | E_type | E_const _ | E_var _ -> 0
      | E_bound_var v -> v.bv_idx+1
      | E_app (a,b) | E_arrow (a,b) -> max (db_depth a) (db_depth b)
      | E_not u -> db_depth u
      | E_lam (_, ty,bod) ->
        max (db_depth ty) (max 0 (db_depth bod - 1))
    in
    max d1 d2

  let compute_has_fvars_ e : bool =
    begin match ty e with
      | None -> false
      | Some ty -> has_fvars ty
    end ||
    begin match view e with
      | E_var _ -> true
      | E_kind | E_type | E_bound_var _ -> false
      | E_const (_, args) -> List.exists has_fvars args
      | E_app (a,b) | E_arrow (a,b) -> has_fvars a || has_fvars b
      | E_not u -> has_fvars u
      | E_lam (_,ty,bod) -> has_fvars ty || has_fvars bod
    end

  (* hashconsing + computing metadata *)
  let make_ (ctx:ctx) view ty : t =
    let e = { e_view=view; e_ty=ty; e_id= -1; e_flags=0 } in
    let e_h = Expr_hashcons.hashcons ctx.ctx_exprs e in
    if e == e_h then (
      (* new term, compute metadata *)
      assert ((ctx.ctx_uid land ctx_id_mask) == ctx.ctx_uid);
      let has_fvars = compute_has_fvars_ e in
      e_h.e_flags <-
        ((compute_db_depth_ e) lsl (1+ctx_id_bits))
        lor (if has_fvars then 1 lsl ctx_id_bits else 0)
        lor ctx.ctx_uid;
      ctx_check_e_uid ctx e_h;
    );
    e_h

  let kind ctx = Lazy.force ctx.ctx_kind
  let type_ ctx = Lazy.force ctx.ctx_type

  let[@inline] is_eq_to_type e = match view e with | E_type -> true | _ -> false
  let[@inline] is_a_type e = is_eq_to_type (ty_exn e)
  let is_eq_to_bool e =
    match view e with E_const (c,[]) -> Name.equal c.c_name id_bool | _ -> false
  let is_a_bool e = is_eq_to_bool (ty_exn e)

  let bool ctx = Lazy.force ctx.ctx_bool

  let var ctx v : t =
    ctx_check_e_uid ctx v.v_ty;
    make_ ctx (E_var v) (Lazy.from_val (Some v.v_ty))

  let var_name ctx s ty : t = var ctx {v_name=s; v_ty=ty}

  let bvar ctx i ty : t =
    assert (i>=0);
    ctx_check_e_uid ctx ty;
    make_ ctx (E_bound_var {bv_idx=i; bv_ty=ty}) (Lazy.from_val (Some ty))

  (* map immediate subterms *)
  let[@inline] map ctx ~f (e:t) : t =
    match view e with
    | E_kind | E_type | E_const (_,[]) -> e
    | _ ->
      let ty' = lazy (
        match e.e_ty with
        | lazy None -> None
        | lazy (Some ty) -> Some (f false ty)
      ) in
      begin match view e with
        | E_var v ->
          let v_ty = f false v.v_ty in
          if v_ty == v.v_ty then e
          else make_ ctx (E_var {v with v_ty}) ty'
        | E_const (c,args) ->
          let args' = List.map (f false) args in
          if List.for_all2 equal args args'
          then e
          else make_ ctx (E_const (c,args')) ty'
        | E_bound_var v ->
          let ty' = f false v.bv_ty in
          if v.bv_ty == ty' then e
          else make_ ctx (E_bound_var {v with bv_ty=ty'}) (Lazy.from_val (Some ty'))
        | E_app (hd,a) ->
          let hd' =  f false hd in
          let a' =  f false a in
          if a==a' && hd==hd' then e
          else make_ ctx (E_app (f false hd, f false a)) ty'
        | E_lam (n, tyv, bod) ->
          let tyv' = f false tyv in
          let bod' = f true bod in
          if tyv==tyv' && bod==bod' then e
          else make_ ctx (E_lam (n, tyv', bod')) ty'
        | E_not u ->
          let u' = f false u in
          if u==u' then e
          else make_ ctx (E_not u') ty'
        | E_arrow (a,b) ->
          let a' = f false a in
          let b' = f false b in
          if a==a' && b==b' then e
          else make_ ctx (E_arrow (a', b')) ty'
        | E_kind | E_type -> assert false
      end

  exception IsSub

  let contains e ~sub : bool =
    let rec aux e =
      if equal e sub then raise_notrace IsSub;
      iter e ~f:(fun _ u -> aux u)
    in
    try aux e; false with IsSub -> true

  let free_vars_iter e : var Iter.t =
    fun yield ->
      let rec aux e =
        match view e with
        | E_var v -> yield v; aux (Var.ty v)
        | E_const (_, args) -> List.iter aux args
        | _ -> iter e ~f:(fun _ u -> aux u)
      in
      aux e

  let free_vars ?(init=Var.Set.empty) e : Var.Set.t =
    let set = ref init in
    free_vars_iter e (fun v -> set := Var.Set.add v !set);
    !set

  let id_gen_ = ref 0 (* note: updated atomically *)

  let new_const_ ctx ?def_loc ?in_theory
      name args ty : const =
    let c_def_id = match in_theory with
      | Some th -> C_in_theory th.theory_name
      | None -> incr id_gen_; C_def_gen !id_gen_
    in
    let c = {
      c_name=name; c_def_id; c_ty=ty; c_args=args;
      c_def_loc=def_loc;
    } in
    Const.make_ ctx c

  let new_const ctx ?def_loc name ty_vars ty : const =
    let fvars = free_vars ty in
    let diff = Var.Set.diff fvars (Var.Set.of_list ty_vars) in
    begin match Var.Set.choose_opt diff with
      | None -> ()
      | Some v ->
        Error.failf
          "Kernel.new_const: type variable %a@ \
           occurs in type of the constant `%s`,@ \
           but not in the type variables %a"
          Var.pp v name (Fmt.Dump.list Var.pp) ty_vars
    end;
    let name = Name.make name in
    new_const_ ctx ?def_loc name (C_ty_vars ty_vars) ty

  let new_ty_const ctx ?def_loc name n : ty_const =
    let name = Name.make name in
    new_const_ ctx name ?def_loc (C_arity n) (type_ ctx)

  let mk_const_ ctx c args ty : t =
    make_ ctx (E_const (c,args)) ty

  let subst_empty_ : subst =
    {ty=Var.Map.empty;
     m=Var.Map.empty;
    }

  let subst_pp_ out (self:subst) : unit =
    if Var.Map.is_empty self.m && Var.Map.is_empty self.ty then (
      Fmt.string out "{}"
    ) else (
      let pp_b out (v,t) =
        Fmt.fprintf out "(@[%a := %a@])" Var.pp_with_ty v expr_pp_ t
      in
      Fmt.fprintf out "@[<hv>{@,%a@,}@]"
        (pp_iter ~sep:" " pp_b)
        (Iter.append (Var.Map.to_iter self.ty) (Var.Map.to_iter self.m))
    )

  (* Bind a variable into a substitution. *)
  let subst_bind_ (subst:subst) v t : subst =
    if is_eq_to_type v.v_ty then (
      { subst with ty=Var.Map.add v t subst.ty }
    ) else (
      { subst with m=Var.Map.add v t subst.m;  }
    )

  let db_shift ctx (e:t) (n:int) =
    ctx_check_e_uid ctx e;
    assert (CCOpt.for_all is_closed (Lazy.force e.e_ty));
    let rec loop e k : t =
      if is_closed e then e
      else if is_a_type e then e
      else (
        match view e with
        | E_bound_var bv ->
          if bv.bv_idx >= k
          then bvar ctx (bv.bv_idx + n) bv.bv_ty
          else bvar ctx bv.bv_idx bv.bv_ty
        | _ ->
          map ctx e ~f:(fun inbind u -> loop u (if inbind then k+1 else k))
      )
    in
    assert (n >= 0);
    if n = 0 then e else loop e 0

  module E_int_tbl = CCHashtbl.Make(struct
      type t = expr * int
      let equal (t1,k1) (t2,k2) = equal t1 t2 && k1==k2
      let hash (t,k) = H.combine3 27 (hash t) (H.int k)
    end)

  let subst_ ctx ~recursive e0 (subst:subst) : t =
    (* cache for types and some terms *)
    let cache_ = E_int_tbl.create 16 in
    let ty_subst_empty_ = Var.Map.is_empty subst.ty in

    let rec loop k e =
      if is_a_type e then (
        (* type subst: can use a cache, and only consider subst.ty
           with k=0 since there are no binders *)
        if ty_subst_empty_ then e
        else (
          try E_int_tbl.find cache_ (e,0)
          with Not_found ->
            let r = loop_uncached_ 0 e in
            E_int_tbl.add cache_ (e,0) r;
            r
        )
      ) else (
        try E_int_tbl.find cache_ (e,k)
        with Not_found ->
          let r = loop_uncached_ k e in
          E_int_tbl.add cache_ (e,k) r;
          r
      )

    and loop_uncached_ k (e:t) : t =
      let ty = lazy (
        match e.e_ty with
        | lazy None -> None
        | lazy (Some ty) -> Some (loop 0 ty)
      ) in
      match view e with
      | _ when not (has_fvars e) -> e (* nothing to subst in *)
      | E_var v when is_eq_to_type v.v_ty ->
        (* type variable substitution *)
        begin match Var.Map.find v subst.ty with
          | u ->
            assert (is_closed u); if recursive then loop 0 u else u
          | exception Not_found -> var ctx v
        end
      | E_var v ->
        (* first, subst in type *)
        let v = {v with v_ty=loop k v.v_ty} in
        begin match Var.Map.find v subst.m with
          | u ->
            let u = db_shift ctx u k in
            if recursive then loop 0 u else u
          | exception Not_found -> var ctx v
        end
      | E_const (_, []) -> e
      | E_const (c, args) ->
        (* subst in args, thus changing the whole term's type *)
        let ty = lazy (Some (loop k (ty_exn e))) in
        mk_const_ ctx c (List.map (loop k) args) ty
      | E_app (hd, a) ->
        let hd' = loop k hd in
        let a' = loop k a in
        if hd==hd' && a'==a then e
        else make_ ctx (E_app (hd',a')) ty
      | E_arrow (a, b) ->
        let a' = loop k a in
        let b' = loop k b in
        if a==a' && b'==b then e
        else make_ ctx (E_arrow (a',b')) ty
      | _ ->
        map ctx e ~f:(fun inb u -> loop (if inb then k+1 else k) u)
    in

    if Var.Map.is_empty subst.m && Var.Map.is_empty subst.ty then (
      e0
    ) else (
      loop 0 e0
    )

  let[@inline] subst ctx ~recursive e subst =
    subst_ ctx ~recursive e subst

  let const ctx c args : t =
    ctx_check_e_uid ctx c.c_ty;
    let ty =
      match c.c_args with
      | C_arity n ->
        if List.length args <> n then (
          Error.failf
            "constant %a requires %d arguments, but is applied to %d"
            Name.pp c.c_name
            n (List.length args)
        );
        Lazy.from_val (Some c.c_ty)
      | C_ty_vars ty_vars ->
        if List.length args <> List.length ty_vars then (
          Error.failf
            "constant %a requires %d arguments, but is applied to %d"
            Name.pp c.c_name
            (List.length ty_vars) (List.length args)
        );
        lazy (
          let sigma = List.fold_left2 subst_bind_ subst_empty_ ty_vars args in
          Some (subst ~recursive:false ctx c.c_ty sigma)
        )
    in
    mk_const_ ctx c args ty

  let eq ctx ty =
    let eq = Lazy.force ctx.ctx_eq_c in
    const ctx eq [ty]

  let select ctx ty =
    let sel = Lazy.force ctx.ctx_select_c in
    const ctx sel [ty]

  let abs_on_ ctx (v:var) (e:t) : t =
    ctx_check_e_uid ctx v.v_ty;
    ctx_check_e_uid ctx e;
    if not (is_closed v.v_ty) then (
      Error.failf "cannot abstract on variable with non closed type %a" pp v.v_ty
    );
    let db0 = bvar ctx 0 v.v_ty in
    let body = db_shift ctx e 1 in
    subst ~recursive:false ctx body {m=Var.Map.singleton v db0; ty=Var.Map.empty}

  (* replace DB0 in [e] with [u] *)
  let subst_db_0 ctx e ~by:u : t =
    ctx_check_e_uid ctx e;
    ctx_check_e_uid ctx u;

    let cache_ = E_int_tbl.create 8 in

    let rec aux e k : t =
      if is_a_type e then e
      else if db_depth e < k then e
      else (
        match view e with
        | E_const _ -> e
        | E_bound_var bv when bv.bv_idx = k ->
          (* replace here *)
          db_shift ctx u k
        | _ ->
          (* use the cache *)
          try E_int_tbl.find cache_ (e,k)
          with Not_found ->
            let r =
              map ctx e ~f:(fun inb u -> aux u (if inb then k+1 else k))
            in
            E_int_tbl.add cache_ (e,k) r;
            r
      )
    in
    if is_closed e then e else aux e 0

  (* find a name that doesn't capture a variable of [e] *)
  let pick_name_ (name0:string) (e:t) : string =
    let rec loop i =
      let name = if i= 0 then name0 else Printf.sprintf "%s%d" name0 i in
      if free_vars_iter e |> Iter.exists (fun v -> v.v_name = name)
      then loop (i+1)
      else name
    in
    loop 0

  let open_lambda ctx e : _ option =
    match view e with
    | E_lam (name, ty, bod) ->
      let name = pick_name_ name bod in
      let v = Var.make name ty in
      let bod' = subst_db_0 ctx bod ~by:(var ctx v) in
      Some (v, bod')
    | _ -> None

  let open_lambda_exn ctx e = match open_lambda ctx e with
    | Some tup -> tup
    | None -> Error.failf "open-lambda: term is not a lambda:@ %a" pp e

  let arrow ctx a b : t =
    if not (is_a_type a) || not (is_a_type b) then (
      Error.failf "arrow: both arguments must be types"
    );
    let ty = Lazy.from_val (Some (type_ ctx)) in
    make_ ctx (E_arrow (a,b)) ty

  let not_ ctx e = match view e with
    | E_not v -> v
    | _ ->
      let ty = lazy (Some (bool ctx)) in
      make_ ctx (E_not e) ty

  let app ctx f a : t =
    ctx_check_e_uid ctx f;
    ctx_check_e_uid ctx a;

    let ty_f = ty_exn f in
    let ty_a = ty_exn a in

    let[@inline never] fail () =
      Error.failf
        "@[<2>kernel: cannot apply function@ `@[%a@]`@ \
         to argument `@[%a@]`@]@];@ \
         @[function has type@ `@[%a@]`,@ \
         but arg has type `@[%a@]`@]"
        pp f pp a pp ty_f pp ty_a
    in

    let ty =
      match view ty_f with
      | E_arrow (ty_arg, ty_ret) when equal ty_arg ty_a ->
        ty_ret (* no instantiation needed *)
      | _ -> fail()
    in
    let ty = Lazy.from_val (Some ty) in
    let e = make_ ctx (E_app (f,a)) ty in
    e

  let rec app_l ctx f l = match l with
    | [] -> f
    | x :: l' ->
      let f = app ctx f x in
      app_l ctx f l'

  let app_eq ctx a b =
    let f = eq ctx (ty_exn a) in
    let f = app ctx f a in
    let f = app ctx f b in
    f

  let arrow_l ctx l ret : t = CCList.fold_right (arrow ctx) l ret

  let lambda_db ctx ~name ~ty_v bod : t =
    ctx_check_e_uid ctx ty_v;
    ctx_check_e_uid ctx bod;
    if not (is_a_type ty_v) then (
      Error.failf "lambda: variable must have a type as type, not %a"
        pp ty_v;
    );
    let ty = lazy (
      (* type of [λx:a. t] is [a -> typeof(t)] if [a] is a type *)
      Some (arrow ctx ty_v (ty_exn bod))
    ) in
    make_ ctx (E_lam (name, ty_v, bod)) ty

  let lambda ctx v bod =
    let bod = abs_on_ ctx v bod in
    lambda_db ctx ~name:v.v_name ~ty_v:v.v_ty bod

  let lambda_l ctx = CCList.fold_right (lambda ctx)

  let unfold_app = unfold_app

  let unfold_not e = match view e with
    | E_not u -> Some u
    | _ -> None

  let[@inline] unfold_eq e =
    let f, l = unfold_app e in
    match view f, l with
    | E_const ({c_name;_}, [_]), [a;b] when Name.equal c_name id_eq -> Some(a,b)
    | _ -> None

  let[@unroll 1] rec unfold_arrow e =
    match view e with
    | E_arrow (a,b) ->
      let args, ret = unfold_arrow b in
      a::args, ret
    | _ -> [], e

  let[@unroll 1] rec return_ty e =
    match view e with
    | E_arrow (_,b) -> return_ty b
    | _ -> e

  let[@inline] as_const e = match e.e_view with
    | E_const (c,args) -> Some (c,args)
    | _ -> None

  let[@inline] as_const_exn e = match e.e_view with
    | E_const (c,args) -> c, args
    | _ -> Error.failf "%a is not a constant" pp e

  module AsKey = struct
    type nonrec t = t
    let equal = equal
    let compare = compare
    let hash = hash
  end

  module Map = CCMap.Make(AsKey)
  module Set = Expr_set
  module Tbl = CCHashtbl.Make(AsKey)

  let iter_dag ~f e : unit =
    let tbl = Tbl.create 8 in
    let rec loop e =
      if not (Tbl.mem tbl e) then (
        Tbl.add tbl e ();
        f e;
        iter e ~f:(fun _ u -> loop u)
      )
    in
    loop e
end

(* TODO: write Expr_for_ctx; then use it in tests *)

module Subst = struct
  type t = subst = {
    ty: expr Var.Map.t; (* ty subst *)
    m: expr Var.Map.t; (* term subst *)
  }

  let[@inline] is_empty self =
    Var.Map.is_empty self.ty &&
    Var.Map.is_empty self.m
  let[@inline] find_exn x s =
    if Expr.is_eq_to_type x.v_ty then Var.Map.find x s.ty
    else Var.Map.find x s.m

  let[@inline] mem x s =
    if Expr.is_eq_to_type x.v_ty then Var.Map.mem x s.ty
    else Var.Map.mem x s.m
  let empty = Expr.subst_empty_
  let bind = Expr.subst_bind_
  let pp = Expr.subst_pp_
  let[@inline] bind' x t s : t = bind s x t
  let[@inline] size self = Var.Map.cardinal self.m + Var.Map.cardinal self.ty
  let[@inline] to_iter self =
    Iter.append (Var.Map.to_iter self.m) (Var.Map.to_iter self.ty)
  let to_string = Fmt.to_string pp

  let is_renaming (self:t) : bool =
    let is_renaming_ m =
      try
        let codom =
          Var.Map.fold
            (fun _v e acc -> match Expr.view e with
               | E_var u -> Var.Set.add u acc
               | _ -> raise_notrace Exit) m Var.Set.empty
        in
        Var.Set.cardinal codom = Var.Map.cardinal m
      with Exit -> false
    in
    is_renaming_ self.ty && is_renaming_ self.m

  let[@inline] bind_uncurry_ s (x,t) = bind s x t
  let of_list = List.fold_left bind_uncurry_ empty
  let of_iter = Iter.fold bind_uncurry_ empty
end

(*$inject
  let ctx = Ctx.create ()
  let bool = Expr.bool ctx
  let type_ = Expr.type_ ctx
  let tau = Expr.const ctx (Expr.new_ty_const ctx "tau" 0) []
  let lambda v t = Expr.lambda ctx v t
  let v' s ty = Var.make s ty
  let v x = Expr.var ctx x
  let (@->) a b = Expr.arrow ctx a b
  let (@@) a b = Expr.app ctx a b
  let a = Expr.const ctx (Expr.new_const ctx "a0" [] tau) []
  let b = Expr.const ctx (Expr.new_const ctx "b0" [] tau) []
  let c = Expr.const ctx (Expr.new_const ctx "c0" [] tau) []
  let f1: const = Expr.new_const ctx "f1" [] (tau @-> tau)
  let eq = Expr.app_eq ctx

  let must_fail f = try ignore (f()); false with _ -> true
*)

(*$T
  must_fail (fun() -> a @-> b)
  Expr.equal (tau @-> bool) (tau @-> bool)
*)

(** {2 Context}

    The context is storing the term state, list of axioms,
    and other parameters.
    Terms from distinct contexts must never be mixed. *)
module Ctx = struct
  type t = ctx

  let uid_ = ref 0

  let create () : t =
    let ctx_uid = !uid_ land ctx_id_mask in
    incr uid_;
    let rec ctx = {
      ctx_uid;
      ctx_exprs=Expr_hashcons.create ~size:2_048 ();
      ctx_consts=Const_hashcons.create ~size:32 ();
      ctx_axioms=[];
      ctx_axioms_allowed=true;
      ctx_kind=lazy (Expr.make_ ctx E_kind (Lazy.from_val None));
      ctx_type=lazy (
        let kind = Expr.kind ctx in
        Expr.make_ ctx E_type (Lazy.from_val (Some kind))
      );
      ctx_bool_c=lazy (
        let typ = Expr.type_ ctx in
        Expr.new_const_ ctx id_bool (C_arity 0) typ
      );
      ctx_bool=lazy (
        Expr.const ctx (Lazy.force ctx.ctx_bool_c) []
      );
      ctx_eq_c=lazy (
        let type_ = Expr.type_ ctx in
        let a_ = Var.make "a" type_ in
        let ea = Expr.var ctx a_ in
        let typ = Expr.(arrow ctx ea @@ arrow ctx ea @@ bool ctx) in
        Expr.new_const_ ctx id_eq (C_ty_vars [a_]) typ
      );
      ctx_select_c=lazy (
        let type_ = Expr.type_ ctx in
        let lazy bool_ = ctx.ctx_bool in
        let a_ = Var.make "a" type_ in
        let ea = Expr.var ctx a_ in
        let typ = Expr.(arrow ctx (arrow ctx ea bool_) ea) in
        Expr.new_const_ ctx id_select (C_ty_vars [a_]) typ
      );
    } in
    ctx
end
