
open Common

module K = Kernel

module Datatype : sig
  type t = {
    name: string;
    cstors: cstor list
  } (** Datatype *)

  and cstor = {
    c_name: string;
    c_const: K.const;
    c_isa: K.const; (* recognize this cstor *)
    c_ty: t lazy_t;
    c_args: (sel * K.ty) list; (* with selector *)
  } (** Constructor *)

  and sel = {
    sel_name: string;
    sel_i: int;
    sel_c: K.const;
    sel_ty: t lazy_t;
    sel_cstor: cstor lazy_t;
  } (** Selector *)
  [@@deriving show]
end = struct
  type const = K.const [@printer K.Const.pp] [@@deriving show]
  type t = {
    name: string;
    cstors: cstor list;
  }

  and cstor = {
    c_name: string;
    c_const: const;
    c_isa: const;
    c_ty: (t [@printer fun out s -> Fmt.string out s.name]) lazy_t;
    c_args: (sel * (K.ty [@printer K.Expr.pp])) list;
  }

  and sel = {
    sel_name: string;
    sel_i: int;
    sel_c: const;
    sel_ty: (t [@printer fun out s -> Fmt.string out s.name]) lazy_t;
    sel_cstor: (cstor [@opaque]) lazy_t;
  }
  [@@deriving show {with_path=false}]

end

module type S = sig
  val ctx : K.ctx

  val find_builtin : Builtin.t -> K.const option

  val find_const_by_name : string -> (K.const * Builtin.t option) option

  val find_ty_const_by_name : string -> K.ty_const option

  val find_const_def : string -> (K.const * Clause.t) option

  val find_cstor : string -> Datatype.cstor option

  val find_selector : string -> Datatype.sel option

  val find_datatype : string -> Datatype.t option

  (* TODO: named terms? *)

  val add_assumption : Clause.t -> unit

  val assumptions : unit -> Clause.t Seq.t

  val add_datatype : Datatype.t -> unit

  val decl_ty_const : string -> K.ty_const -> unit

  val decl_const : string -> K.const -> unit
  (** Declare constant *)

  val def_const : string -> K.const -> Clause.t -> unit
  (** Declare + define constant *)

  val pp_debug : unit Fmt.printer
  (** Print the environment, assumptions, etc. for debug. Can be verbose. *)
end

type t = (module S)

let pp_debug out (module M:S) = M.pp_debug out ()

(** Empty environment with smtlib-2 syntax for the builtins *)
let make_new_smt2 ?(ctx=K.Ctx.create()) () : t =
  let module E = K.Expr in
  let module M = struct
    type ('a,'b) tbl =
      ('a,'b) Hashtbl.t
      [@polyprinter Fmt.(CCHashtbl.pp ~pp_start:(return "{@[") ~pp_stop:(return "@]})"))]
    [@@deriving show]

    type 'a vec =
      'a CCVector.vector
      [@polyprinter Fmt.(CCVector.pp ~pp_start:(return "[@[") ~pp_stop:(return "@]]"))]
    [@@deriving show]

    type env = {
      ctx: K.ctx [@opaque];
      consts: (string, (K.const [@printer K.Const.pp]) * Builtin.t option) tbl;
      ty_consts: (string, K.ty_const [@printer K.Const.pp]) tbl;
      data: (string, Datatype.t) tbl;
      cstors: (string, Datatype.cstor) tbl;
      sels: (string, Datatype.sel) tbl;
      defs: (string, (K.const [@printer K.Const.pp]) * Clause.t) tbl;
      named_terms: (string, K.Expr.t) tbl;
      builtins: (K.const [@printer K.Const.pp]) Builtin.Tbl.t;
      assms: Clause.t vec;
    } [@@deriving show {with_path=false}]

    let env =
      let self = {
        ctx;
        consts=Hashtbl.create 32;
        ty_consts=Hashtbl.create 16;
        defs=Hashtbl.create 16;
        data=Hashtbl.create 16;
        cstors=Hashtbl.create 16;
        sels=Hashtbl.create 16;
        builtins=Builtin.Tbl.create 16;
        named_terms=Hashtbl.create 32;
        assms=CCVector.create();
      } in

      (* pre-populate with some builtins *)
      begin
        let bool = E.bool ctx in
        let type_ = E.type_ ctx in
        Hashtbl.add self.ty_consts "Bool" (K.Const.bool ctx);
        let (@->) a b = E.arrow_l ctx a b in
        let addc s b c =
          Hashtbl.add self.consts s (c,Some b);
          Builtin.Tbl.add self.builtins b c;
        and addtyc s b c =
          Hashtbl.add self.ty_consts s c; (* TODO: also remember builtin *)
          Builtin.Tbl.add self.builtins b c;
        in
        let mkc ?(tyvars=[]) s b ty =
          let c =  E.new_const ctx s tyvars ty in
          addc s b c
        in
        let v_alpha = K.Var.make "A" type_ in
        let alpha = E.var ctx v_alpha in
        mkc "true" Builtin.True @@ bool;
        mkc "false" Builtin.False @@ bool;
        mkc "not" Builtin.Not @@ [bool] @-> bool;
        mkc "and" Builtin.And @@ [bool;bool] @-> bool;
        mkc "or" Builtin.Or @@ [bool;bool] @-> bool;
        mkc "xor" Builtin.Xor @@ [bool;bool] @-> bool;
        mkc "=>" Builtin.Imply @@ [bool;bool] @-> bool;
        mkc ~tyvars:[v_alpha] "ite" Builtin.If @@ [bool;alpha;alpha] @-> alpha;
        addtyc "Bool" Builtin.Bool (K.Const.bool ctx);
        addc "=" Builtin.Eq (K.Const.eq ctx);
      end;
      self

    let ctx = ctx
    let find_const_by_name n = CCHashtbl.get env.consts n
    let find_ty_const_by_name n = CCHashtbl.get env.ty_consts n
    let find_builtin b = Builtin.Tbl.get env.builtins b
    let find_const_def n = CCHashtbl.get env.defs n
    let find_cstor n = CCHashtbl.get env.cstors n
    let find_selector n = CCHashtbl.get env.sels n
    let find_datatype n = CCHashtbl.get env.data n
    let add_assumption = CCVector.push env.assms
    let assumptions () = CCVector.to_seq env.assms
    let pp_debug out () = pp_env out env
    let decl_ty_const name c = Hashtbl.replace env.ty_consts name c
    let decl_const name c = Hashtbl.replace env.consts name (c,None)
    let def_const name c th =
      Hashtbl.replace env.defs name (c,th);
      Hashtbl.replace env.consts name (c,None)

    let add_datatype (d:Datatype.t) =
      Hashtbl.replace env.data d.name d;
      List.iter (fun c ->
          Hashtbl.replace env.cstors c.Datatype.c_name c;
          List.iter
            (fun (sel,_) -> Hashtbl.replace env.sels sel.Datatype.sel_name sel)
            c.c_args;
        ) d.cstors
  end
  in
  (module M)
