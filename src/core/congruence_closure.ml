
open Common

module K = Kernel
module E = Kernel.Expr
module Log = (val Logs.src_log (Logs.Src.create "quip.cc"))

module Vec = CCVector

type node = {
  e: E.t;
  mutable next: node; (* next element in the class *)
  mutable root: node; (* pointer to representative *)
  mutable expl: (node * expl) option; (* proof forest *)
  mutable parents: node list;
  sigt: signature option;
}

and signature =
  | S_app of node * node

and expl =
  | Exp_cong
  | Exp_merge of Lit.t
  (* merge [a] and [b] because of theorem [… |- a=b], modulo commutativity *)
  | Exp_eq of E.t * node * node
  | Exp_not of E.t * node * node

type merge_task = Merge of node * node * expl
type update_sig_task = Update_sig of node [@@unboxed]

(* signature table *)
module Sig_tbl = CCHashtbl.Make(struct
    type t = signature
    let equal s1 s2 = match s1, s2 with
      | S_app (x1,y1), S_app (x2,y2) ->
        x1==x2 && y1==y2
    let hash = function
      | S_app (a,b) -> CCHash.(combine3 28 (E.hash a.e) (E.hash b.e))
  end)

(* congruence closure state *)
type t = {
  ctx: K.ctx;
  nodes: node E.Tbl.t;
  to_merge: merge_task Vec.vector;
  to_update_sig: update_sig_task Vec.vector;
  n_true: node lazy_t;
  n_false: node lazy_t;
  sigs: node Sig_tbl.t;
  tmp_tbl: unit E.Tbl.t;
}

let[@inline] n_true self = Lazy.force self.n_true
let[@inline] n_false self = Lazy.force self.n_false

(* find representative of the class *)
let[@unroll 2] rec find (n:node) : node =
  if n.root == n then n
  else (
    let root = find n.root in
    n.root <- root;
    root
  )

let rec add_ (self:t) (e:E.t) : node =
  try E.Tbl.find self.nodes e
  with Not_found ->
    add_uncached_ self e

and add_uncached_ self e =
  let sigt, subs = match E.view e with
    | E.E_app (f, x) ->
      let n_f = find @@ add_ self f in
      let n_x = find @@ add_ self x in
      Some (S_app (n_f, n_x)), [n_f; n_x]
    | E.E_not u ->
      let n_u = find @@ add_ self u in
      None, [n_u]
    | _ -> None, []
  in
  let rec node = {
    e; sigt; next=node; root=node; expl=None; parents=[];
  } in
  E.Tbl.add self.nodes e node;
  List.iter (fun sub -> sub.parents <- node :: sub.parents) subs;
  if CCOpt.is_some sigt then (
    Vec.push self.to_update_sig @@ Update_sig node;
  );
  node

let create ctx ~true_ ~false_ : t =
  let rec self = lazy {
    ctx;
    nodes=E.Tbl.create 32;
    n_true=lazy (add_ (Lazy.force self) true_);
    n_false=lazy (add_ (Lazy.force self) false_);
    to_merge=Vec.create();
    to_update_sig=Vec.create();
    sigs=Sig_tbl.create 16;
    tmp_tbl=E.Tbl.create 16;
  } in
  let lazy self = self in
  ignore (Lazy.force self.n_true : node);
  ignore (Lazy.force self.n_false : node);
  self

(* nodes are equal? *)
let[@inline] are_eq (n1:node) (n2:node) : bool =
  find n1 == find n2

(* find common ancestor of nodes. Precondition: [are_eq n1 n2] *)
let find_common_ancestor (self:t) (n1:node) (n2:node) : node =
  let tbl = self.tmp_tbl in

  let rec add_path1 n =
    E.Tbl.add tbl n.e ();
    match n.expl with
    | None -> ()
    | Some (n2,_expl) -> add_path1 n2
  in
  add_path1 n1;

  let rec find n =
    if E.Tbl.mem tbl n.e then n
    else match n.expl with
      | None -> assert false
      | Some (n2,_) -> find n2
  in

  let res = find n2 in
  E.Tbl.clear tbl; (* be sure to reset temporary table *)
  res

module Proof = struct
  type t =
    | P_refl of E.t
    | P_sym of t
    | P_trans of t * t
    | P_congr of t * t
    | P_eq of E.t * t (* [(a=b)=true] because of [proof(a=b)] *)
    | P_not of E.t * t (* [not a=true] because of [proof(a=false)] *)
    | P_lit of Lit.t
  [@@deriving show {with_path=false}]

  let sym p : t = match p with
    | P_sym p2 -> p2
    | _ -> P_sym p
  let lit l : t = P_lit l
  let refl e : t = P_refl e
  let congr p1 p2 : t = P_congr (p1,p2)
  let trans a b : t = match a, b with
    | P_refl _, _ -> b
    | _, P_refl _ -> a
    | _ -> P_trans (a,b)
end

let rec prove_eq (self:t) (n1:node) (n2:node) : Proof.t =
  if n1 == n2 then (
    Proof.refl n1.e
  ) else (
    let n = find_common_ancestor self n1 n2 in
    let p1 = explain_along_ self n1 n in
    let p2 = explain_along_ self n2 n in
    (* p1: [|- n1=n], p2: [|- n2=n], so build [|- n1=n2] via
       transivity of p1 and sym(p2)==[|- n=n2] *)
    let th = Proof.trans p1 (Proof.sym p2) in
    th
  )

(* explain why [n0 = parent].
   Precondition: parent is in the chain of explanation of [n0]. *)
and explain_along_ (self:t) (n0:node) (parent:node) : Proof.t =
  (* invariant: p is [|- n0=n1] *)
  let rec loop p n1 =
    if n1==parent then p
    else (
      match n1.expl with
      | None -> assert false
      | Some (n2, e_1_2) ->
        (* get a proof of [|- n1.e = n2.e] *)
        let p_12 =
          match e_1_2 with
          | Exp_merge lit_12 ->
            begin match Lit.as_eqn lit_12 with
              | Some (x,y) when x == n2.e ->
                assert (y == n1.e);
                Proof.sym (Proof.lit lit_12)
              | _ -> Proof.lit lit_12
            end
          | Exp_cong ->
            begin match n1.sigt, n2.sigt with
              | Some (S_app (a1,b1)), Some (S_app (a2,b2)) ->
                let p_sub_1 = prove_eq self a1 a2 in
                let p_sub_2 = prove_eq self b1 b2 in
                Proof.congr p_sub_1 p_sub_2
              | None, _ | _, None -> assert false
            end
          | Exp_eq (e,n1,n2) ->
            let p = prove_eq self n1 n2 in
            Proof.P_eq (e,p)
          | Exp_not (e,n1,n2) ->
            let p = prove_eq self n1 n2 in
            Proof.P_not (e,p)
        in
        (* now prove [|- n0.e = n2.e] *)
        let th' = Proof.trans p p_12 in
        loop th' n2
    )
  in
  loop (Proof.refl n0.e) n0

(* TODO: add signature for lambdas and handle congruence on lambdas.

   When adding `\x. t`, look at the DB depth of `t`. Lambda terms of distinct DB depths
    can never be merged, so we can just allocate a distinct fresh variable for each
   DB depth and add `t[x_db / x]` to the congruence with signature `Lam(t[x_db/x])`.
   When merging two such classes, the proof is [Thm.abs] which re-abstracts
   over `x_db`.

   TODO: also add some tests, like [(a=b), (\x. f(a,x)) c = f(a,c) |- (\x. f(b,x)) =b]
*)


let[@inline] canon_sig (s:signature) : signature =
  match s with
  | S_app (n1, n2) -> S_app (find n1, find n2)

(* iterate on all nodes in the class of [n0] *)
let iter_class_ (n0:node) f : unit =
  let continue = ref true in
  let n = ref n0 in
  while !continue do
    f !n;
    n := (!n).next;
    if !n == n0 then continue := false
  done

(* make sure [n1] is the root of its proof forest *)
let[@unroll 2] rec reroot_at (n1:node) : unit =
  match n1.expl with
  | None -> assert (n1.root == n1); ()
  | Some (n2, e_12) ->
    reroot_at n2;
    assert (n2.expl == None);
    n2.expl <- Some (n1, e_12);
    n1.expl <- None;
    ()

(* main repair loop *)
let update (self:t) : unit =
  while not (Vec.is_empty self.to_merge && Vec.is_empty self.to_update_sig) do
    while not (Vec.is_empty self.to_update_sig) do
      let Update_sig n = Vec.pop_exn self.to_update_sig in
      Log.debug (fun k->k"cc: update sig %a" E.pp n.e);
      begin match n.sigt with
        | None -> ()
        | Some s ->
          let s' = canon_sig s in
          begin match Sig_tbl.get self.sigs s' with
            | None -> Sig_tbl.add self.sigs s' n
            | Some n' when are_eq n n' -> ()
            | Some n' ->
              Vec.push self.to_merge @@ Merge (n,n',Exp_cong);
          end;

          (* if [find(a) = find(b)], merge [a=b] with [true] *)
          begin match E.unfold_eq n.e with
            | Some (a,b) ->
              let na = add_ self a in
              let nb = add_ self b in
              if find na==find nb then (
                Vec.push self.to_merge @@
                Merge (n, n_true self, Exp_eq (n.e, na, nb))
              )
            | None -> ()
          end;
      end;

      (* if [n == true], merge [not n] with [false] (and conversely) *)
      begin match E.unfold_not n.e with
        | Some u ->
          let nu = add_ self u in
          if find nu == find @@ n_true self then (
            Vec.push self.to_merge @@
            Merge (n, n_false self, Exp_not (n.e, n, n_false self))
          ) else if find nu == find @@ n_false self then (
            Vec.push self.to_merge @@
            Merge (n, n_true self, Exp_not (n.e, n, n_true self))
          )
        | None -> ()
      end;
    done;

    while not (Vec.is_empty self.to_merge) do
      let Merge (n1,n2,e_12) = Vec.pop_exn self.to_merge in
      let r1 = find n1 in
      let r2 = find n2 in
      if r1 != r2 then (
        Log.debug (fun k->k"cc: merge `%a` and `%a`" E.pp n1.e E.pp n2.e);
        (* make sure to keep true/false as representative *)
        let n1, n2, r1, r2 =
          if n2 == n_true self || n2 == n_false self
          then n2, n1, r2, r1
          else n1, n2, r1, r2 in
        (* add explanation for the merge *)
        reroot_at n1;
        assert (n1.expl == None);
        n1.expl <- Some (n2, e_12);
        (* merge r1 into r2 *)
        iter_class_ r1
          (fun n1' ->
             n1'.root <- r2;
             (* update signature of [parents(n1')] *)
             List.iter
               (fun n1'_p -> Vec.push self.to_update_sig @@ Update_sig n1'_p)
               n1'.parents);
        (* merge the equiv classes *)
        let n1_next = n1.next in
        n1.next <- n2.next;
        n2.next <- n1_next;
      )
    done
  done;
  ()

let add_lit (self:t) (lit:Lit.t) : unit =
  begin match Lit.as_eqn lit with
    | Some (a,b) ->
      let a = add_ self a in
      let b = add_ self b in
      if not (are_eq a b) then (
        Vec.push self.to_merge (Merge (a,b,Exp_merge lit));
      );
    | None -> ()
  end;
  let n_bool = if Lit.sign lit then n_true self else n_false self in
  let n = add_ self (Lit.atom lit) in
  Vec.push self.to_merge (Merge (n, n_bool, Exp_merge lit))

let is_absurd (ctx:K.ctx) ~true_ ~false_ (lits:Lit.t list) : Proof.t option =
  Profile.with_ "cc.is-absurd" @@ fun () ->
  Log.debug (fun k->k"(@[cc.is-absurd@ %a@])" (pp_l Lit.pp) lits);
  let self = create ctx ~true_ ~false_ in
  List.iter (add_lit self) lits;
  update self;
  let n_true = n_true self and n_false = n_false self in
  if are_eq n_true n_false then (
    let p = prove_eq self n_true n_false in
    Some p
  ) else None
