
open Common
module Vec = CCVector

module Log = (val Logs.src_log (Logs.Src.create "quip.rup"))

module type TERM = sig
  type t
  val dummy : t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val pp : t Fmt.printer
end

(** An instance of the checker *)
module type S = sig
  module T : TERM

  module Atom : sig
    type t

    val make : ?sign:bool -> T.t -> t
    val pp : t Fmt.printer
  end
  type atom = Atom.t

  module Clause : sig
    type store
    val create : unit -> store

    type t

    val size : t -> int

    val get : t -> int -> atom

    val iter : f:(atom -> unit) -> t -> unit

    val pp : t Fmt.printer

    val of_list : store -> atom list -> t
    val of_iter : store -> atom Iter.t -> t
  end
  type clause = Clause.t

  module Checker : sig
    type t

    val create : Clause.store -> t

    val add_clause : t -> Clause.t -> unit
    val add_clause_l : t -> atom list -> unit

    val is_valid_drup : t -> Clause.t -> bool
  end
end

module Make(T:TERM)
  : S with module T = T
= struct
  module T = T

  module T_tbl = CCHashtbl.Make(T)

  module Atom : sig
    type t
    type atom = t

    val sign : t -> bool
    val term : t -> T.t
    val neg : t -> t
    val make : ?sign:bool -> T.t -> t

    val equal : t -> t -> bool
    val compare : t -> t -> int

    val pp : t Fmt.printer
    val dummy : t

    module Set : CCSet.S with type elt = t
    module Tbl : CCHashtbl.S with type key = t
    module Assign : sig
      type t
      val create : unit -> t
      val is_true : t -> atom -> bool
      val is_false : t -> atom -> bool
      val is_unassigned : t -> atom -> bool
      val set : t -> atom -> bool -> unit
    end
    module Stack : sig
      type t
      val create : unit -> t
      val push : t -> atom -> unit
      val pop_exn : t -> atom
      val length : t -> int
      val shrink : t -> int -> unit
      val is_empty : t -> bool
      val get : t -> int -> atom
      val to_iter : t -> atom Iter.t
    end
  end = struct
    type term = T.t
    type t = { sign: bool; term: term }
    type atom = t

    let term self = self.term
    let sign self = self.sign
    let equal a b = a.sign=b.sign && T.equal a.term b.term
    let neg self = {self with sign=not self.sign}
    let make ?(sign=true) term : t = {sign;term}
    let compare a b =
      let c = compare a.sign b.sign in
      if c <> 0 then c
      else T.compare a.term b.term
    let hash a = CCHash.(combine2 (bool a.sign) (T.hash a.term))
    let pp out self =
      Fmt.fprintf out "%s%a"
        (if self.sign then "+" else "-") T.pp self.term

    let dummy = make T.dummy

    module As_key = struct
      type nonrec t = t
      let compare = compare
      let equal = equal
      let hash = hash
    end
    module Set = CCSet.Make(As_key)
    module Tbl = CCHashtbl.Make(As_key)

    module Assign = struct
      type t = bool T_tbl.t
      let create () = T_tbl.create 32
      let is_true (self:t) a : bool =
        match a.sign, T_tbl.get self a.term with
        | true, Some true
        | false, Some false -> true
        | _ -> false
      let[@inline] is_false self (a:atom) : bool =
        is_true self (neg a)
      let[@inline] is_unassigned self a =
        not (is_true self a) && not (is_false self a)
      let set self a sign =
        let sign = sign=a.sign in
        T_tbl.replace self a.term sign
    end
    module Stack = struct
      type t = atom Vec.vector
      let create = Vec.create
      let is_empty = Vec.is_empty
      let push = Vec.push
      let pop_exn = Vec.pop_exn
      let length = Vec.length
      let get = Vec.get
      let to_iter = Vec.to_iter
      let shrink = Vec.truncate
    end
  end
  type atom = Atom.t

  (** Boolean clauses *)
  module Clause : sig
    type store
    val create : unit -> store
    type t
    val size : t -> int
    val id : t -> int
    val get : t -> int -> atom
    val iter : f:(atom -> unit) -> t -> unit
    val watches: t -> atom * atom
    val set_watches : t -> atom * atom -> unit
    val pp : t Fmt.printer
    val of_list : store -> atom list -> t
    val of_iter : store -> atom Iter.t -> t
    module Tbl : CCHashtbl.S with type key = t
  end = struct
    type t = {
      id: int;
      atoms: atom array;
      mutable watches: atom * atom;
    }
    type store = {
      mutable n: int;
    }
    let create(): store =
      { n=0; }
    let[@inline] id self = self.id
    let[@inline] size self = Array.length self.atoms
    let[@inline] get self i = Array.get self.atoms i
    let[@inline] watches self = self.watches
    let[@inline] set_watches self w = self.watches <- w
    let[@inline] iter ~f self =
      for i=0 to Array.length self.atoms-1 do
        f (Array.unsafe_get self.atoms i)
      done
    let pp out (self:t) =
      let pp_watches out = function
        | (p,q) when p==Atom.dummy || q==Atom.dummy -> ()
        | (p,q) -> Fmt.fprintf out "@ :watches (%a,%a)" Atom.pp p Atom.pp q in
      Fmt.fprintf out "(@[cl[%d]@ %a%a])"
        self.id (Fmt.Dump.array Atom.pp) self.atoms pp_watches self.watches
    let of_iter self (atoms:atom Iter.t) : t =
      (* normalize + find in table *)
      let atoms = Atom.Set.of_iter atoms |> Atom.Set.to_iter |> Iter.to_array  in
      let id = self.n in
      self.n <- 1 + self.n;
      let c = {atoms; id; watches=Atom.dummy, Atom.dummy} in
      c
    let of_list self atoms : t = of_iter self (Iter.of_list atoms)

    module As_key = struct
      type nonrec t=t
      let[@inline] hash a = CCHash.int a.id
      let[@inline] equal a b = a.id = b.id
      let[@inline] compare a b = compare a.id b.id
    end
    module Tbl = CCHashtbl.Make(As_key)
  end
  type clause = Clause.t

  (** Forward proof checker.

      Each event is checked by reverse-unit propagation on previous events. *)
  module Checker : sig
    type t
    val create : Clause.store -> t
    val add_clause : t -> Clause.t -> unit
    val add_clause_l : t -> atom list -> unit
    val is_valid_drup : t -> Clause.t -> bool
  end = struct
    type t = {
      cstore: Clause.store;
      assign: Atom.Assign.t; (* atom -> is_true(atom) *)
      trail: Atom.Stack.t; (* current assignment *)
      mutable trail_ptr : int; (* offset in trail for propagation *)
      active_clauses: unit Clause.Tbl.t;
      watches: Clause.t Vec.vector Atom.Tbl.t; (* atom -> clauses it watches *)
    }

    let create cstore : t =
      { trail=Atom.Stack.create();
        trail_ptr = 0;
        cstore;
        active_clauses=Clause.Tbl.create 32;
        assign=Atom.Assign.create();
        watches=Atom.Tbl.create 32;
      }

    (* ensure data structures are big enough to handle [a] *)
    let ensure_atom_ self (a:atom) =
      if not (Atom.Tbl.mem self.watches a) then (
        Atom.Tbl.add self.watches a (Vec.create ());
        Atom.Tbl.add self.watches (Atom.neg a) (Vec.create ());
      );
      ()

    let[@inline] is_true self (a:atom) : bool =
      Atom.Assign.is_true self.assign a
    let[@inline] is_false self (a:atom) : bool =
      Atom.Assign.is_false self.assign a
    let[@inline] is_unassigned self a =
      Atom.Assign.is_unassigned self.assign a

    let add_watch_ self (a:atom) (c:clause) =
      Vec.push (Atom.Tbl.find self.watches a) c

    let remove_watch_ self (a:atom) idx =
      let v = Atom.Tbl.find self.watches a in
      Vec.remove_unordered v idx

    exception Conflict

    let raise_conflict_ _self a =
      Log.debug (fun k->k"conflict on atom %a" Atom.pp a);
      raise Conflict

    (* set atom to true *)
    let[@inline] set_atom_true (self:t) (a:atom) : unit =
      if is_true self a then ()
      else if is_false self a then raise_conflict_ self a
      else (
        Atom.Assign.set self.assign a true;
        Atom.Stack.push self.trail a
      )

    (* print the trail *)
    let pp_trail_ out self =
      Fmt.fprintf out "(@[%a@])" (Fmt.iter Atom.pp) (Atom.Stack.to_iter self.trail)

    exception Is_sat
    exception Is_undecided

    (* check if [c] is false in current trail *)
    let c_is_false_ self c =
      try Clause.iter c ~f:(fun a -> if not (is_false self a) then raise Exit); true
      with Exit -> false

    type propagation_res =
      | Keep
      | Remove

    (* do boolean propagation in [c], which is watched by the true literal [a] *)
    let propagate_in_clause_ (self:t) (a:atom) (c:clause) : propagation_res =
      assert (is_true self a);
      let a1, a2 = Clause.watches c in
      let na = Atom.neg a in
      (* [q] is the other literal in [c] such that [¬q] watches [c]. *)
      let q = if Atom.equal a1 na then a2 else (assert(Atom.equal a2 na); a1) in
      try
        if is_true self q then Keep (* clause is satisfied *)
        else (
          let n_unassigned = ref 0 in
          let unassigned_a = ref a in (* an unassigned atom, if [!n_unassigned > 0] *)
          if not (is_false self q) then unassigned_a := q;
          begin
            try
              Clause.iter c
                ~f:(fun ai ->
                    if is_true self ai then raise Is_sat (* no watch update *)
                    else if is_unassigned self ai then (
                      incr n_unassigned;
                      if q <> ai then unassigned_a := ai;
                      if !n_unassigned >= 2 then raise Is_undecided; (* early exit *)
                    );
                  )
            with Is_undecided -> ()
          end;

          if !n_unassigned = 0 then (
            (* if we reach this point it means no literal is true, and none is
               unassigned. So they're all false and we have a conflict. *)
            assert (is_false self q);
            raise_conflict_ self a;
          ) else if !n_unassigned = 1 then (
            (* no lit is true, only one is unassigned: propagate it.
               no need to update the watches as the clause is satisfied. *)
            assert (is_unassigned self !unassigned_a);
            let p = !unassigned_a in
            Log.debug (fun k->k"(@[propagate@ :atom %a@ :reason %a@])" Atom.pp p Clause.pp c);
            set_atom_true self p;
            Keep
          ) else (
            (* at least 2 unassigned, just update the watch literal to [¬p] *)
            let p = !unassigned_a in
            assert (p <> q);
            Clause.set_watches c (q, p);
            add_watch_ self (Atom.neg p) c;
            Remove
          );
        )
      with
      | Is_sat -> Keep

    let propagate_atom_ self (a:atom) : unit =
      ensure_atom_ self a;
      let v = Atom.Tbl.find self.watches a in
      let i = ref 0 in
      while !i < Vec.length v do
        match propagate_in_clause_ self a (Vec.get v !i) with
        | Keep -> incr i;
        | Remove ->
          remove_watch_ self a !i
      done

    (* perform boolean propagation in a fixpoint
       @raise Conflict if a clause is false *)
    let bcp_fixpoint_ (self:t) : unit =
      while self.trail_ptr < Atom.Stack.length self.trail do
        let a = Atom.Stack.get self.trail self.trail_ptr in
        Log.debug (fun k->k"(@[bcp@ :atom %a@])" Atom.pp a);
        self.trail_ptr <- 1 + self.trail_ptr;
        propagate_atom_ self a;
      done

    (* calls [f] and then restore trail to what it was *)
    let with_restore_trail_ self f =
      let trail_size0 = Atom.Stack.length self.trail in
      let ptr0 = self.trail_ptr in

      let restore () =
        (* unassign new literals *)
        for i=trail_size0 to Atom.Stack.length self.trail - 1 do
          let a = Atom.Stack.get self.trail i in
          assert (is_true self a);
          Atom.Assign.set self.assign a false;
        done;

        (* remove literals from trail *)
        Atom.Stack.shrink self.trail trail_size0;
        self.trail_ptr <- ptr0
      in

      CCFun.finally ~h:restore ~f

    (* add clause to the state *)
    let add_clause (self:t) (c:Clause.t) =
      Log.debug (fun k->k"(@[add-clause@ %a@])" Clause.pp c);
      Clause.iter c ~f:(ensure_atom_ self);
      Clause.Tbl.add self.active_clauses c ();

      begin match Clause.size c with
        | 0 -> ()
        | 1 ->
          set_atom_true self (Clause.get c 0);
        | _ ->
          let c0 = Clause.get c 0 in
          let c1 = Clause.get c 1 in
          assert (c0 <> c1);
          Clause.set_watches c (c0,c1);
          (* make sure watches are valid *)
          if is_false self c0 then (
            match propagate_in_clause_ self (Atom.neg c0) c with
            | Keep -> add_watch_ self (Atom.neg c0) c;
            | Remove -> ()
          ) else (
            add_watch_ self (Atom.neg c0) c
          );
          if is_false self c1 then (
            match propagate_in_clause_ self (Atom.neg c1) c with
            | Keep -> add_watch_ self (Atom.neg c1) c;
            | Remove -> ()
          ) else (
            add_watch_ self (Atom.neg c1) c
          )
      end;
      ()

    let add_clause_l self (c:atom list) =
      let c = Clause.of_list self.cstore c in
      add_clause self c

    let is_valid_drup (self:t) (c:Clause.t) : bool =
      (* negate [c], pushing each atom on trail, and see if we get [Conflict]
         by pure propagation *)
      try
        with_restore_trail_ self @@ fun () ->
        Clause.iter c
          ~f:(fun a ->
              if is_true self a then raise_notrace Conflict; (* tautology *)
              let a' = Atom.neg a in
              if is_true self a' then () else (
                set_atom_true self a'
              ));
        bcp_fixpoint_ self;

      (*
      (* slow sanity check *)
      Clause.Tbl.iter
        (fun c () ->
           if c_is_false_ self c then
            Log.debugf 0 (fun k->k"clause is false: %a" Clause.pp c))
        self.active_clauses;
         *)

        false
      with Conflict ->
        true

    let del_clause (_self:t) (_c:Clause.t) : unit =
      () (* TODO *)
  end

end

