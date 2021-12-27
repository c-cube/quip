
type 'a iter = ('a -> unit) -> unit

module type ARG = sig
  type t
  val equal : t -> t -> bool
  val hash : t -> int
  val set_id : t -> int -> unit
  val on_new : t -> unit
end

module Make(A : ARG): sig
  type t
  val create : ?size:int -> unit -> t
  val hashcons : t -> A.t -> A.t
  val to_iter : t -> A.t iter
end = struct
  module W = Weak.Make(A)

  type t = {
    tbl: W.t;
    mutable n: int;
  }

  let create ?(size=1024) () : t = {tbl=W.create size; n=0}

  (* hashcons terms *)
  let hashcons st t =
    let t' = W.merge st.tbl t in
    if t == t' then (
      st.n <- 1 + st.n;
      A.set_id t' st.n;
      (try A.on_new t;
       with e ->
       W.remove st.tbl t; raise e) (* invalid *)
    );
    t'

  let to_iter st yield =
    W.iter yield st.tbl
end
