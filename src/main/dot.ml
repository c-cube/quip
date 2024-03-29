module Log = (val Logs.src_log (Logs.Src.create "quip.dot"))
module K = Kernel

open Ast.Proof
module T = Ast.Term

type name = string (** node name *)

type state = {
  terms: (string, Ast.Term.t) Hashtbl.t;
  clauses: (string, T.t array) Hashtbl.t;
  printed: (string, unit) Hashtbl.t;
  out: string CCVector.vector;
  mutable n: int;
}

let add_line (state:state) (s:string) : unit = CCVector.push state.out s
let add_linef state fmt = Fmt.kasprintf (add_line state) fmt

let cleanup_str s =
  CCString.flat_map
    (function
      | '\n' -> "\\l"
      | '"' -> "'"
      | c -> String.make 1 c)
    s

(** Expand definitions in term *)
let norm_term (st:state) (t:T.t) : T.t =
  let rule t = match T.view t with
    | T.Ref name -> CCHashtbl.get st.terms name
    | T.Var {name;_} -> CCHashtbl.get st.terms name
    | _ -> None
  in
  T.rw ~rule t

let norm_clause st (c:Ast.Clause.t) : T.t array =
  match c.view with
  | Ast.Clause.Clause_ref n ->
    (try Hashtbl.find st.clauses n
     with Not_found ->
       Log.err (fun k->k"cannot find clause %S" n);
       [||])
  | Ast.Clause.Clause lits ->
    Array.map (norm_term st) lits

(** A different type for proofs *)
type normalized_proof = {
  p: (T.t, T.t array, normalized_proof) view;
}

let rec norm_proof (st:state) (p:t) : normalized_proof =
  {p=
    (view p)
    |> map_view (norm_term st) (norm_clause st) (norm_proof st)
  }

let pp_lits out (c:T.t array) =
  Fmt.fprintf out "cl {@[<hv>%a@]}" Fmt.(array ~sep:(return "@ ∨ ") T.pp) c

(* allocate new name *)
let new_name (st:state): name =
  let s = Printf.sprintf "a_%d" st.n in
  st.n <- 1 + st.n;
  s

(* return the node name *)
let rec pp_proof_itself ?name state (self:t) : string =
  match name with
  | Some n -> n
  | None ->
    let p' = norm_proof state self in
    pp_proof_normalized state p'

and pp_proof_normalized (state:state) (p:normalized_proof) : string =
  let name = new_name state in
  let links = ref [] in (* outgoing edges *)

  let label =
    Fmt.asprintf "%a"
      (Ast.Proof.pp_view
         T.pp
         pp_lits
         (fun out p' ->
            let n' =
              match p'.p with
              | Named n' -> n'
              | _ -> pp_proof_normalized state p'
            in
            links := n' :: !links;
            Fmt.string out n'))
      p.p
    |> cleanup_str
  in

  (* define *)
  add_linef state
    {|@[%s [label="%s", shape="box", style="filled", fillcolor="lavenderblush1"];@]|}
    name label;

  (* add edges *)
  List.iter (fun n' -> add_linef state {|@[%s -> %s [label="%s"]@]|} name n' n') !links;
  name

and pp_step (state:state) (self:_ composite_step) : unit =
  match self.view with
  | S_define_t (name,t) ->
    Hashtbl.replace state.terms name t
  | S_declare_ty_const _ -> ()
  | S_declare_const _ -> ()
  | S_define_const { name; ty=_; rhs } ->
    Hashtbl.replace state.terms name rhs
  | S_step_anon {name; proof} ->
    if not (Hashtbl.mem state.printed name) then (
      Hashtbl.add state.printed name ();

      add_linef state
        {|@[%s [label="%s",shape="box",fillcolor="%s",style="filled"]@]|}
        name name "yellow";
      let p = pp_proof_itself state proof in
      add_linef state {|@[%s -> %s [label="proof(%s)"]@]|} name p name;
    )
  | S_step_c {name; res; proof} ->
    if not (Hashtbl.mem state.printed name) then (
      let res = Array.map (norm_term state) res in
      Hashtbl.add state.printed name ();
      Hashtbl.add state.clauses name res;

      let label =
        Fmt.asprintf "%a" pp_lits res |> cleanup_str
      in

      add_linef state
        {|@[%s [label="%s",shape="box",fillcolor="%s",style="filled"]@]|}
        name label (if res=[||] then "red" else "cyan");
      let p = pp_proof_itself state proof in
      add_linef state {|@[%s -> %s [label="proof(%s)"]@]|} name p name;
    );
    ()

let pp_top (state:state) (self:t) : unit =
  match view self with
  | Composite {assumptions=_; steps} ->
    Array.iter
      (fun step ->
         pp_step state step)
      steps;
  | _ ->
    ()

(** Print proof *)
let pr_proof p =
  let st = {
    terms=Hashtbl.create 32;
    printed=Hashtbl.create 32;
    clauses=Hashtbl.create 32;
    out=CCVector.create();
    n=0;
  } in
  pp_top st p;
  Fmt.asprintf "@[<v2>digraph proof {@,%a@,}@]@."
    Fmt.(iter ~sep:(return "@ ") string) (CCVector.to_iter st.out)
