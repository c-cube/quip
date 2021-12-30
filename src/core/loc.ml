
module Fmt = CCFormat
module P = Position

module Index = Line_index

module Input = struct
  type view =
    | String of string
    | File of string lazy_t

  type t = {
    view: view;
    idx: Index.t lazy_t;
  }

  let string s : t = {
    view=String s;
    idx=lazy (Index.of_string s);
  }

  let file file : t =
    let view = lazy (
      Printf.printf "reading %s\n%!" file;
      CCIO.File.read_exn file) in
    let idx = lazy (Index.of_string (Lazy.force view)) in
    { view=File view; idx; }

  let to_pp_loc_input (self:t) =
    match self.view with
    | String s -> Pp_loc.Input.string s
    | File (lazy s) -> Pp_loc.Input.string s

  let find_line_offset (self:t) ~line : int =
    Index.find_line_offset (Lazy.force self.idx) ~line

  let find_offset (self:t) ~line ~col : int =
    Index.find_offset (Lazy.force self.idx) ~line ~col
end

type ctx = {
  file: string;
  input: Input.t [@opaque];
} [@@deriving show]

type t = {
  ctx: ctx;
  start: Position.t;
  stop: Position.t;
}

let contains loc pos =
  Position.( loc.start <= pos && pos <= loc.stop )

let tr_position ~left (self:t) (pos:Position.t) : Lexing.position =
  let line_offset = Input.find_line_offset self.ctx.input ~line:(P.line pos) in
  {Lexing.pos_fname=self.ctx.file;
   pos_lnum=(P.line pos);
   pos_cnum=line_offset + (P.col pos) + (if left then 0 else 1);
   pos_bol=line_offset;
  }

let tr_loc (self:t) : Pp_loc.loc =
  tr_position ~left:true self self.start,
  tr_position ~left:false self self.stop

let none = {ctx={file="<none>"; input=Input.string ""};
            start=P.none; stop=P.none}

let pp_compact out (self:t) =
  if self == none then ()
  else if P.line self.start=P.line self.stop then (
    Format.fprintf out "in file '%s', line %d columns %d..%d"
      self.ctx.file (P.line self.start) (P.col self.start) (P.col self.stop)
  ) else (
    Format.fprintf out "in file '%s', line %d col %d to line %d col %d"
      self.ctx.file (P.line self.start) (P.col self.start) (P.line self.stop) (P.col self.stop)
  )

let pp out (self:t) : unit =
  if self == none then ()
  else (
    let input = Input.to_pp_loc_input self.ctx.input in
    Format.fprintf out "@[<v>%a@ %a@]"
      pp_compact self
      (Pp_loc.pp ~max_lines:5 ~input) [tr_loc self]
  )

let show = Fmt.to_string pp

let pp_l out (l:t list) : unit =
  if l=[] then ()
  else (
    let input = Input.to_pp_loc_input (List.hd l).ctx.input in
    let locs = List.map tr_loc l in
    Format.fprintf out "@[<v>%a@ %a@]"
      Fmt.(list ~sep:(return ";@ and ") pp_compact) l
      (Pp_loc.pp ~max_lines:5 ~input) locs
  )

let of_lexbuf' ~ctx (lexbuf:Lexing.lexbuf) : t =
  let open Lexing in
  let start = lexbuf.lex_start_p in
  let stop = lexbuf.lex_curr_p in
  let tr_pos p = P.make ~line:p.pos_lnum ~col:(p.pos_cnum - p.pos_bol + 1) in
  {ctx; start=tr_pos start; stop=tr_pos stop}

let of_lexbuf ~input (lexbuf:Lexing.lexbuf) : t =
  let open Lexing in
  let file = lexbuf.lex_start_p.pos_fname in
  let ctx={file; input} in
  of_lexbuf' ~ctx lexbuf

let union a b =
  {start=Position.min a.start b.start;
   stop=Position.max a.stop b.stop;
   ctx=a.ctx;}

let union_l = function
  | [] -> None
  | [l] -> Some l
  | l1 :: tl -> Some (List.fold_left union l1 tl)

let pp_opt out = function
  | None -> ()
  | Some pos -> Fmt.fprintf out "At %a" pp pos

let mk ~ctx start_line start_column stop_line stop_column =
  let start = P.make ~line:start_line ~col:start_column in
  let stop = P.make ~line:stop_line ~col:stop_column in
  { ctx; start; stop }

let mk_pair ~ctx (a,b)(c,d) = mk ~ctx a b c d

let set_file buf filename =
  let open Lexing in
  buf.lex_curr_p <- {buf.lex_curr_p with pos_fname=filename;};
  ()

let get_file buf =
  let open Lexing in
  buf.lex_curr_p.pos_fname
