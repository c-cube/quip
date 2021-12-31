
type view =
  | String of string
  | File of string lazy_t

type t = {
  view: view;
  idx: Line_index.t lazy_t;
}

let string s : t = {
  view=String s;
  idx=lazy (Line_index.of_string s);
}

let file file : t =
  let view = lazy (
    Printf.printf "reading %s\n%!" file;
    CCIO.File.read_exn file) in
  let idx = lazy (Line_index.of_string (Lazy.force view)) in
  { view=File view; idx; }

let to_pp_loc_input (self:t) =
  match self.view with
  | String s -> Pp_loc.Input.string s
  | File (lazy s) -> Pp_loc.Input.string s

(* TODO
let find_line_offset (self:t) ~line : int =
  Line_index.find_line_offset (Lazy.force self.idx) ~line

let find_offset (self:t) ~line ~col : int =
  Line_index.find_offset (Lazy.force self.idx) ~line ~col
   *)
