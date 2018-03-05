open Ltltree

let graphLTL = ref (Label.M.empty : instr Label.M.t)

let lookup (c : Coloration.coloring) (r : Register.t) =
  if Register.is_hw r then Reg r else M.find r c

let instr c frame_size eins = match eins with
  | Ertltree.Econst (n, r, l) -> Econst (n, lookup c r, l)
  | _ -> failwith "not yet implemented"

(*

(** une fonction LTL *)
type deffun = {
  fun_name : ident;
  fun_entry: label;
  fun_body : cfg;
}


(** Une fonction ERTL. *)
type deffun = {
  fun_name : ident;
  fun_formals : int; (* nb total d'arguments *)
  fun_locals : Register.set;
  fun_entry : label;
  fun_body : cfg;
}

(** Un programme ERTL. *)
type file = {
  funs : deffun list;
}
*)

let fct (f : Ertltree.deffun) : (Ltltree.deffun) = failwith "more to come here"
let program (p : Ertltree.file) : Ltltree.file = 
    let rec aux pl = match pl with
      | [] -> []
      | f::l -> (fct f)::(aux l) in
      {funs = (aux p.Ertltree.funs)} 