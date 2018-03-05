open Ltltree

let graphLTL = ref (Label.M.empty : instr Label.M.t)

let lookup (c : Coloration.coloring) (r : Register.t) =
  if Register.is_hw r then Reg r else M.find r c

let addToGraph lab instru = graphLTL := Label.M.add lab instru !graphLTL


(*
(** Les différentes instructions ERTL *)
type instr =
  (** les mêmes que dans RTL *)
  | Eload of register * int * register * label
  | Estore of register * register * int * label
  | Embinop of mbinop * register * register * label MOUAIS
  | Eget_param of int * register * label
      (** [r <- ofs(rbp)] *)
  | Ereturn

*)

(* TODO: reprendre au cas par cas les erreurs qui seront relevées lors des tests *)
let instr c frame_size curLab curInstr = match curInstr with
  | Ertltree.Econst (n, r, l)  -> addToGraph curLab (Econst (n, lookup c r, l))
  | Ertltree.Egoto l           -> addToGraph curLab (Egoto l)
  | Ertltree.Ealloc_frame l    -> let ladd = Label.fresh () in
                                  addToGraph ladd (Emunop ((Ops.Maddi (Int32.of_int frame_size)), Register.rsp, l));
                                  let lmov = Label.fresh () in
                                  addToGraph lmov (Embinop (Ops.Mmov, Register.rsp, Register.rbp, ladd));
                                  addToGraph curLab (Epush (Register.rbp, lmov))
  | Ertltree.Edelete_frame l   -> let lpop = Label.fresh () in
                                  addToGraph lpop (Epop (Register.rbp, l));
                                  addToGraph lmov (Embinop (Ops.Mmov, Register.rbp, Register.rsp, lpop))
  | Ertltree.Ecall (f, n, l)   -> addToGraph curLab (Ecall (f, l))
  | Ertltree.Emburanch (ubr, r, l1, l2)       -> addToGraph curLab (Emubranch (ubr, lookup c r, l1, l2))
  | Ertltree.Embbranch (mbbr, r1, r2, l1, l2) -> addToGraph curLab (Embbranch (mbbr, lookup c r1, lookup c r2, l1, l2))
  | Ertltree.Emunop (op, r, l) -> addToGraph curLab (Emunop (n, lookup c r, l))
  | Ertltree.Epush_param (r, l) -> addToGraph curLab (Epush_param (lookup c r, l))
  (* TODO: les binops avec les deux arguments en mémoire -> nope. Relancer mais en ayant mis LE PREMIER ARGUMENT en registre *)
  | Ertltree.Embinop (Ops.Mmov, r1, r2, l) -> let c1 = lookup c r1 and c2 = lookup c r2 in 
                                              (if c1 = c2 then 
                                                addToGraph curLab (Egoto l)
                                              else
                                                addToGraph curLab (Embinop (Ops.Mmov, c1, c2, l)))
  | Ertltree.Embinop (Ops.Mmul, r1, r2, l) -> let c1 = lookup c r1 and let c2 = lookup c r2 in 
                                              (match c2 with
                                                 | Reg _ -> addToGraph curLab (Embinop (Ops.Mmul, c1, c2, l))
                                                 | _     -> failwith "TODO: bad mul")
  | 
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

let fct (f : Ertltree.deffun) : (Ltltree.deffun) =
    let liv  = Liveness.liveness fct.fun_body in
    let grph = Interfgraph.make liv in
    let (col, nbcol) = Coloration.color grph in

    Label.M.iter (fun lab eins -> instr col lab eins) f.Rtltree.fun_body; 

    {
        fun_name = f.Ertltree.fun_name;
        fun_entry = f.Ertltree.fun_entry;
        fun_body = !graphLTL;
    }

let program (p : Ertltree.file) : Ltltree.file = 
    let rec aux pl = match pl with
      | [] -> []
      | f::l -> (fct f)::(aux l) in
      {funs = (aux p.Ertltree.funs)} 