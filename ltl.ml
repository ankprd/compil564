open Ltltree

let graphLTL = ref (Label.M.empty : instr Label.M.t)

let lookup (c : Coloration.coloring) (r : Register.t) =
  if Register.is_hw r then 
    Reg r 
  else 
    try Register.M.find r c
  with Not_found -> failwith ("Register has no coloring : cannot be looked up !")

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

let is_physical r = match r with
    | Reg _ -> true
    | Spilled _ -> false

(* TODO: reprendre au cas par cas les erreurs qui seront relevées lors des tests *)
let instr c frame_size curLab curInstr = match curInstr with
  | Ertltree.Econst (n, r, l)  -> addToGraph curLab (Econst (n, lookup c r, l))
  | Ertltree.Egoto l           -> addToGraph curLab (Egoto l)
  (* FIXME: optimiser quand frame_size = 0 *)
  | Ertltree.Ealloc_frame l    ->   let ladd = Label.fresh () in
                                    addToGraph ladd (Emunop ((Ops.Maddi (Int32.of_int (-8*frame_size))), Reg Register.rsp, l));
                                    let lmov = Label.fresh () in
                                    addToGraph lmov (Embinop (Ops.Mmov, Reg Register.rsp, Reg Register.rbp, ladd));
                                    addToGraph curLab (Epush (Reg Register.rbp, lmov))
                                  
  | Ertltree.Edelete_frame l   -> let lpop = Label.fresh () in
                                  addToGraph lpop (Epop (Register.rbp, l));
                                  addToGraph curLab (Embinop (Ops.Mmov, Reg Register.rbp, Reg Register.rsp, lpop))
                                  (*Eload of register * int * register * label*)
  | Ertltree.Eget_param (n, r, l) -> let cr = lookup c r in 
                                     (match cr with
                                        | Reg k         -> addToGraph curLab (Embinop (Mmov, Spilled n, Reg k, l))
                                        | Spilled k     -> (let lmov = Label.fresh () in
                                                            addToGraph lmov (Embinop (Mmov, Reg Register.tmp1, Spilled k, l));
                                                            addToGraph curLab (Embinop (Mmov, Spilled n, Reg Register.tmp1, lmov));
                                                            ))
  | Ertltree.Ecall (f, n, l)   -> addToGraph curLab (Ecall (f, l))
  | Ertltree.Emubranch (ubr, r, l1, l2)       -> addToGraph curLab (Emubranch (ubr, lookup c r, l1, l2))
  | Ertltree.Embbranch (mbbr, r1, r2, l1, l2) -> addToGraph curLab (Embbranch (mbbr, lookup c r1, lookup c r2, l1, l2))
  | Ertltree.Emunop (op, r, l) -> addToGraph curLab (Emunop (op, lookup c r, l))
  | Ertltree.Epush_param (r, l) -> addToGraph curLab (Epush (lookup c r, l))
  | Ertltree.Embinop (Ops.Mmov, r1, r2, l) -> let c1 = lookup c r1 and c2 = lookup c r2 in 
                                              (if c1 = c2 then 
                                                addToGraph curLab (Egoto l)
                                              else
                                                addToGraph curLab (Embinop (Ops.Mmov, c1, c2, l)))
  | Ertltree.Embinop (Ops.Mmul, r1, r2, l) -> let c1 = lookup c r1 and c2 = lookup c r2 in 
                                              (match c2 with
                                                 | Reg _ -> addToGraph curLab (Embinop (Ops.Mmul, c1, c2, l))
                                                 | Spilled k     -> (let lfromreg = Label.fresh() and lmul = Label.fresh () in 
                                                             addToGraph lfromreg (Embinop (Ops.Mmov, Reg Register.tmp1, c2, l));
                                                             addToGraph lmul (Embinop (Ops.Mmul, c1, Reg Register.tmp1, lfromreg));
                                                             addToGraph  curLab (Embinop (Ops.Mmov, c2, Reg Register.tmp1, lmul))))
  | Ertltree.Embinop (op, r1, r2, l) -> let c1 = lookup c r1 and c2 = lookup c r2 in 
                                              (match c2 with
                                                 | Reg _ -> addToGraph curLab (Embinop (op, c1, c2, l))
                                                 | Spilled k     -> let lcalc = Label.fresh () and lrestore = Label.fresh () in
                                                                      addToGraph lrestore (Embinop (Ops.Mmov, Reg Register.tmp1, c2, l));
                                                                      addToGraph lcalc (Embinop (op, c1, Reg Register.tmp1, lrestore));
                                                                     addToGraph curLab (Embinop (Ops.Mmov, c2, Reg Register.tmp1, lcalc))
                                                                   )
  | Ertltree.Estore (r1, r2, n, l) -> let c1 = lookup c r1 and c2 = lookup c r2 in 
                                      (match c1, c2 with
                                        | Reg rr1, Reg rr2 -> addToGraph curLab (Estore (rr1, rr2, n, l))

                                        | _ -> failwith "not yet implemented in store !")
  | Ertltree.Eload (r1, n, r2, l) -> let c1 = lookup c r1 and c2 = lookup c r2 in 
                                      (match c1, c2 with
                                        | Reg rr1, Reg rr2 -> addToGraph curLab (Eload (rr1, n, rr2, l))
                                        | Spilled k1, Reg rr2 -> (let lload = Label.fresh () in
                                                                 addToGraph lload (Eload (Register.tmp1, n, rr2, l));
                                                                 addToGraph curLab (Embinop (Ops.Mmov, Spilled k1, Reg Register.tmp1, l)))
                                        | Reg rr1, Spilled k2 -> (let lmov = Label.fresh () in 
                                                                  addToGraph lmov (Embinop (Ops.Mmov, Reg Register.tmp1, Spilled k2, l));
                                                                  addToGraph curLab (Eload (rr1, n, Register.tmp1, lmov)))
                                        | Spilled k1, Spilled k2 -> (let lload = Label.fresh () and lmov = Label.fresh () in
                                                                     addToGraph lmov (Embinop (Ops.Mmov, Spilled k1, Reg Register.tmp1, l));
                                                                     addToGraph lload (Eload (Register.tmp1, n, Register.tmp1, lmov));
                                                                     addToGraph curLab (Embinop (Ops.Mmov, Reg Register.tmp1, Spilled k2, lload))))
  | Ertltree.Ereturn -> addToGraph curLab (Ereturn)



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
    let liv  = Liveness.liveness f.fun_body in
    let grph = Interfgraph.make liv in
    let (col, nbcol) = Coloration.color grph in
    Label.M.iter (fun lab eins -> instr col nbcol lab eins) f.Ertltree.fun_body; 

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