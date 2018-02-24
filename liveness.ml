type live_info = 
{
         instr: Ertltree.instr;
          succ: Label.t list;    (* successeurs *)
  mutable pred: Label.set;       (* prédécesseurs *)
          defs: Register.set;    (* définitions *)
          uses: Register.set;    (* utilisations *)
  mutable  ins: Register.set;    (* variables vivantes en entrée *)
  mutable outs: Register.set;    (* variables vivantes en sortie *)
}

let liveness (cfg : Ertltree.cfg) : live_info Label.map = let assoc : ((Ertltree.label, live_info) Hashtbl.t) = Hashtbl.create 1 in
    (* Ertltree.cfg = Ertltree.instr Label.M.t *)
    Label.M.iter (fun lab inst -> let (d,u) = Ertltree.def_use inst in
        Hashtbl.add assoc lab {
        instr = inst;
        succ = [];
        pred = Label.S.empty;
        defs = Register.set_of_list d;
        uses = Register.set_of_list u;
        ins = Register.S.empty;
        outs = Register.S.empty;
    }) cfg;

    failwith "not implemented"
