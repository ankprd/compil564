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
        succ = Ertltree.succ inst;
        pred = Label.S.empty;
        defs = Register.set_of_list d;
        uses = Register.set_of_list u;
        ins = Register.S.empty;
        outs = Register.S.empty;
    }) cfg;

    let preds : ((Ertltree.label, Ertltree.label list) Hashtbl.t) = Hashtbl.create 1 in
    
    (* C'est codé n'importe comment parce que je connais pas mutable et ses conséquences *)

    (* Pour chaque label "lbl" dans le cfg :
        Pour chaque successeur "s" de ce label :
         Ajouter l comme prédecesseur de s
    *)

    (* FIXME: un seul parcours est nécessaire, et preds ne sert à rien à priori *)
    Hashtbl.iter (fun lbl liveinfo -> 
        List.iter (fun s -> 
            try(let oldpreds = Hashtbl.find preds s in
                Hashtbl.replace preds s (lbl::oldpreds)
            ) with Not_found -> Hashtbl.add preds s []) liveinfo.succ
    ) assoc;

    Hashtbl.iter (fun lbl lpreds -> let lvinf = Hashtbl.find assoc lbl in 
        lvinf.pred = Label.S.of_list lpreds;
        Hashtbl.replace assoc lbl lvinf) preds;

    (* Arrivé ici on a rempli pred (normalement) *)

    
    failwith "not implemented"
