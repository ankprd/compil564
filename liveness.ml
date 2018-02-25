open Format

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

let liveness (cfg : Ertltree.cfg) : live_info Label.map = let (assoc : live_info Label.map ref) = ref Label.M.empty in
    Label.M.iter (fun lab inst -> let (d,u) = Ertltree.def_use inst in
        assoc := Label.M.add lab {instr = inst; succ = Ertltree.succ inst; pred = Label.S.empty; defs = Register.set_of_list d; uses = Register.set_of_list u; ins = Register.S.empty; outs = Register.S.empty;} !assoc;
    ) 
    cfg;

    let preds : ((Ertltree.label, Ertltree.label list) Hashtbl.t) = Hashtbl.create 1 in
    
    (* C'est codé n'importe comment parce que je connais pas mutable et ses conséquences *)

    (* Pour chaque label "lbl" dans le cfg :
        Pour chaque successeur "s" de ce label :
         Ajouter l comme prédecesseur de s
    *)

    (* FIXME: un seul parcours est nécessaire, et preds ne sert à rien à priori *)
    Label.M.iter (fun lbl liveinfo ->
        List.iter (fun s -> 
            try(let oldpreds = Hashtbl.find preds s in
                Hashtbl.replace preds s (lbl::oldpreds);
            ) with Not_found -> (Hashtbl.add preds s [lbl])) liveinfo.succ;
    ) !assoc;

    Hashtbl.iter (fun lbl lpreds -> let lvinf = Label.M.find lbl !assoc  in 
        assoc := Label.M.remove lbl !assoc;
        assoc := (Label.M.add lbl {instr = lvinf.instr; succ = lvinf.succ; pred = (Label.S.of_list lpreds); defs = lvinf.defs; uses = lvinf.uses; ins = lvinf.ins; outs = lvinf.outs;} !assoc);
    ) preds;

    (* Arrivé ici on a rempli pred *)

    !assoc
