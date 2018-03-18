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

let kildall (assoc : live_info Label.map) = let ws = ref (Label.S.of_list (List.map fst (Label.M.bindings assoc))) in 
    let (ins : (Register.set Label.map ref)) = ref Label.M.empty and (outs : (Register.set Label.map ref)) = ref Label.M.empty in
    (* Initialise ins et outs à la map qui associe à un label un ensemble vide *)
    Label.M.iter (fun lab _ -> ins  := Label.M.add lab Register.S.empty !ins;
                               outs := Label.M.add lab Register.S.empty !outs
    ) assoc;

    (* Tant qu'il reste des gens à traiter dans ws (working set) *)
    while not (Label.S.is_empty !ws)
    do
        let lbl = Label.S.choose !ws in
        let liveinfo = Label.M.find lbl assoc in
        ws := Label.S.remove lbl !ws;

        (* On effectue une copie de in(lbl) *)
        let oldin = (Label.M.find lbl !ins) in

        (* newout c'est l'union des ins(s) sur chacun des successeurs *)
        let newout = List.fold_left (fun acc s -> Register.S.union acc (Label.M.find s !ins)) Register.S.empty liveinfo.succ in

        (* On remplace out dans outs *)
        outs := Label.M.remove lbl !outs;
        outs := Label.M.add lbl newout !outs;

        (* On calcule le newin qu'on met dans ins *)
        ins := Label.M.remove lbl !ins;
        let newin = Register.S.union liveinfo.uses (Register.S.diff newout liveinfo.defs) in
        ins := Label.M.add lbl newin !ins;

        (* Si on a changé in, ajouter tous les prédécesseurs de lbl dans ws *)
        if (Register.S.compare newin oldin) <> 0 then
        begin
            ws := Label.S.fold (fun lpred acc -> Label.S.add lpred acc) liveinfo.pred !ws;
        end
    done;

    !ins, !outs

(* Retourne assoc, qui à un label associer sa live_info *)
let liveness (cfg : Ertltree.cfg) : live_info Label.map = let (assoc : live_info Label.map ref) = ref Label.M.empty in
    (* On commence en initialisant les champs faciles dans assoc : les successeurs, les defs, les uses*)
    Label.M.iter (fun lab inst -> let (d,u) = Ertltree.def_use inst in
        assoc := Label.M.add lab {instr = inst; succ = Ertltree.succ inst; pred = Label.S.empty; defs = Register.set_of_list d; uses = Register.set_of_list u; ins = Register.S.empty; outs = Register.S.empty;} !assoc;
    ) cfg;

    (* preds va associer à un label la liste de ses prédecesseurs *)
    let preds : ((Ertltree.label, Ertltree.label list) Hashtbl.t) = Hashtbl.create 1 in
    
    (* Pour chaque label "lbl" dans le cfg :
        Pour chaque successeur "s" de ce label :
         Ajouter l comme prédecesseur de s
    *)
    Label.M.iter (fun lbl liveinfo ->
        List.iter (fun s -> 
            try(let oldpreds = Hashtbl.find preds s in
                Hashtbl.replace preds s (lbl::oldpreds);
            ) with Not_found -> (Hashtbl.add preds s [lbl])) liveinfo.succ;
    ) !assoc;

    (* Un peu maladroit, mais fait le taf pour remplir les prédécesseurs *)
    Hashtbl.iter (fun lbl lpreds -> let lvinf = Label.M.find lbl !assoc  in 
        assoc := Label.M.remove lbl !assoc;
        assoc := (Label.M.add lbl {instr = lvinf.instr; succ = lvinf.succ; pred = (Label.S.of_list lpreds); defs = lvinf.defs; uses = lvinf.uses; ins = lvinf.ins; outs = lvinf.outs;} !assoc);
    ) preds;

    (* Arrivé ici on a rempli pred dans assoc *)

    (* Du coup on a ce qu'il faut pour obtenir les in et out grâce à kildall *)
    let ins, outs = kildall !assoc in

    (* Et on finit de remplir assoc (l'iter sur la liste est un peu maladroit mais évite d'itérer sur les clés d'une map qu'on modifie pendant l'itération...) *)
    let labels = List.map fst (Label.M.bindings !assoc) in
    List.iter (fun lab -> let lvinf = Label.M.find lab !assoc in
                          assoc := Label.M.remove lab !assoc;
                          assoc := Label.M.add lab {instr = lvinf.instr; succ = lvinf.succ; pred = lvinf.pred; defs = lvinf.defs; uses = lvinf.uses; ins = (Label.M.find lab ins); outs = (Label.M.find lab outs);} !assoc

    ) labels;
    !assoc



(* Affiche un label et ses propriété de liveness analysis à côté *)
let print_live_info lbl liveinfo =
  let register_print_set = Register.print_set Format.std_formatter in
  Label.print Format.std_formatter lbl; print_string ": "; Ertltree.print_instr Format.std_formatter liveinfo.instr;
                print_string "  d={"; register_print_set liveinfo.defs; print_string "} u={";register_print_set liveinfo.uses;
                print_string "} i={"; register_print_set liveinfo.ins; print_string "} o={"; register_print_set liveinfo.outs;
                print_string "}\n"

(* Affiche le résultat de la liveness analysis pour une fonction donnée, la map qui stocke les infos et l'entry point *)
let print_live funcname (lmap : live_info Label.map) (entry : Ertltree.label) = 
  print_string ("=== LIVENESS(" ^ funcname ^ ") =================================================\n");
  let visited = Hashtbl.create 1 in

  let rec visitIt curlab =
    if not (Hashtbl.mem visited curlab) then
    begin
      Hashtbl.add visited curlab ();
      let liveinfo = Label.M.find curlab lmap in
      print_live_info curlab liveinfo;
      List.iter visitIt liveinfo.succ;
    end in

  visitIt entry
