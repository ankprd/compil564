(*Coloration du graphe d' inference*)
(*TYPE GRAPH
type arcs = { prefs: Register.set; intfs: Register.set }
type igraph = arcs Register.map
*)

open Ltltree
open Format

type color = Ltltree.operand
type coloring = color Register.map

let print_color fmt = function
| Reg hr    -> fprintf fmt "%a" Register.print hr
| Spilled n -> fprintf fmt "stack %d" n
let print cm =
Register.M.iter
    (fun r cr -> printf "%a -> %a@\n" Register.print r print_color cr) cm

let addRegToTodo reg (arcsReg : Interfgraph.arcs) oldTodo =
    let setRegPoss =  Register.S.fold (Register.S.remove) arcsReg.Interfgraph.intfs Register.allocatable in
    Register.M.add reg setRegPoss oldTodo

let color graph = (*renvoie (coloration, nbCouleurs)*) (*Ca serait bien de rajouter plein de assert quand on sait au une map a qu un element par ex*)
    let todo = Register.M.fold addRegToTodo graph Register.M.empty in (*todo est une Map de key = Register et de value = set de RegisterAllocatable*)
    let curColo = ref Register.M.empty in (*Map de Register -> Ltltree.operand (= reg ou spilled)*)
    let nbSpilled = ref 0 in (*Spilled registers are numbered from 0 to nbSpilled - 1*)

    let delCouleur regColore colADel keyReg (oldColsPoss : Register.S.t) = 
        let arcReg = Register.M.find keyReg graph in
        if Register.S.mem regColore arcReg.Interfgraph.intfs then Register.S.remove colADel oldColsPoss 
        else oldColsPoss
    in

    let rec oneColorOnePref curTodo =
        let isOneColOnePref reg colPoss = 
            let arcsReg = Register.M.find reg graph in
            (Register.S.cardinal colPoss = 1) &&
            (Register.S.subset colPoss arcsReg.Interfgraph.prefs) in
        let regPoss = Register.M.filter isOneColOnePref curTodo in
        if Register.M.is_empty regPoss then oneColor curTodo
        else ( (*on a trouve au moins un reg qui a qu'une couleur qui en plus est dans ses prefs*)
            let (regChoisi, couleursPoss) = Register.M.min_binding regPoss in
            let couleur = Register.S.min_elt couleursPoss in
            curColo := Register.M.add regChoisi (Reg couleur) !curColo;
            let newTodo1 = Register.M.mapi (delCouleur regChoisi couleur) curTodo in
            let newTodo2 = Register.M.remove regChoisi newTodo1 in
            oneColorOnePref newTodo2
        )

    and oneColor curTodo = 
        let isOneColor reg colPoss = Register.S.cardinal colPoss = 1 in
        let regPoss = Register.M.filter isOneColor curTodo in
        if Register.M.is_empty regPoss then prefKnownCol curTodo
        else ( (*on a trouve au moins un reg qui a qu'une couleur*)
            let (regChoisi, couleursPoss) = Register.M.min_binding regPoss in
            let couleur = Register.S.min_elt couleursPoss in
            curColo := Register.M.add regChoisi (Reg couleur) !curColo;
            let newTodo1 = Register.M.mapi (delCouleur regChoisi couleur) curTodo in
            let newTodo2 = Register.M.remove regChoisi newTodo1 in
            oneColorOnePref newTodo2
        )
    
    and prefKnownCol curTodo = 
        let getColorsPrefs reg = 
            let addsColorPrefs regi (setCouleurs : Register.S.t) = 
                if not (Register.is_pseudo regi) then Register.S.add regi setCouleurs
                else ( (*Et si la prefs a ete spilled, on veut etre spilled pareil ? -> pour l instant si la pref a ete spilled, on fait genre elle est pas coloree donc bof*)
                    try (
                        match (Register.M.find regi !curColo) with 
                        |Reg r -> Register.S.add r setCouleurs
                        |Spilled n -> setCouleurs
                       (* Register.S.add (Register.M.find regi !curColo) setCouleurs *)
                    )
                    with Not_found -> setCouleurs
                )
            in
            (*let isColored regi = 
                not (Register.is_pseudo regi) ||
                (try Register.M.find regi !curColo; true with Not_found -> false) in*)
            let arcsReg = Register.M.find reg graph in
            Register.S.fold addsColorPrefs arcsReg.Interfgraph.prefs Register.S.empty
        in
        let isPrefKnownCol reg colPoss = not (Register.S.is_empty (Register.S.inter (getColorsPrefs reg) colPoss)) in
        let regPoss = Register.M.filter isPrefKnownCol curTodo in
        if Register.M.is_empty regPoss then colorPoss curTodo
        else ( (*on a trouve au moins un reg qui a une pref coloree*)
            let (regChoisi, couleursPoss) = Register.M.min_binding regPoss in
            let setCompatibleColors = Register.S.inter (getColorsPrefs regChoisi) couleursPoss in
            let couleur = Register.S.min_elt setCompatibleColors in
            curColo := Register.M.add regChoisi (Reg couleur) !curColo;
            let newTodo1 = Register.M.mapi (delCouleur regChoisi couleur) curTodo in
            let newTodo2 = Register.M.remove regChoisi newTodo1 in
            oneColorOnePref newTodo2
        )

    and colorPoss curTodo =
        let isColorPoss reg colPoss= not (Register.S.is_empty colPoss) in
        let regPoss = Register.M.filter isColorPoss curTodo in
        if Register.M.is_empty regPoss then onlySpill curTodo
        else ( (*on a trouve au moins un reg qui a au moins une couleur poss*)
            let (regChoisi, couleursPoss) = Register.M.min_binding regPoss in
            let couleur = Register.S.min_elt couleursPoss in
            curColo := Register.M.add regChoisi (Reg couleur) !curColo;
            let newTodo1 = Register.M.mapi (delCouleur regChoisi couleur) curTodo in
            let newTodo2 = Register.M.remove regChoisi newTodo1 in
            oneColorOnePref newTodo2
        )

    and onlySpill curTodo = 
        try (
            let (regChoisi, couleursPoss) = Register.M.choose curTodo in
            curColo := Register.M.add regChoisi (Spilled !nbSpilled) !curColo;
            nbSpilled := !nbSpilled + 1;
            let newTodo = Register.M.remove regChoisi curTodo in
            oneColorOnePref newTodo
        )
        with Not_found -> () (*todo est vide, on a tout colore*)
    in
    oneColorOnePref todo;
    (!curColo, !nbSpilled)
    





    