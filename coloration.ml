(*Coloration du graphe d' inference*)
(*TYPE GRAPH
type arcs = { prefs: Register.set; intfs: Register.set }
type igraph = arcs Register.map
*)

open Ltltree

type color = Ltltree.operand
type coloring = color Register.map

let addRegToTodo reg arcsReg oldTodo =
    let setRegPoss =  Set.fold (Set.remove) arcsReg.intfs Register.allocatable in
    Map.add reg setRegPoss oldTodo

let color graph = (*renvoie (coloration, nbCouleurs)*) (*Ca serait bien de rajouter plein de assert quand on sait au une map a qu un element par ex*)
    let todo = Map.fold addRegToTodo graph Register.M.empty in (*todo est une Map de key = Register et de value = set de RegisterAllocatable*)
    let curColo = ref Register.M.empty in (*Map de Register -> Ltltree.operand (= reg ou spilled)*)
    let nbSpilled = ref 0 in (*Spilled registers are numbered from 0 to nbSpilled - 1*)

    let rec oneColorOnePref curTodo =
        let isOneColOnePref reg colPoss = 
            let arcsReg = Map.find reg graph in
            (Set.cardinal colPoss = 1) &&
            (Set.subset colPoss arcReg.prefs) in
        let regPoss = Map.filter isOneColOnePref curTodo in
        if Map.is_empty regPoss then oneColor curTodo
        else ( (*on a trouve au moins un reg qui a qu'une couleur qui en plus est dans ses prefs*)
            let (regChoisi, couleursPoss) = Map.min_binding regPoss 
            let couleur = Set.min_elt couleursPoss in
            let delCouleur oldColsPoss = Map.remove couleur oldColsPoss in
            curColo := Map.add regChoisi (Reg couleur) !curColo
            let newTodo1 = Map.map delCouleur oldTodo in
            let newTodo2 = Map.remove regChoisi newTodo1
            oneColorOnePref newTodo2
        )

    and oneColor curTodo = 
        let isOneColor reg colPoss = Set.cardinal colPoss = 1 in
        let regPoss = Map.filter isOneColor curTodo in
        if Map.is_empty regPoss then prefKnownCol curTodo
        else ( (*on a trouve au moins un reg qui a qu'une couleur*)
            let (regChoisi, couleursPoss) = Map.min_binding regPoss 
            let couleur = Set.min_elt couleursPoss in
            let delCouleur oldColsPoss = Map.remove couleur oldColsPoss in
            curColo := Map.add regChoisi (Reg couleur) !curColo
            let newTodo1 = Map.map delCouleur oldTodo in
            let newTodo2 = Map.remove regChoisi newTodo1
            oneColorOnePref newTodo2
        )
    
    and prefKnownCol curTodo = 
        let getColorsPrefs reg = 
            let addsColorPrefs regi setCouleurs = 
                if not (Register.is_pseudo regi) then Set.add (Reg regi) setCouleurs
                else (
                    try Set.add (Map.find regi !curColo) setCouleurs with Not_found -> setCouleurs
                )
            (*let isColored regi = 
                not (Register.is_pseudo regi) ||
                (try Map.find regi !curColo; true with Not_found -> false) in*)
            let arcsReg = Map.find reg graph in
            Set.fold getColorsPrefs arcsReg.prefs Set.empty
        in
        let isPrefKnownCol reg colPoss = not (Set.is_empty (Set.inter (getColorsPrefs reg) colPoss)) in
        let regPoss = Map.filter isPrefKnownCol curTodo in
        if Map.is_empty regPoss then colorPoss curTodo
        else ( (*on a trouve au moins un reg qui a une pref coloree*)
            let (regChoisi, couleursPoss) = Map.min_binding regPoss in
            let setCompatibleColors = Set.inter (getColorsPrefs reg) couleursPoss in
            let Reg couleur = Set.min_elt setCompatibleColors in
            let delCouleur oldColsPoss = Map.remove couleur oldColsPoss in
            curColo := Map.add regChoisi (Reg couleur) !curColo;
            let newTodo1 = Map.map delCouleur oldTodo in
            let newTodo2 = Map.remove regChoisi newTodo1
            oneColorOnePref newTodo2
        )

    and colorPoss curTodo =
        let isColorPoss reg colPoss= not Set.is_empty colPoss in
        let regPoss = Map.filter isColorPoss curTodo in
        if Map.is_empty regPoss then onlySpill curTodo
        else ( (*on a trouve au moins un reg qui a au moins une couleur poss*)
            let (regChoisi, couleursPoss) = Map.min_binding regPoss in
            let couleur = Set.min_elt couleursPoss in
            let delCouleur oldColsPoss = Map.remove couleur oldColsPoss in
            curColo := Map.add regChoisi (Reg couleur) !curColo;
            let newTodo1 = Map.map delCouleur oldTodo in
            let newTodo2 = Map.remove regChoisi newTodo1
            oneColorOnePref newTodo2
        )

    and onlySpill curTodo = 
        try (
            let (regChoisi, couleursPoss) = Map.choose curTodo in
            curColo := Map.add regChoisi (Spilled !nbSpilled) !curColo;
            nbSpilled := !nbSpilled + 1;
            let newTodo = Map.remove regChoisi curTodo in
            oneColorOnePref newTodo
        )
        with Not_found -> () (*todo est vide, on a tout colore*)
        
    oneColorOnePref todo;
    (!curColo, !nbSpilled)
    





    