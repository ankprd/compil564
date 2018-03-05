(*Coloration du graphe d' inference*)
(*TYPE GRAPH
type arcs = { prefs: Register.set; intfs: Register.set }
type igraph = arcs Register.map
*)

type color = Ltltree.operand
type coloring = color Register.map
let todo = Hashtbl.create 2

let addRegToTodo reg arcsReg =
    let setRegPoss =  Set.fold (Set.remove) arcsReg.intfs Register.allocatable in
    Hashtbl.add todo reg setRegPoss


let color graph = (*ren voie (coloration, nbCouleurs)*)
    Map.iter addRegToTodo graph;
    

    