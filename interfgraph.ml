type arcs = { prefs: Register.set; intfs: Register.set }
type igraph = arcs Register.map

let print ig =
  Register.M.iter (fun r arcs ->
    Format.printf "%s: prefs=@[%a@] intfs=@[%a@]@." (r :> string)
      Register.print_set arcs.prefs Register.print_set arcs.intfs) ig


let addPref regi curIgraphi prefi = 
    let adds reg pref curIgraph = 
        let found = 
            try Some (Register.M.find reg curIgraph) with Not_found -> None in 
        match found with
        |None -> Register.M.add reg {prefs = Register.S.singleton pref; intfs = Register.S.empty} curIgraph
        |Some {prefs = curP; intfs = curI} ->(
            let foundPref = 
                try Some (Register.S.find pref curI) with Not_found -> None
            in
            match foundPref with
            |None -> Register.M.add reg {prefs = Register.S.add pref curP; intfs = curI} curIgraph
            |_ -> curIgraph
            )
    in
    adds regi prefi (adds prefi regi curIgraphi)
    

let addInter regi interfi curIgraphi = 
    let adds reg interf curIgraph =
        let found = 
            try Some (Register.M.find reg curIgraph) with Not_found -> None in
        match found with
        |None -> Register.M.add reg {prefs = Register.S.empty; intfs = Register.S.singleton interf} curIgraph
        |Some {prefs = curP; intfs = curI} -> Register.M.add reg {prefs = Register.S.remove interf curP; intfs = Register.S.add interf curI} curIgraph
    in
    if regi = interfi then curIgraphi 
    else adds regi interfi (adds interfi regi curIgraphi)


let addIAndP setInterfs listePrefs reg curIgraph = 
    let graphInter = Register.S.fold (addInter reg) setInterfs curIgraph in
    List.fold_left (addPref reg) graphInter listePrefs

let traiteInstr (label : Label.t) liveInfo (curIgraph : arcs Register.M.t) : arcs Register.map =
    let (regInterfs, regPrefs) = 
        match liveInfo.Liveness.instr with
        |Ertltree.Embinop (Ops.Mmov, regOr, regDest, l) -> (Register.S.remove regOr liveInfo.Liveness.outs, [regOr]) (*liste for prefs because one or 0 elements and easier to write that way*)
        | _ -> (liveInfo.Liveness.outs, [])
    in
    Register.S.fold (addIAndP regInterfs regPrefs) liveInfo.Liveness.defs curIgraph

let make livGraph : igraph = 
    let tmpT : Label.t->Liveness.live_info->arcs Register.map->arcs Register.map = traiteInstr in
    let tmplivGraph : Liveness.live_info Label.map = livGraph in
    Label.M.fold tmpT  tmplivGraph (Register.M.empty : igraph)