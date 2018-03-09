type arcs = { prefs: Register.set; intfs: Register.set }
type igraph = arcs Register.map

let print ig =
  Register.M.iter (fun r arcs ->
    Format.printf "%s: prefs=@[%a@] intfs=@[%a@]@." (r :> string)
      Register.print_set arcs.prefs Register.print_set arcs.intfs) ig


let addPref regi curIgraphi prefi = 
    let adds reg pref curIgraph = 
        match Register.M.find_opt reg curIgraph with
        |None -> Register.M.add reg {prefs = Register.S.singleton pref; intfs = Register.S.empty} curIgraph
        |Some {prefs = curP; intfs = curI} -> (
            match Register.S.find_opt pref intfs with
            |None -> Register.M.add reg {prefs = Register.S.add pref curP; intfs = curI} curIgraph
            |_ -> curIgraph
            )
    in
    adds regi prefi (adds prefi regi curIgraph)
    

let addInter regi interfi curIgraphi = 
    let adds reg interf curIgraph =
        match Register.M.find_opt reg curIgraph with
        |None -> Register.M.add reg {prefs = Register.S.empty; intfs = Register.S.singleton interf} curIgraph
        |Some {prefs = curP; intf = curI} -> Register.M.add reg {prefs = Register.S.remove interf curP; intfs = Register.S.add interf curI}
    in
    adds regi interfi (adds interfi regi curIgraphi)


let addIAndP setInterfs listePrefs reg curIgraph = 
    let graphInter = Register.S.fold (addInter reg) setInterfs curIgraph in
    List.fold_left (addPref reg) graphInter listePrefs

let traiteInstr label liveInfo curIgraph =
    let (regInterfs, regPrefs) = 
        match liveInfo.Liveness.instr with
        |Ertltree.Emunop (Ops.Mmov, reg, l) -> (Register.S.remove reg !liveInfo.Liveness.outs, [reg]) (*liste for prefs because one or 0 elements and easier to write that way*)
        | _ -> (!liveInfo.Liveness.outs, [])
    in
    Register.S.fold (addIAndP regInterfs regPrefs) liveInfo.Liveness.defs

let make livGraph : igraph = 
    Register.M.fold traiteInstr livGraph Register.M.empty 