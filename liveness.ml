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

let liveness (cfg : Ertltree.cfg) : live_info Label.map = failwith "not implemented"

let nfirst n l =
	let rec aux curr n l = match (n,l) with
							| (0,_)     -> curr
							| (_,l) -> aux ((List.hd l)::curr) (n-1) (List.tl l) in
	aux [] n l

(* Fonction helper qui ssocie à une instruction ERTL les registres qu'elle définit, utilise (dans cet ordre) *)
let def_use ertlinstr = match ertlinstr with
	| Ertltree.Econst (_,r,_) -> [r], []
    | Ertltree.Emunop (_,r,_) -> [r], [r]
    | Ertltree.Embinop (_, r1, r2, _) -> [r2], [r1; r2]
    | Ertltree.Emubranch (_, r, _, _) -> [], [r]
    | Ertltree.Embbranch (_, r1, r2, _, _) -> [], [r1; r2]
    | Ertltree.Eload (r1, _, r2, _) -> [r2], [r1]
    | Ertltree.Estore (r1, r2, _, _) -> [r2], [r1]
    | Ertltree.Eget_param (_, r, _) -> [r], []
    | Ertltree.Epush_param (r, _) -> [], [r]
	| Ertltree.Ereturn -> [], Register.rax :: (Register.callee_saved)
	| Ertltree.Ecall (_,n,_) -> Register.caller_saved, nfirst n Register.parameters
	(* (Egoto _|Ealloc_frame _|Edelete_frame _) *)
	| _ -> [], []