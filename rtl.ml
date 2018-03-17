open Label
open Rtltree
open Register
open Set

let graph = ref (Label.M.empty : instr Label.M.t)
let locenv : ((Ttree.decl_var, register) Hashtbl.t) = Hashtbl.create 1

let generate i = let l = Label.fresh () in graph := Label.M.add l i !graph; l

let binop2Op bnop = match bnop with
	| Ptree.Beq  -> Ops.Msete
	| Ptree.Bneq -> Ops.Msetne
	| Ptree.Blt  -> Ops.Msetl
	| Ptree.Ble  -> Ops.Msetle
	| Ptree.Bgt  -> Ops.Msetg
	| Ptree.Bge  -> Ops.Msetge
	| _			 -> failwith "Unreachable binop2Op"

(* Ça peut se mémoïser ça non ? Changer la datastructure "structure" pour stocker une Hashtbl var -> index plutôt que la liste ordonnée pour obtenir l'index en O(1) *)
let indexInList l e =
	let rec aux i ll = match ll with
		| []   -> prerr_endline "not found element in struct"; i
		| x::q -> if x = e then i else aux (i+1) q in
	aux 0 l

let ptreeOp2Mbinop op = match op with
	| Ptree.Badd -> Ops.Madd
	| Ptree.Bsub -> Ops.Msub
	| Ptree.Bdiv -> Ops.Mdiv
	| Ptree.Bmul -> Ops.Mmul
	| _          -> failwith "Unimplemented"


let rec condition e truel falsel = 
	match e.Ttree.expr_node with
	| Ttree.Econst n when n = (Int32.of_int 0) -> falsel
	| Ttree.Econst n -> truel
	| Ttree.Eunop (unope, exprN) -> (
			match unope with 
			| Ptree.Unot -> condition exprN falsel truel
			| Ptree.Uminus -> condition exprN truel falsel
		)
	| Ttree.Ebinop (binope, expr1, expr2) -> (
			match binope with
			| Ptree.Band -> condition expr1 (condition expr2 truel falsel) truel
			| Ptree.Bor -> condition expr1 truel (condition expr2 truel falsel)
			| _ -> failwith "to do condition"
		)
	| _ -> failwith "to do condition"


	(* Arguments : l'expression, le registre où stocker le résultat de celle-ci, le label à qui passer la main à la fin
	   Renvoie : le label de l'entry point qui permet de calculer cette expression dans le graphe *)
	and expr (e : Ttree.expr) destr destl = match e.Ttree.expr_node with
		| Ttree.Econst n -> (generate (Econst (n, destr, destl)), true, Int32.to_int n)
		| Ttree.Eaccess_local nomVar ->  let regVar = Hashtbl.find locenv (e.Ttree.expr_typ, nomVar)
										 in (generate (Embinop (Ops.Mmov, regVar, destr, destl)), false, 0)

		(* Attention: ici on génère un simple mov de regvar vers destr, pas un load *)
		| Ttree.Eassign_local (nomVar, expAAss) -> 	let regVar = Hashtbl.find locenv (e.Ttree.expr_typ, nomVar) in
					                               	let labelAss = generate (Embinop (Ops.Mmov, destr, regVar, destl))in
					                            	expr expAAss destr labelAss

		| Ttree.Ebinop _ -> generateBinop e.Ttree.expr_node destr destl
		| Ttree.Eunop  _ -> generateUnop e.Ttree.expr_node destr destl
		| Ttree.Eaccess_field (ex, f)     -> let regInter = Register.fresh () in 
											 let typeEx = ex.Ttree.expr_typ in
											 let idField = 
											 	(match typeEx with
											 	| Ttree.Tstructp s -> indexInList s.Ttree.str_ordered_fields f.Ttree.field_name
												| _               -> failwith "Unreachable type"
											 	) in
											 let laccField = generate (Eload (regInter, idField * 8, destr, destl)) in
											 expr ex regInter laccField
		| Ttree.Eassign_field (e1, f, e2) -> let regAddrMem = Register.fresh () in
											 let regValExpr = Register.fresh () in
											 let typeEx = e1.Ttree.expr_typ in
											 let idField =  (match typeEx with
                											 	| Ttree.Tstructp s -> indexInList s.Ttree.str_ordered_fields f.Ttree.field_name
                												| _                -> failwith "Unreachable type"
                											) in
											 
                                             let laccField = generate (Estore (regValExpr, regAddrMem, idField * 8, destl)) in
                                             let lassDestr = generate(Embinop (Ops.Mmov, regValExpr, destr, laccField)) in
                                             (* FIXME *)
											 let (lCalcAddr, reducible, v) = expr e1 regAddrMem lassDestr in
											 expr e2 regValExpr lCalcAddr
		(* C'est très simple puisque on sait que tous les champs de structure font 8 bytes *)
		| Ttree.Esizeof s -> let k = 8 * (List.length s.Ttree.str_ordered_fields) in (generate (Econst ((Int32.of_int (k)), destr, destl)), true, k)

		(* "Fold right 2" permet de consommer 2 listes de la droite vers la gauche en même temps ! 
	       Pratique pour parcourir en même temps les expressions passées en paramètres et les registres dans lesquels on les met ! *)
		| Ttree.Ecall (fid, exprlist) -> let myregs = List.map (fun x -> Register.fresh ()) exprlist in
										 let lres = generate (Ecall (destr, fid, myregs, destl)) in
										 List.fold_right2 (fun arg reg (lab,_,_) -> expr arg reg lab) exprlist myregs (lres, false, 0)
 
  and stmt (s : Ttree.stmt) destl retr exitl = match s with
		| Ttree.Sreturn e -> let (l,_,_) = expr e retr exitl in l
		| Ttree.Sexpr e   -> let unusedReg = Register.fresh() in let (l,_,_) = expr e unusedReg destl in l
		| Ttree.Sskip     -> destl

		(* Idiome repris de "fct" *)
		| Ttree.Sblock (decvarl, stmtl) -> (let rec populate l = (match l with
    											| [] -> []
    											| x::ll -> let nreg = Register.fresh () in Hashtbl.add locenv x nreg; (nreg)::(populate ll)) in
    									   let _ = populate decvarl in
    									   let l1 = List.fold_right (fun stm labelnext -> stmt stm labelnext retr exitl) stmtl destl in
    									   List.iter  (fun v -> Hashtbl.remove locenv v) decvarl; l1)

		(* FIXME: utiliser ta fonction condition qui fait mieux le taf (même si avec ça, ça fonctionne) ! *)
		| Ttree.Sif (e, strue, sfalse)  -> let lfalse = stmt sfalse destl retr exitl and ltrue = stmt strue destl retr exitl in
										   let rintermed = Register.fresh () in
										   let comparee = generate (Emubranch (Ops.Mjz, rintermed, lfalse, ltrue)) in
										   let (computee, reducible, v) = expr e rintermed comparee in
										      (if reducible
                                                then (if v = 0 then lfalse else ltrue)
                                              else computee)
		| Ttree.Swhile (e, s) -> let lgoto = Label.fresh () in
								 let lInstr = stmt s lgoto retr exitl in
								 let regInter = Register.fresh () in
								 let lIf = generate (Emubranch (Ops.Mjz, regInter, destl, lInstr)) in
								 let (lcalc, reducible, v) = expr e regInter lIf in
                                    if (reducible && (v = 0)) then destl 
                                    else
								    begin
                                        graph := Label.M.add lgoto (Egoto lcalc) !graph; lcalc
                                    end
								 

    and generateBinop e destr destl = match e with
    	| Ttree.Ebinop (op, e1, e2) when (List.mem op [Ptree.Badd; Ptree.Bsub; Ptree.Bmul; Ptree.Bdiv]) ->  
    											let r2 = Register.fresh () in let lres = generate (Embinop (ptreeOp2Mbinop op, r2, destr, destl)) in
    											let (l2, red2, v2) = expr e2 r2 lres in
    											let (l1, red1, v1) = expr e1 destr l2 in 
                                                
                                                if red1 && red2 && (op <> Ptree.Bdiv || v2 <> 0) then begin
                                                    let finalval = (match op with | Ptree.Badd -> v1+v2 | Ptree.Bsub -> v1 - v2 | Ptree.Bmul -> v1 * v2
                                                                                  | Ptree.Bdiv -> v1 / v2 | _ -> failwith "unreachable") in
                                                    let l = generate (Econst (Int32.of_int finalval, destr, destl)) in
                                                    (l, true, finalval)
                                                end
                                                else
                                                    (l1, false, 0)
    	| Ttree.Ebinop (Ptree.Bor, e1, e2) -> (let rintermed = Register.fresh () in 
    										  let set1 = generate (Econst (Int32.of_int 1, destr, destl)) and set0 = generate (Econst (Int32.of_int 0, destr, destl)) in
    										  let compare2 = generate (Emubranch (Ops.Mjz, rintermed, set0, set1)) in
    										  let (compute2, red2, v2) = expr e2 rintermed compare2 in
    										  let compare1 = generate (Emubranch (Ops.Mjz, rintermed, compute2, set1)) in
    										  let (compute1, red1, v1) = expr e1 rintermed compare1 in
                                              (* FIXME *)
    										  (compute1, false, 0))
    	| Ttree.Ebinop (Ptree.Band, e1, e2) -> (let rintermed = Register.fresh () in 
    										  let set1 = generate (Econst (Int32.of_int 1, destr, destl)) and set0 = generate (Econst (Int32.of_int 0, destr, destl)) in
    										  let compare2 = generate (Emubranch (Ops.Mjz, rintermed, set0, set1)) in
    										  let (compute2, red2, v2) = expr e2 rintermed compare2 in
    										  let compare1 = generate (Emubranch (Ops.Mjz, rintermed, set0, compute2)) in
    										  let (compute1, red1, v1) = expr e1 rintermed compare1 in
                                              (* FIXME *)
    										  (compute1, false, 0))
    	| Ttree.Ebinop (op, e1, e2)			-> let rintermed = Register.fresh () in
    										   let lres = generate (Embinop (binop2Op op, rintermed, destr, destl)) in
    										   let (l2, red2, v2) = expr e2 rintermed lres in 
											   let (l1, red1, v1) = expr e1 destr l2 in
                                               (* FIXME *)
    										   (l1, false, 0)
    	| _ -> failwith "Unreachable generateBinop"

    and generateUnop e destr destl = match e with
    	| Ttree.Eunop (Ptree.Unot, e)  -> let lres = generate (Emunop ((Ops.Msetei (Int32.of_int 0)), destr, destl)) in let (le, red, v) = expr e destr lres in
                                            (if red then
                                                (le, true, if v = 0 then 1 else 0)
                                            else
                                                (le, red, v))
    	| Ttree.Eunop (Ptree.Uminus, e) -> generateBinop (Ttree.Ebinop (Ptree.Bsub, {Ttree.expr_node = Ttree.Econst (Int32.of_int 0); Ttree.expr_typ = Ttree.Tint}, e)) destr destl
    	| _ -> failwith "nope"

    let fct (f : Ttree.decl_fun) = let rec populate (l : Ttree.decl_var list) = match l with
    									| [] -> []
    									| x::ll -> let nreg = Register.fresh () in
    											   Hashtbl.add locenv x nreg;
    											   (nreg)::populate ll in
    							let fformals  = populate f.Ttree.fun_formals in
    							let fres      = Register.fresh () in 
    							let flocals   = Register.set_of_list (populate (fst f.Ttree.fun_body)) in
    							let fexit     = Label.fresh () in
    							graph := (Label.M.empty : instr Label.M.t);
    							let fentry    = List.fold_right (fun s labelnext -> stmt s labelnext fres fexit) (snd f.Ttree.fun_body) fexit in
	    						
	    						List.iter (fun v -> (Hashtbl.remove locenv v)) f.Ttree.fun_formals;
	    						List.iter  (fun v -> (Hashtbl.remove locenv v)) (fst f.Ttree.fun_body);

	    							{fun_name = f.Ttree.fun_name;
	    							fun_formals = fformals;
	    							fun_result = fres;
	    							fun_locals = flocals;
	    							fun_entry = fentry;
	    							fun_exit = fexit;
	    							fun_body = !graph}

    let program p = 
    let rec aux pl = match pl with
      | [] -> []
      | f::l -> (fct f)::(aux l) in
      {Rtltree.funs = (aux p.Ttree.funs)} 

