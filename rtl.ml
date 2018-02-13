open Label
open Rtltree
open Register
open Set

let graph = ref (Label.M.empty : instr Label.M.t)
let locenv : ((Ttree.decl_var, register) Hashtbl.t) = Hashtbl.create 1

let generate i = let l = Label.fresh () in graph := Label.M.add l i !graph; l

(*
	    	type binop = | Beq | Bneq | Blt | Ble | Bgt | Bge |
	    	Badd | Bsub | Bmul | Bdiv | Band | Bor -> fait
    *)
    (*
	    Embinop of mbinop * register * register * label
	    attention au sens : [op r1 r2] représente [r2 <- r2 op r1]
	*)

	(*
	type mbinop =
  | Mmov
  | Madd
  | Msub
  | Mmul
  | Mdiv
  | Msete
  | Msetne
  | Msetl
  | Msetle
  | Msetg
  | Msetge
	*)

let binop2Op bnop = match bnop with
	| Ptree.Beq  -> Ops.Msete
	| Ptree.Bneq -> Ops.Msetne
	| Ptree.Blt  -> Ops.Msetl
	| Ptree.Ble  -> Ops.Msetle
	| Ptree.Bgt  -> Ops.Msetg
	| Ptree.Bge  -> Ops.Msetge
	| _			 -> failwith "Unreachable binop2Op"

let indexInList e l =
	let rec aux i ll = match ll with
		| []   -> i
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
		| Ttree.Econst n -> generate (Econst (n, destr, destl))
		| Ttree.Eaccess_local nomVar ->  let regVar = Hashtbl.find locenv (e.Ttree.expr_typ, nomVar) in generate (Eload (regVar, 0, destr, destl))
		| Ttree.Eassign_local (nomVar, expAAss) -> 	let regVar = Hashtbl.find locenv (e.Ttree.expr_typ, nomVar) in
					                               	let labelAss = generate (Estore (destr, regVar, 0, destl)) in
					                            	expr expAAss destr labelAss
		| Ttree.Ebinop _ -> generateBinop e.Ttree.expr_node destr destl
		| Ttree.Eunop  _ -> generateUnop e.Ttree.expr_node destr destl
		| Ttree.Eaccess_field (ex, f)     -> (match ex.Ttree.expr_typ with
												| Ttree.Tstructp s -> (let n = indexInList f.Ttree.field_name s.Ttree.str_ordered_fields and rintermed = Register.fresh () in
																	  let lres = generate (Eload (rintermed, n*8, destr, destl)) in expr ex rintermed lres)
												| _                -> failwith "Unreachable type")
		| Ttree.Eassign_field (e1, f, e2) -> (match (e1.Ttree.expr_typ, e1.Ttree.expr_node) with
												| (Ttree.Tstructp s, Ttree.Eaccess_local i)  -> (let regVar = Hashtbl.find locenv (e1.Ttree.expr_typ, i) in
																								 let n = indexInList f.Ttree.field_name s.Ttree.str_ordered_fields in
																								 let lres = generate (Estore (destr, regVar, n*8, destl)) in
																								 expr e2 destr lres)
												| (Ttree.Tstructp s, _) -> (let rinter = Register.fresh () and n = indexInList f.Ttree.field_name s.Ttree.str_ordered_fields in
																		    let lres = generate (Estore (destr, rinter, n*8, destl)) in
																		    let l1 = expr e1 rinter lres in expr e2 destr l1)
												| _                     -> failwith "Unreachable type")
		| Ttree.Esizeof s -> generate (Econst (Int32.of_int (8 * (List.length s.Ttree.str_ordered_fields)), destr, destl))
		(* Ecall of register * string * register list * label *)
		| Ttree.Ecall (fid, exprlist) -> let myregs = List.map (fun x -> Register.fresh ()) exprlist in
										 let lres = generate (Ecall (destr, fid, myregs, destl)) in
										 List.fold_right2 (fun arg reg lab -> expr arg reg lab) exprlist myregs lres
 
  and stmt (s : Ttree.stmt) destl retr exitl = match s with
		| Ttree.Sreturn e -> expr e retr exitl
		| Ttree.Sexpr e   -> let unusedReg = Register.fresh() in expr e unusedReg destl
		| Ttree.Sskip     -> destl
		(* Idiome repris de "fct" *)
		| Ttree.Sblock (decvarl, stmtl) -> (let rec populate l = (match l with
    											| [] -> []
    											| x::ll -> let nreg = Register.fresh () in Hashtbl.add locenv x nreg; (nreg)::populate ll) in
    									   let _ = populate decvarl in
    									   let l1 = List.fold_right (fun stm labelnext -> stmt stm labelnext retr exitl) stmtl destl in
    									   List.iter  (fun v -> Hashtbl.remove locenv v) decvarl; l1)
		| Ttree.Sif (e, strue, sfalse)  -> let lfalse = stmt sfalse destl retr exitl and ltrue = stmt strue destl retr exitl in
										   let rintermed = Register.fresh () in
										   let comparee = generate (Emubranch (Ops.Mjz, rintermed, lfalse, ltrue)) in
										   let computee = expr e rintermed comparee in
										   computee
		| _ -> failwith "unimplemented stmt"
    (*
	    	type binop = | Beq | Bneq | Blt | Ble | Bgt | Bge |
	    	Badd | Bsub | Bmul | Bdiv | Band | Bor -> fait
    *)
    (*
	    Embinop of mbinop * register * register * label
	    attention au sens : [op r1 r2] représente [r2 <- r2 op r1]
	*)

	(*
	type mbinop =
  | Mmov
  | Madd
  | Msub
  | Mmul
  | Mdiv
  | Msete
  | Msetne
  | Msetl
  | Msetle
  | Msetg
  | Msetge
	*)


    and generateBinop e destr destl = match e with
    	| Ttree.Ebinop (op, e1, e2) when (List.mem op [Ptree.Badd; Ptree.Bsub; Ptree.Bmul; Ptree.Bdiv]) ->  
    											let r2 = Register.fresh () in let lres = generate (Embinop (ptreeOp2Mbinop op, r2, destr, destl)) in
    											let l2 = expr e2 r2 lres in
    											let l1 = expr e1 destr l2 in l1
    	(* FIXME: vérifier que c'est bien le bon ordre dans les paramètres de mubranch *)
    	| Ttree.Ebinop (Ptree.Bor, e1, e2) -> (let rintermed = Register.fresh () in 
    										  let set1 = generate (Econst (Int32.of_int 1, destr, destl)) and set0 = generate (Econst (Int32.of_int 0, destr, destl)) in
    										  let compare2 = generate (Emubranch (Ops.Mjz, rintermed, set0, set1)) in
    										  let compute2 = expr e2 rintermed compare2 in
    										  let compare1 = generate (Emubranch (Ops.Mjz, rintermed, compute2, set1)) in
    										  let compute1 = expr e1 rintermed compare1 in
    										  compute1)
    	| Ttree.Ebinop (Ptree.Band, e1, e2) -> (let rintermed = Register.fresh () in 
    										  let set1 = generate (Econst (Int32.of_int 1, destr, destl)) and set0 = generate (Econst (Int32.of_int 0, destr, destl)) in
    										  let compare2 = generate (Emubranch (Ops.Mjz, rintermed, set0, set1)) in
    										  let compute2 = expr e2 rintermed compare2 in
    										  let compare1 = generate (Emubranch (Ops.Mjz, rintermed, set0, compute2)) in
    										  let compute1 = expr e1 rintermed compare1 in
    										  compute1)
    	| Ttree.Ebinop (op, e1, e2)			-> let rintermed = Register.fresh () in
    										   let lres = generate (Embinop (binop2Op op, rintermed, destr, destl)) in
    										   let l2 = expr e2 rintermed lres in let l1 = expr e1 destr l2 in
    										   l1
    	| _ -> failwith "Unimplemented binop"

(* type expr = {
  expr_node: expr_node;
  expr_typ : typ        (* chaque expression est décorée par son type *)
}*)
    and generateUnop e destr destl = match e with
    	| Ttree.Eunop (Ptree.Unot, e)  -> let lres = generate (Emunop ((Ops.Msetei (Int32.of_int 0)), destr, destl)) in let le = expr e destr lres in le 
    	| Ttree.Eunop (Ptree.Uminus, e) -> generateBinop (Ttree.Ebinop (Ptree.Bsub, {Ttree.expr_node = Ttree.Econst (Int32.of_int 0); Ttree.expr_typ = Ttree.Tint}, e)) destr destl
    	| _ -> failwith "nope"

(*and decl_fun = {
  fun_typ    : typ;
  fun_name   : ident;
  fun_formals: decl_var list;
  fun_body   : block
}
*)

(*
type deffun = {
  	fun_name : string;
  	fun_formals : register list;
  	fun_result : register;
  	fun_locals : Register.set;	(*toutes les variables locales de la fonction maintenant regroupées ici *)
  	fun_entry : label;
  	fun_exit : label;
  	fun_body : cfg;
}
*)
    let fct (f : Ttree.decl_fun) =
    							let rec populate (l : Ttree.decl_var list) = match l with
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

