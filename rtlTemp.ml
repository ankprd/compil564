open Label
open Rtltree
open Register

let graph = ref (Label.M.empty : instr Label.M.t)

let generate i = let l = Label.fresh () in graph := Label.M.add l i !graph; l

let rec condition e truel falsel = failwith "Unimplemented condition"

	and expr (e : Ttree.expr) destr destl = let realExpr = e.Ttree.expr_node in
    										match realExpr with
													| Ttree.Econst n -> generate (Econst (n, destr, destl))
													| Ttree.Eaccess_local nomVar -> 
															let regVar = Hashtbl.find (e.expr_typ, nomVar) in
															generate (Eload (regVar, 0, destr, destl))
													| Ttree.Eassign_local (nomVar, expAAss) ->
															let regRes = Register.fresh () in
															let regVar = Hashtbl.find (e.expr_typ, nomVar) in
															let labelAss = generate (Estore (regRes, regVar, 0, destl)) in
															expr expAAss regRes labelAss
											    | _ -> failwith "not yet done expr"
    
	and stmt (s : Ttree.stmt) destl retr exitl = 
											match s with
													| Ttree.Sreturn e -> expr e retr exitl
    											| _ -> failwith "unimplemented stmt"

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
    let fct (f : Ttree.decl_fun) =  let locenv : ((Ttree.decl_var, register) Hashtbl.t) = Hashtbl.create 1 in
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

