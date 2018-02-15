
open Ttree

(* utiliser cette exception pour signaler une erreur de typage *)
exception Error of string

let string_of_type = function
  | Tint       -> "int"
  | Tstructp x -> "struct " ^ x.str_name ^ " *"
  | Tvoidstar  -> "void*"
  | Ttypenull  -> "typenull"

let environnement : ((ident, typ) Hashtbl.t) = Hashtbl.create 2
let environnementFcts : ((string, Ttree.decl_fun) Hashtbl.t) = Hashtbl.create 2
let declaredStructs : ((ident, structure) Hashtbl.t)= Hashtbl.create 2

let print_ident identifiant typeId = print_string identifiant

let ttreeTypeToString t = match t with
  | Tint -> "int"
  | Tstructp structName -> structName.str_name
  | Ttypenull -> "null"
  | Tvoidstar -> "void star"


let compatibleTypes t1 t2 = match t1 with
  | Tint -> t2 = Tint || t2 = Ttypenull
  | Ttypenull -> t2 = Tint || t2 = Ttypenull || t2 = Tvoidstar || (match t2 with | Tstructp _ -> true | _ -> false)
  | Tvoidstar -> (match t2 with 
                   | Tstructp s -> true
                   | Tvoidstar  -> true
                   | Ttypenull  -> true
                   | _          -> false)
  (* FIXME: c'est pas Tstructp s2 when s1 == s2 plutôt ? Là je crois que le deuxième s1 masque le premier *)
  | Tstructp s1 -> (match t2 with 
                   | Tstructp s1 -> true
                   | Tvoidstar -> true
                   | Ttypenull -> true
                   | _ -> false)


let declareVar addToEnv ((ptype, nom): Ptree.decl_var) =
  (*print_string "ajout de la variable "; print_string nom.Ptree.id; if addToEnv then print_endline " pour de vrai";
  print_string "var déclarées :"; Hashtbl.iter print_ident environnement; print_newline ();*)
  match ptype with 
  | Ptree.Tint -> (if addToEnv then Hashtbl.add environnement nom.Ptree.id Ttree.Tint); (Ttree.Tint, nom.Ptree.id)
  | Ptree.Tstructp s -> 
      try (
        let typeS = Hashtbl.find declaredStructs s.Ptree.id in
        (if addToEnv then Hashtbl.add environnement nom.Ptree.id (Tstructp typeS));
        (Tstructp typeS, nom.Ptree.id)
      )
      with Not_found -> raise (Error (String.concat "" ["Undeclared structure : "; s.Ptree.id]))(*la structure n'existe pas*)

(*let declareFct (typF, (nomF : Ptree.ident)) =
  match typF with 
  | Ptree.Tint -> Hashtbl.add environnementFcts nomF.Ptree.id Ttree.Tint; (Ttree.Tint, nomF.Ptree.id) (*exception su double declaration ?*)
  | Ptree.Tstructp s -> 
      try(
        let typeF = Hashtbl.find declaredStruct s.Ptree.id in
        Hashtbl.add environnementFcts nomF.Ptree.id (Tstructp typeF);
        (Tstructp typeF, nomF.Ptree.id)
      )  
      with Not_found -> raise (Error ((String.concat "" ["Undeclared structure : "; s.Ptree.id])))
*)
let declareStruct ((nom, listeVar) : Ptree.decl_struct) = 
  try
    (
    	let _ = Hashtbl.find declaredStructs nom.Ptree.id in
    	raise (Error ("Redefinition of structure " ^ nom.Ptree.id))
    ) with Not_found -> Hashtbl.add declaredStructs nom.Ptree.id {str_name = nom.Ptree.id; str_fields = (Hashtbl.create 0); str_ordered_fields = []};
  try (
    let fields = Hashtbl.create 2 in
    let listeF = List.map (declareVar false) listeVar in
    let ordered = ref [] in
    let ajToField (typeF, nomF) = Hashtbl.add fields nomF {field_name = nomF; field_typ = typeF}; ordered := (nomF::!ordered) in
    List.iter ajToField listeF;

    Hashtbl.add declaredStructs nom.Ptree.id {str_name = nom.Ptree.id; str_fields = fields; str_ordered_fields = List.rev !ordered}
  )
  with Error s -> raise (Error (String.concat "" ["In struct "; nom.Ptree.id; " : "; s]))

let declareFct name (df : Ttree.decl_fun) = try(let _ = Hashtbl.find environnementFcts name in
												raise (Error "Redefining a function is illegal !")
												) with Not_found -> Hashtbl.add environnementFcts name df

let rec program p =
  match p with
  |(Ptree.Dstruct s)::t -> declareStruct s; program t
  |(Ptree.Dfun f)::t -> let tf = typeFct f in {funs = tf::((program t).funs)}
  |[] -> {funs = []}

and typeFct f = 
  try (
    let (typeF, nomF) = (pType2Ttype f.Ptree.fun_typ, f.Ptree.fun_name) in
    (* Cette fonction déclare toutes les variables dans l'environnement et nous les retourne typées au sens de Ttree *)
    let rec declareArgs listArgs = 
      match listArgs with
      	| [] -> []
      	| x::t -> let (xId, xTy) = declareVar true x and res = declareArgs t in ((xId, xTy)::res) in
    
    (* Maintenant qu'on a typé les arguments, on peut déclarer la fonction dans environnementFcts *)
    let listArgs = declareArgs f.Ptree.fun_formals in
		declareFct nomF.Ptree.id {fun_typ = typeF; fun_name = nomF.Ptree.id; fun_formals = listArgs; fun_body = ([], [])};

    let (declVar, listInstr) = f.Ptree.fun_body in
    let listVars = declareArgs declVar in
    let listInstT = List.map (typeStmt typeF) listInstr in
    

    (* On supprime tout ce qu'on a ajouté dans l'environnement *)
    List.iter (fun c -> (Hashtbl.remove environnement (snd c))) (listVars);
    List.iter (fun c -> (Hashtbl.remove environnement (snd c))) (listArgs);
    
    (* Grosse optimisation: je ne stocke pas le body puisque je n'ai pas dans l'idée de m'en resservir après *)
    {fun_typ = typeF; fun_name =  nomF.Ptree.id; fun_formals  = listArgs; fun_body = (listVars, listInstT)}
  )
  with Error errorMsg -> raise (Error (String.concat "" ["In function "; f.Ptree.fun_name.Ptree.id; " : "; errorMsg])) (*Quand une erreur est détectée, elle est complétée par la localisation dans la fonction*)

and typeBinop b e1 e2 = let te1 = typeExpr e1 and te2 = typeExpr e2 in
	match b with
  		| Ptree.Beq | Ptree.Bneq | Ptree.Blt | Ptree.Ble | Ptree.Bgt | Ptree.Bge -> (if compatibleTypes te1.expr_typ te2.expr_typ then 
  																					{expr_node = Ttree.Ebinop (b, te1, te2); expr_typ = Ttree.Tint} 
  																				else
  																					raise (Error "Cannot apply comparison on these operands"))
  		| Ptree.Badd | Ptree.Bsub | Ptree.Bmul | Ptree.Bdiv -> (if (compatibleTypes te1.expr_typ Ttree.Tint) && (compatibleTypes te2.expr_typ Ttree.Tint) then
  																	{expr_node = Ttree.Ebinop (b, te1, te2); expr_typ = Ttree.Tint} 
  																else
  																	raise (Error "Cannot apply arithmetic on these operands"))
  		| Ptree.Band | Ptree.Bor -> {expr_node = Ttree.Ebinop (b, te1, te2); expr_typ = Ttree.Tint} 


and typeStmt expectedFctType s = 
  (*print_string "treating instr, liste var décl "; print_int (Hashtbl.length environnement);
  Hashtbl.iter print_ident environnement; 
  print_endline "";*)
  match s.Ptree.stmt_node with
    | Ptree.Sreturn e -> 
        (let typeRet = typeExpr e in 
        if compatibleTypes typeRet.expr_typ expectedFctType then Ttree.Sreturn (typeExpr e) 
        else raise (Error (String.concat "" ["Expression has type "; ttreeTypeToString typeRet.expr_typ; " but type "; ttreeTypeToString expectedFctType; " was expected for return value"])))
    |Ptree.Sskip -> Ttree.Sskip
    |Ptree.Sexpr e -> Ttree.Sexpr (typeExpr e)
    |Ptree.Sif (e, s1, s2) -> Ttree.Sif (typeExpr e, typeStmt expectedFctType s1, typeStmt expectedFctType s2)
    |Ptree.Swhile (e, sw) -> Ttree.Swhile (typeExpr e, typeStmt expectedFctType sw)
    |Ptree.Sblock (listeVarP, listeInstrP) ->
      (*On déclare les vars, en les ajoutant à l'environnement, on traite les instructions, on suppr les vars*)
      let listeVarT = List.map (declareVar true) listeVarP in
      let listeInstrP = List.map (typeStmt expectedFctType) listeInstrP in
      List.iter (fun c -> (Hashtbl.remove environnement (snd c))) (listeVarT);
      Ttree.Sblock (listeVarT, listeInstrP)

and typeExpr e = match e.Ptree.expr_node with
     | Ptree.Econst x when x = Int32.of_int 0 	-> {expr_node = Ttree.Econst x; expr_typ = Ttree.Ttypenull} (*zero était compris comme le nom de variable "zero" donc matchait tout*)
     | Ptree.Econst x 							-> {expr_node = Ttree.Econst x; expr_typ = Ttree.Tint}
     | Ptree.Eright (Ptree.Lident nomLident) ->  {expr_node = Ttree.Eaccess_local nomLident.Ptree.id; expr_typ = typeLIdent nomLident}
     | Ptree.Eright (Ptree.Larrow (expres, nomLarrow)) -> 
          let (exprRes, fieldRes) = typeLarrow (Ptree.Larrow (expres, nomLarrow)) in
          {expr_node = Ttree.Eaccess_field (exprRes, fieldRes); expr_typ = fieldRes.field_typ}
     | Ptree.Eassign (Ptree.Lident nomLident, expres) -> 
          let typeRes = typeLIdent nomLident in
          let typeExprAAss = typeExpr expres in
          if compatibleTypes typeRes typeExprAAss.expr_typ then {expr_node = Ttree.Eassign_local (nomLident.Ptree.id, typeExprAAss); expr_typ = typeLIdent nomLident}
          else raise (Error ("Tried to assign value of type "^(ttreeTypeToString typeExprAAss.expr_typ)^" to var of type "^(ttreeTypeToString typeRes)))
     | Ptree.Eassign (Ptree.Larrow (expres, nomLarrow), expresAAss) ->
          let (expreLarrow, fieldRes) = typeLarrow (Ptree.Larrow (expres, nomLarrow)) in
          let typeExprAAss = typeExpr expresAAss in
          if compatibleTypes fieldRes.field_typ typeExprAAss.expr_typ then  {expr_node = Ttree.Eassign_field (expreLarrow, fieldRes, typeExprAAss); expr_typ = fieldRes.field_typ}
          else raise (Error ("Tried to assign value of type "^(ttreeTypeToString typeExprAAss.expr_typ)^" to field of type "^(ttreeTypeToString fieldRes.field_typ)))

     (*| Ptree.Eright lval -> (match typeLVar lval with 
                            	| (None, Some (var, field))      -> {expr_node = Ttree.Eaccess_field (var, field); expr_typ = var.expr_typ}
              					| (Some (typeVar, nomVar), None) -> {expr_node = Ttree.Eaccess_local nomVar; expr_typ = typeVar}
        						| (_, _) -> raise (Error "this should never have happened, in typeExpr, Eright lval"))
     | Ptree.Eassign (lval, exprP) -> (
        let exprT = typeExpr exprP in
        match typeLVar lval with
        |(None, Some (var, field)) -> 
            if (compatibleTypes exprT.expr_typ field.field_typ) then {expr_node = Ttree.Eassign_field (var, field, exprT); expr_typ = var.expr_typ}
            else raise (Error (String.concat "" ["Tried to assign value of type "; ttreeTypeToString exprT.expr_typ; " to field of type "; ttreeTypeToString field.field_typ]))
        |(Some (typeVar, nomVar), None) ->
            if (compatibleTypes exprT.expr_typ typeVar) then {expr_node = Ttree.Eassign_local (nomVar, exprT); expr_typ = typeVar}
            else raise (Error (String.concat "" ["Tried to assign value of type "; ttreeTypeToString exprT.expr_typ; " to var of type "; ttreeTypeToString typeVar]))
        |(_, _) -> raise (Error "this should never have happended, in typeExpr, Eassign")
     )*)         
     | Ptree.Eunop (op, expr) -> (let exprT = typeExpr expr in match op with
     								| Ptree.Unot -> {expr_node = Ttree.Eunop (Ptree.Unot, exprT); expr_typ = Ttree.Tint}
     								| Ptree.Uminus -> (if compatibleTypes exprT.expr_typ Ttree.Tint then 
     													{expr_node = Ttree.Eunop (Ptree.Uminus, exprT); expr_typ = Ttree.Tint}
     												  else (* TODO: être plus précis *)
     												    raise (Error "Cannot negate something that is not compatible with an integer")))
     | Ptree.Ecall (funcname, exprl) when funcname.Ptree.id = "putchar" -> (if List.length exprl = 1 then
     																	let te = typeExpr (List.hd exprl) in
     																		if compatibleTypes te.expr_typ Ttree.Tint then {expr_node = Ttree.Ecall (funcname.Ptree.id, [te]); expr_typ = Ttree.Tint}
     																	else
     																		raise (Error ("putchar accepts only integer-like values as a parameter while you provided a parameter of type " ^ ttreeTypeToString te.expr_typ)) 
     																  else
     																	raise (Error "putchar takes exactly one argument !"))
     | Ptree.Ecall (funcname, exprl) when funcname.Ptree.id = "sbrk" -> (if List.length exprl = 1 then
     																	let te = typeExpr (List.hd exprl) in
     																		if compatibleTypes te.expr_typ Ttree.Tint then {expr_node = Ttree.Ecall (funcname.Ptree.id, [te]); expr_typ = Ttree.Tvoidstar}
     																	else
     																		raise (Error "sbrk accepts only integer-like values as a parameter !") 
     																  else
     																	raise (Error "sbrk takes exactly one argument !"))
     | Ptree.Ecall (funcname, exprl) -> (try(let functype = Hashtbl.find environnementFcts funcname.Ptree.id and
     									    	 typl = List.map typeExpr exprl in
     									    	 (* Vérifie que 2 à 2 respectivement, le type du ième truc passé et celui du ième argument attendu sont égaux *)
     									    	 if List.for_all2 (fun a b -> compatibleTypes a.expr_typ (fst b)) typl functype.fun_formals then
     									    	 	{expr_node = Ttree.Ecall (funcname.Ptree.id, typl); expr_typ = functype.fun_typ}
     									    	 else
     									    	    failwith "Parameter types mismatch"
     									    ) with | Not_found -> raise (Error ("Function " ^ funcname.Ptree.id ^ " is undefined !")) | Invalid_argument s -> raise (Error "Bad number of arguments !"))
     (* binop of binop * expr * expr *)
     | Ptree.Ebinop (b, e1, e2) -> typeBinop b e1 e2
     | Ptree.Esizeof x -> try(let stored = Hashtbl.find declaredStructs x.Ptree.id in {expr_node = Ttree.Esizeof {str_name = x.Ptree.id; str_fields = stored.str_fields; str_ordered_fields = stored.str_ordered_fields}; expr_typ = Ttree.Tint}) with Not_found -> raise (Error ("Undefined structure " ^ x.Ptree.id))

(* retourne (Some ident, Some (expr, field)), pour pouvoir gérer les 2 cas qui correspondent à des types différents *)
(*and typeLVar lvar  : (typ * ident) option * (expr * field) option = match lvar with
	| Ptree.Lident var -> (try (Some (Hashtbl.find environnement var.Ptree.id, var.Ptree.id), None) with Not_found -> raise (Error (String.concat "" ["Undeclared var "; var.Ptree.id])))
  | Ptree.Larrow (expression, nomField) -> (
        let var = typeExpr expression in (
        match var.expr_typ with
        	| Tstructp s -> 
          		let structTyp = (try Hashtbl.find declaredStructs s.str_name with Not_found -> raise (Error (String.concat "" ["Undeclared structure : "; s.str_name]))) in
          		let field = (try Hashtbl.find structTyp.str_fields nomField.Ptree.id with Not_found -> raise (Error (String.concat "" ["No field "; nomField.Ptree.id; " in struct "; s.str_name]))) in
          		(None, Some (var, field))
        	| _ -> raise (Error "Tried to access a field of something that is not a structure")
        )
      )*)
and typeLIdent lidentVar = try Hashtbl.find environnement lidentVar.Ptree.id with Not_found -> raise (Error (String.concat "" ["Undeclared var "; lidentVar.Ptree.id]))

and typeLarrow lvaria = 
  match lvaria with
  |Ptree.Lident l -> failwith "should never have happened in typeLarrow"
  |Ptree.Larrow (expression, nomField) ->
    (let var = typeExpr expression in (
    match var.expr_typ with
      | Tstructp s -> 
          let structTyp = (try Hashtbl.find declaredStructs s.str_name with Not_found -> raise (Error (String.concat "" ["Undeclared structure : "; s.str_name]))) in
          let fieldRes = 
              (try Hashtbl.find structTyp.str_fields nomField.Ptree.id with Not_found -> raise (Error (String.concat "" ["No field "; nomField.Ptree.id; " in struct "; s.str_name]))) in
              let fieldTyp = (match fieldRes.field_typ with
                              | Tstructp sf when sf.str_name = s.str_name -> Tstructp s
                              | _ -> fieldRes.field_typ
              ) in
              (var, {field_name = fieldRes.field_name; field_typ = fieldTyp})
      | _ -> raise (Error "Tried to access a field of something that is not a structure")
    ))
 (* Fait la conversion PtreeType -> TtreeType. Va piocher dans declaredStructs s'il le faut et gueule si ça foire *)
 (*
 and structure = {
  str_name  : ident;
  str_fields: (ident, field) Hashtbl.t;
  (* on pourra ajouter plus tard ici la taille totale de la structure *)
}*)
 and pType2Ttype ptype = match ptype with
 	| Ptree.Tint          -> Ttree.Tint
 	| Ptree.Tstructp name -> (try (let stored = Hashtbl.find declaredStructs name.Ptree.id in Ttree.Tstructp stored) with Not_found -> raise (Error ("Unknown structure " ^ name.Ptree.id)))