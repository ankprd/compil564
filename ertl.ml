open Ertltree

let graphERTL = ref (Label.M.empty : instr Label.M.t)

let addToGraph lab instru = graphERTL := Label.M.add lab instr !graphERTL

let instr curLabel curInstr = 
    match curInstr with
    |Rtltree.Econst (r, n, l) -> addToGraph curLabel  (Econst (r, n, l))
    |Rtltree.Eload (r1, n, r2, l)-> addToGraph curLabel  (Eload (r1, n, r2, l))
    |_ -> failwith "TODO instr"

let fct (f: Rtltree.deffun) = 
    graphERTL := (Label.M.empty : instr Label.M.t);
    Label.M.iter instr f.Rtltree.fun_body; 
    {
        fun_name = f.Rtltree.fun_name;
        fun_formals = List.length f.Rtltree.fun_formals; (* nb total d'arguments *)
        fun_locals = f.Rtltree.fun_locals;
        fun_entry = f.Rtltree.fun_entry;
        fun_body = !graphERTL;
    }

let program p = 
    let rec aux pl = match pl with
      | [] -> []
      | f::l -> (fct f)::(aux l) in
      {funs = (aux p.Rtltree.funs)} 