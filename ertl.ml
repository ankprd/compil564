open Ertltree

let graphERTL = ref (Label.M.empty : instr Label.M.t)

let instr curLabel curInstr = failwith "TODO"

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