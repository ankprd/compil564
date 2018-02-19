open Ertltree

let graphERTL = ref (Label.M.empty : instr Label.M.t)

let addToGraph lab instru = graphERTL := Label.M.add lab instru !graphERTL

let instr curLabel curInstr = 
    match curInstr with
    |Rtltree.Econst (r, n, l) -> addToGraph curLabel  (Econst (r, n, l))
    |Rtltree.Eload (r1, n, r2, l)-> addToGraph curLabel  (Eload (r1, n, r2, l))
    |Rtltree.Estore (r1, r2, n, l) -> addToGraph curLabel (Estore (r1, r2, n, l))
    |Rtltree.Emunop (o, r, l) -> addToGraph curLabel (Emunop (o, r, l))
    |Rtltree.Embinop (o, r1, r2, l) -> addToGraph curLabel (Embinop (o, r1, r2, l))
    |Rtltree.Emubranch (b, r, l1, l2) -> addToGraph curLabel (Emubranch (b, r, l1, l2))
    |Rtltree.Embbranch (b, r1, r2, l1, l2) -> addToGraph curLabel (Embbranch (b, r1, r2, l1, l2))
    |Rtltree.Egoto l -> addToGraph curLabel (Egoto l)
    | Rtltree.Ecall (r, f, rl, l) -> print_string "Rtltree.Ecall\n";
                                     let nregs = min (List.length Register.parameters) (List.length rl) in
                                     let nstck = max ((List.length rl) - (List.length Register.parameters))  0 in
                                     if nstck = 0 then
                                     begin
                                        print_string "Lorsque rien sur la stack\n";
                                        let labcopyresult = Label.fresh () in
                                        addToGraph labcopyresult (Embinop (Mmov, r, Register.result, l));

                                        print_string "Copié dans le résultat !\n";
                                        let labcall = Label.fresh () in
                                        addToGraph labcall (Ecall (f, nregs, labcopyresult));
                                        
                                        print_string "Appelé la fonction !\n";
                                        
                                        let lablast = ref labcall in

                                        let rec addMov regl paraml = match regl, paraml with
                                                                    | [], []         -> ()
                                                                    | [], l          -> ()
                                                                    | l, []          -> failwith "impossible here : nstck = 0"
                                                                    | r::rll, p::pll -> let labcopy = Label.fresh () in
                                                                                          addToGraph labcopy (Embinop (Mmov, r, p, !lablast));
                                                                                          lablast := labcopy;
                                                                                          addMov rll pll in
                                        addMov rl Register.parameters;
                                        print_string "Added !\n";
                                     end
                                   else
                                   failwith "Not yet"
    |_ -> failwith "TODO instr"

let fct (f: Rtltree.deffun) = 
    graphERTL := (Label.M.empty : instr Label.M.t);
    (*Instructions d'entree dans une fct*)
    let rec getParams funForm regList offset = 
        match (funForm, regList) with
        |([], _) -> f.Rtltree.fun_entry (*tous les parametres sont dans les reg, on peut entrer dans la fct*)
        |(rf::f, []) -> 
            let labelSuiv = getParams f [] (offset + 8) in 
            let curLabel = Label.fresh () in
            addToGraph curLabel (Eget_param(offset, rf, labelSuiv)); curLabel
        |(rf::f, rr::l) -> 
            let labelSuiv = getParams f l offset in
            let curLabel = Label.fresh () in
            addToGraph curLabel (Embinop(Mmov, rr, rf, labelSuiv)); curLabel (*mov source, dest*)
    in
    let labelBeforeGetParams = getParams f.Rtltree.fun_formals Register.parameters 16
    in
    let rec savesCalleeReg regList =
        match regList with
        |[] -> labelBeforeGetParams
        |r::t -> 
            let labelSuiv = savesCalleeReg t in
            let curLabel = Label.fresh () in
            addToGraph curLabel (Embinop(Mmov, r, Register.fresh (), labelSuiv)); curLabel
    in 
    let labelBeforeCalleeSaving  = savesCalleeReg Register.callee_saved in
    let labelBeginFct = Label.fresh () in
    addToGraph labelBeginFct (Ealloc_frame labelBeforeCalleeSaving);

    Label.M.iter instr f.Rtltree.fun_body; 

    (*Instruction de sortie de la fct*)
    (*let labelRet = Label.fresh () in
    addToGraph labelRet Ereturn;
    let labelDelFrame = Label.fresh () in
    addToGraph labelDelFrame (Edelete_frame labelDelFrame)*)

    addToGraph f.Rtltree.fun_exit Ereturn;
    {
        fun_name = f.Rtltree.fun_name;
        fun_formals = List.length f.Rtltree.fun_formals; (* nb total d'arguments *)
        fun_locals = f.Rtltree.fun_locals;
        fun_entry = labelBeginFct;
        fun_body = !graphERTL;
    }

let program p = 
    let rec aux pl = match pl with
      | [] -> []
      | f::l -> (fct f)::(aux l) in
      {funs = (aux p.Rtltree.funs)} 