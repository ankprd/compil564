open Ertltree

let graphERTL = ref (Label.M.empty : instr Label.M.t)

let addToGraph lab instru = graphERTL := Label.M.add lab instru !graphERTL

let instr curLabel curInstr = match curInstr with
    | Rtltree.Econst (r, n, l) -> addToGraph curLabel  (Econst (r, n, l))
    | Rtltree.Eload (r1, n, r2, l)-> addToGraph curLabel  (Eload (r1, n, r2, l))
    | Rtltree.Estore (r1, r2, n, l) -> addToGraph curLabel (Estore (r1, r2, n, l))
    | Rtltree.Emunop (o, r, l) -> addToGraph curLabel (Emunop (o, r, l))
    | Rtltree.Embinop (Mdiv, r1, r2, l) when r2 <> Register.rax -> let labcopy = Label.fresh () in 
                                                                   addToGraph labcopy (Embinop (Mmov, Register.rax, r2, l));
                                                                   let labdiv = Label.fresh () in
                                                                   addToGraph labdiv (Embinop (Mdiv, r1, Register.rax, labcopy));
                                                                   addToGraph curLabel (Embinop (Mmov, r2, Register.rax, labdiv));

    | Rtltree.Embinop (o, r1, r2, l) -> addToGraph curLabel (Embinop (o, r1, r2, l))
    | Rtltree.Emubranch (b, r, l1, l2) -> addToGraph curLabel (Emubranch (b, r, l1, l2))
    | Rtltree.Embbranch (b, r1, r2, l1, l2) -> addToGraph curLabel (Embbranch (b, r1, r2, l1, l2))
    | Rtltree.Egoto l -> addToGraph curLabel (Egoto l)
    | Rtltree.Ecall (r, f, rl, l) -> let nregs = min (List.length Register.parameters) (List.length rl) in
                                     let nstck = max ((List.length rl) - (List.length Register.parameters))  0 in
                                     if nstck = 0 then
                                     begin
                                        let labcopyresult = Label.fresh () in
                                        addToGraph labcopyresult (Embinop (Mmov, Register.result, r, l));

                                        let labcall = Label.fresh () in
                                        addToGraph labcall (Ecall (f, nregs, labcopyresult));
                                        
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
                                        addToGraph curLabel (Egoto !lablast);
                                     end
                                   else
                                   begin
                                        let labunstack = Label.fresh () in

                                        addToGraph labunstack (Emunop (Maddi (Int32.of_int (8*nstck)), Register.rsp, l));

                                        let labcopyresult = Label.fresh () in
                                        addToGraph labcopyresult (Embinop (Mmov, Register.result, r, labunstack));

                                        let labcall = Label.fresh () in
                                        addToGraph labcall (Ecall (f, nregs, labcopyresult));

                                        let lablast = ref labcall in

                                        let rec addMov regl paraml = match regl, paraml with
                                                                    | [], []         -> failwith "no way"
                                                                    | [], l          -> failwith "impossible here : nstck > 0"
                                                                    | l, []          -> l
                                                                    | r::rll, p::pll -> let labcopy = Label.fresh () in
                                                                                          addToGraph labcopy (Embinop (Mmov, r, p, !lablast));
                                                                                          lablast := labcopy;
                                                                                          addMov rll pll; in
                                        let remainingr = addMov rl Register.parameters in

                                        let rec pushThem regl = match regl with
                                                                    | []     -> ()
                                                                    | r::rll -> let labpush = Label.fresh () in
                                                                                addToGraph labpush (Epush_param (r, !lablast));
                                                                                lablast := labpush;
                                                                                pushThem rll; in
                                        pushThem remainingr;
                                        addToGraph curLabel (Egoto !lablast);
                                   end

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
            addToGraph curLabel (Embinop(Ops.Mmov, rr, rf, labelSuiv)); curLabel
    in
    let labelBeforeGetParams = getParams f.Rtltree.fun_formals Register.parameters 16
    in
    let rec savesCalleeReg regList =
        match regList with
        |[] -> (labelBeforeGetParams, [])
        |r::t -> 
            let (labelSuiv, lNReg) = savesCalleeReg t in
            let curLabel = Label.fresh () in
            let nReg = Register.fresh () in
            addToGraph curLabel (Embinop(Ops.Mmov, r, nReg, labelSuiv)); (curLabel, nReg::lNReg)
    in 
    let (labelBeforeCalleeSaving, regCalleeSaved)  = savesCalleeReg Register.callee_saved in
    let labelBeginFct = Label.fresh () in
    addToGraph labelBeginFct (Ealloc_frame labelBeforeCalleeSaving);

    Label.M.iter instr f.Rtltree.fun_body; 

    (*Instruction de sortie de la fct*)
    let labelRet = Label.fresh () in
    addToGraph labelRet Ereturn;
    let labelDelFrame = Label.fresh () in
    addToGraph labelDelFrame (Edelete_frame labelRet);
    let rec restoresCalleeReg regList lNReg = 
        match (regList, lNReg) with
        |([], []) -> labelDelFrame
        |(r::t, n::nt) -> 
            let labelSuiv = restoresCalleeReg t nt in
            let curLabel = Label.fresh () in
            addToGraph curLabel (Embinop(Ops.Mmov, n, r, labelSuiv)); curLabel
        | _ -> failwith "Not the same number of register saved and of calle saved reg"
    in
    let labelRestoresReg = restoresCalleeReg Register.callee_saved regCalleeSaved in
    addToGraph f.Rtltree.fun_exit (Embinop(Ops.Mmov, f.Rtltree.fun_result, Register.rax, labelRestoresReg));
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