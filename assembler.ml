let visited = Hashtbl.create 17

type instr = Code of X86_64.text | Label of Label.t

let code = ref []

let emit l i = code := Code i :: Label l :: !code

let emit_plain_label l = code := Label l :: !code

let emit_wl (i : X86_64.text) = code := Code i :: !code

let labels : ((Label.t, unit) Hashtbl.t) = Hashtbl.create 17

let need_label l = Hashtbl.add labels l ()

let register (rltl : Register.t) = match (rltl :> string) with
  | "%rax" -> X86_64.rax
  | "%rbx" -> X86_64.rbx
  | "%rcx" -> X86_64.rcx
  | "%rdx" -> X86_64.rdx
  | "%rsi" -> X86_64.rsi
  | "%rdi" -> X86_64.rdi
  | "%rbp" -> X86_64.rbp
  | "%rsp" -> X86_64.rsp
  | "%r8" -> X86_64.r8
  | "%r9" -> X86_64.r9
  | "%r10" -> X86_64.r10
  | "%r11" -> X86_64.r11
  | "%r12" -> X86_64.r12
  | "%r13" -> X86_64.r13
  | "%r14" -> X86_64.r14
  | "%r15" -> X86_64.r15
  | _ -> failwith "invalid register in assembler.register"

let operand opLtl = 
    match opLtl with
    |Ltltree.Reg r -> X86_64.reg (register r)
    |Ltltree.Spilled n -> X86_64.ind ~ofs:n (register Register.rbp)

let rec lin (g : Ltltree.instr Label.M.t) l :unit=
  if not (Hashtbl.mem visited l) then begin
    Hashtbl.add visited l ();
    instr g l (Label.M.find l g)
  end else begin
    need_label l;
    emit_wl (X86_64.jmp (l :> string))
  end

and instr (g  : Ltltree.instr Label.M.t) l (instru : Ltltree.instr) : unit= 
    (*1er element indique si set ou arith ou div, 2eme ou 3eme correspond a la traduction en assembleur*)
    let isSetAndTranslateBinop (ope : Ops.mbinop)  = 
      match ope with
      |Ops.Msete -> (1, X86_64.addq, X86_64.sete)
      |Ops.Msetne -> (1, X86_64.addq, X86_64.setne)
      |Ops.Msetl -> (1, X86_64.addq, X86_64.setl)
      |Ops.Msetle -> (1, X86_64.addq, X86_64.setle)
      |Ops.Msetge -> (1, X86_64.addq, X86_64.setge)
      |Ops.Msetg -> (1, X86_64.addq, X86_64.setg)
      |Ops.Madd -> (0, X86_64.addq, X86_64.sete)
      |Ops.Msub -> (0, X86_64.subq, X86_64.sete)
      |Ops.Mmul -> (0, X86_64.imulq, X86_64.sete)
      |Ops.Mmov -> (0, X86_64.movq, X86_64.sete)
      |Ops.Mdiv -> (2, X86_64.addq, X86_64.sete) (*on renvoie n' importe quoi, idivq a pas le bon type*)
    in

    match instru with
    | Ltltree.Econst (n, r, l1) -> emit l (X86_64.movq (X86_64.imm32 n) (operand r)); lin g l1
    | Ltltree.Eload (r1, n, r2, l1) -> emit l (X86_64.movq (X86_64.ind ~ofs:n (register r1)) (X86_64.reg (register r2))); lin g l1
    | Ltltree.Estore(r1, r2, n, l1) -> emit l (X86_64.movq (X86_64.reg (register r1)) (X86_64.ind ~ofs:n (register r2))); lin g l1
    | Ltltree.Egoto l1 -> emit_plain_label l; lin g l1
    | Ltltree.Ereturn -> emit l X86_64.ret
    | Ltltree.Emunop (Ops.Maddi n, op, l1) -> emit l (X86_64.addq (X86_64.imm32 n) (operand op)); lin g l1
    | Ltltree.Emunop (Ops.Msetei n, op, l1) -> emit l (X86_64.cmpq (X86_64.imm32 n) (operand op));  emit_wl (X86_64.sete (X86_64.reg X86_64.r11b)); 
                                               emit_wl (X86_64.movzbq (X86_64.reg X86_64.r11b) (X86_64.r11)); (*on etend pas directement dans op car movzbq attend un registre en 2eme argument et op n'en est pas forcement un*)
                                               emit_wl (X86_64.movq (X86_64.reg X86_64.r11) (operand op));
                                               lin g l1
    | Ltltree.Emunop (Ops.Msetnei n, op, l1) -> emit l (X86_64.cmpq (X86_64.imm32 n) (operand op)); emit l (X86_64.setne (X86_64.reg X86_64.r11b)); 
                                                emit_wl (X86_64.movzbq (X86_64.reg X86_64.r11b) (X86_64.r11)); (*on etend pas directement dans op car movzbq attend un registre en 2eme argument et op n'en est pas forcement un*)
                                               emit_wl (X86_64.movq (X86_64.reg X86_64.r11) (operand op));
                                               lin g l1
    | Ltltree.Embinop (oper, r1, r2, l1) -> (
      let (isSet, opeF, opeT) = isSetAndTranslateBinop oper in
       match isSet with
        | 2 -> emit l (X86_64.pushq (X86_64.reg X86_64.rdx)); 
               emit_wl (X86_64.movq (X86_64.reg X86_64.rax) (X86_64.reg X86_64.rdx));
               emit_wl (X86_64.sarq (X86_64.imm 32) (X86_64.reg X86_64.rdx));
               emit_wl (X86_64.idivq (operand r1)); 
               emit_wl (X86_64.popq X86_64.rdx) (*r2 est rax (cf generation de ertl)*)
        | 0 -> (match (r1, r2) with 
                  | (Ltltree.Reg rr1, x) -> emit l (opeF (operand r1) (operand r2))
                  | (x, Ltltree.Reg rr2) -> emit l (opeF (operand r1) (operand r2))
                  | _ -> emit l (X86_64.movq (operand r1) (X86_64.reg X86_64.r11)); emit_wl (opeF (X86_64.reg X86_64.r11) (operand r2)))
        | 1 -> emit l (X86_64.cmpq (operand r1) (operand r2));
                          emit_wl (opeT (X86_64.reg X86_64.r11b)); 
                          emit_wl (X86_64.movzbq (X86_64.reg X86_64.r11b) (X86_64.r11));
                          emit_wl (X86_64.movq (X86_64.reg X86_64.r11) (operand r2))
        | _ -> failwith "unreachable code"
      );
      lin g l1

    | Ltltree.Epush (op, l1) -> emit l (X86_64.pushq (operand op)); lin g l1
    | Ltltree.Epop (r, l1) -> emit l (X86_64.popq (register r)); lin g l1
    | Ltltree.Ecall (id, l1) -> emit l (X86_64.call id); lin g l1

    | Ltltree.Emubranch (mub, op, l1, l2) -> 
      let (valACmp, typeJump) = 
        match mub with
        |Ops.Mjz -> (X86_64.imm 0, X86_64.je)
        |Ops.Mjnz -> (X86_64.imm 0, X86_64.jne)
        |Ops.Mjlei i -> (X86_64.imm32 i, X86_64.jle)
        |Ops.Mjgi i -> (X86_64.imm32 i, X86_64.jg)
      in
      need_label l1;
      emit l (X86_64.cmpq valACmp (operand op));
      emit_wl (typeJump (l1 :> string));
      lin g l2;
      lin g l1

    | Ltltree.Embbranch (mub, op1, op2, l1, l2) -> 
        emit l (X86_64.cmpq (operand op1) (operand op2));
        let typeJmp = 
          match mub with
          |Ops.Mjl -> X86_64.jl
          |Ops.Mjle -> X86_64.jle
        in
        need_label l1;
        emit_wl (typeJmp (l1 :> string));
        lin g l2;
        lin g l1
