let visited = Hashtbl.create 17

type instr = Code of X86_64.text | Label of Label.t

let code = ref []

let emit l i = code := Code i :: Label l :: !code

let emit_wl (i : X86_64.text) = code := Code i :: !code

let labels = Hashtbl.create 17

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
    |Ltltree.Spilled n -> X86_64.ind ~ofs:n (register Register.rsp)

let rec lin (g : Ltltree.instr Label.M.t) l :unit=
  if not (Hashtbl.mem visited l) then begin
    Hashtbl.add visited l ();
    instr g l (Label.M.find l g)
  end else begin
    need_label l;
    emit_wl (X86_64.jmp (l :> string))
  end

and instr (g  : Ltltree.instr Label.M.t) l (instru : Ltltree.instr) : unit= 
    match instru with
    | Ltltree.Econst (n, r, l1) -> emit l (X86_64.movq (X86_64.imm32 n) (operand r)); lin g l1
    | Ltltree.Eload (r1, n, r2, l1) -> emit l (X86_64.movq (X86_64.ind ~ofs:n (register r1)) (X86_64.reg (register r2)))
    | Ltltree.Estore(r1, r2, n, l1) -> emit l (X86_64.movq (X86_64.reg (register r1)) (X86_64.ind ~ofs:n (register r2)))
    | Ltltree.Egoto l1 -> lin g l1
    | Ltltree.Ereturn -> emit l X86_64.ret
    | Ltltree.Emunop (Ops.Maddi n, op, l1) -> emit l (X86_64.addq (X86_64.imm32 n) (operand op)); lin g l1
    | Ltltree.Emunop (Ops.Msetei n, op, l1) -> emit l (X86_64.sete (X86_64.reg X86_64.r11b)); 
                                               emit_wl (X86_64.movzbq (X86_64.reg X86_64.r11b) (X86_64.r11));  
                                               emit_wl ((X86_64.movq) (X86_64.reg X86_64.r11 )(operand op)); 
                                               lin g l1 (*zbq ou sbq ?*) (*+ je comprend pas trop ce qu'est censee faire cette instruction, n est la valeur a mettre dans reg ? si c'est le cas, ca fait pas du tout ce qu'il faut ici*)
    | Ltltree.Emunop (Ops.Msetnei n, op, l1) -> emit l (X86_64.setne (X86_64.reg X86_64.r11b)); 
                                                emit_wl (X86_64.movzbq (X86_64.reg X86_64.r11b) (X86_64.r11));  
                                                emit_wl ((X86_64.movq) (X86_64.reg X86_64.r11 )(operand op)); 
                                                lin g l1 (*zbq ou sbq ?*)(*idem*)
    | Ltltree.Embinop (Ops.Mmov, r1, r2, l1) ->(
        match (r1, r2) with 
        |(Ltltree.Reg rr1, x) -> emit l (X86_64.movq (operand r1) (operand r2))
        |(x, Ltltree.Reg rr2) -> emit l (X86_64.movq (operand r1) (operand r2))
        |_ -> emit l (X86_64.movq (operand r1) (X86_64.reg X86_64.r11)); emit_wl (X86_64.movq (X86_64.reg X86_64.r11) (operand r2))
        );
        lin g l1

    (*type mbinop =
  | Madd
  | Msub
  | Mmul
  | Mdiv
  | Msete
  | Msetne
  | Msetl
  | Msetle
  | Msetg
  | Msetge*)
    (*
    (** les mêmes que dans ERTL, mais avec operand à la place de register *)
    | Embinop of mbinop * operand * operand * label
    | Emubranch of mubranch * operand * label * label
    | Embbranch of mbbranch * operand * operand * label * label
    | Epush of operand * label
    (** légèrement modifiée *)
    | Ecall of ident * label
    (** nouveau *)
    | Epop of register * label
    *)
    |_-> failwith "not done"
