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
    |_-> failwith "not done"
