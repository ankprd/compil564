let visited = Hashtbl.create 17

type instr = Code of X86_64.text | Label of Label.t

let code = ref []

let emit l i = code := Code i :: Label l :: !code

let emit_plain_label l = code := Label l :: !code

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
    (*on renvoie 3 elements car les types sont differents, et si true c'est le 3eme et pas le 2eme et si false c;est le 2eme*)
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
    | Ltltree.Eload (r1, n, r2, l1) -> emit l (X86_64.movq (X86_64.ind ~ofs:n (register r1)) (X86_64.reg (register r2)))
    | Ltltree.Estore(r1, r2, n, l1) -> emit l (X86_64.movq (X86_64.reg (register r1)) (X86_64.ind ~ofs:n (register r2)))
    | Ltltree.Egoto l1 -> emit_plain_label l; lin g l1
    | Ltltree.Ereturn -> emit l X86_64.ret
    | Ltltree.Emunop (Ops.Maddi n, op, l1) -> emit l (X86_64.addq (X86_64.imm32 n) (operand op)); lin g l1
    | Ltltree.Emunop (Ops.Msetei n, op, l1) -> emit l (X86_64.sete (X86_64.reg X86_64.r11b)); 
                                               emit_wl (X86_64.movzbq (X86_64.reg X86_64.r11b) (X86_64.r11)); (*on etend pas directement dans op car movzbq attend un registre en 2eme argument et op n'en est pas forcement un*)
                                               emit_wl (X86_64.movq (X86_64.reg X86_64.r11) (operand op));
                                               lin g l1 (*zbq ou sbq ?*) (*+ je comprend pas trop ce qu'est censee faire cette instruction, n est la valeur a mettre dans reg ? si c'est le cas, ca fait pas du tout ce qu'il faut ici*)
    | Ltltree.Emunop (Ops.Msetnei n, op, l1) -> emit l (X86_64.setne (X86_64.reg X86_64.r11b)); 
                                                emit_wl (X86_64.movzbq (X86_64.reg X86_64.r11b) (X86_64.r11)); (*on etend pas directement dans op car movzbq attend un registre en 2eme argument et op n'en est pas forcement un*)
                                               emit_wl (X86_64.movq (X86_64.reg X86_64.r11) (operand op));
                                               lin g l1 (*zbq ou sbq ?*)(*idem*)
    | Ltltree.Embinop (oper, r1, r2, l1) -> (
      let (isSet, opeF, opeT) = isSetAndTranslateBinop oper in
       match isSet with
        | 2 -> emit l (X86_64.pushq (X86_64.reg X86_64.rdx)); emit_wl (X86_64.idivq (operand r1)); emit_wl (X86_64.popq X86_64.rdx) (*attention on trashe rdx et r2 est rax normalement (cf generation de ertl)*)
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
    (*
    (** les mêmes que dans ERTL, mais avec operand à la place de register *)
    | Emubranch of mubranch * operand * label * label
    | Embbranch of mbbranch * operand * operand * label * label
    | Epush of operand * label
    (** légèrement modifiée *)
    | Ecall of ident * label
    (** nouveau *)
    | Epop of register * label
    *)
    | Ltltree.Epush (op, l1) -> emit l (X86_64.pushq (operand op)); lin g l1
    | Ltltree.Epop (r, l1) -> emit l (X86_64.popq (register r)); lin g l1
    | Ltltree.Ecall (id, l1) -> emit l (X86_64.call id); lin g l1
    (*  opérations de branchement unaires 
type mubranch =
  | Mjz
  | Mjnz
  | Mjlei of int32
  | Mjgi  of int32
*)
(* let je (z: label) = ins "je %s" z
let jz (z: label) = ins "jz %s" z
let jne(z: label) = ins "jne %s" z
let jnz(z: label) = ins "jnz %s" z
let js (z: label) = ins "js %s" z
let jns(z: label) = ins "jns %s" z
let jg (z: label) = ins "jg %s" z
let jge(z: label) = ins "jge %s" z
let jl (z: label) = ins "jl %s" z
let jle(z: label) = ins "jle %s" z
let ja (z: label) = ins "ja %s" z
let jae(z: label) = ins "jae %s" z
let jb (z: label) = ins "jb %s" z
let jbe(z: label) = ins "jbe %s" z
*)
    | Ltltree.Emubranch (mub, op, l1, l2) -> match mub with
                                                | Mjz -> emit l (X86_64.jz (l2 :> string)); lin g l1; lin g l2
                                                | _ -> failwith "not yet"
    |_-> failwith "not done"
