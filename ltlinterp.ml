
open Format
open Ops
open Memory
open Ltltree

let zero = 0L
let one = 1L

exception Error of string
let error s = raise (Error s)

module Stack = struct
  let max_size = 1_000_000
  let init_rsp = Int64.of_int (8 * max_size)
  type t = { stack: value array }
  let create () = { stack = Array.make max_size zero }
  let index p =
    if p mod 8 <> 0 then begin
      print_string "p = "; print_int p; print_string " !\n";
      error "mis-aligned stack access";
    end ;
    let p = p / 8 in
    if p < 0 || p >= max_size then error "access out of stack";
    p
  let get st ?(ofs = 0) p =
    let i = index (Int64.to_int p + ofs) in st.stack.(i)
  let set st ?(ofs = 0) p v =
    let i = index (Int64.to_int p + ofs) in st.stack.(i) <- v
end

type state = {
     mem: Memory.t;
  fundef: (string, deffun) Hashtbl.t;
    regs: (Register.t, Memory.value) Hashtbl.t; (* physiques *)
   stack: Stack.t;
}

let getr st r =
  try Hashtbl.find st.regs r with Not_found -> zero
let setr st r v =
  Hashtbl.replace st.regs r v

let no_pseudo r =
  error ("pseudo register " ^ r ^ " not allowed in LTL code")

let get st = function
  | Spilled ofs -> Stack.get st.stack ~ofs (getr st Register.rbp)
  | Reg r when Register.is_pseudo r -> no_pseudo (r :> string)
  | Reg r -> getr st r

let set st o v = match o with
  | Spilled ofs -> Stack.set st.stack ~ofs (getr st Register.rbp) v
  | Reg r when Register.is_pseudo r -> no_pseudo (r :> string)
  | Reg r -> setr st r v

let push st v =
  let rsp = Int64.sub (getr st Register.rsp) 8L in
  setr st Register.rsp rsp;
  Stack.set st.stack rsp v

let pop st =
  let rsp = getr st Register.rsp in
  let v = Stack.get st.stack rsp in
  setr st Register.rsp (Int64.add rsp 8L);
  v

let bool b = if b then one else zero

let unop st op r =
  let v = get st r in
  let v = match op with
    | Maddi n -> Int64.add (Int64.of_int32 n) v
    | Msetei n -> bool (Int64.of_int32 n = v)
    | Msetnei n -> bool (Int64.of_int32 n <> v) in
  set st r v

let binop st op r1 r2 =
  let v1 = get st r1 in
  let v2 = get st r2 in
  let v2 = match op with
    | Mmov -> assert false
    | Madd -> Int64.add v2 v1
    | Msub -> Int64.sub v2 v1
    | Mmul -> Int64.mul v2 v1
    | Mdiv when r2 <> Reg Register.rax -> error "div: r2 must be %rax"
    | Mdiv -> Int64.div v2 v1
    | Msete  -> bool (v2 =  v1)
    | Msetne -> bool (v2 <> v1)
    | Msetl  -> bool (v2 <  v1)
    | Msetle -> bool (v2 <= v1)
    | Msetg  -> bool (v2 >  v1)
    | Msetge -> bool (v2 >= v1) in
  set st r2 v2

let rec exec st gr l =
  let i =
    try Label.M.find l gr
    with Not_found -> error ("unknown label " ^ (l :> string )) in
  match i with
  | Econst (n, r, l) ->
    set st r (Int64.of_int32 n);
    exec st gr l
  | Eload (r1, ofs, r2, l) ->
    let p = getr st r1 in
    let v = Memory.get st.mem p ~ofs in
    setr st r2 v;
    exec st gr l
  | Estore (r1, r2, ofs, l) ->
    let p = getr st r2 in
    let v = getr st r1 in
    Memory.set st.mem p ~ofs v;
    exec st gr l
  | Emunop (op, r1, l) ->
    unop st op r1;
    exec st gr l
  | Embinop (Mmov, r1, r2, l) ->
    let v1 = get st r1 in
    set st r2 v1;
    exec st gr l
  | Embinop (op, r1, r2, l) ->
    binop st op r1 r2;
    exec st gr l
  | Emubranch (op, r, l1, l2) ->
    let v = get st r in
    let b = match op with
      | Mjz     -> v = zero
      | Mjnz    -> v <> zero
      | Mjlei n -> v <= Int64.of_int32 n
      | Mjgi n  -> v > Int64.of_int32 n in
    exec st gr (if b then l1 else l2)
  | Embbranch (op, r1, r2, l1, l2) ->
    let v1 = get st r1 in
    let v2 = get st r2 in
    let b = match op with
      | Mjl  -> v2 < v1
      | Mjle -> v2 <= v1 in
    exec st gr (if b then l1 else l2)
  | Ecall ("sbrk", l) ->
    let n = getr st Register.rdi in
    let v = Memory.malloc st.mem (Int64.to_int n) in
    setr st Register.rax v;
    exec st gr l
  | Ecall ("putchar", l) ->
    let n = getr st Register.rdi in
    Format.printf "%c" (Char.chr (Int64.to_int n));
    setr st Register.rax n;
    exec st gr l
  | Ecall (x, l) ->
    call st x;
    exec st gr l
  | Egoto l ->
    exec st gr l
  | Epush (r, l) ->
    let v = get st r in
    push st v;
    exec st gr l
  | Epop (r, l) ->
    let v = pop st in
    setr st r v;
    exec st gr l
  | Ereturn ->
    ignore (pop st) (* dépile l'adresse de retour fictive *)

and call st x =
  let f =
    try Hashtbl.find st.fundef x
    with Not_found -> error ("unknown function " ^ x) in
  push st 0L; (* adresse de retour fictive *)
  exec st f.fun_body f.fun_entry

let program p =
  let fundef = Hashtbl.create 16 in
  List.iter (fun d -> Hashtbl.add fundef d.fun_name d) p.funs;
  let st = { mem = Memory.create (); fundef; regs = Hashtbl.create 1;
             stack = Stack.create () } in
  setr st Register.rsp Stack.init_rsp;
  call st "main";
  getr st Register.rax
