
open Format
open Ops
open Memory
open Ertltree

type frame = Memory.value array
  (* uniquement les arguments 7,8,... passés sur la pile, dans cet ordre *)

type state = {
  mem: Memory.t;
  fundef: (string, deffun) Hashtbl.t;
  regs: (Register.t, Memory.value) Hashtbl.t; (* pseudo *)
  hwregs: (Register.t, Memory.value) Hashtbl.t; (* physiques *)
  mutable stack: frame list;
  mutable next: Memory.value list; (* prochain tableau d'activation *)
}

exception Error of string
let error s = raise (Error s)

let zero = 0L
let one = 1L

let get st r =
  if Register.is_hw r then
    try Hashtbl.find st.hwregs r with Not_found -> zero
  else
    try Hashtbl.find st.regs r
    with Not_found -> error ("unknown register " ^ (r :> string))

let set st r v =
  Hashtbl.replace (if Register.is_hw r then st.hwregs else st.regs) r v

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
    | Mdiv when r2 <> Register.rax -> error "div: r2 must be %rax"
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
    let p = get st r1 in
    let v = Memory.get st.mem p ~ofs in
    set st r2 v;
    exec st gr l
  | Estore (r1, r2, ofs, l) ->
    let p = get st r2 in
    let v = get st r1 in
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
  | Ecall ("sbrk", _, l) ->
    let n = get st Register.rdi in
    let v = Memory.malloc st.mem (Int64.to_int n) in
    set st Register.rax v;
    exec st gr l
  | Ecall ("putchar", _, l) ->
    let n = get st Register.rdi in
    Format.printf "%c" (Char.chr (Int64.to_int n));
    set st Register.rax n;
    exec st gr l
  | Ecall (x, _, l) ->
    call st x;
    exec st gr l
  | Egoto l ->
    exec st gr l
  | Ealloc_frame l ->
    st.stack <- Array.of_list st.next :: st.stack;
    st.next <- [];
    exec st gr l
  | Edelete_frame l ->
    if st.stack = [] then error "delete_frame: empty stack";
    st.stack <- List.tl st.stack;
    st.next <- [];
    exec st gr l
  | Eget_param (ofs, r, l) ->
    let frame = match st.stack with
      | [] -> error "get_param: missing frame" | f :: _ -> f in
    let n = Array.length frame in
    if ofs mod 8 <> 0 then error "get_param: mis-aligned frame access";
    if ofs < 16 || ofs > 16 + 8 * (n-1) then
      error "get_param: access out of frame";
    set st r frame.((ofs - 16) / 8);
    exec st gr l
  | Epush_param (r, l) ->
    let v = get st r in
    st.next <- v :: st.next;
    exec st gr l
  | Ereturn ->
    ()

and call st x =
  let f =
    try Hashtbl.find st.fundef x
    with Not_found -> error ("unknown function " ^ x) in
  let stf = { st with regs = Hashtbl.create 16 } in
  Register.S.iter (fun r -> set stf r zero) f.fun_locals;
  exec stf f.fun_body f.fun_entry

let program p =
  let fundef = Hashtbl.create 16 in
  List.iter (fun d -> Hashtbl.add fundef d.fun_name d) p.funs;
  let st = { mem = Memory.create (); fundef; regs = Hashtbl.create 1;
             hwregs = Hashtbl.create 16; stack = []; next = [] } in
  call st "main";
  get st Register.rax
