
(* Fichier principal du compilateur mini-c *)

open Format
open Lexing
open Liveness

let () = Printexc.record_backtrace true

let parse_only = ref false
let type_only = ref false
let interp_rtl = ref false
let interp_ertl = ref false
let interp_ltl = ref false
let doliveness = ref false
let graphinterf = ref false
let coloration = ref false
let debug = ref false

let ifile = ref ""

let set_file f s = f := s

let options =
  ["--parse-only", Arg.Set parse_only,
     "  stops after parsing";
   "--type-only", Arg.Set type_only,
     "  stops after typing";
   "--interp-rtl", Arg.Set interp_rtl,
     "  interprets RTL (and does not compile)";
   "--interp-ertl", Arg.Set interp_ertl,
     "  interprets ERTL (and does not compile)";
  "--interp-ltl", Arg.Set interp_ltl,
     "  interprets LTL (and does not compile)";
   "--liveness", Arg.Set doliveness,
     "  displays the result of liveness analysis (and does not compile)";
   "--interfgraph", Arg.Set graphinterf,
     "  displays the interference graph (and does not compile)";
   (*"--coloration", Arg.Set coloration,
     "  displays the coloration (and does not compile)";*)
   "--debug", Arg.Set debug,
     "  debug mode";
   ]

let usage = "usage: mini-c [options] file.c"

let localisation pos =
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" !ifile l (c-1) c

let register_print_set = Register.print_set Format.std_formatter

let label_print_set = Label.print_set Format.std_formatter

let label_print_list = Pp.print_list Pp.comma Label.print Format.std_formatter



let print_live_info lbl liveinfo =
  Label.print Format.std_formatter lbl; print_string ": "; Ertltree.print_instr Format.std_formatter liveinfo.instr;
                print_string "  d={"; register_print_set liveinfo.defs; print_string "} u={";register_print_set liveinfo.uses;
                print_string "} i={"; register_print_set liveinfo.ins; print_string "} o={"; register_print_set liveinfo.outs;
                print_string "}\n"

let print_live funcname (lmap : live_info Label.map) (entry : Ertltree.label) = 
  print_string ("=== LIVENESS(" ^ funcname ^ ") =================================================\n");
  let visited = Hashtbl.create 1 in

  let rec visitIt curlab =
    if not (Hashtbl.mem visited curlab) then
    begin
      Hashtbl.add visited curlab ();
      let liveinfo = Label.M.find curlab lmap in
      print_live_info curlab liveinfo;
      List.iter visitIt liveinfo.succ;
    end in

  visitIt entry


let () =
  Arg.parse options (set_file ifile) usage;
  if !ifile="" then begin eprintf "missing file\n@?"; exit 1 end;
  if not (Filename.check_suffix !ifile ".c") then begin
    eprintf "file must have extension .c\n@?";
    Arg.usage options usage;
    exit 1
  end;
  let debug = !debug in
  let f = open_in !ifile in
  let buf = Lexing.from_channel f in
  try
    let p = Parser.file Lexer.token buf in
    close_in f;
    
    if !parse_only then exit 0;
    let p = Typing.program p in
    if !type_only then exit 0;

    let p = Rtl.program p in
    if debug then Rtltree.print_file std_formatter p;
    if !interp_rtl then begin ignore (Rtlinterp.program p); exit 0 end;
    let p = Ertl.program p in
    if debug then Ertltree.print_file std_formatter p;
    
    if !interp_ertl then begin ignore (Ertlinterp.program p); exit 0 end;
    (* ... *)

    if !doliveness then
    begin 
      List.iter (fun f -> let lv = Liveness.liveness f.Ertltree.fun_body in (print_live f.Ertltree.fun_name lv f.Ertltree.fun_entry); print_string "\n") (p.funs);
      exit 0
    end;

    if !graphinterf then
    begin
      List.iter (fun f -> 
        let lv = Liveness.liveness f.Ertltree.fun_body in 
        let gI = Interfgraph.make lv in
        Interfgraph.print gI; print_string "\n") (p.funs);
      exit 0
    end;

    (*if !coloration then
    begin
      List.iter (fun f -> 
        let lv = Liveness.liveness f.Ertltree.fun_body in 
        let gI = Interfgraph.make lv in
        let colo = Coloration.color gI in
        Colocation.print_color colo; print_string "\n") (p.funs);
      exit 0
    end;
  
    let p = Ltl.program p in
    if debug then Ltltree.print_file std_formatter p;
    if !interp_ltl then begin ignore (Ltlinterp.program p); exit 0 end;*)

  with
    | Lexer.Lexical_error c ->
	localisation (Lexing.lexeme_start_p buf);
	eprintf "lexical error: %s@." c;
	exit 1
    | Parser.Error ->
	localisation (Lexing.lexeme_start_p buf);
	eprintf "syntax error@.";
	exit 1
    | Typing.Error s->
	eprintf "typing error: %s@." s;
	exit 1
    | e ->
        let bt = Printexc.get_backtrace () in
        eprintf "anomaly: %s\n@." (Printexc.to_string e);
        eprintf "%s@." bt;
	exit 2





