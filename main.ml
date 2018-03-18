
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
let assembly = ref false

(* Est-ce que l'utilisateur a donné une directive pour l'outfile ? *)
let provided_out = ref false
let outfile = ref "a.out"

let ifile = ref ""

let set_file f s = f := s

let set_out_file ofile = outfile := ofile

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
   "--coloration", Arg.Set coloration,
     "  displays the coloration (and does not compile)";
   "--debug", Arg.Set debug,
     "  debug mode";
    "-S", Arg.Set assembly,
     "  produce assembly code, do not assemble using gcc";
   "-o", Arg.Tuple ([Arg.Set provided_out; Arg.String (set_out_file)]),
     "<file> place the output into <file>"
   ]

let usage = "usage: mini-c [options] file.c"

let localisation pos =
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" !ifile l (c-1) c



let compile ultim_prog = let asmname = ((String.sub !ifile 0 (String.length !ifile - 2)) ^ ".s") in (* si ifile = test.c, asmname = test.s *)
    (* Si on doit produire un exécutable *)
    if not !assembly then begin
        let assembly_file = !outfile ^ ".s" in
        X86_64.print_in_file assembly_file {X86_64.text = X86_64.(++) (X86_64.globl "main") ultim_prog.X86_64.text; X86_64.data = ultim_prog.data};
        let retcode = Sys.command ("gcc -no-pie " ^ assembly_file ^ " -o " ^ !outfile) in
        if retcode <> 0 then print_string "Could'nt compile given file using GCC !\n\n";
        (* Cleanup *)
        Sys.remove assembly_file;
    end
    
    (* Si on doit se contenter d'ASM *)
    else begin
        let assembly_file = if !provided_out then !outfile else asmname in
        X86_64.print_in_file assembly_file {X86_64.text = X86_64.(++) (X86_64.globl "main") ultim_prog.X86_64.text; X86_64.data = ultim_prog.data};
    end


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
  try (
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

    if !doliveness then
    begin 
      List.iter (fun f -> let lv = Liveness.liveness f.Ertltree.fun_body in (Liveness.print_live f.Ertltree.fun_name lv f.Ertltree.fun_entry); print_string "\n") (p.Ertltree.funs);
      exit 0
    end;

    if !graphinterf then
    begin
      List.iter (fun f -> 
        let lv = Liveness.liveness f.Ertltree.fun_body in 
        let gI = Interfgraph.make lv in
        Interfgraph.print gI; print_string "\n") (p.Ertltree.funs);
      exit 0
    end;

    if !coloration then
    begin
      List.iter (fun f -> 
        let lv = Liveness.liveness f.Ertltree.fun_body in 
        let gI = Interfgraph.make lv in
        let (colo, n) = Coloration.color gI in
        Coloration.print colo; print_string "\n") (p.funs);
      exit 0
    end;
  
    let p = Ltl.program p in

    if debug then Ltltree.print_file std_formatter p;
    if !interp_ltl then begin ignore (Ltlinterp.program p); exit 0 end;
    
    (* Transforme un élément e de la liste Assembler.code pour le rendre concaténable avec (++) *)
    let trans e = match e with
                    | Assembler.Code t -> t
                    | Assembler.Label t -> if Hashtbl.mem Assembler.labels t then X86_64.label (t :> string) else X86_64.nop in

    (* Plie les fonctions pour en faire un programme *)
    let rec fold_functions funs = match funs with
        | []   -> {X86_64.text = (X86_64.nop : X86_64.text); data = (X86_64.nop : X86_64.data)}
        | f::q -> (Assembler.code := [];
                  Assembler.lin f.Ltltree.fun_body f.fun_entry;
                  let loctext = X86_64.(++) (X86_64.inline ("\n" ^ f.fun_name ^ ":\n")) (List.fold_right (fun e acc -> X86_64.(++) acc (trans e)) !Assembler.code (X86_64.nop : X86_64.text)) in
                  let locdata = (X86_64.nop : X86_64.data) in
                  let p = fold_functions q in
                  {text = X86_64.(++) loctext p.text; data = locdata}) in

    let ultim_prog = fold_functions p.Ltltree.funs in 
        (* Compile *)
        compile ultim_prog;
        (* Print to stdout *)
        if debug then 
        begin
            print_string "=== ASM ==================================================\n";
            X86_64.print_program std_formatter {text = X86_64.(++) (X86_64.globl "main") ultim_prog.text; data = ultim_prog.data};
        end
  )
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





