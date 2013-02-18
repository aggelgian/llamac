open Scanner
open Ast
open TypeChecker
open Icode
open Udt
open Error
open Format
open Debug

let usage = "Usage: " ^ Sys.argv.(0) ^ " [options] file\n\nOptions:"

let rec speclist =
[ ("-p",
 Arg.Unit (fun () -> __ASTpprint := true),
 " Pretty Print the AST");
("-c",
 Arg.Unit (fun () -> __CST := true),
 " Print the Constraint Set of Type Inference");
("-s",
 Arg.Unit (fun () -> __symbolTable := true),
 " Print the Symbol Table Contents");
("-i",
 Arg.Unit (fun () -> __Icode := true),
 " Print the Intermediate Code Quadruples");
("-V",
 Arg.Unit (fun () -> printf "Llamac - A Llama Compiler v0.3beta\n"; exit 0 ),
 " Print Compiler Version");
("-help",
 Arg.Unit (fun () -> Printf.printf "%s" (Arg.usage_string (Arg.align speclist) usage); exit 0),
 " Display this list of options");
("--help",
 Arg.Unit (fun () -> Printf.printf "%s" (Arg.usage_string (Arg.align speclist) usage); exit 0),
 " Display this list of options"); ]

let main =
  Arg.parse speclist (fun s -> if !file = "" then file := s) usage;
  let chan =
    (if !file <> "" then 
       open_in !file
    else 
       stdin) in
  try
    let lexbuf = Lexing.from_channel chan in       (* Create a buffer from the source file *)
    (try
      Parser.program Scanner.llama_lexer lexbuf;   (* Parse the program                    *)
      debug_ASTpprint ast_tree;                    (* Print the AST                        *)
      semanticAnalysis user_types !ast_tree;       (* Semantic Analysis and Type Inference *)
      iCodeTranslation user_types !ast_tree;       (* Intermediate Code Generation         *)
      exit 0
    with 
    | Parsing.Parse_error ->
       printf "Syntax Error: Ln %d, Col %d.\n" !num_lines !num_chars;
       exit 1
    | Terminate ->
       printf "Exiting ...\n";
       exit 1)
  with End_of_file ->
    close_in chan

