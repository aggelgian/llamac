open Format
open Udt
open Symbol
open Ast
open TypeInference
open Quads

(* ********************************************************************************************* *)
(* ********************************* Type Definitions ****************************************** *)
(* ********************************************************************************************* *)

(* ********************************************************************************************* *)
(* ********************************* Global Variables ****************************************** *)
(* ********************************************************************************************* *)

let __ASTpprint     = ref false    (* Flag for Pretty Printing the AST          *)
let __symbolTable   = ref false    (* Print the Symbol Table                    *)
let __udtTable      = ref false    (* Print UDT table after parsing the program *)
let __typedAst      = ref false    (* Print the Typed AST                       *)
let __CST           = ref false    (* Print the Constraint Set                  *)
let __InferredTypes = ref false    (* Prints the Result of the Type Inference   *)
let __Icode         = ref false    (* Prints the Icode Quadruples               *)

(* ********************************************************************************************* *)
(* *********************************** Exceptions ********************************************** *)
(* ********************************************************************************************* *)

(* ********************************************************************************************* *)
(* ************************************ Functions ********************************************** *)
(* ********************************************************************************************* *)

  (* Pretty Prints the AST *)
let debug_ASTpprint ast_tree = 
   match !__ASTpprint with
   | true ->
      force_newline ();
      printf "*** Pretty Printing AST ***";
      force_newline ();
      printf "***************************";
      force_newline ();
      printf "%a" pretty_print !ast_tree;
   | false ->
      ()
      
  (* Prints the Symbol Table *)
let debug_symbolTable () = 
   match !__symbolTable with
   | true ->
      printSymbolTable()
   | false ->
      ()
      
  (* Prints the UDT table *)
let debug_udtTable env = 
   match !__udtTable with
   | true ->
      force_newline ();
      printf "*** UDT Table Contents ***";
      force_newline ();
      printf "**************************";
      force_newline ();
      printf "%a" print_UDTtable env
   | false ->
      ()
      
  (* Prints the Typed AST *)
let debug_typedAST ast =
   match !__typedAst with
   | true ->
      force_newline ();
      printf "*** Pretty Printing AST with Type Information ***";
      force_newline ();
      printf "*************************************************";
      force_newline ();
      printf "%a" pretty_print ast
   | false ->
      ()
      
  (* Prints the Constraint Set *)
let debug_CST () =
   match !__CST with
   | true ->
      force_newline ();
      printf "*** Constraint Set ***";
      force_newline ();
      printf "**********************";
      force_newline ();
      printf "%a" printCST !cst
   | false ->
      ()
      
  (* Prints the Type Inference Results *)
let debug_TypeInf res =
   match !__InferredTypes with
   | true ->
      force_newline ();
      printf "*** Result Types of Type Inference ***";
      force_newline ();
      printf "**************************************";
      force_newline ();
      printTypInfRes res 1
   | false ->
      ()
      
  (* Prints the Icode Quadruples *)
let debug_Icode () =
   match !__Icode with
   | true ->
      force_newline ();
      printf "*** Icode Quadruples ***";
      force_newline ();
      printf "************************";
      force_newline ();
      List.iter (fun l -> printf "%a" pprint_quads l;
                          force_newline()) (List.rev !func_stack)
   | false ->
      ()
