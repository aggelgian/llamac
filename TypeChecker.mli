(* ********************************************************************************************* *)
(* ********************************* Type Definitions ****************************************** *)
(* ********************************************************************************************* *)

  (* Used for distinguishing between types of Illegal Array use in Type Definitions *)
type illArr = Ill_func | Ill_ref | Ill_array

(* ********************************************************************************************* *)
(* ********************************* Global Variables ****************************************** *)
(* ********************************************************************************************* *)

(* ********************************************************************************************* *)
(* *********************************** Exceptions ********************************************** *)
(* ********************************************************************************************* *)


(* ********************************************************************************************* *)
(* ************************************ Functions ********************************************** *)
(* ********************************************************************************************* *)

val getListWithParamsTypes : Symbol.entry list -> Types.typ list -> Types.typ list     (* Gets a list of Symbol Table entries and returns a list of their respective types *)
val constructFuncType      : Types.typ list -> Types.typ -> Types.typ                  (* Constructs the type of function from the list of its parameters' types and its result type *)
val semanticAnalysis       : Udt.udtTable ref -> Ast.ast_program_node option -> unit   (* Semantic Analysis of the AST Tree *)
val typ_conversion         : Ast.ast_type_node -> illArr option -> Udt.udtTable ref option -> Types.typ
