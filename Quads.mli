(* ********************************************************************************************* *)
(* ********************************* Type Definitions ****************************************** *)
(* ********************************************************************************************* *)

type operator = 
   | Op_unit | Op_endu
   | Op_plus | Op_minus | Op_mult | Op_div | Op_mod
   | Op_fplus | Op_fminus | Op_fmult | Op_fdiv | Op_pow
   | Op_assign | Op_array | Op_dim
   | Op_structEq | Op_structIneq | Op_physEq | Op_physIneq
   | Op_lt | Op_gt | Op_lteq | Op_gteq
   | Op_ifb | Op_jump | Op_label | Op_jumpl
   | Op_call | Op_par | Op_ret
   | Op_match | Op_constr

and pass_type = 
   | V | R | RET

and operand = 
   | Unit
   | Bool of bool
   | Chr of string
   | Int of int
   | Float of float
   | Str of string
   | Entry of Symbol.entry
   | UDT of Symbol.entry * Symbol.scope
   | FuncResult of Types.typ
   | Deref of 
      operand *       (* Symbol Table entry for the Pointer *)
      Types.typ       (* Type of Pointer data *)
   | Label of int
   | PassType of pass_type
   | Star (* for backpatching *)
   | InitPlace (* For Place Initialization *)
   | Empty

and quad =  {
   mutable quad_tag  : int;
   mutable quad_op   : operator;
   mutable quad_argX : operand;
   mutable quad_argY : operand;
   mutable quad_argZ : operand;
}

and semantic_properties = {
   etype          : Types.typ;
   mutable place  : operand;
   mutable next   : int list;
   mutable trues  : int list;
   mutable falses : int list;
   mutable quads  : quad list
}

type quad_stack = quad list list ref

(* ********************************************************************************************* *)
(* ********************************* Global Variables ****************************************** *)
(* ********************************************************************************************* *)

val func_stack : quad_stack   (* Function Stack to store functions' Quads  *)

(* ********************************************************************************************* *)
(* *********************************** Exceptions ********************************************** *)
(* ********************************************************************************************* *)

(* ********************************************************************************************* *)
(* ************************************ Functions ********************************************** *)
(* ********************************************************************************************* *)

val push           : quad list -> unit                        (* Add a function's Quads to the function stack  *)
val pprint_quads   : Format.formatter -> quad list -> unit    (* Pretty Prints a List of Quads                 *)
val normalizeQuads : quad_stack -> unit                       (* Normalize Quads' Numbers                      *)
val filterEmpty    : quad_stack -> unit                       (* Removes Empty Lists for a Quad Lists List     *)
