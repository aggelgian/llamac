open Format
open Types
open Identifier
open Symbol

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

let func_stack = ref []          (* Function Stack to store functions' Quads  *)

(* ********************************************************************************************* *)
(* *********************************** Exceptions ********************************************** *)
(* ********************************************************************************************* *)

(* ********************************************************************************************* *)
(* ************************************ Functions ********************************************** *)
(* ********************************************************************************************* *)

  (* Add a function's Quads to the function stack *)
let push quadList = 
   func_stack := quadList :: !func_stack
   
  (* Pretty Prints an Operator *)
let pprint_operator ppf op = 
match op with
   | Op_unit       -> fprintf ppf "unit"
   | Op_endu       -> fprintf ppf "endu"
   | Op_plus       -> fprintf ppf "+"
   | Op_minus      -> fprintf ppf "-"
   | Op_mult       -> fprintf ppf "*"
   | Op_div        -> fprintf ppf "/"
   | Op_mod        -> fprintf ppf "mod"
   | Op_fplus      -> fprintf ppf "+."
   | Op_fminus     -> fprintf ppf "-."
   | Op_fmult      -> fprintf ppf "*."
   | Op_fdiv       -> fprintf ppf "/."
   | Op_pow        -> fprintf ppf "**"
   | Op_assign     -> fprintf ppf ":="
   | Op_array      -> fprintf ppf "array"
   | Op_dim        -> fprintf ppf "dim"
   | Op_structEq   -> fprintf ppf "="
   | Op_structIneq -> fprintf ppf "<>"
   | Op_physEq     -> fprintf ppf "=="
   | Op_physIneq   -> fprintf ppf "!="
   | Op_lt         -> fprintf ppf "<"
   | Op_gt         -> fprintf ppf ">"
   | Op_lteq       -> fprintf ppf "<="
   | Op_gteq       -> fprintf ppf ">="
   | Op_ifb        -> fprintf ppf "ifb"
   | Op_jump       -> fprintf ppf "jump"
   | Op_label      -> fprintf ppf "label"
   | Op_jumpl      -> fprintf ppf "jumpl"
   | Op_call       -> fprintf ppf "call"
   | Op_par        -> fprintf ppf "par"
   | Op_ret        -> fprintf ppf "ret"
   | Op_match      -> fprintf ppf "match"
   | Op_constr     -> fprintf ppf "constr"
   
  (* Pretty Prints a Pass Type *)
let pprint_passtype ppf p =
   match p with
   | V   -> fprintf ppf "V"
   | R   -> fprintf ppf "R"
   | RET -> fprintf ppf "RET"
   
  (* Pretty Prints an Operand *)
let rec pprint_operand ppf op = 
   match op with
   | Unit             -> fprintf ppf "()"
   | Bool b           -> fprintf ppf "%b" b
   | Chr c            -> fprintf ppf "%s" c
   | Int i            -> fprintf ppf "%d" i
   | Float x          -> fprintf ppf "%f" x
   | Str s            -> fprintf ppf "%s" s
   | Entry en         -> fprintf ppf "%s" (id_name en.entry_id)
   | UDT (en, sco)    -> fprintf ppf "%s" (id_name en.entry_id)
   | FuncResult et    -> fprintf ppf "$$"
   | Deref (en, et)   -> fprintf ppf "[%a]" pprint_operand en
   | Label i          -> fprintf ppf "%d" i
   | PassType p       -> fprintf ppf "%a" pprint_passtype p
   | Star             -> fprintf ppf "*"
   | InitPlace        -> fprintf ppf "<undef>"
   | Empty            -> fprintf ppf "-"

  (* Pretty Prints a Quad *)
let pprint_quad ppf q =
   fprintf ppf "%d :\t%a, %a, %a, %a" q.quad_tag pprint_operator q.quad_op 
      pprint_operand q.quad_argX pprint_operand q.quad_argY pprint_operand q.quad_argZ
      
  (* Pretty Prints a List of Quads *)
let pprint_quads ppf ql = 
   List.iter (fun q -> fprintf ppf "\n%a" pprint_quad q) ql
   
  (* Removes Empty Lists for a Quad Lists List *)
let filterEmpty s =
   let ql = List.filter (fun l -> l <> []) !s in
   s := ql
   
  (* Substitute One Quad's Number in a Quads' List *)
let substOne old nnew ql =
   let foo q =
      if q.quad_tag = old then
         q.quad_tag <- nnew;
      (match q.quad_argZ with
       | Label argZ ->
         if argZ = old then
            q.quad_argZ <- Label nnew
       | _ ->
         ()
      )
   in List.iter foo ql

  (* Normalize Quads' Numbers *)
let normalizeQuads s = 
   let quads = List.flatten (List.rev !s) in
   let walk i q =
      substOne q.quad_tag i quads;
      i-1 in
   let n = (List.fold_left walk (-1) quads) + 1 in
   ignore (List.fold_left walk (-n) (List.rev quads))
   
