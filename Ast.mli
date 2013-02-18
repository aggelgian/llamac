open Format
open Error
open Symbol

(* ********************************************************************************************* *)
(* ********************************* Type Definitions ****************************************** *)
(* ********************************************************************************************* *)

  (* Types of certain Llama tokens *)
type intconst    = { ival  : int;    ipos : (int * int) }
type charconst   = { cname : string; cpos : (int * int) }
type stringconst = { sname : string; spos : (int * int) }
type realconst   = { fval  : float;  fpos : (int * int) }

  (* Auxiliary types for the AST *)
type position_info = 
   (string *          (* Comment *)
    int *             (* Line *)
    int) list         (* Column *)
type sign = S_plus | S_minus | S_fplus | S_fminus | Unsigned
type loop_type = L_to | L_downto
type binop = B_plus | B_minus | B_mult | B_div | B_fplus | B_fminus
| B_fmult | B_fdiv | B_mod | B_pow | B_assign | B_ltgt
| B_lt | B_gt | B_lteq | B_gteq | B_eq | B_neq | B_conj
| B_disj | B_semic | B_refassign

(* ********************* *)
(* *** AST Datatypes *** *)
(* ********************* *)

  (* Non Terminal Symbol <program> *)
type ast_program_node = {
   tag_pg : ast_program;
   meta_pg : position_info
}
and ast_program = ast_block_node list

  (* <letdef> | <typedef> *)
and ast_block_node = {
   tag_bl : ast_block;
   meta_bl : position_info
}
and ast_block = 
| Letdef of ast_letdef_node
| Typedef of ast_typedef_node

  (* Non terminal symbol <letdef> *)
and ast_letdef_node = {
   tag_lt : ast_letdef;
   meta_lt : position_info
}
and ast_letdef = 
   int *   (* Flag : 0 if it's a Let, 1 if it's a Letrec *)
   (ast_def_node list)

 (* Non terminal symbol <def> *)
and ast_def_node = {
   tag_df : ast_def;
   meta_df : position_info;
   mutable entry_df : entry option;
   mutable scope_df : scope option
}
and ast_def = 
| Def_func of 
   string *                            (* Name of the function / constant                *)
   ast_par_node list *                 (* List of parameters                             *)
   ast_type_node option ref *          (* Reference to the type, None if absent          *)
   ast_expr_node                       (* Inner Expression                               *)
| Def_mut of 
   string *                            (* Name of the mutable                            *)
   ast_expr_node list *                (* List of Dimension Expressions in case of array *)
   ast_type_node option ref            (* Reference to the type, None if absent          *)

  (* Non terminal symbol <typedef> *)
and ast_typedef_node = {
   tag_pd : ast_typedef;
   meta_pd : position_info
}
and ast_typedef = ast_tdef_node list   (* A Typedef is a list of type definitions *)

  (* Non terminal symbol <tdef> *)
and ast_tdef_node = {
   tag_td : ast_tdef; 
   meta_td : position_info
}
and ast_tdef = 
   string *                            (* Name of the User Defined Type      *)
   ast_constr_node list                (* Structure of the User Defined Type *)
   
  (* Non terminal symbol <constr> *)
and ast_constr_node = {
   tag_co : ast_constr;
   meta_co : position_info
}
and ast_constr =
   string *                            (* Name of the constructor       *)
   ast_type_node list                  (* Parameters of the constructor *)
   
  (* Non terminal symbol <par> *)
and ast_par_node = {
   tag_pr : ast_par;
   meta_pr : position_info
}
and ast_par = 
   string *                            (* Name of the parameter                 *)
   ast_type_node option ref *          (* Reference to the type, None if absent *)
   entry option ref                    (* Parameter entry in the Symbol Table   *)
   
  (* Non terminal symbol <type> *)
and ast_type_node = {
   tag_tp : ast_type;
   meta_tp : position_info
}
and ast_type = 
| Tp_unit
| Tp_int
| Tp_char
| Tp_bool
| Tp_float
| Tp_func of ast_type_node * ast_type_node
| Tp_ref of ast_type_node
| Tp_array of 
   int *                               (* Number of array dimensions    *)
   ast_type_node                       (* Array of what type            *)
| Tp_id of 
   string                              (* Name of the user defined type *)
| Tp_duck of int                       (* QUACK!!                       *)
   
  (* Non terminal symbol <expr> *)
and ast_expr_node = {
   tag_ex : ast_expr;
   meta_ex : position_info;
   mutable entry_ex : entry option;
   mutable matchType_ex : Types.typ
}
and ast_expr = 
| E_int of int
| E_real of float
| E_char of string
| E_string of string
| E_bool of bool
| E_unit
| E_var of 
   string                              (* Name of the variable                    *)
| E_func of 
   string *                            (* Name of the function                    *)
   ast_expr_node list                  (* List of function's actual parameters    *)
| E_constr of 
   string *                            (* Name of the constructor                 *)
   ast_expr_node list                  (* List of constructor's actual parameters *)
| E_bang of ast_expr_node
| E_not of ast_expr_node
| E_signed of sign * ast_expr_node
| E_binop of ast_expr_node * binop * ast_expr_node
| E_array of 
   string *                            (* Name of the array *)
   ast_expr_node list
| E_dim of 
   int list * 
   string                              (* Name of the array *)
| E_new of ast_type_node
| E_del of ast_expr_node
| E_in of ast_letdef_node * ast_expr_node
| E_begin of ast_expr_node
| E_if of ast_expr_node * ast_expr_node
| E_ifelse of ast_expr_node * ast_expr_node * ast_expr_node
| E_while of ast_expr_node * ast_expr_node
| E_for of string * ast_expr_node * loop_type * ast_expr_node * ast_expr_node
| E_match of ast_expr_node * ast_clause_node list

  (* Non terminal symbol <clause> *)
and ast_clause_node = {
   tag_cl : ast_clause;
   meta_cl : position_info
}
and ast_clause = ast_pattern_node * ast_expr_node

  (* Non terminal symbol <pattern> *)
and ast_pattern_node = {
   tag_pt : ast_pattern;
   meta_pt : position_info
}
and ast_pattern = 
| P_int of sign * int
| P_real of sign * float
| P_char of string
| P_bool of bool
| P_id of 
   pattype
| P_constr of 
   string *                            (* Name of the constructor                              *)
   ast_pattern_node list               (* List of patterns that match constructor's parameters *)
   
and pattype = { 
   pname  : string;                    (* Name of the Variable               *)
   ptype  : ast_type_node option ref;  (* Type of the Variable               *)
   mutable pentry : entry option       (* Variable entry in the Symbol Table *)
}

(* ********************************************************************************************* *)
(* ********************************* Global Variables ****************************************** *)
(* ********************************************************************************************* *)

val ast_tree : ast_program_node option ref  (* Mutable to store the AST                     *)
val file     : string ref                   (* Mutable to store the name of the source file *)

(* ********************************************************************************************* *)
(* ************************************ Functions ********************************************** *)
(* ********************************************************************************************* *)

  (* Add Position info and comment in an AST node *)
val addInfo       : int * int -> string -> string * int * int
  (* Get Position info from Position comment      *)
val getPosFromMsg : (string * int * int) list -> string -> int * int
  (* Pretty Prints the AST                        *)
val pretty_print  : Format.formatter -> ast_program_node option -> unit

