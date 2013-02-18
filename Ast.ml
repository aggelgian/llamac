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

let ast_tree = ref None  (* Mutable to store the AST                     *)
let file     = ref ""    (* Mutable to store the name of the source file *)

(* ********************************************************************************************* *)
(* ************************************ Functions ********************************************** *)
(* ********************************************************************************************* *)

  (* Add Position info and comment in an AST node *)
let addInfo (a, b) s = (s, a, b)

  (* Get Position info from Position comment *)
let rec getPosFromMsg l msg =
   match l with
   | [] -> 
      iInternal ("Couldn't Locate Position with info " ^ msg) None;
      (-1, -1) (* Just so it compiles *)
   | (s, a, b)::t -> 
      if (s = msg) then
         (a, b)
      else
         getPosFromMsg t msg
         
  (* Functions for Pretty Printing the AST *)
let rec print_pattern ppf ast = 
   match ast.tag_pt with
   | P_int (s, x) ->
      (match s with
       | S_plus   -> fprintf ppf "+ %d " x
       | S_minus  -> fprintf ppf "- %d " x
       | S_fplus  -> eprintf "%s@." "Error in AST"
       | S_fminus -> eprintf "%s@." "Error in AST"
       | Unsigned -> fprintf ppf "%d " x)
   | P_real (s, x) ->
      (match s with
       | S_plus   -> eprintf "%s@." "Error in AST"
       | S_minus  -> eprintf "%s@." "Error in AST"
       | S_fplus  -> fprintf ppf "+. %f " x
       | S_fminus -> fprintf ppf "-. %f " x
       | Unsigned -> fprintf ppf "%f " x)
   | P_char c ->
      fprintf ppf "%s " c
   | P_bool b ->
      fprintf ppf "%b " b
   | P_id x ->
      fprintf ppf "%s " x.pname
   | P_constr (x, patlist) ->
      fprintf ppf "%s " x;
      let foo l = print_pattern ppf l in
      List.iter foo patlist

let rec print_type ppf ast = 
   match ast.tag_tp with
   | Tp_unit ->
      fprintf ppf "unit "
   | Tp_int ->
      fprintf ppf "int "
   | Tp_char ->
      fprintf ppf "char "
   | Tp_bool ->
      fprintf ppf "bool "
   | Tp_float ->
      fprintf ppf "float "
   | Tp_func (et1, et2) ->
      fprintf ppf "(%a-> %a)" print_type et1 print_type et2
   | Tp_ref et ->
      fprintf ppf "%aref " print_type et
   | Tp_array (sz, et) ->
      if sz = 1 then
         fprintf ppf "array of %a" print_type et
      else
         begin
         fprintf ppf "array [*";
         for i = 2 to sz do
            fprintf ppf ",*"
         done;
         fprintf ppf "] of %a" print_type et
      end;
   | Tp_id x ->
      fprintf ppf "%s " x
   | Tp_duck i ->
      fprintf ppf "@@%d " i

let print_par ppf ast =
   match ast.tag_pr with
   | (x, et, en) ->
      (match !et with
       | None   -> fprintf ppf "%s " x
       | Some t -> fprintf ppf "( %s : %a) " x print_type t)
                   
let print_constr ppf ast =
   match ast.tag_co with
   | (x, []) ->
      fprintf ppf "%s " x
   | (x, l)  ->
      fprintf ppf "%s of " x;
      let foo y = print_type ppf y in
      List.iter foo l
      
let print_tdef ppf ast =
   match ast.tag_td with
   | (x, []) ->
      eprintf "%s@." "Error in AST"
   | (x, c::rest) ->
      fprintf ppf "%s =" x;
      force_newline ();
      fprintf ppf "  %a" print_constr c;
      let foo y = 
         force_newline ();
         fprintf ppf "| %a" print_constr y
      in List.iter foo rest
      
let print_typedef ppf ast =
   match ast.tag_pd with
   | [] ->
      eprintf "%s@." "Error in AST"
   | bl::rest ->
      open_hovbox 2;
      fprintf ppf "type %a" print_tdef bl;
      close_box ();
      let foo =
         fun y -> 
            force_newline ();
            open_hovbox 2;
            fprintf ppf "and %a" print_tdef y;
            close_box()
      in List.iter foo rest
      
let rec print_expr ppf ast =
   match ast.tag_ex with
   | E_int x ->
      fprintf ppf "%d" x
   | E_real x ->
      fprintf ppf "%f" x
   | E_char c ->
      fprintf ppf "%s" c
   | E_string s ->
      fprintf ppf "%s" s
   | E_bool b ->
      fprintf ppf "%b" b
   | E_unit ->
      fprintf ppf "()"
   | E_var x ->
      fprintf ppf "%s" x
   | E_func (x, l) ->
      fprintf ppf "%s" x;
      let foo =
         fun e ->
            fprintf ppf " %a" 
            print_expr e
      in List.iter foo l
   | E_constr (x, l) ->
      fprintf ppf "%s " x;
      let foo = 
         fun e ->
            fprintf ppf "%a " print_expr e
      in List.iter foo l
   | E_bang e ->
      fprintf ppf "!%a" print_expr e
   | E_not e ->
      fprintf ppf "not %a" print_expr e
   | E_signed (s, e) ->
      (match s with
       | S_plus   -> fprintf ppf "+"
       | S_minus  -> fprintf ppf "-"
       | S_fplus  -> fprintf ppf "+."
       | S_fminus -> fprintf ppf "-."
       | Unsigned -> eprintf "%s@." "Error in AST");
      print_expr ppf e
   | E_binop (e1, bn, e2) ->
      print_expr ppf e1;
      (match bn with
       | B_plus       -> fprintf ppf " + "
       | B_minus      -> fprintf ppf " - "
       | B_mult       -> fprintf ppf " * "
       | B_div        -> fprintf ppf  " / "
       | B_fplus      -> fprintf ppf " +. "
       | B_fminus     -> fprintf ppf " -. "
       | B_fmult      -> fprintf ppf " *. "
       | B_fdiv       -> fprintf ppf " /. "
       | B_mod        -> fprintf ppf " mod "
       | B_pow        -> fprintf ppf " ** "
       | B_assign     -> fprintf ppf " = "
       | B_ltgt       -> fprintf ppf " <> "
       | B_lt         -> fprintf ppf " < "
       | B_gt         -> fprintf ppf " > "
       | B_lteq       -> fprintf ppf " <= "
       | B_gteq       -> fprintf ppf " >= "
       | B_eq         -> fprintf ppf " == "
       | B_neq        -> fprintf ppf " != "
       | B_conj       -> fprintf ppf " && "
       | B_disj       -> fprintf ppf " || "
       | B_semic      -> fprintf ppf ";";
                         force_newline ()
       | B_refassign  -> fprintf ppf " := ");
      print_expr ppf e2
   | E_array (x, []) ->
      eprintf "%s@." "Error in AST"
   | E_array (x, h::t) ->
      fprintf ppf "%s[%a" x print_expr h;
      let foo = 
         fun e ->
            fprintf ppf ", %a" print_expr e
      in List.iter foo t;
      fprintf ppf "]"
   | E_dim (il, x) -> 
      if il = [] then
         fprintf ppf "dim %s" x
      else
         fprintf ppf "dim %d %s" (List.hd il) x
   | E_new et ->
      fprintf ppf "new %a" print_type et
   | E_del e ->
      fprintf ppf "delete %a" print_expr e
   | E_in (letdf, e) ->
      print_letdef ppf letdf;
      force_newline ();
      fprintf ppf "in %a" print_expr e
   | E_begin e ->
      force_newline ();
      open_hovbox 2;
      fprintf ppf "begin";
      force_newline ();
      print_expr ppf e;
      close_box ();
      force_newline ();
      fprintf ppf "end"
   | E_if (e1, e2) ->
      fprintf ppf "if %a" print_expr e1;
      force_newline ();
      fprintf ppf "then %a" print_expr e2
   | E_ifelse (e, e1, e2) ->
      fprintf ppf "if %a" print_expr e;
      force_newline ();
      fprintf ppf "then %a" print_expr e1;
      force_newline ();
      fprintf ppf "else %a" print_expr e2
   | E_while (e1, e2) -> 
      open_hovbox 2;
      fprintf ppf "while %a do" print_expr e1;
      force_newline ();
      print_expr ppf e2;
      close_box ();
      force_newline ();
      fprintf ppf "done";
   | E_for (x, e1, lptype, e2, e3) ->
      open_hovbox 2;
      fprintf ppf "for %s = %a " x print_expr e1;
      (match lptype with
       | L_to     -> fprintf ppf "to "
       | L_downto -> fprintf ppf "downto "
      );
      fprintf ppf "%a do" print_expr e2;
      force_newline ();
      fprintf ppf "%a" print_expr e3;
      close_box ();
      force_newline ();
      fprintf ppf "done"
   | E_match (e, []) -> 
      eprintf "%s@." "Error in AST"
   | E_match (e, h::t) -> 
      fprintf ppf "match %a with" print_expr e;
      force_newline ();
      fprintf ppf "  %a" print_clause h;
      let foo =
         fun c -> 
            force_newline ();
            fprintf ppf "| %a" print_clause c
      in List.iter foo t;
      force_newline ();
      fprintf ppf "end"

and print_letdef ppf ast =
   match ast.tag_lt with
   | (_, []) ->
      eprintf "%s@." "Error in AST"
   | (0, h::t) ->
      open_hovbox 2;
      fprintf ppf "let %a" print_def h;
      close_box ();
      let foo = 
         fun d -> 
            force_newline ();
             open_hovbox 2;
             fprintf ppf "and %a" print_def d;
             close_box ()
      in List.iter foo t
   | (1, h::t) ->
      open_hovbox 2;
      fprintf ppf "let rec %a" print_def h;
      close_box ();
      let foo = 
         fun d -> 
            force_newline ();
             open_hovbox 2;
             fprintf ppf "and %a" print_def d;
             close_box ()
      in List.iter foo t
   | _ ->
      eprintf "%s@." "Error in AST"

and print_clause ppf ast =
   match ast.tag_cl with
   | (pat, e) ->
      fprintf ppf "%a-> " print_pattern pat;
      open_hovbox 0;
      print_expr ppf e;
      close_box ()
     
and print_def ppf ast =
   match ast.tag_df with
   | Def_func (x, lp, tp, e) ->
      (match !tp with
       | None    -> 
          fprintf ppf "%s " x;
          let foo y = print_par ppf y in
          List.iter foo lp;
          fprintf ppf "=";
          force_newline();
          print_expr ppf e
       | Some et -> 
          fprintf ppf "%s " x;
          let foo y = print_par ppf y in
          List.iter foo lp;
          fprintf ppf ": %a=" print_type et;
          force_newline();
          print_expr ppf e)
   | Def_mut (x, [], tp) ->
      (match !tp with
       | None    -> 
          fprintf ppf "mutable %s" x
       | Some et -> 
          fprintf ppf "mutable %s : %a" x print_type et)
   | Def_mut (x, h::t, tp) ->
      (match !tp with
       | None    -> 
          fprintf ppf "mutable %s [%a" x print_expr h;
          let foo =
             fun e -> 
                fprintf ppf ", %a" print_expr e
          in List.iter foo t;
          fprintf ppf "]"
       | Some et -> 
          fprintf ppf "mutable %s [%a" x print_expr h;
          let foo =
             fun e -> 
                fprintf ppf ", %a" print_expr e
          in List.iter foo t;
          fprintf ppf "] : %a" print_type et)
          
let print_block ppf ast =
   match ast.tag_bl with
   | Letdef lt ->
      open_hovbox 0;
      print_letdef ppf lt;
      close_box ();
      print_newline ()
   | Typedef td ->
      open_hovbox 0;
      print_typedef ppf td;
      close_box ();
      print_newline ()
      
let rec print_program ppf ast =
   match ast with
   | []    -> 
      ()
   | h::[] -> 
      print_block ppf h
   | h::t  -> 
      print_block ppf h;
      print_newline ();
      print_program ppf t

  (* Pretty Prints the AST *)
let pretty_print ppf ast =
   match ast with
   | None ->
      eprintf "%s@." "AST is empty"
   | Some tree ->
      print_program ppf tree.tag_pg
