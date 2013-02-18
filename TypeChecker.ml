open Types
open Ast
open Udt
open Error
open Debug
open Identifier
open Symbol
open TypeInference

(* ********************************************************************************************* *)
(* ********************************* Type Definitions ****************************************** *)
(* ********************************************************************************************* *)

  (* Used for distinguishing between types of Illegal Array use in Type Definitions *)
type illArr = Ill_func | Ill_ref | Ill_array

(* ********************************************************************************************* *)
(* ********************************* Global Variables ****************************************** *)
(* ********************************************************************************************* *)

let duckCounter  = ref 0    (* Counter for Fresh Type Variables for Type Inference      *)
let numScopes    = ref 0    (* Counter for Letdef open scopes in Top Level              *)
let unknownArray = ref 0    (* Counter for Fresh Dimension Variables for Type Inference *)
let treeDucks    = ref []   (* List of AST tree pointers to Fresh Type Variables        *)

  (* List of all the supported Llama Library Functions and their specs *)
let library_functions = [
     (*  I/O Functions *)
   ("print_int",    TYPE_unit,  [("x", TYPE_int, PASS_BY_VALUE)]);
   ("print_bool",   TYPE_unit,  [("x", TYPE_bool, PASS_BY_VALUE)]);
   ("print_char",   TYPE_unit,  [("x", TYPE_char, PASS_BY_VALUE)]);
   ("print_float",  TYPE_unit,  [("x", TYPE_float, PASS_BY_VALUE)]);
   ("print_string", TYPE_unit,  [("x", TYPE_array(TYPE_char, 1), PASS_BY_VALUE)]);
   ("read_int",     TYPE_int,   [("x", TYPE_unit, PASS_BY_VALUE)]);
   ("read_bool",    TYPE_bool,  [("x", TYPE_unit, PASS_BY_VALUE)]);
   ("read_char",    TYPE_char,  [("x", TYPE_unit, PASS_BY_VALUE)]);
   ("read_float",   TYPE_float, [("x", TYPE_unit, PASS_BY_VALUE)]);
   ("read_string",  TYPE_unit,  [("x", TYPE_array(TYPE_char, 1), PASS_BY_VALUE)]);
     (* Math Functions *)
   ("abs",  TYPE_int,   [("x", TYPE_int, PASS_BY_VALUE)]);
   ("fabs", TYPE_float, [("x", TYPE_float, PASS_BY_VALUE)]);
   ("sqrt", TYPE_float, [("x", TYPE_float, PASS_BY_VALUE)]);
   ("sin",  TYPE_float, [("x", TYPE_float, PASS_BY_VALUE)]);
   ("cos",  TYPE_float, [("x", TYPE_float, PASS_BY_VALUE)]);
   ("tan",  TYPE_float, [("x", TYPE_float, PASS_BY_VALUE)]);
   ("atan", TYPE_float, [("x", TYPE_float, PASS_BY_VALUE)]);
   ("exp",  TYPE_float, [("x", TYPE_float, PASS_BY_VALUE)]);
   ("ln",   TYPE_float, [("x", TYPE_float, PASS_BY_VALUE)]);
   ("pi",   TYPE_float, [("x", TYPE_float, PASS_BY_VALUE)]);
     (* Increase / Decrease Functions *)
   ("incr", TYPE_unit, [("x", TYPE_ref TYPE_int, PASS_BY_VALUE)]);
   ("decr", TYPE_unit, [("x", TYPE_ref TYPE_int, PASS_BY_VALUE)]);
     (* Type Conversion Functions *)
   ("float_of_int", TYPE_float, [("x", TYPE_int, PASS_BY_VALUE)]);
   ("int_of_float", TYPE_int,   [("x", TYPE_float, PASS_BY_VALUE)]);
   ("round",        TYPE_int,   [("x", TYPE_float, PASS_BY_VALUE)]);
   ("int_of_char",  TYPE_int,   [("x", TYPE_char, PASS_BY_VALUE)]);
   ("char_of_int",  TYPE_char,  [("x", TYPE_int, PASS_BY_VALUE)]);
     (* String Manipulation Functions *)
   ("strlen", TYPE_int, 
      [("x",  TYPE_array(TYPE_char, 1), PASS_BY_VALUE)]);
   ("strcmp", TYPE_int, 
      [("x",  TYPE_array(TYPE_char, 1), PASS_BY_VALUE);
       ("y",  TYPE_array(TYPE_char, 1), PASS_BY_VALUE)]);
   ("strcpy", TYPE_unit, 
      [("x",  TYPE_array(TYPE_char, 1), PASS_BY_VALUE);
       ("y",  TYPE_array(TYPE_char, 1), PASS_BY_VALUE)]);
   ("strcat", TYPE_unit, 
      [("x",  TYPE_array(TYPE_char, 1), PASS_BY_VALUE);
       ("y",  TYPE_array(TYPE_char, 1), PASS_BY_VALUE)]);
]

(* ********************************************************************************************* *)
(* *********************************** Exceptions ********************************************** *)
(* ********************************************************************************************* *)

exception IllegalTypeArray of (int * int * illArr)
exception UnboundUDT of (int * int * string)
exception Duplicate_Parameter of ((int * int) * string)
exception Duplicate_Variable of ((int * int) * string)
exception Duplicate_Function of ((int * int) * string)
exception Unbound_Identifier of ((int * int) * string)
exception Not_Function of ((int * int) * string)
exception Not_Variable of ((int * int) * string)
exception Function_Mismatch_ParamNo of ((int * int) * string * int * int)
exception Unbound_Constructor of ((int * int) * string)
exception Constructor_Mismatch_ParamNo of ((int * int) * string * int * int)
exception Illegal_Pattern of (int * int)
exception VClosure of ((int * int) * string * Types.typ)
exception FClosure of ((int * int) * string * Types.typ)
exception TypeInfErr of (int * int)
exception Polymorphic_Array_Dim of ((int * int) * string)
exception Polymorphic_Type of ((int * int) * string * Types.typ)
exception OutOfBounds of ((int * int) * string * int * int)
exception RetArray of ((int * int) * string)
exception EqIneqArray of ((int * int) * string)
exception EqIneqFunc of ((int * int) * string)
exception ComparOp of ((int * int) * string)
exception Not_found

(* ********************************************************************************************* *)
(* ************************************ Functions ********************************************** *)
(* ********************************************************************************************* *)

(* ************************* *)
(* *** Generic Functions *** *)
(* ************************* *)

let rec unzipList l acc1 acc2 =
   match l with
   | []        -> (List.rev acc1, List.rev acc2)
   | (a, b)::t -> unzipList t (a::acc1) (b::acc2)
   
let getFromTuple2 (a, b) = b

let getFromTuple3 (a, b, c) = c

let add3ToTuple (a, b) c = (a, b, c)

let getPosFromTuple3 (a, b, c) = (a, b)

let rec getCtagFromList l acc =
   match l with
   | []   -> List.rev acc
   | h::t -> getCtagFromList t (h.tag_co::acc)
   
(* ******************************************* *)
(* *** Handle a Typedef / Update UDT Table *** *)
(* ******************************************* *)

  (* Takes a ast_typedef (= ast_tdef_node list) and strips off the positions of the tdef_nodes *)
let rec strip_tdef_node_list l acc =  
   match l with
   | []   -> List.rev acc
   | h::t -> strip_tdef_node_list t (h.tag_td::acc)
   
  (* Converts a Types.typ to Ast.ast_type_node - No checks whatsoever *)
let rec revTypConversion et = 
   match et with
   | TYPE_unit            -> { tag_tp = Tp_unit; meta_tp = [] }
   | TYPE_int             -> { tag_tp = Tp_int; meta_tp = [] }
   | TYPE_char            -> { tag_tp = Tp_char; meta_tp = [] }
   | TYPE_bool            -> { tag_tp = Tp_bool; meta_tp = [] }
   | TYPE_float           -> { tag_tp = Tp_float; meta_tp = [] }
   | TYPE_func (et1, et2) -> { tag_tp = (Tp_func ((revTypConversion et1), (revTypConversion et2))); meta_tp = [] }
   | TYPE_ref t           -> { tag_tp = (Tp_ref (revTypConversion t)); meta_tp = [] }
   | TYPE_array (t, i)    -> { tag_tp = (Tp_array (i, (revTypConversion t))); meta_tp = [] }
   | TYPE_userdef id      -> { tag_tp = (Tp_id id); meta_tp = [] }
   | TYPE_duck i          -> { tag_tp = (Tp_duck i); meta_tp = [] }
   | TYPE_none            -> iInternal "Invalid TYPE_none" None;
                             raise Exit (* Just for compile *)
   
  (* Converts a ast_type_node to Types.typ and checks for consistency *)
let rec typ_conversion et arrayFlag udtFlag =              (* The arrayFlag parameter helps in type validation *)
   match et.tag_tp with
   | Tp_unit            -> TYPE_unit
   | Tp_int             -> TYPE_int
   | Tp_char            -> TYPE_char
   | Tp_bool            -> TYPE_bool
   | Tp_float           -> TYPE_float
   | Tp_func (et1, et2) -> TYPE_func ((typ_conversion et1 None udtFlag), (typ_conversion et2 (Some Ill_func) udtFlag)) 
   | Tp_ref t           -> TYPE_ref (typ_conversion t (Some Ill_ref) udtFlag)
   | Tp_array (n, t)    -> (match arrayFlag with 
                            | Some err -> 
                               let pos = getPosFromMsg et.meta_tp "array_start" in  (* Get Position of Error *)
                               let msg = add3ToTuple pos err in                     (* Add Type of Error in Msg *)
                               raise (IllegalTypeArray msg)                         (* Raise the exception *)
                            | None ->
                               TYPE_array ((typ_conversion t (Some Ill_array) udtFlag), n))
   | Tp_id s            -> (match udtFlag with
                            | None -> 
                               TYPE_userdef s
                            | Some env ->
                               let chk = checkIsDefined s env in
                               if (chk) then
                                  TYPE_userdef s
                               else
                                  let pos = getPosFromMsg et.meta_tp "type_name_start" in
                                  let msg = add3ToTuple pos s in
                                  raise (UnboundUDT msg)
                           )
   | Tp_duck i          -> TYPE_duck i

  (* Takes an ast_type_node list and strips off the positions of the ast_type_nodes and converts to Types.typ *)
let rec strip_ast_type_node_list l acc = 
  match l with 
  | []   -> List.rev acc
  | h::t -> strip_ast_type_node_list t ((typ_conversion h None None)::acc)
  
  (* Takes a list of (constr_name, ast_type_node list) and converts it to a list of (constr_name, types list) *)
let rec strip_tuple_with_tlist l acc = 
   match l with
   | []                      -> List.rev acc
   | (constr_name, tlist)::t -> strip_tuple_with_tlist t ((constr_name, (strip_ast_type_node_list tlist []))::acc)
  
  (* Takes an ast_constr_node list and strips off the positions of the ast_constr_nodes *)
let rec strip_ast_constr_node_list l acc = 
   match l with
   | []   -> strip_tuple_with_tlist (List.rev acc) []
   | h::t -> strip_ast_constr_node_list t (h.tag_co::acc)
   
  (* Takes a list of (type_name, ast_constr_node list) and converts it to a list of (type_name, constructor list) *)
let rec strip_tuple_with_clist l acc = 
   match l with
   | []                    -> List.rev acc
   | (type_name, clist)::t -> strip_tuple_with_clist t ((type_name, (strip_ast_constr_node_list clist []))::acc)
   
  (* Find position info for exception AlreadyDefinedType *)
let rec traverseForType name typdf = 
   match typdf with
   [] ->
      iInternal ("Couldn't locate definition of type " ^ name) None;
      (-1, -1) (* Just for compile *)
   | h::t ->
      (match h.tag_td with
       | (tname, clist) -> 
          if tname = name then
             getPosFromMsg h.meta_td "type_name_start"  (* Get position info from node's meta field *)
          else
             traverseForType name t)
             
  (* Find position info for exceptions DuplicateClauseInEnv and DuplicateClauseInNewBlock *)
let traverseForConstr name typdf num =
   let l1 = strip_tdef_node_list typdf [] in                      (* A list of (type_name, ast_constr_node list) *)
   let l2 = List.flatten (getFromTuple2 (unzipList l1 [] [])) in  (* A list of ast_constr_node *)
   let foo c =                                                    (* Predicate function to locate the constructor *)
      match c.tag_co with
      | (cname, tlist) -> cname = name
   in let conNode = List.nth (List.filter foo l2) num in          (* Get the proper constructor node depending on num parameter *)
   getPosFromMsg conNode.meta_co "constr_name_start"              (* Get position info from node's meta field *)
   
  (* Searches within a type for the usage of a specific UDT name, if there is none it raises the exception Not_found *)
let rec loc_type name et = 
   match et.tag_tp with
   | Tp_id s -> 
      if s = name then
         getPosFromMsg et.meta_tp "type_name_start"     (* Get position info from node's meta field *)
      else
         raise Not_found
   | Tp_func (et1, et2) -> 
      (try 
          loc_type name et1 
       with Not_found -> 
          loc_type name et2)
   | Tp_ref t -> 
      loc_type name t
   | Tp_array (n, t) -> 
      loc_type name t
   | _ -> 
      raise Not_found
   
  (* Find position info for exception UnboundType *)
let traverseForUnboundType name typdf =
   let l1 = strip_tdef_node_list typdf [] in                          (* A list of (type_name, ast_constr_node list) *)
   let l2 = List.flatten (getFromTuple2 (unzipList l1 [] [])) in      (* A list of ast_constr_node *)
   let l3 = getCtagFromList l2 [] in                                  (* A list of ast_constr *)
   let l4 = List.flatten (getFromTuple2 (unzipList l3 [] [])) in      (* A list of ast_type_node *)
   let rec foo l =                                                    (* Function to locate the type usage *)
      (match l with
      | h::t -> 
         (try
            loc_type name h
         with
            Not_found -> foo t)
      | [] ->
         iInternal ("Couldn't locate usage of type " ^ name) None;
         (-1, -1)) (* Just for compile *)
   in foo l4
      
  (* Co-ordinates the operations needed for handling a new typedef block *)
let handleNewTypedef udt_env typdf =
   try
      let l1 = strip_tdef_node_list typdf [] in (* A list of (type_name, ast_constr_node list) *)
      let l2 = strip_tuple_with_clist l1 [] in  (* A list of (type_name, type_structure) *)
      forwardCreateType l2 udt_env;             (* Insert all new UDT names in the UDT table *)
      updateTypeStructure l2 udt_env            (* Update their structure and check for errors *)
   with
   | IllegalTypeArray msg ->
      let pos = getPosFromTuple3 msg in
      let res = getFromTuple3 msg in
      (match res with
       | Ill_func  -> ifatal "Cannot use Array type as result of a function" (Some pos) 
       | Ill_ref   -> ifatal "Cannot use reference to an Array type" (Some pos) 
       | Ill_array -> ifatal "Cannot use an Array Type of arrays" (Some pos))
   | AlreadyDefinedType name ->
      ifatal ("Type " ^ name ^ " is already defined or is defined again in the same typedef block") (Some (traverseForType name typdf))
   | UnboundType name ->
      ifatal ("Type " ^ name ^ " is Unbound") (Some (traverseForUnboundType name typdf)) 
   | DuplicateClauseInEnv name ->
      ifatal ("Constructor " ^ name ^ " is already defined in a previous declaration") (Some (traverseForConstr name typdf 0)) 
   | DuplicateClauseInNewBlock name ->
      ifatal ("Constructor " ^ name ^ " is defined more than once in this declaration") (Some (traverseForConstr name typdf 1)) 
      
(* ********************************************** *)
(* *** Handle a Letdef / Generate constraints *** *)
(* ********************************************** *)

  (* Gets a list of Symbol Table entries - hopefully parameters - and returns a list of their respective types *)
let rec getListWithParamsTypes l acc = 
   match l with
   | []   -> List.rev acc
   | h::t -> (match h.entry_info with
              | ENTRY_parameter pinfo -> 
                 let par_type = pinfo.parameter_type in
                 getListWithParamsTypes t (par_type :: acc)
              | _ ->   (* If it's not a parameter then something has gone wrong *)
                 iInternal "Expected Parameter but something else showed up!" None;
                 []    (* Just for compile *)
             )
             
  (* Constructs the type of function from the list of its parameters' types and its result type *)
let constructFuncType parList resType =
   let rec foo l acc =
      (match l with
       | []   -> acc
       | h::t -> foo t (TYPE_func (h, acc))
      )
   in foo (List.rev parList) resType
   
  (* Handles an ast_expr_node *)
let rec genPass_Expr udt_env expr =
   match expr.tag_ex with
   | E_int i ->
      TYPE_int
   | E_real x ->
      TYPE_float
   | E_char c ->
      TYPE_char
   | E_string s ->
      TYPE_array (TYPE_char, 1)
   | E_bool b ->
      TYPE_bool
   | E_unit ->
      TYPE_unit
   | E_var id ->
      let pos = getPosFromMsg expr.meta_ex "id_name_start" in
      (try
         let entry = lookupEntry (id_make id) LOOKUP_ALL_SCOPES true in                 (* Lookup Variable in the Symbol Table    *)
         (match entry.entry_info with
          | ENTRY_variable vinfo ->                                                     (* If the entry is a variable             *)
             vinfo.variable_type                                                        (* Return its type                        *)
          | ENTRY_parameter pinfo ->                                                    (* If the entry is a variable             *)
             pinfo.parameter_type                                                       (* Return its type                        *)
          | ENTRY_function finfo ->                                                     (* If the entry is a function             *)
             let res_type = finfo.function_result in                                    (* Find its result type                   *)
             let par_types = getListWithParamsTypes finfo.function_paramlist [] in      (* Make a list of its parameters' types   *)
             constructFuncType par_types res_type                                       (* Construct the function's type          *)
          | _ ->  (* If it's not a variable or parameter or function then something has gone wrong *)
             iInternal ("Identifier " ^ id ^ " is not Variable or Parameter or Function") (Some pos);
             raise Terminate
         )
       with
       | Unknown_Identifier ->                                                          (* If the Identifier is Unbound           *)
          raise (Unbound_Identifier (pos, id))                                          (* Raise the Unbound_Identifier exception *)
      )
   | E_func (id, elist) ->
      let pos = getPosFromMsg expr.meta_ex "id_name_start" in
      (try
         let entry = lookupEntry (id_make id) LOOKUP_ALL_SCOPES true in                 (* Lookup Function in the Symbol Table        *)
         (match entry.entry_info with
          | ENTRY_function finfo ->                                                     (* If the entry is indeed a function          *)
             let num_of_expected = List.length finfo.function_paramlist in              (* Get the number of Expected Parameters      *)
             let num_of_actual = List.length elist in                                   (* Get the number of Actual Parameters        *)
             if num_of_actual != num_of_expected then                                   (* If they don't match raise an exception     *)
                raise (Function_Mismatch_ParamNo (pos, id, num_of_expected, num_of_actual));
             let par_types = getListWithParamsTypes finfo.function_paramlist [] in      (* Get the List of the Parameter Types        *)
             let e_types = List.map (fun e -> genPass_Expr udt_env e) elist in          (* Get the List of the Actual Parameter Types *)
             List.iter (fun c -> addConstraint c pos) (List.combine par_types e_types); (** ADD CONSTRAINTS *)
             finfo.function_result                                                      (* Return its result type                     *)
          | ENTRY_parameter pinfo ->                                                    (* If the entry is indeed a function          *)
             let e_types = List.map (fun e -> genPass_Expr udt_env e) elist in          (* Get the List of the Actual Parameter Types *)
             incr duckCounter;
             let duck = TYPE_duck !duckCounter in                                       (* New Type Variable for result type          *)
             let func_type = constructFuncType e_types duck in                          (* Construct funciton's full type             *)
             addConstraint (pinfo.parameter_type, func_type) pos;                       (** ADD CONSTRAINTS *)
             duck                                                                       (* Return its result type                     *)
          | _ ->                                                                        (* If it's not a function                     *)
             raise (Not_Function (pos, id))                                             (* Raise the Not_Funcion exception            *)
         )
       with
       | Unknown_Identifier ->                                                          (* If the Identifier is Unbound               *)
          raise (Unbound_Identifier (pos, id))                                          (* Raise the Unbound_Identifier exception     *)
      )
   | E_constr (id, elist) ->
      let pos = getPosFromMsg expr.meta_ex "constr_name_start" in
      (try 
         let entry = lookupConstructor udt_env id in                                    (* Lookup Constructor in the UDT Table        *)
         (match entry with
          | (type_name, tlist) ->
             let num_of_expected = List.length tlist in                                 (* Get the number of Expected Parameters      *)
             let num_of_actual = List.length elist in                                   (* Get the number of Actual Parameters        *)
             if num_of_actual != num_of_expected then                                   (* If they don't match raise an exception     *)
                raise (Constructor_Mismatch_ParamNo (pos, id, num_of_expected, num_of_actual));
             let e_types = List.map (fun e -> genPass_Expr udt_env e) elist in          (* Get the List of the Actual Parameter Types *)
             List.iter (fun c -> addConstraint c pos) (List.combine tlist e_types);     (** ADD CONSTRAINTS *)
             TYPE_userdef type_name                                                     (* Return the udt as result type              *)
         )
       with
       | Unknown_Constructor ->                                                         (* If the Constructor is Unbound              *)
          raise (Unbound_Constructor (pos, id))                                         (* Raise the Unbound_Constructor exception    *)
      )
   | E_bang e ->
      let pos = getPosFromMsg expr.meta_ex "bang_start" in
      let e_type = genPass_Expr udt_env e in                                            (* Get the type of the inner expression       *)
      incr duckCounter;
      let duck = TYPE_duck !duckCounter in                                              (* New Type Variable for result type          *)
      addConstraint (e_type, TYPE_ref duck) pos;                                        (** ADD CONSTRAINT *)
      duck
   | E_not e ->
      let pos = getPosFromMsg expr.meta_ex "not_start" in
      let e_type = genPass_Expr udt_env e in                                            (* Get the type of the inner expression       *)
      addConstraint (e_type, TYPE_bool) pos;                                            (** ADD CONSTRAINT *)
      TYPE_bool                                                                         (* Return bool as type                        *)
   | E_signed (s, e) ->
      let pos = getPosFromMsg expr.meta_ex "op_start" in
      let e_type =  genPass_Expr udt_env e in                                           (* Get the type of the inner expression       *)
      (match s with
       | S_plus   -> addConstraint (e_type, TYPE_int) pos;                              (** ADD CONSTRAINT *)
                     TYPE_int
       | S_minus  -> addConstraint (e_type, TYPE_int) pos;                              (** ADD CONSTRAINT *)
                     TYPE_int
       | S_fplus  -> addConstraint (e_type, TYPE_float) pos;                            (** ADD CONSTRAINT *)
                     TYPE_float
       | S_fminus -> addConstraint (e_type, TYPE_float) pos;                            (** ADD CONSTRAINT *)
                     TYPE_float
       | Unsigned -> iInternal "Didn't Expect Unsigned Expression" None;
                     raise Terminate
      )
   | E_binop (e1, bn, e2) ->
      let pos = getPosFromMsg expr.meta_ex "op_start" in
      let e1_type = genPass_Expr udt_env e1 in                                          (* Get the type of the left inner expression  *)
      let e2_type = genPass_Expr udt_env e2 in                                          (* Get the type of the right inner expression *)
      (match bn with
       | B_plus       -> addConstraint (e1_type, TYPE_int) pos;                         (** ADD CONSTRAINT *)
                         addConstraint (e2_type, TYPE_int) pos;                         (** ADD CONSTRAINT *)
                         TYPE_int
       | B_minus      -> addConstraint (e1_type, TYPE_int) pos;                         (** ADD CONSTRAINT *)
                         addConstraint (e2_type, TYPE_int) pos;                         (** ADD CONSTRAINT *)
                         TYPE_int
       | B_mult       -> addConstraint (e1_type, TYPE_int) pos;                         (** ADD CONSTRAINT *)
                         addConstraint (e2_type, TYPE_int) pos;                         (** ADD CONSTRAINT *)
                         TYPE_int
       | B_div        -> addConstraint (e1_type, TYPE_int) pos;                         (** ADD CONSTRAINT *)
                         addConstraint (e2_type, TYPE_int) pos;                         (** ADD CONSTRAINT *)
                         TYPE_int
       | B_fplus      -> addConstraint (e1_type, TYPE_float) pos;                       (** ADD CONSTRAINT *)
                         addConstraint (e2_type, TYPE_float) pos;                       (** ADD CONSTRAINT *)
                         TYPE_float
       | B_fminus     -> addConstraint (e1_type, TYPE_float) pos;                       (** ADD CONSTRAINT *)
                         addConstraint (e2_type, TYPE_float) pos;                       (** ADD CONSTRAINT *)
                         TYPE_float
       | B_fmult      -> addConstraint (e1_type, TYPE_float) pos;                       (** ADD CONSTRAINT *)
                         addConstraint (e2_type, TYPE_float) pos;                       (** ADD CONSTRAINT *)
                         TYPE_float
       | B_fdiv       -> addConstraint (e1_type, TYPE_float) pos;                       (** ADD CONSTRAINT *)
                         addConstraint (e2_type, TYPE_float) pos;                       (** ADD CONSTRAINT *)
                         TYPE_float
       | B_mod        -> addConstraint (e1_type, TYPE_int) pos;                         (** ADD CONSTRAINT *)
                         addConstraint (e2_type, TYPE_int) pos;                         (** ADD CONSTRAINT *)
                         TYPE_int
       | B_pow        -> addConstraint (e1_type, TYPE_float) pos;                       (** ADD CONSTRAINT *)
                         addConstraint (e2_type, TYPE_float) pos;                       (** ADD CONSTRAINT *)
                         TYPE_float
       | B_assign     -> addConstraint (e1_type, e2_type) pos;                          (** ADD CONSTRAINT *)
                         TYPE_bool
       | B_ltgt       -> addConstraint (e1_type, e2_type) pos;                          (** ADD CONSTRAINT *)
                         TYPE_bool
       | B_lt         -> addConstraint (e1_type, e2_type) pos;                          (** ADD CONSTRAINT *)
                         TYPE_bool
       | B_gt         -> addConstraint (e1_type, e2_type) pos;                          (** ADD CONSTRAINT *)
                         TYPE_bool
       | B_lteq       -> addConstraint (e1_type, e2_type) pos;                          (** ADD CONSTRAINT *)
                         TYPE_bool
       | B_gteq       -> addConstraint (e1_type, e2_type) pos;                          (** ADD CONSTRAINT *)
                         TYPE_bool
       | B_eq         -> addConstraint (e1_type, e2_type) pos;                          (** ADD CONSTRAINT *)
                         TYPE_bool
       | B_neq        -> addConstraint (e1_type, e2_type) pos;                          (** ADD CONSTRAINT *)
                         TYPE_bool
       | B_conj       -> addConstraint (e1_type, TYPE_bool) pos;                        (** ADD CONSTRAINT *)
                         addConstraint (e2_type, TYPE_bool) pos;                        (** ADD CONSTRAINT *)
                         TYPE_bool
       | B_disj       -> addConstraint (e1_type, TYPE_bool) pos;                        (** ADD CONSTRAINT *)
                         addConstraint (e2_type, TYPE_bool) pos;                        (** ADD CONSTRAINT *)
                         TYPE_bool
       | B_semic      -> e2_type
       | B_refassign  -> incr duckCounter;
                         let duck = TYPE_duck !duckCounter in                           (* New Type Variable for result type          *)
                         addConstraint (e1_type, TYPE_ref duck) pos;                    (** ADD CONSTRAINT *)
                         addConstraint (e2_type, duck) pos;                             (** ADD CONSTRAINT *)
                         TYPE_unit
      )
   | E_array (id, elist) ->
      let pos = getPosFromMsg expr.meta_ex "array_name_start" in
      (try
         let entry = lookupEntry (id_make id) LOOKUP_ALL_SCOPES true in
         (match entry.entry_info with
          | ENTRY_variable vinfo ->                                                     (* If the entry is a variable                 *)
             let e_types = List.map (fun e -> genPass_Expr udt_env e) elist in          (* Recurse on all the Inner Expressions       *)
             List.iter (fun e -> addConstraint (e, TYPE_int) pos) e_types;              (** ADD CONSTRAINT *)
             incr duckCounter;
             let n = List.length elist in
             let duck = TYPE_duck !duckCounter in                                       (* New Type Variable for result type          *)
             addConstraint (vinfo.variable_type, TYPE_array(duck, n)) pos;              (** ADD CONSTRAINT *)
             TYPE_ref duck
          | ENTRY_parameter pinfo ->                                                    (* If the entry is a parameter                *)
             let e_types = List.map (fun e -> genPass_Expr udt_env e) elist in          (* Recurse on all the Inner Expressions       *)
             List.iter (fun e -> addConstraint (e, TYPE_int) pos) e_types;              (** ADD CONSTRAINT *)
             incr duckCounter;
             let n = List.length elist in
             let duck = TYPE_duck !duckCounter in                                       (* New Type Variable for result type          *)
             addConstraint (pinfo.parameter_type, TYPE_array(duck, n)) pos;             (** ADD CONSTRAINT *)
             TYPE_ref duck
          | _ ->                                                                        (* If it's something else                     *)
             raise (Not_Variable (pos, id))                                             (* Raise the Not_Variable exception           *)
         )
       with
       | Unknown_Identifier ->                                                          (* If the Identifier is Unbound               *)
          raise (Unbound_Identifier (pos, id))                                          (* Raise the Unbound_Identifier exception     *)
      )
   | E_dim (il, id) ->
      let pos = getPosFromMsg expr.meta_ex "id_name_start" in
      (try
         let entry = lookupEntry (id_make id) LOOKUP_ALL_SCOPES true in
         (match entry.entry_info with
          | ENTRY_variable vinfo ->                                                     (* If the entry is a variable                 *)
             incr duckCounter;
             let duck = TYPE_duck !duckCounter in                                       (* New Type Variable                          *)
             decr unknownArray;                                                         (* New Array Dimension Variable               *)
             addConstraint (vinfo.variable_type, TYPE_array(duck, !unknownArray)) pos;  (** ADD CONSTRAINT *) 
             TYPE_int
          | ENTRY_parameter pinfo ->                                                    (* If the entry is a parameter                *)
             incr duckCounter;
             let duck = TYPE_duck !duckCounter in                                       (* New Type Variable                          *)
             decr unknownArray;                                                         (* New Array Dimension Variable               *)
             addConstraint (pinfo.parameter_type, TYPE_array(duck, !unknownArray)) pos; (** ADD CONSTRAINT *) 
             TYPE_int
          | _ ->                                                                        (* If it's something else                     *)
             raise (Not_Variable (pos, id))                                             (* Raise the Not_Variable exception           *)
         )
       with
       | Unknown_Identifier ->                                                          (* If the Identifier is Unbound               *)
          raise (Unbound_Identifier (pos, id))                                          (* Raise the Unbound_Identifier exception     *)
      )
   | E_new et ->
      let et_type = typ_conversion et (Some Ill_ref) (Some udt_env) in                  (* Get the type of et                         *)
      TYPE_ref et_type                                                                  (* Return a reference to et                   *)
   | E_del e ->
      let pos = getPosFromMsg expr.meta_ex "del_start" in
      let e_type = genPass_Expr udt_env e in                                            (* Get the type of the Inner Expression       *)
      incr duckCounter;
      let duck = TYPE_duck !duckCounter in                                              (* New Type Variable                          *)
      addConstraint (e_type, TYPE_ref duck) pos;                                        (** ADD CONSTRAINT *)
      TYPE_unit
   | E_in (lt, e) ->
      openScope ();                                                                     (* Open Letdef's Scope                        *)
      handleNewLetDef udt_env lt.tag_lt;                                                (* Handle the Letdef                          *)
      let e_type = genPass_Expr udt_env e in                                            (* Get the type of the Inner Expression       *)
      closeScope ();                                                                    (* Close Letdef's Scope                       *)
      e_type                                                                            (* Return the type of the Inner Expression    *)
   | E_begin e ->
      genPass_Expr udt_env e                                                            (* Just do the work for the Inner Expression  *)
   | E_if (e, e1) ->
      let pos = getPosFromMsg expr.meta_ex "if_start" in
      let e_type = genPass_Expr udt_env e in                                            (* Get the type of the Condition Expression   *)
      let e1_type = genPass_Expr udt_env e1 in                                          (* Get the type of the True Expression        *)
      addConstraint (e_type, TYPE_bool) pos;                                            (** ADD CONSTRAINT *)
      addConstraint (e1_type, TYPE_unit) pos;                                           (** ADD CONSTRAINT *)
      TYPE_unit                                                                         (* Return the type of the true Expression     *)
   | E_ifelse (e, e1, e2) ->
      let pos = getPosFromMsg expr.meta_ex "if_start" in
      let e_type = genPass_Expr udt_env e in                                            (* Get the type of the Condition Expression   *)
      let e1_type = genPass_Expr udt_env e1 in                                          (* Get the type of the True Expression        *)
      let e2_type = genPass_Expr udt_env e2 in                                          (* Get the type of the False Expression       *)
      incr duckCounter;
      let duck = TYPE_duck !duckCounter in                                              (* New Type Variable                          *)
      addConstraint (e_type, TYPE_bool) pos;                                            (** ADD CONSTRAINT *)
      addConstraint (e1_type, duck) pos;                                                (** ADD CONSTRAINT *)
      addConstraint (e2_type, duck) pos;                                                (** ADD CONSTRAINT *)
      duck
   | E_while (e, e1) ->
      let pos = getPosFromMsg expr.meta_ex "while_start" in
      let e_type = genPass_Expr udt_env e in                                            (* Get the type of the Condition Expression   *)
      let e1_type = genPass_Expr udt_env e1 in                                          (* Get the type of the True Expression        *)
      addConstraint (e_type, TYPE_bool) pos;                                            (** ADD CONSTRAINT *)
      addConstraint (e1_type, TYPE_unit) pos;                                           (** ADD CONSTRAINT *)
      TYPE_unit                                                                         (* Return Unit as type                        *)
   | E_for (id, e1, lt, e2, e) ->
      let pos = getPosFromMsg expr.meta_ex "id_name_start" in
      (try
         openScope ();                                                                  (* Open the Scope for the Counter Var         *)
         ignore (newVariable (id_make id) TYPE_int true pos);                           (* Add the Counter Var to the Symbol Table    *)
         let e1_type = genPass_Expr udt_env e1 in                                       (* Get the type of the Start Expression       *)
         let e2_type = genPass_Expr udt_env e2 in                                       (* Get the type of the End Expression         *)
         let e_type = genPass_Expr udt_env e in                                         (* Get the type of the Inner Expression       *)
         addConstraint (e1_type, TYPE_int) pos;                                         (** ADD CONSTRAINT *)
         addConstraint (e2_type, TYPE_int) pos;                                         (** ADD CONSTRAINT *)
         addConstraint (e_type, TYPE_unit) pos;                                         (** ADD CONSTRAINT *)
         closeScope ();                                                                 (* Close the Scope for the Counter Var        *)
         TYPE_unit                                                                      (* Return Unit as type                        *)
       with
       | Exit -> raise (Duplicate_Variable (pos, id))
      )
   | E_match (e, clList) ->
      let e_type = genPass_Expr udt_env e in                                            (* Get the type of the Inner Expression       *) 
      let cl_types = List.map (fun cl -> genPass_Clause udt_env e_type cl) clList in    (* Recurse on all clauses providing e_type    *)
      incr duckCounter;
      let match_type = TYPE_duck !duckCounter in                                        (* Generate a type for the match expression   *)
      let pos = getPosFromMsg expr.meta_ex "match_start" in
      List.iter (fun c -> addConstraint (match_type, c) pos) cl_types;                  (** ADD CONSTRAINT *)
      match_type
      
and genPass_Clause udt_env common_pat_type cl = 
   match cl.tag_cl with
   | (pat, e) ->
      openScope ();                                                                     (* Open the Scope for the pattern             *)
      let pat_type = genPass_Pat udt_env pat true in                                    (* Get the type of the pattern                *)
      let pos = getPosFromMsg cl.meta_cl "pat_name_start" in
      addConstraint (common_pat_type, pat_type) pos;                                    (** ADD CONSTRAINT *)
      let e_type = genPass_Expr udt_env e in                                            (* Get the type of the expression             *)
      closeScope ();                                                                    (* Close the Scope of the pattern             *)
      e_type                                                                            (* Return the type of the expression          *)
      
and genPass_Pat udt_env pat flag =
   let pos = getPosFromMsg pat.meta_pt "pat_name_start" in
   match pat.tag_pt with
   | P_int (sgn, i) ->
      if flag then
         raise (Illegal_Pattern pos)
      else
         TYPE_int
   | P_real (sgn, x) ->
      if flag then
         raise (Illegal_Pattern pos)
      else
         TYPE_float
   | P_char c ->
      if flag then
         raise (Illegal_Pattern pos)
      else
         TYPE_char
   | P_bool b ->
      if flag then
         raise (Illegal_Pattern pos)
      else
         TYPE_bool
   | P_id id ->
      (try
         incr duckCounter;
         let var_type = TYPE_duck !duckCounter in
         ignore (newVariable (id_make id.pname) var_type true pos);
         id.ptype := Some {tag_tp = Tp_duck !duckCounter; meta_tp = []};
         treeDucks := id.ptype::!treeDucks;
         var_type
       with
       | Exit -> raise (Duplicate_Variable (pos, id.pname))
      )
   | P_constr (id, patList) ->
      (try 
         let entry = lookupConstructor udt_env id in                                    (* Lookup Constructor in the UDT Table        *)
         (match entry with
          | (type_name, tlist) ->
             let num_of_expected = List.length tlist in                                 (* Get the number of Expected Parameters      *)
             let num_of_actual = List.length patList in                                 (* Get the number of Actual Parameters        *)
             if num_of_actual != num_of_expected then                                   (* If they don't match raise an exception     *)
                raise (Constructor_Mismatch_ParamNo (pos, id, num_of_expected, num_of_actual));
             let p_types = List.map (fun p -> genPass_Pat udt_env p false) patList in   (* Get the List of the Actual Parameter Types *)
             List.iter (fun c -> addConstraint c pos) (List.combine tlist p_types);     (** ADD CONSTRAINTS *)
             TYPE_userdef type_name                                                     (* Return the udt as result type              *)
         )
       with
       | Unknown_Constructor ->                                                         (* If the Constructor is Unbound              *)
          raise (Unbound_Constructor (pos, id))                                         (* Raise the Unbound_Constructor exception    *)
      )
   
  (* Handles an ast_par_node *)
and genPass_Par udt_env par func =
   match par.tag_pr with
   | (id, t, en) ->
      let pos = getPosFromMsg par.meta_pr "par_name_start" in                           (* Get Position Info of Parameter             *)
      (try
         (match !t with
          | None ->     (* If the user ommited the type *)
             incr duckCounter;
             let par_type = TYPE_duck !duckCounter in                                   (* Create New Type Variable                   *)
             ignore (newParameter (id_make id) par_type PASS_BY_VALUE func true pos);   (* Add Parameter to Symbol Table              *)
             t := Some {tag_tp = Tp_duck !duckCounter; meta_tp = []};                   (* Update the AST with the Type Variable      *)
             treeDucks := t::!treeDucks;                                                (* Add new Type variable to list              *)
             par_type
          | Some et ->  (* If the user has declared the type *)
             let par_type = typ_conversion et None (Some udt_env) in                    (* Read the type annotation from the AST      *)
             ignore (newParameter (id_make id) par_type PASS_BY_VALUE func true pos);   (* Add Parameter to Symbol Table              *)
             par_type
         )
       with
       | Exit -> raise (Duplicate_Parameter (pos, id))
      )
      
  (* Handles an ast_def_now with Let *)
and genPass_Def udt_env df =  (* Will ultimately return the Func / Var so that handleNewLetDef makes it visible *)
   match df.tag_df with
   | Def_func (id, [], t, e) ->  (* Case of Variable *)
      let pos = getPosFromMsg df.meta_df "id_name_start" in             (* Get Variable Position Info *)
      (try
         (match !t with
          | None ->
             incr duckCounter;
             let var_type = TYPE_duck !duckCounter in                             (* Create New Type Variable                 *)
             let var = newVariable (id_make id) var_type true pos in              (* Add Variable to Symbol Table             *)
             visibilityOfEntry var false;                                         (* Make entry invisible                     *)
             t := Some {tag_tp = Tp_duck !duckCounter; meta_tp = []};             (* Update the AST with the Type Variable    *)
             treeDucks := t::!treeDucks;                                          (* Add new Type variable to list            *)
             openScope ();
             let expr_type = genPass_Expr udt_env e in                            (* Get the type of the Inner Expression     *)
             closeScope ();
             addConstraint (var_type, expr_type) pos;                             (** ADD CONSTRAINTS *)
             var                                                                  (* Return the Variable entry                *)
          | Some et ->
             let var_type = typ_conversion et None (Some udt_env) in              (* Read the type annotation from the AST    *)
             let var = newVariable (id_make id) var_type true pos in              (* Add Variable to Symbol Table             *)
             visibilityOfEntry var false;                                         (* Make entry invisible                     *)
             openScope ();
             let expr_type = genPass_Expr udt_env e in                            (* Get the type of the Inner Expression     *)
             closeScope ();
             addConstraint (var_type, expr_type) pos;                             (** ADD CONSTRAINTS *)
             var                                                                  (* Return the Variable entry                *)
         )
       with
       | Exit -> raise (Duplicate_Variable (pos, id))
      )
   | Def_func (id, parList, t, e) ->  (* Case of function *)
      let pos = getPosFromMsg df.meta_df "id_name_start" in                       (* Get Function Position Info               *)
      (try
         (match !t with
          | None ->
             incr duckCounter;
             let fun_type = TYPE_duck !duckCounter in                             (* Create New Type Variable                 *)
             let func = newFunction (id_make id) true pos in                      (* Add Function to Symbol Table             *)
             t := Some {tag_tp = Tp_duck !duckCounter; meta_tp = []};             (* Update the AST with the Type Variable    *)
             treeDucks := t::!treeDucks;                                          (* Add new Type variable to list            *)
             visibilityOfEntry func false;                                        (* Make entry invisible                     *)
             openScope();                                                         (* Open Inner Scope                         *)
             ignore(List.map (fun par -> genPass_Par udt_env par func) parList);  (* Process Function Parameters              *)
             endFunctionHeader func fun_type;                                     (* Add Function's Result Type               *)
             let expr_type = genPass_Expr udt_env e in                            (* Get the type of the Inner Expression     *)
             addConstraint (fun_type, expr_type) pos;                             (** ADD CONSTRAINTS *)
             closeScope();                                                        (* Close Inner Scope                        *)
             func                                                                 (* Return the Function entry                *)
          | Some et ->
             let fun_type = typ_conversion et (Some Ill_func) (Some udt_env) in   (* Get Result Type that's stored in the AST *)
             let func = newFunction (id_make id) true pos in                      (* Definition of function                   *)
             visibilityOfEntry func false;                                        (* Make entry invisible                     *)
             openScope();                                                         (* Open Inner Scope                         *)
             ignore(List.map (fun par -> genPass_Par udt_env par func) parList);  (* Process Function Parameters              *)
             endFunctionHeader func fun_type;                                     (* Add Function's Result Type               *)
             let expr_type = genPass_Expr udt_env e in                            (* Get the type of the Inner Expression     *)
             addConstraint (fun_type, expr_type) pos;                             (** ADD CONSTRAINTS *)
             closeScope();                                                        (* Close Inner Scope                        *)
             func                                                                 (* Return the Function entry                *)
         )
       with
       | Exit -> raise (Duplicate_Function (pos, id))
      )
   | Def_mut (id, e, t) ->  (* Case of mutable *)
      let pos = getPosFromMsg df.meta_df "id_name_start" in                       (* Get Mutable Position Info                *)
      (try
         (match !t with
          | None ->
             incr duckCounter;
             (match List.length e with                                            (* Distinguish between array and resy types *)
              | 0 -> 
                 let var_type = TYPE_ref (TYPE_duck !duckCounter) in              (* Create New Type Variable                 *)
                 let var = newVariable (id_make id) var_type true pos in          (* Add Mutable to Symbol Table              *)
                 t := Some {tag_tp = Tp_duck !duckCounter; meta_tp = []};         (* Update the AST with the Type Variable    *)
                 treeDucks := t::!treeDucks;                                      (* Add new Type variable to list            *)
                 visibilityOfEntry var false;
                 var
              | n -> 
                 let var_type = TYPE_array (TYPE_duck !duckCounter, n) in         (* Create New Type Variable                 *)
                 let var = newVariable (id_make id) var_type true pos in          (* Add Mutable to Symbol Table              *)
                 t := Some {tag_tp = Tp_duck !duckCounter; meta_tp = []};         (* Update the AST with the Type Variable    *)
                 treeDucks := t::!treeDucks;                                      (* Add new Type variable to list            *)
                 visibilityOfEntry var false;
                 let e_types = List.map (fun ex -> genPass_Expr udt_env ex) e in  (* Get the types of the Inner Expressions   *)
                 List.iter (fun e -> addConstraint (e, TYPE_int) pos) e_types;    (** ADD CONSTRAINTS *)
                 var
             )
          | Some et ->
             (match List.length e with                                            (* Distinguish between array and resy types *)
              | 0 -> 
                 let var_type = 
                    TYPE_ref (typ_conversion et (Some Ill_ref) (Some udt_env)) in (* Create New Type Variable                 *)
                 let var = newVariable (id_make id) var_type true pos in          (* Add Mutable to Symbol Table              *)
                 visibilityOfEntry var false;
                 var
              | n -> 
                 let var_type = 
                    TYPE_array (typ_conversion et (Some Ill_array) (Some udt_env), n) in  (* Create New Type Variable         *)
                 let var = newVariable (id_make id) var_type true pos in          (* Add Mutable to Symbol Table              *)
                 visibilityOfEntry var false;
                 let e_types = List.map (fun ex -> genPass_Expr udt_env ex) e in  (* Get the types of the Inner Expressions   *)
                 List.iter (fun e -> addConstraint (e, TYPE_int) pos) e_types;    (** ADD CONSTRAINTS *)
                 var
             )
         )
       with
       | Exit -> raise (Duplicate_Variable (pos, id))
      )

  (* Handles an ast_def_now with Let Rec *)
and genPass_Rec_Def mode udt_env df =  (* mode 0 is normal, mode 1 is forward declaration *)
   match df.tag_df with
   | Def_func (id, [], t, e) ->  (* Case of Variable *)
      let pos = getPosFromMsg df.meta_df "id_name_start" in                 (* Get Variable Position Info                        *)
      (match mode with
       | 0 -> (* 2nd Pass *)
          (try
             let entry = lookupEntry (id_make id) LOOKUP_ALL_SCOPES true in
             (match entry.entry_info with
              | ENTRY_variable vinfo ->
                 let var_type = vinfo.variable_type in                      (* Get the type of the variable from the Symbol Table *)
                 openScope ();
                 let expr_type = genPass_Expr udt_env e in                  (* Get the type of the Inner Expression               *)
                 closeScope ();
                 addConstraint (var_type, expr_type) pos                    (** ADD CONSTRAINT *)
              | _ -> 
                 iInternal "Forward Pass added entry but it's not a Variable" (Some pos)
             )
           with
           | Unknown_Identifier -> 
              iInternal "Forward Pass didn't add Variable" (Some pos)
          )
       | _ ->  (* 1st Pass *)
          (try
             (match !t with
              | None ->
                 incr duckCounter;
                 let var_type = TYPE_duck !duckCounter in                   (* Create New Type Variable              *)
                 ignore (newVariable (id_make id) var_type true pos);       (* Add Variable to Symbol Table          *)
                 t := Some {tag_tp = Tp_duck !duckCounter; meta_tp = []};   (* Update the AST with the Type Variable *)
                 treeDucks := t::!treeDucks;                                (* Add new Type variable to list         *)
              | Some et ->
                 let var_type = typ_conversion et None (Some udt_env) in    (* Read the type annotation from the AST *)
                 ignore (newVariable (id_make id) var_type true pos)        (* Add Variable to Symbol Table          *)
             )
           with
           | Exit -> raise (Duplicate_Variable (pos, id))
          )
      )
   | Def_func (id, parList, t, e) ->  (* Case of function *)
      let pos = getPosFromMsg df.meta_df "id_name_start" in                       (* Get Function Position Info               *)
      (match mode with
       | 0 ->  (* 2nd Pass - Don't expect Exit exception for newFunction since it was caught on 1st Pass *)
         (match !t with
          | None -> 
             iInternal "Failed to add Function Result Type on 1st Pass for Forward Definitions" None
          | Some et ->
             let fun_type = typ_conversion et (Some Ill_func) (Some udt_env) in      (* Get Result Type that is stored in the AST *)
             let func = newFunction (id_make id) true pos in                         (* Definition of function                    *)
             openScope();                                                            (* Open Inner Scope                          *)
             ignore(List.map (fun par -> genPass_Par udt_env par func) parList);     (* Process Function Parameters               *)
             endFunctionHeader func fun_type;                                        (* Add Function's Result Type                *)
             let expr_type = genPass_Expr udt_env e in                               (* Get the type of the Inner Expression      *)
             addConstraint (fun_type, expr_type) pos;                                (** ADD CONSTRAINT *)
             closeScope()                                                            (* Close Inner Scope                         *)
         )
       | _ -> (* 1st Pass *)
         (try
            (match !t with
             | None ->
                incr duckCounter;
                let fun_type = TYPE_duck !duckCounter in                             (* Create New Type Variable                  *)
                let func = newFunction (id_make id) true pos in                      (* Add Function to Symbol Table              *)
                t := Some {tag_tp = Tp_duck !duckCounter; meta_tp = []};             (* Update the AST with the Type Variable     *)
                treeDucks := t::!treeDucks;                                          (* Add new Type variable to list             *)
                forwardFunction func;                                                (* Declare this is a forward definition      *)
                openScope();                                                         (* Open Inner Scope                          *)
                ignore(List.map (fun par -> genPass_Par udt_env par func) parList);  (* Process Function Parameters               *)
                endFunctionHeader func fun_type;                                     (* Add Function's Result Type                *)
                closeScope()                                                         (* Close Inner Scope                         *)
             | Some et ->
                let fun_type = typ_conversion et (Some Ill_func) (Some udt_env) in   (* Read the type annotation from the AST     *)
                let func = newFunction (id_make id) true pos in                      (* Add Function to Symbol Table              *)
                forwardFunction func;                                                (* Declare this is a forward definition      *)
                openScope();                                                         (* Open Inner Scope                          *)
                ignore(List.map (fun par -> genPass_Par udt_env par func) parList);  (* Process Function Parameters               *)
                endFunctionHeader func fun_type;                                     (* Add Function's Result Type                *)
                closeScope()                                                         (* Close Inner Scope                         *)
            )
          with
          | Exit -> raise (Duplicate_Function (pos, id))
         )
      )
   | Def_mut (id, e, t) ->  (* Case of mutable *)
      let pos = getPosFromMsg df.meta_df "id_name_start" in                          (* Get Mutable Position Info                 *)
      (match mode with
       | 0 -> (* 2nd Pass *)
          let e_types = List.map (fun ex -> genPass_Expr udt_env ex) e in            (* Get the types of the Inner Expressions    *)
          List.iter (fun e -> addConstraint (e, TYPE_int) pos) e_types;              (** ADD CONSTRAINTS *)
       | _ -> (* 1st Pass *)
          (try
             (match !t with
              | None ->
                 incr duckCounter;
                 (match List.length e with                                           (* Distinguish between array and resy types  *)
                  | 0 -> 
                     let par_type = TYPE_ref (TYPE_duck !duckCounter) in             (* Create New Type Variable                  *)
                     ignore (newVariable (id_make id) par_type true pos);            (* Add Mutable to Symbol Table               *)
                     t := Some {tag_tp = Tp_duck !duckCounter; meta_tp = []};        (* Update the AST with the Type Variable     *)
                     treeDucks := t::!treeDucks;                                     (* Add new Type variable to list             *)
                  | n -> 
                     let par_type = TYPE_array (TYPE_duck !duckCounter, n) in        (* Create New Type Variable                  *)
                     ignore (newVariable (id_make id) par_type true pos);            (* Add Mutable to Symbol Table               *)
                     t := Some {tag_tp = Tp_duck !duckCounter; meta_tp = []};        (* Update the AST with the Type Variable     *)
                     treeDucks := t::!treeDucks;                                     (* Add new Type variable to list             *)
                 )
              | Some et ->
                 (match List.length e with                                           (* Distinguish between array and resy types  *)
                  | 0 -> 
                     let par_type = 
                        TYPE_ref (typ_conversion et (Some Ill_ref) (Some udt_env)) in  
                     ignore (newVariable (id_make id) par_type true pos)             (* Add Mutable to Symbol Table               *)
                  | n -> 
                     let par_type = 
                        TYPE_array (typ_conversion et (Some Ill_array) (Some udt_env), n) in
                     ignore (newVariable (id_make id) par_type true pos)             (* Add Mutable to Symbol Table               *)
                 )
             )
           with
           | Exit -> raise (Duplicate_Variable (pos, id))
          )
       )

  (* Co-ordinates the operations needed for handling a new letdef block AND catches all exceptions *)
and handleNewLetDef udt_env letdf =
   try 
      match letdf with
      | (0, defs) -> (* Case of Let     *)
         let handlers = List.map (fun df -> genPass_Def udt_env df) defs in  (* Handle all defs                       *)
         List.iter (fun h -> visibilityOfEntry h true) handlers              (* Restore Visibility to all def entries *)
      | (1, defs) -> (* Case of Let Rec *)
         List.iter (fun df -> genPass_Rec_Def 1 udt_env df) defs;            (* 1st Pass for forward declaration      *)
         List.iter (fun df -> genPass_Rec_Def 0 udt_env df) defs             (* 1nd Pass for handling all defs        *)
      | _ -> 
         iInternal "Illegal Letdef Representation" None
   with
   | IllegalTypeArray msg ->
      let pos = getPosFromTuple3 msg in
      let res = getFromTuple3 msg in
      (match res with
       | Ill_func  -> ifatal "Cannot use Array type as result of a function" (Some pos) 
       | Ill_ref   -> ifatal "Cannot use reference to an Array type" (Some pos) 
       | Ill_array -> ifatal "Cannot use an Array Type of arrays" (Some pos)
      ) 
   | UnboundUDT msg ->
      let pos =  getPosFromTuple3 msg in
      let type_name = getFromTuple3 msg in
      ifatal ("Type " ^ type_name ^ " is Unbound") (Some pos)
   | Duplicate_Parameter (pos, id) ->
      ifatal ("Duplicate Identifier " ^ id ^ " as Parameter") (Some pos)
   | Duplicate_Variable (pos, id) ->
      ifatal ("Duplicate Identifier " ^ id ^ " as Variable") (Some pos)
   | Duplicate_Function (pos, id) ->
      ifatal ("Duplicate Identifier " ^ id ^ " as Function") (Some pos)
   | Unbound_Identifier (pos, id) ->
      ifatal ("Unbound Identifier " ^ id) (Some pos)
   | Not_Function (pos, id) ->
      ifatal ("Identifier " ^ id ^ " is not a function") (Some pos)
   | Function_Mismatch_ParamNo (pos, id, exp, act) ->
      ifatal ("Function " ^ id ^ " has arity of " ^ (string_of_int exp) ^ ", but it is called with " ^ (string_of_int act) ^ " parameter(s)") (Some pos)
   | Unbound_Constructor (pos, id) ->
      ifatal ("Unbound Constructor " ^ id) (Some pos)
   | Constructor_Mismatch_ParamNo (pos, id, exp, act) ->
      ifatal ("Constructor " ^ id ^ " has arity of " ^ (string_of_int exp) ^ ", but it is called with " ^ (string_of_int act) ^ " parameter(s)") (Some pos)
   | Not_Variable (pos, id) ->
      ifatal ("Identifier " ^ id ^ " is not a variable") (Some pos)
   | Illegal_Pattern pos ->
      ifatal ("Illegal Pattern. Pattern should start with a Constructor or a catch all clause") (Some pos)
      
  (* Update the AST Type Nodes with the Inferred Types *)
let rec updateAST_TypeNode node res =
   match !node with
   | None -> 
      iInternal "Type Node is Empty!!" None
   | Some et ->
      (match et.tag_tp with
       | Tp_duck i -> 
          let inf_type = revTypConversion (List.nth res (i-1)) in
          node := Some inf_type
       | _                ->
          iInternal "Expected Duck!!" None
      )
      
  (* Creates a List of all the created Ducks for Type Inference *)
let rec createRes n acc =
   match n with
   | 0 -> acc
   | _ -> let duck = TYPE_duck n in
          createRes (n-1) (duck::acc)
 
(* ********************************************************* *)
(* *** Initialize Symbol Table and Add Library Functions *** *)
(* ********************************************************* *)

  (* Adds Library Functions to the Symbol Table *)
let addLibFunc (func_name, res_type, func_args) =
   let f = newFunction (id_make func_name) true (-1,-1) in
   openScope();
   List.iter (fun (param_name, param_type, param_mode) -> 
                 ignore (newParameter (id_make param_name) param_type param_mode f true (-1, -1))) 
             func_args;
   endFunctionHeader f res_type;
   closeScope()

  (* Wrapper for Initializing Symbol Table and adding Library Functions *)
let initializeSymbolTable () = 
   numScopes := 0;                         (* Initialize open scope counter *)
   initSymbolTable 331999;                 (* Initialize symbol table *)
   openScope();                            (* Open top level scope *)
   List.iter addLibFunc library_functions
   
(* ************************************ *)
(* *** Handle a Letdef / Type Check *** *)
(* ************************************ *)

  (* Check if a type is polymorphic *)
let rec isPolymorphic et = 
   match et with
   | TYPE_duck _        -> true
   | TYPE_ref t         -> isPolymorphic t
   | TYPE_array (t, n)  -> isPolymorphic t
   | TYPE_func (t1, t2) -> (isPolymorphic t1) || (isPolymorphic t2)
   | _                  -> false
   
  (* Check if a type is array dim polymorphic *)
let rec isDimArrayPolymorphic et =
   match et with
   | TYPE_array (t, n)  -> if n < 0 then
                              true
                           else
                              false
   | TYPE_ref t         -> isDimArrayPolymorphic t
   | TYPE_func (t1, t2) -> (isDimArrayPolymorphic t1) || (isDimArrayPolymorphic t2)
   | _                  -> false 
   
  (* Type check an ast_expr_node *)
let rec checkExpr udt_env expr = 
   match expr.tag_ex with
   | E_int i ->
      TYPE_int
   | E_real x ->
      TYPE_float
   | E_char c ->
      TYPE_char
   | E_string s ->
      TYPE_array (TYPE_char, 1)
   | E_bool b ->
      TYPE_bool
   | E_unit ->
      TYPE_unit
   | E_var id ->
      let pos = getPosFromMsg expr.meta_ex "id_name_start" in
      let entry = lookupEntry (id_make id) LOOKUP_ALL_SCOPES true in                    (* Lookup Identifier in the Symbol Table       *)
      expr.entry_ex <- Some entry;                                                      (* Store the Symbol entry in the AST           *)
      (match entry.entry_info with
       | ENTRY_variable vinfo ->                                                        (* If the entry is a variable                  *)
         vinfo.variable_type                                                            (* Return its type                             *)
       | ENTRY_parameter pinfo ->                                                       (* If the entry is a variable                  *)
         pinfo.parameter_type                                                           (* Return its type                             *)
       | ENTRY_function finfo ->                                                        (* If the entry is a function                  *)
         let res_type = finfo.function_result in                                        (* Find its result type                        *)
         let par_types = getListWithParamsTypes finfo.function_paramlist [] in          (* Make a list of its parameters' types        *)
         constructFuncType par_types res_type                                           (* Construct the function's type               *)
       | _ ->  (* If it's not a variable or parameter or function then something has gone wrong *)
         iInternal ("Identifier " ^ id ^ " is not Variable or Parameter or Function") (Some pos);
         raise Terminate
      )
   | E_func (id, elist) ->
      let pos = getPosFromMsg expr.meta_ex "id_name_start" in
      let entry = lookupEntry (id_make id) LOOKUP_ALL_SCOPES true in                    (* Lookup Identifier in the Symbol Table       *)
      expr.entry_ex <- Some entry;                                                      (* Store the Symbol entry in the AST           *)
      (match entry.entry_info with
       | ENTRY_function finfo ->                                                        (* If the entry is indeed a function           *)
          let par_types = getListWithParamsTypes finfo.function_paramlist [] in         (* Get the List of the Parameter Types         *)
          let e_types = List.map (fun e -> checkExpr udt_env e) elist in                (* Get the List of the Actual Parameter Types  *)
          List.iter (fun (a, b) -> 
             if a <> b then raise (TypeInfErr pos)) (List.combine par_types e_types);   (** Validate Type Inference *)
          finfo.function_result                                                         (* Return its result type                      *)
       | ENTRY_parameter pinfo ->                                                       (* If the entry is indeed a function           *)
          let e_types = List.map (fun e -> checkExpr udt_env e) elist in                (* Get the List of the Actual Parameter Types  *)
          let full_type = pinfo.parameter_type in                                       (* Get function full type                      *)
          (match full_type with
           | TYPE_func _ -> 
              let res_type = funcReturnType full_type in
              let ft = constructFuncType e_types res_type in
              if ft <> full_type then raise (TypeInfErr pos);                           (** Validate Type Inference *)
              res_type
           | _                  -> 
              raise (TypeInfErr pos)                                                    (** Validate Type Inference *)
          )
       | _ ->                                                                           (* If it's not a function                      *)
         raise (Not_Function (pos, id))                                                 (* Raise the Not_Function exception            *)
      )
   | E_constr (id, elist) ->
      let pos = getPosFromMsg expr.meta_ex "constr_name_start" in
      let (type_name, tlist) = lookupConstructor udt_env id in                          (* Lookup Constructor in the UDT Table         *)
      let e_types = List.map (fun e -> checkExpr udt_env e) elist in                    (* Get the List of the Actual Parameter Types  *)
      List.iter (fun (a, b) -> 
         if a <> b then raise (TypeInfErr pos)) (List.combine tlist e_types);           (** Validate Type Inference *)
      TYPE_userdef type_name                                                            (* Return the udt as result type               *)
   | E_bang e ->
      let pos = getPosFromMsg expr.meta_ex "bang_start" in
      let e_type = checkExpr udt_env e in                                               (* Get the type of the inner expression        *)
      (match e_type with
       | TYPE_ref t -> t
       | _          -> raise (TypeInfErr pos);                                          (** Validate Type Inference *)
      )
   | E_not e ->
      let pos = getPosFromMsg expr.meta_ex "not_start" in
      let e_type = checkExpr udt_env e in                                               (* Get the type of the inner expression        *)
      if e_type <> TYPE_bool then raise (TypeInfErr pos);                               (** Validate Type Inference *)
      TYPE_bool
   | E_signed (s, e) ->
      let pos = getPosFromMsg expr.meta_ex "op_start" in
      let e_type =  checkExpr udt_env e in                                              (* Get the type of the inner expression        *)
      (match s with
       | S_plus   -> if e_type <> TYPE_int then raise (TypeInfErr pos);                 (** Validate Type Inference *)
                     TYPE_int
       | S_minus  -> if e_type <> TYPE_int then raise (TypeInfErr pos);                 (** Validate Type Inference *)
                     TYPE_int
       | S_fplus  -> if e_type <> TYPE_float then raise (TypeInfErr pos);               (** Validate Type Inference *)
                     TYPE_float
       | S_fminus -> if e_type <> TYPE_float then raise (TypeInfErr pos);               (** Validate Type Inference *)
                     TYPE_float
       | Unsigned -> iInternal "Didn't Expect Unsigned Expression" None;
                     raise Terminate
      )
   | E_binop (e1, bn, e2) ->
      let pos = getPosFromMsg expr.meta_ex "op_start" in
      let e1_type = checkExpr udt_env e1 in                                             (* Get the type of the left inner expression   *)
      let e2_type = checkExpr udt_env e2 in                                             (* Get the type of the right inner expression  *)
      (match bn with
       | B_plus       -> if e1_type <> TYPE_int then raise (TypeInfErr pos);            (** Validate Type Inference *)
                         if e2_type <> TYPE_int then raise (TypeInfErr pos);            (** Validate Type Inference *)
                         TYPE_int
       | B_minus      -> if e1_type <> TYPE_int then raise (TypeInfErr pos);            (** Validate Type Inference *)
                         if e2_type <> TYPE_int then raise (TypeInfErr pos);            (** Validate Type Inference *)
                         TYPE_int
       | B_mult       -> if e1_type <> TYPE_int then raise (TypeInfErr pos);            (** Validate Type Inference *)
                         if e2_type <> TYPE_int then raise (TypeInfErr pos);            (** Validate Type Inference *)
                         TYPE_int
       | B_div        -> if e1_type <> TYPE_int then raise (TypeInfErr pos);            (** Validate Type Inference *)
                         if e2_type <> TYPE_int then raise (TypeInfErr pos);            (** Validate Type Inference *)
                         TYPE_int
       | B_fplus      -> if e1_type <> TYPE_float then raise (TypeInfErr pos);          (** Validate Type Inference *)
                         if e2_type <> TYPE_float then raise (TypeInfErr pos);          (** Validate Type Inference *)
                         TYPE_float
       | B_fminus     -> if e1_type <> TYPE_float then raise (TypeInfErr pos);          (** Validate Type Inference *)
                         if e2_type <> TYPE_float then raise (TypeInfErr pos);          (** Validate Type Inference *)
                         TYPE_float
       | B_fmult      -> if e1_type <> TYPE_float then raise (TypeInfErr pos);          (** Validate Type Inference *)
                         if e2_type <> TYPE_float then raise (TypeInfErr pos);          (** Validate Type Inference *)
                         TYPE_float
       | B_fdiv       -> if e1_type <> TYPE_float then raise (TypeInfErr pos);          (** Validate Type Inference *)
                         if e2_type <> TYPE_float then raise (TypeInfErr pos);          (** Validate Type Inference *)
                         TYPE_float
       | B_mod        -> if e1_type <> TYPE_int then raise (TypeInfErr pos);            (** Validate Type Inference *)
                         if e2_type <> TYPE_int then raise (TypeInfErr pos);            (** Validate Type Inference *)
                         TYPE_int
       | B_pow        -> if e1_type <> TYPE_float then raise (TypeInfErr pos);          (** Validate Type Inference *)
                         if e2_type <> TYPE_float then raise (TypeInfErr pos);          (** Validate Type Inference *)
                         TYPE_float
       | B_assign     -> if e1_type <> e2_type then raise (TypeInfErr pos);             (** Validate Type Inference *)
                         (match e1_type with
                          | TYPE_array _ -> raise (EqIneqArray (pos, "="))
                          | TYPE_func _  -> raise (EqIneqFunc (pos, "="))
                          | _            -> ()
                         );
                         TYPE_bool
       | B_ltgt       -> if e1_type <> e2_type then raise (TypeInfErr pos);             (** Validate Type Inference *)
                         (match e1_type with
                          | TYPE_array _ -> raise (EqIneqArray (pos, "<>"))
                          | TYPE_func _  -> raise (EqIneqFunc (pos, "<>"))
                          | _            -> ()
                         );
                         TYPE_bool
       | B_lt         -> if e1_type <> e2_type then raise (TypeInfErr pos);             (** Validate Type Inference *)
                         (match e1_type with
                          | TYPE_int   -> ()
                          | TYPE_float -> ()
                          | TYPE_char  -> ()
                          | _          -> raise (ComparOp (pos, "<"))
                         );
                         TYPE_bool
       | B_gt         -> if e1_type <> e2_type then raise (TypeInfErr pos);             (** Validate Type Inference *)
                         (match e1_type with
                          | TYPE_int   -> ()
                          | TYPE_float -> ()
                          | TYPE_char  -> ()
                          | _          -> raise (ComparOp (pos, ">"))
                         );
                         TYPE_bool
       | B_lteq       -> if e1_type <> e2_type then raise (TypeInfErr pos);             (** Validate Type Inference *)
                         (match e1_type with
                          | TYPE_int   -> ()
                          | TYPE_float -> ()
                          | TYPE_char  -> ()
                          | _          -> raise (ComparOp (pos, "<="))
                         );
                         TYPE_bool
       | B_gteq       -> if e1_type <> e2_type then raise (TypeInfErr pos);             (** Validate Type Inference *)
                         (match e1_type with
                          | TYPE_int   -> ()
                          | TYPE_float -> ()
                          | TYPE_char  -> ()
                          | _          -> raise (ComparOp (pos, ">="))
                         );
                         TYPE_bool
       | B_eq         -> if e1_type <> e2_type then raise (TypeInfErr pos);             (** Validate Type Inference *)
                         (match e1_type with
                          | TYPE_array _ -> raise (EqIneqArray (pos, "=="))
                          | TYPE_func _  -> raise (EqIneqFunc (pos, "=="))
                          | _            -> ()
                         );
                         TYPE_bool
       | B_neq        -> if e1_type <> e2_type then raise (TypeInfErr pos);             (** Validate Type Inference *)
                         (match e1_type with
                          | TYPE_array _ -> raise (EqIneqArray (pos, "!="))
                          | TYPE_func _  -> raise (EqIneqFunc (pos, "!="))
                          | _            -> ()
                         );
                         TYPE_bool
       | B_conj       -> if e1_type <> TYPE_bool then raise (TypeInfErr pos);           (** Validate Type Inference *)
                         if e2_type <> TYPE_bool then raise (TypeInfErr pos);           (** Validate Type Inference *)
                         TYPE_bool
       | B_disj       -> if e1_type <> TYPE_bool then raise (TypeInfErr pos);           (** Validate Type Inference *)
                         if e2_type <> TYPE_bool then raise (TypeInfErr pos);           (** Validate Type Inference *)
                         TYPE_bool
       | B_semic      -> e2_type
       | B_refassign  -> (match e1_type with
                          | TYPE_ref t -> if t <> e2_type then
                                             raise (TypeInfErr pos)                     (** Validate Type Inference *)
                                          else
                                             TYPE_unit
                          | _          -> raise (TypeInfErr pos)                        (** Validate Type Inference *)
                         )
      )
   | E_array (id, elist) ->
      let pos = getPosFromMsg expr.meta_ex "array_name_start" in
      let entry = lookupEntry (id_make id) LOOKUP_ALL_SCOPES true in
      expr.entry_ex <- Some entry;                                                      (* Store the Symbol entry in the AST           *)
      (match entry.entry_info with
       | ENTRY_variable vinfo ->                                                        (* If the entry is a variable                  *)
         let e_types = List.map (fun e -> checkExpr udt_env e) elist in                 (* Recurse on all the Inner Expressions        *)
         List.iter (fun t -> if t <> TYPE_int then raise (TypeInfErr pos)) e_types;     (** Validate Type Inference *)
         let n = List.length elist in                                                   (* Get the number of actual dimensions         *)
         (match vinfo.variable_type with
          | TYPE_array (tt, i) -> if n <> i then raise (TypeInfErr pos);                (** Validate Type Inference *)
                                  TYPE_ref tt
          | _                  -> raise (TypeInfErr pos)                                (** Validate Type Inference *)
         )
       | ENTRY_parameter pinfo ->                                                       (* If the entry is a parameter                 *)
         let e_types = List.map (fun e -> checkExpr udt_env e) elist in                 (* Recurse on all the Inner Expressions        *)
         List.iter (fun t -> if t <> TYPE_int then raise (TypeInfErr pos)) e_types;     (** Validate Type Inference *)
         let n = List.length elist in                                                   (* Get the number of actual dimensions         *)
         (match pinfo.parameter_type with
          | TYPE_array (tt, i) -> if n <> i then raise (TypeInfErr pos);                (** Validate Type Inference *)
                                  TYPE_ref tt
          | _                  -> raise (TypeInfErr pos)                                (** Validate Type Inference *)
         )
       | _ ->                                                                           (* If it's something else                      *)
         raise (Not_Variable (pos, id))                                                 (* Raise the Not_Variable exception            *)
      )
   | E_dim (il, id) ->
      let pos = getPosFromMsg expr.meta_ex "id_name_start" in
      let entry = lookupEntry (id_make id) LOOKUP_ALL_SCOPES true in
      expr.entry_ex <- Some entry;                                                      (* Store the Symbol entry in the AST           *)
      (match entry.entry_info with
       | ENTRY_variable vinfo ->                                                        (* If the entry is a variable                  *)
         (match vinfo.variable_type with
          | TYPE_array (t, n) -> 
             (match il with
              | []    -> TYPE_int
              | i::tt -> let ipos = getPosFromMsg expr.meta_ex "int_start" in
                if i <= n then
                   TYPE_int
                else
                   raise (OutOfBounds (ipos, id, i, n))                                 (* Access Out Of Bounds                        *)
             )
          | _ -> 
             raise (TypeInfErr pos)                                                     (** Validate Type Inference *)
         )
       | ENTRY_parameter pinfo ->                                                       (* If the entry is a parameter                 *)
         (match pinfo.parameter_type with
          | TYPE_array (t, n) -> 
             (match il with
              | []    -> TYPE_int
              | i::tt -> let ipos = getPosFromMsg expr.meta_ex "int_start" in
                if i <= n then
                   TYPE_int
                else
                   raise (OutOfBounds (ipos, id, i, n))                                 (* Access Out Of Bounds                        *)
             )
          | _ -> 
             raise (TypeInfErr pos)                                                     (** Validate Type Inference *)
         )
       | _ ->                                                                           (* If it's something else                      *)
         raise (Not_Variable (pos, id))                                                 (* Raise the Not_Variable exception            *)
      )
   | E_new et ->
      let et_type = typ_conversion et (Some Ill_ref) (Some udt_env) in                  (* Get the type of et                          *)
      TYPE_ref et_type                                                                  (* Return a reference to et                    *)
   | E_del e ->
      let pos = getPosFromMsg expr.meta_ex "del_start" in
      let e_type = checkExpr udt_env e in                                               (* Get the type of the Inner Expression        *)
      (match e_type with
       | TYPE_ref t -> TYPE_unit
       | _          -> raise (TypeInfErr pos)                                           (** Validate Type Inference *)
      )
   | E_in (lt, e) ->
      openScope ();                                                                     (* Open Letdef's Scope                         *)
      checkNewLetdef udt_env lt.tag_lt;                                                 (* Handle the Letdef                           *)
      let e_type = checkExpr udt_env e in                                               (* Get the type of the Inner Expression        *)
      closeScope ();                                                                    (* Close Letdef's Scope                        *)
      e_type                                                                            (* Return the type of the Inner Expression     *)
   | E_begin e ->
      checkExpr udt_env e                                                               (* Just do the work for the Inner Expression   *)
   | E_if (e, e1) ->
      let pos = getPosFromMsg expr.meta_ex "if_start" in
      let e_type = checkExpr udt_env e in                                               (* Get the type of the Condition Expression    *)
      let e1_type = checkExpr udt_env e1 in                                             (* Get the type of the True Expression         *)
      if e_type <> TYPE_bool then raise (TypeInfErr pos);                               (** Validate Type Inference *)
      if e1_type <> TYPE_unit then raise (TypeInfErr pos);                              (** Validate Type Inference *)
      TYPE_unit                                                                         (* Return the type of the true Expression      *)
   | E_ifelse (e, e1, e2) ->
      let pos = getPosFromMsg expr.meta_ex "if_start" in
      let e_type = checkExpr udt_env e in                                               (* Get the type of the Condition Expression    *)
      let e1_type = checkExpr udt_env e1 in                                             (* Get the type of the True Expression         *)
      let e2_type = checkExpr udt_env e2 in                                             (* Get the type of the False Expression        *)
      if e_type <> TYPE_bool then raise (TypeInfErr pos);                               (** Validate Type Inference *)
      if e1_type <> e2_type then raise (TypeInfErr pos);                                (** Validate Type Inference *)
      e1_type
   | E_while (e, e1) ->
      let pos = getPosFromMsg expr.meta_ex "while_start" in
      let e_type = checkExpr udt_env e in                                               (* Get the type of the Condition Expression    *)
      let e1_type = checkExpr udt_env e1 in                                             (* Get the type of the True Expression         *)
      if e_type <> TYPE_bool then raise (TypeInfErr pos);                               (** Validate Type Inference *)
      if e1_type <> TYPE_unit then raise (TypeInfErr pos);                              (** Validate Type Inference *)
      TYPE_unit                                                                         (* Return Unit as type                         *)
   | E_for (id, e1, lt, e2, e) ->
      let pos = getPosFromMsg expr.meta_ex "id_name_start" in
      openScope ();                                                                     (* Open the Scope for the Counter Var          *)
      let var = newVariable (id_make id) TYPE_int true pos in                           (* Add the Counter Var to the Symbol Table     *)
      expr.entry_ex <- Some var;                                                        (* Store the Symbol entry in the AST           *)
      let e1_type = checkExpr udt_env e1 in                                             (* Get the type of the Start Expression        *)
      let e2_type = checkExpr udt_env e2 in                                             (* Get the type of the End Expression          *)
      let e_type = checkExpr udt_env e in                                               (* Get the type of the Inner Expression        *)
      if e1_type <> TYPE_int then raise (TypeInfErr pos);                               (** Validate Type Inference *)
      if e2_type <> TYPE_int then raise (TypeInfErr pos);                               (** Validate Type Inference *)
      if e_type <> TYPE_unit then raise (TypeInfErr pos);                               (** Validate Type Inference *)
      closeScope ();                                                                    (* Close the Scope for the Counter Var         *)
      TYPE_unit                                                                         (* Return Unit as type                         *)
   | E_match (e, clList) ->
      let pos = getPosFromMsg expr.meta_ex "match_start" in
      let e_type = checkExpr udt_env e in                                               (* Get the type of the Inner Expression        *) 
      let (cl_types, cl_cnames) = 
         List.split (List.map (fun cl -> checkClause udt_env e_type cl) clList) in      (* Recurse on all clauses providing e_type     *)
      let match_type = List.hd cl_types in
      expr.matchType_ex <- match_type;                                                  (* Store the match type in the AST             *)
      if not (List.for_all (fun t -> t = match_type) cl_types) then
         raise (TypeInfErr pos);                                                        (** Validate Type Inference *)
      (match e_type with
       | TYPE_userdef id ->
          let udt_structure = lookupType udt_env id in                                  (* Get the structure of the UDT                *)
          let (cnames, tlists) = List.split udt_structure in                            (* Get all the Constructor names               *)
          let unused = List.filter (fun x -> not (List.mem x cl_cnames)) cnames in      (* Find all the unmatched Constructors         *)
          if (List.length unused) <> 0 && not (List.mem "all" cl_cnames) then           (* Condition for non-exhaustive match          *)
             iwarning ("Non-Exhaustive match detected\n Example of unused Construct : " ^ (List.hd unused)) (Some pos)
          else
             ()
       | _               -> 
          iInternal "Expected to match User Defined Type" None
      );
      match_type

  (* Type checks an ast_clause_node *)
and checkClause udt_env common_pat_type cl = 
   match cl.tag_cl with
   | (pat, e) ->
      openScope ();                                                                     (* Open the Scope for the pattern              *)
      let (pat_type, cname) = checkPat udt_env pat in                                   (* Get the type of the pattern                 *)
      let pos = getPosFromMsg cl.meta_cl "pat_name_start" in
      if common_pat_type <> pat_type then raise (TypeInfErr pos);                       (** Validate Type Inference *)
      let e_type = checkExpr udt_env e in                                               (* Get the type of the expression              *)
      closeScope ();                                                                    (* Close the Scope of the pattern              *)
      (e_type, cname)
      
  (* Type checks an ast_pattern_node *)
and checkPat udt_env pat =
   let pos = getPosFromMsg pat.meta_pt "pat_name_start" in
   match pat.tag_pt with
   | P_int (sgn, i) ->
      (TYPE_int, "")
   | P_real (sgn, x) ->
      (TYPE_float, "")
   | P_char c ->
      (TYPE_char, "")
   | P_bool b ->
      (TYPE_bool, "")
   | P_id id ->
      (match !(id.ptype) with
       | None -> 
         iInternal "Failed to add type node in 1st Pass" (Some pos);                    (* AST should have type info                   *)
         raise Terminate
       | Some et ->
          let var_type = typ_conversion et None (Some udt_env) in
          let var = newVariable (id_make id.pname) var_type true pos in
          id.pentry <- Some var;                                                        (* Store the Symbol Entry in the AST           *)
          (var_type, "all")
      )
   | P_constr (id, patList) ->
      let (type_name, tlist) = lookupConstructor udt_env id in                          (* Lookup Constructor in the UDT Table         *)
      let (p_types, _) = 
         List.split (List.map (fun p -> checkPat udt_env p) patList) in                 (* Get the List of the Actual Parameter Types  *)
      List.iter (fun (a, b) -> 
         if a <> b then raise (TypeInfErr pos)) (List.combine tlist p_types);           (** Validate Type Inference *)
      (TYPE_userdef type_name, id)                                                      (* Return the udt as result type               *)
      
  (* Type checks an ast_par_node *)
and checkPar udt_env par func =
   match par.tag_pr with
   | (id, t, en) ->
      let pos = getPosFromMsg par.meta_pr "par_name_start" in                           (* Get Position Info of Parameter              *)
      (match !t with
       | None -> 
          iInternal "Failed to add type node in 1st Pass" (Some pos);                   (* AST should have type info                   *)
          raise Terminate
       | Some et ->
          let par_type = typ_conversion et None (Some udt_env) in                       (* Read the type annotation from the AST       *)
          if isPolymorphic par_type then                                                (* If it's a Polymorphic Type                  *)
             raise (Polymorphic_Type (pos, id, par_type));                              (* raise exception                             *)
          if isDimArrayPolymorphic par_type then                                        (* If it's an array with Polymorphic Dims      *)
             raise (Polymorphic_Array_Dim (pos, id));                                   (* raise exception                             *)
          let param = newParameter (id_make id) par_type PASS_BY_VALUE func true pos in (* Add Parameter to Symbol Table               *)
          en := Some param;                                                             (* Store the Symbol Entry in the AST           *)
          par_type
      )

  (* Type Checks an ast_def_now with Let *)
and checkDef udt_env df =  (* Will ultimately return the Func / Var so that checkNewLetdef makes it visible *)
   match df.tag_df with
   | Def_func (id, [], t, e) ->  (* Case of Variable *)
      let pos = getPosFromMsg df.meta_df "id_name_start" in                             (* Get Variable Position Info                  *)
      (match !t with
       | None ->
          iInternal "Failed to add type node in 1st Pass" (Some pos);                   (* AST should have type info                   *)
          raise Terminate
       | Some et ->
          let var_type = typ_conversion et None (Some udt_env) in                       (* Read the type annotation from the AST       *)
          (match var_type with
           | TYPE_func _ -> raise (VClosure (pos, id, var_type))                        (* If it's a Closure, raise exception          *)
           | _           -> if isPolymorphic var_type then                              (* If it's a Polymorphic Type                  *)
                               raise (Polymorphic_Type (pos, id, var_type));            (* raise exception                             *)
                            if isDimArrayPolymorphic var_type then                      (* If it's an array with Polymorphic Dims      *)
                               raise (Polymorphic_Array_Dim (pos, id))                  (* raise exception                             *)
          );
          let var = newVariable (id_make id) var_type true pos in                       (* Add Variable to Symbol Table                *)
          df.entry_df <- Some var;                                                      (* Store the Symbol Entry in the AST           *)
          visibilityOfEntry var false;                                                  (* Make entry invisible                        *)
          openScope ();                                                                 (* Open the scope of the Inner Expression      *)
          let e_type = checkExpr udt_env e in                                           (* Check the Inner Expression                  *)
          df.scope_df <- Some !currentScope;                                                 (* Store the current Scope info                *)
          closeScope ();                                                                (* Close the scope of the Inner Expression     *)
          if e_type <> var_type then raise (TypeInfErr pos);                            (** Validate Type Inference *)
          var                                                                           (* Return the Symbol Entry                     *)
      )
   | Def_func (id, parList, t, e) ->  (* Case of function *)
      let pos = getPosFromMsg df.meta_df "id_name_start" in                             (* Get Function Position Info                  *)
      (match !t with
       | None ->
          iInternal "Failed to add type node in 1st Pass" (Some pos);                   (* AST should have type info                   *)
          raise Terminate
       | Some et ->
          let fun_type = typ_conversion et (Some Ill_func) (Some udt_env) in            (* Get Result Type that is stored in the AST   *)
          (match fun_type with
           | TYPE_func _  -> raise (FClosure (pos, id, fun_type))                       (* If it's a Closure, raise exception          *)
           | TYPE_array _ -> raise (RetArray (pos, id))                                 (* If it returns an Array, raise exception     *)
           | _            -> ()
          );
          let func = newFunction (id_make id) true pos in                               (* Definition of function                      *)
          df.entry_df <- Some func;                                                     (* Store the Symbol Entry in the AST           *)
          visibilityOfEntry func false;                                                 (* Make entry invisible                        *)
          openScope();                                                                  (* Open Inner Scope                            *)
          let par_types = List.map (fun par -> checkPar udt_env par func) parList in    (* Process Function Parameters                 *)
          let full_type = constructFuncType par_types fun_type in                       (* Construct function's full type              *)
          if isPolymorphic full_type then                                               (* If it's a Polymorphic Type                  *)
             raise (Polymorphic_Type (pos, id, full_type));                             (* raise an exception                          *)
          if isDimArrayPolymorphic full_type then                                       (* If it has an array with Polymorphic Dims    *)
             raise (Polymorphic_Array_Dim (pos, id));                                   (* raise an exception                          *)
          endFunctionHeader func fun_type;                                              (* Add Function's Result Type                  *)
          let expr_type = checkExpr udt_env e in                                        (* Get the type of the Inner Expression        *)
          if expr_type <> fun_type then raise (TypeInfErr pos);                         (** Validate Type Inference *)
          df.scope_df <- Some !currentScope;                                                 (* Store the current Scope info                *)
          closeScope();                                                                 (* Close Inner Scope                           *)
          func                                                                          (* Return the Function entry                   *)
      )
   | Def_mut (id, e, t) ->  (* Case of mutable *)
      let pos = getPosFromMsg df.meta_df "id_name_start" in                             (* Get Mutable Position Info                   *)
      (match !t with
       | None ->
          iInternal "Failed to add type node in 1st Pass" (Some pos);                   (* AST should have type info                   *)
          raise Terminate
       | Some et ->
          (match List.length e with                                                     (* Distinguish between array and ref types     *)
           | 0 -> 
              let var_type = 
                 TYPE_ref (typ_conversion et (Some Ill_ref) (Some udt_env)) in          (* Convert Type                                *)
              if isPolymorphic var_type then                                            (* If it's a Polymorphic Type                  *)
                 raise (Polymorphic_Type (pos, id, var_type));                          (* raise an exception                          *)
              if isDimArrayPolymorphic var_type then                                    (* If it has an array with Polymorphic Dims    *)
                 raise (Polymorphic_Array_Dim (pos, id));                               (* raise an exception                          *)
              let var = newVariable (id_make id) var_type true pos in                   (* Add Mutable to Symbol Table                 *)
              df.entry_df <- Some var;                                                  (* Store the Symbol Entry in the AST           *)
              df.scope_df <- Some !currentScope;                                        (* Store the current Scope info                *)
              visibilityOfEntry var false;                                              (* Hide the entry                              *)
              var                                                                       (* Return the Variable Entry                   *)
           | n -> 
              let var_type = 
                 TYPE_array (typ_conversion et (Some Ill_array) (Some udt_env), n) in   (* Convert Type                                *)
              if isPolymorphic var_type then                                            (* If it's a Polymorphic Type                  *)
                 raise (Polymorphic_Type (pos, id, var_type));                          (* raise an exception                          *)
              if isDimArrayPolymorphic var_type then                                    (* If it has an array with Polymorphic Dims    *)
                 raise (Polymorphic_Array_Dim (pos, id));                               (* raise an exception                          *)
              let var = newVariable (id_make id) var_type true pos in                   (* Add Mutable to Symbol Table                 *)
              df.entry_df <- Some var;                                                  (* Store the Symbol Entry in the AST           *)
              df.scope_df <- Some !currentScope;                                        (* Store the current Scope info                *)
              visibilityOfEntry var false;                                              (* Hide the entry                              *)
              let etypes = List.map (fun ex -> checkExpr udt_env ex) e in               (* Get the List of types of the Inner Exprs    *)
              List.iter (fun t -> if t <> TYPE_int then raise (TypeInfErr pos)) etypes; (** Validate Type Inference *)
              var                                                                       (* Return the Variable Entry                   *)
          )
      )
      
  (* Type Checks an ast_def_now with Let Rec *)
and checkRec_Def mode udt_env df = 
   match df.tag_df with
   | Def_func (id, [], t, e) ->  (* Case of Variable *)
      let pos = getPosFromMsg df.meta_df "id_name_start" in                             (* Get Variable Position Info                  *)
      (match mode with
       | 0 ->  (* 2nd Pass *)
          let entry = lookupEntry (id_make id) LOOKUP_ALL_SCOPES true in                (* Lookup Entry                                *)
          (match entry.entry_info with
           | ENTRY_variable vinfo ->
              let var_type = vinfo.variable_type in                                     (* Get the type of the variable                *)
              openScope ();                                                             (* Open Inner Scope                            *)
              let e_type = checkExpr udt_env e in                                       (* Get the type of the Inner Expression        *)
              df.scope_df <- Some !currentScope;                                        (* Store the current Scope info                *)
              closeScope ();                                                            (* Close Inner Scope                           *)
              if e_type <> var_type then raise (TypeInfErr pos)                         (** Validate Type Inference *)
           | _ ->
              iInternal "Forward Pass added entry but it's not a Variable" (Some pos)
          )
       | _ ->  (* 1st Pass *)
          (match !t with
           | None ->
              iInternal "Failed to add type node in 1st Pass" (Some pos);               (* AST should have type info                   *)
              raise Terminate
           | Some et ->
              let var_type = typ_conversion et None (Some udt_env) in                   (* Read the type annotation from the AST       *)
              (match var_type with
               | TYPE_func _ -> raise (VClosure (pos, id, var_type))                    (* If it's a Closure, raise exception          *)
               | _           -> if isPolymorphic var_type then                          (* If it's a Polymorphic Type                  *)
                                   raise (Polymorphic_Type (pos, id, var_type));        (* raise exception                             *)
                                if isDimArrayPolymorphic var_type then                  (* If it's an array with Polymorphic Dims      *)
                                   raise (Polymorphic_Array_Dim (pos, id))              (* raise exception                             *)
              );
              let var = newVariable (id_make id) var_type true pos in                   (* Add Variable to Symbol Table                *)
              df.entry_df <- Some var                                                   (* Store the Symbol Entry in the AST           *)
          )
      )
   | Def_func (id, parList, t, e) ->  (* Case of function *)
      let pos = getPosFromMsg df.meta_df "id_name_start" in                             (* Get Function Position Info                  *)
      (match mode with
       | 0 ->  (* 2nd Pass - Don't expect Exit exception for newFunction since it was caught on 1st Pass *)
          (match !t with
           | None -> 
             iInternal "Failed to add Function Result Type on 1st Pass for Forward Definitions" None
           | Some et ->
             let fun_type = typ_conversion et (Some Ill_func) (Some udt_env) in         (* Get Result Type that is stored in the AST   *)
             let func = newFunction (id_make id) true pos in                            (* Definition of function                      *)
             openScope();                                                               (* Open Inner Scope                            *)
             ignore (List.map (fun p -> checkPar udt_env p func) parList);              (* Process Function Parameters                 *)
             endFunctionHeader func fun_type;                                           (* Add Function's Result Type                  *)
             df.entry_df <- Some func;                                                  (* Store the Symbol Entry in the AST           *)
             let e_type = checkExpr udt_env e in                                        (* Get the type of the Inner Expression        *)
             if e_type <> fun_type then raise (TypeInfErr pos);                         (** Validate Type Inference *)
             df.scope_df <- Some !currentScope;                                         (* Store the current Scope info                *)
             closeScope()                                                               (* Close Inner Scope                           *)
          )
       | _ -> (* 1st Pass *)
          (match !t with
           | None ->
              iInternal "Failed to add type node in 1st Pass" (Some pos)                (* AST should have type info                   *)
           | Some et ->
              let fun_type = typ_conversion et (Some Ill_func) (Some udt_env) in        (* Read the type annotation from the AST       *)
              (match fun_type with
               | TYPE_func _  -> raise (FClosure (pos, id, fun_type))                   (* If it's a Closure, raise exception          *)
               | TYPE_array _ -> raise (RetArray (pos, id))                             (* If it returns an Array, raise exception     *)
               | _            -> ()
              );
              let func = newFunction (id_make id) true pos in                           (* Add Function to Symbol Table                *)
              forwardFunction func;                                                     (* Declare this is a forward definition        *)
              openScope();                                                              (* Open Inner Scope                            *)
              let par_types = List.map (fun p -> checkPar udt_env p func) parList in    (* Process Function Parameters                 *)
              endFunctionHeader func fun_type;                                          (* Add Function's Result Type                  *)
              closeScope();                                                             (* Close Inner Scope                           *)
              let full_type = constructFuncType par_types fun_type in                   (* Construct function's full type              *)
              if isPolymorphic full_type then                                           (* If it's a Polymorphic Type                  *)
                raise (Polymorphic_Type (pos, id, full_type));                          (* raise an exception                          *)
              if isDimArrayPolymorphic full_type then                                   (* If it has an array with Polymorphic Dims    *)
                raise (Polymorphic_Array_Dim (pos, id))                                 (* raise an exception                          *)
          )
      )
   | Def_mut (id, e, t) ->  (* Case of mutable *)
      let pos = getPosFromMsg df.meta_df "id_name_start" in                             (* Get Mutable Position Info                   *)
      (match mode with
       | 0 -> (* 2nd Pass *)
          let e_types = List.map (fun ex -> checkExpr udt_env ex) e in                  (* Get the types of the Inner Expressions      *)
          df.scope_df <- Some !currentScope;                                            (* Store the current Scope info                *)
          List.iter (fun t -> if t <> TYPE_int then raise (TypeInfErr pos)) e_types;    (** Validate Type Inference *)
       | _ -> (* 1st Pass *)
          (match !t with
           | None ->
              iInternal "Failed to add type node in 1st Pass" (Some pos)                (* AST should have type info                   *)
           | Some et ->
              (match List.length e with                                                 (* Distinguish between array and ref types     *)
               | 0 ->
                  let var_type = 
                     TYPE_ref (typ_conversion et (Some Ill_ref) (Some udt_env)) in
                  if isPolymorphic var_type then                                        (* If it's a Polymorphic Type                  *)
                     raise (Polymorphic_Type (pos, id, var_type));                      (* raise an exception                          *)
                  if isDimArrayPolymorphic var_type then                                (* If it has an array with Polymorphic Dims    *)
                     raise (Polymorphic_Array_Dim (pos, id));                           (* raise an exception                          *)
                  let var = newVariable (id_make id) var_type true pos in               (* Add Mutable to Symbol Table                 *)
                  df.entry_df <- Some var                                               (* Store Symbol Entry in the AST               *)
               | n ->
                  let var_type = 
                     TYPE_array (typ_conversion et (Some Ill_array) (Some udt_env), n) in
                  if isPolymorphic var_type then                                        (* If it's a Polymorphic Type                  *)
                     raise (Polymorphic_Type (pos, id, var_type));                      (* raise an exception                          *)
                  if isDimArrayPolymorphic var_type then                                (* If it has an array with Polymorphic Dims    *)
                     raise (Polymorphic_Array_Dim (pos, id));                           (* raise an exception                          *)
                  let var = newVariable (id_make id) var_type true pos in               (* Add Mutable to Symbol Table                 *)
                  df.entry_df <- Some var                                               (* Store Symbol Entry in the AST               *)
              )
          )
      )
   
  (* Type Checks an ast_letdef *)
and checkNewLetdef udt_env letdf = 
   try 
      match letdf with
      | (0, defs) -> (* Case of Let     *)
         let handlers = List.map (fun df -> checkDef udt_env df) defs in                (* Handle all defs                             *)
         List.iter (fun h -> visibilityOfEntry h true) handlers                         (* Restore Visibility to all def entries       *)
      | (1, defs) -> (* Case of Let Rec *)
         List.iter (fun df -> checkRec_Def 1 udt_env df) defs;                          (* 1st Pass for forward declaration            *)
         List.iter (fun df -> checkRec_Def 0 udt_env df) defs                           (* 1nd Pass for handling all defs              *)
      | _ -> 
         iInternal "Illegal Letdef Representation" None
   with
   | Polymorphic_Type (pos, id, var_type) ->
      let typ = print_to_string "%a" pprint_typ var_type in
      ifatal ("Identifier " ^ id ^ " has polymorphic type\n  Type : " ^ typ) (Some pos)
   | VClosure (pos, id, var_type) ->
      let typ = print_to_string "%a" pprint_typ var_type in
      ifatal ("Illegal Closure. Variable " ^ id ^ " has function type.\n  Type : " ^ typ) (Some pos)
   | FClosure (pos, id, var_type) ->
      let typ = print_to_string "%a" pprint_typ var_type in
      ifatal ("Illegal Closure. Function " ^ id ^ " returns a function.\n  Return Type : " ^ typ) (Some pos)
   | RetArray (pos, id) ->
      ifatal ("Illegal Function Return Type. Function " ^ id ^ " returns an Array") (Some pos)
   | EqIneqArray (pos, op) ->
      ifatal ("Type Mismatch. Both operands of " ^ op ^ " must not be of type array") (Some pos)
   | EqIneqFunc (pos, op) ->
      ifatal ("Type Mismatch. Both operands of " ^ op ^ " must not be of type function") (Some pos)
   | ComparOp (pos, op) ->
      ifatal ("Type Mismatch. Both operands of " ^ op ^ " must be either of type int, float or char") (Some pos)
   | OutOfBounds (pos, id, i, n) ->
      ifatal ("Out Of Array Bounds.\n  Array " ^ id ^ " has " ^ (string_of_int n) ^ " dimensions.\n  You tried to access the " ^ (string_of_int i) ^ "th dimension") (Some pos)
   | TypeInfErr pos ->
      iInternal ("Type Inference Validation Failed") (Some pos)

(* ***************************************** *)
(* *** Coordinate Typechecker operations *** *)
(* ***************************************** *)

  (* Semantic Analysis of the AST Tree *)
let semanticAnalysis udt_env ast = 
   try 
      (match ast with
       | None ->
         iInternal "Failed to Store AST in ast_tree!" None
       | Some tree when tree.tag_pg = [] ->
         iwarning "Trivial Case\n  Empty Program" (Some (1,1))
       | Some tree ->
         let chooseModeP1 block_node = 
            (match block_node.tag_bl with
             | Letdef node  ->
                openScope();                                     (* Open Scope for new Letdef                *)
                incr numScopes;                                  (* Increase open scope counter              *)
                handleNewLetDef udt_env node.tag_lt              (* Handle the Letdef / Generate Constraints *)
             | Typedef node ->
                handleNewTypedef udt_env node.tag_pd             (* Handle the Typedef / Update UDT Table    *)
            )
         in let chooseModeP2 block_node =
            (match block_node.tag_bl with
             | Letdef node  ->
                openScope();                                     (* Open Scope for new Letdef                *)
                incr numScopes;                                  (* Increase open scope counter              *)
                checkNewLetdef udt_env node.tag_lt               (* Type Check the Letdef                    *)
             | Typedef node ->
                ()                                               (* Ignore Typedef since UDT Table is ready  *)
            )
         in initializeSymbolTable();                             (* Initialize the Symbol Table for 1st Pass *)
         List.iter chooseModeP1 tree.tag_pg;                     (* 1st Pass of the AST                      *)
         debug_symbolTable();                                    (* Print the top level scope                *)
         for i = 1 to !numScopes do closeScope() done;           (* Close all Letdefs' Scopes                *)
         closeScope();                                           (* Close the top level scope                *)
         debug_udtTable udt_env;                                 (* Print the contents of the UDT table      *)
         debug_CST ();                                           (* Print List of generated Constraints      *)
         debug_typedAST ast;                                     (* Print Typed AST with ducks               *)
         let allDucks = createRes !duckCounter [] in             (* Make a list of all the used ducks        *)
         let inferredTypes = unify !cst [] [] allDucks in        (* Get Types from Type Inference            *)
         List.iter (fun node -> 
             updateAST_TypeNode node inferredTypes) !treeDucks;
         debug_typedAST ast;                                     (* Print Typed AST                          *)
         debug_TypeInf inferredTypes;                            (* Print the result of the Type Inference   *)
         initializeSymbolTable();                                (* Initialize the Symbol Table for 2nd Pass *)
         List.iter chooseModeP2 tree.tag_pg;                     (* 2nd Pass of the AST                      *)
         debug_symbolTable();                                    (* Print the top level scope                *)
         for i = 1 to !numScopes do closeScope() done;           (* Close all Letdefs' Scopes                *)
         closeScope()                                            (* Close the top level scope                *)
      )
   with
   | Unify_Fail (et1, et2, pos) ->
      let t1 = print_to_string "%a" pprint_typ et1 in
      let t2 = print_to_string "%a" pprint_typ et2 in
      ifatal ("Unification Error\n  Cannot Unify " ^ t1 ^ " with " ^ t2) (Some pos)
