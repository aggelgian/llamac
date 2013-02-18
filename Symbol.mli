(* Symbol table *)

type pass_mode = PASS_BY_VALUE | PASS_BY_REFERENCE

type param_status =
  | PARDEF_COMPLETE                             (* ������ �������     *)
  | PARDEF_DEFINE                               (* �� ���� �������    *)
  | PARDEF_CHECK                                (* �� ���� �������    *)

type scope = {
  sco_parent : scope option;
  sco_nesting : int;
  mutable sco_entries : entry list;
  mutable sco_negofs : int
}

and variable_info = {                         (******* ��������� *******)
  variable_type    : Types.typ;               (* �����                 *)
  variable_offset  : int;                     (* Offset ��� �.�.       *)
  mutable variable_visible : bool;   
  variable_decl_pos : int * int     
}

and function_info = {                         (******* ��������� *******)
  mutable function_isForward : bool;          (* ������ forward        *)
  mutable function_paramlist : entry list;    (* ����� ����������      *)
  mutable function_redeflist : entry list;    (* ����� ���������� (2�) *)
  mutable function_result    : Types.typ;     (* ����� �������������   *)
  mutable function_pstatus   : param_status;  (* ��������� ����������  *)
  mutable function_decl_pos  : int * int;     (* Position Info *)
  mutable function_visible   : bool;          (* Visibility of function on lookup *)
  mutable function_initquad  : int            (* ������ �������        *)
}

and parameter_info = {                        (****** ���������� *******)
  parameter_type           : Types.typ;       (* �����                 *)
  mutable parameter_offset : int;             (* Offset ��� �.�.       *)
  parameter_mode           : pass_mode;       (* ������ ����������     *)
  parameter_decl_pos       : int * int 
}

and temporary_info = {                        (** ��������� ��������� **)
  temporary_type   : Types.typ;               (* �����                 *)
  temporary_offset : int                      (* Offset ��� �.�.       *)
}

and entry_info = ENTRY_none
               | ENTRY_variable of variable_info
               | ENTRY_function of function_info
               | ENTRY_parameter of parameter_info
               | ENTRY_temporary of temporary_info

and entry = {
  entry_id    : Identifier.id;
  entry_scope : scope;
  entry_info  : entry_info
}

exception Unknown_Identifier

type lookup_type = LOOKUP_CURRENT_SCOPE | LOOKUP_ALL_SCOPES

val currentScope : scope ref              (* �������� ��������         *)
val quadNext : int ref                    (* ������� �������� �������� *)
val tempNumber : int ref                  (* �������� ��� temporaries  *)

val initSymbolTable  : int -> unit
val openScope        : unit -> unit
val closeScope       : unit -> unit
  (* Params : Var Name, Var Type, Show Errors, Position in File *)
val newVariable      : Identifier.id -> Types.typ -> bool -> int * int -> entry
  (* Params: Func Name, Show Errors, Position in File *)
val newFunction      : Identifier.id -> bool -> int * int -> entry
  (* Params: Param Name, Param Type, Param Pass Mode, Func, Show Errors, Position in File *)
val newParameter     : Identifier.id -> Types.typ -> pass_mode ->
                                        entry -> bool -> int * int -> entry
val newTemporary     : Types.typ -> scope -> entry

val forwardFunction   : entry -> unit
val endFunctionHeader : entry -> Types.typ -> unit
val lookupEntry       : Identifier.id -> lookup_type -> bool -> entry

val start_positive_offset : int   (* ������ ������ offset ��� �.�.   *)
val start_negative_offset : int   (* ������ �������� offset ��� �.�. *)

(* ***** *)

val printSymbolTable  : unit -> unit
  (* Show / Hide a Func / Var from lookup in the Symbol Table *)
val visibilityOfEntry : entry -> bool -> unit
