open Format

open Identifier
open Error
open Types

module H = Hashtbl.Make (
  struct
    type t = id
    let equal = (==)
    let hash = Hashtbl.hash
  end
)

type pass_mode = PASS_BY_VALUE | PASS_BY_REFERENCE

type param_status =
  | PARDEF_COMPLETE
  | PARDEF_DEFINE
  | PARDEF_CHECK

type scope = {
  sco_parent : scope option;
  sco_nesting : int;
  mutable sco_entries : entry list;
  mutable sco_negofs : int
}

and variable_info = {
  variable_type    : Types.typ;
  variable_offset  : int;
  mutable variable_visible : bool;   (* Visibility of variable on lookup *)
  variable_decl_pos : int * int      (* Position in File *)
}

and function_info = {
  mutable function_isForward : bool;
  mutable function_paramlist : entry list;
  mutable function_redeflist : entry list;
  mutable function_result    : Types.typ;
  mutable function_pstatus   : param_status;
  mutable function_decl_pos  : int * int;    (* Function declaration's position info *)
  mutable function_visible   : bool;         (* Visibility of function on lookup *)
  mutable function_initquad  : int
}

and parameter_info = {
  parameter_type           : Types.typ;
  mutable parameter_offset : int;
  parameter_mode           : pass_mode;
  parameter_decl_pos       : int * int    (* Position in file *)
}

and temporary_info = {
  temporary_type   : Types.typ;
  temporary_offset : int
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

type lookup_type = LOOKUP_CURRENT_SCOPE | LOOKUP_ALL_SCOPES

let start_positive_offset = 8
let start_negative_offset = 0

let the_outer_scope = {
  sco_parent = None;
  sco_nesting = 0;
  sco_entries = [];
  sco_negofs = start_negative_offset
}

let no_entry id = {
  entry_id = id;
  entry_scope = the_outer_scope;
  entry_info = ENTRY_none
}

let currentScope = ref the_outer_scope
let quadNext = ref 1
let tempNumber = ref 1

let tab = ref (H.create 0)

let initSymbolTable size =
   tab := H.create size;
   currentScope := the_outer_scope

let openScope () =
  let sco = {
    sco_parent = Some !currentScope;
    sco_nesting = !currentScope.sco_nesting + 1;
    sco_entries = [];
    sco_negofs = start_negative_offset
  } in
  currentScope := sco

let closeScope () =
  let sco = !currentScope in
  let manyentry e = H.remove !tab e.entry_id in
  List.iter manyentry sco.sco_entries;
  match sco.sco_parent with
  | Some scp ->
      currentScope := scp
  | None ->
      internal "cannot close the outer scope!"

exception Failure_NewEntry of entry
exception Unknown_Identifier

let newEntry id inf err =
  try
    if err then begin
      try
        let e = H.find !tab id in
        if e.entry_scope.sco_nesting = !currentScope.sco_nesting then
           raise (Failure_NewEntry e)
      with Not_found ->
        ()
    end;
    let e = {
      entry_id = id;
      entry_scope = !currentScope;
      entry_info = inf
    } in
    H.add !tab id e;
    !currentScope.sco_entries <- e :: !currentScope.sco_entries;
    e
  with Failure_NewEntry e ->
    (*error "duplicate Iidentifier %a" pretty_id id;
    e*)raise Exit
    
let rec findMostCurrInList l = (* added *)
  match l with
  | [] ->
     raise Not_found
  | e::t ->
     (match e.entry_info with
      | ENTRY_function f -> if f.function_visible then e else findMostCurrInList t
      | ENTRY_variable v -> if v.variable_visible then e else findMostCurrInList t
      | _ -> e)

let lookupEntry id how err =
  let scc = !currentScope in
  let lookup () =
    match how with
    | LOOKUP_CURRENT_SCOPE ->
        let e = H.find !tab id in
        if e.entry_scope.sco_nesting = scc.sco_nesting then
          e
        else
          raise Not_found
    | LOOKUP_ALL_SCOPES ->
        (* changed this *)
        let e = H.find !tab id in
        (match e.entry_info with
         | ENTRY_function f -> if f.function_visible then e else findMostCurrInList (H.find_all !tab id)
         | ENTRY_variable v -> if v.variable_visible then e else findMostCurrInList (H.find_all !tab id)
         | _ -> e)
     in
        (* up to here *)
  if err then
    try
      lookup ()
    with Not_found ->
      (*error "unknown identifier %a (first occurrence)"
        pretty_id id;
      (* put it in, so we don't see more errors *)
      H.add !tab id (no_entry id);
      raise Exit*)
      raise Unknown_Identifier
  else
    lookup ()

let newVariable id typ err pos =
  !currentScope.sco_negofs <- !currentScope.sco_negofs - sizeOfType typ;
  let inf = {
    variable_type = typ;
    variable_offset = !currentScope.sco_negofs;
    variable_decl_pos = pos; (* added *)
    variable_visible = true (* added *)
  } in
  newEntry id (ENTRY_variable inf) err

let newFunction id err pos =
  try
    let e = lookupEntry id LOOKUP_CURRENT_SCOPE false in
    match e.entry_info with
    | ENTRY_function inf when inf.function_isForward ->
        inf.function_isForward <- false;
        inf.function_pstatus <- PARDEF_CHECK;
        inf.function_redeflist <- inf.function_paramlist;
        e
    | _ ->
       (* if err then
          error "duplicate iidentifier: %a" pretty_id id;*)
          raise Exit
  with Not_found ->
    let inf = {
      function_isForward = false;
      function_paramlist = [];
      function_redeflist = [];
      function_result = TYPE_none;
      function_pstatus = PARDEF_DEFINE;
      function_decl_pos  = pos; (* added *)
      function_visible = true;  (* added *)
      function_initquad = 0
    } in
    newEntry id (ENTRY_function inf) false

let newParameter id typ mode f err pos =
  match f.entry_info with
  | ENTRY_function inf -> begin
      match inf.function_pstatus with
      | PARDEF_DEFINE ->
          let inf_p = {
            parameter_type = typ;
            parameter_offset = 0;
            parameter_mode = mode;
            parameter_decl_pos = pos (* added *)
          } in
          let e = newEntry id (ENTRY_parameter inf_p) err in
          inf.function_paramlist <- e :: inf.function_paramlist;
          e
      | PARDEF_CHECK -> begin
          match inf.function_redeflist with
          | p :: ps -> begin
              inf.function_redeflist <- ps;
              match p.entry_info with
              | ENTRY_parameter inf ->
                  if not (equalType inf.parameter_type typ) then
                    error "Parameter type mismatch in redeclaration \
                           of function %a" pretty_id f.entry_id
                  else if inf.parameter_mode != mode then
                    error "Parameter passing mode mismatch in redeclaration \
                           of function %a" pretty_id f.entry_id
                  else if p.entry_id != id then
                    error "Parameter name mismatch in redeclaration \
                           of function %a" pretty_id f.entry_id
                  else begin
                    H.add !tab id p;
                    !currentScope.sco_entries <- p :: !currentScope.sco_entries
                  end;
                  p
              | _ ->
                  internal "I found a parameter that is not a parameter!";
                  raise Exit
            end
          | [] ->
              error "More parameters than expected in redeclaration \
                     of function %a" pretty_id f.entry_id;
              raise Exit
        end
      | PARDEF_COMPLETE ->
          internal "Cannot add a parameter to an already defined function";
          raise Exit
    end
  | _ ->
      internal "Cannot add a parameter to a non-function";
      raise Exit

let newTemporary typ sco = (* Changed and added scope as parameter *)
  let id = id_make ("$" ^ string_of_int !tempNumber) in
  sco.sco_negofs <- sco.sco_negofs - sizeOfType typ;
  let inf = {
    temporary_type = typ;
    temporary_offset = sco.sco_negofs
  } in
  incr tempNumber;
  newEntry id (ENTRY_temporary inf) false

let forwardFunction e =
  match e.entry_info with
  | ENTRY_function inf ->
      inf.function_isForward <- true
  | _ ->
      internal "Cannot make a non-function forward"
      
let visibilityOfEntry e b =     (* added *)
  match e.entry_info with
  | ENTRY_function f ->
      f.function_visible <- b
  | ENTRY_variable v ->
      v.variable_visible <- b
  | _ ->
      internal "Cannot change visibility of a non-function and non-variable argument"

let endFunctionHeader e typ =
  match e.entry_info with
  | ENTRY_function inf ->
      begin
        match inf.function_pstatus with
        | PARDEF_COMPLETE ->
            internal "Cannot end parameters in an already defined function"
        | PARDEF_DEFINE ->
            inf.function_result <- typ;
            let offset = ref start_positive_offset in
            let fix_offset e =
              match e.entry_info with
              | ENTRY_parameter inf ->
                  inf.parameter_offset <- !offset;
                  let size =
                    match inf.parameter_mode with
                    | PASS_BY_VALUE     -> sizeOfType inf.parameter_type
                    | PASS_BY_REFERENCE -> 2 in
                  offset := !offset + size
              | _ ->
                  internal "Cannot fix offset to a non parameter" in
            List.iter fix_offset inf.function_paramlist;
            inf.function_paramlist <- List.rev inf.function_paramlist
        | PARDEF_CHECK ->
            if inf.function_redeflist <> [] then
              error "Fewer parameters than expected in redeclaration \
                     of function %a" pretty_id e.entry_id;
            if not (equalType inf.function_result typ) then
              error "Result type mismatch in redeclaration of function %a"
                    pretty_id e.entry_id;
      end;
      inf.function_pstatus <- PARDEF_COMPLETE
  | _ ->
      internal "Cannot end parameters in a non-function"
      
(* ******************************************** *)

let show_offsets = false

let rec pretty_typ ppf typ =
  match typ with
  | TYPE_none ->
      fprintf ppf "<undefined>"
  | TYPE_unit ->
      fprintf ppf "unit"
  | TYPE_bool ->
      fprintf ppf "bool"      
  | TYPE_char ->
      fprintf ppf "char"      
  | TYPE_int ->
      fprintf ppf "int"
  | TYPE_float ->
      fprintf ppf "float"
  | TYPE_ref t ->
      fprintf ppf "ref ";
      pretty_typ ppf t
  | TYPE_array (et, sz) ->
      (match sz with
      | 1 -> fprintf ppf "(array of %a)" pretty_typ et
      | _ -> fprintf ppf "(array [*";
             for i=2 to sz do fprintf ppf ",*" done;
             fprintf ppf "] of %a)" pretty_typ et)
  | TYPE_userdef id ->
      fprintf ppf "%s" id
  | TYPE_func (t1, t2) ->
      pretty_typ ppf t1;
      fprintf ppf " -> ";
      pretty_typ ppf t2
  | TYPE_duck x ->
      fprintf ppf "@@%d" x

let pretty_mode ppf mode =
  match mode with
  | PASS_BY_REFERENCE ->
      fprintf ppf "reference "
  | _ ->
      ()

let printSymbolTable () =
  let rec walk ppf scp =
    if scp.sco_nesting <> 0 then begin
      fprintf ppf "scope: ";
      let entry ppf e =
        fprintf ppf "%a" pretty_id e.entry_id;
        match e.entry_info with
        | ENTRY_none ->
            fprintf ppf "<none>"
        | ENTRY_variable inf ->
            if inf.variable_visible = false then fprintf ppf "*";
            if show_offsets then
              fprintf ppf "[%d]" inf.variable_offset;
            fprintf ppf " : %a" pretty_typ inf.variable_type
        | ENTRY_function inf ->
            if inf.function_visible = false then fprintf ppf "*";
            let param ppf e =
              match e.entry_info with
                | ENTRY_parameter inf ->
                   fprintf ppf "%a%a : %a"
                      pretty_mode inf.parameter_mode
                      pretty_id e.entry_id
                      pretty_typ inf.parameter_type
                | _ ->
                    fprintf ppf "<invalid>" in
            let rec params ppf ps =
              match ps with
              | [p] ->
                  fprintf ppf "%a" param p
              | p :: ps ->
                  fprintf ppf "%a; %a" param p params ps;
              | [] ->
                  () in
            fprintf ppf "(%a) : %a"
              params inf.function_paramlist
              pretty_typ inf.function_result
        | ENTRY_parameter inf ->
            if show_offsets then
              fprintf ppf "[%d]" inf.parameter_offset
        | ENTRY_temporary inf ->
            if show_offsets then
              fprintf ppf "[%d]" inf.temporary_offset in
      let rec entries ppf es =
        match es with
          | [e] ->
              fprintf ppf "%a" entry e
          | e :: es ->
              fprintf ppf "%a, %a" entry e entries es;
          | [] ->
              () in
      match scp.sco_parent with
      | Some scpar ->
          fprintf ppf "%a\n%a"
            entries scp.sco_entries
            walk scpar
      | None ->
          fprintf ppf "<impossible>\n"
    end in
  let scope ppf scp =
    if scp.sco_nesting == 0 then
      fprintf ppf "no scope\n"
    else
      walk ppf scp in
  force_newline ();
  printf "*** Symbol Table Contents ***";
  force_newline ();
  printf "*****************************";
  force_newline ();
  printf "%a" scope !currentScope
