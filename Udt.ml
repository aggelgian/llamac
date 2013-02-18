open Types
open Format

(* ********************************************************************************************* *)
(* ********************************* Type Definitions ****************************************** *)
(* ********************************************************************************************* *)

type udtTable =                    (* UDT table *)
   udtTable_entry list         (* List of table entries         *)
   
and udtTable_entry =               (* Entry of UDT table *)
   string *                    (* User Defined Type name        *)
   (udtEntry_constr list) ref  (* Reference to type's structure *)
   
and udtEntry_constr =              (* Structure's clause *)
   string *                    (* Constructor name              *)
   Types.typ list              (* List of constructor's types   *) 

(* ********************************************************************************************* *)
(* ********************************* Global Variables ****************************************** *)
(* ********************************************************************************************* *)

let user_types = ref []        (* User Defined Types' Table                     *)
let icode_UDTEnv = ref []      (* All Constructors paired with their Icode info *)

(* ********************************************************************************************* *)
(* *********************************** Exceptions ********************************************** *)
(* ********************************************************************************************* *)

exception AlreadyDefinedType of string          (* Redefinition of a bound UDT                 *)
exception UnboundType of string                 (* Unbound UDT name                            *)
exception DuplicateClauseInEnv of string        (* Constructor name already in use             *)
exception DuplicateClauseInNewBlock of string   (* Duplicate Constructor name in the new block *)
exception Unknown_Constructor                   (* Unbound Constructor name                    *)

(* ********************************************************************************************* *)
(* ************************************ Functions ********************************************** *)
(* ********************************************************************************************* *)

  (* Find the maximum number in a List of non-negative integers *)
let maxInList l =
   let rec foo ll max = 
      match ll with
      | []   -> 
         max
      | h::t -> 
         if h > max then
            foo t h
         else
            foo t max
   in foo l 0

  (* Find Maximun Needed Heapsize to store a UDT *)
let maxUDTsize env name = 
   let clist = List.assoc name !env in
   let csize (c, tlist) =
      let l = List.map (fun t -> sizeOfType t) tlist
      in List.fold_left (+) 0 l
   in 
   let sizes = List.map csize !clist in
   (maxInList sizes) + (sizeOfType (TYPE_array (TYPE_char, 1)))

  (* Return (tname, cname, tlist) list for a (tname, clist) *)
let bindTypeStruct (tname, clist) = 
   let rec foo id l acc =
      match l with
      | [] ->
         List.rev acc
      | (cname, tlist)::t ->
         foo id t ((id, cname, tlist)::acc)
   in foo tname clist []

  (* Return all the (cname, tlist) for the Quad creation *)
let allConstructorInfo env =
   List.flatten (List.map (fun (name, clist) -> bindTypeStruct (name, !clist)) !env)

  (* Looks up a Constructor Name in the UDT table and returns (udt_name, types_list) *)
let lookupConstructor env id =
   let rec foo l x = 
      match l with
      | [] ->                                          (* If I have iterated over all the UDT table and haven't found it *)
         raise Unknown_Constructor                     (* raise Unknow_Constructor exception                             *)
      | (name, clist)::t ->                            (* Check the udt at the top of the UDT table                      *)
         (try
            let ctypes = List.assoc x !clist in        (* Try to find the constructor in this udt                        *)
            (name, ctypes)                             (* If it's found return the (udt_name, types_list)                *)
          with
          | Not_found ->
             foo t x)                                  (* else check the rest of the UDT table                           *)
   in foo !env id

  (* Looks up a UDT Name in the UDT Table and returns its structure *)
let lookupType env id = 
   let typ_struct = List.assoc id !env in
   !typ_struct

  (* Checks if an identifier is already a user defined type *)
let checkIsDefined name env = 
   try
      ignore(List.assoc name !env);
      true
   with
   | Not_found -> 
      false

  (* Forward creation of UDTs in the new block *)
let forwardCreateType lst env =
   let stripped_list = 
      List.map (fun (name, clst) -> name) lst in   (* Get a list of the types' names in the UDT Table                *)
   let foo name =
      if (checkIsDefined name env) then            (* If there is a type already defined with the same name          *)
         raise (AlreadyDefinedType name)           (* Raise the AlreadyDefinedType exception                         *)
      else
         env := (name, ref []) :: !env             (* else create a new entry with the type name and empty structure *)
   in List.iter foo stripped_list
   
  (* Return all the constructors defined in the UDT table *)
let flattenEnvConstructors env =
   let 
      x = fun (name, clist) -> !clist              (* Get the structure of each type                *)
   in let 
      y = fun (cname, tlist) -> cname              (* Get the constructors' names of each structure *)
   in List.map y (List.flatten (List.map x !env))
  
  (* Return all the constructors defined in the new block*)
let flattenCandidateConstructors lst =
   let 
      x = fun (name, clist) -> clist               (* Get the structure of each type                *)
   in let 
      y = fun (cname, tlist) -> cname              (* Get the constructors' names of each structure *)
   in List.map y (List.flatten (List.map x lst))
   
  (* Return all defined types in UDT table and the new block *)
let flattenEnvTypes lst env =
   let x = fun (name, clist) -> name               (* Function that returns the name of the type             *)
   in (List.map x lst) @ (List.map x !env)         (* Apply that function to the UDT table and the new block *)
   
  (* Return all used UDTs in the new block *)
let flattenListTypes lst =
   let 
      x = fun (name, clist) -> clist               (* Get the structure of each type                *)
   in let 
      y = fun (cname, tlist) ->                    (* Get the list with UDTs used in each structure *)
         let rec getUDT = fun et ->
            (match et with
            | TYPE_userdef id      -> [id]
            | TYPE_ref ett         -> getUDT ett
            | TYPE_array (ett, sz) -> getUDT ett
            | TYPE_func (et1, et2) -> (getUDT et1) @ (getUDT et2)
            | _                    -> [])
         in List.map getUDT tlist
   in List.flatten (List.flatten (List.map y (List.flatten (List.map x lst))))
   
  (* Checks a list for duplicate entries and returns one if it occurs *)
let rec hasDuplicate l =
   match l with
   | [] -> None
   | h::t ->
      if (List.mem h t) then
         Some h
      else
         hasDuplicate t
         
  (* Compares the UDTs in a list with the UDT table and checks if any is Unbound, and if so returns its name *)
let rec isUnbound l lenv =
   match l with
   | [] -> None
   | h::t ->
      if (List.mem h lenv) then
         isUnbound t lenv
      else
         Some h
               
  (* Updates the structure of the new UDTs in the env *)
let updateTypeStructure lst env =
   let flatcEnv = flattenEnvConstructors env in          (* List with all the constructors' names in the UDT          *)
   let flatcList = flattenCandidateConstructors lst in   (* List with all the constructors' names in the new block    *)
   let flattEnv = flattenEnvTypes lst env in             (* List with all the types' names in the UDT and new block   *)
   let flattList = flattenListTypes lst in               (* List with all the types' names in the new block           *)
   match hasDuplicate flatcList with                     (* Check for duplicate constructors in new block             *)
   | Some c ->
      raise (DuplicateClauseInNewBlock c)                (* If so, raise DuplicateClauseInNewBlock exception          *)
   | None ->
      match hasDuplicate (flatcList @ flatcEnv) with     (* Check for duplicate constructors in the UDT and new block *)
      | Some c ->
         raise (DuplicateClauseInEnv c)                  (* If so, raise DuplicateClauseInEnv exception               *)
      | None ->
         match isUnbound flattList flattEnv with         (* Check for using Unbound UDT                               *)
         | Some c ->
            raise (UnboundType c)                        (* If so, raise UnboundType exception                        *)
         | None ->
            let foo = fun (name, clist) ->               (* else update the UDT the structure of the new types        *)
               (List.assoc name !env) := clist;
            in List.iter foo lst 
            
(* ******************************************* *)
(* ******** Pretty Print the UDT Table ******* *)
(* ******************************************* *)

  (* Pretty prints a Types.typ *)
let rec print_typ ppf t =
   match t with
   | TYPE_unit            -> fprintf ppf "()"
   | TYPE_bool            -> fprintf ppf "bool"
   | TYPE_char            -> fprintf ppf "char"
   | TYPE_int             -> fprintf ppf "int"
   | TYPE_float           -> fprintf ppf "float"
   | TYPE_array (tt, num) -> (match num with
                              | 1 -> fprintf ppf "(array of %a)" print_typ tt
                              | _ -> fprintf ppf "(array [*";
                                     for i=2 to num do fprintf ppf ",*" done;
                                     fprintf ppf "] of %a)" print_typ tt)
   | TYPE_ref tt          -> fprintf ppf "ref %a" print_typ tt
   | TYPE_func (t1, t2)   -> fprintf ppf "(%a -> %a)" print_typ t1 print_typ t2
   | TYPE_userdef id      -> fprintf ppf "%s" id
   | _                    -> ()
   
  (* Pretty prints a whole UDT entry *)
let print_UDTtable_entry ppf (type_name, clist) =     (* takes a UDT representation as parameter  *)
   let print_typ_spaced = fun t ->                    (* Prints the Types.typ followed by a space *)
      fprintf ppf "%a " print_typ t
   in let print_allCases = fun (cname, tlist) ->      (* Prints all the possible cases of a UDT - Constructors' names and parameters *)
      (match tlist with
       | [] -> fprintf ppf "  | %s" cname
       | _  -> fprintf ppf "  | %s -> " cname;
               List.iter print_typ_spaced tlist);
      force_newline();
   in
      fprintf ppf "%s =" type_name;
      force_newline();
      List.iter print_allCases !clist

  (* Pretty prints the whole UDT table *)
let print_UDTtable ppf env =
   List.iter (fun e -> fprintf ppf "%a" print_UDTtable_entry e) !env

