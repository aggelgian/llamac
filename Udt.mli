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

val user_types   : udtTable ref                                               (* User Defined Types' Table                     *)
val icode_UDTEnv : (string * (Symbol.entry * string * Symbol.scope)) list ref (* All Constructors paired with their Icode info *)

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

  (* Looks up a Constructor Name in the UDT table and returns (udt_name, types_list) *)
val lookupConstructor   : udtTable ref -> string -> string * (Types.typ list)
  (* Looks up a UDT Name in the UDT Table and returns its structure                  *)
val lookupType          : udtTable ref -> string -> udtEntry_constr list
  (* Checks if an identifier is already a user defined type                          *)
val checkIsDefined      : string -> udtTable ref -> bool
  (* Forward creation of UDTs in the new block                                       *)
val forwardCreateType   : (string * (string * Types.typ list) list) list -> udtTable ref -> unit
  (* Updates the structure of the new UDTs in the env                                *)
val updateTypeStructure : (string * (string * Types.typ list) list) list -> udtTable ref -> unit
  (* Pretty prints the whole UDT table                                               *)
val print_UDTtable      : Format.formatter -> udtTable ref -> unit
  (* Return all the (cname, tlist) for the Quad creation                             *)
val allConstructorInfo  : udtTable ref -> (string * string * (Types.typ list)) list
  (* Find Maximun Needed Heapsize to store a UDT                                     *)
val maxUDTsize          : udtTable ref -> string -> int
