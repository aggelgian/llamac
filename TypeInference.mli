(* ********************************************************************************************* *)
(* ********************************* Type Definitions ****************************************** *)
(* ********************************************************************************************* *)

type constraint_set   = (Types.typ * Types.typ * (int *int)) list  (* Constraints generated for the Type Inference *)
type duckSubstitution = (Types.typ * Types.typ)                    (* Type substitution                            *)
type dimSubstitution  = (int * int)                                (* Array dimension substitution                 *)
type inferedTypes     = Types.typ list                             (* Results of Type Inference                    *)

(* ********************************************************************************************* *)
(* ********************************* Global Variables ****************************************** *)
(* ********************************************************************************************* *)

val cst : constraint_set ref    (* Set of Constraints *)

(* ********************************************************************************************* *)
(* *********************************** Exceptions ********************************************** *)
(* ********************************************************************************************* *)

exception Unify_Fail of (    (* Failure to Unify two types              *)
   Types.typ * Types.typ *   (* Constraint that couldn't be unified     *)
   (int *int)                (* Position where constraint was generated *)
)

(* ********************************************************************************************* *)
(* ************************************ Functions ********************************************** *)
(* ********************************************************************************************* *)

val printCST          : Format.formatter -> constraint_set -> unit      (* Pretty Prints the constraint set           *)
val printTypInfRes    : inferedTypes -> int -> unit                     (* Print the result of Type Inference         *)
val initConstraintSet : unit -> unit                                    (* Initialize / Reset constraint set          *)
val addConstraint     : (Types.typ * Types.typ) -> (int * int) -> unit  (* Add a new constraint to the constraint set *)
val unify             : constraint_set -> duckSubstitution list ->      (* Unification / Based on algorithm W         *)
                           dimSubstitution list -> inferedTypes -> 
                           inferedTypes
