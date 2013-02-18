open Types
open Format

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

let cst = ref []    (* Set of Constraints *)

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

  (* Pretty Prints the constraint set *)
let rec printCST ppf cst = 
   match cst with
   | [] -> 
      ()
   | (t1, t2, (l,c))::t ->
      fprintf ppf "%a = %a (Generated at Ln %d, Col %d)\n" pprint_typ t1 pprint_typ t2 l c;
      printCST ppf t
      
  (* Prints the result of the Type Inference *)
let rec printTypInfRes l i =
   match l with
   | [] -> 
      ()
   | h::t -> 
      printf "@@%d -> %a" i pprint_typ h;
      force_newline ();
      printTypInfRes t (i+1)
      
  (* If it finds a TYPE_array with dimensions old, it substitutes old with nnew *)
let rec subDimInType old nnew et =
   match  et with
   | TYPE_array (t, i)  -> if old = i then
                              TYPE_array ((subDimInType old nnew t), nnew)
                           else
                              TYPE_array ((subDimInType old nnew t), i)
   | TYPE_ref t         -> TYPE_ref (subDimInType old nnew t)
   | TYPE_func (t1, t2) -> TYPE_func ((subDimInType old nnew t1), (subDimInType old nnew t2))
   | _ as t             -> t
  
  (* Applies subDimInType to the CST *)
let subDimInCST old nnew cst =
   let walk (et1, et2, pos) = 
      ((subDimInType old nnew et1), (subDimInType old nnew et2), pos)
   in List.map walk cst
   
  (* Applies subDimInType to the array with the results *)
let subDimInRes old nnew l = 
   let walk h = subDimInType old nnew h
   in List.map walk l
   
  (* If it finds a @ = old, it substitutes it with the type nnew *)
let rec subDuckInType old nnew et =
   if et = old then
      nnew
   else
      (match et with
       | TYPE_array (t, i)  -> TYPE_array ((subDuckInType old nnew t), i)
       | TYPE_ref t         -> TYPE_ref (subDuckInType old nnew t)
       | TYPE_func (t1, t2) -> TYPE_func ((subDuckInType old nnew t1), (subDuckInType old nnew t2))
       | _ as t             -> t
      )
      
  (* Applies subDuckInType to the CST *)
let rec subDuckInCST old nnew cst =
   let walk (et1, et2, pos) =
      ((subDuckInType old nnew et1), (subDuckInType old nnew et2), pos)
   in List.map walk cst
   
  (* Applies subDuckInType to the array with the results *)
let rec subDuckInRes old nnew l =
   let walk h = subDuckInType old nnew h
   in List.map walk l
   
  (* Checks if a certain @ is present in the other type of the constraint equation *)
let rec isDuckInType duck et =
   if duck = et then
      true
   else
      (match et with
       | TYPE_array (t, i)  -> isDuckInType duck t
       | TYPE_ref t         -> isDuckInType duck t
       | TYPE_func (t1, t2) -> (isDuckInType duck t1) || (isDuckInType duck t2)
       | _                  -> false
      )
      
  (* Initialize / Reset constraint set *)
let initConstraintSet () =
   cst := []

  (* Add a new constraint to the constraint set *)
let addConstraint (t1, t2) pos =
   let newConstraint = (t1, t2, pos) in
   cst := newConstraint :: !cst
  
  (* Unification / Based on algorithm W *)
let rec unify cst duckS dimS res = 
   match cst with
   | [] ->                                                         (* If the CST is empty, unification is completed *)
      res                                                          (* Return the result array                       *)
   | (et1, et2, pos)::rest ->
      if et1 = et2 then                                            (* If the two types are the same                 *)
         unify rest duckS dimS res                                 (* Continue and discard this trivial constraint  *)
      else
      (match et1, et2 with
       | TYPE_duck _ , _ ->                                        (* Case 1 : @ = some_type                                 *)
          if (isDuckInType et1 et2) then                           (* If the same @ exists in the right type of the equation *)
             raise (Unify_Fail (et1, et2, pos))                    (* raise exception                                        *)
          else                                                     (* else unify                                             *)
             begin
                let new_CST = subDuckInCST et1 et2 rest in         (* Apply the substitution to the CST                      *)
                let new_duckS = (et1, et2)::duckS in               (* Store the substitution                                 *)
                let new_res = subDuckInRes et1 et2 res in          (* Apply the substitution to the result array             *)
                unify new_CST new_duckS dimS new_res               (* Unify the rest                                         *)
             end
       | _, TYPE_duck _ ->                                         (* Case 2 : some_type = @                                 *)
          if (isDuckInType et2 et1) then                           (* If the same @ exists in the left type of the equation  *)
             raise (Unify_Fail (et1, et2, pos))                    (* raise exception                                        *)
          else                                                     (* else unify                                             *)
             begin
                let new_CST = subDuckInCST et2 et1 rest in         (* Apply the substitution to the CST                      *)
                let new_duckS = (et2, et1)::duckS in               (* Store the substitution                                 *)
                let new_res = subDuckInRes et2 et1 res in          (* Apply the substitution to the result array             *)
                unify new_CST new_duckS dimS new_res               (* Unify the rest                                         *)
             end
       | TYPE_func (et11, et12), TYPE_func (et21, et22) ->         (* Case 3 : t11 -> t12 = t21 -> t22                       *)
          let n1 = (et11, et21, pos) in                            (* Create the constraint t11 = t21                        *)
          let n2 = (et12, et22, pos) in                            (* Create the constraint t12 = t22                        *)
          unify (n1::n2::rest) duckS dimS res                      (* Unify the rest                                         *)
       | TYPE_array (t1, i1), TYPE_array (t2, i2) when i1 < 0->    (* Case 4 : array of t1 = array of t2 with 1st array having unknown dimensions *)
          let new_CST = (t1, t2, pos)::(subDimInCST i1 i2 rest) in (* Add the constraint t1 = t2 and substitute the array dimensions *)
          let new_dimS = (i1, i2)::dimS in                         (* Store the array dimensions' substitution                       *)
          let new_res = subDimInRes i1 i2 res in                   (* Apply the array dimensions' substitution to the result array   *)
          unify new_CST duckS new_dimS new_res                     (* Unify the rest                                                 *)
       | TYPE_array (t1, i1), TYPE_array (t2, i2) when i2 < 0->    (* Case 5 : array of t1 = array of t2 with 2nd array having unknown dimensions *)
          let new_CST = (t1, t2, pos)::(subDimInCST i2 i1 rest) in (* Add the constraint t1 = t2 and substitute the array dimensions *)
          let new_dimS = (i1, i1)::dimS in                         (* Store the array dimensions' substitution                       *)
          let new_res = subDimInRes i2 i1 res in                   (* Apply the array dimensions' substitution to the result array   *)
          unify new_CST duckS new_dimS new_res                     (* Unify the rest                                                 *)
       | TYPE_array (t1, i1), TYPE_array (t2, i2) ->               (* Case 6 : array of t1 = array of t2, both of known dimensions   *)
          if i1 = i2 then                                          (* If they have the same dimension size, unify                    *)
             let new_CST = (t1, t2, pos)::rest in                  (* Add the constraint t1 = t2                                     *)
             unify new_CST duckS dimS res                          (* Unify the rest                                                 *)
          else
             raise (Unify_Fail (et1, et2, pos))                    (* raise exception                                        *)
       | TYPE_ref t1, TYPE_ref t2 ->                               (* Case 7 : t1 ref = t2 ref                               *)
          let new_CST = (t1, t2, pos):: rest in                    (* Add the constraint t1 = t2                             *)
          unify new_CST duckS dimS res                             (* Unify the rest                                         *)
       | _, _ ->                                                   (* Anything else is a Unification Error                   *)
          raise (Unify_Fail (et1, et2, pos))                       (* raise exception                                        *)
      )
