open Format

(* ********************************************************************************************* *)
(* ********************************* Type Definitions ****************************************** *)
(* ********************************************************************************************* *)

type typ = TYPE_none          (* Not to be used *)
         | TYPE_unit          (* Unit *)
         | TYPE_bool          (* Bool *)
         | TYPE_char          (* Char *)
         | TYPE_int           (* Int *)
         | TYPE_float         (* Float *)
         | TYPE_array of      (* Array *)
            typ *    (* Array Type *)
            int      (* Number of Dimensions *)
         | TYPE_ref of        (* Reference (mutable) *)
            typ      (* Reference to which type *)
         | TYPE_func of       (* Function *)
            typ *    (* Parameter type *)
            typ      (* Result type *)
         | TYPE_userdef of    (* User Defined Type *)
            string   (* Name of the User Defined Type *)
         | TYPE_duck of       (* Special Type - Used for Type Inference *)
            int      (* Counter *)

(* ********************************************************************************************* *)
(* ************************************ Functions ********************************************** *)
(* ********************************************************************************************* *)

  (* Calculate the size of a type *)
let rec sizeOfType t =
   match t with
   | TYPE_bool           -> 1                   (* 8-bit Bool                                    *)
   | TYPE_char           -> 1                   (* 8-bit Char                                    *)
   | TYPE_float          -> 4                   (* 32-bit IEEE 754 Single-Precision Binary Float *)
   | TYPE_int            -> 2                   (* 16-bit Int                                    *)
   | TYPE_ref et         -> 2                   (* 8-bit Pointer                                 *)
   | TYPE_array (et, sz) -> 2                   (* Array Size                                    *)
   | TYPE_func (t1, t2)  -> 2                   (* Function Pointer Size                         *)
   | TYPE_userdef id     -> 2                   (* Pointer                                       *)
   | _                   -> 0                   (* duck & Unit & none                            *)

  (* Checks if two types are equal *)
let rec equalType t1 t2 =
   t1 = t2
   
  (* Finds the return type of a function *)
let rec funcReturnType t = 
   match t with
   | TYPE_func (et1, et2) -> funcReturnType et2
   | _                    -> t
   
  (* Pretty Print a Type *)
let rec pprint_typ ppf typ =
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
      fprintf ppf "ref %a" pprint_typ t
  | TYPE_array (et, sz) ->
      (match sz with
      | 1 -> 
         fprintf ppf "(array of %a)" pprint_typ et
      | i when i < 0 ->
         fprintf ppf "(array %d of %a)" i pprint_typ et
      | _ -> 
         fprintf ppf "(array [*";
         for i=2 to sz do Format.fprintf ppf ",*" done;
         fprintf ppf "] of %a)" pprint_typ et)
  | TYPE_userdef id ->
      fprintf ppf "%s" id
  | TYPE_func (t1, t2) ->
      Format.fprintf ppf "(%a -> %a)" pprint_typ t1 pprint_typ t2
  | TYPE_duck x ->
      Format.fprintf ppf "@@%d" x
