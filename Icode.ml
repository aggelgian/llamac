open Types
open Identifier
open Symbol
open Error
open Ast
open Udt
open Quads
open Debug
open Format

(* ********************************************************************************************* *)
(* ********************************* Type Definitions ****************************************** *)
(* ********************************************************************************************* *)

module T = TypeChecker

(* ********************************************************************************************* *)
(* ********************************* Global Variables ****************************************** *)
(* ********************************************************************************************* *)

let array_stack = ref []         (* Array Stack to store the Array entries    *)

(* ********************************************************************************************* *)
(* *********************************** Exceptions ********************************************** *)
(* ********************************************************************************************* *)

exception UninitializedPlace of (int * int)

(* ********************************************************************************************* *)
(* ************************************ Functions ********************************************** *)
(* ********************************************************************************************* *)

let listMerge l1 l2 = 
   let tmp = List.filter (fun x -> not (List.mem x l1)) l2 in
   l1 @ tmp

let listMake n = 
   let rec foo x acc =
      match x with
      | 0 -> acc
      | _ -> foo (x-1) ((string_of_int x)::acc)
   in foo n []
   
  (* Return the array type from a Symbol Entry option *)
let getArrayTypeFromEntry en =
   match en with
   | None -> 
      iInternal "Icode: Failed to find Symbol Entry for array" None;
      raise Terminate
   | Some entry ->
      (match entry.entry_info with
       | ENTRY_variable vinfo ->
         (match vinfo.variable_type with
          | TYPE_array (et, n) ->
            (entry, et, vinfo.variable_type)
          | _ ->
            iInternal "Icode: Expected Array type" None;
            raise Terminate
         )
       | ENTRY_parameter pinfo ->
         (match pinfo.parameter_type with
          | TYPE_array (et, n) ->
            (entry, et, pinfo.parameter_type)
          | _ ->
            iInternal "Icode: Expected Array type" None;
            raise Terminate
         )
       | _ ->
         iInternal "Icode: Incompatible Symbol Entry for array" None;
         raise Terminate
      )
      
  (* Return the function result type from a Symbol Entry option *)
let getFuncResTypeFromEntry en =
   match en with
   | None ->
      iInternal "Icode: Failed to find Symbol Entry for function" None;
      raise Terminate
   | Some entry ->
      (match entry.entry_info with
       | ENTRY_function finfo ->
         (entry, finfo.function_result)
       | ENTRY_parameter pinfo ->
         (entry, funcReturnType pinfo.parameter_type)
       | _ ->
         iInternal "Icode: Incompatible Symbol Entry for function" None;
         raise Terminate
      )

  (* Returns the Label of the Next Quad *)
let nextQuad () = 
   !quadNext

  (* Generate the Next Quad *)
let genQuad op argX argY argZ =
   let nQ = nextQuad() in
   incr quadNext;
   { quad_tag = nQ;
     quad_op = op;
     quad_argX = argX;
     quad_argY = argY;
     quad_argZ = argZ }
     
  (* Create a new Temporary Variable *)
let newTemp et currScope =
   match currScope with
   | None ->
      iInternal "Need a scope in order to create a new Temporary" None;
      raise Terminate
   | Some sc ->
      let temp = newTemporary et sc in                   (* Create a new Symbol Entry        *)
      sc.sco_entries <- temp :: sc.sco_entries;          (* Add Entry to Scope Entries       *)
      temp                                               (* Return the Symbol Entry          *)
   
  (* Substitutes the Stars in all Quads in l with Label z *)
let backpatch ql il z = 
   match il with
   | [] ->
      ()
   | _ ->
      List.iter (fun q -> 
         if List.mem q.quad_tag il then
         if q.quad_argZ = Star then
            q.quad_argZ <- Label z ) ql
     
  (* Create an object with default Semantic Properties *)
let newProp et = {
   etype  = et;
   place  = InitPlace;
   next   = [];
   trues  = [];
   falses = [];
   quads  = []
}

  (* Convert a binary operator to the corresponding Operator *)
let bnToOp bn =
   match bn with
   | B_plus      -> Op_plus
   | B_minus     -> Op_minus
   | B_mult      -> Op_mult
   | B_div       -> Op_div
   | B_fplus     -> Op_fplus
   | B_fminus    -> Op_fminus
   | B_fmult     -> Op_fmult
   | B_fdiv      -> Op_fdiv
   | B_mod       -> Op_mod
   | B_pow       -> Op_pow
   | B_assign    -> Op_structEq
   | B_ltgt      -> Op_structIneq
   | B_lt        -> Op_lt
   | B_gt        -> Op_gt
   | B_lteq      -> Op_lteq
   | B_gteq      -> Op_gteq
   | B_eq        -> Op_physEq
   | B_neq       -> Op_physIneq
   | B_conj      -> failwith "B_conj doesn't correspond to an Icode.operator"
   | B_disj      -> failwith "B_disj doesn't correspond to an Icode.operator"
   | B_semic     -> failwith "B_semic doesn't correspond to an Icode.operator"
   | B_refassign -> Op_assign
   
  (* Convert a Cond to Expr *)
let condToExpr prop sco = 
   let w = newTemp TYPE_bool sco in                                                     (* Generate new Temporary variable             *)
   backpatch prop.quads prop.trues (nextQuad ());                                       (* Backpatch the TRUE with the nextQuad        *)
   let qt = genQuad Op_assign (Bool true) Empty (Entry w) in                            (* Quad1: :=, true, -, W                       *)
   let qj = genQuad Op_jump Empty Empty Star in                                         (* Quad2: jump, -, -, *                        *)
   backpatch prop.quads prop.falses (nextQuad ());                                      (* Backpatch the FALSE with the nextQuad       *)
   let qf = genQuad Op_assign (Bool false) Empty (Entry w) in                           (* Quad3: :=, false, -, W                      *)
   prop.place <- Entry w;                                                               (* PLACE = w                                   *)
   prop.next <- [qj.quad_tag];                                                          (* NEXT = Quad2                                *)
   prop.trues <- [];
   prop.falses <- [];
   prop.quads <- prop.quads @ [qt; qj; qf]                                              (* Add new Quads                               *)
   
  (* Convert an Expr to Cond *)
let exprToCond prop sco = 
   let qt = genQuad Op_ifb prop.place Empty Star in                                     (* Quad1: ifb, prop.place, - *                 *)
   let qf = genQuad Op_jump Empty Empty Star in                                         (* Quad2: jump, -, -, *                        *)
   prop.trues <- [qt.quad_tag];                                                         (* TRUE = Quad1                                *)
   prop.falses <- [qf.quad_tag];                                                        (* FALSE = Quad2                               *)
   prop.quads <- prop.quads @ [qt; qf]                                                  (* Add new Quads                               *)

  (* Translate an ast_expr_node to Icode *)
let rec icodeExpr udt_env currScope stmt_flag expr =
   match expr.tag_ex with
   | E_int i ->
      let prop = newProp TYPE_int in                                                    (* Generate a fresh Semantic Properties Object *)
      prop.place <- Int i;                                                              (* Set the Place of the Expression             *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_real x ->
      let prop = newProp TYPE_float in                                                  (* Generate a fresh Semantic Properties Object *)
      prop.place <- Float x;                                                            (* Set the Place of the Expression             *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_char c ->
      let prop = newProp TYPE_char in                                                   (* Generate a fresh Semantic Properties Object *)
      prop.place <- Chr c;                                                              (* Set the Place of the Expression             *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_string s ->
      let prop = newProp (TYPE_array (TYPE_char, 1)) in                                 (* Generate a fresh Semantic Properties Object *)
      prop.place <- Str s;                                                              (* Set the Place of the Expression             *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_bool b ->
      let prop = newProp TYPE_bool in                                                   (* Generate a fresh Semantic Properties Object *)
      prop.place <- Bool b;                                                             (* Set the Place of the Expression             *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_unit ->
      let prop = newProp TYPE_unit in                                                   (* Generate a fresh Semantic Properties Object *)
      prop.place <- Unit;                                                               (* Set the Place of the Expression             *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_var id ->
      let pos = getPosFromMsg expr.meta_ex "id_name_start" in                           (* Locate the position of the expr in the file *)
      (match expr.entry_ex with
       | None ->
         iInternal "Icode: Symbol entry isn't stored for E_var" (Some pos);
         raise Terminate
       | Some entry ->
         (match entry.entry_info with                                                   (* Match the type of the Symbol Entry          *)
          | ENTRY_variable vinfo ->
            let prop = newProp vinfo.variable_type in                                   (* Generate a fresh Semantic Properties Object *)
            prop.place <- Entry entry;                                                  (* Place = the Symbol Table Entry              *)
            prop                                                                        (* Return the Semantic Properties Object       *)
          | ENTRY_function finfo ->
            let res_type = finfo.function_result in                                     (* Get the type of the function's result       *)
            let par_types = T.getListWithParamsTypes finfo.function_paramlist [] in     (* Get the types of the function's parameters  *)
            let full_type = T.constructFuncType par_types res_type in                   (* Construct function's type                   *)
            let prop = newProp full_type in                                             (* Generate a fresh Semantic Properties Object *)
            prop.place <- Entry entry;                                                  (* Place = the Symbol Table Entry              *)
            prop                                                                        (* Return the Semantic Properties Object       *)
          | ENTRY_parameter pinfo ->
            let prop = newProp pinfo.parameter_type in                                  (* Generate a fresh Semantic Properties Object *)
            prop.place <- Entry entry;                                                  (* Place = the Symbol Table Entry              *)
            prop                                                                        (* Return the Semantic Properties Object       *)
          | _ ->
            iInternal "Icode: E_var entry isn't var / func / param" (Some pos);
            raise Terminate
         )
      )
   | E_func (id, el) ->
      let (en, et) = getFuncResTypeFromEntry expr.entry_ex in                           (* Get the func Symbol Entry and Result Type   *)
      let elprop = List.map (fun e -> icodeExpr udt_env currScope false e) el in        (* Semantic Properties Objects of the Exprs    *)
      let icodeOne e =                                                                  (* Function to handle an Inner Expr e          *)
         if (e.trues <> []) && (e.falses <> []) then                                    (* If e is a Cond                              *)
         begin
            backpatch e.quads e.next (nextQuad ());                                     (* Backpatch e.NEXT with nextQuad              *)
            e.next <- [];                                                               (* Empty e.NEXT                                *)
            condToExpr e currScope                                                      (* Convert e to Expr *)
         end;
         backpatch e.quads e.next (nextQuad ());                                        (* Backpatch e.NEXT with nextQuad              *)
         e.next <- [];                                                                  (* Empty e.NEXT                                *)
         let q = genQuad Op_par e.place (PassType V) Empty in                           (* Quad: par, e.PLACE, V, -                    *)
         e.quads <- e.quads @ [q] in                                                    (* Add the new Quad                            *)
      List.iter icodeOne elprop;                                                        (* Parse all function Parameters               *)
      let par_quads = List.flatten (List.map (fun p -> p.quads) elprop) in              (* Concat all Parameters' Quads                *)
      let w = newTemp et currScope in                                                   (* Generate a new Temporary variable           *)
      let qr = genQuad Op_par (Entry w) (PassType RET) Empty in                         (* Quad1: par, W, RET, -                       *)
      let qc = genQuad Op_call Empty Empty (Entry en) in                                (* Quad2: call, -, -, func                     *)
      let prop = newProp et in                                                          (* Generate a fresh Semantic Properties Object *)
      prop.place <- Entry w;                                                            (* PLACE = W                                   *)
      prop.quads <- par_quads @ [qr; qc];                                               (* Add the new Quads                           *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_constr (id, el) ->
      let (en, tname, _) = List.assoc id udt_env in                                     (* Get Constr entry and UDT type               *)
      let elprop = List.map (fun e -> icodeExpr udt_env currScope false e) el in        (* Semantic Properties Objects of the Exprs    *)
      let icodeOne e =                                                                  (* Function to handle an Inner Expr e          *)
         if (e.trues <> []) && (e.falses <> []) then                                    (* If e is a Cond                              *)
         begin
            backpatch e.quads e.next (nextQuad ());                                     (* Backpatch e.NEXT with nextQuad              *)
            e.next <- [];                                                               (* Empty e.NEXT                                *)
            condToExpr e currScope                                                      (* Convert e to Expr *)
         end;
         backpatch e.quads e.next (nextQuad ());                                        (* Backpatch e.NEXT with nextQuad              *)
         e.next <- [];                                                                  (* Empty e.NEXT                                *)
         let q = genQuad Op_par e.place (PassType V) Empty in                           (* Quad: par, e.PLACE, V, -                    *)
         e.quads <- e.quads @ [q] in                                                    (* Add the new Quad                            *)
      List.iter icodeOne elprop;                                                        (* Parse all function Parameters               *)
      let par_quads = List.flatten (List.map (fun p -> p.quads) elprop) in              (* Concat all Parameters' Quads                *)
      let w = newTemp (TYPE_userdef tname) currScope in                                 (* Generate a new Temporary variable           *)
      let qr = genQuad Op_par (Entry w) (PassType RET) Empty in                         (* Quad1: par, W, RET, -                       *)
      let qc = genQuad Op_call Empty Empty (Entry en) in                                (* Quad2: call, -, -, func                     *)
      let prop = newProp (TYPE_userdef tname) in                                        (* Generate a fresh Semantic Properties Object *)
      prop.place <- Entry w;                                                            (* PLACE = W                                   *)
      prop.quads <- par_quads @ [qr; qc];                                               (* Add the new Quads                           *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_bang e ->
      let pos = getPosFromMsg expr.meta_ex "bang_start" in                              (* Locate the position of the expr in the file *)
      let eprop = icodeExpr udt_env currScope false e in                                (* Semantic Properties of the Inner Expr       *)
      (match eprop.etype with
       | TYPE_ref t ->
         if (eprop.trues <> []) && (eprop.falses <> []) then                            (* IF the Inner Expr is a Cond                 *)
         begin
            backpatch eprop.quads eprop.next (nextQuad ());                             (* Backpatch it with the nextQuad              *)
            condToExpr eprop currScope;                                                 (* Convert Cond to Expr                        *)
         end;
         backpatch eprop.quads eprop.next (nextQuad ());                                (* Backpatch it with the nextQuad              *)
         let w = newTemp (TYPE_ref t) currScope in                                      (* Generate new Temporary variable             *)
         let q = genQuad Op_assign eprop.place Empty (Entry w) in                       (* Quad: :=, e.place, -, W                     *)
         let prop = newProp t in                                                        (* Generate a fresh Semantic Properties Object *)
         prop.place <- Deref ((Entry w), t);                                            (* Place = the dereferenced pointer            *)
         prop.quads <- eprop.quads @ [q];                                               (* Add new Quads                               *)
         prop                                                                           (* Return the Semantic Properties Object       *)
       | _ ->
         iInternal "Icode: E_bang inner expression is not a ref" (Some pos);
         raise Terminate
      )
   | E_not e ->
      let eprop = icodeExpr udt_env currScope false e in                                (* Semantic Properties of the Inner Expr       *)
      if (eprop.trues = []) && (eprop.falses = []) then                                 (* IF the Inner Expr is not a Cond             *)
      begin
         backpatch eprop.quads eprop.next (nextQuad ());                                (* Backpatch NEXT - if exists - with nextQuad  *)
         eprop.next <- [];                                                              (* Empty NEXT after backpatch                  *)
         exprToCond eprop currScope                                                     (* Convert Expr to Cond                        *)
      end;
      let prop = newProp TYPE_bool in                                                   (* Generate a fresh Semantic Properties Object *)
      prop.place <- eprop.place;                                                        (* Assign the same PLACE as Inner Expr         *)
      prop.next <- eprop.next;                                                          (* Assign the same NEXT as Inner Expr          *)
      prop.falses <- eprop.trues;                                                       (* Swap TRUE and FALSE Lists                   *)
      prop.trues <- eprop.falses;
      prop.quads <- eprop.quads;                                                        (* Assign the same QUADS as Inner Expr         *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_signed (s, e) ->
      let eprop = icodeExpr udt_env currScope false e in                                (* Semantic Properties of the Inner Expr       *)
      if (eprop.trues <> []) && (eprop.falses <> []) then                               (* IF the Inner Expr is a Cond                 *)
      begin
         backpatch eprop.quads eprop.next (nextQuad ());                                (* Backpatch NEXT - if exists - with nextQuad  *)
         eprop.next <- [];                                                              (* Empty NEXT after backpatch                  *)
         condToExpr eprop currScope                                                     (* Convert Cond to Expr                        *)
      end;
      (match s with
       | S_plus   -> 
         let prop = newProp TYPE_int in                                                 (* Generate a fresh Semantic Properties Object *)
         prop.place <- eprop.place;                                                     (* Assign the same PLACE as Inner Expr         *)
         prop.next <- eprop.next;                                                       (* Assign the same NEXT as Inner Expr          *)
         prop.quads <- eprop.quads;                                                     (* Assign the same QUADS as Inner Expr         *)
         prop                                                                           (* Return the Semantic Properties Object       *)
       | S_minus  -> 
         backpatch eprop.quads eprop.next (nextQuad ());                                (* Backpatch NEXT - if exists - with nextQuad  *)
         let prop = newProp TYPE_int in                                                 (* Generate a fresh Semantic Properties Object *)
         let w = newTemp TYPE_int currScope in                                          (* Generate a new Temporary variable           *)
         let q = genQuad Op_minus eprop.place Empty (Entry w) in                        (* Quad: -, e.place, -, W                      *)
         prop.place <- Entry w;                                                         (* PLACE = Entry of temporary W                *)
         prop.quads <- eprop.quads @ [q];                                               (* Add the new Quad                            *)
         prop                                                                           (* Return the Semantic Properties Object       *)
       | S_fplus  -> 
         let prop = newProp TYPE_float in                                               (* Generate a fresh Semantic Properties Object *)
         prop.place <- eprop.place;                                                     (* Assign the same PLACE as Inner Expr         *)
         prop.next <- eprop.next;                                                       (* Assign the same NEXT as Inner Expr          *)
         prop.quads <- eprop.quads;                                                     (* Assign the same QUADS as Inner Expr         *)
         prop                                                                           (* Return the Semantic Properties Object       *)
       | S_fminus -> 
         backpatch eprop.quads eprop.next (nextQuad ());                                (* Backpatch NEXT - if exists - with nextQuad  *)
         let prop = newProp TYPE_float in                                               (* Generate a fresh Semantic Properties Object *)
         let w = newTemp TYPE_float currScope in                                        (* Generate a new Temporary variable           *)
         let q = genQuad Op_fminus eprop.place Empty (Entry w) in                       (* Quad: -., e.place, -, W                     *)
         prop.place <- Entry w;                                                         (* PLACE = Entry of temporary W                *)
         prop.quads <- eprop.quads @ [q];                                               (* Add the new Quad                            *)
         prop                                                                           (* Return the Semantic Properties Object       *)
       | Unsigned -> 
         iInternal "Icode: Didn't Expect Unsigned Expression" None;
         raise Terminate
      )
   | E_binop (e1, bn, e2) when List.mem bn [B_plus; B_minus; B_mult; B_div; B_mod] ->
      let e1prop = icodeExpr udt_env currScope false e1 in                              (* Semantic Properties of the Left Expr        *)
      let e2prop = icodeExpr udt_env currScope false e2 in                              (* Semantic Properties of the Right Expr       *)
      if (e1prop.trues <> []) && (e1prop.falses <> []) then                             (* If Expr e1 is a Cond                        *)
      begin
         backpatch e1prop.quads e1prop.next (nextQuad ());                              (* Backpatch e1.NEXT with nextQuad             *)
         e1prop.next <- [];                                                             (* Empty e1.NEXT                               *)
         condToExpr e1prop currScope                                                    (* Convert e1 to Expr                          *)
      end;
      if (e2prop.trues <> []) && (e2prop.falses <> []) then                             (* If Expr e2 is a Cond                        *)
      begin
         backpatch e2prop.quads e2prop.next (nextQuad ());                              (* Backpatch e2.NEXT with nextQuad             *)
         e2prop.next <- [];                                                             (* Empty e2.NEXT                               *)
         condToExpr e2prop currScope                                                    (* Convert e2 to Expr                          *)
      end;
      if e2prop.quads <> [] then                                                        (* If e2 has Quads                             *)
      begin
         let e2first = List.hd e2prop.quads in                                          (* Get the 1st Quad of e2                      *)
         backpatch e1prop.quads e1prop.next e2first.quad_tag;                           (* Backpatch e1.NEXT with e2first              *)
         backpatch e2prop.quads e2prop.next (nextQuad ())                               (* Backpatch e2.NEXT with nextQuad             *)
      end
      else                                                                              (* Else if e2 has no Quads                     *)
         backpatch e1prop.quads e1prop.next (nextQuad ());                              (* Backpatch e1.NEXT with nextQuad             *)
      let w = newTemp TYPE_int currScope in                                             (* Generate a new Temporary variable           *)
      let q = genQuad (bnToOp bn) e1prop.place e2prop.place (Entry w) in                (* Quad: bn, e1.place, e2.place, W             *)
      let prop = newProp TYPE_int in                                                    (* Generate a fresh Semantic Properties Object *)
      prop.place <- Entry w;                                                            (* PLACE = W                                   *)
      prop.quads <- e1prop.quads @ e2prop.quads @ [q];                                  (* Concat e1 and e2 Quads and add new Quad     *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_binop (e1, bn, e2) when List.mem bn [B_fplus; B_fminus; B_fmult; B_fdiv; B_pow] ->
      let e1prop = icodeExpr udt_env currScope false e1 in                              (* Semantic Properties of the Left Expr        *)
      let e2prop = icodeExpr udt_env currScope false e2 in                              (* Semantic Properties of the Right Expr       *)
      if (e1prop.trues <> []) && (e1prop.falses <> []) then                             (* If Expr e1 is a Cond                        *)
      begin
         backpatch e1prop.quads e1prop.next (nextQuad ());                              (* Backpatch e1.NEXT with nextQuad             *)
         e1prop.next <- [];                                                             (* Empty e1.NEXT                               *)
         condToExpr e1prop currScope                                                    (* Convert e1 to Expr                          *)
      end;
      if (e2prop.trues <> []) && (e2prop.falses <> []) then                             (* If Expr e2 is a Cond                        *)
      begin
         backpatch e2prop.quads e2prop.next (nextQuad ());                              (* Backpatch e2.NEXT with nextQuad             *)
         e2prop.next <- [];                                                             (* Empty e2.NEXT                               *)
         condToExpr e2prop currScope                                                    (* Convert e2 to Expr                          *)
      end;
      if e2prop.quads <> [] then                                                        (* If e2 has Quads                             *)
      begin
         let e2first = List.hd e2prop.quads in                                          (* Get the 1st Quad of e2                      *)
         backpatch e1prop.quads e1prop.next e2first.quad_tag;                           (* Backpatch e1.NEXT with e2first              *)
         backpatch e2prop.quads e2prop.next (nextQuad ())                               (* Backpatch e2.NEXT with nextQuad             *)
      end
      else                                                                              (* Else if e2 has no Quads                     *)
         backpatch e1prop.quads e1prop.next (nextQuad ());                              (* Backpatch e1.NEXT with nextQuad             *)
      let w = newTemp TYPE_float currScope in                                           (* Generate a new Temporary variable           *)
      let q = genQuad (bnToOp bn) e1prop.place e2prop.place (Entry w) in                (* Quad: bn, e1.place, e2.place, W             *)
      let prop = newProp TYPE_float in                                                  (* Generate a fresh Semantic Properties Object *)
      prop.place <- Entry w;                                                            (* PLACE = W                                   *)
      prop.quads <- e1prop.quads @ e2prop.quads @ [q];                                  (* Concat e1 and e2 Quads and add new Quad     *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_binop (e1, bn, e2) when List.mem bn [B_assign; B_ltgt; B_lt; B_gt; B_lteq; B_gteq; B_eq; B_neq] ->
      let e1prop = icodeExpr udt_env currScope false e1 in                              (* Semantic Properties of the Left Expr        *)
      let e2prop = icodeExpr udt_env currScope false e2 in                              (* Semantic Properties of the Right Expr       *)
      if (e1prop.trues <> []) && (e1prop.falses <> []) then                             (* If Expr e1 is a Cond                        *)
      begin
         backpatch e1prop.quads e1prop.next (nextQuad ());                              (* Backpatch e1.NEXT with nextQuad             *)
         e1prop.next <- [];                                                             (* Empty e1.NEXT                               *)
         condToExpr e1prop currScope                                                    (* Convert e1 to Expr                          *)
      end;
      if (e2prop.trues <> []) && (e2prop.falses <> []) then                             (* If Expr e2 is a Cond                        *)
      begin
         backpatch e2prop.quads e2prop.next (nextQuad ());                              (* Backpatch e2.NEXT with nextQuad             *)
         e2prop.next <- [];                                                             (* Empty e2.NEXT                               *)
         condToExpr e2prop currScope                                                    (* Convert e2 to Expr                          *)
      end;
      if e2prop.quads <> [] then                                                        (* If e2 has Quads                             *)
      begin
         let e2first = List.hd e2prop.quads in                                          (* Get the 1st Quad of e2                      *)
         backpatch e1prop.quads e1prop.next e2first.quad_tag;                           (* Backpatch e1.NEXT with e2first              *)
         backpatch e2prop.quads e2prop.next (nextQuad ())                               (* Backpatch e2.NEXT with nextQuad             *)
      end
      else                                                                              (* Else if e2 has no Quads                     *)
         backpatch e1prop.quads e1prop.next (nextQuad ());                              (* Backpatch e2.NEXT with nextQuad             *)
      let qt = genQuad (bnToOp bn) e1prop.place e2prop.place Star in                    (* Quad1: bn, e1.place, e2.place, *            *)
      let qf = genQuad Op_jump Empty Empty Star in                                      (* Quad2: jump, -, -, *                        *)
      let prop = newProp TYPE_bool in                                                   (* Generate a fresh Semantic Properties Object *)
      prop.trues <- [qt.quad_tag];                                                      (* TRUE = [Quad1]                              *)
      prop.falses <- [qf.quad_tag];                                                     (* FALSE = [Quad2]                             *)
      prop.quads <- e1prop.quads @ e2prop.quads @ [qt; qf];                             (* Concat e1 and e2 Quads and add new Quads    *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_binop (e1, B_conj, e2) ->
      let e1prop = icodeExpr udt_env currScope false e1 in                              (* Semantic Properties of the Left Expr        *)
      let e2prop = icodeExpr udt_env currScope false e2 in                              (* Semantic Properties of the Right Expr       *)
      if (e1prop.trues = []) && (e1prop.falses = []) then                               (* If Expr e1 is not a Cond                    *)
      begin
         backpatch e1prop.quads e1prop.next (nextQuad ());                              (* Backpatch e1.NEXT with nextQuad             *)
         e1prop.next <- [];                                                             (* Empty e1.NEXT                               *)
         exprToCond e1prop currScope                                                    (* Convert e1 to Cond                          *)
      end;
      if (e2prop.trues = []) && (e2prop.falses = []) then                               (* If Expr e2 is not a Cond                    *)
      begin
         backpatch e2prop.quads e2prop.next (nextQuad ());                              (* Backpatch e2.NEXT with nextQuad             *)
         e2prop.next <- [];                                                             (* Empty e2.NEXT                               *)
         exprToCond e2prop currScope                                                    (* Convert e2 to Cond                          *)
      end;
      let e2first = List.hd e2prop.quads in                                             (* Get the 1st Quad of e2                      *)
      backpatch e1prop.quads e1prop.next e2first.quad_tag;                              (* Backpatch e1.NEXT with e2first              *)
      backpatch e1prop.quads e1prop.trues e2first.quad_tag;                             (* Backpatch e1.TRUE with e2first              *)
      let prop = newProp TYPE_bool in                                                   (* Generate a fresh Semantic Properties Object *)
      prop.next <- e2prop.next;                                                         (* NEXT = e2.NEXT                              *)
      prop.trues <- e2prop.trues;                                                       (* TRUE = e2.TRUE                              *)
      prop.falses <- listMerge e1prop.falses e2prop.falses;                             (* FALSE = merge e1.FALSE e2.FALSE             *)
      prop.quads <- e1prop.quads @ e2prop.quads;                                        (* Concat the Quads of e1 and e2               *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_binop (e1, B_disj, e2) ->
      let e1prop = icodeExpr udt_env currScope false e1 in                              (* Semantic Properties of the Left Expr        *)
      let e2prop = icodeExpr udt_env currScope false e2 in                              (* Semantic Properties of the Right Expr       *)
      if (e1prop.trues = []) && (e1prop.falses = []) then                               (* If Expr e1 is not a Cond                    *)
      begin
         backpatch e1prop.quads e1prop.next (nextQuad ());                              (* Backpatch e1.NEXT with nextQuad             *)
         e1prop.next <- [];                                                             (* Empty e1.NEXT                               *)
         exprToCond e1prop currScope                                                    (* Convert e1 to Cond                          *)
      end;
      if (e2prop.trues = []) && (e2prop.falses = []) then                               (* If Expr e2 is not a Cond                    *)
      begin
         backpatch e2prop.quads e2prop.next (nextQuad ());                              (* Backpatch e2.NEXT with nextQuad             *)
         e2prop.next <- [];                                                             (* Empty e2.NEXT                               *)
         exprToCond e2prop currScope                                                    (* Convert e2 to Cond                          *)
      end;
      let e2first = List.hd e2prop.quads in                                             (* Get the 1st Quad of e2                      *)
      backpatch e1prop.quads e1prop.next e2first.quad_tag;                              (* Backpatch e1.NEXT with e2first              *)
      backpatch e1prop.quads e1prop.falses e2first.quad_tag;                            (* Backpatch e1.FALSE with e2first             *)
      let prop = newProp TYPE_bool in                                                   (* Generate a fresh Semantic Properties Object *)
      prop.next <- e2prop.next;                                                         (* NEXT = e2.NEXT                              *)
      prop.falses <- e2prop.falses;                                                     (* FALSE = e2.FALSE                            *)
      prop.trues <- listMerge e1prop.trues e2prop.trues;                                (* TRUE = merge e1.TRUE e2.TRUE                *)
      prop.quads <- e1prop.quads @ e2prop.quads;                                        (* Concat the Quads of e1 and e2               *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_binop (e1, B_semic, e2) ->
      let e1prop = icodeExpr udt_env currScope true e1 in                               (* Semantic Properties of the Left Expr        *)
      let e2prop = icodeExpr udt_env currScope stmt_flag e2 in                          (* Semantic Properties of the Right Expr       *)
      if (e1prop.trues <> []) && (e1prop.falses <> []) then                             (* If Expr e1 is a Cond                        *)
      begin
         backpatch e1prop.quads e1prop.next (nextQuad ());                              (* Backpatch e1.NEXT with nextQuad             *)
         e1prop.next <- [];                                                             (* Empty e1.NEXT                               *)
         condToExpr e1prop currScope                                                    (* Convert e1 to Expr                          *)
      end;
      if (e2prop.trues <> []) && (e2prop.falses <> []) then                             (* If Expr e2 is a Cond                        *)
      begin
         backpatch e2prop.quads e2prop.next (nextQuad ());                              (* Backpatch e2.NEXT with nextQuad             *)
         e2prop.next <- [];                                                             (* Empty e2.NEXT                               *)
         condToExpr e2prop currScope                                                    (* Convert e2 to Expr                          *)
      end;
      let prop = newProp e2prop.etype in                                                (* Generate a fresh Semantic Properties Object *)
      if e2prop.quads <> [] then                                                        (* If e2 has Quads                             *)
      begin
         let e2first = List.hd e2prop.quads in                                          (* Get the 1st Quad of e2                      *)
         backpatch e1prop.quads e1prop.next e2first.quad_tag;                           (* Backpatch e1.NEXT with e2first              *)
         prop.next <- e2prop.next                                                       (* NEXT = e2.NEXT                              *)
      end
      else                                                                              (* Else if e2 has no Quads                     *)
         prop.next <- e1prop.next;                                                      (* NEXT = e1.NEXT                              *)
      prop.place <- e2prop.place;                                                       (* PLACE = W                                   *)
      prop.quads <- e1prop.quads @ e2prop.quads;                                        (* Concat e1 and e2 Quads                      *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_binop (e1, B_refassign, e2) ->
      let e1prop = icodeExpr udt_env currScope false e1 in                              (* Semantic Properties of the Left Expr        *)
      let e2prop = icodeExpr udt_env currScope false e2 in                              (* Semantic Properties of the Right Expr       *)
      if (e1prop.trues <> []) && (e1prop.falses <> []) then                             (* If Expr e1 is a Cond                        *)
      begin
         backpatch e1prop.quads e1prop.next (nextQuad ());                              (* Backpatch e1.NEXT with nextQuad             *)
         e1prop.next <- [];                                                             (* Empty e1.NEXT                               *)
         condToExpr e1prop currScope                                                    (* Convert e1 to Expr                          *)
      end;
      if (e2prop.trues <> []) && (e2prop.falses <> []) then                             (* If Expr e2 is a Cond                        *)
      begin
         backpatch e2prop.quads e2prop.next (nextQuad ());                              (* Backpatch e2.NEXT with nextQuad             *)
         e2prop.next <- [];                                                             (* Empty e2.NEXT                               *)
         condToExpr e2prop currScope                                                    (* Convert e2 to Expr                          *)
      end;
      if e2prop.quads <> [] then                                                        (* If e2 has Quads                             *)
      begin
         let e2first = List.hd e2prop.quads in                                          (* Get the 1st Quad of e2                      *)
         backpatch e1prop.quads e1prop.next e2first.quad_tag;                           (* Backpatch e1.NEXT with e2first              *)
         backpatch e2prop.quads e2prop.next (nextQuad ())                               (* Backpatch e2.NEXT with nextQuad             *)
      end
      else                                                                              (* Else if e2 has no Quads                     *)
         backpatch e1prop.quads e1prop.next (nextQuad ());                              (* Backpatch e1.NEXT with nextQuad             *)
      let q = 
         genQuad Op_assign e2prop.place Empty (Deref (e1prop.place, e2prop.etype)) in   (* Quad: :=, e2.place, -, [e1.place]           *)
      let prop = newProp TYPE_unit in                                                   (* Generate a fresh Semantic Properties Object *)
      prop.quads <- e1prop.quads @ e2prop.quads @ [q];                                  (* Concat e1 and e2 Quads and add new Quad     *)
      prop.place <- Unit;                                                               (* PLACE = Unit                                *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_binop _ -> (* To silence the warning *)
      let pos = getPosFromMsg expr.meta_ex "op_start" in
      iInternal "Icode: Guards failed to catch E_binop" (Some pos);
      raise Terminate
   | E_array (id, el) ->
      let (en, et, _) = getArrayTypeFromEntry expr.entry_ex in                          (* Get Array Symbol Entry and Type             *)
      let elprop = List.map (fun e -> icodeExpr udt_env currScope false e) el in        (* Semantic Properties Objects of the Exprs    *)
      let icodeOne pl e =                                                               (* Function to handle an Inner Expr e          *)
         backpatch e.quads e.next (nextQuad ());                                        (* Backpatch e.NEXT with nextQuad              *)
         e.next <- [];                                                                  (* Empty e.NEXT                                *)
         let w = newTemp (TYPE_ref et) currScope in                                     (* Generate a new Temporary variable           *)
         let q = genQuad Op_array pl e.place (Entry w) in                               (* Quad: array, pl, e.PLACE, W                 *)
         e.quads <- e.quads @ [q];                                                      (* Add the new Quad                            *)
         e.place <- Entry w;                                                            (* PLACE = W                                   *)
         e.place in                                                                     (* Return PLACE                                *)
      let last_place = List.fold_left icodeOne (Entry en) elprop in                     (* Fold the list, get the last one's place     *)
      let all_quads = List.flatten (List.map (fun pr -> pr.quads) elprop) in            (* Concat all Inner Exprs' Quads               *)
      let prop = newProp (TYPE_ref et) in                                               (* Generate a fresh Semantic Properties Object *)
      prop.place <- last_place;                                                         (* PLACE = last expr's place                   *)
      prop.quads <- all_quads;                                                          (* Store all the Quads                         *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_dim (il, id) ->
      let pos = getPosFromMsg expr.meta_ex "id_name_start" in                           (* Locate the Expr in the Source File          *)
      (match il, expr.entry_ex with
       | [], Some en ->                                                                 (* Case1: dim x                                *)
         let w = newTemp TYPE_int currScope in                                          (* Generate a new Temporary variable           *)
         let q = genQuad Op_dim (Entry en) (Int 1) (Entry w) in                         (* Quad: dim, id, 1, W                         *)
         let prop = newProp TYPE_int in                                                 (* Generate a fresh Semantic Properties Object *)
         prop.place <- Entry w;                                                         (* PLACE = W                                   *)
         prop.quads <- [q];                                                             (* Add the new Quad                            *)
         prop                                                                           (* Return the Semantic Properties Object       *)
       | h::t, Some en ->                                                               (* Case2: dim i x                              *)
         let w = newTemp TYPE_int currScope in                                          (* Generate a new Temporary variable           *)
         let q = genQuad Op_dim (Entry en) (Int h) (Entry w) in                         (* Quad: dim, id, h, W                         *)
         let prop = newProp TYPE_int in                                                 (* Generate a fresh Semantic Properties Object *)
         prop.place <- Entry w;                                                         (* PLACE = W                                   *)
         prop.quads <- [q];                                                             (* Add the new Quad                            *)
         prop                                                                           (* Return the Semantic Properties Object       *)
       | _, None ->
         iInternal "Icode: Didn't find Symbol Table Entry for E_dim" (Some pos);
         raise Terminate
      )
   | E_new et ->
      let tt = T.typ_conversion et None (Some user_types) in                            (* Convert Ast.ast_type_node to Types.typ      *)
      let w = newTemp (TYPE_ref tt) currScope in                                        (* Generate a new Temporary variable           *)
      let qp = genQuad Op_par (Int (sizeOfType tt)) (PassType V) Empty in               (* Quad1: par, sizeOfType, V, -                *)
      let qr = genQuad Op_par (Entry w) (PassType RET) Empty in                         (* Quad2: par, W, RET, -                       *)
      let qc = genQuad Op_call Empty Empty (Str "_new") in                              (* Quad3: call, -, -, _new                     *)
      let prop = newProp (TYPE_ref tt) in                                               (* Generate a fresh Semantic Properties Object *)
      prop.place <- Entry w;                                                            (* PLACE = W                                   *)
      prop.quads <- [qp; qr; qc];                                                       (* Add the new Quads                           *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_del e ->
      let eprop = icodeExpr udt_env currScope false e in                                (* Semantic Properties of the Expr e           *)
      if (eprop.trues <> []) || (eprop.falses <> []) then                               (* If e is a Cond                              *)
      begin
         backpatch eprop.quads eprop.next (nextQuad ());                                (* Backpatch e.NEXT with nextQuad              *)
         eprop.next <- [];                                                              (* Empty e.NEXT                                *)
         condToExpr eprop currScope                                                     (* Convert e to Expr                           *)
      end;
      backpatch eprop.quads eprop.next (nextQuad ());                                   (* Backpatch e.NEXT with newQuad               *)
      let qp = genQuad Op_par eprop.place (PassType V) Empty in                         (* Quad1: par, e.PLACE, V, -                   *)
      let qc = genQuad Op_call Empty Empty (Str "_delete") in                           (* Quad2: call, -, -, _delete                  *)
      let prop = newProp TYPE_unit in                                                   (* Generate a fresh Semantic Properties Object *)
      prop.place <- Unit;                                                               (* PLACE = Unit                                *)
      prop.quads <- eprop.quads @ [qp; qc];                                             (* Add the new Quads                           *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_in (lt, e) ->
      let ltquads = icodeLetdef udt_env lt in                                           (* Quads of the Letdef lt                      *)
      let eprop = icodeExpr udt_env currScope false e in                                (* Semantic Properties of the Expr e           *)
      eprop.quads <- ltquads @ eprop.quads;                                             (* Concat lt and e Quads                       *)
      eprop                                                                             (* Return the Semantic Properties Object of e  *)
   | E_begin e ->
      icodeExpr udt_env currScope stmt_flag e                                           (* Generate Icode for the Inner Expr           *)
   | E_if (e, e1) ->
      let eprop = icodeExpr udt_env currScope false e in                                (* Semantic Properties of the Expr e           *)
      let e1prop = icodeExpr udt_env currScope false e1 in                              (* Semantic Properties of the Expr e1          *)
      if (eprop.trues = []) && (eprop.falses = []) then                                 (* If e is not a Cond                          *)
      begin
         backpatch eprop.quads eprop.next (nextQuad ());                                (* Backpatch e.NEXT with nextQuad              *)
         eprop.next <- [];                                                              (* Empty e.NEXT                                *)
         exprToCond eprop currScope                                                     (* Convert e to Cond                           *)
      end;
      let prop = newProp TYPE_unit in                                                   (* Generate a fresh Semantic Properties Object *)
      if (e1prop.quads <> []) then                                                      (* If e1 has Quads                             *)
      begin
         let e1first = List.hd e1prop.quads in                                          (* Get the first Quad of e1                    *)
         backpatch eprop.quads eprop.trues e1first.quad_tag;                            (* Backpatch e.TRUE with e1first               *)
         backpatch eprop.quads eprop.next e1first.quad_tag;
         prop.next <- listMerge eprop.falses e1prop.next                                (* NEXT = merge e.FALSE e1.NEXT                *)
      end
      else                                                                              (* Else if e1 has no Quads                     *)
         prop.next <- listMerge (listMerge eprop.falses eprop.trues) eprop.next;        (* NEXT = merge e.FALSE e.TRUE                 *)
      prop.quads <- eprop.quads @ e1prop.quads;                                         (* Concat e and e1 Quads                       *)
      prop.place <- Unit;                                                               (* PLACE = Unit                                *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_ifelse (e, e1, e2) ->
      let eprop = icodeExpr udt_env currScope false e in                                (* Semantic Properties of the Expr e           *)
      let e1prop = icodeExpr udt_env currScope false e1 in                              (* Semantic Properties of the Expr e1          *)
      let e2prop = icodeExpr udt_env currScope false e2 in                              (* Semantic Properties of the Expr e2          *)
      if (eprop.trues = []) && (eprop.falses = []) then                                 (* If e is not a Cond                          *)
      begin
         backpatch eprop.quads eprop.next (nextQuad ());                                (* Backpatch e.NEXT with nextQuad              *)
         eprop.next <- [];                                                              (* Empty e.NEXT                                *)
         exprToCond eprop currScope                                                     (* Convert e to Cond                           *)
      end;
      let q = genQuad Op_jump Empty Empty Star in                                       (* Quad: jump, -, -, *                         *)
      let prop = newProp e1prop.etype in                                                (* Generate a fresh Semantic Properties Object *)
      if not stmt_flag then                                                             (* If we need the PLACE                        *)
      begin
         let w = newTemp e1prop.etype currScope in                                      (* Generate a new Temporary variable           *)
         let q1 = genQuad Op_assign e1prop.place Empty (Entry w) in                     (* Quad1: :=, e1.PLACE, -, W                   *)
         backpatch e1prop.quads e1prop.next q1.quad_tag;                                (* Backpatch e1.NEXT with Quad1                *)
         e1prop.next <- [];                                                             (* Empty e1.NEXT                               *)
         e1prop.quads <- e1prop.quads @ [q1];                                           (* Add Quad1 to e1.Quads                       *)
         let q2 = genQuad Op_assign e2prop.place Empty (Entry w) in                     (* Quad2: :=, e2.PLACE, -, W                   *)
         backpatch e2prop.quads e2prop.next q2.quad_tag;                                (* Backpatch e2.NEXT with Quad2                *)
         e2prop.next <- [];                                                             (* Empty e2.NEXT                               *)
         e2prop.quads <- e2prop.quads @ [q2];                                           (* Add Quad2 to e2.Quads                       *)
         prop.place <- Entry w;                                                         (* PLACE = W                                   *)
      end;
      prop.next <- listMerge (q.quad_tag::e1prop.next) e2prop.next;                     (* NEXT = merge e1.NEXT e2.NEXT Quad           *)
      if e1prop.quads <> [] then                                                        (* If e1 has Quads                             *)
         begin
            let e1first = List.hd e1prop.quads in                                       (* Get the 1st Quad of e1                      *)
            backpatch eprop.quads eprop.trues e1first.quad_tag                          (* Backpatch e.TRUE with e1first               *)
         end
      else                                                                              (* Else if e1 has no Quads                     *)
         prop.next <- listMerge prop.next eprop.trues;                                  (* Add e.TRUE to NEXT                          *)
      if e2prop.quads <> [] then                                                        (* If e2 has Quads                             *)
         begin
            let e2first = List.hd e2prop.quads in                                       (* Get the 1st Quad of e2                      *)
            backpatch eprop.quads eprop.falses e2first.quad_tag                         (* Backpatch e.FALSE with e2first              *)
         end
      else                                                                              (* Else if e2 has no Quads                     *)
         prop.next <- listMerge prop.next eprop.falses;                                 (* Add e.FALSE to NEXT                         *)
      prop.quads <- eprop.quads @ e1prop.quads @ [q] @ e2prop.quads;                    (* Concat e, e1, e2 Quads and add new Quad     *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_while (e, e1) ->
      let eprop = icodeExpr udt_env currScope false e in                                (* Semantic Properties of the Expr e           *)
      let e1prop = icodeExpr udt_env currScope false e1 in                              (* Semantic Properties of the Expr e1          *)
      if (eprop.trues = []) && (eprop.falses = []) then                                 (* If e is not a Cond                          *)
      begin
         backpatch eprop.quads eprop.next (nextQuad ());                                (* Backpatch e.NEXT with nextQuad              *)
         eprop.next <- [];                                                              (* Empty e.NEXT                                *)
         exprToCond eprop currScope                                                     (* Convert e to Cond                           *)
      end;
      let efirst = List.hd eprop.quads in                                               (* Get the 1st Quad of e                       *)
      let q = genQuad Op_jump Empty Empty (Label efirst.quad_tag) in                    (* Quad: jump, -, -, efirst                    *)
      backpatch e1prop.quads e1prop.next efirst.quad_tag;                               (* Backpatch e1.NEXT with efirst               *)
      if e1prop.quads <> [] then                                                        (* If e1 has Quads                             *)
      begin
         let e1first = List.hd e1prop.quads in                                          (* Get the 1st Quad of e1                      *)
         backpatch eprop.quads eprop.trues e1first.quad_tag                             (* Backpatch e.TRUE with e1first               *)
      end
      else                                                                              (* Else if e1 has no Quads                     *)
         backpatch eprop.quads eprop.trues efirst.quad_tag;                             (* Backpatch e.FALSE with e1first              *)
      let prop = newProp TYPE_unit in                                                   (* Generate a fresh Semantic Properties Object *)
      prop.place <- Unit;                                                               (* PLACE = Unit                                *)
      prop.next <- eprop.falses;                                                        (* NEXT = e.FALSE                              *)
      prop.quads <- eprop.quads @ e1prop.quads @ [q];                                   (* Concat e and e1 Quads and add the new Quad  *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | E_for (id, e1, lt, e2, e3) ->
      let pos = getPosFromMsg expr.meta_ex "id_name_start" in
      (match expr.entry_ex with
       | None ->
         iInternal "Icode: Didn't find Symbol Entry for counter Var in for" (Some pos);
         raise Terminate
       | Some en ->
         let e1prop = icodeExpr udt_env currScope false e1 in                           (* Semantic Properties of the Expr e1          *)
         let e2prop = icodeExpr udt_env currScope false e2 in                           (* Semantic Properties of the Expr e2          *)
         let e3prop = icodeExpr udt_env currScope false e3 in                           (* Semantic Properties of the Expr e3          *)
         backpatch e1prop.quads e1prop.next (nextQuad ());                              (* Backpatch e1.NEXT with nextQuad             *)
         let qb = genQuad Op_assign e1prop.place Empty (Entry en) in                    (* Quad1: :=, e1.PLACE, -, i                   *)
         backpatch e2prop.quads e2prop.next (nextQuad ());                              (* Backpatch e2.NEXT with nextQuad             *)
         let w = newTemp TYPE_int currScope in                                          (* Generate new Temporary variable             *)
         let qe = genQuad Op_assign e2prop.place Empty (Entry w) in                     (* Quad2: :=, e2.PLACE, -, W                   *)
         let prop = newProp TYPE_unit in                                                (* Generate a fresh Semantic Properties Object *)
         (match lt with
          | L_to ->                                                                     (* If it's a 'to' for-loop                     *)
            let qc = genQuad Op_gt (Entry en) (Entry w) Star in                         (* Quad3: <, i, W, *                           *)
            let qUP = genQuad Op_plus (Entry en) (Int 1) (Entry en) in                  (* Quad4: +, i, 1, i                           *)
            backpatch e3prop.quads e3prop.next qUP.quad_tag;                            (* Backpatch e3.NEXT with Quad3                *)
            let qj = genQuad Op_jump Empty Empty (Label qc.quad_tag) in                 (* Quad5: jump, -, -, Quad3                    *)
            prop.place <- Unit;                                                         (* PLACE = Unit                                *)
            prop.next <- [qc.quad_tag];                                                 (* NEXT = [Quad3]                              *)
            prop.quads <-                                                               (* Concat e1, e2, e3 and new Quads             *)
               e1prop.quads @ [qb] @ e2prop.quads @ [qe; qc] @ e3prop.quads @ [qUP; qj];
            prop                                                                        (* Return the Semantic Properties Object       *)
          | L_downto ->                                                                 (* If it's a 'downto' for-loop                 *)
            let qc = genQuad Op_lt (Entry en) (Entry w) Star in                         (* Quad3: <, i, W, *                           *)
            let qDOWN = genQuad Op_minus (Entry en) (Int 1) (Entry en) in               (* Quad4: -, i, 1, i                           *)
            backpatch e3prop.quads e3prop.next qDOWN.quad_tag;                          (* Backpatch e3.NEXT with Quad3                *)
            let qj = genQuad Op_jump Empty Empty (Label qc.quad_tag) in                 (* Quad5: jump, -, -, Quad3                    *)
            prop.place <- Unit;                                                         (* PLACE = Unit                                *)
            prop.next <- [qc.quad_tag];                                                 (* NEXT = [Quad3]                              *)
            prop.quads <-                                                               (* Concat e1, e2, e3 and new Quads             *)
               e1prop.quads @ [qb] @ e2prop.quads @ [qe; qc] @ e3prop.quads @ [qDOWN; qj];
            prop                                                                        (* Return the Semantic Properties Object       *)
         )
      )
   | E_match (e, cl) ->
      let eprop = icodeExpr udt_env currScope false e in                                (* Semantic Properties of the Expr e           *)
      let clprops = 
         List.map (fun c -> icodeClause udt_env currScope eprop.place c) cl in          (* Semantic Properties of all the clauses      *)
      let w = newTemp expr.matchType_ex currScope in                                    (* Generate new Temporary for match result     *)
      let addQuads c =                                                                  (* Fun to add 2 new Quads to each clause Quads *)
         backpatch c.quads c.next (nextQuad ());                                        (* Backpatch c.NEXT with nextQuad              *)
         backpatch c.quads c.trues (nextQuad ());                                       (* Backpatch c.TRUE with nextQuad              *)
         let q = genQuad Op_assign c.place Empty (Entry w) in                           (* Quad1: :=, c.PLACE, -, W                    *)
         let qj = genQuad Op_jump Empty Empty Star in                                   (* Quad2: jump, -, -, *                        *)
         c.next <- [qj.quad_tag];                                                       (* c.NEXT = [Quad2]                            *)
         c.quads <- c.quads @ [q; qj] in                                                (* Add new Quads                               *)
      List.iter addQuads clprops;                                                       (* Map addQuads to clause list                 *)
      let bpatch c lbl_opt =                                                            (* Fun to backpatch FALSE list of all clauses  *)
         (match lbl_opt with
          | Some lbl ->                                                                 (* Any clause but the last                     *)
            backpatch c.quads c.falses lbl;                                             (* Backpatch c.FALSE with lbl                  *)
            let qfirst = List.hd c.quads in                                             (* Find the first quad of c                    *)
            Some qfirst.quad_tag                                                        (* Return it so next object can be backpatched *)
          | None ->                                                                     (* The last clause                             *)
            let qfirst = List.hd c.quads in                                             (* Find the first quad of c                    *)
            Some qfirst.quad_tag                                                        (* Return it so next object can be backpatched *)
         ) in
      ignore (List.fold_right bpatch clprops None);                                     (* Right fold the clause list with bpatch      *)
      let clLast = List.hd (List.rev clprops) in                                        (* Get the Semantic Object of the last clause  *)
      let cl_quads = List.flatten (List.map (fun c -> c.quads) clprops) in              (* Get all clause quads                        *)
      let cl_nexts = List.flatten (List.map (fun c -> c.next) clprops) in               (* Concat the NEXT of all clauses              *)
      let prop = newProp expr.matchType_ex in                                           (* Generate a fresh Semantic Properties Object *)
      prop.place <- Entry w;                                                            (* PLACE = W                                   *)
      prop.next <- listMerge cl_nexts clLast.falses;                                    (* NEXT = all clause NEXT and clLast.FALSE     *)
      prop.quads <- eprop.quads @ cl_quads;                                             (* Concat the Quads of e and cls               *)
      prop                                                                              (* Return the Semantic Properties Object       *)
      
  (* Translate an ast_clause_node to Icode *)
and icodeClause udt_env currScope matched_expr cl =
   match cl.tag_cl with
   | (pat, e) ->
      let patprop = icodePattern udt_env currScope (Some matched_expr) pat in           (* Semantic Properties of the pattern p        *)
      let eprop = icodeExpr udt_env currScope false e in                                (* Semantic Properties of the expression e     *)
      if (eprop.trues <> []) && (eprop.falses <> []) then                               (* If e is a Cond                              *)
      begin
         backpatch eprop.quads eprop.next (nextQuad ());                                (* Backpatch e.NEXT with nextQuad              *)
         eprop.next <- [];                                                              (* Empty e.NEXT                                *)
         condToExpr eprop currScope                                                     (* Convert e to Expr                           *)
      end;
      if eprop.quads <> [] then                                                         (* If e has Quads                              *)
      begin
         let efirst = List.hd eprop.quads in                                            (* Find the first Quad                         *)
         backpatch patprop.quads patprop.trues efirst.quad_tag                          (* Backpatch pat.TRUE with efirst              *)
      end;
      let prop = newProp eprop.etype in                                                 (* Generate a fresh Semantic Properties Object *)
      prop.place <- eprop.place;                                                        (* PLACE = e.PLACE                             *)
      prop.trues <- patprop.trues;                                                      (* TRUE = pat.TRUE - for empty e.quads         *)
      prop.falses <- patprop.falses;                                                    (* FALSE = pat.FALSE                           *)
      prop.next <- eprop.next;                                                          (* NEXT = e.NEXT                               *)
      prop.quads <- patprop.quads @ eprop.quads;                                        (* Concat Quads                                *)
      prop                                                                              (* Return the Semantic Properties Object       *)

  (* Translate an ast_pattern_node to Icode *)
and icodePattern udt_env currScope matched_expr_opt pat =
   let pos = getPosFromMsg pat.meta_pt "pat_name_start" in                              (* Locate the Pattern in the Source File       *)
   match pat.tag_pt with
   | P_int (sgn, i) ->
      let prop = newProp TYPE_int in                                                    (* Generate a fresh Semantic Properties Object *)
      (match sgn with
       | S_plus | Unsigned ->                                                           (* Case1: + pat / pat                          *)
         prop.place <- Int i;                                                           (* PLACE = i                                   *)
         prop                                                                           (* Return the Semantic Properties Object       *)
       | S_minus ->                                                                     (* Case2: - pat                                *)
         let w = newTemp TYPE_int currScope in                                          (* Generate a new Temporary variable           *)
         let q = genQuad Op_minus (Int i) Empty (Entry w) in                            (* Quad: -, i, -, W                            *)
         prop.place <- Entry w;                                                         (* PLACE = W                                   *)
         prop.quads <- [q];                                                             (* Add the new Quad                            *)
         prop                                                                           (* Return the Semantic Properties Object       *)
       | _ ->
         iInternal "Icode: Invalid sgn for P_int" (Some pos);
         raise Terminate
      )
   | P_real (sgn, x) ->
      let prop = newProp TYPE_float in                                                  (* Generate a fresh Semantic Properties Object *)
      (match sgn with
       | S_fplus | Unsigned ->                                                          (* Case1: +. pat / pat                         *)
         prop.place <- Float x;                                                         (* PLACE = x                                   *)
         prop                                                                           (* Return the Semantic Properties Object       *)
       | S_fminus ->                                                                    (* Case2: -. pat                               *)
         let w = newTemp TYPE_float currScope in                                        (* Generate a new Temporary variable           *)
         let q = genQuad Op_fminus (Float x) Empty (Entry w) in                         (* Quad: -., x, -, W                           *)
         prop.place <- Entry w;                                                         (* PLACE = W                                   *)
         prop.quads <- [q];                                                             (* Add the new Quad                            *)
         prop                                                                           (* Return the Semantic Properties Object       *)
       | _ ->
         iInternal "Icode: Invalid sgn for P_real" (Some pos);
         raise Terminate
      )
   | P_char c ->
      let prop = newProp TYPE_char in                                                   (* Generate a fresh Semantic Properties Object *)
      prop.place <- Chr c;                                                              (* PLACE = c                                   *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | P_bool b ->
      let prop = newProp TYPE_bool in                                                   (* Generate a fresh Semantic Properties Object *)
      prop.place <- Bool b;                                                             (* PLACE = b                                   *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | P_id id ->
      (match !(id.ptype), id.pentry with
       | Some et, Some en ->
         let tt = T.typ_conversion et None (Some user_types) in                         (* Convert ast_type_node to Types.typ          *)
         let prop = newProp tt in                                                       (* Generate a fresh Semantic Properties Object *)
         prop.place <- Entry en;                                                        (* PLACE = id                                  *)
         (match matched_expr_opt with
          | None ->                                                                     (* If it's not a catch-all clause              *)
            ()                                                                          (* Do nothing                                  *)
          | Some e ->                                                                   (* If it's a catch all clause                  *)
            let q = genQuad Op_assign e Empty (Entry en) in                             (* Quad: :=, e, -, id                          *)
            prop.quads <- [q]                                                           (* Add the new Quad                            *)
         );
         prop                                                                           (* Return the Semantic Properties Object       *)
       | _ ->
         iInternal "Icode: Missing ptype or pentry" (Some pos);
         raise Terminate
      )
   | P_constr (id, patList) ->
      let (en, tname, _) = List.assoc id udt_env in 
      let prop = newProp (TYPE_userdef tname) in                                        (* Generate a fresh Semantic Properties Object *)
      (match matched_expr_opt with
       | Some e ->                                                                      (* If it's the outer Match                     *)
         let patprops = 
            List.map (fun p -> icodePattern udt_env currScope None p) patList in        (* Semantic Properties of the parameters       *)
         let icodeOne i p =                                                             (* Fun to handle a parameter p                 *)
            let q = genQuad Op_constr e (Int i) p.place in                              (* Quad: constr, e, offset, p.PLACE            *)
            p.quads <- q::p.quads;                                                      (* Add the new Quad at the head of the list    *)
            i - (sizeOfType p.etype) in                                                 (* Return the offset of the next parameter     *)
         ignore (List.fold_left icodeOne 
                     (0 - (sizeOfType (TYPE_array (TYPE_char, 1)))) patprops);          (* Left fold the params with initial offset    *)
         let pat_quads = List.flatten (List.map (fun p -> p.quads) patprops) in         (* Quads of all the parameters                 *)
         let pat_falses = List.flatten (List.map (fun p -> p.falses) patprops) in       (* Concat the FALSE of the parameters          *)
         let qm = genQuad Op_match e (Str id) Star in                                   (* Quad1: match, e, constr_name, *             *)
         if pat_quads <> [] then                                                        (* If the parameters have Quads                *)
         begin
            let firstPat = List.hd pat_quads in                                         (* Find the 1st Quad of the parameters         *)
            qm.quad_argZ <- Label firstPat.quad_tag                                     (* Backpatch Quad1 with firstPat               *)
         end
         else                                                                           (* Else if the parameters have no Quads        *)
            prop.trues <- [qm.quad_tag];                                                (* TRUE = [Quad1]                              *)
         let qj = genQuad Op_jump Empty Empty Star in                                   (* Quad2: jump, -, -, *                        *)
         prop.falses <- qj.quad_tag::pat_falses;                                        (* FALSE = Quad2::pat.FALSE                    *)
         prop.place <- e;                                                               (* PLACE = e                                   *)
         prop.quads <- [qm; qj] @ pat_quads;                                            (* Add the new Quads                           *)
         prop                                                                           (* Return the Semantic Properties Object       *)
       | None ->                                                                        (* If it's an inner Match                      *)
         let w = newTemp (TYPE_userdef tname) currScope in                              (* Generate a new Temporarty variable          *)
         let patprops = 
            List.map (fun p -> icodePattern udt_env currScope None p) patList in        (* Semantic Properties of the parameters       *)
         let icodeOne i p =                                                             (* Fun to handle a parameter p                 *)
            let q = genQuad Op_constr (Entry w) (Int i) p.place in                      (* Quad: constr, W, offset, p.PLACE            *)
            p.quads <- q::p.quads;                                                      (* Add the new Quad at the head of the list    *)
            i - (sizeOfType p.etype) in                                                 (* Return the offset of the next parameter     *)
         ignore (List.fold_left icodeOne 
                     (0 - (sizeOfType (TYPE_array (TYPE_char, 1)))) patprops);          (* Left fold the params with initial offset    *)
         let pat_quads = List.flatten (List.map (fun p -> p.quads) patprops) in         (* Quads of all the parameters                 *)
         let pat_falses = List.flatten (List.map (fun p -> p.falses) patprops) in       (* Concat the FALSE of the parameters          *)
         let qm = genQuad Op_match (Entry w) (Str id) Star in                           (* Quad1: match, W, constr_name, *             *)
         if pat_quads <> [] then                                                        (* If the parameters have Quads                *)
         begin
            let firstPat = List.hd pat_quads in                                         (* Find the 1st Quad of the parameters         *)
            qm.quad_argZ <- Label firstPat.quad_tag                                     (* Backpatch Quad1 with firstPat               *)
         end
         else                                                                           (* Else if the parameters have no Quads        *)
            prop.trues <- [qm.quad_tag];                                                (* TRUE = [Quad1]                              *)
         let qj = genQuad Op_jump Empty Empty Star in                                   (* Quad2: jump, -, -, *                        *)
         prop.falses <- qj.quad_tag::pat_falses;                                        (* FALSE = Quad2::pat.FALSE                    *)
         prop.place <- Entry w;                                                         (* PLACE = W                                   *)
         prop.quads <- [qm; qj] @ pat_quads;                                            (* Add the new Quads                           *)
         prop                                                                           (* Return the Semantic Properties Object       *)
      )
   

  (* Translate an ast_def_node to Icode *)
and icodeDef udt_env df =
match df.tag_df, df.entry_df with
   | Def_func (id, [], t, e), Some en ->  (* Case of Variable *)
      let eprop = icodeExpr udt_env df.scope_df false e in                              (* Semantic Properties of the Inner Expr       *)
      if (eprop.trues <> []) && (eprop.falses <> []) then                               (* If e is a Cond                              *)
      begin
         backpatch eprop.quads eprop.next (nextQuad ());                                (* Backpatch e.NEXT with nextQuad              *)
         eprop.next <- [];                                                              (* Empty e.NEXT                                *)
         condToExpr eprop df.scope_df                                                   (* Convert e to Expr                           *)
      end;
      let prop = newProp eprop.etype in                                                 (* Generate a fresh Semantic Properties Object *)
      let q = genQuad Op_assign eprop.place Empty (Entry en) in                         (* Quad: :=, e.PLACE, -, id                    *)
      prop.quads <- eprop.quads @ [q];                                                  (* Add the new Quad                            *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | Def_func (id, parList, t, e), Some en ->  (* Case of function *)
      let qs = genQuad Op_unit (Entry en) Empty Empty in                                (* Quad1: unit, func, -, -,                    *)
      let eprop = icodeExpr udt_env df.scope_df false e in                              (* Semantc Properties of the Inner Expr        *)
      if (eprop.trues <> []) && (eprop.falses <> []) then                               (* If e is a Cond                              *)
      begin
         backpatch eprop.quads eprop.next (nextQuad ());                                (* Backpatch e.NEXT with nextQuad              *)
         eprop.next <- [];                                                              (* Empty e.NEXT                                *)
         condToExpr eprop df.scope_df                                                   (* Convert e to Expr                           *)
      end;
      backpatch eprop.quads eprop.next (nextQuad ());                                   (* Backpatch e.NEXT with nextQuad              *)
      let prop = newProp eprop.etype in                                                 (* Generate a fresh Semantic Properties Object *)
      let q = genQuad Op_assign eprop.place Empty (FuncResult eprop.etype) in           (* Quad2: :=, e.PLACE, -, $$                   *)
      let qe = genQuad Op_endu (Entry en) Empty Empty in                                (* Quad3: endu, func, -, -                     *)
      let fun_quads = (qs::eprop.quads) @ [q; qe] in                                    (* Add the new Quads                           *)
      push fun_quads;                                                                   (* Push the Quads to the function stack        *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | Def_mut (id, [], t), Some en ->  (* Case of mutable *)
      newProp TYPE_none
   | Def_mut (id, el, t), Some en ->  (* Case of mutable / array *)
      let (_, tt, et) = getArrayTypeFromEntry df.entry_df in
      let elprop = List.map (fun e -> icodeExpr udt_env df.scope_df false e) el in      (* Semantic Properties Objects of the Exprs    *)
      let icodeOne e =                                                                  (* Function to handle an Inner Expr e          *)
         backpatch e.quads e.next (nextQuad ());                                        (* Backpatch e.NEXT with nextQuad              *)
         e.next <- [];                                                                  (* Empty e.NEXT                                *)
         let q = genQuad Op_par e.place (PassType V) Empty in                           (* Quad: par, e.PLACE, V, -                    *)
         e.quads <- e.quads @ [q] in                                                    (* Add the new Quad                            *)
      List.iter icodeOne elprop;                                                        (* Parse all mutable Parameters                *)
      let par_quads = List.flatten (List.map (fun p -> p.quads) elprop) in              (* Concat all Parameters' Quads                *)
      let qs = genQuad Op_par (Int (sizeOfType tt)) (PassType V) Empty in               (* Quad1: par, sizeof tt, V, -                 *)
      let qd = genQuad Op_par (Int (List.length el)) (PassType V) Empty in              (* Quad2: par, num_dims, V, -                  *)
      let qr = genQuad Op_par (Entry en) (PassType RET) Empty in                        (* Quad3: par, W, RET, -                       *)
      let qc = genQuad Op_call Empty Empty (Str "_make_array") in                       (* Quad4: call, -, -, _make_array              *)
      array_stack := en::!array_stack;                                                  (* Add the array ot the array stack            *)
      let prop = newProp et in                                                          (* Generate a fresh Semantic Properties Object *)
      prop.quads <- par_quads @ [qs; qd; qr; qc];                                       (* Add the new Quads                           *)
      prop                                                                              (* Return the Semantic Properties Object       *)
   | _, None ->
      let pos = getPosFromMsg df.meta_df "id_name_start" in
      iInternal "Icode: Didn't find Symbol Table Entry for Def" (Some pos);
      raise Terminate
      

  (* Translate an ast_letdef_node to Icode *)
and icodeLetdef udt_env ltdf = 
   try
      (match ltdf.tag_lt with
       | (_, defs) ->
         let props = List.map (fun df -> icodeDef udt_env df) defs in                   (* Semantic Properties Objects of the Defs     *)
         List.flatten (List.map (fun x -> x.quads) props)                               (* Concat all the Quads                        *)
      )
   with
   | UninitializedPlace pos ->
      iInternal "Icode: Inner Exression has Uninitialised PLACE" (Some pos);
      raise Terminate
      
  (* Generate Icode for every Constructor in UDT Table *)
let icodeUDT udt = 
   match udt with
   | (tname, cname, tlist) ->
      let n = List.length tlist in                                                      (* Number of Constructor Parameters         *)
      let ntlist = List.combine (listMake n) tlist in                                   (* Make an ordered list of Params           *)
      let entry = newFunction (id_make ("_udt_" ^ cname)) true (0,0) in                 (* Add Constr as func to the Symb Table     *)
      openScope ();                                                                     (* Open the Inner Scope                     *)
      let parList = List.map (fun (i, et) ->                                            (* Add the Constr's Parameters              *)
         newParameter (id_make ("p" ^ i)) et PASS_BY_VALUE entry true (0,0)) ntlist in
      ignore parList;
      endFunctionHeader entry (TYPE_userdef tname);                                     (* Return type = UDT                        *)
      let w = newTemporary (TYPE_userdef tname) !currentScope in                        (* Create a new Temporary                   *)
      let q_unit = genQuad Op_unit (UDT (entry, !currentScope)) Empty Empty in          (* Quad1: unit, _dt_cname, -, -             *)
      let alloc_size = maxUDTsize user_types tname in                                   (* Heap size needed for UDT Allocation      *)
      let q_par1 = genQuad Op_par (Int alloc_size) (PassType V) Empty in                (* Quad2: par, alloc_size, V, -             *)
      let q_par2 = genQuad Op_par (Entry w) (PassType RET) Empty in                     (* Quad3: par, W, RET, -                    *)
      let q_call = genQuad Op_call Empty Empty (Str "_alloc") in                        (* Quad4: call, -, -, _alloc                *)
      let q_ret = 
         genQuad Op_assign (Entry w) Empty (FuncResult (TYPE_userdef tname)) in         (* Quad5: :=, W, -, $$                      *)
      let q_end = genQuad Op_endu (UDT (entry, !currentScope)) Empty Empty in           (* Quad6: endu, _udt_cname, -, -            *)
      let quads = [q_unit; q_par1; q_par2; q_call; q_ret; q_end] in                     (* Make a list of the new Quads             *)
      ignore quads;
      push quads;                                                                       (* Push the new Quads to the func_stack     *)
      let tup = (cname, (entry, tname, !currentScope)) in                               (* Ret value for lookup on Constr call      *)
      closeScope();                                                                     (* Close the Inner Scope                    *)
      tup
      

  (* UDT Env to Icode *)
let icodeUDTEnv udt_env =
   let envInfo = allConstructorInfo udt_env in                                          (* Transform UDT Env to a Constr List       *)
   List.map icodeUDT envInfo                                                            (* Generate Icode for all Constrs in Env    *)
   
  (* Deallocate all the allocated arrays *)
let dealloc_arrays s =
   let icodeOne a =
      let qp = genQuad Op_par (Entry a) (PassType V) Empty in
      let qc = genQuad Op_call Empty Empty (Str "_delete") in
      [qp; qc]
   in List.flatten (List.map icodeOne s)

  (* Translate the AST to Icode *)
let iCodeTranslation udt_env ast = 
   match ast with
   | Some tree ->
      let walk block_node =
         (match block_node.tag_bl with
          | Letdef lt ->
             icodeLetdef !icode_UDTEnv lt                                               (* Generate Icode for the Letdef            *)
          | Typedef tp ->
             []                                                                         (* No Quads generated for a Typedef         *)
         ) 
      in 
      openScope ();                                                                     (* Open a scope for UDT Env to Icode        *)
      icode_UDTEnv := icodeUDTEnv udt_env;                                              (* Generate Icode for the UDT Env           *)
      closeScope ();                                                                    (* Close the UDT Env to Icode scope         *)
      openScope ();                                                                     (* Open a scope for the Icode Generation    *)
      let qs = genQuad Op_unit (Str "_outer") Empty Empty in                            (* Quad1: unit, _outer, -, -                *)
      let qe = genQuad Op_endu (Str "_outer") Empty Empty in                            (* Quad2: endu, _outer, -, -                *)
      let pquads = List.flatten (List.map walk tree.tag_pg) in                          (* Program Quads                            *)
      let dearray = dealloc_arrays !array_stack in                                      (* Deallocate all the allocated arrays      *)
      let outer = 
         (qs::pquads) @ dearray @ [qe] in                                               (* _outer Quads                             *)
      push outer;                                                                       (* Add _outer Quads to the function stack   *)
      filterEmpty func_stack;                                                           (* Remove Empty Quad Lists                  *)
      normalizeQuads func_stack;                                                        (* Normalize Quads' Numbers                 *)
      debug_Icode ();                                                                   (* Print the Icode                          *)
      closeScope ()                                                                     (* Close the scope of the Icode Generation  *)
   | _         -> 
      iInternal "Empty Program" (Some (1,1));
      raise Terminate
