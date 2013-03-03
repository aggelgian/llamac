open Format
open Lexing
exception Terminate

type verbose = Vquiet | Vnormal | Vverbose

let flagVerbose = ref Vnormal 

let numErrors = ref 0
let maxErrors = ref 10
let flagWarnings = ref true
let numWarnings = ref 0
let maxWarnings = ref 200

type position =
    PosPoint   of Lexing.position
  | PosContext of Lexing.position * Lexing.position
  | PosDummy

let position_point lpos = PosPoint lpos
let position_context lpos_start lpos_end = PosContext (lpos_start, lpos_end)
let position_dummy = PosDummy

let print_position ppf pos =
  match pos with
  | PosPoint lpos ->
      fprintf ppf "@[file \"%s\",@ line %d,@ character %d:@]@ "
        lpos.pos_fname lpos.pos_lnum (lpos.pos_cnum - lpos.pos_bol)
  | PosContext (lpos_start, lpos_end) ->
      if lpos_start.pos_fname != lpos_end.pos_fname then
        fprintf ppf "@[file \"%s\",@ line %d,@ character %d to@ \
                     file %s,@ line %d,@ character %d:@]@ "
          lpos_start.pos_fname lpos_start.pos_lnum
          (lpos_start.pos_cnum - lpos_start.pos_bol)
          lpos_end.pos_fname lpos_end.pos_lnum
          (lpos_end.pos_cnum - lpos_end.pos_bol)
      else if lpos_start.pos_lnum != lpos_end.pos_lnum then
        fprintf ppf "@[file \"%s\",@ line %d,@ character %d to@ \
                     line %d,@ character %d:@]@ "
          lpos_start.pos_fname lpos_start.pos_lnum
          (lpos_start.pos_cnum - lpos_start.pos_bol)
          lpos_end.pos_lnum
          (lpos_end.pos_cnum - lpos_end.pos_bol)
      else if lpos_start.pos_cnum - lpos_start.pos_bol !=
              lpos_end.pos_cnum - lpos_end.pos_bol then
        fprintf ppf "@[file \"%s\",@ line %d,@ characters %d to %d:@]@ "
          lpos_start.pos_fname lpos_start.pos_lnum
          (lpos_start.pos_cnum - lpos_start.pos_bol)
          (lpos_end.pos_cnum - lpos_end.pos_bol)
      else
        fprintf ppf "@[file \"%s\", line %d, character %d:@]@ "
          lpos_start.pos_fname lpos_start.pos_lnum
          (lpos_start.pos_cnum - lpos_start.pos_bol)
  | PosDummy ->
      ()

let no_out buf pos len = ()
let no_flush () = ()
let null_formatter = make_formatter no_out no_flush

let internal_raw (fname, lnum) fmt =
  let fmt = "@[<v 2>" ^^ fmt ^^ "@]@;@?" in
  incr numErrors;
  let cont ppf =
    raise Terminate in
  eprintf "Internal error occurred at %s:%d,@ " fname lnum;
  kfprintf cont err_formatter fmt

and fatal fmt =
  let fmt = "@[<v 2>Fatal error: " ^^ fmt ^^ "@]@;@?" in
  incr numErrors;
  let cont ppf =
    raise Terminate in
  kfprintf cont err_formatter fmt

and error fmt =
  let fmt = "@[<v 2>Error: " ^^ fmt ^^ "@]@;@?" in
  incr numErrors;
  if !numErrors >= !maxErrors then
    let cont ppf =
      eprintf "Too many errors, aborting...\n";
      raise Terminate in
    kfprintf cont err_formatter fmt
  else
    eprintf fmt

and warning fmt =
  let fmt = "@[<v 2>Warning: " ^^ fmt ^^ "@]@;@?" in
  if !flagWarnings then
  begin
    incr numWarnings;
    if !numWarnings >= !maxWarnings then
      let cont ppf =
        eprintf "Too many warnings, no more will be shown...\n";
        flagWarnings := false in
      kfprintf cont err_formatter fmt
    else
      eprintf fmt
  end
  else
    fprintf null_formatter fmt

and message fmt =
  let fmt = "@[<v 2>" ^^ fmt ^^ "@]@;@?" in
  eprintf fmt
  
  (* My fatal Error *)
let ifatal msg pos =
   (match pos with
    | None        -> printf "Fatal Error (Unknown Position) : %s\n" msg
    | Some (r, c) -> printf "Fatal Error (Ln %d, Col %d) : %s\n" r c msg);
   raise Terminate
   
  (* My Internal Error *)
let iInternal msg pos =
   (match pos with
    | None        -> printf "Internal Error : %s\n" msg
    | Some (r, c) -> printf "Internal Error (Ln %d, Col %d) : %s\n" r c msg);
   raise Terminate
   
  (* My Warning *)
let iwarning msg pos = 
   incr numWarnings;
   (match pos with
    | None        -> printf "Warning (Unknown Position) : %s\n" msg
    | Some (r, c) -> printf "Warning (Ln %d, Col %d) : %s\n" r c msg);
   if (numWarnings = maxWarnings) then
      begin
         printf "Too many warnings...\n";
         raise Terminate
      end
      
  (* Print to string *)
let print_to_string format = 
   let buffer = Buffer.create 512 in
   let fmt = Format.formatter_of_buffer buffer in
   Format.kfprintf
     (begin fun fmt ->
         Format.pp_print_flush fmt ();
         let s = Buffer.contents buffer in
         Buffer.clear buffer;
      s
      end)
     fmt
     format
