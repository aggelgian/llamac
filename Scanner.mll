{
  open Parser
  open Ast
  open Error
  
  let num_lines = ref 1
  let num_chars = ref 1
  let nested_comments = ref 0
}

let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z']
let simple_char = [^ '\'' '\"' '\\']
let hex = "\\x" ['0'-'9' 'a'-'f' 'A'-'F'] ['0'-'9' 'a'-'f' 'A'-'F']
let white = [' ' '\t' '\r']
let escape = '\\' ['n' 't' 'r' '0' '\\' '\'' '\"']

rule llama_lexer = parse
  | "and"
    { num_chars := !num_chars + 3;
      T_and }
  | "array"
   { num_chars := !num_chars + 5;
     T_array (!num_lines, !num_chars - 5) }
  | "begin"
   { num_chars := !num_chars + 5;
     T_begin }
  | "bool"
   { num_chars := !num_chars + 4;
     T_bool }
  | "char"
   { num_chars := !num_chars + 4;
     T_char }
  | "delete"
   { num_chars := !num_chars + 6;
     T_delete (!num_lines, !num_chars - 6) }
  | "dim"
   { num_chars := !num_chars + 3;
     T_dim }
  | "do"
   { num_chars := !num_chars + 2;
     T_do }
  | "done"
   { num_chars := !num_chars + 4;
     T_done }
  | "downto"
   { num_chars := !num_chars + 6;
     T_downto }
  | "else"
   { num_chars := !num_chars + 4;
     T_else }
  | "end"
   { num_chars := !num_chars + 3;
     T_end }
  | "false"
   { num_chars := !num_chars + 5;
     T_false (!num_lines, !num_chars - 5) }
  | "float"
   { num_chars := !num_chars + 5;
     T_float }
  | "for"
   { num_chars := !num_chars + 3;
     T_for }
  | "if"
   { num_chars := !num_chars + 2;
     T_if (!num_lines, !num_chars - 2) }
  | "in"
   { num_chars := !num_chars + 2;
     T_in }
  | "int"
   { num_chars := !num_chars + 3;
     T_int }
  | "let"
   { num_chars := !num_chars + 3;
     T_let }
  | "match"
   { num_chars := !num_chars + 5;
     T_match (!num_lines, !num_chars - 5) }
  | "mod"
   { num_chars := !num_chars + 3;
     T_mod (!num_lines, !num_chars - 3) }
  | "mutable"
   { num_chars := !num_chars + 7;
     T_mutable }
  | "new"
   { num_chars := !num_chars + 3;
     T_new }
  | "not"
   { num_chars := !num_chars + 3;
     T_not (!num_lines, !num_chars - 3) }
  | "of"
   { num_chars := !num_chars + 2;
     T_of }
  | "rec"
   { num_chars := !num_chars + 3;
     T_rec }
  | "ref"
   { num_chars := !num_chars + 3;
     T_ref }
  | "then"
   { num_chars := !num_chars + 4;
     T_then }
  | "to"
   { num_chars := !num_chars + 2;
     T_to }
  | "true"
   { num_chars := !num_chars + 4;
     T_true (!num_lines, !num_chars - 4) }
  | "type"
   { num_chars := !num_chars + 4;
     T_type }
  | "unit"
   { num_chars := !num_chars + 4;
     T_unit }
  | "while"
   { num_chars := !num_chars + 5;
     T_while (!num_lines, !num_chars - 5) }
  | "with"
   { num_chars := !num_chars + 4;
     T_with }
  | "->"
   { num_chars := !num_chars + 2;
     T_arrow }
  | "="
   { incr num_chars;
     T_assign (!num_lines, !num_chars - 1) }
  | "|"
   { incr num_chars;
     T_bar }
  | "+"
   { incr num_chars;
     T_plus (!num_lines, !num_chars - 1) }
  | "-"
   { incr num_chars;
     T_minus (!num_lines, !num_chars - 1) }
  | "*"
   { incr num_chars;
     T_mult (!num_lines, !num_chars - 1) }
  | "/"
   { incr num_chars;
     T_div (!num_lines, !num_chars - 1) }
  | "+."
   { num_chars := !num_chars + 2;
     T_fplus (!num_lines, !num_chars - 2) }
  | "-."
   { num_chars := !num_chars + 2;
     T_fminus (!num_lines, !num_chars - 2) }
  | "*."
   { num_chars := !num_chars + 2;
     T_fmult (!num_lines, !num_chars - 2) }
  | "/."
   { num_chars := !num_chars + 2;
     T_fdiv (!num_lines, !num_chars - 2) }
  | "**"
   { num_chars := !num_chars + 2;
     T_pow (!num_lines, !num_chars - 2) }
  | "!"
   { incr num_chars;
     T_bang (!num_lines, !num_chars - 1) }
  | ";"
   { incr num_chars;
     T_semicolon (!num_lines, !num_chars - 1) }
  | "&&"
   { num_chars := !num_chars + 2;
     T_conjunct (!num_lines, !num_chars - 2) }
  | "||"
   { num_chars := !num_chars + 2;
     T_disjunct (!num_lines, !num_chars - 2) }
  | "<>"
   { num_chars := !num_chars + 2;
     T_ltgt (!num_lines, !num_chars - 2) }
  | "<"
   { incr num_chars;
     T_lt (!num_lines, !num_chars - 1) }
  | ">"
   { incr num_chars;
     T_gt (!num_lines, !num_chars - 1) }
  | "<="
   { num_chars := !num_chars + 2;
     T_lteq (!num_lines, !num_chars - 2) }
  | ">="
   { num_chars := !num_chars + 2;
     T_gteq (!num_lines, !num_chars - 2) }
  | "=="
   { num_chars := !num_chars + 2;
     T_eq (!num_lines, !num_chars - 2) }
  | "!="
   { num_chars := !num_chars + 2;
     T_neq (!num_lines, !num_chars - 2) }
  | ":="
   { num_chars := !num_chars + 2;
     T_refassign (!num_lines, !num_chars - 2) }
  | "("
   { incr num_chars;
     T_lparen }
  | ")"
   { incr num_chars;
     T_rparen }
  | "["
   { incr num_chars;
     T_lbrack }
  | "]"
   { incr num_chars;
     T_rbrack }
  | ","
   { incr num_chars;
     T_comma }
  | ":"
   { incr num_chars;
     T_colon }
  | "--" [^ '\n']* '\n'
   { incr num_lines;
     num_chars := 1;
     llama_lexer lexbuf }
  | "(*"
   { incr nested_comments;
     num_chars := !num_chars + 2;
     llama_comment lexbuf }
  | "'" (simple_char | escape | hex) "'" as charconst
   { num_chars := !num_chars + (String.length charconst);
     T_charconst {cname = charconst; cpos = (!num_lines, !num_chars - (String.length charconst);)} }
  | ['A'-'Z'] (letter | digit | '_')* as identc
   { num_chars := !num_chars + (String.length identc);
     T_constructor {sname = identc; spos = (!num_lines, !num_chars - (String.length identc);)} }
  | letter (letter | digit | '_')* as ident
   { num_chars := !num_chars + (String.length ident);
     T_id {sname = ident; spos = (!num_lines, !num_chars - (String.length ident);)}  }
  | digit+ as intconst
   { num_chars := !num_chars + (String.length intconst);
     let num = int_of_string intconst in
     if (num > 32767) || (num < -32768) then
        iwarning ("Llama supports 16-bit signed int.\n  " ^ intconst ^ " will overflow") (Some (!num_lines, !num_chars - (String.length intconst)));
     T_intconst {ival = num; ipos = (!num_lines, !num_chars - (String.length intconst);)} }
  | digit+ '.' digit+ (['e' 'E'] ['+' '-']? digit+)? as realconst
   { num_chars := !num_chars + (String.length realconst);
     T_realconst {fval = (float_of_string realconst); fpos = (!num_lines, !num_chars - (String.length realconst);)} }
  | '\"' (simple_char | escape | hex)* '\"' as stringconst
   { num_chars := !num_chars + (String.length stringconst);
     T_stringconst stringconst }
  | '\n'
   { incr num_lines;
     num_chars := 1;
     llama_lexer lexbuf }
  | white+ as blanks
   { num_chars := !num_chars + (String.length blanks);
     llama_lexer lexbuf }
  | eof	{ T_eof }
  | _ as chr
   { incr num_chars;
     Printf.eprintf "Lexical Error: '%c' at Ln %d, Col %d.\n" chr !num_lines !num_chars;
     llama_lexer lexbuf }

and llama_comment = parse
  | "*)"
   { decr nested_comments;
     num_chars := !num_chars + 2;
     if !nested_comments == 0 then
       llama_lexer lexbuf
     else
       llama_comment lexbuf }
  | "(*"
   { incr nested_comments;
     num_chars := !num_chars + 2;
     llama_comment lexbuf}
  | "\n"
   { incr num_lines;
     num_chars := 1;
     llama_comment lexbuf }
  | '*'
   { incr num_chars;
     llama_comment lexbuf }
  | '('
   { incr num_chars;
     llama_comment lexbuf }
  | [^ '*' '(' '\n']+ as junk
   { num_chars := !num_chars + (String.length junk);
     llama_comment lexbuf }
  | eof
   { if !nested_comments <> 0 then
     Printf.eprintf "Lexical Error: Umatched Comment\n";
     T_eof }
  | _ as chr
   { incr num_chars;
     Printf.eprintf "Lexical Error: '%c' at Ln %d, Col %d).\n" chr !num_lines !num_chars;
     llama_lexer lexbuf }

