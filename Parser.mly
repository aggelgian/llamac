%{
  open Ast
  open Scanner
  open Symbol
  open Types
%}

%token T_and
%token <(int * int)>T_array
%token T_begin
%token T_bool
%token T_char
%token <(int * int)>T_delete
%token T_dim
%token T_do
%token T_done
%token T_downto
%token T_else
%token T_end
%token <(int * int)>T_false
%token T_float
%token T_for
%token <(int * int)>T_if
%token T_in
%token T_int
%token T_let
%token <(int * int)>T_match
%token <(int * int)>T_mod
%token T_mutable
%token T_new
%token <(int * int)>T_not
%token T_of
%token T_rec
%token T_ref
%token T_then
%token T_to
%token <(int * int)>T_true
%token T_type
%token T_unit
%token <(int * int)>T_while
%token T_with

%token T_arrow                  /* "->" */
%token <(int * int)>T_assign    /* "="  */
%token T_bar                    /* "|"  */
%token <(int * int)>T_plus      /* "+"  */
%token <(int * int)>T_minus     /* "-"  */
%token <(int * int)>T_mult      /* "*"  */
%token <(int * int)>T_div       /* "/"  */
%token <(int * int)>T_fplus     /* "+." */
%token <(int * int)>T_fminus    /* "-." */
%token <(int * int)>T_fmult     /* "*." */
%token <(int * int)>T_fdiv      /* "/." */
%token <(int * int)>T_pow       /* "**" */
%token <(int * int)>T_bang      /* "!"  */
%token <(int * int)>T_semicolon /* ";"  */
%token <(int * int)>T_conjunct  /* "&&" */
%token <(int * int)>T_disjunct  /* "||" */
%token <(int * int)>T_ltgt      /* "<>" */
%token <(int * int)>T_lt        /* "<"  */
%token <(int * int)>T_gt        /* ">"  */
%token <(int * int)>T_lteq      /* "<=" */
%token <(int * int)>T_gteq      /* ">=" */
%token <(int * int)>T_eq        /* "==" */
%token <(int * int)>T_neq       /* "!=" */
%token <(int * int)>T_refassign /* ":=" */

%token T_lparen                 /* "("  */
%token T_rparen                 /* ")"  */
%token T_lbrack                 /* "["  */
%token T_rbrack                 /* "]"  */
%token T_comma                  /* ","  */
%token T_colon                  /* ":"  */

%token <Ast.stringconst> T_id
%token <Ast.stringconst> T_constructor
%token <Ast.intconst> T_intconst
%token <Ast.realconst> T_realconst
%token <Ast.charconst> T_charconst
%token <string> T_stringconst

%token T_eof

%right T_arrow
%nonassoc T_of
%left T_ref
%nonassoc T_let T_in
%left T_semicolon
%nonassoc T_if
%nonassoc T_then
%nonassoc T_else
%nonassoc T_refassign
%left T_disjunct
%left T_conjunct
%nonassoc T_assign T_ltgt T_lt T_gt T_lteq T_gteq T_eq T_neq
%left T_plus T_minus T_fplus T_fminus
%left T_mult T_div T_fmult T_fdiv T_mod
%right T_pow
%nonassoc UNARY T_not T_delete
%nonassoc T_bang
%nonassoc T_lbrack T_rbrack
%nonassoc T_new

%start program
%type <unit> program
%type <Ast.ast_block_node list> list_of_defs
%type <Ast.ast_block_node > block
%type <Ast.ast_letdef_node> letdef
%type <Ast.ast_def_node list> def_list
%type <Ast.ast_def_node> def
%type <Ast.ast_par_node list> par_list
%type <Ast.ast_expr_node list> exprs_with_comma
%type <Ast.ast_typedef_node> typedef
%type <Ast.ast_tdef_node list> tdef_list
%type <Ast.ast_tdef_node> tdef
%type <Ast.ast_constr_node list> constr_list
%type <Ast.ast_constr_node> constr
%type <Ast.ast_type_node list> ttype_list
%type <Ast.ast_par_node> par
%type <Ast.ast_type_node> ttype
%type <int> mult_list
%type <Ast.ast_expr_node> expr
%type <Ast.ast_expr_node> expr_call
%type <Ast.ast_expr_node list> exprb_list
%type <Ast.ast_expr_node> exprb
%type <Ast.ast_clause_node list> clause_list
%type <Ast.ast_clause_node> clause
%type <Ast.ast_pattern_node> pattern
%type <Ast.ast_pattern_node list> pattern_lst
%type <Ast.ast_pattern_node> pattern_strong

%%

program : list_of_defs T_eof { 
          Ast.ast_tree :=  Some { tag_pg = $1; meta_pg = [] } 
        }

list_of_defs : /* nothing */ { [] }
             | block list_of_defs { $1 :: $2 }

block : letdef { 
        { tag_bl = Letdef $1; meta_bl = [] }
      }
      | typedef { 
        { tag_bl = Typedef $1; meta_bl = [] }
      }

letdef : T_let def def_list { 
         { tag_lt = (0, $2 :: $3); meta_lt = [] }
       }
       | T_let T_rec def def_list { 
         { tag_lt = (1, $3 :: $4); meta_lt = [] }
       }

def_list : /* nothing */ { [] }
         | T_and def def_list { $2 :: $3 }

def : T_id par_list T_assign expr { 
      { tag_df = Def_func ($1.sname, $2, ref None, $4); 
        meta_df = [addInfo $1.spos "id_name_start"];
        entry_df = None; scope_df = None }
    }
    | T_id par_list T_colon ttype T_assign expr { 
      { tag_df = Def_func ($1.sname, $2, ref (Some $4), $6); 
        meta_df = [addInfo $1.spos "id_name_start"];
        entry_df = None; scope_df = None }
    }
    | T_mutable T_id { 
      { tag_df = Def_mut ($2.sname, [], ref None); 
        meta_df = [addInfo $2.spos "id_name_start"];
        entry_df = None; scope_df = None }
    }
    | T_mutable T_id T_lbrack expr exprs_with_comma T_rbrack { 
      { tag_df = Def_mut ($2.sname, $4 :: $5, ref None); 
        meta_df = [addInfo $2.spos "id_name_start"];
        entry_df = None; scope_df = None }
    }
    | T_mutable T_id T_colon ttype { 
      { tag_df = Def_mut ($2.sname, [], ref (Some $4)); 
        meta_df = [addInfo $2.spos "id_name_start"];
        entry_df = None; scope_df = None }
    }
    | T_mutable T_id T_lbrack expr exprs_with_comma T_rbrack T_colon ttype { 
      { tag_df = Def_mut ($2.sname, $4 :: $5, ref (Some $8)); 
        meta_df = [addInfo $2.spos "id_name_start"];
        entry_df = None; scope_df = None }
    }

par_list : /* nothing */ { [] }
         | par par_list { $1 :: $2 }

exprs_with_comma : /* nothing */ { [] }
                 | T_comma expr exprs_with_comma { $2 :: $3 }

typedef : T_type tdef tdef_list { 
          { tag_pd = $2 :: $3; meta_pd = [] }
        }

tdef_list : /* nothing */ { [] }
          | T_and tdef tdef_list { $2 :: $3 }

tdef : T_id T_assign constr constr_list { 
       { tag_td = ($1.sname, $3 :: $4); meta_td = [addInfo $1.spos "type_name_start"] }
     }

constr_list : /* nothing */ { [] }
            | T_bar constr constr_list { $2 :: $3 }

constr : T_constructor { 
         { tag_co = ($1.sname, []); meta_co = [addInfo $1.spos "constr_name_start"] } 
       }
       | T_constructor T_of ttype ttype_list { 
         { tag_co = ($1.sname, $3 :: $4); meta_co = [addInfo $1.spos "constr_name_start"] } 
       }

ttype_list : /* nothing */ { [] }
           | ttype ttype_list { $1 :: $2 }

par : T_id { 
      { tag_pr = ($1.sname, ref None, ref None); 
        meta_pr = [addInfo $1.spos "par_name_start"] } 
    }
    | T_lparen T_id T_colon ttype T_rparen { 
      { tag_pr = ($2.sname, ref (Some $4), ref None); 
        meta_pr = [addInfo $2.spos "par_name_start"] } 
    }

ttype : T_unit { 
        { tag_tp = Tp_unit; meta_tp = [] }
      }
      | T_int { 
        { tag_tp = Tp_int; meta_tp = [] }
      }
      | T_char { 
        { tag_tp = Tp_char; meta_tp = [] }
      }
      | T_bool { 
        { tag_tp = Tp_bool; meta_tp = [] }
      }
      | T_float { 
        { tag_tp = Tp_float; meta_tp = [] }
      }
      | T_lparen ttype T_rparen { $2 }
      | ttype T_arrow ttype { 
        { tag_tp = Tp_func ($1, $3); meta_tp = [] }
      }
      | ttype T_ref { 
        { tag_tp = Tp_ref $1; meta_tp = [] }
      }
      | T_array T_of ttype { 
        { tag_tp = Tp_array (1, $3); meta_tp = [addInfo $1 "array_start"] } 
      }
      | T_array T_lbrack T_mult mult_list T_rbrack T_of ttype { 
        { tag_tp = Tp_array ($4 + 1, $7); meta_tp = [addInfo $1 "array_start"] } 
      }
      | T_id { 
        { tag_tp = Tp_id $1.sname; meta_tp = [addInfo $1.spos "type_name_start"] } 
      }

mult_list : /* nothing */ { 0 }
          | T_comma T_mult mult_list { 1 + $3 }

expr : T_plus expr %prec UNARY {
       { tag_ex = E_signed (S_plus, $2); meta_ex = [addInfo $1 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | T_minus expr %prec UNARY {
       { tag_ex = E_signed (S_minus, $2); meta_ex = [addInfo $1 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | T_fplus expr %prec UNARY {
       { tag_ex = E_signed (S_fplus, $2); meta_ex = [addInfo $1 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | T_fminus expr %prec UNARY {
       { tag_ex = E_signed (S_fminus, $2); meta_ex = [addInfo $1 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | T_not expr {
       { tag_ex = E_not $2; meta_ex = [addInfo $1 "not_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | expr T_plus expr {
       { tag_ex = E_binop ($1, B_plus, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | expr T_minus expr {
       { tag_ex = E_binop ($1, B_minus, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | expr T_mult expr {
       { tag_ex = E_binop ($1, B_mult, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | expr T_div expr {
       { tag_ex = E_binop ($1, B_div, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | expr T_fplus expr {
       { tag_ex = E_binop ($1, B_fplus, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | expr T_fminus expr {
       { tag_ex = E_binop ($1, B_fminus, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | expr T_fmult expr {
       { tag_ex = E_binop ($1, B_fmult, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | expr T_fdiv expr {
       { tag_ex = E_binop ($1, B_fdiv, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | expr T_mod expr {
       { tag_ex = E_binop ($1, B_mod, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | expr T_pow expr {
       { tag_ex = E_binop ($1, B_pow, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | expr T_assign expr {
       { tag_ex = E_binop ($1, B_assign, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | expr T_ltgt expr {
       { tag_ex = E_binop ($1, B_ltgt, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | expr T_lt expr {
       { tag_ex = E_binop ($1, B_lt, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | expr T_gt expr { 
       { tag_ex = E_binop ($1, B_gt, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none } 
     }
     | expr T_lteq expr { 
       { tag_ex = E_binop ($1, B_lteq, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none } 
     }
     | expr T_gteq expr { 
       { tag_ex = E_binop ($1, B_gteq, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none } 
     }
     | expr T_eq expr { 
       { tag_ex = E_binop ($1, B_eq, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none } 
     }
     | expr T_neq expr { 
       { tag_ex = E_binop ($1, B_neq, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none } 
     }
     | expr T_conjunct expr { 
       { tag_ex = E_binop ($1, B_conj, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none } 
     }
     | expr T_disjunct expr { 
       { tag_ex = E_binop ($1, B_disj, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none } 
     }
     | expr T_semicolon expr { 
       { tag_ex = E_binop ($1, B_semic, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none } 
     }
     | expr T_refassign expr { 
       { tag_ex = E_binop ($1, B_refassign, $3); meta_ex = [addInfo $2 "op_start"];
         entry_ex = None; matchType_ex = TYPE_none } 
     }
     | T_dim T_id { 
       { tag_ex = E_dim ([], $2.sname); meta_ex = [addInfo $2.spos "id_name_start"];
         entry_ex = None; matchType_ex = TYPE_none } 
     }
     | T_dim T_intconst T_id { 
       { tag_ex = E_dim ([$2.ival], $3.sname); 
         meta_ex = [(addInfo $3.spos "id_name_start"); (addInfo $2.ipos "int_start")];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | T_delete expr { 
       { tag_ex = E_del $2; meta_ex = [addInfo $1 "del_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | letdef T_in expr { 
       { tag_ex = E_in ($1, $3); meta_ex = [];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | T_begin expr T_end { 
       { tag_ex = E_begin $2; meta_ex = [];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | T_if expr T_then expr { 
       { tag_ex = E_if ($2, $4); meta_ex = [addInfo $1 "if_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | T_if expr T_then expr T_else expr { 
       { tag_ex = E_ifelse ($2, $4, $6); meta_ex = [addInfo $1 "if_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | T_while expr T_do expr T_done { 
       { tag_ex = E_while ($2, $4); meta_ex = [addInfo $1 "while_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | T_for T_id T_assign expr T_to expr T_do expr T_done { 
       { tag_ex = E_for ($2.sname, $4, L_to, $6, $8); 
         meta_ex = [addInfo $2.spos "id_name_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | T_for T_id T_assign expr T_downto expr T_do expr T_done { 
       { tag_ex = E_for ($2.sname, $4, L_downto, $6, $8); 
         meta_ex = [addInfo $2.spos "id_name_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | T_match expr T_with clause clause_list T_end { 
       { tag_ex = E_match ($2, $4 :: $5); meta_ex = [addInfo $1 "match_start"];
         entry_ex = None; matchType_ex = TYPE_none }
     }
     | expr_call { $1 }
     | exprb { $1 }

expr_call : T_id exprb_list { 
            { tag_ex = E_func($1.sname, $2); 
              meta_ex =[addInfo $1.spos "id_name_start"];
              entry_ex = None; matchType_ex = TYPE_none }
          }
          | T_constructor exprb_list { 
            { tag_ex = E_constr ($1.sname, $2); meta_ex =[addInfo $1.spos "constr_name_start"];
              entry_ex = None; matchType_ex = TYPE_none }
          }

exprb_list : exprb { [$1] }
           | exprb exprb_list { $1 :: $2 }

exprb : T_id { 
        { tag_ex = E_var $1.sname; meta_ex = [addInfo $1.spos "id_name_start"];
          entry_ex = None; matchType_ex = TYPE_none } 
      }
      | T_constructor {
        { tag_ex = E_constr ($1.sname, []); meta_ex = [addInfo $1.spos "constr_name_start"];
          entry_ex = None; matchType_ex = TYPE_none } 
      }
      | T_intconst {
        { tag_ex = E_int $1.ival; meta_ex = [];
          entry_ex = None; matchType_ex = TYPE_none } 
      }
      | T_realconst {
        { tag_ex = E_real $1.fval; meta_ex = [];
          entry_ex = None; matchType_ex = TYPE_none } 
      }
      | T_charconst {
        { tag_ex = E_char $1.cname; meta_ex = [];
          entry_ex = None; matchType_ex = TYPE_none } 
      }
      | T_stringconst {
        { tag_ex = E_string $1; meta_ex = [];
          entry_ex = None; matchType_ex = TYPE_none } 
      }
      | T_true {
        { tag_ex = E_bool true; meta_ex = [];
          entry_ex = None; matchType_ex = TYPE_none } 
      }
      | T_false {
        { tag_ex = E_bool false; meta_ex = [];
          entry_ex = None; matchType_ex = TYPE_none } 
      }
      | T_lparen T_rparen {
        { tag_ex = E_unit; meta_ex = [];
          entry_ex = None; matchType_ex = TYPE_none } 
      }
      | T_lparen expr T_rparen { $2 }
      | T_bang exprb {
        { tag_ex = E_bang $2; meta_ex = [addInfo $1 "bang_start"];
          entry_ex = None; matchType_ex = TYPE_none } 
      }
      | T_new ttype {
        { tag_ex = E_new $2; meta_ex = [];
          entry_ex = None; matchType_ex = TYPE_none } 
      }
      | T_id T_lbrack expr exprs_with_comma T_rbrack {
        { tag_ex = E_array ($1.sname, $3 :: $4); meta_ex = [addInfo $1.spos "array_name_start"];
          entry_ex = None; matchType_ex = TYPE_none } 
      }

clause_list : /* nothing */ { [] }
            | T_bar clause clause_list { $2 :: $3 }

clause : pattern T_arrow expr { 
         { tag_cl = ($1, $3); meta_cl = $1.meta_pt }
       }

pattern : T_plus T_intconst %prec UNARY { 
          { tag_pt = P_int (S_plus, $2.ival); meta_pt = [addInfo $1 "pat_name_start"] } 
        }
        | T_minus T_intconst %prec UNARY { 
          { tag_pt = P_int (S_minus, $2.ival); meta_pt = [addInfo $1 "pat_name_start"] } 
        }
        | T_fplus T_realconst %prec UNARY { 
          { tag_pt = P_real (S_fplus, $2.fval); meta_pt = [addInfo $1 "pat_name_start"] } 
        }
        | T_fminus T_realconst %prec UNARY { 
          { tag_pt = P_real (S_minus, $2.fval); meta_pt = [addInfo $1 "pat_name_start"] } 
        }
        | T_constructor pattern_lst {
          { tag_pt = P_constr ($1.sname, $2); meta_pt = [addInfo $1.spos "pat_name_start"] } 
        }
        | pattern_strong { $1 }

pattern_lst : pattern_strong { [$1] }
            | pattern_strong pattern_lst { $1 :: $2 }

pattern_strong : T_intconst { 
                 { tag_pt = P_int (Unsigned, $1.ival); meta_pt = [addInfo $1.ipos "pat_name_start"] } 
               }
               | T_realconst { 
                 { tag_pt = P_real (Unsigned, $1.fval); meta_pt = [addInfo $1.fpos "pat_name_start"] } 
               }
               | T_charconst { 
                 { tag_pt = P_char $1.cname; meta_pt = [addInfo $1.cpos "pat_name_start"] } 
               }
               | T_true { 
                 { tag_pt = P_bool true; meta_pt = [addInfo $1 "pat_name_start"] } 
               }
               | T_false { 
                 { tag_pt = P_bool false; meta_pt = [addInfo $1 "pat_name_start"] } 
               }
               | T_id { 
                 { tag_pt = P_id { pname = $1.sname; ptype = ref None; pentry = None }; 
                   meta_pt = [addInfo $1.spos "pat_name_start"] } 
               }
               | T_constructor { 
                 { tag_pt = P_constr ($1.sname, []); meta_pt = [addInfo $1.spos "pat_name_start"] } 
               }
               | T_lparen pattern T_rparen { $2 }

