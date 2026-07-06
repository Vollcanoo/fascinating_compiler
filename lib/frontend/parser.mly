/** Yacc parser for ToyC */

%{
open Ast

let parse_error _ : unit = failwith "Parse error"
%}

%token <int> NUMBER
%token <string> ID
%token INT CONST VOID
%token IF ELSE WHILE BREAK CONTINUE RETURN
%token PLUS MINUS TIMES DIVIDE MOD
%token LT GT LE GE EQ NE
%token AND OR NOT
%token ASSIGN
%token LPAREN RPAREN LBRACE RBRACE COMMA SEMICOLON
%token EOF

%nonassoc THEN
%nonassoc ELSE
%left OR
%left AND
%left LT GT LE GE EQ NE
%left PLUS MINUS
%left TIMES DIVIDE MOD
%right NOT UMINUS UPLUS

%start comp_unit
%type <Ast.comp_unit> comp_unit

%%

comp_unit:
  | top_levels EOF { $1 }
;

top_levels:
  | { [] }
  | top_level top_levels { $1 :: $2 }
;

top_level:
  | decl { failwith "TODO: parse global declaration" }
  | func_def { failwith "TODO: parse function definition" }
;

decl:
  | CONST INT ID ASSIGN expr SEMICOLON { failwith "TODO: parse const declaration" }
  | INT ID ASSIGN expr SEMICOLON { failwith "TODO: parse var declaration" }
;

func_def:
  | INT ID LPAREN param_list RPAREN block { failwith "TODO: parse int function" }
  | VOID ID LPAREN param_list RPAREN block { failwith "TODO: parse void function" }
;

param_list:
  | { [] }
  | param { [$1] }
  | param_list COMMA param { $1 @ [$3] }
;

param:
  | INT ID { $2 }
;

block:
  | LBRACE stmts RBRACE { $2 }
;

stmts:
  | { [] }
  | stmt stmts { $1 :: $2 }
;

stmt:
  | block { Block $1 }
  | SEMICOLON { Empty }
  | expr SEMICOLON { ExprStmt $1 }
  | ID ASSIGN expr SEMICOLON { Assign ($1, $3) }
  | decl { failwith "TODO: parse declaration statement" }
  | IF LPAREN expr RPAREN stmt %prec THEN { failwith "TODO: parse if statement" }
  | IF LPAREN expr RPAREN stmt ELSE stmt { failwith "TODO: parse if-else statement" }
  | WHILE LPAREN expr RPAREN stmt { failwith "TODO: parse while statement" }
  | BREAK SEMICOLON { Break }
  | CONTINUE SEMICOLON { Continue }
  | RETURN SEMICOLON { Return None }
  | RETURN expr SEMICOLON { Return (Some $2) }
;

expr:
  | lor_expr { $1 }
;

lor_expr:
  | land_expr { $1 }
  | lor_expr OR land_expr { Binary ($1, Or, $3) }
;

land_expr:
  | rel_expr { $1 }
  | land_expr AND rel_expr { Binary ($1, And, $3) }
;

rel_expr:
  | add_expr { $1 }
  | rel_expr LT add_expr { Binary ($1, Lt, $3) }
  | rel_expr GT add_expr { Binary ($1, Gt, $3) }
  | rel_expr LE add_expr { Binary ($1, Le, $3) }
  | rel_expr GE add_expr { Binary ($1, Ge, $3) }
  | rel_expr EQ add_expr { Binary ($1, Eq, $3) }
  | rel_expr NE add_expr { Binary ($1, Ne, $3) }
;

add_expr:
  | mul_expr { $1 }
  | add_expr PLUS mul_expr { Binary ($1, Add, $3) }
  | add_expr MINUS mul_expr { Binary ($1, Sub, $3) }
;

mul_expr:
  | unary_expr { $1 }
  | mul_expr TIMES unary_expr { Binary ($1, Mul, $3) }
  | mul_expr DIVIDE unary_expr { Binary ($1, Div, $3) }
  | mul_expr MOD unary_expr { Binary ($1, Mod, $3) }
;

unary_expr:
  | primary_expr { $1 }
  | PLUS unary_expr %prec UPLUS { Unary (UPlus, $2) }
  | MINUS unary_expr %prec UMINUS { Unary (UMinus, $2) }
  | NOT unary_expr { Unary (Not, $2) }
;

primary_expr:
  | ID { Var $1 }
  | NUMBER { IntLit $1 }
  | LPAREN expr RPAREN { $2 }
  | ID LPAREN arg_list RPAREN { Call ($1, $3) }
;

arg_list:
  | { [] }
  | expr { [$1] }
  | arg_list COMMA expr { $1 @ [$3] }
;
