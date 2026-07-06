

%{
open Ast

(* Decl 在顶层与语句中语法相同，先解析为 decl_kind 再分别构造 AST *)
type decl_kind =
  | DConst of string * exp
  | DVar of string * exp

let parse_error _ : unit = failwith "Parse error"
%}

%token <int> NUMBER
%token <string> ID
%token INT CONST VOID
%token IF ELSE WHILE BREAK CONTINUE RETURN
%token ADD SUB MUL DIV MOD
%token LT GT LE GE EQ NE
%token AND OR NOT
%token ASSIGN
%token LPAREN RPAREN LBRACE RBRACE COMMA SEMICOLON
%token EOF

%nonassoc THEN
%nonassoc ELSE
%left OR
%left AND
%nonassoc LT GT LE GE EQ NE
%left ADD SUB
%left MUL DIV MOD
%right NOT UMINUS UADD

%start comp_unit
%type <Ast.comp_unit> comp_unit
%type <decl_kind> decl
%type <string * Ast.exp> const_decl
%type <string * Ast.exp> var_decl
%type <Ast.func_def> func_def
%type <string> param
%type <Ast.block> block
%type <Ast.stmt> stmt
%type <Ast.exp> expr
%type <Ast.exp> l_or_expr
%type <Ast.exp> l_and_expr
%type <Ast.exp> rel_expr
%type <Ast.exp> add_expr
%type <Ast.exp> mul_expr
%type <Ast.exp> unary_expr
%type <Ast.exp> primary_expr

%%

comp_unit:
  | comp_unit_item comp_unit_tail EOF { $1 :: $2 }
;

comp_unit_tail:
  | { [] }
  | comp_unit_item comp_unit_tail { $1 :: $2 }
;

comp_unit_item:
  | decl
    { match $1 with
      | DConst (name, e) -> GlobalConstDecl (name, e)
      | DVar (name, e) -> GlobalVarDecl (name, e) }
  | func_def { FuncDef $1 }
;

decl:
  | const_decl { let (n, e) = $1 in DConst (n, e) }
  | var_decl { let (n, e) = $1 in DVar (n, e) }
;

const_decl:
  | CONST INT ID ASSIGN expr SEMICOLON { ($3, $5) }
;

var_decl:
  | INT ID ASSIGN expr SEMICOLON { ($2, $4) }
;

func_def:
  | INT ID LPAREN param_list RPAREN block
    { { ret_type = IntRet; name = $2; params = $4; body = $6 } }
  | VOID ID LPAREN param_list RPAREN block
    { { ret_type = VoidRet; name = $2; params = $4; body = $6 } }
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
  | LBRACE block_tail RBRACE { $2 }
;

block_tail:
  | { [] }
  | stmt block_tail { $1 :: $2 }
;

stmt:
  | block { Block $1 }
  | SEMICOLON { Empty }
  | expr SEMICOLON { ExprStmt $1 }
  | ID ASSIGN expr SEMICOLON { Assign ($1, $3) }
  | decl
    { match $1 with
      | DConst (name, e) -> ConstDecl (name, e)
      | DVar (name, e) -> VarDecl (name, e) }
  | IF LPAREN expr RPAREN stmt %prec THEN { If ($3, $5, None) }
  | IF LPAREN expr RPAREN stmt ELSE stmt { If ($3, $5, Some $7) }
  | WHILE LPAREN expr RPAREN stmt { While ($3, $5) }
  | BREAK SEMICOLON { Break }
  | CONTINUE SEMICOLON { Continue }
  | RETURN SEMICOLON { Return None }
  | RETURN expr SEMICOLON { Return (Some $2) }
;

expr:
  | l_or_expr { $1 }
;

l_or_expr:
  | l_and_expr { $1 }
  | l_or_expr OR l_and_expr { Binary ($1, Or, $3) }
;

l_and_expr:
  | rel_expr { $1 }
  | l_and_expr AND rel_expr { Binary ($1, And, $3) }
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
  | add_expr ADD mul_expr { Binary ($1, Add, $3) }
  | add_expr SUB mul_expr { Binary ($1, Sub, $3) }
;

mul_expr:
  | unary_expr { $1 }
  | mul_expr MUL unary_expr { Binary ($1, Mul, $3) }
  | mul_expr DIV unary_expr { Binary ($1, Div, $3) }
  | mul_expr MOD unary_expr { Binary ($1, Mod, $3) }
;

unary_expr:
  | primary_expr { $1 }
  | ADD unary_expr %prec UADD { Unary (UPlus, $2) }
  | SUB unary_expr %prec UMINUS { Unary (UMinus, $2) }
  | NOT unary_expr { Unary (Not, $2) }
;

primary_expr:
  | ID { Var $1 }
  | NUMBER { IntLit $1 }
  | LPAREN expr RPAREN { $2 }
  | ID LPAREN expr_list_opt RPAREN { Call ($1, $3) }
;

expr_list_opt:
  | { [] }
  | expr { [$1] }
  | expr_list_opt COMMA expr { $1 @ [$3] }
;
