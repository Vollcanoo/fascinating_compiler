{
  open Parser
}

let digit = ['0'-'9']
let ident_start = ['_' 'a'-'z' 'A'-'Z']
let ident_char = ident_start | digit
let ident = ident_start ident_char*
let whitespace = [' ' '\t' '\r' '\n']+

rule read = parse
  | whitespace { read lexbuf }
  | "//" [^ '\n']* { read lexbuf }
  | "/*" { comment lexbuf }
  | "const" { CONST }
  | "int" { INT }
  | "void" { VOID }
  | "if" { IF }
  | "else" { ELSE }
  | "while" { WHILE }
  | "break" { BREAK }
  | "continue" { CONTINUE }
  | "return" { RETURN }
  | "<=" { LE }
  | ">=" { GE }
  | "==" { EQ }
  | "!=" { NE }
  | "&&" { AND }
  | "||" { OR }
  | ";" { SEMICOLON }
  | "=" { ASSIGN }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { TIMES }
  | "/" { DIVIDE }
  | "%" { MOD }
  | "<" { LT }
  | ">" { GT }
  | "!" { NOT }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "," { COMMA }
  | ident as name { ID name }
  | '-'? ('0' | ['1'-'9'] digit*) as num { NUMBER (int_of_string num) }
  | eof { EOF }
  | _ as c { failwith (Printf.sprintf "Lexical error: unexpected character '%c'" c) }

and comment = parse
  | "*/" { read lexbuf }
  | _ { comment lexbuf }
  | eof { failwith "Unterminated block comment" }
