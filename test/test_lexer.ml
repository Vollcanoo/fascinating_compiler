let () =
  let lexbuf = Lexing.from_string "int main() { return 0; }" in
  let _token = Frontend.Lexer.read lexbuf in
  Printf.printf "lexer smoke test passed\n"
