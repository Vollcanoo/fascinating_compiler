let parse source =
  let lexbuf = Lexing.from_string source in
  Frontend.Parser.comp_unit Frontend.Lexer.read lexbuf

let contains haystack needle =
  let n = String.length needle in
  let rec loop i =
    i + n <= String.length haystack
    && (String.sub haystack i n = needle || loop (i + 1))
  in
  n = 0 || loop 0

let compile source =
  let ast = parse source in
  Analysis.Semantic.check ast;
  let program = Backend.Ir.lower ast in
  let path = Filename.temp_file "toyc-codegen" ".s" in
  let out = open_out_bin path in
  Fun.protect
    ~finally:(fun () -> close_out_noerr out)
    (fun () -> Backend.Codegen.emit out program);
  let input = open_in_bin path in
  let assembly =
    Fun.protect
      ~finally:(fun () -> close_in_noerr input)
      (fun () -> really_input_string input (in_channel_length input))
  in
  Sys.remove path;
  assembly

let () =
  let assembly =
    compile "int main() { int x = 1; int y = 2; return x + y; }"
  in
  if not (contains assembly "sw s1,") then
    failwith "allocated callee-saved register is not preserved";
  if not (contains assembly "lw s1,") then
    failwith "allocated callee-saved register is not restored";
  if not (contains assembly "mv s") then
    failwith "temporaries were not assigned register homes";

  let assembly =
    compile
      ("int sum(int a,int b,int c,int d,int e,int f,int g,int h,int i,"
       ^ "int j,int k,int l) { return a+b+c+d+e+f+g+h+i+j+k+l; }"
       ^ "int main() { return sum(1,2,3,4,5,6,7,8,9,10,11,12); }")
  in
  if not (contains assembly "call sum") then
    failwith "function call was not emitted";
  if not (contains assembly "(s0)") then
    failwith "register pressure did not exercise spill/incoming stack slots"
