(lang dune 3.19)

(name fascinating_compiler)

(generate_opam_files true)

(source
 (github Vollcanoo/fascinating_compiler))

(authors "Vollcanoo")

(license MIT)

(package
 (name fascinating_compiler)
 (synopsis "ToyC compiler targeting RISC-V32")
 (depends
  (ocaml (>= 5.3.0))
  (dune (>= 3.19)))
 (tags
  ("compiler" "toyc" "riscv")))
