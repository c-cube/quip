(lang dune 2.0)
(name quip)
(generate_opam_files true)
(maintainers "Simon Cruanes")
(authors "Simon Cruanes")
(homepage "https://github.com/c-cube/quip")
(source (github c-cube/quip))

(package
  (name quip)
  (license MIT)
  (synopsis "Proof checker for Quip")
  (depends
    (containers (and (>= "3.0") (< "4.0")))
    ppx_deriving
    (smtlib-utils (>= "0.3"))
    (ounit2 :with-test)
    logs
    (mtime (>= 2.0))
    cmdliner
    (iter (>= "1.0"))
    (ocaml (>= "4.08"))
    (pp_loc (>= 2.0))
    ))
