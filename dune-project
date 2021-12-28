(lang dune 2.0)
(name quip)
(generate_opam_files true)

(package
  (name quip)
  (license MIT)
  (depends
    (containers (and (>= "3.0") (< "4.0")))
    ppx_deriving
    (smtlib-utils (>= "0.3"))
    (ounit2 :with-test)
    logs
    mtime
    (iter (>= "1.0"))
    (ocaml (>= "4.08"))
    pp_loc
    ))
