(lang dune 2.5)
(name milner)
(generate_opam_files true)
(using menhir 2.1)
(authors "Alan Hu <hu.ala@northeastern.edu>")
(maintainers "Alan Hu <hu.ala@northeastern.edu>")
(source (github milner-lang/milner))

(package
  (name milner)
  (synopsis "Programming language")
  (description "\
Programming language")
  (depends
    (cmdliner (>= 1.0.4))
    (dune (>= 2.6.0))
    (llvm (>= 10.0.0))
    (menhir (>= 20200612))
    (sedlex (>= 2.2))))
