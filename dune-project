(lang dune 3.7)

(name tosat)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name")

(maintainers "Maintainer Name")

(license MIT)

(documentation https://url/to/documentation)

(using menhir 2.1)

(package
 (name tosat)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  dune
  (ocaml (>= 5.0.0))
  (menhir (>= 20220210))
  (minisat (= 0.4))
  (alcotest (and :with-test (>= 1.7.0)))
  (fpath (>= 0.7.3))
  (eio_main (>= 0.8.0))
  (ocamlformat :with-dev-setup)
  (ocaml-lsp-server :with-dev-setup)
  (utop :with-dev-setup))
 (tags
  (sat-solver dpll cdcl)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
