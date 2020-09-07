(lang dune 2.0)
(using coq 0.1)
(name coq-puzzles)

(generate_opam_files true)
(source (github Mbodin/coq-puzzles))

(package
  (name coq-puzzles)
  (synopsis "A collection of puzzles formalised in Coq")
	(license CeCILL-C)
	(maintainers "Martin Constantino–Bodin <martin.bodin@ens-lyon.org>"))

