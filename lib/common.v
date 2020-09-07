(** Some very basic definitions, already present in quite a lot of libraries. **)

From Coq Require Export Bool.Bool.

Definition decidable P := { P } + { ~ P }.

Coercion is_true : bool >-> Sortclass.

