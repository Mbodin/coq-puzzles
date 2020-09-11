(** Some very basic definitions. **)

From Coq Require Export Bool.Bool.
From Coq Require Export PeanoNat Arith.Arith Arith.Compare_dec.

Coercion is_true : bool >-> Sortclass.

