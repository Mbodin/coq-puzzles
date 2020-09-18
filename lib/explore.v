(** Definitions to build explorable predicates. **)

From Coq Require Import List.
From Lib Require Import decide pick.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** * Definition of explorability **)

(** Explorable means that we can list all the elements satisfying the constraint. **)
Definition explorable A (P : A -> Prop) :=
  { l : list A | forall x, P x <-> In x l }.

Definition explorable2 A1 A2 (P : A1 -> A2 -> Prop) :=
  explorable (fun x => let '(x1, x2) := x in P x1 x2).

Definition explorable3 A1 A2 A3 (P : A1 -> A2 -> A3 -> Prop) :=
  explorable (fun x => let '(x1, x2, x3) := x in P x1 x2 x3).

Definition explorable4 A1 A2 A3 A4 (P : A1 -> A2 -> A3 -> A4 -> Prop) :=
  explorable (fun x => let '(x1, x2, x3, x4) := x in P x1 x2 x3 x4).

Definition explorable5 A1 A2 A3 A4 A5 (P : A1 -> A2 -> A3 -> A4 -> A5 -> Prop) :=
  explorable (fun x => let '(x1, x2, x3, x4, x5) := x in P x1 x2 x3 x4 x5).

Definition explorable_Type T :=
  explorable (fun _ : T => True).

Create HintDb explorability.

Ltac prove_explorable := now eauto with explorability pickability decidability.


(** * Lemmas about explorability **)

Lemma explorable_pickable : forall A (P : A -> Prop),
  explorable P ->
  pickable P.
Proof.
  intros A P [[|x l] F].
  - right. intros [x p]. apply F in p. now inversion p.
  - left. exists x. apply F. now left.
Defined.

Hint Resolve explorable_pickable : pickability.

Lemma explorable2_pickable2 : forall A1 A2 (P : A1 -> A2 -> Prop),
  explorable2 P ->
  pickable2 P.
Proof.
  intros A1 A2 P [[|[x1 x2] l] F].
  - right. intros [x1 [x2 p]]. apply F with (x1, x2) in p. now inversion p.
  - left. exists (x1, x2). apply F with (x := (x1, x2)). now left.
Defined.

Hint Resolve explorable2_pickable2 : pickability.

Lemma explorable3_pickable3 : forall A1 A2 A3 (P : A1 -> A2 -> A3 -> Prop),
  explorable3 P ->
  pickable3 P.
Proof.
  intros A1 A2 A3 P [[|[[x1 x2] x3] l] F].
  - right. intros [x1 [x2 [x3 p]]]. apply F with (x1, x2, x3) in p. now inversion p.
  - left. exists (x1, x2, x3). apply F with (x := (x1, x2, x3)). now left.
Defined.

Hint Resolve explorable3_pickable3 : pickability.

Lemma explorable4_pickable4 : forall A1 A2 A3 A4 (P : A1 -> A2 -> A3 -> A4 -> Prop),
  explorable4 P ->
  pickable4 P.
Proof.
  intros A1 A2 A3 A4 P [[|[[[x1 x2] x3] x4] l] F].
  - right. intros [x1 [x2 [x3 [x4 p]]]]. apply F with (x1, x2, x3, x4) in p. now inversion p.
  - left. exists (x1, x2, x3, x4). apply F with (x := (x1, x2, x3, x4)). now left.
Defined.

Hint Resolve explorable4_pickable4 : pickability.

Lemma explorable5_pickable5 : forall A1 A2 A3 A4 A5 (P : A1 -> A2 -> A3 -> A4 -> A5 -> Prop),
  explorable5 P ->
  pickable5 P.
Proof.
  intros A1 A2 A3 A4 A5 P [[|[[[[x1 x2] x3] x4] x5] l] F].
  - right. intros [x1 [x2 [x3 [x4 [x5 p]]]]]. apply F with (x1, x2, x3, x4, x5) in p. now inversion p.
  - left. exists (x1, x2, x3, x4, x5). apply F with (x := (x1, x2, x3, x4, x5)). now left.
Defined.

Hint Resolve explorable5_pickable5 : pickability.


(** * Tactics **)

Ltac prove_explorable_Type l :=
  let x := fresh "x" in
  exists l; intros x; split; [ destruct x; repeat first [ now left | right ] | now auto ].


(** * Adding external lemmas to the database **)

(** ** Basic data types **)

Lemma explorable_unit : explorable_Type unit.
Proof.
  prove_explorable_Type (tt :: nil).
Defined.

Hint Resolve explorable_unit : explorability.

Lemma explorable_bool : explorable_Type bool.
Proof.
  prove_explorable_Type (true :: false :: nil).
Defined.

Hint Resolve explorable_bool : explorability.

Lemma explorable_comparison : explorable_Type comparison.
Proof.
  prove_explorable_Type (Eq :: Lt :: Gt :: nil).
Defined.

Hint Resolve explorable_comparison : explorability.

(** ** List **)

Lemma explorable_In : forall T (l : list T),
  explorable (fun x => List.In x l).
Proof.
  intros T l. now exists l.
Defined.

Hint Resolve explorable_In : explorability.

