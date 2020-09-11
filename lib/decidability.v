(** Definitions to build decidable predicates. **)

From Lib Require Export common.

(*From mathcomp Require Import ssreflect ssrbool eqtype.*)
Definition decidable P := { P } + { ~ P }.

Create HintDb decidability.

Hint Resolve left : decidability.
Hint Resolve right : decidability.

Hint Resolve reflect_dec : decidability.

Ltac prove_decidable := now eauto with decidability.

Definition decidable_to_bool P (D : decidable P) :=
  if D then true else false.

Notation "'decide' P" :=
  (decidable_to_bool P ltac:(prove_decidable))
  (at level 70, only parsing).

Lemma dec_reflect : forall P (D : decidable P),
  reflect P (decidable_to_bool P D).
Proof.
  intros P [?|?]; now constructor.
Defined.

Lemma and_decidable : forall P1 P2,
  decidable P1 ->
  decidable P2 ->
  decidable (P1 /\ P2).
Proof.
  intros P1 P2 [?|?].
  - now intros [?|?]; [left| right].
  - now right.
Defined.

Hint Resolve and_decidable : decidability.

Lemma or_decidable : forall P1 P2,
  decidable P1 ->
  decidable P2 ->
  decidable (P1 \/ P2).
Proof.
  intros P1 P2 [?|?].
  - now do 2 left.
  - now intros [?|?]; [left; right| right; intros [?|?]].
Defined.

Hint Resolve or_decidable : decidability.

Lemma impl_decidable : forall P1 P2,
  decidable P1 ->
  decidable P2 ->
  decidable (P1 -> P2).
Proof.
  intros P1 P2 [?|?].
  - now intros [?|?]; [left| right; auto].
  - now left.
Defined.

Hint Resolve impl_decidable : decidability.

Lemma equiv_decidable : forall P1 P2,
  decidable P1 ->
  decidable P2 ->
  decidable (P1 <-> P2).
Proof.
  prove_decidable.
Defined.

Lemma decidable_equiv : forall P1 P2,
  (P1 <-> P2) ->
  decidable P1 ->
  decidable P2.
Proof.
  intros P1 P2 [I1 I2] [H | nH].
  - now left; auto.
  - now right; auto.
Defined.


Lemma is_true_bool : forall b1 b2 : bool,
  (b1 = b2) <-> (b1 <-> b2).
Proof.
  do 2 intros [|]; split;
    tauto
    || (intros H; rewrite H; tauto)
    || (intros [? ?]; exfalso;
        match goal with
        | H : is_true true -> is_true false |- _ =>
          let H' := fresh H in
          set (H' := H eq_refl); inversion H'
        | _ => idtac
        end).
Qed.

Lemma is_true_decidable : forall b : bool, decidable b.
Proof.
  intros [|].
  - now left.
  - now right.
Defined.

Hint Resolve is_true_decidable : decidability.

Lemma True_decidable : decidable True.
Proof.
  now left.
Defined.

Hint Resolve True_decidable : decidability.

Lemma False_decidable : decidable False.
Proof.
  now right.
Defined.

Hint Resolve False_decidable : decidability.

(** [test P] splits the goal into two: one in which P holds, and one in which it doesn’t.
  Only works for propositions [P] that [prove_decidable] can prove decidable. **)
Ltac test P :=
  let D := fresh "D" in
  assert (D : decidable P);
  [ prove_decidable
  | let d := fresh "d" in
    destruct D as [d|d]; generalize d; clear d ].

