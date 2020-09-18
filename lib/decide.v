(** Definitions to build decidable predicates. **)

From Lib Require Export common.

(** * General definitions **)

(** In contrary to [Decidable.decidable] this file is based on a computable version. **)
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

Lemma dec_BoolSpec : forall P D,
  BoolSpec P (~ P) (decidable_to_bool P D).
Proof.
  now intros P [?|?]; constructor.
Qed.

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
  now intros [|]; [left|right].
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

Lemma not_decidable : forall P,
  decidable P ->
  decidable (~ P).
Proof.
  prove_decidable.
Defined.

Lemma eq_refl_decidable : forall T (x : T),
  decidable (x = x).
Proof.
  now left.
Defined.

Hint Resolve eq_refl_decidable : decidability.

(** [test P] splits the goal into two: one in which P holds, and one in which it doesn’t.
  Only works for propositions [P] that [prove_decidable] can prove decidable. **)
Ltac test P :=
  let D := fresh "D" in
  assert (D : decidable P);
  [ prove_decidable
  | let d := fresh "d" in
    destruct D as [d|d]; generalize d; clear d ].

Definition comparable T := forall x y : T, decidable (x = y).

Hint Unfold comparable : decidability.


(** * Classical logic **)

(** Once a proposition is proven decidable, we get all the usual classical properties
  for free, without having to add any axioms to Coq. **)

Lemma dec_excluded_middle : forall P,
  decidable P ->
  P \/ ~ P.
Proof.
  now intros P [?|?]; [left|right].
Qed.

Lemma dec_not_not : forall P,
  decidable P ->
  ~ ~ P ->
  P.
Proof.
  now intros P [?|?].
Qed.

Lemma not_not : forall P : Prop,
  P ->
  ~ ~ P.
Proof.
  now auto.
Qed.

Lemma dec_pierce : forall P Q,
  decidable P ->
  ((P -> Q) -> P) -> P.
Proof.
  intros P Q [?|?] F; auto.
  now apply F.
Qed.

Lemma dec_not_and : forall P Q,
  decidable P ->
  ~ (P /\ Q) ->
  ~ P \/ ~ Q.
Proof.
  now intros P Q [?|?]; auto.
Qed.

Lemma not_or : forall P Q,
  ~ (P \/ Q) ->
  ~ P /\ ~ Q.
Proof.
  now auto.
Qed.

Lemma or_not : forall P Q,
  ~ P \/ ~ Q ->
  ~ (P /\ Q).
Proof.
  now intros P Q [?|?]; auto.
Qed.

Lemma and_not : forall P Q,
  ~ P /\ ~ Q ->
  ~ (P \/ Q).
Proof.
  now intros P Q [? ?] [?|?]; auto.
Qed.

Lemma dec_flatten_impl : forall P Q : Prop,
  decidable P ->
  (P -> Q) ->
  ~ P \/ Q.
Proof.
  now intros P Q [?|?]; auto.
Qed.

Lemma dec_not_impl : forall P Q : Prop,
  decidable P ->
  ~ (P -> Q) ->
  P \/ ~ Q.
Proof.
  now intros P Q [?|?]; auto.
Qed.

Lemma contrapositive : forall P Q : Prop,
  (P -> Q) ->
  ~ Q -> ~ P.
Proof.
  now auto.
Qed.

Lemma dec_contrapositive : forall P Q,
  decidable P ->
  (~ P -> ~ Q) ->
  Q -> P.
Proof.
  intros P Q D nf q. apply (dec_not_not _ D).
  now apply (contrapositive _ (~ Q)); auto.
Qed.

(** Simplify an hypothesis. **)
Ltac dsimpl_in H :=
  repeat match type of H with
  | ~ ~ ?P =>
    let D := fresh "D" in
    assert (D : decidable P); [
        prove_decidable
      | let H' := fresh H in
        assert (H' : P); [
            now apply (dec_not_not P D H)
          | clear H; rename H' into H; clear D ] ]
  | ~ (?P \/ ?Q) =>
    let H' := fresh H in
    assert (H' : ~ P /\ ~ Q); [
        now apply (not_or _ _ H)
      | clear H; rename H' into H ]
  | ~ (?P /\ ?Q) =>
    let D := fresh "D" in
    assert (D : decidable P); [
        prove_decidable
      | let H' := fresh H in
        assert (H' : ~ P \/ ~ Q); [
            now apply (dec_not_and P Q D H)
          | clear H; rename H' into H; clear D ] ]
  | ~ (?P -> ?Q) =>
    let D := fresh "D" in
    assert (D : decidable P); [
        prove_decidable
      | let H' := fresh H in
        assert (H' : ~ P \/ ~ Q); [
            now apply (dec_not_impl P Q D H)
          | clear H; rename H' into H; clear D ] ]
  | True /\ ?P => destruct H as [_ H]
  | ?P /\ True => destruct H as [H _]
  | False \/ ?P => destruct H as [H|H]; [ now destruct H |]
  | ?P \/ False => destruct H as [H|H]; [| now destruct H ]
  end.

Tactic Notation "dsimpl" "in" hyp(H) :=
  dsimpl_in H.

(** Simplify the goal. **)
Ltac dsimpl :=
  lazymatch goal with
  | |- ~ _ -> ~ _ => apply contrapositive; dsimpl
  | |- _ -> _ =>
    let H := fresh "H" in
    intro H;
    dsimpl in H;
    dsimpl;
    generalize H; clear H
  | |- _ =>
    repeat lazymatch goal with
    | |- ~ ~ ?P => apply (not_not P)
    | |- ~ (?P \/ ?Q) => apply (and_not P Q)
    | |- ~ (?P /\ ?Q) => apply (or_not P Q)
    | |- True /\ ?P => split; [now auto|]
    | |- ?P /\ True => split; [|now auto]
    | |- False \/ ?P => right
    | |- ?P \/ False => left
    end
  end.

Tactic Notation "dsimpl" "in" "*" :=
  dsimpl;
  repeat match goal with
  | H : _ |- _ => progress dsimpl in H
  end.


(** * Adding external lemmas to the database **)

(** ** Basic data types **)

Lemma unit_comparable : comparable unit.
Proof.
  now intros [] []; left.
Defined.

Hint Resolve unit_comparable : decidability.

Lemma bool_comparable : comparable bool.
Proof.
  intros [|] [|]; solve [ now left | now right ].
Defined.

Hint Resolve bool_comparable : decidability.

Lemma comparison_comparable : comparable comparison.
Proof.
  intros [| |] [| |]; solve [ now right | now left ].
Defined.

Hint Resolve comparison_comparable : decidability.

(** ** Lists **)

Lemma list_comparable : forall T,
  comparable T ->
  comparable (list T).
Proof.
  intros T C l1. induction l1 as [|a1 l1]; intro l2; destruct l2 as [|a2 l2];
    try first [ now left | now right ].
  test (a1 = a2).
  - intro. subst. test (l1 = l2).
    + intro. subst. prove_decidable.
    + right. now inversion 1.
  - right. now inversion 1.
Defined.

Hint Resolve list_comparable : decidability.

Lemma list_comparable_nil : forall T (l : list T),
  decidable (l = nil).
Proof.
  intros T [|? ?]; [left|right]; prove_decidable.
Defined.

Hint Resolve list_comparable_nil : decidability.

Lemma decidable_In : forall T (a : T) l,
  comparable T ->
  decidable (List.In a l).
Proof.
  intros T a l C. induction l as [|b l]; prove_decidable.
Defined.

Hint Resolve decidable_In : decidability.

Lemma decidable_Forall : forall T (P : T -> Prop) l,
  (forall a, decidable (P a)) ->
  decidable (List.Forall P l).
Proof.
  intros T P l D. induction l as [|a l].
  - left. now constructor.
  - apply decidable_equiv with (P a /\ List.Forall P l); [| prove_decidable ].
    split.
    + intros [? ?]. now constructor.
    + now inversion 1.
Defined.

Hint Resolve decidable_Forall : decidability.

Lemma decidable_Exists : forall T (P : T -> Prop) l,
  (forall a, decidable (P a)) ->
  decidable (List.Exists P l).
Proof.
  intros T P l D. induction l as [|a l].
  - right. now inversion 1.
  - apply decidable_equiv with (P a \/ List.Exists P l); [| prove_decidable ].
    split.
    + intros [?|?]; now constructor.
    + now inversion 1; [left|right].
Defined.

Hint Resolve decidable_Exists : decidability.

Lemma decidable_Forall2 : forall T1 T2 (P : T1 -> T2 -> Prop) l1 l2,
  (forall a b, decidable (P a b)) ->
  decidable (List.Forall2 P l1 l2).
Proof.
  intros T1 T2 P l1 l2 D. generalize l2. clear l2.
  induction l1 as [|a1 l1]; intros [|a2 l2]; try now right; inversion 1.
  - left. now constructor.
  - apply decidable_equiv with (P a1 a2 /\ List.Forall2 P l1 l2); [| prove_decidable ].
    split.
    + intros [? ?]. now constructor.
    + now inversion 1.
Defined.

Hint Resolve decidable_Forall2 : decidability.

Lemma decidable_NoDup : forall T (l : list T),
  comparable T ->
  decidable (List.NoDup l).
Proof.
  intros T l C. induction l as [|a l].
  - left. now constructor.
  - apply decidable_equiv with (~ List.In a l /\ List.NoDup l); [| prove_decidable ].
    split.
    + intros [? ?]. now constructor.
    + now inversion 1.
Defined.

Hint Resolve decidable_NoDup : decidability.


(** ** Arithmetic **)

Lemma nat_comparable : comparable nat.
Proof.
  intros n m. eapply reflect_dec. now apply Nat.eqb_spec.
Defined.

Hint Resolve nat_comparable : decidability.

Lemma ltb_decidable : forall n m : nat,
  decidable (n < m).
Proof.
  intros n m. eapply reflect_dec. now apply Nat.ltb_spec0.
Defined.

Hint Resolve ltb_decidable : decidability.

Lemma gtb_decidable : forall n m : nat,
  decidable (n > m).
Proof.
  prove_decidable.
Defined.

Lemma leb_decidable : forall n m : nat,
  decidable (n <= m).
Proof.
  intros n m. eapply reflect_dec. now apply Nat.leb_spec0.
Defined.

Hint Resolve leb_decidable : decidability.

Lemma geb_decidable : forall n m : nat,
  decidable (n >= m).
Proof.
  prove_decidable.
Defined.

