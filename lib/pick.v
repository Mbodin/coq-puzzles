(** Definitions to build computable functions. **)

From Lib Require Import decide.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** * Definition of pickability **)

(** A variant of [decidable] in which we provide a witness. **)
Definition pickable A (P : A -> Prop) :=
  { x | P x } + { ~ exists x, P x }.

Definition pickable2 A1 A2 (P : A1 -> A2 -> Prop) :=
  { x | let '(x1, x2) := x in P x1 x2 } + { ~ exists x1 x2, P x1 x2 }.

Definition pickable3 A1 A2 A3 (P : A1 -> A2 -> A3 -> Prop) :=
  { x | let '(x1, x2, x3) := x in P x1 x2 x3 } + { ~ exists x1 x2 x3, P x1 x2 x3 }.

Definition pickable4 A1 A2 A3 A4 (P : A1 -> A2 -> A3 -> A4 -> Prop) :=
  { x | let '(x1, x2, x3, x4) := x in P x1 x2 x3 x4 } + { ~ exists x1 x2 x3 x4, P x1 x2 x3 x4 }.

Definition pickable5 A1 A2 A3 A4 A5 (P : A1 -> A2 -> A3 -> A4 -> A5 -> Prop) :=
  { x | let '(x1, x2, x3, x4, x5) := x in P x1 x2 x3 x4 x5 } + { ~ exists x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5 }.

Create HintDb pickability.


(** * Lemmas about pickability **)

Lemma pickable_decidable : forall A (P : A -> Prop),
  pickable P ->
  decidable (exists x, P x).
Proof.
  intros A P [[x p]|N].
  - left. now exists x.
  - now right.
Defined.

Hint Resolve pickable_decidable : decidability.

Lemma pickable_disjunction : forall A (P : A -> Prop),
  pickable P ->
  (exists x, P x) \/ forall x, ~ P x.
Proof.
  intros A P [[x p]|N].
  - now left; exists x.
  - right. intros x p. apply N. now exists x.
Qed.

Lemma not_exists : forall A (P : A -> Prop),
  ~ (exists x, P x) ->
  forall x, ~ P x.
Proof.
  intros A P nE x p. apply nE. now exists x.
Qed.

Lemma pickable_not_exists : forall A (P : A -> Prop),
  (forall x, decidable (P x)) ->
  pickable (fun x => ~ P x) ->
  ~ (forall x, P x) ->
  exists x, ~ P x.
Proof.
  intros A P D [[x p]|N] nF.
  - now exists x.
  - exfalso. apply nF. intro x. test (P x).
    + now auto.
    + intro n. exfalso. apply N. now exists x.
Qed.

Lemma pickable_equiv : forall A (P1 P2 : A -> Prop),
  (forall a, P1 a <-> P2 a) ->
  pickable P1 ->
  pickable P2.
Proof.
  intros A P1 P2 E [[x p]|N].
  - left. exists x. now apply E.
  - right. intros [x p]. apply N. exists x. now apply E.
Defined.

Lemma pickable2_equiv : forall A1 A2 (P1 P2 : A1 -> A2 -> Prop),
  (forall a1 a2, P1 a1 a2 <-> P2 a1 a2) ->
  pickable2 P1 ->
  pickable2 P2.
Proof.
  intros A1 A2 P1 P2 E [[[x1 x2] p]|N].
  - left. exists (x1, x2). now apply E.
  - right. intros [x1 [x2 p]]. apply N. exists x1. exists x2. now apply E.
Defined.

Lemma pickable3_equiv : forall A1 A2 A3 (P1 P2 : A1 -> A2 -> A3 -> Prop),
  (forall a1 a2 a3, P1 a1 a2 a3 <-> P2 a1 a2 a3) ->
  pickable3 P1 ->
  pickable3 P2.
Proof.
  intros A1 A2 A3 P1 P2 E [[[[x1 x2] x3] p]|N].
  - left. exists (x1, x2, x3). now apply E.
  - right. intros [x1 [x2 [x3 p]]]. apply N.
    exists x1. exists x2. exists x3. now apply E.
Defined.

Lemma pickable4_equiv : forall A1 A2 A3 A4 (P1 P2 : A1 -> A2 -> A3 -> A4 -> Prop),
  (forall a1 a2 a3 a4, P1 a1 a2 a3 a4 <-> P2 a1 a2 a3 a4) ->
  pickable4 P1 ->
  pickable4 P2.
Proof.
  intros A1 A2 A3 A4 P1 P2 E. intros [[[[[x1 x2] x3] x4] p]|N].
  - left. exists (x1, x2, x3, x4). now apply E.
  - right. intros [x1 [x2 [x3 [x4 p]]]]. apply N.
    exists x1. exists x2. exists x3. exists x4. now apply E.
Defined.

Lemma pickable5_equiv : forall A1 A2 A3 A4 A5 (P1 P2 : A1 -> A2 -> A3 -> A4 -> A5 -> Prop),
  (forall a1 a2 a3 a4 a5, P1 a1 a2 a3 a4 a5 <-> P2 a1 a2 a3 a4 a5) ->
  pickable5 P1 ->
  pickable5 P2.
Proof.
  intros A1 A2 A3 A4 A5 P1 P2 E [[[[[[x1 x2] x3] x4] x5] p]|N].
  - left. exists (x1, x2, x3, x4, x5). now apply E.
  - right. intros [x1 [x2 [x3 [x4 [x5 p]]]]]. apply N.
    exists x1. exists x2. exists x3. exists x4. exists x5. now apply E.
Defined.

Lemma pickable_convert : forall A B (P1 P2 : _ -> Prop) (f : A -> B),
  (forall a, P1 a -> P2 (f a)) ->
  (forall b, P2 b -> exists a, P1 a) ->
  pickable P1 ->
  pickable P2.
Proof.
  intros A B P1 P2 f E1 E2 [[x p]|N].
  - left. exists (f x). now apply E1.
  - right. intros [x p]. apply N. destruct (E2 _ p) as [a p']. now exists a.
Defined.

Lemma pickable2_convert : forall A1 A2 B1 B2 (P1 P2 : _ -> _ -> Prop) (f : A1 * A2 -> B1 * B2),
  (forall a1 a2, P1 a1 a2 -> let (b1, b2) := f (a1, a2) in P2 b1 b2) ->
  (forall b1 b2, P2 b1 b2 -> exists a1 a2, P1 a1 a2) ->
  pickable2 P1 ->
  pickable2 P2.
Proof.
  intros A1 A2 B1 B2 P1 P2 f E1 E2 [[[x1 x2] p]|N].
  - left. exists (f (x1, x2)). now apply E1.
  - right. intros [x1 [x2 p]]. apply N. destruct (E2 _ _ p) as [a1 [a2 p']].
    exists a1. now exists a2.
Defined.

Lemma pickable2_weaken : forall A1 A2 (P : A1 -> A2 -> Prop),
  pickable2 P ->
  pickable (fun a1 => exists a2, P a1 a2).
Proof.
  intros A1 A2 P [[[x1 x2] p]|nE].
  - left. exists x1. now exists x2.
  - right. intros [x1 [x2 p]]. apply nE. exists x1. now exists x2.
Defined.

Hint Resolve pickable2_weaken : pickability.

Lemma pickable3_weaken : forall A1 A2 A3 (P : A1 -> A2 -> A3 -> Prop),
  pickable3 P ->
  pickable2 (fun a1 a2 => exists a3, P a1 a2 a3).
Proof.
  intros A1 A2 A3 P [[[[x1 x2] x3] p]|nE].
  - left. exists (x1, x2). now exists x3.
  - right. intros [x1 [x2 [x3 p]]]. apply nE. exists x1. exists x2. now exists x3.
Defined.

Hint Resolve pickable3_weaken : pickability.

Lemma pickable4_weaken : forall A1 A2 A3 A4 (P : A1 -> A2 -> A3 -> A4 -> Prop),
  pickable4 P ->
  pickable3 (fun a1 a2 a3 => exists a4, P a1 a2 a3 a4).
Proof.
  intros A1 A2 A3 A4 P [[[[[x1 x2] x3] x4] p]|nE].
  - left. exists (x1, x2, x3). now exists x4.
  - right. intros [x1 [x2 [x3 [x4 p]]]]. apply nE.
    exists x1. exists x2. exists x3. now exists x4.
Defined.

Hint Resolve pickable4_weaken : pickability.

Lemma pickable5_weaken : forall A1 A2 A3 A4 A5 (P : A1 -> A2 -> A3 -> A4 -> A5 -> Prop),
  pickable5 P ->
  pickable4 (fun a1 a2 a3 a4 => exists a5, P a1 a2 a3 a4 a5).
Proof.
  intros A1 A2 A3 A4 A5 P [[[[[[x1 x2] x3] x4] x5] p]|nE].
  - left. exists (x1, x2, x3, x4). now exists x5.
  - right. intros [x1 [x2 [x3 [x4 [x5 p]]]]]. apply nE.
    exists x1. exists x2. exists x3. exists x4. now exists x5.
Defined.

Hint Resolve pickable5_weaken : pickability.

Lemma pickable_augment : forall A1 A2 (P : A2 -> Prop),
  A1 ->
  pickable P ->
  pickable2 (fun _ : A1 => P).
Proof.
  intros A1 A2 P x1 [[x2 p]|nE].
  - left. now exists (x1, x2).
  - right. intros [_ [x2 p]]. apply nE. now exists x2.
Defined.

Hint Resolve pickable_augment : pickability.

Lemma pickable2_augment : forall A1 A2 A3 (P : A2 -> A3 -> Prop),
  A1 ->
  pickable2 P ->
  pickable3 (fun _ : A1 => P).
Proof.
  intros A1 A2 A3 P x1 [[[x2 x3] p]|nE].
  - left. now exists (x1, x2, x3).
  - right. intros [_ [x2 [x3 p]]]. apply nE. exists x2. now exists x3.
Defined.

Hint Resolve pickable2_augment : pickability.

Lemma pickable3_augment : forall A1 A2 A3 A4 (P : A2 -> A3 -> A4 -> Prop),
  A1 ->
  pickable3 P ->
  pickable4 (fun _ : A1 => P).
Proof.
  intros A1 A2 A3 A4 P x1 [[[[x2 x3] x4] p]|nE].
  - left. now exists (x1, x2, x3, x4).
  - right. intros [_ [x2 [x3 [x4 p]]]]. apply nE.
    exists x2. exists x3. now exists x4.
Defined.

Hint Resolve pickable3_augment : pickability.

Lemma pickable4_augment : forall A1 A2 A3 A4 A5 (P : A2 -> A3 -> A4 -> A5 -> Prop),
  A1 ->
  pickable4 P ->
  pickable5 (fun _ : A1 => P).
Proof.
  intros A1 A2 A3 A4 A5 P x1 [[[[[x2 x3] x4] x5] p]|nE].
  - left. now exists (x1, x2, x3, x4, x5).
  - right. intros [_ [x2 [x3 [x4 [x5 p]]]]]. apply nE.
    exists x2. exists x3. exists x4. now exists x5.
Defined.

Hint Resolve pickable4_augment : pickability.

Lemma decidable_pickable : forall A P,
  A ->
  decidable P ->
  pickable (fun _ : A => P).
Proof.
  intros A P a [p|nP].
  - left. now exists a.
  - right. now intros [_ p].
Defined.

Hint Resolve decidable_pickable : pickability.

Lemma pickable2_decidable : forall A1 A2 (P : A1 -> A2 -> Prop),
  pickable2 P ->
  decidable (exists x1 x2, P x1 x2).
Proof.
  intros A1 A2 P p. apply pickable_decidable. now apply pickable2_weaken.
Defined.

Hint Resolve pickable2_decidable : decidability.

Lemma pickable3_decidable : forall A1 A2 A3 (P : A1 -> A2 -> A3 -> Prop),
  pickable3 P ->
  decidable (exists x1 x2 x3, P x1 x2 x3).
Proof.
  intros A1 A2 A3 P p. apply pickable2_decidable. now apply pickable3_weaken.
Defined.

Hint Resolve pickable3_decidable : decidability.

Lemma pickable4_decidable : forall A1 A2 A3 A4 (P : A1 -> A2 -> A3 -> A4 -> Prop),
  pickable4 P ->
  decidable (exists x1 x2 x3 x4, P x1 x2 x3 x4).
Proof.
  intros A1 A2 A3 A4 P p. apply pickable3_decidable. now apply pickable4_weaken.
Defined.

Hint Resolve pickable4_decidable : decidability.

Lemma pickable5_decidable : forall A1 A2 A3 A4 A5 (P : A1 -> A2 -> A3 -> A4 -> A5 -> Prop),
  pickable5 P ->
  decidable (exists x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5).
Proof.
  intros A1 A2 A3 A4 A5 P p. apply pickable4_decidable. now apply pickable5_weaken.
Defined.

Hint Resolve pickable5_decidable : decidability.

Lemma pickable2_rotate : forall A1 A2 (P : A1 -> A2 -> Prop),
  pickable2 P ->
  pickable2 (fun a2 a1 => P a1 a2).
Proof.
  intros A1 A2 P [[[x1 x2] p]|nE].
  - left. now exists (x2, x1).
  - right. intros [x1 [x2 p]]. apply nE.
    exists x2. now exists x1.
Defined.

Lemma pickable3_rotate : forall A1 A2 A3 (P : A1 -> A2 -> A3 -> Prop),
  pickable3 P ->
  pickable3 (fun a2 a3 a1 => P a1 a2 a3).
Proof.
  intros A1 A2 A3 P [[[[x1 x2] x3] p]|nE].
  - left. now exists (x2, x3, x1).
  - right. intros [x2 [x3 [x1 p]]]. apply nE.
    exists x1. exists x2. now exists x3.
Defined.

Lemma pickable4_rotate : forall A1 A2 A3 A4 (P : A1 -> A2 -> A3 -> A4 -> Prop),
  pickable4 P ->
  pickable4 (fun a2 a3 a4 a1 => P a1 a2 a3 a4).
Proof.
  intros A1 A2 A3 A4 P [[[[[x1 x2] x3] x4] p]|nE].
  - left. now exists (x2, x3, x4, x1).
  - right. intros [x2 [x3 [x4 [x1 p]]]]. apply nE.
    exists x1. exists x2. exists x3. now exists x4.
Defined.

Lemma pickable5_rotate : forall A1 A2 A3 A4 A5 (P : A1 -> A2 -> A3 -> A4 -> A5 -> Prop),
  pickable5 P ->
  pickable5 (fun a2 a3 a4 a5 a1 => P a1 a2 a3 a4 a5).
Proof.
  intros A1 A2 A3 A4 A5 P [[[[[[x1 x2] x3] x4] x5] p]|nE].
  - left. now exists (x2, x3, x4, x5, x1).
  - right. intros [x2 [x3 [x4 [x5 [x1 p]]]]]. apply nE.
    exists x1. exists x2. exists x3. exists x4. now exists x5.
Defined.


Definition pickable_to_option : forall A (P : A -> Prop),
  pickable P ->
  option A.
Proof.
  intros A P [[x p]|nE].
  - exact (Some x).
  - exact None.
Defined.

Lemma pickable_to_option_Some : forall A P (PP : pickable P) (a : A),
  pickable_to_option PP = Some a ->
  P a.
Proof.
  intros A P [[x p]|nE] a E; inversion E.
  now subst.
Qed.

Lemma pickable_to_option_None : forall A P (PP : pickable P) (a : A),
  P a ->
  pickable_to_option PP <> None.
Proof.
  intros A P [[x p]|nE] a pa E; inversion E.
  apply nE. now exists a.
Qed.


(** * Tactics **)

Ltac prove_pickable := now eauto with pickability decidability.

Notation "'pick' P" :=
  (@pickable_to_option _ P ltac:(prove_pickable))
  (at level 70, only parsing).

(** Return the function associated to a function call, whichever the arity. **)
Ltac get_head H :=
  lazymatch H with
  | ?f _ => get_head f
  | ?f => constr:(f)
  end.

(** Given a [pickable_n], apply the right [pickable_n_weaken] lemma. **)
Ltac pickable_weaken H :=
  lazymatch type of H with
  | pickable _ => constr:(pickable_decidable H)
  | pickable2 _ => constr:(pickable2_weaken H)
  | pickable3 _ => constr:(pickable3_weaken H)
  | pickable4 _ => constr:(pickable4_weaken H)
  | pickable5 _ => constr:(pickable5_weaken H)
  end.

(** Given a [pickable_n], and an element [a : A1], apply the right [pickable_n_augment] lemma. **)
Ltac pickable_augment a H :=
  lazymatch type of H with
  | decidable _ => constr:(decidable_pickable a H)
  | pickable _ => constr:(pickable_augment a H)
  | pickable2 _ => constr:(pickable2_augment a H)
  | pickable3 _ => constr:(pickable3_augment a H)
  | pickable4 _ => constr:(pickable4_augment a H)
  end.

(** Given a [pickable_n], apply the right [pickable_n_rotate] lemma. **)
Ltac pickable_rotate H :=
  lazymatch type of H with
  | decidable _ => constr:(H)
  | pickable _ => constr:(H)
  | pickable2 _ => constr:(pickable2_rotate H)
  | pickable3 _ => constr:(pickable3_rotate H)
  | pickable4 _ => constr:(pickable4_rotate H)
  | pickable5 _ => constr:(pickable5_rotate H)
  end.

(** Return the arity [n] of a [pickable_n] property. **)
Ltac pickable_arity H :=
  let h := get_head H in
  lazymatch h with
  | decidable => constr:(0 : nat)
  | pickable => constr:(1 : nat)
  | pickable2 => constr:(2 : nat)
  | pickable3 => constr:(3 : nat)
  | pickable4 => constr:(4 : nat)
  | pickable5 => constr:(5 : nat)
  end.

(** Given a [pickable_n] property, produce a [decidable]. **)
Ltac to_decidable H :=
  lazymatch type of H with
  | pickable _ => constr:(pickable_decidable H)
  | _ => to_decidable ltac:(pickable_weaken H)
  end.

(** A tactic to try to apply the right lemmas above to make [H] appliable to the goal. **)
Ltac convert_pickable H :=
  lazymatch goal with
  | |- ?g =>
    let ag := pickable_arity g in
    let rec aux H :=
			let Ht := type of H in
      let aH := pickable_arity Ht in
      let le := eval compute in (Nat.leb ag aH) in
      lazymatch le with
      | true =>
        let eq := eval compute in (Nat.eqb ag aH) in
        lazymatch eq with
        | true => (* ag = aH *)
          lazymatch g with
          | decidable _ => first [ apply H | refine (decidable_equiv _ H) ]
          | pickable _ => first [ apply H | refine (pickable_equiv _ H) ]
          | pickable2 _ => first [ apply H | refine (pickable2_equiv _ H) ]
          | pickable3 _ => first [ apply H | refine (pickable3_equiv _ H) ]
          | pickable4 _ => first [ apply H | refine (pickable4_equiv _ H) ]
          | pickable5 _ => first [ apply H | refine (pickable5_equiv _ H) ]
          end; auto
        | false => (* ag < aH *)
          let rec aux' n H :=
            lazymatch n with
            | 0 => fail
            | S ?n =>
              let H := pickable_weaken H in
              first [ aux H
                    | let H := pickable_rotate H in
                      aux' n H ]
            end in
          aux' aH H
        end
      | false => (* ag > aH *)
        let rec aux' n H :=
          lazymatch n with
          | 0 => fail
          | S ?n =>
            let H := pickable_augment H in
            first [ aux H
                  | let H := pickable_rotate H in
                    aux' n H ]
          end in
        aux' aH H
      end in
    aux H
  end.

