
(* TODO: Explain the problem *)

Record game_state := {
    length : nat * nat ;
    state : nat -> nat -> bool ;
    state_out_x : forall x y, x >= fst length -> state x y = false ;
    state_out_y : forall x y, y >= snd length -> state x y = false ;
    state_origin : state 0 0 = true
  }.

(** With this definition, we know that there is at least one tile. **)
Lemma game_state_length_gt_0 : forall st : game_state,
  fst (length st) <> 0 /\ snd (length st) <> 0.
Proof.
  intro st. pose (E := state_origin st).
  split; intro E0.
  - rewrite state_out_x in E.
    + now inversion E.
    + now rewrite E0; auto.
  - rewrite state_out_y in E.
    + now inversion E.
    + now rewrite E0; auto.
Qed.

