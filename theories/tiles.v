
From Lib Require Import decide pick explore.
Open Scope nat_scope.

(** This problem was given to me by Rao Xiaojia.
  It is about a two-player game in which players remove tiles in a two-dimensional grid. **)

(** Let us consider a finite set of tiles, as follows:
[[
  O X X X X X X X X X X X X X X X X X X X X X
  X X X X X X X X X X X X X X X X X X X X X X
  X X X X X X X X X X X X X X X X X X X X X X
  X X X X X X X X X X X X X X X X X X X X X X
  X X X X X X X X X X X X X X X X X X X X X X
]]

  Each [X] represents a tile.
  The origin [O] is special: it can never be removed. **)

Record board := {
    length : nat * nat ;
    state : nat -> nat -> bool ;
    state_out_x : forall x y, x >= fst length -> state x y = false ;
    state_out_y : forall x y, y >= snd length -> state x y = false ;
    state_origin : state 0 0 = true
  }.

(** The board is never void: there is at least the origin tile. **)
Lemma board_length_gt_0 : forall st : board,
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

(** The initial board is simply filled with tiles. **)
Program Definition initial x y (Ix : x > 0) (Iy : y > 0) := {|
    length := (x, y) ;
    state := fun x' y' => (x' <? x) && (y' <? y)
  |}.
Next Obligation.
Proof.
  do 2 erewrite Nat.ltb_antisym. now erewrite leb_correct.
Qed.
Next Obligation.
Proof.
  do 2 erewrite Nat.ltb_antisym. erewrite andb_comm. now erewrite leb_correct.
Qed.
Next Obligation.
Proof.
  do 2 erewrite Nat.ltb_antisym. now repeat erewrite leb_correct_conv.
Qed.

(** A board is entirely represented by its state. **)
Definition board_equiv (b1 b2 : board) := forall x y, state b1 x y = state b2 x y.

(** [board_equiv] is an equivalence relation. **)

Lemma board_equiv_refl : forall b, board_equiv b b.
Proof.
  now intros b x y.
Qed.

Lemma board_equiv_sym : forall b1 b2,
  board_equiv b1 b2 ->
  board_equiv b2 b1.
Proof.
  now intros b1 b2 E x y.
Qed.

Lemma board_equiv_trans : forall b1 b2 b3,
  board_equiv b1 b2 ->
  board_equiv b2 b3 ->
  board_equiv b1 b3.
Proof.
  intros b1 b2 b3 E12 E23 x y. rewrite E12. now rewrite E23.
Qed.

(** The rules of the game are simple: at each turn, the current player chooses
  a [X] tile.  Then every tile below or right of the chosen tile (including the
  current tile itself) is removed from the game.

  For instance, the first player can remove the following [-] tiles:
[[
  O X X X X X X X X X X X X X X X X X X X X X
  X X X X X X X X X X X X X X X X X X X X X X
  X X X X X X X X X X X X X X X X - - - - - -
  X X X X X X X X X X X X X X X X - - - - - -
  X X X X X X X X X X X X X X X X - - - - - -
]]

  Then the second player can continue by removing the following tiles:
[[
  O X X X X X X X X X X X X X X X X X X X X X
  X X X X X X X X X X X X X X X X X X X X X X
  X X X X X X X X X X X X X X X X            
  X X X X X X X X - - - - - - - -            
  X X X X X X X X - - - - - - - -            
]]

  The first player who can no longer play looses.
**)

(** Given a board, and a turn position [(x, y)], recognize the resulting board. **)
Record turn_position (st : board) x y (st' : board) : Prop := {
    turn_valid : state st x y = true ;
    turn_update : forall x' y',
      state st' x' y' =
        if (x' <? x) || (y' <? y) then
          state st x' y'
        else false
  }.

Definition turn (st st' : board) : Prop :=
  exists x y, turn_position st x y st'.

(** Reconstruct the board from a position [(x, y)]. **)
Local Program Definition make_turn st x y (valid : state st x y = true) (not_origin : x <> 0 \/ y <> 0) := {|
    length := length st ;
    state x' y' :=
      if (x' <? x) || (y' <? y) then
        state st x' y'
      else false
  |}.
Next Obligation.
Proof.
  destruct orb; auto. now apply state_out_x.
Qed.
Next Obligation.
Proof.
  destruct orb; auto. now apply state_out_y.
Qed.
Next Obligation.
Proof.
  rewrite state_origin. destruct orb eqn: E; auto.
  destruct (orb_false_elim _ _ E) as [E1 E2].
  apply Nat.ltb_ge in E1. apply Nat.ltb_ge in E2.
  apply le_n_0_eq in E1. apply le_n_0_eq in E2. subst.
  now destruct not_origin as [D|D].
Qed.

Local Lemma make_turn_correct : forall st x y valid not_origin,
  turn_position st x y (make_turn st x y valid not_origin).
Proof.
  intros st x y valid not_origin. now constructor.
Qed.

(** We can use the definition [make_turn] to show that the next turn is explorable. **)
Lemma turn_pickable : forall st x y,
  pickable (turn_position st x y). (* TODO: explorable *)
Proof.
  intros st x y. dtest (state st x y = true /\ (x <> 0 \/ y <> 0)).
  - intros [valid not_origin]. left.
    exists (make_turn st x y valid not_origin). now apply make_turn_correct.
  - intros A. right. intros [b T]. destruct A as [D|[? ?]].
    + apply D. now apply turn_valid with b.
    + subst. pose (E := state_origin b).
      now rewrite (turn_update _ _ _ _ T) in E.
Defined.

(** If the current player can’t play, then only the origin is left on the board. **)
Lemma no_turn_only_origin : forall st,
  (forall st', ~ turn st st') -> forall x y,
  state st x y = true <-> x = 0 /\ y = 0.
Proof.
  intros st N x y. test (x = 0 /\ y = 0).
  - intros [? ?]. subst. split; auto.
    intro. now apply state_origin.
  - intro nE. assert (not_origin : x <> 0 \/ y <> 0).
    { now test (x = 0); auto. }
    clear nE. split.
    + intro E'. exfalso. eapply N. do 2 eexists.
      now apply make_turn_correct with (valid := E') (not_origin := not_origin).
    + intros [? ?]. subst. now inversion not_origin.
Qed.

(** We can now state the puzzle: for which value of [x] and [y] is there a winning
  strategy for the first player starting from [initial x y _ _]? **)

(** If [x = y = 1], then only the origin is there and the first player immediately looses. **)

Lemma x_y_1 : forall st,
  ~ turn (initial 1 1 ltac:(apply gt_Sn_O) ltac:(apply gt_Sn_O)) st.
Proof.
  intros st [x [y turn]].
  assert (Exy : x = 0 /\ y = 0).
  {
    pose (E := turn_valid _ _ _ _ turn).
    simpl in E. apply andb_true_iff in E. destruct E as [E1 E2].
    apply Nat.ltb_lt in E1. apply Nat.ltb_lt in E2.
    apply Nat.lt_1_r in E1. now apply Nat.lt_1_r in E2.
  }
  destruct Exy as [? ?]. subst.
  pose (E := turn_update _ _ _ _ turn 0 0).
  simpl in E. now rewrite state_origin in E.
Qed.

(** My first approach was to explore strategies.
  For instance, here is a nice winning strategy if given a square:
[[
  O X X X X
  X X X X X
  X X X X X
  X X X X X
  X X X X X
]]
  The first move consists in taking the tile [(1, 1)]:
[[
  O X X X X
  X - - - -
  X - - - -
  X - - - -
  X - - - -
]]
  Then, the idea is to mimick what the second players does on the other branch.
  For instance, if the second player does:
[[
  O X X - -
  X        
  X        
  X        
  X        
]]
  Just make the symmetrical move:
[[
  O X X    
  X        
  X        
  -        
  -        
]]
  This will continue until the second player will no longer be able to play. **)

(* TODO *)

