
(* TODO: Explain the problem *)

Record game_state := {
    length : nat * nat ;
    state : { x | x < fst length } -> { y | y < fst length } -> bool
  }.

