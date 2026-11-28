import OMAStatements.S_oeis_a288429

-- Refutation of the statement in #22129 (statement by @blakestone-x). Credit: @bnb9001
-- With the printed rule (1 -> 100, 01 -> 0100, 00 -> 0101) every pass doubles the length:
-- word 2 = 01000100 has length 8, while reference 2 = 5.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a288429.main) := by
  intro h
  have h2 := h 2
  revert h2
  decide
