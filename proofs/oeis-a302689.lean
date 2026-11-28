import OMAStatements.S_oeis_a302689

-- Problem: A302689: a(n) = 4 + 2^n - 4*n.
-- Upstream: formal-conjectures statements/oeis-a302689.lean:0 (declaration OMA.S_oeis_a302689.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: n = 6 is a counterexample. a(6) = 4 + 64 - 24 = 44, while A258547(6 - 5) = A258547(1)
-- counts all 16 arrays of 0..1 of size 2X2: such an array has a single 2X2 subblock, so both
-- monotonicity conditions are vacuous. And 44 is not 16.

open OMA.S_oeis_a302689 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a302689.main) := by
  intro H
  exact absurd (H 6 (by decide)) (by decide)
