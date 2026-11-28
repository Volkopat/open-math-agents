import OMAStatements.S_oeis_a236305

-- Problem: A236305: The number of P-positions in the game of Nim with up to 3 piles, allowing for piles of zero, such that the number of objects in each pile does not exceed n.
-- Upstream: formal-conjectures statements/oeis-a236305.lean:0 (declaration OMA.S_oeis_a236305.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: at n = 1 the four triples (0,0,0), (0,1,1), (1,0,1), (1,1,0) give a(1) = 4, while the
-- formula gives 4^0 + 3*(1 mod 1)^2 = 1. (The formula fits a(n-1), not a(n).)

open OMA.S_oeis_a236305 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a236305.main) := by
  intro H
  exact absurd (H 1 le_rfl) (by decide)
