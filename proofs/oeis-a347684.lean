import OMAStatements.S_oeis_a347684

-- Problem: A347684: Array read by antidiagonals: T(n,k) (n>=1, k>=1) = f(n,k), where f(x,y) = x*red_inv(x,y) + y*red_inv(y,x) if gcd(x,y)=1, or 0 if gcd(x,y)>1, and red_inv is defined in the comments.
-- Upstream: formal-conjectures statements/oeis-a347684.lean:0 (declaration OMA.S_oeis_a347684.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: n = 1, j = 1, i = 1, so k = 2. T(1,2) = f(1,2) = 1*1 + 2*0 = 1 and f(1,1) = 0, so
-- A347687(1,1) = (1 - 0)/2 = 0 (integer division), and the claimed value is 0 + 2*1*1*0 = 0.

open OMA.S_oeis_a347684 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a347684.main) := by
  intro H
  exact absurd (H 1 1 1 le_rfl le_rfl le_rfl) (by decide)
