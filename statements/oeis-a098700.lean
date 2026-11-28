import Mathlib

/-!
# A098700: Numbers k such that x' = k has no integer solution

Source: https://oeis.org/A098700
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Numbers k such that x' = k has no integer solution, where x' is the arithmetic derivative of x.
Conjecture (implied by Goldbach's conjecture): No even integer k > 2 appears in this sequence.
-/

namespace OMA.S_oeis_a098700

def arithDeriv (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∑ p ∈ n.primeFactors, n.factorization p * (n / p)

theorem main :
    ∀ k : ℕ, 2 < k → Even k → ∃ x : ℕ, arithDeriv x = k := by
  sorry

end OMA.S_oeis_a098700
