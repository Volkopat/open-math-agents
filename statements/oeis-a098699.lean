import Mathlib

/-!
# A098699: Anti-derivative of n (least x with arithmetic derivative x' = n, or 0)

Source: https://oeis.org/A098699
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(n) is the least natural number x whose arithmetic derivative x' equals n, or 0 if no such x exists.
Conjecture (implied by Goldbach's conjecture): For every k >= 2, 0 < a(2*k) and a(2*k) <= k^2.
-/

namespace OMA.S_oeis_a098699

def arithDeriv (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∑ p ∈ n.primeFactors, n.factorization p * (n / p)

noncomputable def a (n : ℕ) : ℕ :=
  sInf {x : ℕ | arithDeriv x = n}

theorem main :
    ∀ k : ℕ, 2 ≤ k → 0 < a (2 * k) ∧ a (2 * k) ≤ k ^ 2 := by
  sorry

end OMA.S_oeis_a098699
