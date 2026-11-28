import Mathlib

/-!
# A088120: Smallest prime obtained as product of n terms of an AP + common difference

Source: https://oeis.org/A088120
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(n) is the smallest prime obtained as a product of n terms of a positive
arithmetic progression plus the common difference:
  a * (a + d) * ... * (a + (n - 1) * d) + d   (a >= 1, d >= 1).
Conjectures:
(1) The sequence is infinite (such a prime exists for every n >= 1).
(2) The common difference d giving a(n) is 1, except for n = 4 and n = 5 where it is 2.
-/

namespace OMA.S_oeis_a088120

/-- Product of `n` terms of an arithmetic progression starting at `a` with step `d`, plus `d`. -/
def apProdPlus (n a d : ℕ) : ℕ :=
  (∏ i ∈ Finset.range n, (a + i * d)) + d

/-- The smallest prime of the form `apProdPlus n a d` with `a ≥ 1`, `d ≥ 1`. -/
noncomputable def minPrime (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ ∃ a d : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ apProdPlus n a d = p}

theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ a d : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ (apProdPlus n a d).Prime) ∧
    (∀ n : ℕ, 1 ≤ n →
      ∃ a : ℕ, 1 ≤ a ∧ apProdPlus n a (if n = 4 ∨ n = 5 then 2 else 1) = minPrime n) := by
  sorry

end OMA.S_oeis_a088120
