import Mathlib

/-! OEIS A140320 and its stated growth consequences for A137576. -/

namespace OMA.S_oeis_a140320

/-- Multiplicative order of 2 modulo d. -/
noncomputable def ordTwo (d : ℕ) : ℕ := orderOf (2 : ZMod d)

/-- The divisor-sum formula for OEIS A137576. -/
noncomputable def a137576 (n : ℕ) : ℕ :=
  let N := 2 * n + 1
  1 + ordTwo N * ((∑ d ∈ N.divisors, d.totient / ordTwo d) - 1)

/-- The closed formula and the lower envelope and unbounded quotient of A137576. -/
theorem main :
    (∀ n : ℕ, a137576 ((3 ^ n - 1) / 2) = 2 * n * 3 ^ (n - 1) + 1) ∧
    (∀ n : ℕ, 2 * n + 1 ≤ a137576 n) ∧
    (∀ n : ℕ, (2 * n + 1).Prime → a137576 n = 2 * n + 1) ∧
    (∀ N : ℕ, ∃ n ≥ N, a137576 n = 2 * n + 1) ∧
    (∀ B N : ℕ, ∃ n : ℕ, N ≤ n ∧ B * n < a137576 n) := by
  sorry

end OMA.S_oeis_a140320
