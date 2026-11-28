import Mathlib

/-!
# OEIS A111869: least k with n² ∣ C(2k, k)

Source: https://oeis.org/A111869
`a n` is the least `k` such that `binom(2k, k)` is divisible by `n²`. Conjecture 1:
`a(n) = (n² - 1)/2 + 1` for odd primes `n`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a111869

/-- A111869. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k | 1 ≤ k ∧ n ^ 2 ∣ (2 * k).choose k}

theorem main : ∀ p : ℕ, p.Prime → p ≠ 2 → a p = (p ^ 2 - 1) / 2 + 1 := by
  sorry

end OMA.S_oeis_a111869
