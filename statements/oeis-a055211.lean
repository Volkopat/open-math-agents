import Mathlib

/-!
# OEIS A055211: lesser Fortunate numbers are prime

Source: https://oeis.org/A055211
The lesser Fortunate number of `n ≥ 2` is the least `m > 1` such that `p_n# - m` is prime,
where `p_n#` is the product of the first `n` primes. The first 1000 terms are all prime, and
it is conjectured that all terms are primes.

Conventions. `p_n# = primorial (p_n)` with `p_n = Nat.nth Nat.Prime (n - 1)` (Mathlib's
`primorial m` is the product of the primes `≤ m`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a055211

/-- The `n`-th primorial `p_n#`. -/
noncomputable def P (n : ℕ) : ℕ := primorial (Nat.nth Nat.Prime (n - 1))

/-- The lesser Fortunate number of `n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m | 1 < m ∧ m < P n ∧ (P n - m).Prime}

theorem main : ∀ n : ℕ, 2 ≤ n → (a n).Prime := by
  sorry

end OMA.S_oeis_a055211
