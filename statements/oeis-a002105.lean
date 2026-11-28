import Mathlib

/-!
# OEIS A002105: reduced tangent numbers modulo `k`

Source: https://oeis.org/A002105
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = 2^n (2^(2n) - 1) |B_{2n}| / n` (`n ≥ 1`), the reduced tangent numbers
`1, 1, 4, 34, 496, …`. Conjecture (OEIS entry): for every integer `k`, the sequence
`a(n) mod k` is eventually periodic with a period dividing `φ(k)`.

Conventions:
* `k ≥ 1` (for `k = 1` everything is `0`). 'Eventually purely periodic with period dividing
  `φ(k)`' means: there is `N` with `a(n + φ(k)) ≡ a(n) (mod k)` for all `n ≥ N`.
* `a n` is computed in `ℚ` from Mathlib's `bernoulli` and is an integer; the congruence is
  stated for the rational numbers via `∃ z : ℤ, a (n + φ k) - a n = k z`.
-/

namespace OMA.S_oeis_a002105

/-- The reduced tangent numbers `a(n) = 2^n (2^(2n) - 1) |B_{2n}| / n`. -/
noncomputable def a (n : ℕ) : ℚ :=
  2 ^ n * (2 ^ (2 * n) - 1) * |bernoulli (2 * n)| / n

/-- `a(n) mod k` is eventually periodic with period dividing `φ(k)`. -/
theorem main : ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n →
    ∃ z : ℤ, a (n + Nat.totient k) - a n = (k : ℚ) * z := by
  sorry

end OMA.S_oeis_a002105
