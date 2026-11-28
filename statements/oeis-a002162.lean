import Mathlib

/-!
# OEIS A002162: a family of rapidly convergent series for `log 2`

Source: https://oeis.org/A002162
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Bala, 2023): for every `k ≥ 0`,
`log 2 = c(k) + (2k)!³ / (16^k k!²) · ∑_{n ≥ 1} (-1)^(n+k+1) (n + k) / (n (n+1) ⋯ (n+2k))²`
for some rational number `c(k)`.

Conventions:
* `n (n+1) ⋯ (n+2k)` is `∏_{i=0}^{2k} (n + i)`; the series converges absolutely and is a
  `tsum` over `n ≥ 1` (indexed as `n + 1`, `n : ℕ`).
-/

namespace OMA.S_oeis_a002162

/-- The `k`-th series. -/
noncomputable def S (k : ℕ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ (n + 1 + k + 1) * ((n + 1 + k : ℕ) : ℝ) /
    (∏ i ∈ Finset.range (2 * k + 1), ((n + 1 + i : ℕ) : ℝ)) ^ 2

/-- For each `k`, `log 2 - (2k)!³/(16^k k!²) · S(k)` is rational. -/
theorem main : ∀ k : ℕ, ∃ c : ℚ,
    Real.log 2 = c + ((2 * k).factorial : ℝ) ^ 3 / (16 ^ k * (k.factorial : ℝ) ^ 2) * S k := by
  sorry

end OMA.S_oeis_a002162
