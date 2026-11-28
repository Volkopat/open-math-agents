import Mathlib

/-!
# OEIS A034015: small 3-Schröder numbers, a double-sum formula

Source: https://oeis.org/A034015
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = ∑_{k=0}^{n} 2^k C(n, k) C(2n+2, k)/(k + 1)`. Conjecture (Weiner; proved by Easwar,
Theorem 3.8): `a(n) = ∑_{i=0}^{n} ∑_{j=0}^{i} (-2)^(n-i) C(i, j) C(2i+j, n) C(n+1, i)/(n + 1)`.

Conventions:
* Both sums are computed in `ℚ`; `n ≥ 0`.
-/

namespace OMA.S_oeis_a034015

/-- The small 3-Schröder numbers. -/
def a (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), 2 ^ k * (n.choose k : ℚ) * ((2 * n + 2).choose k : ℚ) / (k + 1)

/-- Weiner's double-sum formula. -/
theorem main : ∀ n : ℕ, a n = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1),
    (-2 : ℚ) ^ (n - i) * (i.choose j : ℚ) * ((2 * i + j).choose n : ℚ) * ((n + 1).choose i : ℚ) /
      (n + 1) := by
  sorry

end OMA.S_oeis_a034015
