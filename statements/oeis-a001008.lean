import Mathlib

/-!
# OEIS A001008: a binomial-sum formula for harmonic numbers

Source: https://oeis.org/A001008
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A001008 is the numerator of `H(n) = ∑_{i=1}^{n} 1/i`. Conjecture (OEIS entry): for nonzero `m`,
`H(n) = (1/m) ∑_{k=1}^{n} ((-1)^(k+1)/k) · C(m k, k) · C(n + (m-1) k, n - k)`.

Conventions:
* `m` ranges over nonzero integers and `n` over natural numbers. For negative `m` the binomial
  coefficients have negative upper argument, so `C(x, j)` is the generalised binomial
  coefficient `x (x-1) ⋯ (x-j+1) / j!` (`Ring.choose` in `ℚ`); for `m ≥ 1` it is the usual one.
-/

namespace OMA.S_oeis_a001008

/-- The harmonic number `H(n)`. -/
def H (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, (1 : ℚ) / (i + 1)

/-- The conjectured identity, for every nonzero integer `m`. -/
theorem main : ∀ (m : ℤ), m ≠ 0 → ∀ n : ℕ,
    H n = (1 / (m : ℚ)) * ∑ k ∈ Finset.Icc 1 n,
      ((-1 : ℚ) ^ (k + 1) / k) * Ring.choose ((m * k : ℤ) : ℚ) k *
        Ring.choose ((n + (m - 1) * k : ℤ) : ℚ) (n - k) := by
  sorry

end OMA.S_oeis_a001008
