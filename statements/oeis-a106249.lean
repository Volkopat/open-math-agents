import Mathlib

/-!
# A106249: Expansion of (1-x+x^2+x^3)/((1+x)*(1+x^2)*(1-x)^2).

Source: https://oeis.org/A106249
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (offset 0, data 1, 0, 1, 2, 3, 2, 3, 4, 5, 4, 5, 6, 7, 6, 7, 8, ...) records in its
FORMULA section:

  a(n) = Sum_{k=0..n} Jacobi(2^k, 2k+1) (Conjecture). - Paul Barry, Jul 23 2005

Conventions:
* The sequence is indexed from `0`, as in the entry (offset 0).
* The sequence is defined from its name: `a n` is the coefficient of `x^n` in the power series
  expansion (over `ℤ`) of `(1-x+x^2+x^3)/((1+x)*(1+x^2)*(1-x)^2)`. The denominator has constant
  coefficient `1`, so it is a unit in `ℤ⟦X⟧`, and the quotient is the numerator times
  `PowerSeries.invOfUnit` of the denominator (with the unit `1` as its constant coefficient).
* `Jacobi(a, b)` is the Jacobi symbol, Mathlib's `jacobiSym a b` with `a : ℤ` and `b : ℕ`;
  here `b = 2k+1` is odd, so the Jacobi symbol is the usual one.
* The conjecture is stated for every `n ≥ 0`, with the sum over `k = 0, 1, ..., n`.
-/

namespace OMA.S_oeis_a106249

open PowerSeries

/-- The denominator `(1+x)*(1+x^2)*(1-x)^2`, a power series with constant coefficient `1`. -/
noncomputable def den : PowerSeries ℤ := (1 + X) * (1 + X ^ 2) * (1 - X) ^ 2

/-- The numerator `1-x+x^2+x^3`. -/
noncomputable def num : PowerSeries ℤ := 1 - X + X ^ 2 + X ^ 3

/-- The generating function `(1-x+x^2+x^3)/((1+x)*(1+x^2)*(1-x)^2)` of A106249. -/
noncomputable def gf : PowerSeries ℤ := num * invOfUnit den 1

/-- A106249: `a n` is the coefficient of `x^n` in the expansion of the generating function. -/
noncomputable def a (n : ℕ) : ℤ := coeff n gf

/-- The conjecture of A106249 (Paul Barry): `a(n) = Sum_{k=0..n} Jacobi(2^k, 2k+1)`. -/
theorem main : ∀ n : ℕ,
    a n = ∑ k ∈ Finset.range (n + 1), jacobiSym ((2 : ℤ) ^ k) (2 * k + 1) := by
  sorry

end OMA.S_oeis_a106249
