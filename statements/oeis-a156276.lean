import Mathlib

/-!
# A156276: denominator of Euler(n, 1/10)

Source: https://oeis.org/A156276
Credit: @sntntHb

`a(n)` is the denominator of `E_n(1/10)`, where `E_n` is the `n`-th Euler polynomial (offset 0).
The data begins `1, 5, 100, 250, 10000, 25000, 1000000, 2500000, ...`.

The entry records the conjecture (Harvey P. Dale, Apr 17 2024): the sequence satisfies a linear
recurrence with signature `(0, 100)`, i.e. `a(n) = 100 * a(n-2)`. The recurrence fails at `n = 3`
(`a(3) = 250` but `100 * a(1) = 500`) and holds for `4 ≤ n ≤ 40` numerically, so `main` states it
for `n ≥ 4`, written `a(n+2) = 100 * a(n)` for `n ≥ 2`.

The Euler polynomials are given by the standard recurrence
`E_n(x) = x^n - (1/2) * Σ_{k<n} C(n,k) E_k(x)`, equivalent to the defining identity
`Σ_{k ≤ n} C(n,k) E_k(x) + E_n(x) = 2 x^n` (from the generating function `2 e^{xt} / (e^t + 1)`);
`eulerAt x n` is `E_n(x)` for rational `x`, and `Rat.den` gives the reduced denominator.
-/

namespace OMA.S_oeis_a156276

/-- `eulerAt x n` is the value `E_n(x)` of the `n`-th Euler polynomial at a rational `x`. -/
def eulerAt (x : ℚ) : ℕ → ℚ
  | n => x ^ n - (1 / 2) * ∑ k : Fin n, (n.choose k : ℚ) * eulerAt x k
decreasing_by exact k.isLt

/-- `a n`: the denominator of `E_n(1/10)` (OEIS A156276). -/
def a (n : ℕ) : ℕ := (eulerAt (1 / 10) n).den

/-- Conjecture of OEIS A156276: `a(n) = 100 a(n-2)` for `n ≥ 4`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → a (n + 2) = 100 * a n := by
  sorry

end OMA.S_oeis_a156276
