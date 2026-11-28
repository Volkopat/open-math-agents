import Mathlib

/-!
# A002104: Logarithmic numbers.

Source: https://oeis.org/A002104
Credit: @divmxnd0x

Conjecture (R. J. Mathar, Dec 02 2012, stated in A002104):
`a(n) + (-n-1) a(n-1) + 2 (n-1) a(n-2) + (-n+2) a(n-3) = 0`.

Formalization notes:
* `a n = ∑_{k=1}^{n} binomial(n, k) (k-1)!`, the coefficient of `x^n / n!` in `-log(1-x) exp(x)`
  (the e.g.f. of A002104); offset 0: `a 0, a 1, ... = 0, 1, 3, 8, 24, 89, 415, ...`.
* The recurrence involves `a(n-3)`, so it is stated for `n ≥ 3`, in `ℤ`.
-/

namespace OMA.S_oeis_a002104

/-- A002104(n) = ∑_{k=1}^{n} binomial(n, k) (k-1)!. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, ((n.choose k * (k - 1).factorial : ℕ) : ℤ)

/-- Mathar's recurrence for the logarithmic numbers. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    a n + (-(n : ℤ) - 1) * a (n - 1) + 2 * ((n : ℤ) - 1) * a (n - 2) + (-(n : ℤ) + 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a002104
