import Mathlib

/-!
# A199944: Number of -n..n arrays x(0..2) of 3 elements with zeroth through 2nd differences all nonzero.

Source: https://oeis.org/A199944
Conjectures: Colin Barker, May 17 2018
Credit: @ceejcake

An array `x(0..2)` with entries in `-n..n` has zeroth differences `x0, x1, x2`, first differences
`x1 - x0, x2 - x1` and second difference `x2 - 2*x1 + x0`; all of them must be nonzero.
The offset is 1. Conjectures (Barker):
* G.f.: `2*x*(1 + 15*x + 19*x^2 + 13*x^3) / ((1 - x)^4*(1 + x))`;
* `a(n) = 6*n - 10*n^2 + 8*n^3` for `n` even;
* `a(n) = -2 + 6*n - 10*n^2 + 8*n^3` for `n` odd.

The generating function is stated as an identity of formal power series over `ℤ`, cleared of its
denominator. The power series is `∑ a(n) x^n` over all `n ≥ 0`; the definition gives `a(0) = 0`
(the only array for `n = 0` is all zero), so this is the series `∑_{n ≥ 1} a(n) x^n` of the entry.
-/

namespace OMA.S_oeis_a199944

/-- `a n` is the number of triples `(x0, x1, x2)` with every entry in `-n..n` such that the
zeroth differences `x0, x1, x2`, the first differences `x1 - x0, x2 - x1` and the second
difference `x2 - 2*x1 + x0` are all nonzero. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    fun x : ℤ × ℤ × ℤ =>
      x.1 ≠ 0 ∧ x.2.1 ≠ 0 ∧ x.2.2 ≠ 0 ∧ x.2.1 - x.1 ≠ 0 ∧ x.2.2 - x.2.1 ≠ 0 ∧
        x.2.2 - 2 * x.2.1 + x.1 ≠ 0).card

/-- Barker's conjectures for A199944: the generating function
`2*x*(1 + 15*x + 19*x^2 + 13*x^3) / ((1 - x)^4*(1 + x))` and the closed forms
`a(n) = 6*n - 10*n^2 + 8*n^3` for even `n ≥ 1` and `a(n) = -2 + 6*n - 10*n^2 + 8*n^3` for odd `n ≥ 1`. -/
theorem main :
    ((1 - PowerSeries.X) ^ 4 * (1 + PowerSeries.X) * PowerSeries.mk (fun n => (a n : ℤ)) =
        2 * PowerSeries.X *
          (1 + 15 * PowerSeries.X + 19 * PowerSeries.X ^ 2 + 13 * PowerSeries.X ^ 3)) ∧
      (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℤ) = 6 * n - 10 * n ^ 2 + 8 * n ^ 3) ∧
      (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℤ) = -2 + 6 * n - 10 * n ^ 2 + 8 * n ^ 3) := by
  sorry

end OMA.S_oeis_a199944
