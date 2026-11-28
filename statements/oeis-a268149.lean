import Mathlib

/-!
# OEIS A268149

Richard P. Brent's double binomial sum and the recurrence conjectured by
R. J. Mathar. Source: https://oeis.org/A268149 (offset zero).

The summation indices are translated by n, so the difference of the
two translated indices is still the original signed difference.
-/

namespace OMA.S_oeis_a268149

def a (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (2 * n + 1), ∑ j ∈ Finset.range (2 * n + 1),
    ((2 * n).choose i : ℤ) * ((2 * n).choose j : ℤ) * |(i : ℤ) - j| ^ 3

theorem main : ∀ k : ℕ, let n : ℤ := k + 2
    (2 * n - 1) * (n - 1) * a (k + 2) +
      2 * (-22 * n ^ 2 + 27 * n - 36) * a (k + 1) +
      12 * (4 * n - 5) * (4 * n - 7) * a k = 0 := by
  sorry

end OMA.S_oeis_a268149
