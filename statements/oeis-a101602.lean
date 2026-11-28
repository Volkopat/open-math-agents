import Mathlib

/-!
# A101602: Expansion of g.f. c(3x)^4, where c(x) is the g.f. of A000108

Source: https://oeis.org/A101602
Credit: @jagong-cmu

The sequence (offset 0) starts 1, 12, 126, 1296, 13365, 138996, ...

Conjecture (R. J. Mathar, 2011): (n+4)*a(n) - 6*(3*n+7)*a(n-1) + 36*(2*n+1)*a(n-2) = 0.

Conventions:
* `c` is the ordinary generating function `Sum_{n ≥ 0} catalan(n) x^n` of the Catalan numbers
  A000108, in `PowerSeries ℤ`. The substitution `x ↦ 3x` is `PowerSeries.rescale 3`, so
  `a n` is the coefficient of `x^n` in `(rescale 3 c)^4`.
* The recurrence is stated in `ℤ` for `n ≥ 2`, where all of `a(n)`, `a(n-1)`, `a(n-2)` are terms
  of the sequence (offset 0), so the truncated subtractions `n - 1`, `n - 2` are exact.
  (With the usual convention a(-1) = 0 the recurrence also holds at n = 1; that case is not
  part of this statement.)
-/

namespace OMA.S_oeis_a101602

/-- The g.f. `c(x) = Sum_{n ≥ 0} catalan(n) x^n` of A000108. -/
def c : PowerSeries ℤ := PowerSeries.mk fun n => (catalan n : ℤ)

/-- A101602: the coefficient of `x^n` in `c(3x)^4`. -/
noncomputable def a (n : ℕ) : ℤ := PowerSeries.coeff n ((PowerSeries.rescale (3 : ℤ) c) ^ 4)

/-- Mathar's conjectured recurrence, for `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℤ) + 4) * a n - 6 * (3 * (n : ℤ) + 7) * a (n - 1) +
      36 * (2 * (n : ℤ) + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a101602
