import Mathlib

/-!
# A227721: Floor(1/s(n)), where s(n) = (2n+1)/(2n+2) - n*log((n+1)/n).

Source: https://oeis.org/A227721
Credit: @rickmanelius

Conjectures in the entry (Clark Kimberling, Jul 22 2013; the formula lines are unsigned):
a(n) = 2 + 9*n + 6*n^2 (conjectured). a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) (conjectured).
The comment adds: Conjecture: the four sequences are linearly recurrent. The four are A227719,
A227720, this sequence and its rounded companion; for this sequence that is the recurrence
above (the other two entries are separate problems).

Formalization notes:
* Offset 1. `a n` is defined for every natural number n, but the claims are made only for
  n ≥ 1 (the closed form) and for n ≥ 4 (the recurrence, so that a(n-3) has index at least 1;
  the natural-number subtractions n - 1, n - 2, n - 3 are then exact).
* s(n) is computed in the reals with `Real.log` of the real number (n+1)/n, exactly as in the
  name of the entry (for n ≥ 1 this is the same as log(1+1/n)). Floor is `Int.floor`, so
  `a n` is an integer.
* The entry also lists the g.f. (-17 + 7x - 2x^2)/(-1 + x)^3, marked conjectured. Its
  coefficients are 6m^2 + 21m + 17 = 2 + 9(m+1) + 6(m+1)^2 at x^m, so it says the same as the
  closed form, and it is not restated.
-/

namespace OMA.S_oeis_a227721

/-- s(n) = (2n+1)/(2n+2) - n*log((n+1)/n), in the reals. -/
noncomputable def s (n : ℕ) : ℝ :=
  (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) - (n : ℝ) * Real.log (((n : ℝ) + 1) / (n : ℝ))

/-- A227721: a(n) = Floor(1/s(n)). -/
noncomputable def a (n : ℕ) : ℤ := ⌊1 / s n⌋

/-- Kimberling's conjectures on A227721: the closed form a(n) = 2 + 9n + 6n^2 for n ≥ 1, and
the linear recurrence a(n) = 3a(n-1) - 3a(n-2) + a(n-3) for n ≥ 4. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = 2 + 9 * (n : ℤ) + 6 * (n : ℤ) ^ 2) ∧
    (∀ n : ℕ, 4 ≤ n → a n = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a227721
