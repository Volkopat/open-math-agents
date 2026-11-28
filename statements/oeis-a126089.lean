import Mathlib

/-!
# A126089: Mathar's first-order recurrence

Source: https://oeis.org/A126089
Credit: @ivillar

A126089 (offset 0): expansion of the e.g.f. (1-2*x)*sqrt(1-4*x);
data 1, -4, 4, 0, -48, -960, -20160, -483840, -13305600, ...

Conjecture (R. J. Mathar, Jan 24 2020): D-finite with recurrence
(-n+4)*a(n) + 2*(2*n-5)*(n-3)*a(n-1) = 0.

Formalization: the e.g.f. is the formal power series F over ℚ with constant term 1 and
F^2 = (1-2*x)^2*(1-4*x); these two conditions determine F, the constant term selecting the branch
of the square root. For such an F the sequence is a(n) = n! [x^n] F. The recurrence involves
a(n-1), so it is stated for n ≥ 1; it is checked by the data, for example at n = 5:
(-1)*(-960) + 2*5*2*(-48) = 0.
-/

namespace OMA.S_oeis_a126089

open PowerSeries

/-- The sequence with exponential generating function F: a(n) = n! [x^n] F. -/
noncomputable def a (F : ℚ⟦X⟧) (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n F

/-- Mathar's conjectured recurrence for the e.g.f. (1 - 2x) sqrt(1 - 4x). -/
theorem main : ∀ F : ℚ⟦X⟧, F ^ 2 = (1 - 2 * X) ^ 2 * (1 - 4 * X) → coeff 0 F = 1 →
    ∀ n : ℕ, 1 ≤ n →
      (4 - (n : ℚ)) * a F n + 2 * (2 * (n : ℚ) - 5) * ((n : ℚ) - 3) * a F (n - 1) = 0 := by
  sorry

end OMA.S_oeis_a126089
