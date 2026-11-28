import Mathlib

/-!
# A383700: a recurrence for the coefficient of x^2 in (x+1)(x+5)...(x+4n-3)

Source: https://oeis.org/A383700
Credit: @ivillar

Status: known result. The entry records: Conjecture verified using the differential equation
y + (124*x - 31)*y' + (240*x^2 - 120*x + 15)*y'' + (64*x^3 - 48*x^2 + 12*x - 1)*y''' = 0 satisfied by the
e.g.f. (Robert Israel, Mar 12 2026).

A383700 (offset 0): a(n) is the coefficient of x^2 in the expansion of
(x+1) * (x+5) * ... * (x+4*n-3); data 0, 0, 1, 15, 254, 5130, 122119, ...

Conjecture (R. J. Mathar, May 07 2025): the sequence is D-finite with recurrence
a(n) + 3*(-4*n+7)*a(n-1) + (48*n^2-216*n+247)*a(n-2) - (4*n-11)^3*a(n-3) = 0.

Formalization: the product has the n factors x + (4j + 1), j = 0, ..., n-1, as a polynomial over
ℤ (the empty product is 1). The recurrence is stated for every n ≥ 3, the range in which a(n-3)
is defined.
-/

namespace OMA.S_oeis_a383700

open Polynomial

/-- a(n): the coefficient of x^2 in (x+1)(x+5)...(x+4n-3). -/
noncomputable def a (n : ℕ) : ℤ :=
  (∏ j ∈ Finset.range n, (X + C (4 * (j : ℤ) + 1))).coeff 2

/-- The conjectured recurrence. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    a n + 3 * (-4 * (n : ℤ) + 7) * a (n - 1) + (48 * (n : ℤ) ^ 2 - 216 * n + 247) * a (n - 2) -
      (4 * (n : ℤ) - 11) ^ 3 * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a383700
