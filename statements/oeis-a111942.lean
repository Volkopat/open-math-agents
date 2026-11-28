import Mathlib

/-!
# A111942: Mathar's recurrence

Source: https://oeis.org/A111942
Credit: @ivillar

Status: open conjecture (R. J. Mathar, Nov 25 2015); the entry records it as a conjecture and notes no proof or
verification of it.

A111942 (offset 0): column 0 of the matrix logarithm (A111941) of triangle A111940, which shifts columns
left and up under matrix inverse; these terms are the result of multiplying the element in row n by n!;
data 0, 1, -1, 1, -2, 4, -12, 36, -144, 576, -2880, 14400, ...

Conjecture (R. J. Mathar, Nov 25 2015):
4*a(n) + 2*a(n-1) - (n-1)*(n-2)*a(n-2) = 0, n > 2.

Formalization: the entry gives the closed form
  a(n) = (-1)^(n-1) * floor((n-1)/2)! * floor(n/2)! for n > 0, with a(0) = 0,
and this formula is used as the definition here (`a` below). The recurrence is stated for n > 2, as in the
entry; it is checked by the data, for example at n = 3: (4)*(1) + (2)*(-1) + (-2)*(1) = 0, and at n = 4:
(4)*(-2) + (2)*(1) + (-6)*(-1) = 0.
-/

namespace OMA.S_oeis_a111942

/-- A111942 through the closed form of the entry:
a(n) = (-1)^(n-1) * floor((n-1)/2)! * floor(n/2)! for n > 0, and a(0) = 0. -/
def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else (-1) ^ (n - 1) * (((n - 1) / 2).factorial : ℤ) * ((n / 2).factorial : ℤ)

/-- Mathar's conjectured recurrence for A111942, for n > 2. -/
theorem main : ∀ n : ℕ, 2 < n →
    4 * a n + 2 * a (n - 1) - ((n : ℤ) - 1) * ((n : ℤ) - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a111942
