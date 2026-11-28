import Mathlib

/-!
# A133044: Area of the spiral of equilateral triangles with side lengths which follow the Padovan sequence, divided by the area of the initial triangle.

Source: https://oeis.org/A133044
Credit: @rtflynn

The conjectures listed in the entry (Colin Barker, Sep 18 2013), stated below as one conjunction:
* a(n) = a(n-1) + a(n-2) + a(n-3) - a(n-4) + a(n-5) - a(n-6).
* G.f.: x*(x^3+x+1) / ((x^3-x^2+2*x-1)*(x^3-x-1)).

Conventions:
* The triangles of the spiral have side lengths 1, 1, 1, 2, 2, 3, 4, 5, 7, 9, ... (the Padovan
  sequence `p 0 = p 1 = p 2 = 1`, `p (k + 3) = p k + p (k + 1)`), and the n-th term is the area of
  the first n triangles. The area of an equilateral triangle is proportional to the square of its
  side, so the area divided by the area of the initial (side 1) triangle is
  `a n = p 0 ^ 2 + ... + p (n - 1) ^ 2`.
  This gives the data 1, 2, 3, 7, 11, 20, 36, 61, 110, 191, ... (offset 1).
* `a 0 = 0` (empty sum), so the power series with coefficients `a n` is the g.f. of the entry,
  whose expansion starts at x^1.
* The recurrence involves a(n-6) and the offset is 1, so it is stated for n ≥ 7.
-/

namespace OMA.S_oeis_a133044

/-- The side lengths of the triangles: the Padovan sequence 1, 1, 1, 2, 2, 3, 4, 5, 7, 9, ... -/
def p : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | k + 3 => p k + p (k + 1)

/-- A133044(n): the area of the first n triangles of the spiral, in units of the first one. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range n, p k ^ 2

open PowerSeries in
/-- Barker's conjectured recurrence and generating function for A133044. -/
theorem main :
    (∀ n : ℕ, 7 ≤ n → a n = a (n - 1) + a (n - 2) + a (n - 3) - a (n - 4) + a (n - 5) - a (n - 6)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X ^ 3 - X ^ 2 + 2 * X - 1) * (X ^ 3 - X - 1) : ℚ⟦X⟧) =
      X * (X ^ 3 + X + 1) := by
  sorry

end OMA.S_oeis_a133044
