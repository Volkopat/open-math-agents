import Mathlib

/-!
# A294139: Barker's closed forms and recurrence

Source: https://oeis.org/A294139
Credit: @ivillar

Wesley Ivan Hurt's sequence: the sum of the areas of the distinct rectangles (and the areas of
the squares on their sides) with positive integer sides such that L + W = n, W < L, i.e.
a(n) = Sum_{i=1..floor((n-1)/2)} (2*i^2 + 2*(n-i)^2 + i*(n-i)) (offset 1; data 0, 0, 12, 23, 70,
105, ...; the summand follows the Mathematica program of the entry). Colin Barker conjectured
(Nov 01 2017):
a(n) = n*(6*n - 1)*(n - 2) / 8 for n even, a(n) = n*(3*n - 1)*(n - 1) / 4 for n odd, and
a(n) = a(n-1) + 3*a(n-2) - 3*a(n-3) - 3*a(n-4) + 3*a(n-5) + a(n-6) - a(n-7) for n > 7.

Status: known result (Sela Fried, Aug 11 2024, in the entry: 'The first three conjectures of
Barker are true'; the recurrence follows from the closed forms).

Formalization notes:
* The closed forms are stated over ℚ for n ≥ 1, the recurrence over ℤ.
* Barker's generating function x^3*(12 + 11*x + 11*x^2 + 2*x^3) / ((1 - x)^4*(1 + x)^3) is the
  rational function determined by the recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a294139

/-- A294139: `a(n) = Sum_{i=1..floor((n-1)/2)} (2*i^2 + 2*(n-i)^2 + i*(n-i))`. -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 ((n - 1) / 2), (2 * i ^ 2 + 2 * (n - i) ^ 2 + i * (n - i))

/-- Barker's closed forms (even and odd n) and order-7 recurrence for A294139. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = (n : ℚ) * (6 * n - 1) * (n - 2) / 8) ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = (n : ℚ) * (3 * n - 1) * (n - 1) / 4) ∧
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = a (n - 1) + 3 * a (n - 2) - 3 * a (n - 3) - 3 * a (n - 4) + 3 * a (n - 5) +
        a (n - 6) - a (n - 7)) := by
  sorry

end OMA.S_oeis_a294139
