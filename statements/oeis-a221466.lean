import Mathlib

/-!
# A221466: Number of 0..n arrays of length 7 with each element unequal to at least one neighbor, starting with 0.

Source: https://oeis.org/A221466
Credit: @agchua

Colin Barker (Aug 05 2018), in the formula section of A221466:
  Conjectures from Colin Barker, Aug 05 2018: (Start)
  G.f.: 8*x*(1 + 23*x + 54*x^2 + 14*x^3 - 2*x^4) / (1 - x)^7.
  a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
  (End)
This file states both parts: the recurrence for n > 7 (offset 1, so all indices are terms), and the
g.f. as an identity of formal power series over Q,
(sum of a(n) X^n) * (1 - X)^7 = 8X(1 + 23X + 54X^2 + 14X^3 - 2X^4); its coefficient of X^0 is a(0),
which the definition below makes 0 (for n = 0 the only array is 0,0,0,0,0,0,0, whose first entry
equals its only neighbor), in accordance with the factor x of the g.f. (offset 1).
Definition: an array is (x0, x1, ..., x6) with entries in 0..n and x0 = 0 (starting with 0). The
neighbors of x(i) are x(i-1) and x(i+1) where these exist, so x0 and x6 have one neighbor each and
x1, ..., x5 have two. The condition is that each entry is unequal to at least one of its
neighbors: x0 ≠ x1, x5 ≠ x6, and x(i-1) ≠ x(i) or x(i) ≠ x(i+1) for i = 1..5. These are the seven
clauses of ok below. The definition gives the listed terms 8, 240, 1944, 8960, 30000, 81648,
192080 for n = 1..7 (checked by direct enumeration).
-/

namespace OMA.S_oeis_a221466

/-- Each entry of the array (x0, x1, x2, x3, x4, x5, x6) is unequal to at least one neighbor. -/
abbrev ok (x0 x1 x2 x3 x4 x5 x6 : ℕ) : Prop :=
  x0 ≠ x1 ∧ (x0 ≠ x1 ∨ x1 ≠ x2) ∧ (x1 ≠ x2 ∨ x2 ≠ x3) ∧ (x2 ≠ x3 ∨ x3 ≠ x4) ∧
    (x3 ≠ x4 ∨ x4 ≠ x5) ∧ (x4 ≠ x5 ∨ x5 ≠ x6) ∧ x5 ≠ x6

/-- A221466: the number of arrays (0, x1, x2, x3, x4, x5, x6) with entries in 0..n satisfying
ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
      ok 0 t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2)).card

/-- Barker's conjectures: the recurrence of order 7 for n > 7, and the g.f.
8x(1 + 23x + 54x^2 + 14x^3 - 2x^4)/(1 - x)^7. -/
theorem main : (∀ n : ℕ, 8 ≤ n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) +
        21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 7 =
      8 * PowerSeries.X * (1 + 23 * PowerSeries.X + 54 * PowerSeries.X ^ 2 +
        14 * PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 4) := by
  sorry

end OMA.S_oeis_a221466
