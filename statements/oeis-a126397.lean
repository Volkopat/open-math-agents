import Mathlib

/-!
# A126397: Number of base 10 n-digit numbers with adjacent digits differing by two or less.

Source: https://oeis.org/A126397
Credit: @agchua

Colin Barker (May 31 2017), in the formula section of A126397:
  Conjectures from Colin Barker, May 31 2017: (Start)
  G.f.: (1 + 3*x - 15*x^2 + 2*x^3 + x^4) / (1 - 7*x + 11*x^2 - x^4).
  a(n) = 7*a(n-1) - 11*a(n-2) + a(n-4) for n>4.
  (End)
This file states both: the recurrence for n > 4 as written (offset 0), and the g.f. as an identity
of formal power series over ℚ, (∑ a(n) X^n) * (1 - 7X + 11X^2 - X^4) = 1 + 3X - 15X^2 + 2X^3 + X^4.
Definition: a(n) counts the strings s(0), ..., s(n-1) of digits in {0, ..., 9} in which adjacent
digits differ by at most 2, with leading zeros allowed. This is what the entry's program counts
(R. H. Hardin's state variables range over 0..M-1 with no other condition, M = 10), and it matches
the data: a(1) = 10 counts the ten digits and a(2) = 44 counts all such ordered digit pairs; a(0) = 1
counts the empty string. A string is a function s : Fin n → ℕ with values in Finset.range 10, and
|s(i) - s(i+1)| ≤ 2 is written as two inequalities between s i and s j for j = i + 1.
-/

namespace OMA.S_oeis_a126397

/-- A126397(n): the number of digit strings of length n over {0, ..., 9} (leading zeros allowed)
whose adjacent digits differ by at most 2. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin n => Finset.range 10).filter
    (fun s => ∀ i j : Fin n, j.val = i.val + 1 → s j ≤ s i + 2 ∧ s i ≤ s j + 2)).card

/-- Barker's conjectures: a(n) = 7a(n-1) - 11a(n-2) + a(n-4) for n > 4, and the g.f.
(1 + 3x - 15x^2 + 2x^3 + x^4)/(1 - 7x + 11x^2 - x^4). -/
theorem main : (∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * a (n - 1) - 11 * a (n - 2) + a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) *
        (1 - 7 * PowerSeries.X + 11 * PowerSeries.X ^ 2 - PowerSeries.X ^ 4) =
      1 + 3 * PowerSeries.X - 15 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 +
        PowerSeries.X ^ 4 := by
  sorry

end OMA.S_oeis_a126397
