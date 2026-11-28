import Mathlib

/-!
# A119651: Number of different values of exactly n standard American coins (pennies, nickels, dimes and quarters).

Source: https://oeis.org/A119651
Credit: @agchua

Colin Barker (Oct 24 2019), in the formula section of A119651:
  Conjectures from Colin Barker, Oct 24 2019: (Start)
  G.f.: x*(4 + 2*x + 4*x^2 + 4*x^3 + 4*x^4 + 3*x^5 + 2*x^6 + x^7) / (1 - x)^2.
  a(n) = 2*a(n-1) - a(n-2) for n>2.
  a(n) = 24*(n-3) for n>6.
  (End)
The sequence has offset 1 (a(1) = 4: one coin of each kind). A collection of exactly n coins is
given by the numbers p, k, d, q of pennies, nickels, dimes and quarters with p + k + d + q = n;
its value is p + 5k + 10d + 25q cents, and a(n) is the number of distinct values.
The g.f. is stated as an identity of formal power series over ℚ for the series of the terms,
the sum of a(n) x^n over n ≥ 1 (the constant coefficient is 0, as the offset is 1):
(sum of a(n) x^n) * (1 - x)^2 = x*(4 + 2x + 4x^2 + 4x^3 + 4x^4 + 3x^5 + 2x^6 + x^7).
Range of the recurrence: as written (n > 2) it fails for 3 ≤ n ≤ 8, for example a(3) = 20 while
2a(2) - a(1) = 2*10 - 4 = 16 (the listed terms are 4, 10, 20, 34, 52, 73, 96, 120, 144, ...).
The g.f. in the same line implies the recurrence exactly for n > 8, since its numerator has degree 8;
that is the range in which it is stated below. The closed form is stated for n > 6, as written.
-/

namespace OMA.S_oeis_a119651

/-- The values in cents of all collections of exactly n coins: p pennies, k nickels, d dimes and
q quarters, t = (p, k, d, q), with p + k + d + q = n. -/
def coinValues (n : ℕ) : Finset ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun t : ℕ × ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2.1 + t.2.2.2 = n)).image
    (fun t : ℕ × ℕ × ℕ × ℕ => t.1 + 5 * t.2.1 + 10 * t.2.2.1 + 25 * t.2.2.2)

/-- A119651(n): the number of different values of exactly n coins. -/
def a (n : ℕ) : ℕ := (coinValues n).card

/-- Barker's conjectures: the g.f., the recurrence (for n > 8, see above) and the closed form
a(n) = 24(n-3) for n > 6. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - PowerSeries.X) ^ 2 =
      PowerSeries.X * (4 + 2 * PowerSeries.X + 4 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 +
        4 * PowerSeries.X ^ 4 + 3 * PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 6 + PowerSeries.X ^ 7) ∧
    (∀ n : ℕ, 9 ≤ n → (a n : ℤ) = 2 * (a (n - 1) : ℤ) - (a (n - 2) : ℤ)) ∧
    (∀ n : ℕ, 7 ≤ n → a n = 24 * (n - 3)) := by
  sorry

end OMA.S_oeis_a119651
