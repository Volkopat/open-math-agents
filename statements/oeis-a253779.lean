import Mathlib

/-!
# A253779: Numbers c whose cubes are equal to the sum of m^3 consecutive cubes for m^3 not divisible by 3 (A118719).

Source: https://oeis.org/A253779
Credit: @agchua

Colin Barker (Jan 13 2015), in the formula section of A253779:
  Conjectures from Colin Barker, Jan 13 2015: (Start)
  a(n) = (81*n^5 - 270*n^4 + 396*n^3 - 312*n^2 + 96*n) / 64 for n even.
  a(n) = (81*n^5 - 135*n^4 + 126*n^3 - 66*n^2 - 15*n + 9) / 64 for n odd.
  G.f.: 6*x^2*(x^8+29*x^7+55*x^6+241*x^5+158*x^4+241*x^3+55*x^2+29*x+1) / ((x-1)^6*(x+1)^5).
  (End)
Definition: the entry gives a(n) = m(m^2-1)(m^2+2)/6 where m = A001651(n) (formula section;
the Maple program of the entry computes the terms in the same way), and A001651(n), the n-th
positive integer not divisible by 3, is floor((3n-1)/2). This is the definition below, computed
in ℚ (all values are integers). The offset is 1, so both closed forms are stated for n >= 1.
At n = 0 the definition gives A001651(0) = 0 and a(0) = 0, so PowerSeries.mk a is exactly the
g.f. Sum_{n>=1} a(n) x^n of the entry; the g.f. is stated as an identity of formal power series
over ℚ: (Sum a(n) X^n) * (X-1)^6 * (X+1)^5 = 6 X^2 (X^8 + 29 X^7 + ... + 29 X + 1).
-/

namespace OMA.S_oeis_a253779

/-- A001651(n), the n-th positive integer not divisible by 3: floor((3n-1)/2). -/
def A001651 (n : ℕ) : ℕ := (3 * n - 1) / 2

/-- A253779: a(n) = m(m^2-1)(m^2+2)/6 with m = A001651(n). -/
def a (n : ℕ) : ℚ :=
  (A001651 n : ℚ) * ((A001651 n : ℚ) ^ 2 - 1) * ((A001651 n : ℚ) ^ 2 + 2) / 6

/-- Barker's conjectures: the closed forms for even and for odd n >= 1, and the g.f.
6x^2(x^8+29x^7+55x^6+241x^5+158x^4+241x^3+55x^2+29x+1)/((x-1)^6(x+1)^5). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → Even n →
      a n = (81 * (n : ℚ) ^ 5 - 270 * (n : ℚ) ^ 4 + 396 * (n : ℚ) ^ 3 - 312 * (n : ℚ) ^ 2 +
        96 * (n : ℚ)) / 64) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n →
      a n = (81 * (n : ℚ) ^ 5 - 135 * (n : ℚ) ^ 4 + 126 * (n : ℚ) ^ 3 - 66 * (n : ℚ) ^ 2 -
        15 * (n : ℚ) + 9) / 64) ∧
    PowerSeries.mk a * ((PowerSeries.X - 1) ^ 6 * (PowerSeries.X + 1) ^ 5) =
      6 * PowerSeries.X ^ 2 * (PowerSeries.X ^ 8 + 29 * PowerSeries.X ^ 7 + 55 * PowerSeries.X ^ 6 +
        241 * PowerSeries.X ^ 5 + 158 * PowerSeries.X ^ 4 + 241 * PowerSeries.X ^ 3 +
        55 * PowerSeries.X ^ 2 + 29 * PowerSeries.X + 1) := by
  sorry

end OMA.S_oeis_a253779
