import Mathlib

/-!
# A253778: Numbers b that are the first of m^3 consecutive cubes whose sum is a cube c^3, where m^3 is not divisible by 3 (A118719).

Source: https://oeis.org/A253778
Credit: @agchua

Colin Barker (Jan 13 2015), in the formula section of A253778:
  Conjectures from Colin Barker, Jan 13 2015: (Start)
  a(n) = (54*n^4 - 252*n^3 + 312*n^2 - 144*n + 64) / 64 for n even.
  a(n) = (54*n^4 - 180*n^3 + 96*n^2 - 12*n + 42) / 64 for n odd.
  G.f.: -x^2*(x^7+5*x^6+60*x^5+69*x^4+147*x^3+36*x^2+8*x-2) / ((x-1)^5*(x+1)^4).
  (End)
Definition: the entry gives a(n) = (m-1)(m^2 (m-2)-4(m+1))/6 where m = A001651(n) (formula
section; the Maple program of the entry computes the terms in the same way), and A001651(n), the
n-th positive integer not divisible by 3, is floor((3n-1)/2). This is the definition below,
computed in ℚ (all values for n >= 1 are integers; it gives the listed terms 0, -2, 6, 34, 213,
...). The offset is 1, so both closed forms are stated for n >= 1, and the g.f. is the series
Sum_{n >= 1} a(n) x^n = x * Sum_{n >= 0} a(n+1) x^n, stated as an identity of formal power series
over ℚ after multiplying by the denominator (x-1)^5 (x+1)^4. (The value of the formula at n = 0
plays no role.)
-/

namespace OMA.S_oeis_a253778

/-- A001651(n), the n-th positive integer not divisible by 3: floor((3n-1)/2). -/
def A001651 (n : ℕ) : ℕ := (3 * n - 1) / 2

/-- A253778: a(n) = (m-1)(m^2 (m-2) - 4(m+1))/6 with m = A001651(n). -/
def a (n : ℕ) : ℚ :=
  ((A001651 n : ℚ) - 1) * ((A001651 n : ℚ) ^ 2 * ((A001651 n : ℚ) - 2) -
    4 * ((A001651 n : ℚ) + 1)) / 6

/-- Barker's conjectures: the closed forms for even and for odd n >= 1, and the g.f.
-x^2(x^7+5x^6+60x^5+69x^4+147x^3+36x^2+8x-2)/((x-1)^5(x+1)^4). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → Even n →
      a n = (54 * (n : ℚ) ^ 4 - 252 * (n : ℚ) ^ 3 + 312 * (n : ℚ) ^ 2 - 144 * (n : ℚ) +
        64) / 64) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n →
      a n = (54 * (n : ℚ) ^ 4 - 180 * (n : ℚ) ^ 3 + 96 * (n : ℚ) ^ 2 - 12 * (n : ℚ) +
        42) / 64) ∧
    PowerSeries.X * PowerSeries.mk (fun n => a (n + 1)) *
        ((PowerSeries.X - 1) ^ 5 * (PowerSeries.X + 1) ^ 4) =
      -PowerSeries.X ^ 2 * (PowerSeries.X ^ 7 + 5 * PowerSeries.X ^ 6 + 60 * PowerSeries.X ^ 5 +
        69 * PowerSeries.X ^ 4 + 147 * PowerSeries.X ^ 3 + 36 * PowerSeries.X ^ 2 +
        8 * PowerSeries.X - 2) := by
  sorry

end OMA.S_oeis_a253778
