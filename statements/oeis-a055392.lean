import Mathlib

/-!
# A055392: Mathar's recurrence

Source: https://oeis.org/A055392
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A055392 (offset 1): number of bracketings of 0#0#0#...#0 giving result 0, where 0#0 = 1, 0#1 = 1#0 = 1#1 = 0;
data 1, 0, 2, 1, 12, 14, 100, 180, 990, 2310, 10920, 30030, ...

Conjecture (R. J. Mathar, Nov 26 2012):
500*n*(n-1)*a(n) +100*(n-1)*(5*n -12)*a(n-1) +20*(25*n^2 -463*n +846)*a(n-2) +(-140161*n^2
+966559*n -1637508)*a(n-3) +2*(250*n^2 -26509*n +105084)*a(n-4) +98036*(4*n -19)*(4*n -21)*a(n-5)
= 0.

Formalization: The entry gives the g.f. (1/2)*(1 + sqrt(3 - 2*sqrt(1 - 4*x))), and this closed form is used as the
definition here. T is the formal power series over ℚ with T^2 = 1-4*x and constant term 1; W is the
formal power series with W^2 = 3 - 2*T and constant term 1, that is W = sqrt(3 - 2*sqrt(1-4x)) (the
constant terms select the branches of the square roots); and G is determined by G*2 = 1 + W (its
constant term 1, which is not a term of the sequence, is recorded as a hypothesis);
a(n) = [x^n] G. The sequence has offset 1 and the recurrence involves a(n-5), so it is stated for n ≥ 6,
where every index is at least the offset; it is checked by the data, for example at n = 6:
(15000)*(14) + (9000)*(12) + (-20640)*(1) + (-883950)*(2) + (-89940)*(0) + (1470540)*(1) = 0.
-/

namespace OMA.S_oeis_a055392

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A055392, for n ≥ 6. -/
theorem main : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    coeff 0 T = 1 →
    W ^ 2 = 3 - 2 * T →
    coeff 0 W = 1 →
    G * 2 = 1 + W →
    coeff 0 G = 1 →
    ∀ n : ℕ, 6 ≤ n →
      (-500 * (n : ℚ) + 500 * (n : ℚ) ^ 2) * coeff n G + (1200 - 1700 * (n : ℚ) + 500 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (16920 - 9260 * (n : ℚ) + 500 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-1637508 + 966559 * (n : ℚ) - 140161 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (210168 - 53018 * (n : ℚ) + 500 * (n : ℚ) ^ 2) * coeff (n - 4) G + (39116364 - 15685760 * (n : ℚ) + 1568576 * (n : ℚ) ^ 2) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a055392
