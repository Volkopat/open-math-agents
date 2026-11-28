import Mathlib

/-!
# A000483: Mathar's recurrence

Source: https://oeis.org/A000483
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A000483 (offset 6): associated Stirling numbers: second-order reciprocal Stirling numbers (Fekete)
a(n) = [[n, 3]]. The number of 3-orbit permutations of an n-set with at least 2 elements in each orbit;
data 15, 210, 2380, 26432, 303660, 3678840, 47324376, 647536032, 9418945536, ...

Conjecture (R. J. Mathar, Jul 18 2015):
(n-2)*(n-4)*a(n) -(n-1)*(3*n^2-21*n+35)*a(n-1) +(n-1)*(n-2)*(3*n^2-24*n+47)*a(n-2)
-(n-5)*(n-1)*(n-2)*(n-3)*(n-4)*a(n-3) = 0.
(This is the first of the two recurrences conjectured in the entry on that date.)

Formalization: the entry gives the e.g.f. -((x+log(1-x))^3)/6 (Vladeta Jovovic, May 03 2008), and this
is used as the definition here. L is the formal power series over ℚ with zero constant term and
(1-x)*L' = -1, that is L = log(1-x) = -x - x^2/2 - x^3/3 - ... (these two conditions determine L); the
e.g.f. F is determined by 6*F = -(x + L)^3; and a(n) = n! [x^n] F, which is 0 for n < 6 and gives
a(6) = 15. The sequence has offset 6 and the recurrence involves a(n-3), so every index is at least
the offset for n ≥ 9. `main` is stated for n ≥ 7, with a(4) = a(5) = 0 as given by the e.g.f.; this
includes every n ≥ 9. It is checked by the data, for example at n = 9:
(7)*(5)*(26432) - (8)*(89)*(2380) + (8)*(7)*(74)*(210) - (4)*(8)*(7)*(6)*(5)*(15) = 0.
-/

namespace OMA.S_oeis_a000483

open PowerSeries

/-- The sequence with exponential generating function F: a(n) = n! [x^n] F. -/
noncomputable def a (F : ℚ⟦X⟧) (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n F

/-- Mathar's conjectured recurrence for A000483 (a(n) = n! [x^n] F), for n ≥ 7. -/
theorem main : ∀ L F : ℚ⟦X⟧, coeff 0 L = 0 →
    (1 - X) * derivative ℚ L = -1 →
    6 * F = -(X + L) ^ 3 →
    ∀ n : ℕ, 7 ≤ n →
      ((n : ℚ) - 2) * ((n : ℚ) - 4) * a F n -
        ((n : ℚ) - 1) * (3 * (n : ℚ) ^ 2 - 21 * (n : ℚ) + 35) * a F (n - 1) +
        ((n : ℚ) - 1) * ((n : ℚ) - 2) * (3 * (n : ℚ) ^ 2 - 24 * (n : ℚ) + 47) * a F (n - 2) -
        ((n : ℚ) - 5) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * ((n : ℚ) - 4) * a F (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a000483
