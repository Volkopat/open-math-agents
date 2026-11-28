import Mathlib

/-!
# A094287: Number of (s(0), s(1), ..., s(n)) such that 0 < s(i) < 7 and |s(i) - s(i-1)| <= 1 for i = 1,2,...,n, s(0) = 1, s(n) = 1.

Source: https://oeis.org/A094287
Credit: @agchua

R. J. Mathar (Dec 20 2011), in the formula section of A094287:
  Conjecture: a(n)= +6*a(n-1) -10*a(n-2) +9*a(n-4) -2*a(n-5) -a(n-6) with g.f.
  -x*(-1+4*x-2*x^2-5*x^3+2*x^4+x^5) / ( (x^3+3*x^2-4*x+1)*(x^3-x^2-2*x+1) ).
The sequence has offset 0 (a(0) = 1 was prepended in 2023). A sequence s(0), ..., s(n) is a
function s : Fin (n+1) → ℕ; the condition 0 < s(i) < 7 is s i ∈ {1, ..., 6}, and
|s(i) - s(i-1)| ≤ 1 is written as two inequalities between s at i.castSucc and i.succ.
The recurrence is stated for n ≥ 6, where all its indices are terms.
The g.f. was written when the data started at a(1) = 1: its series is x + 2x^2 + 4x^3 + ...,
the sum of a(n) x^n over n ≥ 1 (with a(0) = 1 included the identity fails only at the
constant term). It is stated as an identity of formal power series over ℚ for that series:
(sum of a(n) x^n, n ≥ 1) * ((x^3+3x^2-4x+1)(x^3-x^2-2x+1)) = -x(-1+4x-2x^2-5x^3+2x^4+x^5).
-/

namespace OMA.S_oeis_a094287

/-- A094287(n): the number of s : Fin (n+1) → ℕ with all values in 1..6, s 0 = 1, s n = 1 and
consecutive values differing by at most 1. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin (n + 1) => Finset.Icc 1 6).filter
    (fun s => s 0 = 1 ∧ s (Fin.last n) = 1 ∧
      ∀ i : Fin n, s i.succ ≤ s i.castSucc + 1 ∧ s i.castSucc ≤ s i.succ + 1)).card

/-- Mathar's conjecture: the recurrence (n ≥ 6) and the g.f. (for the terms with n ≥ 1). -/
theorem main : (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 10 * a (n - 2) + 9 * a (n - 4) -
      2 * a (n - 5) - a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 2 - 4 * PowerSeries.X + 1) *
          (PowerSeries.X ^ 3 - PowerSeries.X ^ 2 - 2 * PowerSeries.X + 1)) =
      -PowerSeries.X * (-1 + 4 * PowerSeries.X - 2 * PowerSeries.X ^ 2 -
        5 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 + PowerSeries.X ^ 5) := by
  sorry

end OMA.S_oeis_a094287
