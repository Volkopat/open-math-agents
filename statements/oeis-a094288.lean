import Mathlib

/-!
# A094288: Number of (s(0), s(1), ..., s(n)) such that 0 < s(i) < 8 and |s(i) - s(i-1)| <= 1 for i = 1,2,...,n, s(0) = 1, s(n) = 1.

Source: https://oeis.org/A094288
Credit: @agchua

R. J. Mathar (Dec 20 2011), in the formula section of A094288:
  Conjecture: a(n)= +7*a(n-1) -15*a(n-2) +5*a(n-3) +15*a(n-4) -9*a(n-5) -3*a(n-6) +a(n-7) with g.f.
  -x*(1-5*x+5*x^2+6*x^3-7*x^4-2*x^5+x^6) / ( (x-1)*(x^2+2*x-1)*(x^4-4*x^3-2*x^2+4*x-1) ).
The sequence has offset 0 (a(0) = 1 was prepended in 2023). A sequence s(0), ..., s(n) is a
function s : Fin (n+1) → ℕ; the condition 0 < s(i) < 8 is s i ∈ {1, ..., 7}, and
|s(i) - s(i-1)| ≤ 1 is written as two inequalities between s at i.castSucc and i.succ.
The recurrence is stated for n ≥ 7, where all its indices are terms.
The g.f. was written when the data started at a(1) = 1: its series is x + 2x^2 + 4x^3 + ...,
the sum of a(n) x^n over n ≥ 1 (with a(0) = 1 included the series would differ only in its
constant term). It is stated as an identity of formal power series over ℚ for that series:
(sum of a(n) x^n, n ≥ 1) * ((x-1)(x^2+2x-1)(x^4-4x^3-2x^2+4x-1)) = -x(1-5x+5x^2+6x^3-7x^4-2x^5+x^6).
-/

namespace OMA.S_oeis_a094288

/-- A094288(n): the number of s : Fin (n+1) → ℕ with all values in 1..7, s 0 = 1, s n = 1 and
consecutive values differing by at most 1. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin (n + 1) => Finset.Icc 1 7).filter
    (fun s => s 0 = 1 ∧ s (Fin.last n) = 1 ∧
      ∀ i : Fin n, s i.succ ≤ s i.castSucc + 1 ∧ s i.castSucc ≤ s i.succ + 1)).card

/-- Mathar's conjecture: the recurrence (n ≥ 7) and the g.f. (for the terms with n ≥ 1). -/
theorem main : (∀ n : ℕ, 7 ≤ n → (a n : ℤ) = 7 * a (n - 1) - 15 * a (n - 2) + 5 * a (n - 3) +
      15 * a (n - 4) - 9 * a (n - 5) - 3 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 + 2 * PowerSeries.X - 1) *
          (PowerSeries.X ^ 4 - 4 * PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 2 +
            4 * PowerSeries.X - 1)) =
      -PowerSeries.X * (1 - 5 * PowerSeries.X + 5 * PowerSeries.X ^ 2 + 6 * PowerSeries.X ^ 3 -
        7 * PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6) := by
  sorry

end OMA.S_oeis_a094288
