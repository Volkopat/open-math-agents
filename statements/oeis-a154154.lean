import Mathlib

/-!
# OEIS A154154: the recurrence and the two g.f.s for the k with 30 + k(k+1)/2 a square

Source: https://oeis.org/A154154 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A154154 (R. J. Mathar, Oct 18 2009), offset 1: Numbers k such that 30 plus the k-th
triangular number is a perfect square. Data: 3, 13, 34, 84, 203, 493, 1186, 2876, 6915, 16765, ...
Formula section: {k: 30+k*(k+1)/2 in A000290}. Conjectures:
a(n) = +a(n-1) +6*a(n-2) -6*a(n-3) -a(n-4) +a(n-5).
G.f.: x*(-3-10*x-3*x^2+10*x^3+4*x^4)/((x-1) * (x^2-2*x-1) * (x^2+2*x-1)).
G.f.: ( 8 + (-5-2*x)/(x^2+2*x-1) + (12+29*x)/(x^2-2*x-1) + 1/(x-1) )/2.

Formalization notes:
* The k-th triangular number is k(k+1)/2 (A000217), and a perfect square is m^2 with m a natural
  number, as in the formula {k: 30+k*(k+1)/2 in A000290}; k ranges over the natural numbers.
* a(n) is the n-th such k in increasing order, Nat.nth P (n - 1) for n >= 1 (offset 1).
* The recurrence is stated for n > 5, where all five earlier terms are defined, in the integers.
* Both generating functions are A(x) = Sum_{n >= 1} a(n) x^n in the formal power series ring over
  the rationals. The first identity A = N/D is stated as A * D = N with D as written, which is
  equivalent because D has constant term -1. The second is stated as written, with 1/q read as
  the power series inverse of q (x^2 + 2x - 1, x^2 - 2x - 1 and x - 1 have constant term -1) and
  the halving as C (1/2).
* Controls from the entry, proved in the proof file: a(1..10) = 3, 13, 34, 84, 203, 493, 1186,
  2876, 6915, 16765.
-/

namespace OMA.S_oeis_a154154

open PowerSeries

/-- 30 plus the k-th triangular number k(k+1)/2 is a perfect square. -/
def P (k : ℕ) : Prop := ∃ m : ℕ, 30 + k * (k + 1) / 2 = m ^ 2

/-- A154154(n), n >= 1: the n-th k (in increasing order) with 30 + k(k+1)/2 a perfect square. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

/-- The conjectured recurrence and both conjectured generating functions. -/
theorem main :
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((X - 1) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
        X * (-3 - 10 * X - 3 * X ^ 2 + 10 * X ^ 3 + 4 * X ^ 4) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      C (1 / 2 : ℚ) * (8 + (-5 - 2 * X) * (X ^ 2 + 2 * X - 1)⁻¹ +
        (12 + 29 * X) * (X ^ 2 - 2 * X - 1)⁻¹ + (X - 1)⁻¹) := by
  sorry

end OMA.S_oeis_a154154
