import Mathlib

/-!
# OEIS A154151: the conjectured recurrence and g.f. for the k with 25 + k(k+1)/2 a square

Source: https://oeis.org/A154151 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A154151 (R. J. Mathar, Oct 18 2009), offset 1: Numbers k such that 25 plus the k-th triangular
number is a perfect square. Data: 0, 18, 21, 111, 128, 650, 749, 3791, 4368, 22098, ...
Formula section: {k: 25+k*(k+1)/2 in A000290}. Conjectures:
a(n)= +a(n-1) +6*a(n-2) -6*a(n-3) -a(n-4) +a(n-5).
G.f.: x^2*(-18-3*x+18*x^2+x^3)/( (x-1) * (x^2+2*x-1) * (x^2-2*x-1)).
G.f.: ( 2 + 1/(x-1) + (10+29*x)/(x^2-2*x-1) + (-9+8*x)/(x^2+2*x-1) )/2.

Formalization notes:
* The k-th triangular number is k(k+1)/2 (A000217), and a perfect square is m^2 with m a natural
  number, as in the formula {k: 25+k*(k+1)/2 in A000290}; k ranges over the natural numbers
  (k = 0 qualifies, since 25 is a square, and is a(1)).
* a(n) is the n-th such k in increasing order, Nat.nth P (n - 1) for n >= 1 (offset 1).
* The recurrence is stated for n > 5, where all five earlier terms are defined, in the integers.
* Both generating functions are A(x) = Sum_{n >= 1} a(n) x^n in the formal power series ring over the
  rationals. The identity A = N/D is stated as A * D = N with D as written, which is equivalent
  because D has constant term 1 or -1. The partial fraction form is stated as written, with 1/q read as the power series inverse of q (each q has constant term -1) and the halving as C (1/2).
* Controls from the entry, proved in the proof file: a(1..10) = 0, 18, 21, 111, 128, 650, 749, 3791, 4368, 22098.
-/

namespace OMA.S_oeis_a154151

open PowerSeries

/-- 25 plus the k-th triangular number k(k+1)/2 is a perfect square. -/
def P (k : ℕ) : Prop := ∃ m : ℕ, 25 + k * (k + 1) / 2 = m ^ 2

/-- A154151(n), n >= 1: the n-th k (in increasing order) with 25 + k(k+1)/2 a perfect square. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

/-- The conjectured recurrence and generating functions. -/
theorem main :
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((X - 1) * (X ^ 2 + 2 * X - 1) * (X ^ 2 - 2 * X - 1)) =
        X ^ 2 * (-18 - 3 * X + 18 * X ^ 2 + X ^ 3) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      C (1 / 2 : ℚ) * (2 + (X - 1)⁻¹ + (10 + 29 * X) * (X ^ 2 - 2 * X - 1)⁻¹ + (-9 + 8 * X) * (X ^ 2 + 2 * X - 1)⁻¹) := by
  sorry

end OMA.S_oeis_a154151
