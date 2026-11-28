import Mathlib

/-!
# OEIS A154140: the conjectured recurrence and g.f. for the k with 6 + k(k+1)/2 a square

Source: https://oeis.org/A154140 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A154140 (R. J. Mathar, Oct 18 2009), offset 1: Indices k such that 6 plus the k-th triangular
number is a perfect square. Data: 2, 4, 19, 29, 114, 172, 667, 1005, 3890, 5860, ...
Formula section: {k: 6+k*(k+1)/2 in A000290}. Conjectures:
a(n) = +a(n-1) +6*a(n-2) -6*a(n-3) -a(n-4) +a(n-5).
G.f.: x*(2 +2*x +3*x^2 -2*x^3 -3*x^4)/((1-x)* (x^2-2*x-1)* (x^2+2*x-1))
G.f.: ( 6 + (-1 -4*x)/(x^2+2*x-1) + (6 +13*x)/(x^2-2*x-1) + 1/(x-1) )/2.

Formalization notes:
* The k-th triangular number is k(k+1)/2 (A000217), and a perfect square is m^2 with m a natural
  number, as in the formula {k: 6+k*(k+1)/2 in A000290}; k ranges over the natural numbers
  (k = 0 does not qualify, since 6 is not a square).
* a(n) is the n-th such k in increasing order, Nat.nth P (n - 1) for n >= 1 (offset 1).
* The recurrence is stated for n > 5, where all five earlier terms are defined, in the integers.
* Both generating functions are A(x) = Sum_{n >= 1} a(n) x^n in the formal power series ring over the
  rationals. The identity A = N/D is stated as A * D = N with D as written, which is equivalent
  because D has constant term 1 or -1. The partial fraction form is stated as written, with 1/q read as the power series inverse of q (each q has constant term -1) and the halving as C (1/2).
* Controls from the entry, proved in the proof file: a(1..10) = 2, 4, 19, 29, 114, 172, 667, 1005, 3890, 5860.
-/

namespace OMA.S_oeis_a154140

open PowerSeries

/-- 6 plus the k-th triangular number k(k+1)/2 is a perfect square. -/
def P (k : ℕ) : Prop := ∃ m : ℕ, 6 + k * (k + 1) / 2 = m ^ 2

/-- A154140(n), n >= 1: the n-th k (in increasing order) with 6 + k(k+1)/2 a perfect square. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

/-- The conjectured recurrence and generating functions. -/
theorem main :
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
        X * (2 + 2 * X + 3 * X ^ 2 - 2 * X ^ 3 - 3 * X ^ 4) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      C (1 / 2 : ℚ) * (6 + (-1 - 4 * X) * (X ^ 2 + 2 * X - 1)⁻¹ + (6 + 13 * X) * (X ^ 2 - 2 * X - 1)⁻¹ + (X - 1)⁻¹) := by
  sorry

end OMA.S_oeis_a154140
