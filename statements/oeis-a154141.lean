import Mathlib

/-!
# OEIS A154141: the recurrence and the two g.f.s for the k with 8 + k(k+1)/2 a square

Source: https://oeis.org/A154141 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A154141 (R. J. Mathar, Oct 18 2009), offset 1: Indices k such that 8 plus the k-th
triangular number is a perfect square. Data: 1, 7, 16, 46, 97, 271, 568, 1582, 3313, 9223, ...
Formula section: {k: 8+k*(k+1)/2 in A000290}. Conjectures:
a(n) = a(n-1) + 6*a(n-2) - 6*a(n-3) - a(n-4) + a(n-5).
G.f.: x*(1 +6*x +3*x^2 -6*x^3 -2*x^4)/((1-x) * (x^2-2*x-1) * (x^2+2*x-1)).
G.f.: ( 4 + 1/(x-1) - 3/(x^2+2*x-1) + (6+15*x)/(x^2-2*x-1) )/2.

Formalization notes:
* The k-th triangular number is k(k+1)/2 (A000217), and a perfect square is m^2 with m a natural
  number, as in the formula {k: 8+k*(k+1)/2 in A000290}; k ranges over the natural numbers (k = 0
  does not qualify, since 8 is not a square).
* a(n) is the n-th such k in increasing order, Nat.nth P (n - 1) for n >= 1 (offset 1).
* The recurrence is stated for n > 5, where all five earlier terms are defined, in the integers.
* Both generating functions are A(x) = Sum_{n >= 1} a(n) x^n in the formal power series ring over
  the rationals. The first identity A = N/D is stated as A * D = N, which is equivalent because D
  has constant term 1. The second is stated as written, with 1/q read as the power series inverse
  of q (x - 1, x^2 + 2x - 1 and x^2 - 2x - 1 have constant term -1) and the halving as C (1/2).
* Controls from the entry, proved in the proof file: a(1..10) = 1, 7, 16, 46, 97, 271, 568,
  1582, 3313, 9223.
-/

namespace OMA.S_oeis_a154141

open PowerSeries

/-- 8 plus the k-th triangular number k(k+1)/2 is a perfect square. -/
def P (k : ℕ) : Prop := ∃ m : ℕ, 8 + k * (k + 1) / 2 = m ^ 2

/-- A154141(n), n >= 1: the n-th k (in increasing order) with 8 + k(k+1)/2 a perfect square. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

/-- The conjectured recurrence and both conjectured generating functions. -/
theorem main :
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
        X * (1 + 6 * X + 3 * X ^ 2 - 6 * X ^ 3 - 2 * X ^ 4) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      C (1 / 2 : ℚ) * (4 + (X - 1)⁻¹ - 3 * (X ^ 2 + 2 * X - 1)⁻¹ +
        (6 + 15 * X) * (X ^ 2 - 2 * X - 1)⁻¹) := by
  sorry

end OMA.S_oeis_a154141
