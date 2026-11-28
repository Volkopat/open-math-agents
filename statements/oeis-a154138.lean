import Mathlib

/-!
# OEIS A154138: the conjectured recurrence and g.f. for the k with 3 + k(k+1)/2 a square

Source: https://oeis.org/A154138 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A154138 (R. J. Mathar, Oct 18 2009), offset 1: Indices k such that 3 plus the k-th triangular
number is a perfect square. Data: 1, 3, 12, 22, 73, 131, 428, 766, 2497, 4467, ...
Formula section: {k: 3+k*(k+1)/2 in A000290}. Conjectures:
a(n) = +a(n-1) +6*a(n-2) -6*a(n-3) -a(n-4) +a(n-5);
G.f.: x*(1 + 2*x + 3*x^2 - 2*x^3 - 2*x^4)/((1-x)*(x^2-2*x-1)*(x^2+2*x-1)).
[Comment from Zak Seidov, Oct 21 2009: I believe both of these conjectures are
correct.]

Formalization notes:
* The k-th triangular number is k(k+1)/2 (A000217), and a perfect square is m^2 with m a natural
  number, as in the formula {k: 3+k*(k+1)/2 in A000290}; k ranges over the natural numbers
  (k = 0 does not qualify, since 3 is not a square).
* a(n) is the n-th such k in increasing order, Nat.nth P (n - 1) for n >= 1 (offset 1).
* The recurrence is stated for n > 5, where all five earlier terms are defined, in the integers.
* The generating function is A(x) = Sum_{n >= 1} a(n) x^n in the formal power series ring over the
  rationals. The identity A = N/D is stated as A * D = N with D as written, which is equivalent
  because D has constant term 1 or -1.
* Controls from the entry, proved in the proof file: a(1..10) = 1, 3, 12, 22, 73, 131, 428, 766, 2497, 4467.
-/

namespace OMA.S_oeis_a154138

open PowerSeries

/-- 3 plus the k-th triangular number k(k+1)/2 is a perfect square. -/
def P (k : ℕ) : Prop := ∃ m : ℕ, 3 + k * (k + 1) / 2 = m ^ 2

/-- A154138(n), n >= 1: the n-th k (in increasing order) with 3 + k(k+1)/2 a perfect square. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

/-- The conjectured recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1)) =
        X * (1 + 2 * X + 3 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4) := by
  sorry

end OMA.S_oeis_a154138
