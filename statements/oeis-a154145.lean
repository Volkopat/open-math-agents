import Mathlib

/-!
# OEIS A154145: the conjectured recurrence and g.f.s for the k with 15 + k(k+1)/2 a square

Source: https://oeis.org/A154145 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A154145 (R. J. Mathar, Oct 18 2009), offset 1: Indices k such that 15 plus the k-th
triangular number is a perfect square. Data: 1, 4, 6, 11, 20, 33, 43, 70, 121, 196, 254, 411, ...
Formula section: {k: 15+k*(k+1)/2 in A000290}. Conjectures:
a(n)= +a(n-1) +6*a(n-4) -6*a(n-5) -a(n-8) +a(n-9).
G.f.: x*(-1-3*x-2*x^2-5*x^3-3*x^4+5*x^5+2*x^6+3*x^7+2*x^8)/((x-1) * (x^4+2*x^2-1) *
(x^4-2*x^2-1)).
G.f.: ( 4 + (7+4*x+16*x^2+11*x^3)/(x^4-2*x^2-1) + 1/(x-1) + (-4-7*x-3*x^2-2*x^3)/(x^4+2*x^2-1) )/2.

Formalization notes:
* The k-th triangular number is k(k+1)/2 (A000217), and a perfect square is m^2 with m a natural
  number, as in the formula {k: 15+k*(k+1)/2 in A000290}; k ranges over the natural numbers
  (k = 0 does not qualify, since 15 is not a square).
* a(n) is the n-th such k in increasing order, Nat.nth P (n - 1) for n >= 1 (offset 1).
* The recurrence is stated for n > 9, where all nine earlier terms are defined, in the integers.
* Both generating functions are A(x) = Sum_{n >= 1} a(n) x^n in the formal power series ring over
  the rationals. The first identity A = N/D is stated as A * D = N with D as written, which is
  equivalent because D has constant term -1. The second is stated as written, with 1/q read as
  the power series inverse of q (x^4 - 2x^2 - 1, x - 1 and x^4 + 2x^2 - 1 have constant term -1)
  and the halving as C (1/2).
* Controls from the entry, proved in the proof file: a(1..12) = 1, 4, 6, 11, 20, 33, 43, 70, 121,
  196, 254, 411.
-/

namespace OMA.S_oeis_a154145

open PowerSeries

/-- 15 plus the k-th triangular number k(k+1)/2 is a perfect square. -/
def P (k : ℕ) : Prop := ∃ m : ℕ, 15 + k * (k + 1) / 2 = m ^ 2

/-- A154145(n), n >= 1: the n-th k (in increasing order) with 15 + k(k+1)/2 a perfect square. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

/-- The conjectured recurrence and both conjectured generating functions. -/
theorem main :
    (∀ n : ℕ, 9 < n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 4) - 6 * a (n - 5) - a (n - 8) + a (n - 9)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((X - 1) * (X ^ 4 + 2 * X ^ 2 - 1) * (X ^ 4 - 2 * X ^ 2 - 1)) =
        X * (-1 - 3 * X - 2 * X ^ 2 - 5 * X ^ 3 - 3 * X ^ 4 + 5 * X ^ 5 + 2 * X ^ 6 +
          3 * X ^ 7 + 2 * X ^ 8) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      C (1 / 2 : ℚ) * (4 + (7 + 4 * X + 16 * X ^ 2 + 11 * X ^ 3) * (X ^ 4 - 2 * X ^ 2 - 1)⁻¹ +
        (X - 1)⁻¹ + (-4 - 7 * X - 3 * X ^ 2 - 2 * X ^ 3) * (X ^ 4 + 2 * X ^ 2 - 1)⁻¹) := by
  sorry

end OMA.S_oeis_a154145
