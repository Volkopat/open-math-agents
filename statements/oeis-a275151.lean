import Mathlib

/-!
# OEIS A275151: Barker's closed form, recurrence and g.f. for a(n) = 3a(n-1) + 2 sqrt(2a(n-1)(a(n-1)-7)) - 7

Source: https://oeis.org/A275151 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Manuel López Holgueras, Jul 17 2016), offset 1: a(1) = 8; a(n) = 3*a(n-1) +
2*sqrt(2*a(n-1)*(a(n-1)-7)) - 7 for n > 1. Data: 8, 25, 128, 729, 4232, 24649, ... Formula:
Conjectures from Colin Barker, Jul 19 2016: a(n) = (14 + (11-6*sqrt(2))*(3+2*sqrt(2))^n +
(3-2*sqrt(2))^n*(11+6*sqrt(2)))/4. a(n) = 7*a(n-1) - 7*a(n-2) + a(n-3) for n > 3.
G.f.: x*(8 - 31*x + 9*x^2) / ((1-x)*(1 - 6*x + x^2)).

Formalization notes:
* The sequence is defined in the reals exactly as in the name, with `Real.sqrt` for the square
  root. The entry starts at n = 1; the value of `a 0` is a placeholder that no conjecture uses.
* The closed form is stated for every n >= 1 and the recurrence for every n > 3, as in the entry.
* The g.f. is Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x)*D(x) = N(x) in R[[x]], which is
  equivalent to A = N/D because D has constant term 1.
* `main` is the conjunction of Barker's three conjectures.
* Controls proved in the proof file: a(n) = b(n) for every n >= 1, where b is the integer
  sequence b(0) = 9, b(1) = 8, b(n) = 6 b(n-1) - b(n-2) - 14, and b(1..16) = 8, 25, 128, 729,
  4232, 24649, 143648, 837225, 4879688, 28440889, 165765632, 966152889, 5631151688, 32820757225,
  191293391648, 1114939592649, the entry's data.
-/

namespace OMA.S_oeis_a275151

open PowerSeries

/-- A275151, offset 1: a(1) = 8 and a(n) = 3 a(n-1) + 2 sqrt(2 a(n-1) (a(n-1) - 7)) - 7 for
n > 1. The value at 0 is not part of the sequence. -/
noncomputable def a : ℕ → ℝ
  | 0 => 0
  | 1 => 8
  | n + 2 => 3 * a (n + 1) + 2 * Real.sqrt (2 * a (n + 1) * (a (n + 1) - 7)) - 7

/-- Barker's conjectures: the closed form, the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = (14 + (11 - 6 * Real.sqrt 2) * (3 + 2 * Real.sqrt 2) ^ n +
      (3 - 2 * Real.sqrt 2) ^ n * (11 + 6 * Real.sqrt 2)) / 4) ∧
    (∀ n : ℕ, 3 < n → a n = 7 * a (n - 1) - 7 * a (n - 2) + a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℝ) else a n) * ((1 - X) * (1 - 6 * X + X ^ 2)) =
      X * (8 - 31 * X + 9 * X ^ 2) := by
  sorry

end OMA.S_oeis_a275151
