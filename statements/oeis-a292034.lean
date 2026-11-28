import Mathlib

/-!
# A292034: a linear recurrence for round(lambda(6) * alpha(6)^n), a Salem number of order 4

Source: https://oeis.org/A292034 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A292034, offset 1:
Linear divisibility sequence based on Salem number of order 4 (case t=6, see formula). Data
1, 6, 29, 144, 725, 3654, 18409, 92736, 467161, 2353350, 11855141, 59720976, ...

Formula section: a(n) = round(lambda(6)*alpha(6)^n)
where alpha(t) = (t+sqrt((t-4)*t+8)+sqrt(2)*sqrt(t*(t+sqrt((t-4)*t+8)-2)-4))/4
and lambda(t) = 1/sqrt((t-4)*t+8).
Conjectures from Colin Barker, Dec 17 2017:
G.f.: x*(1 - x)*(1 + x) / (1 - 6*x + 6*x^2 - 6*x^3 + x^4).
a(n) = 6*a(n-1) - 6*a(n-2) + 6*a(n-3) - a(n-4) for n>4.

Formalization notes.
* `alpha` and `lam` are the functions of the entry over the real numbers (`Real.sqrt`), and
  `a n = round (lam 6 * alpha 6 ^ n)` with `round : ℝ → ℤ`.
* The two conjectures are two forms of one claim: the generating function is the recurrence
  together with the terms a(1..4) = 1, 6, 29, 144 (x(1-x)(1+x) = x - x^3, and
  29 - 6*6 + 6*1 = -1, 144 - 6*29 + 6*6 - 6*1 = 0). `main` states these four terms and the
  recurrence for n > 4.
-/

namespace OMA.S_oeis_a292034

/-- alpha(t) = (t + sqrt((t-4)t+8) + sqrt(2) sqrt(t (t + sqrt((t-4)t+8) - 2) - 4)) / 4. -/
noncomputable def alpha (t : ℝ) : ℝ :=
  (t + √((t - 4) * t + 8) + √2 * √(t * (t + √((t - 4) * t + 8) - 2) - 4)) / 4

/-- lambda(t) = 1 / sqrt((t-4)t+8). -/
noncomputable def lam (t : ℝ) : ℝ := 1 / √((t - 4) * t + 8)

/-- A292034(n) = round(lambda(6) * alpha(6)^n), n ≥ 1. -/
noncomputable def a (n : ℕ) : ℤ := round (lam 6 * alpha 6 ^ n)

/-- Barker's conjectures: the recurrence a(n) = 6a(n-1) - 6a(n-2) + 6a(n-3) - a(n-4) for n > 4,
with the initial terms 1, 6, 29, 144 (this is the generating function
x(1-x)(1+x)/(1 - 6x + 6x^2 - 6x^3 + x^4)). -/
theorem main : a 1 = 1 ∧ a 2 = 6 ∧ a 3 = 29 ∧ a 4 = 144 ∧
    ∀ n : ℕ, 4 < n → a n = 6 * a (n - 1) - 6 * a (n - 2) + 6 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a292034
