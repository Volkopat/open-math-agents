import Mathlib

/-!
# A292035: Linear divisibility sequence based on Salem number of order 4 (case t=7, see formula).

Source: https://oeis.org/A292035

Definition (FORMULA section of the entry, the name refers to it):
  a(n) = round(lambda(7)*alpha(7)^n)
  where alpha(t) = (t+sqrt((t-4)*t+8)+sqrt(2)*sqrt(t*(t+sqrt((t-4)*t+8)-2)-4))/4
  and lambda(t) = 1/sqrt((t-4)*t+8).

Conjecture (Colin Barker, Dec 17 2017), quoted:
  a(n) = 7*a(n-1) - 7*a(n-2) + 7*a(n-3) - a(n-4) for n>4.
(The accompanying conjectured g.f. x*(1 - x)*(1 + x) / (1 - 7*x + 7*x^2 - 7*x^3 + x^4) is an
equivalent form of the same recurrence together with the initial terms; only the recurrence
is stated here.)

Translation notes.
* Offset 1. `alpha`, `lam` (for lambda) and `a` are transcribed literally from the entry,
  over the reals, with `Real.sqrt` and Mathlib's `round : ℝ → ℤ` (round half up; the value
  is never a half-integer, so the rounding convention does not matter).
* `a` is defined for every natural n by the same formula (a 0 = 0), but the statement only
  uses indices n - 4 >= 1, exactly the range n > 4 of the conjecture.
* The subtractions n - 1, ..., n - 4 are natural-number subtractions; they are harmless
  because of the hypothesis 4 < n. The values live in ℤ.
-/

namespace OMA.S_oeis_a292035

/-- alpha(t) of the OEIS entry. -/
noncomputable def alpha (t : ℝ) : ℝ :=
  (t + Real.sqrt ((t - 4) * t + 8)
    + Real.sqrt 2 * Real.sqrt (t * (t + Real.sqrt ((t - 4) * t + 8) - 2) - 4)) / 4

/-- lambda(t) of the OEIS entry. -/
noncomputable def lam (t : ℝ) : ℝ := 1 / Real.sqrt ((t - 4) * t + 8)

/-- a(n) = round(lambda(7)*alpha(7)^n). -/
noncomputable def a (n : ℕ) : ℤ := round (lam 7 * alpha 7 ^ n)

theorem main : ∀ n : ℕ, 4 < n →
    a n = 7 * a (n - 1) - 7 * a (n - 2) + 7 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a292035
