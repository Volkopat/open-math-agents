import Mathlib

/-!
# A003285: Linear recurrence for continued fraction convergents of sqrt(d)

Source: https://oeis.org/A003285
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Title: A003285: Period of continued fraction for square root of n (or 0 if n is a square).

Statement:
Apparently the generating function of the sequence for the denominators of continued fraction
convergents to sqrt(n) is always rational and of form p(x)/[1 - C*x^m + (-1)^m * x^(2m)],
or equivalently, the denominators satisfy the linear recurrence
b(k + 2m) = C*b(k + m) - (-1)^m * b(k), where m = a(n) is the period for each nonsquare n.
The same conjecture applies to the numerators of continued fraction convergents to sqrt(n).

Conventions:
- Simple continued fraction partial quotients and convergent numerators/denominators are
  defined recursively via the Gauss map on `ℝ`.
-/

namespace OMA.S_oeis_a003285

/-- One step of the simple continued fraction remainder map on `ℝ`. -/
noncomputable def cfStep (x : ℝ) : ℝ :=
  if x = ⌊x⌋ then 0 else 1 / (x - ⌊x⌋)

/-- The `k`-th partial quotient of the simple continued fraction of `x`. -/
noncomputable def cfCoeff (x : ℝ) (k : ℕ) : ℤ :=
  ⌊Nat.iterate cfStep k x⌋

/-- The minimal period `A003285(d)` of the simple continued fraction of `sqrt(d)`. -/
noncomputable def cfPeriod (d : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∀ k : ℕ, 1 ≤ k →
    cfCoeff (Real.sqrt d) (k + m) = cfCoeff (Real.sqrt d) k}

/-- Numerator of the `k`-th convergent of the simple continued fraction of `x`. -/
noncomputable def convNum (x : ℝ) : ℕ → ℤ
  | 0 => cfCoeff x 0
  | 1 => cfCoeff x 1 * cfCoeff x 0 + 1
  | k + 2 => cfCoeff x (k + 2) * convNum x (k + 1) + convNum x k

/-- Denominator of the `k`-th convergent of the simple continued fraction of `x`. -/
noncomputable def convDen (x : ℝ) : ℕ → ℤ
  | 0 => 1
  | 1 => cfCoeff x 1
  | k + 2 => cfCoeff x (k + 2) * convDen x (k + 1) + convDen x k

theorem main :
    ∀ d : ℕ, ¬ IsSquare d →
      ∃ C : ℤ,
        let m := cfPeriod d
        (∀ k : ℕ, convDen (Real.sqrt d) (k + 2 * m) =
          C * convDen (Real.sqrt d) (k + m) - (-1 : ℤ) ^ m * convDen (Real.sqrt d) k) ∧
        (∀ k : ℕ, convNum (Real.sqrt d) (k + 2 * m) =
          C * convNum (Real.sqrt d) (k + m) - (-1 : ℤ) ^ m * convNum (Real.sqrt d) k) := by
  sorry

end OMA.S_oeis_a003285
