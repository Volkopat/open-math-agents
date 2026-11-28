import Mathlib

/-!
# A085579: a(n) is the n-th digit after the decimal point of the positive real root of x^2+n*x-2.

Source: https://oeis.org/A085579
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: this diagonal expressed as a decimal is irrational and transcendental.
-/

namespace OMA.S_oeis_a085579

noncomputable def posRoot (n : ℕ) : ℝ :=
  (-(n : ℝ) + Real.sqrt ((n : ℝ) ^ 2 + 8)) / 2

noncomputable def a (n : ℕ) : ℕ :=
  Int.toNat (⌊posRoot n * (10 : ℝ) ^ n⌋ % 10)

noncomputable def diagonalReal : ℝ :=
  ∑' n : ℕ, (a (n + 1) : ℝ) / (10 : ℝ) ^ (n + 1)

theorem main : Irrational diagonalReal ∧ Transcendental ℚ diagonalReal := by
  sorry

end OMA.S_oeis_a085579
