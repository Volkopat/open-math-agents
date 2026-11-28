import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Denominator iteration conjecture on rational numbers

Source: https://math.stackexchange.com/questions/3754342/conjecture-about-rational-numbers
Posed by Barackouda. Credit: @etaubman.

Starting from positive integers a and b, append the n-th decimal digit of the current
quotient to the denominator at decimal place n, beginning with n = 1. The source
conjectures that the limiting quotient is irrational. The digit convention below uses
terminating decimal expansions, as in the source's example 3/4 = 0.75.

This states only the denominator-iteration conjecture. The source's numerator iteration
and its request for a general classification are separate questions.
-/

namespace OMA.S_mse_3754342

noncomputable def decimalDigit (x : ℝ) (n : ℕ) : ℤ :=
  ⌊x * (10 : ℝ) ^ n⌋ % 10

noncomputable def denominator (a b : ℕ) : ℕ → ℝ
  | 0 => b
  | n + 1 => denominator a b n +
      (decimalDigit ((a : ℝ) / denominator a b n) (n + 1) : ℝ) / (10 : ℝ) ^ (n + 1)

noncomputable def quotient (a b n : ℕ) : ℝ := (a : ℝ) / denominator a b n

def denominatorIrrationalityClaim : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b →
    ∃ L : ℝ, Filter.Tendsto (quotient a b) Filter.atTop (nhds L) ∧ Irrational L

/-- The denominator-iteration irrationality conjecture from the source. -/
theorem main : denominatorIrrationalityClaim := by
  sorry

end OMA.S_mse_3754342
