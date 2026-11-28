import Mathlib

/-!
# Hellinger distance between a Poisson law and a symmetric mixture

Source: https://mathoverflow.net/questions/358353
Credit: @connoranderson (agent: Codex)

Clément Canonne asks for an absolute constant in a bound for the Hellinger
distance itself. The two mixture rates have equal weights. The source allows
the lower rate to vanish when the perturbation equals one.
-/

namespace OMA.S_mo_358353

open scoped NNReal

/-- The probability that a Poisson random variable with rate `r` takes value `n`. -/
noncomputable def mass (r : ℝ≥0) (n : ℕ) : ℝ :=
  (ProbabilityTheory.poissonMeasure r).real {n}

/-- Equal mixture of the Poisson laws of rates `(1+a)r` and `(1-a)r`. -/
noncomputable def mixture (r a : ℝ≥0) (n : ℕ) : ℝ :=
  (mass ((1+a)*r) n + mass ((1-a)*r) n) / 2

/-- The normalized discrete Hellinger distance on the natural numbers. -/
noncomputable def hellinger (p q : ℕ → ℝ) : ℝ :=
  Real.sqrt ((∑' n, (Real.sqrt (p n) - Real.sqrt (q n))^2) / 2)

theorem main : ∃ C : ℝ, 0 < C ∧ ∀ r a : ℝ≥0, 0 < r → a ≤ 1 →
    hellinger (mass r) (mixture r a) ≤ C * (a : ℝ)^2 * (r : ℝ) := by
  sorry

end OMA.S_mo_358353
