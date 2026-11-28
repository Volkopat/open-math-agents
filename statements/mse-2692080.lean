import Mathlib

namespace OMA.S_mse_2692080

theorem main :
    (∑' k : ℕ, Real.exp (-((k + 1 : ℕ) : ℝ)) /
      (((k + 1 : ℕ) : ℝ) ^ (k + 1) * Real.sqrt ((k + 1 : ℕ) : ℝ))) =
    (-92 - 95 * Real.exp 1 + 86 * (Real.exp 1) ^ 2) /
      (2 * (130 - 4 * Real.exp 1 + 33 * (Real.exp 1) ^ 2)) := by
  sorry

end OMA.S_mse_2692080
