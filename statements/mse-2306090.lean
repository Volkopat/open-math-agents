import Mathlib

namespace OMA.S_mse_2306090

/-- The Gauss hypergeometric series `₂F₁(1, b; c; z) = ∑_{n=0}^∞ ((b)_n / (c)_n) z^n`
(since `(1)_n = n!` cancels `n!`). -/
noncomputable def hyp2F1_1 (b c z : ℝ) : ℝ :=
  ∑' n : ℕ, (∏ k ∈ Finset.range n, (b + (k : ℝ)) / (c + (k : ℝ))) * z ^ n

/-- The function `K(a, x) = ((a - 1) x - 1) / (x + 1) * ₂F₁(1, a x; 2 + x; 1 / a)`
from MSE 2306090 equation (1). -/
noncomputable def K (a x : ℝ) : ℝ :=
  ((a - 1) * x - 1) / (x + 1) * hyp2F1_1 (a * x) (2 + x) (1 / a)

/-- The real Beta function `B(x, y) = Γ(x) Γ(y) / Γ(x + y)`. -/
noncomputable def betaFn (x y : ℝ) : ℝ :=
  Real.Gamma x * Real.Gamma y / Real.Gamma (x + y)

theorem main :
    (∀ a x : ℝ, 2 < a → 0 < x → 2 + K a x + K (1 - a) x = 0) ∧
    (∀ a x : ℝ, 1 < a → 0 < x →
      2 + (1 / a) * K a x + ((a - 1) / a) * K (a / (a - 1)) ((a - 1) * x) =
        a * x * (a - 1) ^ (x - 1) * (a / (a - 1)) ^ (a * x - 2) * betaFn x ((a - 1) * x)) := by
  sorry

end OMA.S_mse_2306090
