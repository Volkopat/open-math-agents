import Mathlib

namespace OMA.S_mse_4398439

/-- Open inequality problem from Math Stack Exchange #4398439 (V. Cîrtoaje and L. Giugiuc, 2022):
if `a, b, c, d > 0` satisfy `1/(1+a) + 1/(1+b) + 1/(1+c) + 1/(1+d) = 2`, then
`1/√a + 1/√b + 1/√c + 1/√d + 4*(3√2 - 4)/(a + b + c + d) ≥ 3√2`. -/
theorem main :
    ∀ a b c d : ℝ, 0 < a → 0 < b → 0 < c → 0 < d →
      1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) + 1 / (1 + d) = 2 →
      1 / Real.sqrt a + 1 / Real.sqrt b + 1 / Real.sqrt c + 1 / Real.sqrt d +
        4 * (3 * Real.sqrt 2 - 4) / (a + b + c + d) ≥ 3 * Real.sqrt 2 := by sorry

end OMA.S_mse_4398439
