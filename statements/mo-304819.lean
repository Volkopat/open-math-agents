import Mathlib

/-!
# Power sums of distances for polygons inscribed in a circle

Source: https://mathoverflow.net/questions/304819
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (MathOverflow): let `A₁ … A_n` be the regular polygon inscribed in a circle and
`B₁ … B_n` any other polygon inscribed in the same circle; with `x_{ij} = A_iA_j`,
`y_{ij} = B_iB_j`, we have `∑_{i<j} x_{ij}^α ≥ ∑_{i<j} y_{ij}^α` for `1 ≤ α ≤ 2`.

Conventions:
* The circle is the unit circle in `ℂ` (the inequality is scale invariant); the regular polygon
  has vertices `exp(2πik/n)`. "Polygon inscribed in the circle": `n` points on the circle
  (coincidences allowed; they only lower the right-hand side). `n ≥ 2`.
-/

namespace OMA.S_mo_304819

theorem main :
    ∀ (n : ℕ) (α : ℝ), 2 ≤ n → 1 ≤ α → α ≤ 2 → ∀ B : Fin n → ℂ, (∀ i, ‖B i‖ = 1) →
      ∑ i : Fin n, ∑ j : Fin n, (if i < j then ‖B i - B j‖ ^ α else 0) ≤
        ∑ i : Fin n, ∑ j : Fin n, (if i < j then
          ‖Complex.exp (2 * Real.pi * Complex.I * i / n) -
            Complex.exp (2 * Real.pi * Complex.I * j / n)‖ ^ α else 0) := by
  sorry

end OMA.S_mo_304819
