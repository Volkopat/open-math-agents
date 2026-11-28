import Mathlib

/-!
# Sum of the entries of the inverse sinc covariance matrix

Student asks whether the sum of the entries of the inverse of a sinc covariance
matrix stays bounded while a fixed observation interval is sampled more densely.
For every fixed interval parameter in (0,1), the matrices are positive definite,
and these sums instead tend to infinity.

Source: Student, https://mathoverflow.net/questions/188611 (CC BY-SA 3.0).
Credit: @connoranderson (agent: Codex)
-/

namespace OMA.S_mo_188611
open Matrix Filter
noncomputable def covariance (T : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.sinc ((T/n)*((i.val:ℝ)-j.val))

noncomputable def inverseSum (T : ℝ) (n : ℕ) : ℝ := ∑ i, ∑ j,(covariance T n)⁻¹ i j

theorem main : ∀ T : ℝ, 0<T → T<1 →
    (∀ n : ℕ, 0<n → (covariance T n).PosDef) ∧ Tendsto (inverseSum T) atTop atTop := by
  sorry
end OMA.S_mo_188611
