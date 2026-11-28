import Mathlib

/-!
# Singular values of two-sided matrix compressions

Source: Xiangxiang Xu, https://mathoverflow.net/questions/437602 (CC BY-SA 4.0).
Credit: @connoranderson. The source discussion gives a convexity proof for p≥1
and a unitarily invariant norm argument. We establish a stronger pointwise
bound for arbitrary rectangular real or complex contractions on both sides.
All partial sums of nonnegative real powers then decrease, including 0<p<1.
-/
namespace OMA.S_mo_437602
open Matrix Finset
noncomputable def sv {𝕜 : Type} [RCLike 𝕜] {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜)
    (i : ℕ) : ℝ := A.toEuclideanLin.singularValues i
open scoped Matrix.Norms.L2Operator

theorem main :
    (∀ (𝕜 : Type) [RCLike 𝕜] (a b c d : ℕ)
      (L : Matrix (Fin a) (Fin b) 𝕜) (A : Matrix (Fin b) (Fin c) 𝕜)
      (R : Matrix (Fin c) (Fin d) 𝕜), ‖L‖ ≤ 1 → ‖R‖ ≤ 1 →
      ∀ i : ℕ, sv (L*A*R) i ≤ sv A i) ∧
    (∀ (𝕜 : Type) [RCLike 𝕜] (n k : ℕ) (A : Matrix (Fin n) (Fin n) 𝕜)
      (M₁ M₂ : Matrix (Fin n) (Fin k) 𝕜), M₁.conjTranspose*M₁=1 →
      M₂.conjTranspose*M₂=1 → ∀ (r : ℕ) (p : ℝ), 0≤p →
      (∑ i ∈ Finset.range r, (sv (M₁.conjTranspose*A*M₂) i)^p) ≤
        ∑ i ∈ Finset.range r, (sv A i)^p) := by
  sorry
end OMA.S_mo_437602
