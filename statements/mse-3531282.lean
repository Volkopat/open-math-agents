import Mathlib

/-!
# Volume-Preserving Smooth Map of the Closed Unit Disk with Prescribed Singular Values

Source: https://math.stackexchange.com/questions/3531282/is-there-a-volume-preserving-diffeomorphism-of-the-disk-with-prescribed-singular
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

## Problem Statement
Let `0 < σ₁ < σ₂` satisfy `σ₁ * σ₂ = 1`, and let `D ⊆ ℝ^2` be the closed unit disk.
Does there exist a smooth map `f : D → D` such that at every point `x ∈ D`, the
differential `df(x)` has singular values `σ₁, σ₂` and `det(df(x)) = 1`?

## Formalization Notes
For a `2 × 2` real matrix `M` with `det M = 1`, its singular values are `σ₁, σ₂` (where
`σ₁ * σ₂ = 1`) iff its Frobenius norm squared is `σ₁^2 + σ₂^2`.
We express "smooth on `D`" as `C^∞` (not analytic: the order is `((⊤ : ℕ∞) : WithTop ℕ∞)`)
on some open set `U ⊇ D`, with `f '' D ⊆ D`, and `fderiv ℝ f x` of determinant `1` and Frobenius
norm squared `σ₁^2 + σ₂^2` at every `x ∈ D`. The first question of the post (a smooth map;
the diffeomorphism variant is a follow-up) is stated, for every admissible pair `σ₁ < σ₂`.
-/

namespace OMA.S_mse_3531282

abbrev R2 := EuclideanSpace ℝ (Fin 2)

def closedDisk : Set R2 := Metric.closedBall 0 1

noncomputable def matrixOfCLM (L : R2 →L[ℝ] R2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => (L (EuclideanSpace.single j (1 : ℝ))) i

theorem main :
    ∀ σ₁ σ₂ : ℝ, 0 < σ₁ → σ₁ < σ₂ → σ₁ * σ₂ = 1 →
      ∃ (U : Set R2) (f : R2 → R2),
        IsOpen U ∧ closedDisk ⊆ U ∧
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U ∧
        Set.MapsTo f closedDisk closedDisk ∧
        ∀ x ∈ closedDisk,
          let M := matrixOfCLM (fderiv ℝ f x)
          M.det = 1 ∧
          (∑ i : Fin 2, ∑ j : Fin 2, (M i j) ^ 2) = σ₁ ^ 2 + σ₂ ^ 2 := by
  sorry

end OMA.S_mse_3531282
