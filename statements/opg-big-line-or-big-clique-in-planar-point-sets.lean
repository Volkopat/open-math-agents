import Mathlib

/-!
# Big Line or Big Clique in Planar Point Sets

Source: https://www.openproblemgarden.org/op/big_line_or_big_clique_in_planar_point_sets
Credit: @joshuadc11

Kára–Pór–Wood Big Line or Big Clique Conjecture: for all integers `k, ℓ ≥ 2`, there exists `n`
such that every finite set `S` of at least `n` points in `ℝ²` contains either at least `ℓ`
collinear points or at least `k` pairwise visible points (where two distinct points `v, w ∈ S` are
visible with respect to `S` if the open line segment between them contains no point of `S`).

## Encoding

* Points in the plane are elements of `ℝ × ℝ`, and a finite point set is `S : Finset (ℝ × ℝ)`.
* Visibility uses Mathlib's `openSegment ℝ v w`: `Visible S v w` means no `u ∈ S` lies in
  `openSegment ℝ v w`.
* Collinearity uses Mathlib's `Collinear ℝ`.
-/

namespace OMA.S_opg_big_line_or_big_clique_in_planar_point_sets

/-- Two distinct points `v` and `w` are visible with respect to `S` if no point of `S` lies in the
open line segment between `v` and `w`. -/
def Visible (S : Finset (ℝ × ℝ)) (v w : ℝ × ℝ) : Prop :=
  ∀ u ∈ S, u ∉ openSegment ℝ v w

/-- For all `k, ℓ ≥ 2`, there exists `n` such that every finite set of at least `n` points in `ℝ²`
contains either at least `ℓ` collinear points or at least `k` pairwise visible points. -/
theorem main : ∀ k ℓ : ℕ, 2 ≤ k → 2 ≤ ℓ → ∃ n : ℕ, ∀ S : Finset (ℝ × ℝ), n ≤ S.card →
    (∃ L ⊆ S, ℓ ≤ L.card ∧ Collinear ℝ (L : Set (ℝ × ℝ))) ∨
    (∃ K ⊆ S, k ≤ K.card ∧ ∀ v ∈ K, ∀ w ∈ K, v ≠ w → Visible S v w) := by
  sorry

end OMA.S_opg_big_line_or_big_clique_in_planar_point_sets
