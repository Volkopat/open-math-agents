import Mathlib

-- Mahler's conjecture: the Mahler volume of a centrally symmetric convex body is at least
-- that of the hypercube of the same dimension.
-- Source: https://en.wikipedia.org/wiki/Mahler_volume
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
Source definitions: a convex body in Euclidean space is a compact convex set with non-empty
interior. For a centrally symmetric convex body `B` in `n`-dimensional Euclidean space, the polar
body is `B° = {x | x ⬝ y ≤ 1 for all y ∈ B}` and the Mahler volume is `vol(B) · vol(B°)`.
The Mahler volume of the hypercube is `4^n / Γ(n+1) = 4^n / n!` (computed in the source).
The open question asks whether every centrally symmetric convex body has Mahler volume at least
that of the hypercube; it is stated here in the affirmative.

Conventions:
* Euclidean space is `EuclideanSpace ℝ (Fin n)` with Lebesgue measure `volume`.
* Centrally symmetric means symmetric about the origin, `x ∈ B ↔ -x ∈ B`: the polar in the
  source is taken with respect to the origin, so the centre of symmetry is the origin.
* The hypercube's Mahler volume is written as the explicit value `4^n / n!` from the source.
* All dimensions `n` are included (for `n = 0` both sides equal `1`).
-/

namespace OMA.S_wp_mahler_s_conjecture

/-- The polar body `{x | ⟪x, y⟫ ≤ 1 for all y ∈ B}`. -/
def polarBody {n : ℕ} (B : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ y ∈ B, inner ℝ x y ≤ 1}

/-- Mahler's conjecture. -/
theorem main : ∀ (n : ℕ) (B : Set (EuclideanSpace ℝ (Fin n))),
    IsCompact B → Convex ℝ B → (interior B).Nonempty → (∀ x, x ∈ B ↔ -x ∈ B) →
      ENNReal.ofReal (4 ^ n / (n.factorial : ℝ)) ≤
        MeasureTheory.volume B * MeasureTheory.volume (polarBody B) := by
  sorry

end OMA.S_wp_mahler_s_conjecture
