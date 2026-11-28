import Mathlib

/-!
# Smooth proper schemes over `ℤ` with points everywhere locally

Source: https://mathoverflow.net/questions/11316/smooth-proper-schemes-over-z-with-points-everywhere-locally
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question: is there a smooth proper scheme `X → Spec ℤ` with `X(ℚ_v) ≠ ∅` for every place `v`
of `ℚ` (including `v = ∞`) and yet `X(ℚ) = ∅`? The asker expects the answer No; `main` states
that: every smooth proper `ℤ`-scheme with points over every `ℚ_p` and over `ℝ` has a rational
point.

Encoding: `X(K)` for a field `K` is the set of scheme morphisms `Spec K ⟶ X` (over `Spec ℤ`
automatically, `Spec ℤ` being terminal); smooth and proper are Mathlib's
`AlgebraicGeometry.Smooth` and `AlgebraicGeometry.IsProper` for the structure morphism.
-/

namespace OMA.S_mo_11316

open AlgebraicGeometry CategoryTheory

/-- The `No` answer (Hasse principle for smooth proper `ℤ`-schemes). -/
theorem main :
    ∀ (X : Scheme) (f : X ⟶ Spec (CommRingCat.of ℤ)), Smooth f → IsProper f →
      (∀ p : ℕ, ∀ _ : Fact p.Prime, Nonempty (Spec (CommRingCat.of ℚ_[p]) ⟶ X)) →
      Nonempty (Spec (CommRingCat.of ℝ) ⟶ X) →
      Nonempty (Spec (CommRingCat.of ℚ) ⟶ X) := by
  sorry

end OMA.S_mo_11316
