import Mathlib

/-!
# Besicovitch directionally-limited property for polynomial-eccentricity ellipsoids

Source: https://mathoverflow.net/questions/188526
Credit: @artnoage

In Euclidean space `ℝᵈ` (`d ≥ 2`), consider closed ellipsoids obtained from an axis-aligned
ellipsoid with semi-axes `R ^ (α i)` (where `0 < R < 1` and `1 < α i < α₀` for a uniform bound
`α₀ > 1`) by an orthogonal transformation and translation. The question asks whether the
directionally-limited multiplicity bound of Besicovitch's covering theorem holds: is there a
uniform bound `M` (depending only on `d` and `α₀`) on the number of such ellipsoids that have
a common point while no ellipsoid contains the center of another?
-/

namespace OMA.S_mo_188526

/-- Closed ellipsoid in `ℝᵈ` with center `c`, orthogonal frame `U`, base scale `R`, and
axis exponents `α : Fin d → ℝ`. -/
noncomputable def ellipsoid {d : ℕ} (c : EuclideanSpace ℝ (Fin d))
    (U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (R : ℝ) (α : Fin d → ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∑ i : Fin d, (U (x - c) i / R ^ (α i)) ^ 2 ≤ 1}

/-- Whether a uniform Besicovitch multiplicity bound holds for intersecting admissible ellipsoids
whose centers belong only to their own ellipsoid. -/
theorem main :
    ∀ (d : ℕ), 2 ≤ d → ∀ α₀ : ℝ, 1 < α₀ →
      ∃ M : ℕ, ∀ (N : ℕ)
        (c : Fin N → EuclideanSpace ℝ (Fin d))
        (U : Fin N → (EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)))
        (R : Fin N → ℝ) (α : Fin N → Fin d → ℝ),
        (∀ k, 0 < R k ∧ R k < 1) →
        (∀ k i, 1 < α k i ∧ α k i < α₀) →
        (∃ p, ∀ k, p ∈ ellipsoid (c k) (U k) (R k) (α k)) →
        (∀ j k, c j ∈ ellipsoid (c k) (U k) (R k) (α k) → j = k) →
        N ≤ M := by
  sorry

end OMA.S_mo_188526
