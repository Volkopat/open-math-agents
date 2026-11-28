import Mathlib

/-!
# Reinhardt's conjecture

Source: https://en.wikipedia.org/wiki/Reinhardt's_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Reinhardt, 1934): the smoothed octagon has the lowest maximum packing density of all
centrally symmetric convex plane sets.

Conventions:
* Convex plane sets are convex bodies: compact convex `K ⊆ ℝ²` with nonempty interior; centrally
  symmetric means `K = -K` (up to translation, which changes no density).
* For centrally symmetric convex bodies in the plane the maximum packing density equals the
  maximum lattice packing density (Fejes Tóth; Rogers). A lattice `ℤ b₁ + ℤ b₂` (`b₁, b₂`
  linearly independent) packs `K` if the translates `K + λ` have pairwise disjoint interiors,
  i.e. `int K ∩ int (K + λ) = ∅` for `λ ≠ 0`; the density is `area K / |det(b₁, b₂)|`.
* The smoothed octagon has maximum packing density `(8 - 4√2 - log 2) / (2√2 - 1) ≈ 0.902414`
  (Reinhardt; Mahler). The conjecture is therefore that every centrally symmetric convex body has
  maximum (lattice) packing density at least this number, which is what `main` states (equality
  for the smoothed octagon is known).
-/

namespace OMA.S_wp_reinhardt_s_conjecture

open MeasureTheory

/-- The plane. -/
abbrev E := EuclideanSpace ℝ (Fin 2)

/-- The lattice `ℤ b₁ + ℤ b₂`. -/
def lattice (b₁ b₂ : E) : Set E := {v | ∃ m n : ℤ, v = (m : ℝ) • b₁ + (n : ℝ) • b₂}

/-- The lattice `ℤ b₁ + ℤ b₂` packs `K`. -/
def Packs (K : Set E) (b₁ b₂ : E) : Prop :=
  ∀ v ∈ lattice b₁ b₂, v ≠ 0 → Disjoint (interior K) (interior ((fun x => x + v) '' K))

/-- `|det(b₁, b₂)|`, the covolume of the lattice. -/
def covol (b₁ b₂ : E) : ℝ := |b₁ 0 * b₂ 1 - b₁ 1 * b₂ 0|

/-- The maximum lattice packing density of `K`. -/
noncomputable def latticePackingDensity (K : Set E) : ℝ :=
  sSup {δ | ∃ b₁ b₂ : E, covol b₁ b₂ ≠ 0 ∧ Packs K b₁ b₂ ∧ δ = (volume K).toReal / covol b₁ b₂}

/-- The packing density of the smoothed octagon. -/
noncomputable def smoothedOctagonDensity : ℝ :=
  (8 - 4 * Real.sqrt 2 - Real.log 2) / (2 * Real.sqrt 2 - 1)

/-- Reinhardt's conjecture. -/
theorem main : ∀ K : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
    (∀ x ∈ K, -x ∈ K) → smoothedOctagonDensity ≤ latticePackingDensity K := by
  sorry

end OMA.S_wp_reinhardt_s_conjecture
