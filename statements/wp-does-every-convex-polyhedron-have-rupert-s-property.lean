import Mathlib

/-!
# Does every convex polyhedron have Rupert's property?

Source: https://en.wikipedia.org/wiki/Prince_Rupert's_cube#Generalizations
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A convex polyhedron `P` has Rupert's property if a copy of `P` congruent to it can pass through a
straight tunnel cut through `P`. Question: does every convex polyhedron have this property?

Conventions:
* A convex polyhedron is the convex hull of a finite set `S ⊆ ℝ³` with nonempty interior.
* Standard reformulation (used e.g. by Jerrard–Wetzel–Yuan and Steininger–Yurkevich): `P` is
  Rupert iff there are rotations `R₁, R₂ ∈ SO(3)` and a translation `t ∈ ℝ²` such that the
  orthogonal projection of `R₁ P` to the `xy`-plane, shifted by `t`, lies in the interior of the
  projection of `R₂ P`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_wp_does_every_convex_polyhedron_have_rupert_s_property

open Matrix

/-- Orthogonal projection `ℝ³ → ℝ²` onto the first two coordinates. -/
def proj (x : Fin 3 → ℝ) : Fin 2 → ℝ := fun i => x (Fin.castLE (by norm_num) i)

/-- The rotation group `SO(3)` acting on `ℝ³ = Fin 3 → ℝ`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- `P` has Rupert's property. -/
def IsRupert (P : Set (Fin 3 → ℝ)) : Prop :=
  ∃ (R₁ R₂ : SO3) (t : Fin 2 → ℝ),
    (fun x => proj ((R₁ : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) + t) '' P ⊆
      interior ((fun x => proj ((R₂ : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x)) '' P)

/-- Every convex polyhedron has Rupert's property. -/
theorem main : ∀ S : Finset (Fin 3 → ℝ),
    (interior (convexHull ℝ (S : Set (Fin 3 → ℝ)))).Nonempty →
    IsRupert (convexHull ℝ (S : Set (Fin 3 → ℝ))) := by
  sorry

end OMA.S_wp_does_every_convex_polyhedron_have_rupert_s_property
