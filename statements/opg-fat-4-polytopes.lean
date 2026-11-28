import Mathlib

/-!
# Fat 4-polytopes

Source: https://www.openproblemgarden.org/op/fat_4_polytopes
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (Eppstein, Kuperberg, Ziegler): the fatness of a 4-polytope `P` is
`(f₁ + f₂) / (f₀ + f₃)`, where `fᵢ` is the number of `i`-dimensional faces of `P`. Is there a
constant `c` such that every convex 4-polytope has fatness at most `c`?

Conventions:
* A convex 4-polytope is the convex hull of a finite set `S ⊆ ℝ⁴` whose affine span is all of
  `ℝ⁴`.
* The faces of a polytope are exactly its exposed faces; a face's dimension is the dimension of
  its affine span. `fᵢ` counts the nonempty exposed faces of dimension `i` (for `i ≤ 3` these are
  proper faces automatically).
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_opg_fat_4_polytopes

/-- Four-dimensional Euclidean space. -/
abbrev E := EuclideanSpace ℝ (Fin 4)

/-- The number of nonempty `i`-dimensional faces of a set `P ⊆ ℝ⁴`. -/
noncomputable def faceCount (P : Set E) (i : ℕ) : ℕ :=
  {F : Set E | IsExposed ℝ P F ∧ F.Nonempty ∧
    Module.finrank ℝ (affineSpan ℝ F).direction = i}.ncard

/-- The fatness `(f₁ + f₂) / (f₀ + f₃)` of `P`. -/
noncomputable def fatness (P : Set E) : ℝ :=
  ((faceCount P 1 + faceCount P 2 : ℕ) : ℝ) / ((faceCount P 0 + faceCount P 3 : ℕ) : ℝ)

/-- There is a uniform bound on the fatness of convex 4-polytopes. -/
theorem main : ∃ c : ℝ, ∀ S : Finset E, affineSpan ℝ (S : Set E) = ⊤ →
    fatness (convexHull ℝ (S : Set E)) ≤ c := by
  sorry

end OMA.S_opg_fat_4_polytopes
