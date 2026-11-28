import Mathlib

/-!
# McMullen problem on projectively transforming points into convex position

Source: https://en.wikipedia.org/wiki/McMullen_problem

`ν(d)` is the largest number such that any `ν(d)` points in general position in `ℝ^d` can be
mapped by a projective transformation into convex position. Larman proved
`2d + 1 ≤ ν(d)`; the conjecture is `ν(d) = 2d + 1` (proved for `d = 2, 3, 4`).

Conventions.
- `d ≥ 2` (for `d = 1` three collinear points are never in convex position, so `ν(1) = 2`).
- General position: every `d + 1` of the points are affinely independent.
- A projective transformation is `x ↦ (A x + b) / (⟪c, x⟫ + δ)` with invertible
  `(d+1) × (d+1)` block matrix `[[A, b], [cᵀ, δ]]`, required to be defined at every point
  (`⟪c, x⟫ + δ ≠ 0`).
- Convex position: no point lies in the convex hull of the others.
- `ν(d) = 2d + 1` is stated as: the property holds for `2d + 1` points and fails for every
  larger number of points.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_wp_mcmullen_problem_on_projectively_transforming_sets_of_points_into_convex_positio

/-- Every `d + 1` of the points are affinely independent. -/
def GenPos {d n : ℕ} (x : Fin n → (Fin d → ℝ)) : Prop :=
  ∀ s : Finset (Fin n), s.card = d + 1 → AffineIndependent ℝ (fun i : s => x i)

/-- No point lies in the convex hull of the others. -/
def ConvexPos {d n : ℕ} (y : Fin n → (Fin d → ℝ)) : Prop :=
  ∀ i, y i ∉ convexHull ℝ (y '' {j | j ≠ i})

/-- Some projective transformation, defined at every point, maps the points into convex
position. -/
def ProjToConvex {d n : ℕ} (x : Fin n → (Fin d → ℝ)) : Prop :=
  ∃ (A : Matrix (Fin d) (Fin d) ℝ) (b c : Fin d → ℝ) (δ : ℝ),
    (Matrix.fromBlocks A (Matrix.of fun i (_ : Unit) => b i) (Matrix.of fun (_ : Unit) j => c j)
        (Matrix.of fun (_ : Unit) (_ : Unit) => δ)).det ≠ 0 ∧
    (∀ i, c ⬝ᵥ x i + δ ≠ 0) ∧
    ConvexPos (fun i => (c ⬝ᵥ x i + δ)⁻¹ • (A.mulVec (x i) + b))

/-- The McMullen property for `n` points in `ℝ^d`. -/
def McMullenProp (d n : ℕ) : Prop :=
  ∀ x : Fin n → (Fin d → ℝ), GenPos x → ProjToConvex x

theorem main :
    ∀ d : ℕ, 2 ≤ d → McMullenProp d (2 * d + 1) ∧ ∀ n : ℕ, 2 * d + 1 < n → ¬ McMullenProp d n := by
  sorry

end OMA.S_wp_mcmullen_problem_on_projectively_transforming_sets_of_points_into_convex_positio
