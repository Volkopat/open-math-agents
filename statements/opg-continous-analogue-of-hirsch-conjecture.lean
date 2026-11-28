import Mathlib

namespace OMA.S_opg_continous_analogue_of_hirsch_conjecture

open scoped BigOperators

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The points with positive slack in every defining inequality. -/
def strictRegion {d n : ℕ} (A : Fin n → Space d) (b : Fin n → ℝ) : Set (Space d) :=
  {x | ∀ i, inner ℝ (A i) x < b i}

/-- The primal central path obtained by minimizing the logarithmic barrier objective. -/
def IsPrimalPath {d n : ℕ} (A : Fin n → Space d) (b : Fin n → ℝ)
    (c : Space d) (path : ℝ → Space d) : Prop :=
  ∀ μ : ℝ, 0 < μ →
    path μ ∈ strictRegion A b ∧
      IsMinOn
        (fun x => inner ℝ c x - μ * ∑ i, Real.log (b i - inner ℝ (A i) x))
        (strictRegion A b) (path μ)

/-- The sum of the angles between consecutive directed segments of a polygonal path. -/
noncomputable def turningSum {d m : ℕ} (points : Fin (m + 2) → Space d) : ℝ :=
  ∑ i : Fin m, InnerProductGeometry.angle
    (points i.succ.castSucc - points i.castSucc.castSucc)
    (points i.succ.succ - points i.succ.castSucc)

/-- The primal central path curvature has no uniform bound linear in the number
of inequalities. This is the negative answer to the continuous Hirsch conjecture. -/
theorem main :
    ∀ C : ℝ, 0 < C →
      ∃ (d n m : ℕ) (A : Fin n → Space d) (b : Fin n → ℝ) (c : Space d)
        (path : ℝ → Space d) (time : Fin (m + 2) → ℝ),
        IsCompact {x : Space d | ∀ i, inner ℝ (A i) x ≤ b i} ∧
        (strictRegion A b).Nonempty ∧ c ≠ 0 ∧ IsPrimalPath A b c path ∧
        StrictMono time ∧ (∀ i, 0 < time i) ∧
        (∀ i : Fin (m + 1), path (time i.castSucc) ≠ path (time i.succ)) ∧
        C * (n : ℝ) < turningSum (path ∘ time) := by
  sorry

end OMA.S_opg_continous_analogue_of_hirsch_conjecture
