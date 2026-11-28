import Mathlib

namespace OMA.S_mo_212361

open Filter

abbrev Plane := ℝ × ℝ

/-- The points where two chords with different endpoints cross in their interiors. -/
def crossingPoints {n : ℕ} (p : Fin n → Plane) : Set Plane :=
  {x | ∃ a : Fin 4 ↪ Fin n,
    x ∈ openSegment ℝ (p (a 0)) (p (a 1)) ∧
    x ∈ openSegment ℝ (p (a 2)) (p (a 3))}

/-- The minimum number of distinct interior diagonal crossings over convex n-gons. -/
noncomputable def fewestCrossings (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ p : Fin n → Plane,
    ConvexIndependent ℝ p ∧ (crossingPoints p).ncard = m}

/-- Is the minimum number of distinct diagonal crossings asymptotic to n⁴/24? -/
theorem main :
    Tendsto (fun n : ℕ => (fewestCrossings n : ℝ) / (n : ℝ) ^ 4)
      atTop (nhds (1 / 24 : ℝ)) := by
  sorry

end OMA.S_mo_212361
