import Mathlib

namespace OMA.S_mo_452847

abbrev Point := EuclideanSpace ℝ (Fin 3)

/-- The twelve vertices of a regular icosahedron of edge length two. -/
def vertices : Set Point :=
  let φ := (1 + Real.sqrt 5) / 2
  {p | ∃ u v : ℝ, (u = 1 ∨ u = -1) ∧ (v = φ ∨ v = -φ) ∧
    (p = WithLp.toLp 2 ![0, u, v] ∨
      p = WithLp.toLp 2 ![u, v, 0] ∨ p = WithLp.toLp 2 ![v, 0, u])}

/-- Every placement of a regular icosahedron has a closed triangular face
that contains no point with rational coordinates. -/
theorem main :
    ∀ (scale : ℝ), 0 < scale →
      ∀ (rotation : Point ≃ₗᵢ[ℝ] Point) (translation : Point),
        ∃ a b c : Point, a ∈ vertices ∧ b ∈ vertices ∧ c ∈ vertices ∧
          dist a b = 2 ∧ dist b c = 2 ∧ dist c a = 2 ∧
          ¬ ∃ p ∈ convexHull ℝ
            ({translation + scale • rotation a,
              translation + scale • rotation b,
              translation + scale • rotation c} : Set Point),
            ∀ i : Fin 3, ∃ q : ℚ, (q : ℝ) = p i := by
  sorry

end OMA.S_mo_452847
