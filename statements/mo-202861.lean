import Mathlib

namespace OMA.S_mo_202861

abbrev Point := EuclideanSpace ℝ (Fin 3)

/-- A three-coloring of Euclidean three-space avoids rainbow unit triangles
and takes the prescribed colors on a unit rhombus with a transcendental diagonal. -/
theorem main :
    ∀ α β : ℝ, 0 < α → 0 < β → α ^ 2 + β ^ 2 = 1 → Transcendental ℚ α →
      ∃ color : Point → Fin 3,
        color (WithLp.toLp 2 ![α, 0, 0]) = 0 ∧
        color (WithLp.toLp 2 ![0, β, 0]) = 0 ∧
        color (WithLp.toLp 2 ![-α, 0, 0]) = 1 ∧
        color (WithLp.toLp 2 ![0, -β, 0]) = 2 ∧
        ∀ x y z : Point, dist x y = 1 → dist y z = 1 → dist z x = 1 →
          color x = color y ∨ color y = color z ∨ color z = color x := by
  sorry

end OMA.S_mo_202861
