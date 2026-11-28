import Mathlib

/-! Source: https://mathoverflow.net/questions/171746 -/

open Matrix Set
open scoped ComplexOrder

namespace OMA.S_mo_171746

noncomputable def compressed {m n q : ℕ}
    (T : Matrix (Fin m) (Fin m) ℂ)
    (Z : Matrix (Fin q) (Fin m × Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  Z * Matrix.kronecker T (X * (1 + Xᴴ * X)⁻¹ * Xᴴ) * Zᴴ

noncomputable def objective {m n q : ℕ}
    (T : Matrix (Fin m) (Fin m) ℂ)
    (Z : Matrix (Fin q) (Fin m × Fin n) ℂ)
    (D : Matrix (Fin q) (Fin n × Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  let v := D.mulVec (fun i => X i.1 i.2)
  (dotProduct (star v) ((compressed T Z X)⁻¹.mulVec v)).re

noncomputable def mix {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :=
  (1 - t) • X + t • Y

/-- The proposed quasiconvexity inequality on each segment on which the
 two inverses in the objective both exist. -/
theorem main : ∀ (m n q : ℕ) (T : Matrix (Fin m) (Fin m) ℂ)
    (Z : Matrix (Fin q) (Fin m × Fin n) ℂ)
    (D : Matrix (Fin q) (Fin n × Fin n) ℂ),
    q < m * n → T.PosDef →
    (∀ i j, Z i j = 0 ∨ Z i j = 1) →
    (∀ i, ∃! j, Z i j ≠ 0) →
    (∀ i, ∃! j, D i j ≠ 0) →
    (∀ j, ∃ i, D i j ≠ 0) →
    ∀ (X Y : Matrix (Fin n) (Fin n) ℂ),
      (∀ t ∈ Icc (0 : ℝ) 1, IsUnit (1 + (mix X Y t)ᴴ * mix X Y t) ∧
        IsUnit (compressed T Z (mix X Y t))) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        objective T Z D (mix X Y t) ≤ max (objective T Z D X) (objective T Z D Y) := by
  sorry

end OMA.S_mo_171746
