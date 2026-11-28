import Mathlib

/-! Source: https://mathoverflow.net/questions/115317 -/

namespace OMA.S_mo_115317

/-- The real block matrix from the question, indexed by block and position in the block. -/
noncomputable def giuliaMatrix {n : ℕ} (a c : Fin n → ℝ) (C : Fin n → Fin n → ℝ) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ :=
  fun i j =>
    if i.1 = j.1 then
      if i.2 = j.2 then (if i.2 = 0 then a i.1 else -a i.1) else 0
    else
      let b := C i.1 j.1 * (c i.1 * c j.1) / (2 * Real.sqrt (a i.1 * a j.1))
      if j.2 = 0 then b else -b

/-- Do the quantitative bounds in the question suffice for all eigenvalues to be real? -/
theorem main :
    ∀ (n : ℕ) (a c : Fin n → ℝ) (C : Fin n → Fin n → ℝ),
      (∀ i, 0 < a i ∧ 0 ≤ c i ∧ c i < a i) →
      (∀ i j, C i j = C j i ∧ |C i j| < 1) →
      ∀ z : ℂ,
        (∃ v : (Fin n × Fin 2) → ℂ, v ≠ 0 ∧
          ((giuliaMatrix a c C).map Complex.ofReal).mulVec v = z • v) →
        z.im = 0 := by
  sorry

end OMA.S_mo_115317
