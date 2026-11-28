import FormalConjectures.OpenQuantumProblems.«23»

/-! Use the established overlap constant and normalization for the Hesse family.
The first proof is credited to @jlgmaarav. -/

open OpenQuantumProblem23

theorem OMA.solution : type_of% @OpenQuantumProblem23.hasSICPOVM_three := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : hesseS ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hs4 : hesseS ^ 4 = 1 / 4 := by
    rw [show hesseS ^ 4 = (hesseS ^ 2) ^ 2 by ring, hs]; norm_num
  have hω : ω = ⟨-1 / 2, Real.sqrt 3 / 2⟩ := Complex.ext (by simp [ω]) (by simp [ω])
  have hω2 : (⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ^ 2 = ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩ := by
    apply Complex.ext <;> simp [pow_two] <;> nlinarith [h3]
  refine ⟨hesseFamily, hesseFamily_normalized, fun i j hij => ?_⟩
  rw [sicOverlapSq_three]
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    simp [overlapSq, hesseFamily, vec3, Fin.sum_univ_three, hω, hω2, Complex.normSq_apply] <;>
    ring_nf <;> simp only [hs, h3, hs4] <;> ring_nf <;> nlinarith [h3, hs]
