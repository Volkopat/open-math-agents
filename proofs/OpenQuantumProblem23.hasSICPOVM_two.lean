import FormalConjectures.OpenQuantumProblems.«23»

/-!
# Shorter proof of `OpenQuantumProblem23.hasSICPOVM_two`
-/

open OpenQuantumProblem23

theorem OMA.solution : type_of% @OpenQuantumProblem23.hasSICPOVM_two := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ha : tetraA ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
  have hb : tetraB ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have h4 : ∀ x : ℝ, x ^ 4 = (x ^ 2) ^ 2 := fun x => by ring
  have hω : ω = ⟨-1 / 2, Real.sqrt 3 / 2⟩ := Complex.ext (by simp [ω]) (by simp [ω])
  have hω2 : (⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ^ 2 = ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩ := by
    apply Complex.ext <;> simp [pow_two] <;> nlinarith [h3]
  refine ⟨qubitSICFamily, qubitSICFamily_normalized, fun i j hij => ?_⟩
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    simp [sicOverlapSq, overlapSq, qubitSICFamily, vec2, Fin.sum_univ_two, hω, hω2,
      Complex.normSq_apply] <;>
    ring_nf <;> simp only [h4, ha, hb, h3] <;> norm_num
