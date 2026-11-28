import FormalConjectures.OpenQuantumProblems.«23»

open OpenQuantumProblem23

lemma tA2 : tetraA ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
lemma tB2 : tetraB ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
lemma s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
lemma q {x c : ℝ} (h : x ^ 2 = c) : x ^ 4 = c ^ 2 ∧ x ^ 6 = c ^ 3 := by subst h; constructor <;> ring
lemma ω_re : ω.re = -1 / 2 := by simp [ω]
lemma ω_im : ω.im = √3 / 2 := by simp [ω]

theorem OMA.solution : type_of% @OpenQuantumProblem23.qubitSICFamily_pairwise := by
  intro i j hij
  rw [sicOverlapSq_two]
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    simp [overlapSq, qubitSICFamily, vec2, Fin.sum_univ_two, Complex.normSq_apply,
      ω_re, ω_im, pow_two, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;> norm_num [tA2, tB2, q tA2, q tB2, q s3, s3]
