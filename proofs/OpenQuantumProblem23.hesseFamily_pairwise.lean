import FormalConjectures.OpenQuantumProblems.«23»

/-! Direct pairwise overlap calculation for the nine Hesse qutrit states.
The original proof is due to @HudZah (PR #407), with the current coordinate
certificate by @joshuadc11 (PR #13355). -/

open OpenQuantumProblem23

set_option maxHeartbeats 1000000 in
theorem OMA.solution : type_of% @OpenQuantumProblem23.hesseFamily_pairwise := by
  intro i j hij
  have hs : hesseS ^ 2 = (1 / 2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hr2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have fourth (x : ℝ) : x ^ 4 = (x ^ 2) ^ 2 := pow_mul x 2 2
  have hw2 : ω ^ 2 = star ω := by
    apply Complex.ext <;> norm_num [ω, pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith [hr2]
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    simp only [overlapSq, hesseFamily, vec3, Fin.sum_univ_three, hw2];
  all_goals simp [Complex.normSq_apply, ω, sicOverlapSq] <;>
    ring_nf <;> norm_num [fourth, hs, hr2]
