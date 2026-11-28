import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph Matrix Polynomial WrittenOnTheWallII.Test

theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.Star5_cvetkovic := by
  let A : Matrix (Fin 1 ⊕ Fin 5) (Fin 2) ℝ := fun i j =>
    if i.isLeft = (j == 0) then 1 else 0
  let B : Matrix (Fin 2) (Fin 1 ⊕ Fin 5) ℝ := fun i j =>
    if j.isRight = (i == 0) then 1 else 0
  have hA : Star5.adjMatrix ℝ = A * B := by
    ext i j
    rw [adjMatrix_apply, Matrix.mul_apply]
    cases i <;> cases j <;>
      norm_num [Star5, completeBipartiteGraph_adj, Fin.sum_univ_two, A, B]
  have hB : B * A = !![0, 5; 1, 0] := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    fin_cases i <;> fin_cases j <;> norm_num [Fin.sum_univ_succ, A, B]
  have hpoly : (Star5.adjMatrix ℝ).charpoly = X^4 * (X^2 - C 5) := by
    rw [hA, Matrix.charpoly_mul_comm_of_le _ _ (by decide), hB]
    norm_num [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_two, Matrix.one_apply]
    ring
  have hfactor : (X ^ 2 - C 5 : ℝ[X]) =
      (X - C (Real.sqrt 5)) * (X - C (-Real.sqrt 5)) := by
    rw [map_neg]
    calc
      _ = X ^ 2 - (C (Real.sqrt 5)) ^ 2 := by rw [← map_pow, Real.sq_sqrt (by norm_num)]
      _ = _ := by ring
  have hne : (X - C (Real.sqrt 5)) * (X - C (-Real.sqrt 5)) ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  unfold cvetkovic
  rw [hpoly, hfactor, roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hne),
    roots_pow, roots_X, roots_mul hne, roots_X_sub_C, roots_X_sub_C]
  have hr : 0 < Real.sqrt 5 := by positivity
  simp [Multiset.countP_eq_card_filter, Multiset.filter_nsmul, Multiset.filter_singleton, hr,
    hr.le, hr.ne, hr.ne', hr.not_ge, hr.asymm]
