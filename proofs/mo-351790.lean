import OMAStatements.S_mo_351790

-- Problem: MathOverflow 351790, size 8. Take H = [[-1, 1], [1, 1]] (H H = 2 I, det H = -2, last row and
-- column all 1) and Q = (1 / (2 sqrt 2)) (H ⊗ H ⊗ H), reindexed by Fin 8. Then Q^T Q = (1/8) 8 I = I,
-- det Q = (2 sqrt 2)^(-8) (-2)^4 ((-2)^2 (-2)^2)^2 = 4096 / 4096 = 1, every entry is ±1/(2 sqrt 2), and the
-- last row and column (index 7 = (1, 1, 1)) are products of 1s, hence positive.

namespace OMA.MO351790

open Matrix
open scoped Kronecker

noncomputable def H : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; 1, 1]

lemma H_apply_one (a : Fin 2) : H a 1 = 1 := by fin_cases a <;> simp [H]

lemma H_symm (a b : Fin 2) : H a b = H b a := by fin_cases a <;> fin_cases b <;> simp [H]

lemma H_abs (a b : Fin 2) : |H a b| = 1 := by fin_cases a <;> fin_cases b <;> simp [H]

lemma H_mul : H * H = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [H, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

lemma H_det : H.det = -2 := by simp [H, det_fin_two]; norm_num

noncomputable def K : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℝ := H ⊗ₖ (H ⊗ₖ H)

lemma K_apply (a b : Fin 2 × Fin 2 × Fin 2) :
    K a b = H a.1 b.1 * (H a.2.1 b.2.1 * H a.2.2 b.2.2) := by
  simp [K]

lemma K_transpose : Kᵀ = K := by
  ext a b; rw [transpose_apply, K_apply, K_apply, H_symm a.1, H_symm a.2.1, H_symm a.2.2]

lemma K_mul : K * K = (8 : ℝ) • (1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℝ) := by
  rw [K, ← mul_kronecker_mul, ← mul_kronecker_mul, H_mul]
  simp only [smul_kronecker, kronecker_smul, one_kronecker_one, smul_smul]
  norm_num

lemma K_det : K.det = 4096 := by
  rw [K, det_kronecker, det_kronecker, H_det]; simp; norm_num

lemma K_abs (a b : Fin 2 × Fin 2 × Fin 2) : |K a b| = 1 := by
  rw [K_apply, abs_mul, abs_mul, H_abs, H_abs, H_abs]; norm_num

def e : Fin 2 × Fin 2 × Fin 2 ≃ Fin 8 :=
  ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv).trans (finCongr rfl)

lemma e_symm_seven : e.symm 7 = (1, 1, 1) := by decide

noncomputable def c : ℝ := 1 / (2 * Real.sqrt 2)

lemma c_pos : 0 < c := by unfold c; positivity

lemma c_sq : c ^ 2 * 8 = 1 := by
  unfold c
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma c_pow_eight : c ^ 8 * 4096 = 1 := by
  have : c ^ 8 = (c ^ 2) ^ 4 := by ring
  rw [this]
  have h := c_sq
  have hc2 : c ^ 2 = 1 / 8 := by linarith
  rw [hc2]; norm_num

noncomputable def Q : Matrix (Fin 8) (Fin 8) ℝ := c • reindex e e K

lemma Q_apply (i j : Fin 8) : Q i j = c * K (e.symm i) (e.symm j) := by
  simp [Q, reindex_apply]

end OMA.MO351790

open OMA.MO351790 Matrix in
theorem OMA.solution : type_of% @OMA.S_mo_351790.main := by
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · rw [Q, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, transpose_reindex,
      K_transpose, reindex_apply, submatrix_mul_equiv, K_mul]
    ext i j
    have h := c_sq
    by_cases hij : i = j
    · subst hij; simp; nlinarith
    · simp [Matrix.one_apply, hij]
  · rw [Q, det_smul, det_reindex_self, K_det, Fintype.card_fin, c_pow_eight]
  · intro i j
    rw [Q_apply, Q_apply, abs_mul, abs_mul, K_abs, K_abs]
  · intro i
    rw [Q_apply, Q_apply, e_symm_seven, K_apply, K_apply]
    simp only [H_apply_one, mul_one]
    refine ⟨?_, ?_⟩
    · exact c_pos
    · rw [H_symm 1, H_symm 1, H_symm 1]; simp only [H_apply_one, mul_one]; exact c_pos
