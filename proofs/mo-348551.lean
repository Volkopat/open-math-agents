import OMAStatements.S_mo_348551

/-!
# A nonnegative contraction with an oscillating normalized spectral gap

The first coordinate of A is fixed, and its other two coordinates form a
weighted swap. The Perron root is one. At even times the lower two eigenvalues
of the Gram matrix coincide, and at odd times they are distinct. All three
eigenvalues lie in [0, 1] at every time.
-/

namespace OMA.BoundedGap

open OMA.S_mo_348551 Matrix Polynomial

@[local simp] lemma thirdEntry {α : Type*} (x : α) (u : Fin 2 → α) :
    Matrix.vecCons x u (2 : Fin 3) = u 1 := rfl

noncomputable def A : Matrix (Fin 3) (Fin 3) ℝ := !![1,0,0; 0,0,1; 0,1/4,0]

noncomputable def scale (m : ℕ) : ℝ := (1/4 : ℝ)^m

noncomputable def E (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1,0,0; 0,t,0; 0,0,t]

noncomputable def O (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1,0,0; 0,0,t; 0,t/4,0]

lemma evenPower (m : ℕ) : A ^ (2*m) = E (scale m) := by
  induction m with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> norm_num [E, scale]
  | succ m ih =>
    rw [Nat.mul_succ, pow_add, ih, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [E, A, scale, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

lemma oddPower (m : ℕ) : A ^ (2*m+1) = O (scale m) := by
  rw [pow_succ, evenPower]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E, A, O, Matrix.mul_apply, Fin.sum_univ_three, div_eq_mul_inv]

lemma perron : IsPositivePerronRoot A 1 := by
  have h : A.charpoly = (X - 1) * (X - C (1/2 : ℝ)) * (X + C (1/2 : ℝ)) := by
    rw [Matrix.charpoly, Matrix.det_fin_three]
    norm_num [Matrix.charmatrix_apply, Matrix.diagonal, A, Fin.ext_iff]
    have hhalf : (C (1/2 : ℝ))^2 = C (1/4 : ℝ) := by
      rw [← map_pow]
      norm_num
    linear_combination (X - 1) * hhalf
  refine ⟨zero_lt_one, ?_, ?_⟩
  · simp [h]
  · intro z hz
    simp [h, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at hz
    rcases hz with (rfl | rfl) | rfl <;> norm_num [norm_div]

noncomputable def s (k : ℕ) : Fin 3 → ℝ :=
  ![1, (scale (k/2))^2, if k%2 = 0 then (scale (k/2))^2 else (scale (k/2))^2/16]

lemma scaleBounds (m : ℕ) : 0 < scale m ∧ scale m ≤ 1 := by
  exact ⟨by unfold scale; positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩

lemma spectrumOrder (k : ℕ) : Antitone (s k) := by
  have h := scaleBounds (k / 2)
  rw [Fin.antitone_iff_succ_le]
  intro i
  fin_cases i
  · simpa [s] using pow_le_one₀ h.1.le h.2 (n := 2)
  · dsimp [s]
    split_ifs
    · rfl
    · nlinarith [sq_nonneg (scale (k / 2))]

lemma spectrum (k : ℕ) : IsOrderedSpectrum (normalizedGram A 1 k) (s k) := by
  refine ⟨spectrumOrder k, ?_⟩
  rcases k.even_or_odd' with ⟨m, rfl | rfl⟩
  · have hg : normalizedGram A 1 (2*m) =
        Matrix.diagonal ![1, (scale m)^2, (scale m)^2] := by
      simp only [normalizedGram, one_pow, inv_one, one_smul, ← Matrix.transpose_pow, evenPower]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [E, Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal, Fin.sum_univ_three] <;> ring
    rw [hg, Matrix.charpoly_diagonal]
    simp [s, Fin.prod_univ_three]
  · have hg : normalizedGram A 1 (2*m+1) =
        Matrix.diagonal ![1, (scale m)^2/16, (scale m)^2] := by
      simp only [normalizedGram, one_pow, inv_one, one_smul, ← Matrix.transpose_pow, oddPower]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [O, Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal, Fin.sum_univ_three] <;> ring
    rw [hg, Matrix.charpoly_diagonal]
    simp [s, Fin.prod_univ_three, show (2*m+1)/2 = m by omega]
    ring

end OMA.BoundedGap

open OMA.S_mo_348551 OMA.BoundedGap in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_348551.main) := by
  intro h
  have hp : ∀ i j, 0 ≤ A i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [A]
  obtain ⟨m, hm, _, hd⟩ := h A hp 1 perron s (fun k _ => spectrum k) 1 (by decide)
  have hn := hd (2*m) (by omega)
  have ht := (scaleBounds m).1
  have hpos : 0 < (scale m)^2 - (scale m)^2/16 := by nlinarith [sq_pos_of_pos ht]
  norm_num [gap, s, show (2*m+1)/2 = m by omega] at hn
  exact (not_le_of_gt (div_pos hpos (by positivity))) hn
