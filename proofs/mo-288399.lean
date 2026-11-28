import OMAStatements.S_mo_288399

-- Problem: Bound on gap between least eigenvalues of $n \times n$ correlation matrix and of its $(n -1) \times (n-1)$ submatrices
-- Upstream: statements/mo-288399.lean (declaration OMA.S_mo_288399.main)
-- Credit: @FrancoisCharroin
-- Refutation via the 3 x 3 equicorrelation matrix with diagonal 1 and off-diagonal -1/2.

namespace OMA.Mo288399

open OMA.S_mo_288399

noncomputable def A3 : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if i = j then 1 else -(1 / 2 : ℝ)

lemma A3_symm : A3.IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, A3]
  by_cases h : i = j
  · subst h; simp
  · have h' : j ≠ i := Ne.symm h
    simp [h, h']

lemma A3_diag (i : Fin 3) : A3 i i = 1 := by
  simp [A3]

lemma quad_A3 (x : Fin 3 → ℝ) :
    quad A3 x =
      (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 - x 0 * x 1 - x 0 * x 2 - x 1 * x 2 := by
  simp [quad, Fin.sum_univ_three, A3]
  ring

lemma normSq_three (x : Fin 3 → ℝ) :
    normSq x = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
  simp only [normSq, Fin.sum_univ_three]

lemma A3_psd (x : Fin 3 → ℝ) : 0 ≤ quad A3 x := by
  rw [quad_A3]
  have h :
      (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 - x 0 * x 1 - x 0 * x 2 - x 1 * x 2 =
        ((x 0 - x 1) ^ 2 + (x 0 - x 2) ^ 2 + (x 1 - x 2) ^ 2) / 2 := by ring
  rw [h]
  positivity

lemma A3_least_full : LeastOn A3 (fun _ => True) 0 := by
  refine ⟨fun x _ => ?_, fun _ => (1 : ℝ), trivial, ?_, ?_⟩
  · simpa using A3_psd x
  · rw [normSq_three]; norm_num
  · rw [quad_A3, normSq_three]; norm_num

lemma A3_least_del (i : Fin 3) : LeastOn A3 (fun x => x i = 0) (1 / 2 : ℝ) := by
  fin_cases i
  · refine ⟨fun x hx => ?_, fun k : Fin 3 => if k = 0 then (0 : ℝ) else 1, by simp, ?_, ?_⟩
    · change x 0 = 0 at hx
      rw [quad_A3, normSq_three, hx]
      nlinarith [sq_nonneg (x 1 - x 2)]
    · simp [normSq_three]
    · simp [quad_A3, normSq_three]; norm_num
  · refine ⟨fun x hx => ?_, fun k : Fin 3 => if k = 1 then (0 : ℝ) else 1, by simp, ?_, ?_⟩
    · change x 1 = 0 at hx
      rw [quad_A3, normSq_three, hx]
      nlinarith [sq_nonneg (x 0 - x 2)]
    · simp [normSq_three]
    · simp [quad_A3, normSq_three]; norm_num
  · refine ⟨fun x hx => ?_, fun k : Fin 3 => if k = 2 then (0 : ℝ) else 1, by simp, ?_, ?_⟩
    · change x 2 = 0 at hx
      rw [quad_A3, normSq_three, hx]
      nlinarith [sq_nonneg (x 0 - x 1)]
    · simp [normSq_three]
    · simp [quad_A3, normSq_three]; norm_num

end OMA.Mo288399

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_288399.main) := by
  intro hmain
  have h :=
    hmain 3 (by decide) OMA.Mo288399.A3 OMA.Mo288399.A3_symm OMA.Mo288399.A3_diag
      OMA.Mo288399.A3_psd 0 (fun _ => (1 / 2 : ℝ))
      OMA.Mo288399.A3_least_full OMA.Mo288399.A3_least_del 0
  rcases h with ⟨i, hi⟩
  have hsum :
      (∑ k : Fin 3, if k = (0 : Fin 3) then (0 : ℝ) else (OMA.Mo288399.A3 k 0) ^ 2) = 1 / 2 := by
    simp [Fin.sum_univ_three, OMA.Mo288399.A3]
    norm_num
  rw [hsum] at hi
  have h1 : (1 : ℝ) ≤ Real.sqrt (1 / 2 : ℝ) := by
    norm_num at hi ⊢
    exact hi
  have hsq : ((1 : ℝ)) ^ 2 ≤ (Real.sqrt (1 / 2 : ℝ)) ^ 2 :=
    sq_le_sq' (by linarith [Real.sqrt_nonneg (1 / 2 : ℝ)]) h1
  rw [Real.sq_sqrt (by norm_num)] at hsq
  norm_num at hsq
