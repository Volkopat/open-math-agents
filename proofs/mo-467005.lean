import OMAStatements.S_mo_467005

-- Problem: MathOverflow 467005, the circular matrix C with C i j = x_i x_(i+1) ... x_(j-1) (cyclic).
-- With S the weighted cyclic shift and P the product of all x_i, row subtraction gives
-- C * (1 - S) = (1 - P) * I, and expanding det (1 - S) along column 0 gives 1 - P.
-- If P is not 1 this yields det C = (1 - P)^n and the inverse formula; if P = 1 then every x_i = 1
-- (they lie in [0, 1]), so C is the all-ones matrix, whose determinant is 0^n.

namespace OMA.MO467005
open OMA.S_mo_467005
open scoped Fin.NatCast

theorem path_full {n : ℕ} (x : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    path x i (n+1) = ∏ j, x j := by
  unfold path
  rw [← Fin.prod_univ_eq_prod_range (fun t => x (i + (t : Fin (n+1))))]
  simp only [Fin.cast_val_eq_self]
  exact Fintype.prod_equiv (Equiv.addLeft i) _ _ (fun _ => rfl)

theorem mul_eq {n : ℕ} (x : Fin (n+1) → ℝ) :
    circular x * (1 - shift x) = (1 - ∏ j, x j) • (1 : Matrix _ _ ℝ) := by
  ext i j
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, Matrix.mul_apply]
  have hs : ∀ k, circular x i k * shift x k j = if k = j - 1 then circular x i (j-1) * x (j-1) else 0 := by
    intro k
    simp only [shift, Matrix.of_apply]
    by_cases hk : k = j - 1
    · subst hk; simp
    · have : ¬ (k + 1 = j) := by intro h; apply hk; rw [← h]; abel
      simp [hk, this]
  simp only [hs, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [circular, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    have h1 : (i - 1 - i).val = n := by
      rw [show i - 1 - i = -1 by abel, Fin.coe_neg_one]
    rw [sub_self, Fin.val_zero, h1, mul_comm, path]
    simp only [Finset.prod_range_zero, if_true, mul_one]
    rw [← path_full x i]; unfold path; rw [Finset.prod_range_succ, mul_comm (x (i - 1))]
    congr 3
    rw [Fin.natCast_eq_last]
    rw [show (Fin.last n) = -1 by rw [Fin.ext_iff, Fin.coe_neg_one]; rfl]
    abel
  · simp only [hij, if_false, mul_zero]
    have hne : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
    have h1 : (j - i).val = (j - 1 - i).val + 1 := by
      rw [show j - 1 - i = (j - i) - 1 by abel, Fin.val_sub_one_of_ne_zero hne]
      have := Fin.pos_iff_ne_zero.mpr hne
      have : 0 < (j-i).val := this
      omega
    rw [h1, path, Finset.prod_range_succ, Fin.cast_val_eq_self, ← path]
    rw [show i + (j - 1 - i) = j - 1 by abel]
    ring


theorem det_shift {n : ℕ} (x : Fin (n+1) → ℝ) : (1 - shift x).det = 1 - ∏ j, x j := by
  cases n with
  | zero =>
    rw [Matrix.det_fin_one]
    simp [shift, Fin.prod_univ_one]
  | succ m =>
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    have hmid : ∀ k : Fin m, (1 - shift x) (Fin.castSucc k).succ 0 = 0 := by
      intro k
      simp only [shift, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply]
      have h1 : (Fin.castSucc k).succ ≠ 0 := Fin.succ_ne_zero _
      have h2 : ¬ ((Fin.castSucc k).succ + 1 = 0) := by
        rw [Fin.ext_iff, Fin.val_add_one]
        split_ifs with h
        · exfalso; rw [Fin.ext_iff] at h; simp at h; omega
        · simp
      simp [h1, h2]
    simp only [hmid, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
    -- first term
    have hA00 : (1 - shift x) 0 0 = 1 := by
      simp only [shift, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply]
      have : ¬ ((0 : Fin (m+2)) + 1 = 0) := by
        rw [Fin.ext_iff]; simp
      simp [this]
    have hM0 : ((1 - shift x).submatrix (Fin.succAbove 0) Fin.succ).det = 1 := by
      rw [Matrix.det_of_isUpperTriangular]
      · apply Finset.prod_eq_one
        intro r _
        simp only [shift, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, Matrix.submatrix_apply,
          Fin.succAbove_zero]
        have : ¬ (r.succ + 1 = r.succ) := by
          intro h; rw [Fin.ext_iff, Fin.val_add_one] at h; split_ifs at h <;> simp at h
        simp [this]
      · intro r c hrc
        simp only [shift, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, Matrix.submatrix_apply,
          Fin.succAbove_zero]
        have h1 : r.succ ≠ c.succ := by intro h; rw [Fin.succ_inj] at h; subst h; exact lt_irrefl _ hrc
        have h2 : ¬ (r.succ + 1 = c.succ) := by
          intro h
          have hrc' : c.val < r.val := hrc
          rw [Fin.ext_iff, Fin.val_add_one] at h
          split_ifs at h with h3
          · rw [Fin.ext_iff] at h3; simp at h3 h <;> omega
          · simp at h; omega
        simp [h1, h2]
    have hAl : (1 - shift x) (Fin.last m).succ 0 = - x (Fin.last m).succ := by
      simp only [shift, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply]
      have h1 : (Fin.last m).succ ≠ 0 := Fin.succ_ne_zero _
      have h2 : (Fin.last m).succ + 1 = 0 := by
        rw [Fin.ext_iff, Fin.val_add_one]; simp
      simp [h1, h2]
    have hMl : ((1 - shift x).submatrix (Fin.succAbove (Fin.last m).succ) Fin.succ).det
        = ∏ r : Fin (m+1), (- x (Fin.castSucc r)) := by
      rw [Matrix.det_of_isLowerTriangular]
      · apply Finset.prod_congr rfl
        intro r _
        simp only [shift, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, Matrix.submatrix_apply]
        rw [Fin.succ_last, Fin.succAbove_last]
        have h1 : Fin.castSucc r ≠ r.succ := by
          rw [Ne, Fin.ext_iff]; simp
        have h2 : Fin.castSucc r + 1 = r.succ := by
          rw [Fin.ext_iff, Fin.val_add_one]
          split_ifs with h3
          · exfalso; rw [Fin.ext_iff] at h3; simp at h3; omega
          · simp
        simp [h1, h2]
      · intro r c hrc
        simp only [shift, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, Matrix.submatrix_apply]
        rw [Fin.succ_last, Fin.succAbove_last]
        have hrc' : r.val < c.val := hrc
        have h1 : Fin.castSucc r ≠ c.succ := by
          rw [Ne, Fin.ext_iff]; simp; omega
        have h2 : ¬ (Fin.castSucc r + 1 = c.succ) := by
          rw [Fin.ext_iff, Fin.val_add_one]
          split_ifs with h3
          · rw [Fin.ext_iff] at h3; simp at h3; omega
          · simp; omega
        simp [h1, h2]
        intro h; subst h; omega
    rw [hA00, hM0, hAl, hMl]
    rw [Fin.prod_univ_castSucc (fun j => x j), Finset.prod_neg, Fin.succ_last]
    simp only [Fin.val_zero, pow_zero, one_mul, mul_one, Fin.val_succ, Fin.val_last, Finset.card_univ,
      Fintype.card_fin]
    have e2 : ((-1:ℝ))^(m+1) * (-1)^(m+1) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    simp only [Nat.succ_eq_add_one]
    linear_combination (-((∏ i : Fin (m+1), x (Fin.castSucc i)) * x (Fin.last (m+1)))) * e2

theorem all_one {n : ℕ} (x : Fin (n+1) → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0:ℝ) 1)
    (hP : ∏ i, x i = 1) : ∀ i, x i = 1 := by
  intro j
  by_contra hj
  have hlt : x j < 1 := lt_of_le_of_ne (hx j).2 hj
  have hle : ∏ i ∈ Finset.univ.erase j, x i ≤ 1 :=
    Finset.prod_le_one (fun i _ => (hx i).1) (fun i _ => (hx i).2)
  have := Finset.mul_prod_erase Finset.univ x (Finset.mem_univ j)
  have h0 : 0 ≤ ∏ i ∈ Finset.univ.erase j, x i := Finset.prod_nonneg (fun i _ => (hx i).1)
  nlinarith [(hx j).1]

end OMA.MO467005

open OMA.S_mo_467005 OMA.MO467005 in
theorem OMA.solution : type_of% @OMA.S_mo_467005.main := by
  intro n x hx
  have hm := mul_eq x
  refine ⟨?_, ?_⟩
  · by_cases hP : ∏ i, x i = 1
    · have h1 := all_one x hx hP
      have hC : ∀ i j, circular x i j = 1 := by
        intro i j
        simp [circular, path, h1]
      rw [hP, sub_self]
      cases n with
      | zero => rw [Matrix.det_fin_one, hC]; simp
      | succ m =>
        rw [zero_pow (Nat.succ_ne_zero m)]
        apply Matrix.det_zero_of_row_eq (i := 0) (j := 1)
        · rw [Ne, Fin.ext_iff]; simp
        · funext j; rw [hC, hC]
    · have hd := congrArg Matrix.det hm
      rw [Matrix.det_mul, det_shift, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
        pow_succ] at hd
      have hne : (1 - ∏ i, x i) ≠ 0 := sub_ne_zero.mpr (Ne.symm hP)
      exact mul_right_cancel₀ hne hd
  · intro hP
    have hne : (1 - ∏ i, x i) ≠ 0 := sub_ne_zero.mpr (Ne.symm hP)
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_smul, hm, smul_smul, inv_mul_cancel₀ hne, one_smul]

