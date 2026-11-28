import OMAStatements.S_mo_466218

-- Problem: A stochastic matrix $B = \lambda(\lambda I - A)^{-1}$ such that $B-B^2$ has a non-negative diagonal
-- Upstream: formal-conjectures statements/mo-466218.lean:0 (declaration OMA.S_mo_466218.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)

theorem OMA.solution : type_of% @OMA.S_mo_466218.main := by
  intro n A hoff hrow t ht i
  unfold OMA.S_mo_466218.resolvent
  by_cases hdet : IsUnit (t • (1 : Matrix (Fin n) (Fin n) ℝ) - A).det
  swap
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hdet]
    simp [sq]
  set B := t • (1 : Matrix (Fin n) (Fin n) ℝ) - A with hB
  set R := t • B⁻¹ with hR
  have hBR : B * R = t • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hR, Matrix.mul_smul, Matrix.mul_nonsing_inv _ hdet]
  have hRB : R * B = t • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hR, Matrix.smul_mul, Matrix.nonsing_inv_mul _ hdet]
  have hE : ∀ j k, t * R j k = t * (if j = k then 1 else 0) + ∑ l, A j l * (R l k - R j k) := by
    intro j k
    have h := congrFun (congrFun hBR j) k
    simp only [Matrix.mul_apply, hB, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul] at h
    have h2 : ∑ l, (t * (if j = l then 1 else 0) - A j l) * R l k
        = t * R j k - ∑ l, A j l * R l k := by
      simp [sub_mul, Finset.sum_sub_distrib]
    have h3 : ∑ l, A j l * (R l k - R j k) = ∑ l, A j l * R l k := by
      simp [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow]
    rw [h2] at h
    rw [h3]
    linarith
  have hnn : ∀ k j, 0 ≤ R j k := by
    intro k j
    obtain ⟨m, -, hm⟩ := Finset.exists_min_image Finset.univ (fun j => R j k) ⟨j, Finset.mem_univ j⟩
    have hs : 0 ≤ ∑ l, A m l * (R l k - R m k) := by
      apply Finset.sum_nonneg
      intro l _
      by_cases hl : m = l
      · subst hl; simp
      · exact mul_nonneg (hoff m l hl).le (sub_nonneg.2 (hm l (Finset.mem_univ l)))
    have h1 := hE m k
    have h4 : 0 ≤ t * (if m = k then (1 : ℝ) else 0) := by
      split_ifs <;> simp [ht.le]
    have h5 : 0 ≤ t * R m k := by linarith
    have h6 : 0 ≤ R m k := by
      by_contra hc
      have := mul_neg_of_pos_of_neg ht (not_le.1 hc)
      linarith
    exact le_trans h6 (hm j (Finset.mem_univ j))
  have hmax : ∀ k j, R j k ≤ R k k := by
    intro k j
    obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun j => R j k) ⟨j, Finset.mem_univ j⟩
    by_cases hmk : m = k
    · subst hmk; exact hm j (Finset.mem_univ j)
    · have hs : ∑ l, A m l * (R l k - R m k) ≤ 0 := by
        apply Finset.sum_nonpos
        intro l _
        by_cases hl : m = l
        · subst hl; simp
        · exact mul_nonpos_of_nonneg_of_nonpos (hoff m l hl).le
            (sub_nonpos.2 (hm l (Finset.mem_univ l)))
      have h1 := hE m k
      rw [if_neg hmk] at h1
      have h5 : t * R m k ≤ 0 := by linarith
      have h6 : R m k ≤ 0 := by
        by_contra hc
        have := mul_pos ht (not_le.1 hc)
        linarith
      exact le_trans (hm j (Finset.mem_univ j)) (le_trans h6 (hnn k k))
  have hsum : ∑ j, R i j = 1 := by
    have h : ∀ k, ∑ j, R i j * B j k = t * (if i = k then 1 else 0) := by
      intro k
      have h := congrFun (congrFun hRB i) k
      simpa [Matrix.mul_apply, Matrix.one_apply] using h
    have hBrow : ∀ j, ∑ k, B j k = t := by
      intro j
      simp [hB, Matrix.sub_apply, Matrix.one_apply, Finset.sum_sub_distrib, hrow]
    have h7 : ∑ k, ∑ j, R i j * B j k = t := by
      rw [Finset.sum_congr rfl (fun k _ => h k)]
      simp
    rw [Finset.sum_comm] at h7
    have h8 : ∑ j, ∑ k, R i j * B j k = t * ∑ j, R i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_sum, hBrow j, mul_comm]
    rw [h8] at h7
    have : t * (∑ j, R i j - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hfin : (R ^ 2) i i ≤ R i i := by
    rw [sq, Matrix.mul_apply]
    calc ∑ j, R i j * R j i ≤ ∑ j, R i j * R i i :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hmax i j) (hnn j i))
      _ = R i i := by rw [← Finset.sum_mul, hsum, one_mul]
  rw [Matrix.sub_apply]
  linarith
