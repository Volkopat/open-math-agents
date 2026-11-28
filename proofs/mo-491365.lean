import OMAStatements.S_mo_491365

section
open OMA.S_mo_491365

section
open Matrix

lemma ev_nonneg {n m : ℕ} (x : Fin (m+1) → E n) (j : Fin (m+1)) :
    0 ≤ (Matrix.isHermitian_gram ℝ x).eigenvalues j :=
  (Matrix.posSemidef_gram ℝ x).eigenvalues_nonneg j

lemma ev_sum {n m : ℕ} (x : Fin (m+1) → E n) :
    ∑ j, (Matrix.isHermitian_gram ℝ x).eigenvalues j = ∑ i, ‖x i‖^2 := by
  have h := (Matrix.isHermitian_gram ℝ x).trace_eq_sum_eigenvalues
  simp only [Matrix.trace, Matrix.diag, Matrix.gram_apply, RCLike.ofReal_real_eq_id, id] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_self_eq_norm_sq]

lemma largest_le {n m : ℕ} (x : Fin (m+1) → E n) : largest x ≤ ∑ i, ‖x i‖^2 := by
  rw [← ev_sum]
  refine Finset.sup'_le _ _ fun j _ => ?_
  exact Finset.single_le_sum (fun k _ => ev_nonneg x k) (Finset.mem_univ j)

lemma le_largest {n m : ℕ} (x : Fin (m+1) → E n) :
    (∑ i, ‖x i‖^2) ≤ (m+1) * largest x := by
  rw [← ev_sum]
  have : ∑ j, (Matrix.isHermitian_gram ℝ x).eigenvalues j ≤ ∑ _j : Fin (m+1), largest x :=
    Finset.sum_le_sum fun j _ => Finset.le_sup' _ (Finset.mem_univ j)
  simpa using this

lemma smallest_two {n : ℕ} (x : Fin 2 → E n) :
    (Matrix.gram ℝ x).det ≤ smallest x * (‖x 0‖^2 + ‖x 1‖^2) ∧
    smallest x * (‖x 0‖^2 + ‖x 1‖^2) ≤ 2 * (Matrix.gram ℝ x).det := by
  have hd := (Matrix.isHermitian_gram ℝ x).det_eq_prod_eigenvalues
  have ht := ev_sum x
  simp only [RCLike.ofReal_real_eq_id, id, Fin.prod_univ_two] at hd
  simp only [Fin.sum_univ_succ, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one] at ht
  rw [← ht, hd]
  set μ := (Matrix.isHermitian_gram ℝ x).eigenvalues
  have h0 := ev_nonneg x 0
  have h1 := ev_nonneg x 1
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin 2)) μ
  have hs : smallest x = μ j := hj
  have le0 : smallest x ≤ μ 0 := Finset.inf'_le _ (Finset.mem_univ _)
  have le1 : smallest x ≤ μ 1 := Finset.inf'_le _ (Finset.mem_univ _)
  fin_cases j
  · simp at hs
    rw [hs] at le1 ⊢
    constructor <;> nlinarith
  · simp at hs
    rw [hs] at le0 ⊢
    constructor <;> nlinarith
end

section
noncomputable def vv (s : ℝ) : Fin 2 → E 2 := ![!₂[(1:ℝ), 1], !₂[(1:ℝ), s]]

lemma change_vv (s : ℝ) : changeTwo (vv s) = vv (2*s) := by
  unfold changeTwo vv
  simp

lemma gram_det_vv (s : ℝ) : (Matrix.gram ℝ (vv s)).det = (s-1)^2 := by
  rw [Matrix.det_fin_two]
  simp [Matrix.gram_apply, vv, EuclideanSpace.norm_sq_eq, PiLp.inner_apply, Fin.sum_univ_two]
  ring

lemma norm_vv (s : ℝ) : ‖vv s 0‖^2 + ‖vv s 1‖^2 = 3 + s^2 := by
  simp [vv, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  ring

lemma indep_vv {s : ℝ} (h : s ≠ 1) : LinearIndependent ℝ (vv s) := by
  unfold vv
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h0 := congrArg (fun v : E 2 => v 0) hab
  have h1 := congrArg (fun v : E 2 => v 1) hab
  simp at h0 h1
  have hb : b * (s - 1) = 0 := by linarith
  have hb' : b = 0 := by
    rcases mul_eq_zero.mp hb with h' | h'
    · exact h'
    · exact absurd (by linarith) h
  subst hb'
  exact ⟨by linarith, rfl⟩

lemma sm_vv (s : ℝ) : (s-1)^2 ≤ smallest (vv s) * (3 + s^2) ∧
    smallest (vv s) * (3 + s^2) ≤ 2 * (s-1)^2 := by
  have := smallest_two (vv s)
  rw [gram_det_vv, norm_vv] at this
  exact this
end

section
lemma sm_nonneg {n : ℕ} (x : Fin 2 → E n) : 0 ≤ smallest x :=
  (Finset.le_inf' _ _ fun j _ => ev_nonneg x j)

lemma abs_part1 (m : ℕ) (M N L L' t t' : ℝ) (hL : L ≤ t) (hL' : L' ≤ t')
    (ht : t ≤ (m+1) * L) (ht' : t' ≤ (m+1) * L') (h1 : t' ≤ M^2 * t) (h2 : t ≤ N^2 * t')
    (ht0 : 0 ≤ t) (ht0' : 0 ≤ t') :
    1 / (((m:ℝ)+1) * (M^2+1)) * L' ≤ L ∧ L ≤ (((m:ℝ)+1) * (N^2+1)) * L' := by
  have hm : (0:ℝ) < (m:ℝ)+1 := by positivity
  have hL0 : 0 ≤ L := by nlinarith
  have hL0' : 0 ≤ L' := by nlinarith
  constructor
  · rw [one_div, inv_mul_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hL0 hm.le, sq_nonneg M, mul_nonneg hm.le hL0]
  · nlinarith [mul_nonneg hL0' hm.le, sq_nonneg N, mul_nonneg hm.le hL0']

lemma part1 (n m : ℕ) (T : Fin (m+1) → E n ≃L[ℝ] E n) : ∃ c : ℝ, 0<c ∧ ∃ C : ℝ, 0<C ∧
      ∀ x : Fin (m+1) → E n, c*largest (fun i => T i (x i)) ≤ largest x ∧
        largest x ≤ C*largest (fun i => T i (x i)) := by
  set M : ℝ := ∑ i, ‖((T i : E n →L[ℝ] E n))‖ with hM
  set N : ℝ := ∑ i, ‖(((T i).symm : E n →L[ℝ] E n))‖ with hN
  have hMi : ∀ i, ‖((T i : E n →L[ℝ] E n))‖ ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => ‖((T i : E n →L[ℝ] E n))‖) (fun k _ => norm_nonneg _) (Finset.mem_univ i)
  have hNi : ∀ i, ‖(((T i).symm : E n →L[ℝ] E n))‖ ≤ N := fun i =>
    Finset.single_le_sum (f := fun i => ‖(((T i).symm : E n →L[ℝ] E n))‖) (fun k _ => norm_nonneg _) (Finset.mem_univ i)
  refine ⟨1 / (((m:ℝ)+1) * (M^2+1)), by positivity, ((m:ℝ)+1) * (N^2+1), by positivity, fun x => ?_⟩
  have hfw : ∀ i, ‖T i (x i)‖ ≤ M * ‖x i‖ := fun i =>
    ((T i : E n →L[ℝ] E n).le_opNorm (x i)).trans (by gcongr; exact hMi i)
  have hbw : ∀ i, ‖x i‖ ≤ N * ‖T i (x i)‖ := fun i => by
    have := ((T i).symm : E n →L[ℝ] E n).le_opNorm (T i (x i))
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at this
    exact this.trans (by gcongr; exact hNi i)
  have h1 : ∑ i, ‖T i (x i)‖^2 ≤ M^2 * ∑ i, ‖x i‖^2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc ‖T i (x i)‖^2 ≤ (M * ‖x i‖)^2 := by gcongr; exact hfw i
      _ = M^2 * ‖x i‖^2 := by ring
  have h2 : ∑ i, ‖x i‖^2 ≤ N^2 * ∑ i, ‖T i (x i)‖^2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc ‖x i‖^2 ≤ (N * ‖T i (x i)‖)^2 := by gcongr; exact hbw i
      _ = N^2 * ‖T i (x i)‖^2 := by ring
  exact abs_part1 m M N _ _ _ _ (largest_le x) (largest_le (fun i => T i (x i)))
    (le_largest x) (le_largest (fun i => T i (x i))) h1 h2
    (Finset.sum_nonneg fun i _ => by positivity) (Finset.sum_nonneg fun i _ => by positivity)

lemma part2 (K : ℝ) (hK : 0 < K) : ∃ x : Fin 2 → E 2, LinearIndependent ℝ x ∧
      LinearIndependent ℝ (changeTwo x) ∧
      K*(Matrix.gram ℝ x).det < (Matrix.gram ℝ (changeTwo x)).det ∧
      K*smallest x < smallest (changeTwo x) := by
  set ε : ℝ := 1 / (8 * (K+2)) with hε
  have hε0 : 0 < ε := by positivity
  have hKε : K * ε ≤ 1/8 := by
    rw [hε, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hε1 : ε ≤ 1/16 := by
    rw [hε, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  refine ⟨vv (1+ε), indep_vv (by linarith), ?_, ?_, ?_⟩
  · rw [change_vv]; exact indep_vv (by linarith)
  · rw [change_vv, gram_det_vv, gram_det_vv]; nlinarith
  · rw [change_vv]
    have ha := sm_vv (1+ε)
    have hb := sm_vv (2*(1+ε))
    have ha0 := sm_nonneg (vv (1+ε))
    have hb0 := sm_nonneg (vv (2*(1+ε)))
    set a := smallest (vv (1+ε))
    set b := smallest (vv (2*(1+ε)))
    have h3 : 3 * a ≤ 2 * ε^2 := by nlinarith [mul_nonneg ha0 (sq_nonneg (1+ε))]
    have h4 : 1 ≤ 19 * b := by nlinarith [mul_nonneg hb0 (show 0 ≤ 16 - (2*(1+ε))^2 by nlinarith)]
    nlinarith [mul_nonneg hK.le (sq_nonneg ε), mul_le_mul_of_nonneg_right hKε hε0.le]

lemma part3 (K : ℝ) (hK : 0 < K) : ∃ x : Fin 2 → E 2, LinearIndependent ℝ x ∧
      LinearIndependent ℝ (changeTwo x) ∧
      K*(Matrix.gram ℝ (changeTwo x)).det < (Matrix.gram ℝ x).det ∧
      K*smallest (changeTwo x) < smallest x := by
  set ε : ℝ := 1 / (64 * (K+2)) with hε
  have hε0 : 0 < ε := by positivity
  have hKε : K * ε ≤ 1/64 := by
    rw [hε, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hε1 : ε ≤ 1/128 := by
    rw [hε, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  refine ⟨vv (1/2+ε), indep_vv (by linarith), ?_, ?_, ?_⟩
  · rw [change_vv]; exact indep_vv (by linarith)
  · rw [change_vv, gram_det_vv, gram_det_vv]; nlinarith
  · rw [change_vv]
    have ha := sm_vv (1/2+ε)
    have hb := sm_vv (2*(1/2+ε))
    have ha0 := sm_nonneg (vv (1/2+ε))
    have hb0 := sm_nonneg (vv (2*(1/2+ε)))
    set a := smallest (vv (1/2+ε))
    set b := smallest (vv (2*(1/2+ε)))
    have h3 : 3 * b ≤ 8 * ε^2 := by nlinarith [mul_nonneg hb0 (sq_nonneg (2*(1/2+ε)))]
    have h4 : 1 ≤ 20 * a := by nlinarith [mul_nonneg ha0 (show 0 ≤ 1 - (1/2+ε)^2 by nlinarith)]
    nlinarith [mul_nonneg hK.le (sq_nonneg ε), mul_le_mul_of_nonneg_right hKε hε0.le]
end
end

theorem OMA.solution : type_of% @OMA.S_mo_491365.main := by
  exact ⟨fun n m T => part1 n m T, fun K hK => part2 K hK, fun K hK => part3 K hK⟩
