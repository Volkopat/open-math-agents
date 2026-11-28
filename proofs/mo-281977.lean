import OMAStatements.S_mo_281977

open OMA.S_mo_281977
open Set Metric InnerProductSpace

private noncomputable def quadratic (ε t : ℝ) : ℝ := (t - 1 / 4) ^ 2 / 2 + ε

private theorem quadratic_poisson {ε : ℝ} (hε : 0 < ε) :
    PositivePoissonOnUnitBall ℝ (quadratic ε) := by
  have hs : ContDiff ℝ 2 (quadratic ε) := by
    unfold quadratic
    fun_prop
  have hd : deriv (quadratic ε) = fun t => t - 1 / 4 := by
    funext t
    have hsub : HasDerivAt (fun x : ℝ => x - 1 / 4) 1 t :=
      (hasDerivAt_id t).sub_const _
    have h := (((hsub.pow 2).div_const 2).add_const ε).deriv
    change deriv (quadratic ε) t = _ at h
    rw [h]
    ring
  refine ⟨hs.contDiffOn, fun t _ => ⟨?_, ?_⟩⟩
  · unfold quadratic
    positivity
  · rw [InnerProductSpace.laplacianWithin_univ,
        laplacian_eq_iteratedFDeriv_orthonormalBasis _ (OrthonormalBasis.singleton (Fin 1) ℝ)]
    simp [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Fin.prod_univ_two,
      iteratedDeriv_succ, hd]

theorem OMA.solution : type_of% @OMA.S_mo_281977.main := by
  constructor
  · intro E _ _ _ w hw
    let B : Set E := closedBall 0 (1 / 2)
    have hsub : B ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
    have hcompact : IsCompact B := isCompact_closedBall (0 : E) _
    have hnonempty : B.Nonempty := ⟨0, mem_closedBall_self (by norm_num)⟩
    obtain ⟨x, hx, hmin⟩ := hcompact.exists_isMinOn hnonempty
      (hw.1.continuousOn.mono hsub)
    have hxpos : 0 < w x := (hw.2 x (hsub hx)).1
    have h0pos : 0 < w 0 := (hw.2 0 (mem_ball_self (by norm_num))).1
    refine ⟨w x / w 0, div_pos hxpos h0pos, fun y hy => ?_⟩
    rw [div_mul_cancel₀ _ h0pos.ne']
    exact hmin (ball_subset_closedBall hy)
  · intro h
    obtain ⟨c, hc, huniform⟩ := h ℝ
    have hy : (1 / 4 : ℝ) ∈ ball (0 : ℝ) (1 / 2) := by
      norm_num [Metric.mem_ball, Real.dist_eq]
    have hb := huniform (quadratic (c / 64)) (quadratic_poisson (by positivity)) (1 / 4) hy
    unfold quadratic at hb
    nlinarith [sq_nonneg c]