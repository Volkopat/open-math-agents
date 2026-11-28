import OMAStatements.S_mo_103292

-- Problem: Two Concepts of Monotonicity
-- Upstream: formal-conjectures statements/mo-103292.lean:0 (declaration OMA.S_mo_103292.main)
-- Credit: @artnoage (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Example: F x = (2 - ‖x‖^2) • x on the closed unit ball of the plane.
-- Pseudomonotone with constant 1: if ⟪F x, y - x⟫ ≥ 0 then ⟪x, y - x⟫ ≥ 0, hence
-- ⟪y, y - x⟫ ≥ ‖y - x‖^2, and 2 - ‖y‖^2 ≥ 1 on the ball.
-- Not strongly monotone: along a ray, t ↦ (2 - t^2) t decreases between 9/10 and 1.

open scoped RealInnerProductSpace

theorem OMA.solution : type_of% @OMA.S_mo_103292.main := by
  refine ⟨2, le_refl 2, Metric.closedBall 0 1, Metric.isClosed_closedBall,
    convex_closedBall 0 1, ?_, fun x => (2 - ‖x‖ ^ 2) • x, ?_, ?_⟩
  · refine ⟨0, ?_⟩
    rw [interior_closedBall _ one_ne_zero]
    exact Metric.mem_ball_self one_pos
  · refine ⟨1, one_pos, ?_⟩
    intro x hx y hy h
    have hx1 : ‖x‖ ≤ 1 := by simpa using hx
    have hy1 : ‖y‖ ≤ 1 := by simpa using hy
    have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
    have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
    have hxs : ‖x‖ ^ 2 ≤ 1 := by nlinarith
    have hys : ‖y‖ ^ 2 ≤ 1 := by nlinarith
    simp only [real_inner_smul_left] at h ⊢
    have hxy : 0 ≤ ⟪x, y - x⟫ := by
      by_contra hneg
      push_neg at hneg
      nlinarith
    have hsplit : ⟪y, y - x⟫ = ⟪x, y - x⟫ + ‖y - x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq (y - x), ← inner_add_left]
      congr 1
      abel
    have hd : 0 ≤ ‖y - x‖ ^ 2 := by positivity
    rw [hsplit]
    nlinarith
  · rintro ⟨γ, hγ, hmono⟩
    obtain ⟨e, he⟩ : ∃ e : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 :=
      ⟨EuclideanSpace.single 0 1, by simp⟩
    have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
    have hxK : ((9 / 10 : ℝ) • e) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      simp [norm_smul, he]
      norm_num
    have heK : e ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      simp [he]
    have h := hmono _ hxK _ heK
    have hn : ‖(9 / 10 : ℝ) • e‖ = 9 / 10 := by
      rw [norm_smul, he]; norm_num
    have hdiff : e - (9 / 10 : ℝ) • e = (1 / 10 : ℝ) • e := by
      rw [← sub_eq_zero]
      module
    have hF : (2 - ‖e‖ ^ 2) • e - (2 - ‖(9 / 10 : ℝ) • e‖ ^ 2) • ((9 / 10 : ℝ) • e)
        = (-(71 / 1000) : ℝ) • e := by
      rw [hn, he, ← sub_eq_zero]
      module
    simp only at h
    rw [hF, hdiff, real_inner_smul_left, real_inner_smul_right, hee, norm_smul, he] at h
    norm_num at h
    nlinarith
