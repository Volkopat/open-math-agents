import OMAStatements.S_mo_462279
import Mathlib
/-! Adapt @caa1982's coercivity proof in pending #28167. Use strict concavity's
standard uniqueness theorem for the final maximizer. -/
open OMA.S_mo_462279

lemma coercive (f : ℝ × ℝ → ℝ) (m : ℝ) (hm : 0 < m) (hf : StrongConcaveOn Set.univ m f)
    (M : ℝ) (hM : ∀ y : ℝ × ℝ, ‖y‖ ≤ 1 → f y ≤ M) (x : ℝ × ℝ) (hx : 1 ≤ ‖x‖) :
    f x ≤ ‖x‖ * (M - f 0) + f 0 - m / 2 * (‖x‖ - 1) * ‖x‖ := by
  set R := ‖x‖ with hR
  have hR0 : 0 < R := by linarith
  have ha : 0 ≤ 1 - 1 / R := by
    rw [sub_nonneg, div_le_one hR0]; exact hx
  have hb : 0 ≤ 1 / R := by positivity
  have hab : (1 - 1 / R) + 1 / R = 1 := by ring
  have h := hf.2 (Set.mem_univ (0 : ℝ × ℝ)) (Set.mem_univ x) ha hb hab
  simp only [smul_zero, zero_add, zero_sub, norm_neg, smul_eq_mul] at h
  have hnorm : ‖(1 / R) • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb, ← hR]
    rw [div_mul_cancel₀ _ hR0.ne']
  have h2 := hM _ hnorm
  have key : (1 - 1 / R) * f 0 + 1 / R * f x + (1 - 1 / R) * (1 / R) * (m / 2 * R ^ 2) ≤ M := by
    linarith
  have e : (1 - 1 / R) * (1 / R) * (m / 2 * R ^ 2) = m / 2 * (R - 1) := by
    field_simp
  rw [e] at key
  have key2 : R * ((1 - 1 / R) * f 0 + 1 / R * f x + m / 2 * (R - 1)) ≤ R * M :=
    mul_le_mul_of_nonneg_left key hR0.le
  have e2 : R * ((1 - 1 / R) * f 0 + 1 / R * f x + m / 2 * (R - 1)) =
      (R - 1) * f 0 + f x + m / 2 * (R - 1) * R := by
    field_simp
  rw [e2] at key2
  nlinarith

theorem OMA.solution : type_of% @OMA.S_mo_462279.main := by
  intro f m hm hf _ _
  have hcont : Continuous f := by
    have hc := (hf.concaveOn (fun r => by positivity)).continuousOn isOpen_univ
    exact continuousOn_univ.mp hc
  -- bound on the unit ball
  obtain ⟨y1, -, hy1⟩ := (isCompact_closedBall (0 : ℝ × ℝ) 1).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩ hcont.continuousOn
  set M := f y1 with hMdef
  have hM : ∀ y : ℝ × ℝ, ‖y‖ ≤ 1 → f y ≤ M := by
    intro y hy
    exact hy1 (by rw [Metric.mem_closedBall, dist_zero_right]; exact hy)
  have hM0 : f 0 ≤ M := hM 0 (by simp)
  -- radius beyond which f is below f 0
  set R0 : ℝ := 2 + 4 * (M - f 0) / m with hR0
  have hR0pos : 1 ≤ R0 := by
    have : 0 ≤ 4 * (M - f 0) / m := by
      apply div_nonneg _ hm.le; linarith
    linarith
  have hout : ∀ x : ℝ × ℝ, R0 < ‖x‖ → f x < f 0 := by
    intro x hx
    have h1 := coercive f m hm hf M hM x (by linarith)
    set R := ‖x‖
    have hRpos : 0 < R := by linarith
    -- m/2 (R - 1) > M - f 0
    have h3 : M - f 0 < m / 2 * (R - 1) := by
      have : 4 * (M - f 0) / m < R - 2 := by linarith
      rw [div_lt_iff₀ hm] at this
      nlinarith
    nlinarith
  obtain ⟨p, -, hp⟩ := (isCompact_closedBall (0 : ℝ × ℝ) R0).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self (by linarith)⟩ hcont.continuousOn
  have hp0 : f 0 ≤ f p := hp (Metric.mem_closedBall_self (by linarith))
  have hmax : ∀ q, f q ≤ f p := by
    intro q
    by_cases hq : ‖q‖ ≤ R0
    · exact hp (by rw [Metric.mem_closedBall, dist_zero_right]; exact hq)
    · rw [not_le] at hq
      exact (hout q hq).le.trans hp0
  refine ⟨p, hmax, fun q hq => ?_⟩
  exact (hf.strictConcaveOn hm).eq_of_isMaxOn (fun _ _ => hq _)
    (fun _ _ => hmax _) (Set.mem_univ _) (Set.mem_univ _)
