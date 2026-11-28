import OMAStatements.S_mo_291544

theorem OMA.solution : type_of% @OMA.S_mo_291544.main := by
  intro A x
  suffices ∀ a b c : ℝ, a + b = 2 * c → a * b ≤ c ^ 2 by
    apply this
    simp [Matrix.det_fin_three, Matrix.smul_apply]
    ring
  intro a b c h
  nlinarith [sq_nonneg (a - b), congrArg (· ^ 2) h]
