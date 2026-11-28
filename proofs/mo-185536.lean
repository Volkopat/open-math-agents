import OMAStatements.S_mo_185536

-- Yes: on self-adjoint elements the continuous functional calculus logarithm inverts exp
-- (`CFC.log_exp`), so exp x = exp y forces x = y.

theorem OMA.solution : type_of% @OMA.S_mo_185536.main := by
  intro A _ x y hx hy hne heq
  apply hne
  rw [← CFC.log_exp x hx, ← CFC.log_exp y hy, heq]
