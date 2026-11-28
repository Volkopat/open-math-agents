import OMAStatements.S_mo_236533

theorem OMA.solution : type_of% @OMA.S_mo_236533.main := by
  intro n m hn A _ hA
  have k : ∀ i j, (A * Matrix.of fun (_ : Fin m) (_ : Fin n) => (1 : ℝ) / n) i j = 1 / n := by
    simp [Matrix.mul_apply, ← Finset.sum_mul, hA]
  exact ⟨.of fun _ _ => 1 / n, by simp, by simp [hn.ne'], fun _ _ => by rw [k, k], fun _ _ => by rw [k, k]⟩
