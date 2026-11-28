import OMAStatements.S_oeis_a316316

open OMA.S_oeis_a316316 in
theorem OMA.solution : type_of% @OMA.S_oeis_a316316.main := by
  have h : ∀ k, window (k + 12) =
      let w := window k; ⟨w.a + 40, w.b + 40, w.c + 40, w.d + 40, w.e + 40, w.f + 40⟩ := by
    intro k
    induction k with
    | zero => decide
    | succ k ih => show step _ = _; rw [ih]; simp [window, step]; try ring
  rintro (_ | k) _
  · omega
  · show (window (k + 12)).a = _; rw [h]; rfl
