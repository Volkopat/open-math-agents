import OMAStatements.S_oeis_a009388

open OMA.S_oeis_a009388 in
theorem OMA.solution : type_of% @OMA.S_oeis_a009388.main := by
  have r (x) (h : InSeq x) : x % 3 = 0 ∨ x % 3 = 2 := by
    induction h with
    | base => decide
    | @step a b _ _ ha hb =>
      have h := Nat.mul_mod a b 3
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] at h <;> omega
  exact ⟨r, fun n ⟨a, b, c⟩ => by have := r _ a; have := r _ b; have := r _ c; omega⟩
