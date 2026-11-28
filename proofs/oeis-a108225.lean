import OMAStatements.S_oeis_a108225

open OMA.S_oeis_a108225 in
theorem OMA.solution : type_of% @OMA.S_oeis_a108225.main := by
  have key (n : ℕ) : a (n + 1) = b (n + 1) + 1 ∧ a (n + 1 + 1) = b (n + 1 + 1) + 1 := by
    induction n with
    | zero => decide
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [a, ih.1, ih.2, show b (n + 1 + 2) = b (n + 1 + 1) * (b (n + 1 + 1) + 1) / 2 + 1 from rfl,
        show b (n + 1 + 1) = b (n + 1) * (b (n + 1) + 1) / 2 + 1 from rfl]
      generalize b (n + 1) = x
      obtain ⟨k, hk⟩ := Nat.even_mul_succ_self x
      rw [show x * (x + 1) / 2 = k by omega]
      have : x + 1 ≤ k + 1 + 1 := by nlinarith
      have h := congrArg (Nat.cast : ℕ → ℤ) hk
      push_cast at h
      rw [show (k + 1 + 1 + (x + 1)) * (k + 1 + 1 - (x + 1) + 1) = (k + 1) * (k + 1 + 1) + 4 by
        zify [this]; linear_combination -h]
      generalize (k + 1) * (k + 1 + 1) = P
      omega
  rintro (_ | n) h
  · omega
  · exact (key n).1
