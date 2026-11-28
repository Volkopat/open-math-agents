import OMAStatements.S_oeis_a112701

open OMA.S_oeis_a112701

private theorem catalan_ratio (n : ℕ) :
    ((n : ℤ) + 2) * (catalan (n + 1) : ℤ) =
      2 * (2 * (n : ℤ) + 1) * (catalan n : ℤ) := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n + 1),
    ← succ_mul_catalan_eq_centralBinom n] at h
  have h' : ((n : ℤ) + 1) * (((n : ℤ) + 1 + 1) * (catalan (n + 1) : ℤ)) =
      2 * (2 * (n : ℤ) + 1) * (((n : ℤ) + 1) * (catalan n : ℤ)) := by
    exact_mod_cast h
  apply mul_left_cancel₀ (a := (n : ℤ) + 1) (by positivity)
  linear_combination h'

private theorem sum_succ (n : ℕ) :
    (a (n + 1) : ℤ) = (a n : ℤ) + (catalan (n + 1) : ℤ) * 7 ^ (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ, Nat.cast_add]
  push_cast
  rfl

/-- The recurrence follows by subtracting adjacent partial sums. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a112701.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  have h₁ : k + 2 - 1 = k + 1 := by omega
  have h₂ : k + 2 - 2 = k := by omega
  rw [h₁, h₂, sum_succ (k + 1), sum_succ k, pow_succ (7 : ℤ) (k + 1)]
  push_cast
  have h := catalan_ratio (k + 1)
  push_cast at h
  linear_combination 7 * 7 ^ (k + 1) * h
