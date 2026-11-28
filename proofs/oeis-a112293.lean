import OMAStatements.S_oeis_a112293

theorem OMA.aux_df (m : ℕ) :
    Nat.doubleFactorial (2 * (m + 1) - 1) = (2 * m + 1) * Nat.doubleFactorial (2 * m - 1) := by
  cases m with
  | zero => rfl
  | succ k =>
    have h1 : 2 * (k + 1 + 1) - 1 = (2 * k + 1) + 2 := by omega
    have h2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [h1, h2, Nat.doubleFactorial_add_two]
    ring

theorem OMA.aux_succ (m : ℕ) :
    OMA.S_oeis_a112293.a (m + 1) = (2 * (m : ℚ) + 1) * OMA.S_oeis_a112293.a m + 1 := by
  unfold OMA.S_oeis_a112293.a
  rw [Finset.sum_range_succ _ (m + 1)]
  have hne : (Nat.doubleFactorial (2 * (m + 1) - 1) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos _).ne'
  rw [div_self hne, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [OMA.aux_df m]
  push_cast
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a112293.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2]
  have h1 : OMA.S_oeis_a112293.a (m + 2) =
      (2 * ((m + 1 : ℕ) : ℚ) + 1) * OMA.S_oeis_a112293.a (m + 1) + 1 := OMA.aux_succ (m + 1)
  have h2 := OMA.aux_succ m
  push_cast at h1 ⊢
  linear_combination h1 - h2
