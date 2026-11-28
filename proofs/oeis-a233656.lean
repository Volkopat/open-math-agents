import OMAStatements.S_oeis_a233656

/-! After checking the first period, the recurrence propagates equality of the last digits. -/

open OMA.S_oeis_a233656

theorem OMA.solution : type_of% @OMA.S_oeis_a233656.main := by
  have period (n : ℕ) : a (n + 20) % 10 = a n % 10 := by
    induction n with
    | zero => decide
    | succ n ih =>
      change a ((n + 20) + 1) % 10 = a (n + 1) % 10
      simp only [a, Nat.cast_add, Nat.cast_ofNat]
      omega
  refine ⟨?_, by decide⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 20
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 20 := ⟨n - 20, by omega⟩
      rw [period, ih m (by omega), Nat.add_mod_right]
