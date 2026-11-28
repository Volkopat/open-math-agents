import OMAStatements.S_oeis_a267623

section Aux
open OMA.S_oeis_a267623

lemma rule_eq (l c r : Bool) : rule l c r = (!c || r) := by
  cases l <;> cases c <;> cases r <;> decide

lemma state_succ (n : ℕ) (x : ℤ) : state (n + 1) x = (!state n x || state n (x + 1)) := by
  simp only [state, step, rule_eq]

lemma state_ge (n : ℕ) : ∀ x, state (n + 1) x = decide (x ≠ -(n : ℤ)) := by
  induction n with
  | zero =>
    intro x
    rw [state_succ]
    simp only [state, initial]
    by_cases h : x = 0 <;> by_cases h2 : x + 1 = 0 <;> simp [h, h2]
  | succ n ih =>
    intro x
    rw [state_succ, ih, ih]
    by_cases h : x = -(n : ℤ) <;> by_cases h2 : x + 1 = -(n : ℤ) <;> simp [h, h2] <;> omega

lemma a_val (n : ℕ) (hn : 2 ≤ n) : a n = 10 * a (n - 1) + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h : state (m + 2) 0 = true := by
    rw [state_ge (m + 1)]; simp; omega
  show column (m + 2 + 1) = 10 * column (m + 1 + 1) + 1
  rw [column]
  simp [bit, h]

end Aux

open OMA.S_oeis_a267623 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267623.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have := a_val (m + 3) (by omega)
    have := a_val (m + 2) (by omega)
    simp_all
    omega
  · have a0 : a 0 = 1 := by decide
    have a1 : a 1 = 10 := by decide
    have a2 : a 2 = 101 := by decide
    rw [show series * ((1 - X) * (1 - 10 * X)) = series - C 11 * (series * X ^ 1) + C 10 * (series * X ^ 2) by simp; ring]
    ext (_ | _ | _ | m) <;> simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', series, coeff_mk,
      coeff_one, coeff_X_pow] <;> simp [a0, a1, a2, coeff_X]
    obtain h1 : a (m + 1 + 1 + 1) = 10 * a (m + 1 + 1) + 1 := a_val (m + 3) (by omega)
    obtain h2 : a (m + 1 + 1) = 10 * a (m + 1) + 1 := a_val (m + 2) (by omega)
    omega
