import OMAStatements.S_oeis_a267884

open PowerSeries
open OMA.S_oeis_a267884

namespace OMA.P_a267884

theorem s1 (x : ℤ) : state 233 1 x = decide (x < -1 ∨ 1 < x) := by
  show step 233 (fun x => decide (x = 0)) x = _
  simp only [step]
  rcases (by omega : x < -1 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ 1 < x) with h|h|h|h|h <;>
    simp (disch := omega) only [decide_eq_true, decide_eq_false] <;> rfl

theorem s2 (x : ℤ) : state 233 2 x = decide (x ≠ -1 ∧ x ≠ 1) := by
  show step 233 (state 233 1) x = _
  simp only [step, s1]
  rcases (by omega : x < -2 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ 2 < x) with
    h|h|h|h|h|h|h <;>
    simp (disch := omega) only [decide_eq_true, decide_eq_false] <;> rfl

theorem s3 (x : ℤ) : state 233 3 x = decide (x ≠ 0) := by
  show step 233 (state 233 2) x = _
  simp only [step, s2]
  rcases (by omega : x < -2 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ 2 < x) with
    h|h|h|h|h|h|h <;>
    simp (disch := omega) only [decide_eq_true, decide_eq_false] <;> rfl

theorem s4 (n : ℕ) (x : ℤ) : state 233 (n + 4) x = true := by
  induction n generalizing x with
  | zero =>
    show step 233 (state 233 3) x = _
    simp only [step, s3]
    rcases (by omega : x < -1 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ 1 < x) with h|h|h|h|h <;>
      simp (disch := omega) only [decide_eq_true, decide_eq_false] <;> rfl
  | succ n ih =>
    show step 233 (state 233 (n + 4)) x = _
    simp only [step, ih]
    rfl

theorem off4 (n : ℕ) : offCount (state 233 (n + 4)) (n + 4) = 0 := by
  unfold offCount
  simp [s4]

theorem a_succ (n : ℕ) (h : 3 ≤ n) : a (n + 1) = a n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [a, Finset.sum_range_succ, show 3 + m + 1 = m + 4 by omega, off4, add_zero, a,
    show 3 + m + 1 = m + 4 by omega]

theorem a0 : a 0 = 0 := by decide +kernel
theorem a1 : a 1 = 3 := by decide +kernel
theorem a2 : a 2 = 5 := by decide +kernel
theorem a3 : a 3 = 6 := by decide +kernel

theorem a_eq (n : ℕ) (h : 3 ≤ n) : a n = 6 := by
  induction n, h using Nat.le_induction with
  | base => exact a3
  | succ n hn ih => rw [a_succ n hn, ih]

end OMA.P_a267884

open OMA.P_a267884

theorem OMA.solution : type_of% @OMA.S_oeis_a267884.main := by
  have h6 : ∀ n, 2 < n → a n = 6 := fun n h => a_eq n h
  refine ⟨h6, ?_, ?_⟩
  · intro n hn
    rw [h6 n (by omega), h6 (n - 1) (by omega)]
  · rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    have e : (3 + 2 * X + X ^ 2 : ℚ⟦X⟧) = C (3 : ℚ) + C (2 : ℚ) * X + X ^ 2 := by
      simp [map_ofNat]
    rw [e]
    ext n
    rw [mul_sub, mul_one, map_sub]
    rcases n with _ | n
    · simp [A, a0]
    · rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_succ_X_mul]
      simp only [A, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
      rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n) with h|h|h|h
      · subst h; simp [a0, a1]
      · subst h; simp [a1, a2]; norm_num
      · subst h; simp [a2, a3]; norm_num
      · rw [a_eq (n + 1) (by omega), a_eq n h]
        simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
          if_false]
        norm_num

