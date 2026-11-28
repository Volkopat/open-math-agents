import OMAStatements.S_oeis_a267923

namespace OMA.S_oeis_a267923

open PowerSeries




lemma rule245 (l c x : Bool) : rule 245 l c x = (l || !x) := by
  cases l <;> cases c <;> cases x <;> decide

lemma pattern (n : ℕ) (hn : 1 ≤ n) (i : ℤ) : row 245 n i = true ↔ i ≠ (n : ℤ) - 2 := by
  induction n, hn using Nat.le_induction generalizing i with
  | base =>
    simp only [row, rule245, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_true_eq, decide_eq_false_iff_not]
    push_cast
    omega
  | succ n hn ih =>
    have e1 := ih (i - 1)
    have e2 := ih (i + 1)
    simp only [row, rule245]
    rcases hb1 : row 245 n (i - 1) <;> rcases hb2 : row 245 n (i + 1) <;>
      simp_all <;> omega

lemma a_closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℤ) = ∑ k ∈ Finset.range (2 * n + 1), (10 : ℤ) ^ k - 100 := by
  have hsplit : ∀ k ∈ Finset.range (2 * n + 1),
      ((if row 245 n ((n : ℤ) - k) then 10 ^ k else 0 : ℕ) : ℤ) =
        (10 : ℤ) ^ k - (if k = 2 then 100 else 0) := by
    intro k _
    by_cases hk : k = 2
    · subst hk
      have : row 245 n ((n : ℤ) - (2 : ℕ)) = false := by
        rcases h : row 245 n ((n : ℤ) - (2 : ℕ)) with _ | _
        · rfl
        · have := (pattern n hn _).1 h; push_cast at this; omega
      rw [this]; simp
    · have : row 245 n ((n : ℤ) - k) = true := (pattern n hn _).2 (by omega)
      rw [this]; simp [hk]
  rw [a, Nat.cast_sum, Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' (Finset.range (2 * n + 1)) 2, if_pos (by simp; omega)]

lemma nine_a (n : ℕ) (hn : 1 ≤ n) : 9 * (a n : ℤ) = 10 * 100 ^ n - 901 := by
  rw [a_closed n hn, mul_sub]
  have h : ∀ m : ℕ, 9 * ∑ k ∈ Finset.range m, (10 : ℤ) ^ k = 10 ^ m - 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
  rw [h, pow_succ, pow_mul]
  norm_num
  ring

/-- Barker's recurrence a(n) = 101 a(n-1) - 100 a(n-2), n > 2. -/
theorem recurrence (n : ℕ) (hn : 2 < n) :
    (a n : ℤ) = 101 * a (n - 1) - 100 * a (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
  have h0 := nine_a (m + 3) (by omega)
  have h1 := nine_a (m + 2) (by omega)
  have h2 := nine_a (m + 1) (by omega)
  have : 9 * (a (m + 3) : ℤ) = 9 * (101 * a (m + 2) - 100 * a (m + 1)) := by
    rw [h0, mul_sub, mul_left_comm, h1, mul_left_comm, h2]; ring
  linarith

lemma a0 : a 0 = 1 := by decide

/-- Control: the definition reproduces the listed a(3) and a(4) directly. -/
example : a 3 = 1111011 ∧ a 4 = 111111011 := by decide +kernel
lemma a1 : a 1 = 11 := by
  have := nine_a 1 le_rfl; norm_num at this; omega
lemma a2 : a 2 = 11011 := by
  have := nine_a 2 (by norm_num); norm_num at this; omega

/-- Barker's generating function, as an identity of formal power series. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 100 * X)) =
    1 - 90 * X + 10000 * X ^ 2 := by
  have hD : ((1 - X) * (1 - 100 * X) : ℤ⟦X⟧) = 1 - (C 101) * X ^ 1 + (C 100) * X ^ 2 := by
    simp only [map_ofNat, pow_one]; ring
  have hN : (1 - 90 * X + 10000 * X ^ 2 : ℤ⟦X⟧) = C 1 - C 90 * X ^ 1 + C 10000 * X ^ 2 := by
    simp only [map_ofNat, map_one, pow_one]
  rw [hD, hN]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, mul_comm (C _), ← mul_assoc,
    coeff_mul_X_pow', coeff_mul_C, coeff_mk, coeff_C_mul, coeff_X_pow, coeff_C]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp [a0, a1, a2]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have := recurrence (m + 3) (by omega)
    rw [if_pos (show 1 ≤ m + 3 by omega), if_pos (show 2 ≤ m + 3 by omega),
      show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega] at *
    rw [if_neg (show ¬ (m + 3 = 0) by omega), if_neg (show ¬ (m + 3 = 1) by omega),
      if_neg (show ¬ (m + 3 = 2) by omega)]
    linarith

end OMA.S_oeis_a267923

theorem OMA.solution : type_of% @OMA.S_oeis_a267923.main :=
  ⟨OMA.S_oeis_a267923.recurrence, OMA.S_oeis_a267923.gf⟩
