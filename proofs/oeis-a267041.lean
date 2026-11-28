import OMAStatements.S_oeis_a267041

namespace OMA.S_oeis_a267041




/-- Rule 91 is NAND on the neighbours of a dead cell and XOR on those of a live cell. -/
private lemma rule_truth_table (l c r : Bool) :
    rule l c r = ((!c && !(l && r)) || (c && ((l && !r) || (!l && r)))) := by
  cases l <;> cases c <;> cases r <;> decide

lemma s1 (i : ℤ) : state 1 i = decide (i ≠ 0) := by
  change rule (decide (i - 1 = 0)) (decide (i = 0)) (decide (i + 1 = 0)) = _
  simp only [rule_truth_table, ← decide_not, ← Bool.decide_and, ← Bool.decide_or, decide_eq_decide]
  omega

lemma s2 (i : ℤ) : state 2 i = decide (i = 1 ∨ i = -1) := by
  change rule (state 1 (i - 1)) (state 1 i) (state 1 (i + 1)) = _
  simp only [s1, rule_truth_table, ← decide_not, ← Bool.decide_and, ← Bool.decide_or, decide_eq_decide]
  omega

lemma s3 (i : ℤ) : state 3 i = decide (i < -1 ∨ 1 < i) := by
  change rule (state 2 (i - 1)) (state 2 i) (state 2 (i + 1)) = _
  simp only [s2, rule_truth_table, ← decide_not, ← Bool.decide_and, ← Bool.decide_or, decide_eq_decide]
  omega

/-- Odd row (OFF exactly at `-1..1`) to even row (ON exactly at `-2..2`). -/
lemma stepOE (i : ℤ) :
    rule (decide (i - 1 < -1 ∨ 1 < i - 1)) (decide (i < -1 ∨ 1 < i)) (decide (i + 1 < -1 ∨ 1 < i + 1))
      = decide (-2 ≤ i ∧ i ≤ 2) := by
  simp only [rule_truth_table, ← decide_not, ← Bool.decide_and, ← Bool.decide_or, decide_eq_decide]
  omega

/-- Even row (ON exactly at `-2..2`) to odd row (OFF exactly at `-1..1`). -/
lemma stepEO (i : ℤ) :
    rule (decide (-2 ≤ i - 1 ∧ i - 1 ≤ 2)) (decide (-2 ≤ i ∧ i ≤ 2)) (decide (-2 ≤ i + 1 ∧ i + 1 ≤ 2))
      = decide (i < -1 ∨ 1 < i) := by
  simp only [rule_truth_table, ← decide_not, ← Bool.decide_and, ← Bool.decide_or, decide_eq_decide]
  omega

/-- The rows from time 3 on. -/
lemma pattern (t : ℕ) (ht : 3 ≤ t) (i : ℤ) :
    state t i = if t % 2 = 1 then decide (i < -1 ∨ 1 < i) else decide (-2 ≤ i ∧ i ≤ 2) := by
  induction t, ht using Nat.le_induction generalizing i with
  | base => rw [s3]; rfl
  | succ t _ ih =>
    show rule (state t (i - 1)) (state t i) (state t (i + 1)) = _
    rw [ih, ih, ih]
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), stepEO]
    · rw [if_pos h, if_pos h, if_pos h, if_neg (by omega), stepOE]

/-- Rewrite `a n` as a sum over the exponent `m = 2n - k`. -/
lemma a_reflect (n : ℕ) : a n =
    ∑ m ∈ Finset.range (2 * n + 1), if state n ((n : ℤ) - m) then 10 ^ m else 0 := by
  unfold a
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_range.mp hm
  rw [show 2 * n + 1 - 1 - m = 2 * n - m by omega, show 2 * n - (2 * n - m) = m by omega]
  congr 2
  push_cast [show m ≤ 2 * n by omega]
  ring

lemma a_even (n : ℕ) (hn : 4 ≤ n) (he : n % 2 = 0) : a n = 11111 * 10 ^ (n - 2) := by
  rw [a_reflect]
  have h : ∀ m ∈ Finset.range (2 * n + 1), (if state n ((n : ℤ) - m) then 10 ^ m else 0) =
      if m ∈ Finset.Ico (n - 2) (n + 3) then 10 ^ m else 0 := by
    intro m _
    rw [pattern n (le_trans (by norm_num) hn), if_neg (show ¬ (n % 2 = 1) by omega)]
    by_cases hm : m ∈ Finset.Ico (n - 2) (n + 3)
    · have hm' := Finset.mem_Ico.mp hm
      rw [if_pos hm, if_pos (decide_eq_true (by omega))]
    · have hm' : ¬ (n - 2 ≤ m ∧ m < n + 3) := fun h => hm (Finset.mem_Ico.mpr h)
      rw [if_neg hm, if_neg (show ¬ (decide (-2 ≤ (n : ℤ) - m ∧ (n : ℤ) - m ≤ 2) = true) by
        rw [decide_eq_true_iff]; omega)]
  rw [Finset.sum_congr rfl h, ← Finset.sum_filter]
  have hf : (Finset.range (2 * n + 1)).filter (fun m => m ∈ Finset.Ico (n - 2) (n + 3)) =
      Finset.Ico (n - 2) (n + 3) := by
    ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hf, Finset.sum_Ico_eq_sum_range, show n + 3 - (n - 2) = 5 by omega]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_add]
  ring

lemma a_odd (n : ℕ) (hn : 3 ≤ n) (ho : n % 2 = 1) :
    9 * (a n : ℤ) = 10 ^ (2 * n + 1) - 1 - 999 * 10 ^ (n - 1) := by
  have hcast : (a n : ℤ) = ∑ m ∈ Finset.range (2 * n + 1),
      (if state n ((n : ℤ) - m) then (10 : ℤ) ^ m else 0) := by
    rw [a_reflect]; push_cast; rfl
  rw [hcast]
  have h : ∀ m ∈ Finset.range (2 * n + 1), (if state n ((n : ℤ) - m) then (10 : ℤ) ^ m else 0) =
      (10 : ℤ) ^ m - (if m ∈ Finset.Ico (n - 1) (n + 2) then (10 : ℤ) ^ m else 0) := by
    intro m _
    rw [pattern n (by omega), if_pos ho]
    by_cases hm : m ∈ Finset.Ico (n - 1) (n + 2)
    · have hm' := Finset.mem_Ico.mp hm
      rw [if_pos hm, if_neg (by rw [decide_eq_true_iff]; omega)]; ring
    · have hm' : ¬ (n - 1 ≤ m ∧ m < n + 2) := fun h => hm (Finset.mem_Ico.mpr h)
      rw [if_neg hm, if_pos (decide_eq_true (by omega))]; ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, ← Finset.sum_filter]
  have hf : (Finset.range (2 * n + 1)).filter (fun m => m ∈ Finset.Ico (n - 1) (n + 2)) =
      Finset.Ico (n - 1) (n + 2) := by
    ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hf, Finset.sum_Ico_eq_sum_range, show n + 2 - (n - 1) = 3 by omega]
  have hgeom := geom_sum_mul (10 : ℤ) (2 * n + 1)
  have hs : ∑ i ∈ Finset.range 3, (10 : ℤ) ^ (n - 1 + i) = 111 * 10 ^ (n - 1) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_add]; ring
  rw [hs]
  linarith

lemma values : a 0 = 1 ∧ a 1 = 101 ∧ a 2 = 1010 ∧ a 3 = 1100011 ∧ a 4 = 1111100 ∧
    a 5 = 11110001111 ∧ a 6 = 111110000 ∧ a 7 = 111111000111111 ∧ a 8 = 11111000000 := by
  decide

/-- Barker's recurrence, for every `n > 8`. -/
theorem recurrence (n : ℕ) (hn : 8 < n) :
    (a n : ℤ) = 10101 * a (n - 2) - 1010100 * a (n - 4) + 1000000 * a (n - 6) := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    rw [a_even _ (by omega) he, a_even _ (by omega) (by omega), a_even _ (by omega) (by omega),
      a_even _ (by omega) (by omega)]
    simp only [show k + 10 - 2 = k + 8 by omega, show k + 10 - 2 - 2 = k + 6 by omega,
      show k + 10 - 4 = k + 6 by omega, show k + 10 - 4 - 2 = k + 4 by omega,
      show k + 10 - 6 = k + 4 by omega, show k + 10 - 6 - 2 = k + 2 by omega]
    push_cast
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    have h0 := a_odd (k + 9) (by omega) ho
    have h2 := a_odd (k + 9 - 2) (by omega) (by omega)
    have h4 := a_odd (k + 9 - 4) (by omega) (by omega)
    have h6 := a_odd (k + 9 - 6) (by omega) (by omega)
    simp only [show k + 9 - 2 = k + 7 by omega, show k + 9 - 4 = k + 5 by omega,
      show k + 9 - 6 = k + 3 by omega, show k + 9 - 1 = k + 8 by omega,
      show k + 7 - 1 = k + 6 by omega, show k + 5 - 1 = k + 4 by omega,
      show k + 3 - 1 = k + 2 by omega] at h0 h2 h4 h6 ⊢
    have : (9 : ℤ) * (a (k + 9) - (10101 * a (k + 7) - 1010100 * a (k + 5) + 1000000 * a (k + 3)))
        = 0 := by
      rw [mul_sub, mul_add, mul_sub, show (9 : ℤ) * (10101 * a (k + 7)) = 10101 * (9 * a (k + 7)) by ring,
        show (9 : ℤ) * (1010100 * a (k + 5)) = 1010100 * (9 * a (k + 5)) by ring,
        show (9 : ℤ) * (1000000 * a (k + 3)) = 1000000 * (9 * a (k + 3)) by ring, h0, h2, h4, h6]
      ring
    linarith

open PowerSeries in
/-- Barker's g.f., as an identity in `ℚ⟦X⟧`. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) =
    (1 + 101 * X - 9091 * X ^ 2 + 79810 * X ^ 3 - 8080810 * X ^ 4 + 100810100 * X ^ 5
      - 10092910100 * X ^ 6 - 101000000 * X ^ 7 + 10101000000 * X ^ 8) *
    ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X) * (1 + 100 * X))⁻¹ := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))
  set D : ℚ⟦X⟧ := (1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X) * (1 + 100 * X)
  have hden : constantCoeff D ≠ 0 := by simp [D]
  have hD : D = 1 - C (10101 : ℚ) * X ^ 2 + C (1010100 : ℚ) * X ^ 4 - C (1000000 : ℚ) * X ^ 6 := by
    simp only [D, map_ofNat]; ring
  have hN : (1 + 101 * X - 9091 * X ^ 2 + 79810 * X ^ 3 - 8080810 * X ^ 4 + 100810100 * X ^ 5
      - 10092910100 * X ^ 6 - 101000000 * X ^ 7 + 10101000000 * X ^ 8 : ℚ⟦X⟧) =
      1 + C (101 : ℚ) * X ^ 1 - C (9091 : ℚ) * X ^ 2 + C (79810 : ℚ) * X ^ 3
        - C (8080810 : ℚ) * X ^ 4 + C (100810100 : ℚ) * X ^ 5 - C (10092910100 : ℚ) * X ^ 6
        - C (101000000 : ℚ) * X ^ 7 + C (10101000000 : ℚ) * X ^ 8 := by
    simp only [map_ofNat]; ring
  have key : A * D = 1 + C (101 : ℚ) * X ^ 1 - C (9091 : ℚ) * X ^ 2 + C (79810 : ℚ) * X ^ 3
        - C (8080810 : ℚ) * X ^ 4 + C (100810100 : ℚ) * X ^ 5 - C (10092910100 : ℚ) * X ^ 6
        - C (101000000 : ℚ) * X ^ 7 + C (10101000000 : ℚ) * X ^ 8 := by
    have e1 : A * D = A - C (10101 : ℚ) * (A * X ^ 2) + C (1010100 : ℚ) * (A * X ^ 4)
        - C (1000000 : ℚ) * (A * X ^ 6) := by rw [hD]; ring
    rw [e1]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_one, coeff_X_pow, A,
      coeff_mk, coeff_C]
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := values
    rcases Nat.lt_or_ge n 9 with hn | hn
    · interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7, h8] <;> norm_num
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      simp only [show n ≠ 0 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
        show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega,
        show n - 6 ≠ 0 by omega, show n - 7 ≠ 0 by omega, show n - 8 ≠ 0 by omega, if_false,
        ite_self]
      have hr := recurrence n (by omega)
      have : (a n : ℚ) = 10101 * a (n - 2) - 1010100 * a (n - 4) + 1000000 * a (n - 6) := by
        exact_mod_cast hr
      rw [this]; ring
  rw [hN, ← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]

end OMA.S_oeis_a267041

theorem OMA.solution : type_of% @OMA.S_oeis_a267041.main :=
  ⟨fun n hn => OMA.S_oeis_a267041.recurrence n hn, OMA.S_oeis_a267041.gf⟩
