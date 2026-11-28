import OMAStatements.S_oeis_a266251

namespace OMA.S_oeis_a266251

open PowerSeries




lemma abs_aux {n i : ℤ} (h : n + 1 < |i|) : n < |i - 1| ∧ n < |i| ∧ n < |i + 1| := by
  rcases abs_cases i with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases (i - 1) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rcases abs_cases (i + 1) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> omega

lemma rule9 (l c x : Bool) : rule 9 l c x = ((!l && !c && !x) || (!l && c && x)) := by
  cases l <;> cases c <;> cases x <;> decide

/-- Outside the light cone the row is the background, which alternates. -/
lemma outside (n : ℕ) (i : ℤ) (h : (n : ℤ) < |i|) : row 9 n i = decide (n % 2 = 1) := by
  induction n generalizing i with
  | zero =>
    simp only [row]
    have : i ≠ 0 := by rintro rfl; simp at h
    simp [this]
  | succ n ih =>
    have hh := abs_aux (n := (n : ℤ)) (i := i) (by push_cast at h; exact h)
    simp only [row, rule9]
    rw [ih (i - 1) hh.1, ih i hh.2.1, ih (i + 1) hh.2.2]
    rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;> simp [h2, Nat.succ_mod_two_eq_one_iff]

/-- The explicit rows from n = 4 on. -/
def E (n : ℕ) (i : ℤ) : Bool :=
  if n % 2 = 0 then decide (i = n - 4 ∨ i = n - 3 ∨ i = n - 2 ∨ i = n)
  else decide (i ≤ n - 7 ∨ i = n - 5 ∨ (n : ℤ) < i)

lemma E_step (n : ℕ) (i : ℤ) :
    rule 9 (E n (i - 1)) (E n i) (E n (i + 1)) = E (n + 1) i := by
  rw [rule9]
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
  · have h3 : (n + 1) % 2 = 1 := by omega
    simp only [E, h2, h3, if_true, show ¬ (1 = 0) from by omega, if_false]
    push_cast
    cases h1 : decide (i - 1 = n - 4 ∨ i - 1 = n - 3 ∨ i - 1 = n - 2 ∨ i - 1 = n) <;>
    cases h0 : decide (i = n - 4 ∨ i = n - 3 ∨ i = n - 2 ∨ i = n) <;>
    cases h4 : decide (i + 1 = n - 4 ∨ i + 1 = n - 3 ∨ i + 1 = n - 2 ∨ i + 1 = n) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h1 h0 h4 <;>
    simp only [Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false, Bool.or_false,
      Bool.false_or, Bool.true_or, Bool.or_true, Bool.true_and, Bool.false_and] <;>
    symm <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not] <;> omega
  · have h3 : (n + 1) % 2 = 0 := by omega
    simp only [E, h2, h3, if_true, show ¬ (1 = 0) from by omega, if_false]
    push_cast
    cases h1 : decide (i - 1 ≤ n - 7 ∨ i - 1 = n - 5 ∨ (n : ℤ) < i - 1) <;>
    cases h0 : decide (i ≤ n - 7 ∨ i = n - 5 ∨ (n : ℤ) < i) <;>
    cases h4 : decide (i + 1 ≤ n - 7 ∨ i + 1 = n - 5 ∨ (n : ℤ) < i + 1) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h1 h0 h4 <;>
    simp only [Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false, Bool.or_false,
      Bool.false_or, Bool.true_or, Bool.or_true, Bool.true_and, Bool.false_and] <;>
    symm <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not] <;> omega

lemma row4 (i : ℤ) : row 9 4 i = E 4 i := by
  by_cases h : (4 : ℤ) < |i|
  · rw [outside 4 i (by exact_mod_cast h)]
    simp only [E]
    norm_num
    rcases abs_cases i with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  · have hi : -4 ≤ i ∧ i ≤ 4 := by cases abs_cases i <;> omega
    obtain ⟨h1, h2⟩ := hi
    interval_cases i <;> decide

lemma pattern (n : ℕ) (hn : 4 ≤ n) (i : ℤ) : row 9 n i = E n i := by
  induction n, hn using Nat.le_induction generalizing i with
  | base => exact row4 i
  | succ n hn ih =>
    show rule 9 (row 9 n (i - 1)) (row 9 n i) (row 9 n (i + 1)) = E (n + 1) i
    rw [ih, ih, ih, E_step]

lemma a_even (n : ℕ) (hn : 4 ≤ n) (he : n % 2 = 0) : a n = 2 * n - 3 := by
  have hs : (Finset.range (2 * n + 1)).filter (fun k : ℕ => row 9 n ((k : ℤ) - n) = false) =
      Finset.range (2 * n - 4) ∪ {2 * n - 1} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_singleton,
      pattern n hn, E, he, if_true, decide_eq_false_iff_not]
    omega
  rw [a, hs, Finset.card_union_of_disjoint (by simp; omega), Finset.card_range,
    Finset.card_singleton]
  omega

lemma a_odd (n : ℕ) (hn : 4 ≤ n) (ho : n % 2 = 1) : a n = 6 := by
  have hs : (Finset.range (2 * n + 1)).filter (fun k : ℕ => row 9 n ((k : ℤ) - n) = false) =
      {2 * n - 6} ∪ Finset.Icc (2 * n - 4) (2 * n) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Finset.mem_union,
      Finset.mem_singleton, pattern n hn, E, ho, show ¬ (1 = 0) from by omega, if_false,
      decide_eq_false_iff_not]
    omega
  rw [a, hs, Finset.card_union_of_disjoint (by simp; omega), Nat.card_Icc, Finset.card_singleton]
  omega

/-- Barker's closed form, for n > 3. -/
theorem closed (n : ℕ) (hn : 3 < n) :
    (a n : ℤ) = (2 * (-1) ^ n * n + 2 * n - 9 * (-1) ^ n + 3) / 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have hev : Even n := Nat.even_iff.2 h
    rw [a_even n hn h, hev.neg_one_pow]
    push_cast [show 3 ≤ 2 * n by omega]
    omega
  · have hod : Odd n := Nat.odd_iff.2 h
    rw [a_odd n hn h, hod.neg_one_pow]
    push_cast
    omega

/-- Barker's recurrence, for n > 7. -/
theorem recurrence (n : ℕ) (hn : 7 < n) : (a n : ℤ) = 2 * a (n - 2) - a (n - 4) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [a_even n (by omega) h, a_even (n - 2) (by omega) (by omega),
      a_even (n - 4) (by omega) (by omega)]
    push_cast [show 3 ≤ 2 * n by omega, show 3 ≤ 2 * (n - 2) by omega,
      show 3 ≤ 2 * (n - 4) by omega, show 2 ≤ n by omega, show 4 ≤ n by omega]
    ring
  · rw [a_odd n (by omega) h, a_odd (n - 2) (by omega) (by omega),
      a_odd (n - 4) (by omega) (by omega)]
    norm_num

lemma small : a 0 = 0 ∧ a 1 = 3 ∧ a 2 = 3 ∧ a 3 = 5 := by decide +kernel

/-- Barker's generating function, as an identity of formal power series. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2) =
    X * (3 + 3 * X - X ^ 2 - X ^ 3 - X ^ 4 + 2 * X ^ 5 - X ^ 6) := by
  have hD : ((1 - X) ^ 2 * (1 + X) ^ 2 : ℤ⟦X⟧) = 1 - (X ^ 2 + X ^ 2) + X ^ 4 := by ring
  have hN : (X * (3 + 3 * X - X ^ 2 - X ^ 3 - X ^ 4 + 2 * X ^ 5 - X ^ 6) : ℤ⟦X⟧) =
      (X ^ 1 + X ^ 1 + X ^ 1) + (X ^ 2 + X ^ 2 + X ^ 2) - X ^ 3 - X ^ 4 - X ^ 5 +
        (X ^ 6 + X ^ 6) - X ^ 7 := by ring
  rw [hD, hN]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', coeff_mk,
    coeff_X_pow]
  obtain ⟨h0, h1, h2, h3⟩ := small
  rcases Nat.lt_or_ge n 8 with hn | hn
  · have h4 : a 4 = 5 := by rw [a_even 4 le_rfl rfl]
    have h5 : a 5 = 6 := a_odd 5 (by norm_num) rfl
    have h6 : a 6 = 9 := by rw [a_even 6 (by norm_num) rfl]
    have h7 : a 7 = 6 := a_odd 7 (by norm_num) rfl
    interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    have := recurrence (m + 8) (by omega)
    rw [show m + 8 - 2 = m + 6 by omega, show m + 8 - 4 = m + 4 by omega] at this
    rw [if_pos (show 2 ≤ m + 8 by omega), if_pos (show 4 ≤ m + 8 by omega),
      show m + 8 - 2 = m + 6 by omega, show m + 8 - 4 = m + 4 by omega]
    rw [if_neg (show ¬ (m + 8 = 1) by omega), if_neg (show ¬ (m + 8 = 2) by omega),
      if_neg (show ¬ (m + 8 = 3) by omega), if_neg (show ¬ (m + 8 = 4) by omega),
      if_neg (show ¬ (m + 8 = 5) by omega), if_neg (show ¬ (m + 8 = 6) by omega),
      if_neg (show ¬ (m + 8 = 7) by omega)]
    linarith

end OMA.S_oeis_a266251

theorem OMA.solution : type_of% @OMA.S_oeis_a266251.main :=
  ⟨OMA.S_oeis_a266251.closed, OMA.S_oeis_a266251.recurrence, OMA.S_oeis_a266251.gf⟩
