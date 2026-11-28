import OMAStatements.S_oeis_a266449

namespace OMA.S_oeis_a266449

open PowerSeries




lemma rule25 (l c x : Bool) :
    rule 25 l c x = ((!l && !c && !x) || (!l && c && x) || (l && !c && !x)) := by
  cases l <;> cases c <;> cases x <;> decide

lemma abs_aux {n i : ℤ} (h : n + 1 < |i|) : n < |i - 1| ∧ n < |i| ∧ n < |i + 1| := by
  rcases abs_cases i with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases (i - 1) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rcases abs_cases (i + 1) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> omega

/-- Outside the light cone the row is the background, which alternates. -/
lemma outside (n : ℕ) (i : ℤ) (h : (n : ℤ) < |i|) : row 25 n i = decide (n % 2 = 1) := by
  induction n generalizing i with
  | zero =>
    simp only [row]
    have : i ≠ 0 := by rintro rfl; simp at h
    simp [this]
  | succ n ih =>
    have hh := abs_aux (n := (n : ℤ)) (i := i) (by push_cast at h; exact h)
    simp only [row, rule25]
    rw [ih (i - 1) hh.1, ih i hh.2.1, ih (i + 1) hh.2.2]
    rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;> simp [h2, Nat.succ_mod_two_eq_one_iff]

/-- The explicit rows from n = 4 on (m = floor(n/2)). -/
def E (n : ℕ) (i : ℤ) : Bool :=
  if n % 2 = 0 then decide (i = ((n / 2 : ℕ) : ℤ) - 4 ∨ i = ((n / 2 : ℕ) : ℤ) - 3 ∨
      i = ((n / 2 : ℕ) : ℤ) - 2 ∨ i = ((n / 2 : ℕ) : ℤ))
  else decide (i ≤ ((n / 2 : ℕ) : ℤ) - 6 ∨ i = ((n / 2 : ℕ) : ℤ) - 4 ∨
      ((n / 2 : ℕ) : ℤ) + 1 ≤ i)

lemma E_step (n : ℕ) (i : ℤ) :
    rule 25 (E n (i - 1)) (E n i) (E n (i + 1)) = E (n + 1) i := by
  rw [rule25]
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
  · have h3 : (n + 1) % 2 = 1 := by omega
    have h4 : (n + 1) / 2 = n / 2 := by omega
    simp only [E, h2, h3, h4, if_true, show ¬ (1 = 0) from by omega, if_false]
    generalize ((n / 2 : ℕ) : ℤ) = m
    cases h1 : decide (i - 1 = m - 4 ∨ i - 1 = m - 3 ∨ i - 1 = m - 2 ∨ i - 1 = m) <;>
    cases h0 : decide (i = m - 4 ∨ i = m - 3 ∨ i = m - 2 ∨ i = m) <;>
    cases h5 : decide (i + 1 = m - 4 ∨ i + 1 = m - 3 ∨ i + 1 = m - 2 ∨ i + 1 = m) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h1 h0 h5 <;>
    simp only [Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false, Bool.or_false,
      Bool.false_or, Bool.true_or, Bool.or_true, Bool.true_and, Bool.false_and] <;>
    symm <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not] <;> omega
  · have h3 : (n + 1) % 2 = 0 := by omega
    have h4 : (((n + 1) / 2 : ℕ) : ℤ) = ((n / 2 : ℕ) : ℤ) + 1 := by
      have : (n + 1) / 2 = n / 2 + 1 := by omega
      rw [this]; push_cast; ring
    simp only [E, h2, h3, h4, if_true, show ¬ (1 = 0) from by omega, if_false]
    generalize ((n / 2 : ℕ) : ℤ) = m
    cases h1 : decide (i - 1 ≤ m - 6 ∨ i - 1 = m - 4 ∨ m + 1 ≤ i - 1) <;>
    cases h0 : decide (i ≤ m - 6 ∨ i = m - 4 ∨ m + 1 ≤ i) <;>
    cases h5 : decide (i + 1 ≤ m - 6 ∨ i + 1 = m - 4 ∨ m + 1 ≤ i + 1) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h1 h0 h5 <;>
    simp only [Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false, Bool.or_false,
      Bool.false_or, Bool.true_or, Bool.or_true, Bool.true_and, Bool.false_and] <;>
    symm <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not] <;> omega

lemma row4 (i : ℤ) : row 25 4 i = E 4 i := by
  by_cases h : (4 : ℤ) < |i|
  · rw [outside 4 i (by exact_mod_cast h)]
    simp only [E]
    norm_num
    rcases abs_cases i with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  · have hi : -4 ≤ i ∧ i ≤ 4 := by cases abs_cases i <;> omega
    obtain ⟨h1, h2⟩ := hi
    interval_cases i <;> decide

lemma pattern (n : ℕ) (hn : 4 ≤ n) (i : ℤ) : row 25 n i = E n i := by
  induction n, hn using Nat.le_induction generalizing i with
  | base => exact row4 i
  | succ n hn ih =>
    show rule 25 (row 25 n (i - 1)) (row 25 n i) (row 25 n (i + 1)) = E (n + 1) i
    rw [ih, ih, ih, E_step]

lemma a_even (n : ℕ) (hn : 4 ≤ n) (he : n % 2 = 0) : a n = 2 * n - 3 := by
  have hs : (Finset.range (2 * n + 1)).filter (fun k : ℕ => row 25 n ((k : ℤ) - n) = false) =
      (Finset.range (3 * (n / 2) - 4) ∪ {3 * (n / 2) - 1}) ∪
        Finset.Icc (3 * (n / 2) + 1) (2 * n) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Finset.mem_union,
      Finset.mem_singleton, pattern n hn, E, he, if_true, decide_eq_false_iff_not]
    omega
  rw [a, hs, Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_union_left]; constructor <;> simp [Finset.disjoint_left] <;> omega),
    Finset.card_union_of_disjoint (by simp <;> omega), Finset.card_range,
    Finset.card_singleton, Nat.card_Icc]
  omega

lemma a_odd (n : ℕ) (hn : 4 ≤ n) (ho : n % 2 = 1) : a n = 5 := by
  have hs : (Finset.range (2 * n + 1)).filter (fun k : ℕ => row 25 n ((k : ℤ) - n) = false) =
      {3 * (n / 2) - 4} ∪ Finset.Icc (3 * (n / 2) - 2) (3 * (n / 2) + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Finset.mem_union,
      Finset.mem_singleton, pattern n hn, E, ho, show ¬ (1 = 0) from by omega, if_false,
      decide_eq_false_iff_not]
    omega
  rw [a, hs, Finset.card_union_of_disjoint (by simp <;> omega), Nat.card_Icc,
    Finset.card_singleton]
  omega

lemma small : a 0 = 0 ∧ a 1 = 2 ∧ a 2 = 3 ∧ a 3 = 4 := by decide +kernel

/-- Barker's closed form, for n > 3. -/
theorem closed (n : ℕ) (hn : 3 < n) : (a n : ℤ) = (-1) ^ n * (n - 4) + n + 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [a_even n (by omega) h, (Nat.even_iff.2 h).neg_one_pow]
    push_cast [show 3 ≤ 2 * n by omega]
    ring
  · rw [a_odd n (by omega) h, (Nat.odd_iff.2 h).neg_one_pow]
    push_cast
    ring

/-- Barker's recurrence, for n > 7. -/
theorem recurrence (n : ℕ) (hn : 7 < n) : (a n : ℤ) = 2 * a (n - 2) - a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 2 = m + 2 by omega, show m + 4 - 4 = m by omega, closed (m + 4) (by omega),
    closed (m + 2) (by omega), closed m (by omega)]
  rcases Nat.even_or_odd m with h | h
  · rw [(show Even (m + 4) by exact h.add (by decide)).neg_one_pow,
      (show Even (m + 2) by exact h.add (by decide)).neg_one_pow, h.neg_one_pow]
    push_cast; ring
  · rw [(show Odd (m + 4) by exact h.add_even (by decide)).neg_one_pow,
      (show Odd (m + 2) by exact h.add_even (by decide)).neg_one_pow, h.neg_one_pow]
    push_cast; ring

/-- Barker's generating function, as an identity of formal power series. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2) =
    X * (1 + X - X ^ 2) * (2 + X + X ^ 2 - X ^ 3 + X ^ 4) := by
  have hD : ((1 - X) ^ 2 * (1 + X) ^ 2 : ℤ⟦X⟧) = 1 - (X ^ 2 + X ^ 2) + X ^ 4 := by ring
  have hN : (X * (1 + X - X ^ 2) * (2 + X + X ^ 2 - X ^ 3 + X ^ 4) : ℤ⟦X⟧) =
      (X ^ 1 + X ^ 1) + (X ^ 2 + X ^ 2 + X ^ 2) - X ^ 4 - X ^ 5 + (X ^ 6 + X ^ 6) - X ^ 7 := by
    ring
  rw [hD, hN]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', coeff_mk,
    coeff_X_pow]
  obtain ⟨h0, h1, h2, h3⟩ := small
  rcases Nat.lt_or_ge n 8 with hn | hn
  · have h4 : (a 4 : ℤ) = 5 := by rw [closed 4 (by norm_num)]; norm_num
    have h5 : (a 5 : ℤ) = 5 := by rw [closed 5 (by norm_num)]; norm_num
    have h6 : (a 6 : ℤ) = 9 := by rw [closed 6 (by norm_num)]; norm_num
    have h7 : (a 7 : ℤ) = 5 := by rw [closed 7 (by norm_num)]; norm_num
    interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    have := recurrence (m + 8) (by omega)
    simp only [show m + 8 - 2 = m + 6 by omega, show m + 8 - 4 = m + 4 by omega] at this
    rw [if_pos (show 2 ≤ m + 8 by omega), if_pos (show 4 ≤ m + 8 by omega),
      show m + 8 - 2 = m + 6 by omega, show m + 8 - 4 = m + 4 by omega]
    rw [if_neg (show ¬ (m + 8 = 1) by omega), if_neg (show ¬ (m + 8 = 2) by omega),
      if_neg (show ¬ (m + 8 = 4) by omega), if_neg (show ¬ (m + 8 = 5) by omega),
      if_neg (show ¬ (m + 8 = 6) by omega), if_neg (show ¬ (m + 8 = 7) by omega)]
    linarith

/-- Barker's three conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = (-1) ^ n * (n - 4) + n + 1) ∧
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 2 * a (n - 2) - a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2) =
      X * (1 + X - X ^ 2) * (2 + X + X ^ 2 - X ^ 3 + X ^ 4) :=
  ⟨closed, recurrence, gf⟩

end OMA.S_oeis_a266449

theorem OMA.solution : type_of% @OMA.S_oeis_a266449.main :=
  OMA.S_oeis_a266449.conjecture
