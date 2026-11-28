import OMAStatements.S_oeis_a266450

namespace OMA.S_oeis_a266450

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

lemma off_even (n : ℕ) (hn : 4 ≤ n) (he : n % 2 = 0) : off n = 2 * n - 3 := by
  have hs : (Finset.range (2 * n + 1)).filter (fun k : ℕ => row 25 n ((k : ℤ) - n) = false) =
      (Finset.range (3 * (n / 2) - 4) ∪ {3 * (n / 2) - 1}) ∪
        Finset.Icc (3 * (n / 2) + 1) (2 * n) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Finset.mem_union,
      Finset.mem_singleton, pattern n hn, E, he, if_true, decide_eq_false_iff_not]
    omega
  rw [off, hs, Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_union_left]; constructor <;> simp [Finset.disjoint_left] <;> omega),
    Finset.card_union_of_disjoint (by simp; omega), Finset.card_range, Finset.card_singleton,
    Nat.card_Icc]
  omega

lemma off_odd (n : ℕ) (hn : 4 ≤ n) (ho : n % 2 = 1) : off n = 5 := by
  have hs : (Finset.range (2 * n + 1)).filter (fun k : ℕ => row 25 n ((k : ℤ) - n) = false) =
      {3 * (n / 2) - 4} ∪ Finset.Icc (3 * (n / 2) - 2) (3 * (n / 2) + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Finset.mem_union,
      Finset.mem_singleton, pattern n hn, E, ho, show ¬ (1 = 0) from by omega, if_false,
      decide_eq_false_iff_not]
    omega
  rw [off, hs, Finset.card_union_of_disjoint (by simp; omega), Nat.card_Icc, Finset.card_singleton]
  omega

lemma small : a 0 = 0 ∧ a 1 = 2 ∧ a 2 = 5 ∧ a 3 = 9 ∧ a 4 = 14 := by decide +kernel

lemma a_succ (n : ℕ) : a (n + 1) = a n + off (n + 1) := Finset.sum_range_succ _ _

/-- Barker's closed form multiplied out, for n > 2. -/
theorem closed_mul (n : ℕ) (hn : 2 < n) :
    4 * (a n : ℤ) = 2 * n ^ 2 + 2 * ((-1) ^ n + 3) * n - 7 * (-1) ^ n - 1 := by
  induction n, hn using Nat.le_induction with
  | base => rw [small.2.2.2.1]; norm_num
  | succ n hn ih =>
    rw [a_succ]
    push_cast
    rw [mul_add, ih]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h1 : (n + 1) % 2 = 1 := by omega
      rw [off_odd (n + 1) (by omega) h1, (Nat.even_iff.2 h).neg_one_pow,
        (Nat.odd_iff.2 h1).neg_one_pow]
      push_cast
      ring
    · have h1 : (n + 1) % 2 = 0 := by omega
      rw [off_even (n + 1) (by omega) h1, (Nat.odd_iff.2 h).neg_one_pow,
        (Nat.even_iff.2 h1).neg_one_pow]
      push_cast [show 3 ≤ 2 * (n + 1) by omega]
      ring

/-- Barker's closed form, for n > 2. -/
theorem closed (n : ℕ) (hn : 2 < n) :
    (a n : ℤ) = (2 * n ^ 2 + 2 * ((-1) ^ n + 3) * n - 7 * (-1) ^ n - 1) / 4 := by
  have := closed_mul n hn
  omega

/-- Barker's recurrence, for n > 7. -/
theorem recurrence (n : ℕ) (hn : 7 < n) :
    (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m by omega]
  have e5 := closed_mul (m + 5) (by omega)
  have e4 := closed_mul (m + 4) (by omega)
  have e3 := closed_mul (m + 3) (by omega)
  have e2 := closed_mul (m + 2) (by omega)
  have e1 := closed_mul (m + 1) (by omega)
  have e0 := closed_mul m (by omega)
  rcases Nat.even_or_odd m with h | h
  · have h1 : Odd (m + 1) := h.add_one
    have h2 : Even (m + 2) := h1.add_one
    have h3 : Odd (m + 3) := h2.add_one
    have h4 : Even (m + 4) := h3.add_one
    have h5 : Odd (m + 5) := h4.add_one
    rw [h5.neg_one_pow] at e5; rw [h4.neg_one_pow] at e4; rw [h3.neg_one_pow] at e3
    rw [h2.neg_one_pow] at e2; rw [h1.neg_one_pow] at e1; rw [h.neg_one_pow] at e0
    push_cast at e5 e4 e3 e2 e1 e0
    linarith
  · have h1 : Even (m + 1) := h.add_one
    have h2 : Odd (m + 2) := h1.add_one
    have h3 : Even (m + 3) := h2.add_one
    have h4 : Odd (m + 4) := h3.add_one
    have h5 : Even (m + 5) := h4.add_one
    rw [h5.neg_one_pow] at e5; rw [h4.neg_one_pow] at e4; rw [h3.neg_one_pow] at e3
    rw [h2.neg_one_pow] at e2; rw [h1.neg_one_pow] at e1; rw [h.neg_one_pow] at e0
    push_cast at e5 e4 e3 e2 e1 e0
    linarith

/-- Barker's generating function, as an identity of formal power series. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) =
    X * (1 + X - X ^ 2) * (2 + X + X ^ 2 - X ^ 3 + X ^ 4) := by
  have hD : ((1 - X) ^ 3 * (1 + X) ^ 2 : ℤ⟦X⟧) =
      1 - X ^ 1 - (X ^ 2 + X ^ 2) + (X ^ 3 + X ^ 3) + X ^ 4 - X ^ 5 := by ring
  have hN : (X * (1 + X - X ^ 2) * (2 + X + X ^ 2 - X ^ 3 + X ^ 4) : ℤ⟦X⟧) =
      (X ^ 1 + X ^ 1) + (X ^ 2 + X ^ 2 + X ^ 2) - X ^ 4 - X ^ 5 + (X ^ 6 + X ^ 6) - X ^ 7 := by
    ring
  rw [hD, hN]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', coeff_mk,
    coeff_X_pow]
  obtain ⟨h0, h1, h2, h3, h4⟩ := small
  rcases Nat.lt_or_ge n 8 with hn | hn
  · have h5 : (a 5 : ℤ) = 19 := by rw [closed 5 (by norm_num)]; norm_num
    have h6 : (a 6 : ℤ) = 28 := by rw [closed 6 (by norm_num)]; norm_num
    have h7 : (a 7 : ℤ) = 33 := by rw [closed 7 (by norm_num)]; norm_num
    interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    have := recurrence (m + 8) (by omega)
    simp only [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
      show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega,
      show m + 8 - 5 = m + 3 by omega] at this
    rw [if_pos (show 1 ≤ m + 8 by omega), if_pos (show 2 ≤ m + 8 by omega),
      if_pos (show 3 ≤ m + 8 by omega), if_pos (show 4 ≤ m + 8 by omega),
      if_pos (show 5 ≤ m + 8 by omega),
      show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
      show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega,
      show m + 8 - 5 = m + 3 by omega]
    rw [if_neg (show ¬ (m + 8 = 1) by omega), if_neg (show ¬ (m + 8 = 2) by omega),
      if_neg (show ¬ (m + 8 = 4) by omega), if_neg (show ¬ (m + 8 = 5) by omega),
      if_neg (show ¬ (m + 8 = 6) by omega), if_neg (show ¬ (m + 8 = 7) by omega)]
    linarith

end OMA.S_oeis_a266450

theorem OMA.solution : type_of% @OMA.S_oeis_a266450.main :=
  ⟨OMA.S_oeis_a266450.closed_mul, OMA.S_oeis_a266450.recurrence, OMA.S_oeis_a266450.gf⟩
