import OMAStatements.S_oeis_a266445

namespace OMA.S_oeis_a266445

open PowerSeries





lemma state_succ (t : ℕ) (i : ℤ) :
    state (t + 1) i = rule (state t (i - 1)) (state t i) (state t (i + 1)) := rfl

/-- Relative ON cells of the even stages and relative OFF cells of the odd stages. -/
def E : List ℤ := [-4, -3, -2, 0]
def O : List ℤ := [-5, -3, -2, -1, 0]

lemma s1 (i : ℤ) : state 1 i = decide (i ∉ [(-1 : ℤ), 0]) := by
  show rule (decide (i - 1 = 0)) (decide (i = 0)) (decide (i + 1 = 0)) = _
  rcases (by omega : i ≤ -2 ∨ (-1 ≤ i ∧ i ≤ 2) ∨ 3 ≤ i) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_false (by omega : ¬ i - 1 = 0), decide_eq_false (by omega : ¬ i = 0),
      decide_eq_false (by omega : ¬ i + 1 = 0), decide_eq_true (by simp; omega)]; decide
  · interval_cases i <;> decide
  · rw [decide_eq_false (by omega : ¬ i - 1 = 0), decide_eq_false (by omega : ¬ i = 0),
      decide_eq_false (by omega : ¬ i + 1 = 0), decide_eq_true (by simp; omega)]; decide

lemma s2 (i : ℤ) : state 2 i = decide (i ∈ [(-1 : ℤ), 1]) := by
  rw [state_succ, s1, s1, s1]
  rcases (by omega : i ≤ -3 ∨ (-2 ≤ i ∧ i ≤ 3) ∨ 4 ≤ i) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_true (by simp; omega), decide_eq_true (by simp; omega),
      decide_eq_true (by simp; omega), decide_eq_false (by simp; omega)]; decide
  · interval_cases i <;> decide
  · rw [decide_eq_true (by simp; omega), decide_eq_true (by simp; omega),
      decide_eq_true (by simp; omega), decide_eq_false (by simp; omega)]; decide

lemma s3 (i : ℤ) : state 3 i = decide (i ∉ [(-2 : ℤ), -1, 0, 1]) := by
  rw [state_succ, s2, s2, s2]
  rcases (by omega : i ≤ -3 ∨ (-2 ≤ i ∧ i ≤ 4) ∨ 5 ≤ i) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_false (by simp; omega), decide_eq_false (by simp; omega),
      decide_eq_false (by simp; omega), decide_eq_true (by simp; omega)]; decide
  · interval_cases i <;> decide
  · rw [decide_eq_false (by simp; omega), decide_eq_false (by simp; omega),
      decide_eq_false (by simp; omega), decide_eq_true (by simp; omega)]; decide

lemma s4 (i : ℤ) : state 4 i = decide (i - 2 ∈ E) := by
  rw [state_succ, s3, s3, s3]
  rcases (by omega : i ≤ -4 ∨ (-3 ≤ i ∧ i ≤ 4) ∨ 5 ≤ i) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_true (by simp; omega), decide_eq_true (by simp; omega),
      decide_eq_true (by simp; omega), decide_eq_false (by simp [E]; omega)]; decide
  · interval_cases i <;> decide
  · rw [decide_eq_true (by simp; omega), decide_eq_true (by simp; omega),
      decide_eq_true (by simp; omega), decide_eq_false (by simp [E]; omega)]; decide

/-- Even stage to the next odd stage, relative position e. -/
lemma stepEO (e : ℤ) :
    rule (decide (e - 1 ∈ E)) (decide (e ∈ E)) (decide (e + 1 ∈ E)) = decide (e ∉ O) := by
  rcases (by omega : e ≤ -7 ∨ (-6 ≤ e ∧ e ≤ 2) ∨ 3 ≤ e) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_false (by simp [E]; omega), decide_eq_false (by simp [E]; omega),
      decide_eq_false (by simp [E]; omega), decide_eq_true (by simp [O]; omega)]; decide
  · interval_cases e <;> decide
  · rw [decide_eq_false (by simp [E]; omega), decide_eq_false (by simp [E]; omega),
      decide_eq_false (by simp [E]; omega), decide_eq_true (by simp [O]; omega)]; decide

/-- Odd stage to the next even stage, relative position e (the frame moves by one). -/
lemma stepOE (e : ℤ) :
    rule (decide (e - 1 ∉ O)) (decide (e ∉ O)) (decide (e + 1 ∉ O)) = decide (e - 1 ∈ E) := by
  rcases (by omega : e ≤ -8 ∨ (-7 ≤ e ∧ e ≤ 3) ∨ 4 ≤ e) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_true (by simp [O]; omega), decide_eq_true (by simp [O]; omega),
      decide_eq_true (by simp [O]; omega), decide_eq_false (by simp [E]; omega)]; decide
  · interval_cases e <;> decide
  · rw [decide_eq_true (by simp [O]; omega), decide_eq_true (by simp [O]; omega),
      decide_eq_true (by simp [O]; omega), decide_eq_false (by simp [E]; omega)]; decide

lemma odd_of_even (s : ℕ) (h : ∀ i, state (2 * s) i = decide (i - s ∈ E)) :
    ∀ i, state (2 * s + 1) i = decide (i - s ∉ O) := by
  intro i
  rw [state_succ, h, h, h]
  have e1 : i - 1 - (s : ℤ) = (i - s) - 1 := by ring
  have e2 : i + 1 - (s : ℤ) = (i - s) + 1 := by ring
  rw [e1, e2, stepEO]

lemma even_of_odd (s : ℕ) (h : ∀ i, state (2 * s + 1) i = decide (i - s ∉ O)) :
    ∀ i, state (2 * (s + 1)) i = decide (i - ((s + 1 : ℕ) : ℤ) ∈ E) := by
  intro i
  rw [show 2 * (s + 1) = (2 * s + 1) + 1 by ring, state_succ, h, h, h]
  have e1 : i - 1 - (s : ℤ) = (i - s) - 1 := by ring
  have e2 : i + 1 - (s : ℤ) = (i - s) + 1 := by ring
  have e3 : i - ((s + 1 : ℕ) : ℤ) = (i - s) - 1 := by push_cast; ring
  rw [e1, e2, e3, stepOE]

/-- The glider: stages 2s and 2s + 1 for s >= 2. -/
lemma pattern (s : ℕ) (hs : 2 ≤ s) :
    (∀ i, state (2 * s) i = decide (i - s ∈ E)) ∧
      (∀ i, state (2 * s + 1) i = decide (i - s ∉ O)) := by
  induction s, hs using Nat.le_induction with
  | base =>
    have h4 : ∀ i, state (2 * 2) i = decide (i - ((2 : ℕ) : ℤ) ∈ E) := fun i => by
      rw [s4]; norm_num
    exact ⟨h4, odd_of_even 2 h4⟩
  | succ s hs ih =>
    have he := even_of_odd s ih.2
    exact ⟨he, odd_of_even (s + 1) he⟩

lemma mid_even (s : ℕ) (hs : 2 ≤ s) : mid (2 * s) = if (-(s : ℤ)) ∈ E then 1 else 0 := by
  unfold mid
  rw [(pattern s hs).1 0]
  simp

lemma mid_odd (s : ℕ) (hs : 2 ≤ s) : mid (2 * s + 1) = if (-(s : ℤ)) ∈ O then 0 else 1 := by
  unfold mid
  rw [(pattern s hs).2 0]
  by_cases h : (-(s : ℤ)) ∈ O <;> simp [h]

lemma mid_even_big (s : ℕ) (hs : 5 ≤ s) : mid (2 * s) = 0 := by
  rw [mid_even s (by omega), if_neg]
  simp only [E, List.mem_cons, List.mem_nil_iff, or_false]
  omega

lemma mid_odd_big (s : ℕ) (hs : 6 ≤ s) : mid (2 * s + 1) = 1 := by
  rw [mid_odd s (by omega), if_neg]
  simp only [O, List.mem_cons, List.mem_nil_iff, or_false]
  omega

/-- The middle column from stage 12 on. -/
lemma mid_big (n : ℕ) (hn : 12 ≤ n) : (mid n : ℚ) = (1 - (-1) ^ n) / 2 := by
  rcases Nat.even_or_odd n with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [show n = 2 * s by omega, mid_even_big s (by omega), pow_mul]
    norm_num
  · rw [hs, mid_odd_big s (by omega), pow_succ, pow_mul]
    norm_num

lemma mid_rec (n : ℕ) (hn : 14 ≤ n) : mid n = mid (n - 2) := by
  rcases Nat.even_or_odd n with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [show n = 2 * s by omega, show 2 * s - 2 = 2 * (s - 1) by omega,
      mid_even_big s (by omega), mid_even_big (s - 1) (by omega)]
  · rw [hs, show 2 * s + 1 - 2 = 2 * (s - 1) + 1 by omega,
      mid_odd_big s (by omega), mid_odd_big (s - 1) (by omega)]

lemma mid_values : mid 0 = 1 ∧ mid 1 = 0 ∧ mid 2 = 0 ∧ mid 3 = 0 ∧ mid 4 = 1 ∧ mid 5 = 0 ∧
    mid 6 = 1 ∧ mid 7 = 0 ∧ mid 8 = 1 ∧ mid 9 = 1 ∧ mid 10 = 0 ∧ mid 11 = 0 ∧ mid 12 = 0 ∧
    mid 13 = 1 := by
  have h1 : mid 1 = 0 := by unfold mid; rw [s1]; decide
  have h2 : mid 2 = 0 := by unfold mid; rw [s2]; decide
  have h3 : mid 3 = 0 := by unfold mid; rw [s3]; decide
  refine ⟨by decide, h1, h2, h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 4 = 2 * 2 from rfl, mid_even 2 le_rfl]; decide
  · rw [show 5 = 2 * 2 + 1 from rfl, mid_odd 2 le_rfl]; decide
  · rw [show 6 = 2 * 3 from rfl, mid_even 3 (by norm_num)]; decide
  · rw [show 7 = 2 * 3 + 1 from rfl, mid_odd 3 (by norm_num)]; decide
  · rw [show 8 = 2 * 4 from rfl, mid_even 4 (by norm_num)]; decide
  · rw [show 9 = 2 * 4 + 1 from rfl, mid_odd 4 (by norm_num)]; decide
  · rw [show 10 = 2 * 5 from rfl, mid_even 5 (by norm_num)]; decide
  · rw [show 11 = 2 * 5 + 1 from rfl, mid_odd 5 (by norm_num)]; decide
  · rw [show 12 = 2 * 6 from rfl, mid_even 6 (by norm_num)]; decide
  · rw [show 13 = 2 * 6 + 1 from rfl, mid_odd 6 (by norm_num)]; decide

lemma a_zero : a 0 = mid 0 := by simp [a]

lemma a_succ (n : ℕ) : a (n + 1) = 10 * a n + mid (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
  ring

lemma values : a 0 = 1 ∧ a 1 = 10 ∧ a 2 = 100 ∧ a 3 = 1000 ∧ a 4 = 10001 ∧ a 5 = 100010 ∧
    a 6 = 1000101 ∧ a 7 = 10001010 ∧ a 8 = 100010101 ∧ a 9 = 1000101011 ∧
    a 10 = 10001010110 ∧ a 11 = 100010101100 ∧ a 12 = 1000101011000 ∧
    a 13 = 10001010110001 := by
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13⟩ := mid_values
  have h0 : a 0 = 1 := by rw [a_zero, m0]
  have h1 : a 1 = 10 := by rw [a_succ, h0, m1]
  have h2 : a 2 = 100 := by rw [a_succ, h1, m2]
  have h3 : a 3 = 1000 := by rw [a_succ, h2, m3]
  have h4 : a 4 = 10001 := by rw [a_succ, h3, m4]
  have h5 : a 5 = 100010 := by rw [a_succ, h4, m5]
  have h6 : a 6 = 1000101 := by rw [a_succ, h5, m6]
  have h7 : a 7 = 10001010 := by rw [a_succ, h6, m7]
  have h8 : a 8 = 100010101 := by rw [a_succ, h7, m8]
  have h9 : a 9 = 1000101011 := by rw [a_succ, h8, m9]
  have h10 : a 10 = 10001010110 := by rw [a_succ, h9, m10]
  have h11 : a 11 = 100010101100 := by rw [a_succ, h10, m11]
  have h12 : a 12 = 1000101011000 := by rw [a_succ, h11, m12]
  have h13 : a 13 = 10001010110001 := by rw [a_succ, h12, m13]
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- Barker's closed form, for n > 10. -/
theorem closed_form (n : ℕ) (hn : 10 < n) :
    (a n : ℚ) = (-9 * (-1) ^ n + 9901000008901 * 2 ^ (n - 10) * 5 ^ (n - 11) - 11) / 198 := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [values.2.2.2.2.2.2.2.2.2.2.2.1]
    norm_num
  | succ n hn ih =>
    have hexp2 : (2 : ℚ) ^ (n + 1 - 10) = 2 * 2 ^ (n - 10) := by
      rw [show n + 1 - 10 = (n - 10) + 1 by omega, pow_succ]; ring
    have hexp5 : (5 : ℚ) ^ (n + 1 - 11) = 5 * 5 ^ (n - 11) := by
      rw [show n + 1 - 11 = (n - 11) + 1 by omega, pow_succ]; ring
    rw [a_succ, hexp2, hexp5]
    push_cast
    rw [ih, mid_big (n + 1) (by omega), pow_succ]
    ring

/-- Keller's floor formula, for every n. -/
theorem keller (n : ℕ) : a n = 9901000008901 * 10 ^ n / 9900000000000 := by
  rcases Nat.lt_or_ge n 11 with hn | hn
  · obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, -⟩ := values
    interval_cases n
    · rw [v0]; norm_num
    · rw [v1]; norm_num
    · rw [v2]; norm_num
    · rw [v3]; norm_num
    · rw [v4]; norm_num
    · rw [v5]; norm_num
    · rw [v6]; norm_num
    · rw [v7]; norm_num
    · rw [v8]; norm_num
    · rw [v9]; norm_num
    · rw [v10]; norm_num
  · have hc := closed_form n (by omega)
    have h10 : (10 : ℚ) ^ n = 2 ^ (n - 10) * 5 ^ (n - 11) * 50000000000 := by
      have e1 : (2 : ℚ) ^ n = 2 ^ (n - 10) * 2 ^ 10 := by
        rw [← pow_add, show n - 10 + 10 = n by omega]
      have e2 : (5 : ℚ) ^ n = 5 ^ (n - 11) * 5 ^ 11 := by
        rw [← pow_add, show n - 11 + 11 = n by omega]
      rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow, e1, e2]
      ring
    rcases Nat.even_or_odd n with he | ho
    · have hq : ((9901000008901 * 10 ^ n : ℕ) : ℚ) =
          ((1000000000000 + 9900000000000 * a n : ℕ) : ℚ) := by
        push_cast
        rw [hc, he.neg_one_pow, h10]
        ring
      have hn' : 9901000008901 * 10 ^ n = 1000000000000 + 9900000000000 * a n := by
        exact_mod_cast hq
      rw [hn', Nat.add_mul_div_left _ _ (by norm_num)]
      norm_num
    · have hq : ((9901000008901 * 10 ^ n : ℕ) : ℚ) =
          ((100000000000 + 9900000000000 * a n : ℕ) : ℚ) := by
        push_cast
        rw [hc, ho.neg_one_pow, h10]
        ring
      have hn' : 9901000008901 * 10 ^ n = 100000000000 + 9900000000000 * a n := by
        exact_mod_cast hq
      rw [hn', Nat.add_mul_div_left _ _ (by norm_num)]
      norm_num

/-- Barker's g.f., as an identity in Q[[x]]. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) =
    (1 - X ^ 2 + X ^ 4 + X ^ 9 - X ^ 10 - X ^ 11 + X ^ 13) *
      ((1 - X) * (1 + X) * (1 - 10 * X))⁻¹ := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have hden : constantCoeff ((1 - X) * (1 + X) * (1 - 10 * X) : ℚ⟦X⟧) ≠ 0 := by simp
  have key : A * ((1 - X) * (1 + X) * (1 - 10 * X)) =
      1 - X ^ 2 + X ^ 4 + X ^ 9 - X ^ 10 - X ^ 11 + X ^ 13 := by
    have e1 : A * ((1 - X) * (1 + X) * (1 - 10 * X)) =
        A - C 10 * (A * X ^ 1) - A * X ^ 2 + C 10 * (A * X ^ 3) := by
      simp only [map_ofNat]; ring
    rw [e1]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_one, coeff_X_pow, hA,
      coeff_mk]
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13⟩ := values
    rcases Nat.lt_or_ge n 14 with hn | hn
    · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] <;>
        norm_num
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      simp only [show n ≠ 0 by omega, show n ≠ 2 by omega, show n ≠ 4 by omega,
        show n ≠ 9 by omega, show n ≠ 10 by omega, show n ≠ 11 by omega, show n ≠ 13 by omega,
        if_false]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have r1 := a_succ (m + 2)
      have r2 := a_succ m
      have hm := mid_rec (m + 3) (by omega)
      rw [show m + 3 - 2 = m + 1 by omega] at hm
      rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
        show m + 3 - 3 = m by omega]
      rw [show m + 2 + 1 = m + 3 by omega] at r1
      have q1 : (a (m + 3) : ℚ) = 10 * a (m + 2) + mid (m + 3) := by exact_mod_cast r1
      have q2 : (a (m + 1) : ℚ) = 10 * a m + mid (m + 1) := by exact_mod_cast r2
      have q3 : (mid (m + 3) : ℚ) = mid (m + 1) := by exact_mod_cast hm
      rw [q1, q2, q3]
      ring
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]

/-- Controls: the entry's data a(0..19). -/
theorem controls : a 0 = 1 ∧ a 1 = 10 ∧ a 2 = 100 ∧ a 3 = 1000 ∧ a 4 = 10001 ∧ a 5 = 100010 ∧
    a 6 = 1000101 ∧ a 7 = 10001010 ∧ a 8 = 100010101 ∧ a 9 = 1000101011 ∧
    a 10 = 10001010110 ∧ a 11 = 100010101100 ∧ a 12 = 1000101011000 ∧
    a 13 = 10001010110001 ∧ a 14 = 100010101100010 ∧ a 15 = 1000101011000101 ∧
    a 16 = 10001010110001010 ∧ a 17 = 100010101100010101 ∧ a 18 = 1000101011000101010 ∧
    a 19 = 10001010110001010101 := by
  refine ⟨values.1, values.2.1, values.2.2.1, values.2.2.2.1, values.2.2.2.2.1,
    values.2.2.2.2.2.1, values.2.2.2.2.2.2.1, values.2.2.2.2.2.2.2.1, values.2.2.2.2.2.2.2.2.1,
    values.2.2.2.2.2.2.2.2.2.1, values.2.2.2.2.2.2.2.2.2.2.1, values.2.2.2.2.2.2.2.2.2.2.2.1,
    values.2.2.2.2.2.2.2.2.2.2.2.2.1, values.2.2.2.2.2.2.2.2.2.2.2.2.2, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [keller] <;> norm_num

/-- Barker's two conjectures and Keller's. -/
theorem conjecture :
    (∀ n : ℕ, 10 < n →
      (a n : ℚ) = (-9 * (-1) ^ n + 9901000008901 * 2 ^ (n - 10) * 5 ^ (n - 11) - 11) / 198) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 - X ^ 2 + X ^ 4 + X ^ 9 - X ^ 10 - X ^ 11 + X ^ 13) *
        ((1 - X) * (1 + X) * (1 - 10 * X))⁻¹ ∧
    ∀ n : ℕ, a n = 9901000008901 * 10 ^ n / 9900000000000 :=
  ⟨closed_form, gf, keller⟩

end OMA.S_oeis_a266445

theorem OMA.solution : type_of% @OMA.S_oeis_a266445.main :=
  OMA.S_oeis_a266445.conjecture
