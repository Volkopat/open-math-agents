import OMAStatements.S_oeis_a266249

namespace OMA.S_oeis_a266249




def E : List ℤ := [-4, -3, -2, 0]
def O : List ℤ := [-6, -4, -3, -2, -1, 0]

lemma s1 (i : ℤ) : state 1 i = decide (i ∉ [-1, 0, 1]) := by
  show rule (decide (i - 1 = 0)) (decide (i = 0)) (decide (i + 1 = 0)) = _
  rcases (by omega : i ≤ -2 ∨ (-1 ≤ i ∧ i ≤ 1) ∨ 2 ≤ i) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_false (by omega : ¬ i - 1 = 0), decide_eq_false (by omega : ¬ i = 0),
      decide_eq_false (by omega : ¬ i + 1 = 0), decide_eq_true (by simp <;> omega)]; decide
  · interval_cases i <;> decide
  · rw [decide_eq_false (by omega : ¬ i - 1 = 0), decide_eq_false (by omega : ¬ i = 0),
      decide_eq_false (by omega : ¬ i + 1 = 0), decide_eq_true (by simp <;> omega)]; decide

lemma s2 (i : ℤ) : state 2 i = decide (i ∈ [0, 2]) := by
  show rule (state 1 (i - 1)) (state 1 i) (state 1 (i + 1)) = _
  rw [s1, s1, s1]
  rcases (by omega : i ≤ -3 ∨ (-2 ≤ i ∧ i ≤ 3) ∨ 4 ≤ i) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_true (by simp <;> omega), decide_eq_true (by simp <;> omega),
      decide_eq_true (by simp <;> omega), decide_eq_false (by simp <;> omega)]; decide
  · interval_cases i <;> decide
  · rw [decide_eq_true (by simp <;> omega), decide_eq_true (by simp <;> omega),
      decide_eq_true (by simp <;> omega), decide_eq_false (by simp <;> omega)]; decide

lemma s3 (i : ℤ) : state 3 i = decide (i ∉ [-1, 0, 1, 2, 3]) := by
  show rule (state 2 (i - 1)) (state 2 i) (state 2 (i + 1)) = _
  rw [s2, s2, s2]
  rcases (by omega : i ≤ -3 ∨ (-2 ≤ i ∧ i ≤ 4) ∨ 5 ≤ i) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_false (by simp <;> omega), decide_eq_false (by simp <;> omega),
      decide_eq_false (by simp <;> omega), decide_eq_true (by simp <;> omega)]; decide
  · interval_cases i <;> decide
  · rw [decide_eq_false (by simp <;> omega), decide_eq_false (by simp <;> omega),
      decide_eq_false (by simp <;> omega), decide_eq_true (by simp <;> omega)]; decide

lemma s4 (i : ℤ) : state 4 i = decide (i - 4 ∈ E) := by
  show rule (state 3 (i - 1)) (state 3 i) (state 3 (i + 1)) = _
  rw [s3, s3, s3]
  rcases (by omega : i ≤ -3 ∨ (-2 ≤ i ∧ i ≤ 5) ∨ 6 ≤ i) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_true (by simp <;> omega), decide_eq_true (by simp <;> omega),
      decide_eq_true (by simp <;> omega), decide_eq_false (by simp [E]; omega)]; decide
  · interval_cases i <;> decide
  · rw [decide_eq_true (by simp <;> omega), decide_eq_true (by simp <;> omega),
      decide_eq_true (by simp <;> omega), decide_eq_false (by simp [E]; omega)]; decide

/-- Even row to odd row (relative position `e = i - t`). -/
lemma stepEO (e : ℤ) :
    rule (decide (e - 1 ∈ E)) (decide (e ∈ E)) (decide (e + 1 ∈ E)) = decide (e - 1 ∉ O) := by
  rcases (by omega : e ≤ -6 ∨ (-5 ≤ e ∧ e ≤ 1) ∨ 2 ≤ e) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_false (by simp [E]; omega), decide_eq_false (by simp [E]; omega),
      decide_eq_false (by simp [E]; omega), decide_eq_true (by simp [O]; omega)]; decide
  · interval_cases e <;> decide
  · rw [decide_eq_false (by simp [E]; omega), decide_eq_false (by simp [E]; omega),
      decide_eq_false (by simp [E]; omega), decide_eq_true (by simp [O]; omega)]; decide

/-- Odd row to even row (relative position `e = i - t`). -/
lemma stepOE (e : ℤ) :
    rule (decide (e - 1 ∉ O)) (decide (e ∉ O)) (decide (e + 1 ∉ O)) = decide (e - 1 ∈ E) := by
  rcases (by omega : e ≤ -8 ∨ (-7 ≤ e ∧ e ≤ 1) ∨ 2 ≤ e) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_true (by simp [O]; omega), decide_eq_true (by simp [O]; omega),
      decide_eq_true (by simp [O]; omega), decide_eq_false (by simp [E]; omega)]; decide
  · interval_cases e <;> decide
  · rw [decide_eq_true (by simp [O]; omega), decide_eq_true (by simp [O]; omega),
      decide_eq_true (by simp [O]; omega), decide_eq_false (by simp [E]; omega)]; decide

/-- The rows from time 4 on. -/
lemma pattern (t : ℕ) (ht : 4 ≤ t) (i : ℤ) :
    state t i = if t % 2 = 0 then decide (i - t ∈ E) else decide (i - t ∉ O) := by
  induction t, ht using Nat.le_induction generalizing i with
  | base => rw [s4]; rfl
  | succ t _ ih =>
    show rule (state t (i - 1)) (state t i) (state t (i + 1)) = _
    rw [ih, ih, ih]
    have e1 : i - 1 - (t : ℤ) = (i - t) - 1 := by ring
    have e2 : i + 1 - (t : ℤ) = (i - t) + 1 := by ring
    have e3 : i - ((t + 1 : ℕ) : ℤ) = (i - t) - 1 := by push_cast; ring
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · rw [if_pos h, if_pos h, if_pos h, if_neg (show ¬ ((t + 1) % 2 = 0) by omega), e1, e2, e3,
        stepEO]
    · rw [if_neg (show ¬ (t % 2 = 0) by omega), if_neg (show ¬ (t % 2 = 0) by omega),
        if_neg (show ¬ (t % 2 = 0) by omega), if_pos (show (t + 1) % 2 = 0 by omega), e1, e2, e3,
        stepOE]

lemma a_even (n : ℕ) (hn : 4 ≤ n) (he : n % 2 = 0) : a n = 4 := by
  unfold a
  have hf : (Finset.Icc (-(n : ℤ)) n).filter (fun i => state n i) =
      {(n : ℤ) - 4, (n : ℤ) - 3, (n : ℤ) - 2, (n : ℤ)} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
      pattern n hn i, if_pos he, decide_eq_true_eq, E, List.mem_cons, List.mem_nil_iff, or_false]
    omega
  rw [hf, Finset.card_insert_of_notMem (by simp <;> omega), Finset.card_insert_of_notMem (by simp <;> omega),
    Finset.card_insert_of_notMem (by simp), Finset.card_singleton]

lemma a_odd (n : ℕ) (hn : 5 ≤ n) (ho : n % 2 = 1) : (a n : ℤ) = 2 * n - 5 := by
  unfold a
  have hf : (Finset.Icc (-(n : ℤ)) n).filter (fun i => state n i) =
      Finset.Icc (-(n : ℤ)) n \ {(n : ℤ) - 6, (n : ℤ) - 4, (n : ℤ) - 3, (n : ℤ) - 2, (n : ℤ) - 1,
        (n : ℤ)} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, pattern n (by omega) i, if_neg (show ¬ (n % 2 = 0) by omega),
      decide_eq_true_eq, O, List.mem_cons, List.mem_nil_iff, or_false]
    omega
  have hsub : ({(n : ℤ) - 6, (n : ℤ) - 4, (n : ℤ) - 3, (n : ℤ) - 2, (n : ℤ) - 1, (n : ℤ)} :
      Finset ℤ) ⊆ Finset.Icc (-(n : ℤ)) n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc]
    omega
  have h6 : ({(n : ℤ) - 6, (n : ℤ) - 4, (n : ℤ) - 3, (n : ℤ) - 2, (n : ℤ) - 1, (n : ℤ)} :
      Finset ℤ).card = 6 := by
    rw [Finset.card_insert_of_notMem (by simp <;> omega), Finset.card_insert_of_notMem (by simp <;> omega),
      Finset.card_insert_of_notMem (by simp <;> omega), Finset.card_insert_of_notMem (by simp <;> omega),
      Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
  rw [hf, Finset.card_sdiff_of_subset hsub, h6, Int.card_Icc]
  omega

lemma values : a 0 = 1 ∧ a 1 = 0 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 4 ∧ a 5 = 5 ∧ a 6 = 4 ∧ a 7 = 9 := by
  decide

/-- Barker's closed form, for every `n > 3`. -/
theorem closed_form (n : ℕ) (hn : 3 < n) :
    (a n : ℚ) = (-2 * (-1) ^ n * n + 2 * n + 9 * (-1) ^ n - 1) / 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · rw [a_even n hn he, Even.neg_one_pow (Nat.even_iff.mpr he)]; ring
  · rcases (by omega : n = 4 ∨ 5 ≤ n) with h4 | h5
    · omega
    · have h := a_odd n h5 ho
      have h' : (a n : ℚ) = 2 * n - 5 := by exact_mod_cast h
      rw [h', Odd.neg_one_pow (Nat.odd_iff.mpr ho)]; ring

/-- Barker's recurrence, for every `n > 7`. -/
theorem recurrence (n : ℕ) (hn : 7 < n) : (a n : ℤ) = 2 * a (n - 2) - a (n - 4) := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · rw [a_even n (by omega) he, a_even (n - 2) (by omega) (by omega),
      a_even (n - 4) (by omega) (by omega)]; norm_num
  · rw [a_odd n (by omega) ho, a_odd (n - 2) (by omega) (by omega),
      a_odd (n - 4) (by omega) (by omega)]
    push_cast [show 2 ≤ n by omega, show 4 ≤ n by omega]
    ring

open PowerSeries in
/-- Barker's g.f. `(1+2x^3+x^4+x^5-2x^6+x^7)/((1-x)^2(1+x)^2)`, as an identity in `ℚ⟦X⟧`. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) =
    (1 + 2 * X ^ 3 + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7) * ((1 - X) ^ 2 * (1 + X) ^ 2)⁻¹ := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))
  have hden : constantCoeff ((1 - X) ^ 2 * (1 + X) ^ 2 : ℚ⟦X⟧) ≠ 0 := by simp
  have key : A * ((1 - X) ^ 2 * (1 + X) ^ 2) =
      1 + X ^ 3 + X ^ 3 + X ^ 4 + X ^ 5 - X ^ 6 - X ^ 6 + X ^ 7 := by
    have e1 : A * ((1 - X) ^ 2 * (1 + X) ^ 2) = A - A * X ^ 2 - A * X ^ 2 + A * X ^ 4 := by ring
    rw [e1]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_one, coeff_X_pow, A, coeff_mk]
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := values
    rcases Nat.lt_or_ge n 8 with hn | hn
    · interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7] <;> norm_num
    · rw [if_pos (by omega), if_pos (by omega)]
      simp only [show n ≠ 0 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega,
        show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, if_false]
      have hr := recurrence n (by omega)
      have : (a n : ℚ) = 2 * a (n - 2) - a (n - 4) := by exact_mod_cast hr
      rw [this]; ring
  have hN : (1 + 2 * X ^ 3 + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) =
      1 + X ^ 3 + X ^ 3 + X ^ 4 + X ^ 5 - X ^ 6 - X ^ 6 + X ^ 7 := by ring
  rw [hN, ← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]

end OMA.S_oeis_a266249

theorem OMA.solution : type_of% @OMA.S_oeis_a266249.main :=
  ⟨fun n hn => OMA.S_oeis_a266249.closed_form n hn,
    fun n hn => OMA.S_oeis_a266249.recurrence n hn, OMA.S_oeis_a266249.gf⟩
