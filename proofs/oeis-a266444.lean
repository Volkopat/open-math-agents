import OMAStatements.S_oeis_a266444

namespace OMA.S_oeis_a266444

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

lemma a_even (s : ℕ) (hs : 2 ≤ s) : a (2 * s) = if (-(s : ℤ)) ∈ E then 1 else 0 := by
  unfold a
  rw [(pattern s hs).1 0]
  simp

lemma a_odd (s : ℕ) (hs : 2 ≤ s) : a (2 * s + 1) = if (-(s : ℤ)) ∈ O then 0 else 1 := by
  unfold a
  rw [(pattern s hs).2 0]
  by_cases h : (-(s : ℤ)) ∈ O <;> simp [h]

lemma a_even_big (s : ℕ) (hs : 5 ≤ s) : a (2 * s) = 0 := by
  rw [a_even s (by omega), if_neg]
  simp only [E, List.mem_cons, List.mem_nil_iff, or_false]
  omega

lemma a_odd_big (s : ℕ) (hs : 6 ≤ s) : a (2 * s + 1) = 1 := by
  rw [a_odd s (by omega), if_neg]
  simp only [O, List.mem_cons, List.mem_nil_iff, or_false]
  omega

/-- Barker's closed form, for n > 11. -/
theorem closed_form (n : ℕ) (hn : 11 < n) : (a n : ℚ) = (1 - (-1) ^ n) / 2 := by
  rcases Nat.even_or_odd n with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [show n = 2 * s by omega, a_even_big s (by omega), pow_mul]
    norm_num
  · rw [hs, a_odd_big s (by omega), pow_succ, pow_mul]
    norm_num

/-- Barker's recurrence, for n > 13. -/
theorem recurrence (n : ℕ) (hn : 13 < n) : a n = a (n - 2) := by
  rcases Nat.even_or_odd n with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [show n = 2 * s by omega, show 2 * s - 2 = 2 * (s - 1) by omega,
      a_even_big s (by omega), a_even_big (s - 1) (by omega)]
  · rw [hs, show 2 * s + 1 - 2 = 2 * (s - 1) + 1 by omega,
      a_odd_big s (by omega), a_odd_big (s - 1) (by omega)]

lemma values : a 0 = 1 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 ∧ a 4 = 1 ∧ a 5 = 0 ∧ a 6 = 1 ∧ a 7 = 0 ∧
    a 8 = 1 ∧ a 9 = 1 ∧ a 10 = 0 ∧ a 11 = 0 ∧ a 12 = 0 ∧ a 13 = 1 := by
  have h1 : a 1 = 0 := by unfold a; rw [s1]; decide
  have h2 : a 2 = 0 := by unfold a; rw [s2]; decide
  have h3 : a 3 = 0 := by unfold a; rw [s3]; decide
  refine ⟨by decide, h1, h2, h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 4 = 2 * 2 from rfl, a_even 2 le_rfl]; decide
  · rw [show 5 = 2 * 2 + 1 from rfl, a_odd 2 le_rfl]; decide
  · rw [show 6 = 2 * 3 from rfl, a_even 3 (by norm_num)]; decide
  · rw [show 7 = 2 * 3 + 1 from rfl, a_odd 3 (by norm_num)]; decide
  · rw [show 8 = 2 * 4 from rfl, a_even 4 (by norm_num)]; decide
  · rw [show 9 = 2 * 4 + 1 from rfl, a_odd 4 (by norm_num)]; decide
  · rw [show 10 = 2 * 5 from rfl, a_even 5 (by norm_num)]; decide
  · rw [show 11 = 2 * 5 + 1 from rfl, a_odd 5 (by norm_num)]; decide
  · rw [show 12 = 2 * 6 from rfl, a_even 6 (by norm_num)]; decide
  · rw [show 13 = 2 * 6 + 1 from rfl, a_odd 6 (by norm_num)]; decide

/-- Barker's g.f., as an identity in Q[[x]]. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) =
    (1 - X ^ 2 + X ^ 4 + X ^ 9 - X ^ 10 - X ^ 11 + X ^ 13) * ((1 - X) * (1 + X))⁻¹ := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have hden : constantCoeff ((1 - X) * (1 + X) : ℚ⟦X⟧) ≠ 0 := by simp
  have key : A * ((1 - X) * (1 + X)) = 1 - X ^ 2 + X ^ 4 + X ^ 9 - X ^ 10 - X ^ 11 + X ^ 13 := by
    have e1 : A * ((1 - X) * (1 + X)) = A - A * X ^ 2 := by ring
    rw [e1]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_one, coeff_X_pow, hA, coeff_mk]
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13⟩ := values
    rcases Nat.lt_or_ge n 14 with hn | hn
    · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13]
    · rw [if_pos (by omega)]
      simp only [show n ≠ 0 by omega, show n ≠ 2 by omega, show n ≠ 4 by omega,
        show n ≠ 9 by omega, show n ≠ 10 by omega, show n ≠ 11 by omega, show n ≠ 13 by omega,
        if_false]
      rw [recurrence n (by omega)]
      ring
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]

/-- All three of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 11 < n → (a n : ℚ) = (1 - (-1) ^ n) / 2) ∧
    (∀ n : ℕ, 13 < n → a n = a (n - 2)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 - X ^ 2 + X ^ 4 + X ^ 9 - X ^ 10 - X ^ 11 + X ^ 13) * ((1 - X) * (1 + X))⁻¹ :=
  ⟨closed_form, recurrence, gf⟩

end OMA.S_oeis_a266444

theorem OMA.solution : type_of% @OMA.S_oeis_a266444.main :=
  OMA.S_oeis_a266444.conjecture
