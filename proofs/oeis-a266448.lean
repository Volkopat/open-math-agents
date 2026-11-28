import OMAStatements.S_oeis_a266448

namespace OMA.S_oeis_a266448

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

lemma cnt_even (s : ℕ) (hs : 2 ≤ s) : cnt (2 * s) = 4 := by
  unfold cnt
  have hf : (Finset.Icc (-((2 * s : ℕ) : ℤ)) ((2 * s : ℕ) : ℤ)).filter
      (fun i => state (2 * s) i) =
      {(s : ℤ) - 4, (s : ℤ) - 3, (s : ℤ) - 2, (s : ℤ)} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
      (pattern s hs).1 i, decide_eq_true_eq, E, List.mem_cons, List.mem_nil_iff, or_false]
    push_cast
    omega
  rw [hf, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp), Finset.card_singleton]

lemma cnt_odd (s : ℕ) (hs : 2 ≤ s) : (cnt (2 * s + 1) : ℤ) = 4 * s - 2 := by
  unfold cnt
  have hf : (Finset.Icc (-((2 * s + 1 : ℕ) : ℤ)) ((2 * s + 1 : ℕ) : ℤ)).filter
      (fun i => state (2 * s + 1) i) =
      Finset.Icc (-((2 * s + 1 : ℕ) : ℤ)) ((2 * s + 1 : ℕ) : ℤ) \
        {(s : ℤ) - 5, (s : ℤ) - 3, (s : ℤ) - 2, (s : ℤ) - 1, (s : ℤ)} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, (pattern s hs).2 i, decide_eq_true_eq, O, List.mem_cons,
      List.mem_nil_iff, or_false]
    push_cast
    omega
  have hsub : ({(s : ℤ) - 5, (s : ℤ) - 3, (s : ℤ) - 2, (s : ℤ) - 1, (s : ℤ)} : Finset ℤ) ⊆
      Finset.Icc (-((2 * s + 1 : ℕ) : ℤ)) ((2 * s + 1 : ℕ) : ℤ) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc]
    push_cast
    omega
  have h5 : ({(s : ℤ) - 5, (s : ℤ) - 3, (s : ℤ) - 2, (s : ℤ) - 1, (s : ℤ)} :
      Finset ℤ).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
      Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
      Finset.card_singleton]
  rw [hf, Finset.card_sdiff_of_subset hsub, h5, Int.card_Icc]
  have : (2 * s + 1 : ℕ) + 1 - (-((2 * s + 1 : ℕ) : ℤ)) = ((4 * s + 3 : ℕ) : ℤ) := by
    push_cast; ring
  rw [this, Int.toNat_natCast]
  push_cast
  omega

lemma cnt_vals : cnt 0 = 1 ∧ cnt 1 = 1 ∧ cnt 2 = 2 ∧ cnt 3 = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cnt
    rw [show (Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ)).filter (fun i => state 0 i) = {0} by
      decide]
    rfl
  · unfold cnt
    rw [show (Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)).filter (fun i => state 1 i) = {1} by
      decide]
    rfl
  · unfold cnt
    rw [show (Finset.Icc (-((2 : ℕ) : ℤ)) ((2 : ℕ) : ℤ)).filter (fun i => state 2 i) =
      {-1, 1} by decide]
    rfl
  · unfold cnt
    rw [show (Finset.Icc (-((3 : ℕ) : ℤ)) ((3 : ℕ) : ℤ)).filter (fun i => state 3 i) =
      {-3, 2, 3} by decide]
    rfl

lemma a_succ (n : ℕ) : a (n + 1) = a n + cnt (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ]

/-- The closed form in Q, F(n) = (2n^2 + 2n + (-1)^n (7 - 2n) + 5)/4. -/
noncomputable def F (n : ℕ) : ℚ := (2 * n ^ 2 + 2 * n + (-1) ^ n * (7 - 2 * n) + 5) / 4

/-- Barker's closed form, for n > 2. -/
theorem closed_form (n : ℕ) (hn : 2 < n) :
    (a n : ℚ) = (2 * n ^ 2 + 2 * n + (-1) ^ n * (7 - 2 * n) + 5) / 4 := by
  induction n, hn using Nat.le_induction with
  | base =>
    obtain ⟨c0, c1, c2, c3⟩ := cnt_vals
    have : a 3 = 7 := by
      unfold a
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3]
    rw [this]
    norm_num
  | succ n hn ih =>
    rw [a_succ]
    push_cast
    rw [ih]
    rcases Nat.even_or_odd (n + 1) with ⟨s, hs⟩ | ⟨s, hs⟩
    · have h2 : 2 ≤ s := by omega
      have hc : cnt (n + 1) = 4 := by rw [show n + 1 = 2 * s by omega]; exact cnt_even s h2
      rw [hc]
      have hpar : (-1 : ℚ) ^ n = -1 := by
        rw [Odd.neg_one_pow]; exact ⟨s - 1, by omega⟩
      have hpar' : (-1 : ℚ) ^ (n + 1) = 1 := by
        rw [Even.neg_one_pow]; exact ⟨s, by omega⟩
      rw [hpar, hpar']
      push_cast
      ring
    · have h2 : 2 ≤ s := by omega
      have hc : (cnt (n + 1) : ℚ) = 4 * s - 2 := by
        rw [show n + 1 = 2 * s + 1 by omega]; exact_mod_cast cnt_odd s h2
      rw [hc]
      have hpar : (-1 : ℚ) ^ n = 1 := by
        rw [Even.neg_one_pow]; exact ⟨s, by omega⟩
      have hpar' : (-1 : ℚ) ^ (n + 1) = -1 := by
        rw [Odd.neg_one_pow]; exact ⟨s, by omega⟩
      have hs' : (s : ℚ) = n / 2 := by
        have : (n : ℚ) = 2 * s := by exact_mod_cast (show n = 2 * s by omega)
        linarith
      rw [hpar, hpar', hs']
      ring

/-- Barker's recurrence, for n > 7. -/
theorem recurrence (n : ℕ) (hn : 7 < n) :
    (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  have hq : (a (m + 8) : ℚ) = a (m + 7) + 2 * a (m + 6) - 2 * a (m + 5) - a (m + 4) +
      a (m + 3) := by
    rw [closed_form (m + 8) (by omega), closed_form (m + 7) (by omega),
      closed_form (m + 6) (by omega), closed_form (m + 5) (by omega),
      closed_form (m + 4) (by omega), closed_form (m + 3) (by omega)]
    push_cast
    ring
  rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
    show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega,
    show m + 8 - 5 = m + 3 by omega]
  exact_mod_cast hq

lemma values : a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 4 ∧ a 3 = 7 ∧ a 4 = 11 ∧ a 5 = 17 ∧ a 6 = 21 ∧
    a 7 = 31 := by
  obtain ⟨c0, c1, c2, c3⟩ := cnt_vals
  have h4 := cnt_even 2 (by norm_num)
  have h5 := cnt_odd 2 (by norm_num)
  have h6 := cnt_even 3 (by norm_num)
  have h7 := cnt_odd 3 (by norm_num)
  norm_num at h4 h5 h6 h7
  have h5' : cnt 5 = 6 := by exact_mod_cast h5
  have h7' : cnt 7 = 10 := by exact_mod_cast h7
  unfold a
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, h4, h5', h6, h7']
  norm_num

/-- Barker's g.f., as an identity in Q[[x]]. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) =
    (1 + X + X ^ 3 + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7) * ((1 - X) ^ 3 * (1 + X) ^ 2)⁻¹ := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have hden : constantCoeff ((1 - X) ^ 3 * (1 + X) ^ 2 : ℚ⟦X⟧) ≠ 0 := by simp
  have key : A * ((1 - X) ^ 3 * (1 + X) ^ 2) = 1 + X + X ^ 3 + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7 := by
    have e1 : A * ((1 - X) ^ 3 * (1 + X) ^ 2) =
        A - A * X ^ 1 - C 2 * (A * X ^ 2) + C 2 * (A * X ^ 3) + A * X ^ 4 - A * X ^ 5 := by
      simp only [map_ofNat]; ring
    have e2 : (1 + X + X ^ 3 + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) =
        1 + X ^ 1 + X ^ 3 + X ^ 4 + X ^ 5 - X ^ 6 * C 2 + X ^ 7 := by
      simp only [map_ofNat]; ring
    rw [e1, e2]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', coeff_one,
      coeff_X_pow, hA, coeff_mk]
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := values
    rcases Nat.lt_or_ge n 8 with hn | hn
    · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
        if_pos (by omega)]
      simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 3 by omega,
        show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega,
        if_false]
      have hr := recurrence n (by omega)
      have : (a n : ℚ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
        exact_mod_cast hr
      rw [this]; ring
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]

/-- Controls: the entry's data a(0..20). -/
theorem controls : (List.range 21).map (fun n => (a n : ℚ)) =
    [1, 2, 4, 7, 11, 17, 21, 31, 35, 49, 53, 71, 75, 97, 101, 127, 131, 161, 165, 199, 203] := by
  obtain ⟨v0, v1, v2⟩ : a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 4 := ⟨values.1, values.2.1, values.2.2.1⟩
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append]
  rw [v0, v1, v2]
  simp only [List.cons.injEq, and_true]
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [closed_form _ (by norm_num)] <;> norm_num

/-- All three of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 2 < n → (a n : ℚ) = (2 * n ^ 2 + 2 * n + (-1) ^ n * (7 - 2 * n) + 5) / 4) ∧
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 + X + X ^ 3 + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7) * ((1 - X) ^ 3 * (1 + X) ^ 2)⁻¹ :=
  ⟨closed_form, recurrence, gf⟩

end OMA.S_oeis_a266448

theorem OMA.solution : type_of% @OMA.S_oeis_a266448.main :=
  OMA.S_oeis_a266448.conjecture
