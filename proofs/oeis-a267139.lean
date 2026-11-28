import OMAStatements.S_oeis_a267139

namespace OMA.S_oeis_a267139

open PowerSeries




lemma state_succ (t : ℕ) (i : ℤ) :
    state (t + 1) i = rule (state t (i - 1)) (state t i) (state t (i + 1)) := rfl

/-- Relative ON cells of the even stages and relative OFF cells of the odd stages. -/
def E : List ℤ := [-5, -3, -2, -1, 0]
def O : List ℤ := [-3, -2, -1, 1]

lemma s1 (i : ℤ) : state 1 i = decide (i ∉ [(1 : ℤ)]) := by
  show rule (decide (i - 1 = 0)) (decide (i = 0)) (decide (i + 1 = 0)) = _
  rcases (by omega : i ≤ -2 ∨ (-1 ≤ i ∧ i ≤ 2) ∨ 3 ≤ i) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_false (by omega : ¬ i - 1 = 0), decide_eq_false (by omega : ¬ i = 0),
      decide_eq_false (by omega : ¬ i + 1 = 0), decide_eq_true (by simp; omega)]; decide
  · interval_cases i <;> decide
  · rw [decide_eq_false (by omega : ¬ i - 1 = 0), decide_eq_false (by omega : ¬ i = 0),
      decide_eq_false (by omega : ¬ i + 1 = 0), decide_eq_true (by simp; omega)]; decide

lemma s2 (i : ℤ) : state 2 i = decide (i ∈ [(0 : ℤ), 1]) := by
  rw [state_succ, s1, s1, s1]
  rcases (by omega : i ≤ -3 ∨ (-2 ≤ i ∧ i ≤ 3) ∨ 4 ≤ i) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_true (by simp; omega), decide_eq_true (by simp; omega),
      decide_eq_true (by simp; omega), decide_eq_false (by simp; omega)]; decide
  · interval_cases i <;> decide
  · rw [decide_eq_true (by simp; omega), decide_eq_true (by simp; omega),
      decide_eq_true (by simp; omega), decide_eq_false (by simp; omega)]; decide

lemma s3 (i : ℤ) : state 3 i = decide (i ∉ [(0 : ℤ), 2]) := by
  rw [state_succ, s2, s2, s2]
  rcases (by omega : i ≤ -3 ∨ (-2 ≤ i ∧ i ≤ 4) ∨ 5 ≤ i) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_false (by simp; omega), decide_eq_false (by simp; omega),
      decide_eq_false (by simp; omega), decide_eq_true (by simp; omega)]; decide
  · interval_cases i <;> decide
  · rw [decide_eq_false (by simp; omega), decide_eq_false (by simp; omega),
      decide_eq_false (by simp; omega), decide_eq_true (by simp; omega)]; decide

lemma s4 (i : ℤ) : state 4 i = decide (i ∈ [(-1 : ℤ), 0, 1, 2]) := by
  rw [state_succ, s3, s3, s3]
  rcases (by omega : i ≤ -3 ∨ (-2 ≤ i ∧ i ≤ 4) ∨ 5 ≤ i) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_true (by simp; omega), decide_eq_true (by simp; omega),
      decide_eq_true (by simp; omega), decide_eq_false (by simp; omega)]; decide
  · interval_cases i <;> decide
  · rw [decide_eq_true (by simp; omega), decide_eq_true (by simp; omega),
      decide_eq_true (by simp; omega), decide_eq_false (by simp; omega)]; decide

lemma s5 (i : ℤ) : state 5 i = decide (i - 2 ∉ O) := by
  rw [state_succ, s4, s4, s4]
  rcases (by omega : i ≤ -3 ∨ (-2 ≤ i ∧ i ≤ 5) ∨ 6 ≤ i) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_false (by simp; omega), decide_eq_false (by simp; omega),
      decide_eq_false (by simp; omega), decide_eq_true (by simp [O]; omega)]; decide
  · interval_cases i <;> decide
  · rw [decide_eq_false (by simp; omega), decide_eq_false (by simp; omega),
      decide_eq_false (by simp; omega), decide_eq_true (by simp [O]; omega)]; decide

/-- Even stage to the next odd stage, relative position e. -/
lemma stepEO (e : ℤ) :
    rule (decide (e - 1 ∈ E)) (decide (e ∈ E)) (decide (e + 1 ∈ E)) = decide (e ∉ O) := by
  rcases (by omega : e ≤ -8 ∨ (-7 ≤ e ∧ e ≤ 2) ∨ 3 ≤ e) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_false (by simp [E]; omega), decide_eq_false (by simp [E]; omega),
      decide_eq_false (by simp [E]; omega), decide_eq_true (by simp [O]; omega)]; decide
  · interval_cases e <;> decide
  · rw [decide_eq_false (by simp [E]; omega), decide_eq_false (by simp [E]; omega),
      decide_eq_false (by simp [E]; omega), decide_eq_true (by simp [O]; omega)]; decide

/-- Odd stage to the next even stage, relative position e (the frame moves by one). -/
lemma stepOE (e : ℤ) :
    rule (decide (e - 1 ∉ O)) (decide (e ∉ O)) (decide (e + 1 ∉ O)) = decide (e - 1 ∈ E) := by
  rcases (by omega : e ≤ -6 ∨ (-5 ≤ e ∧ e ≤ 3) ∨ 4 ≤ e) with h | ⟨h1, h2⟩ | h
  · rw [decide_eq_true (by simp [O]; omega), decide_eq_true (by simp [O]; omega),
      decide_eq_true (by simp [O]; omega), decide_eq_false (by simp [E]; omega)]; decide
  · interval_cases e <;> decide
  · rw [decide_eq_true (by simp [O]; omega), decide_eq_true (by simp [O]; omega),
      decide_eq_true (by simp [O]; omega), decide_eq_false (by simp [E]; omega)]; decide

/-- The glider: stages 2s + 1 and 2s + 2 for s >= 2. -/
lemma pattern (s : ℕ) (hs : 2 ≤ s) :
    (∀ i, state (2 * s + 1) i = decide (i - s ∉ O)) ∧
      (∀ i, state (2 * s + 2) i = decide (i - (s + 1) ∈ E)) := by
  have even_of_odd : ∀ s : ℕ, (∀ i, state (2 * s + 1) i = decide (i - s ∉ O)) →
      ∀ i, state (2 * s + 2) i = decide (i - (s + 1) ∈ E) := by
    intro s h i
    rw [state_succ, h, h, h]
    have e1 : i - 1 - (s : ℤ) = (i - s) - 1 := by ring
    have e2 : i + 1 - (s : ℤ) = (i - s) + 1 := by ring
    have e3 : i - ((s : ℤ) + 1) = (i - s) - 1 := by ring
    rw [e1, e2, e3, stepOE]
  induction s, hs using Nat.le_induction with
  | base =>
    have h5 : ∀ i, state (2 * 2 + 1) i = decide (i - ((2 : ℕ) : ℤ) ∉ O) := fun i => by
      rw [s5]; norm_num
    exact ⟨h5, even_of_odd 2 h5⟩
  | succ s hs ih =>
    have hodd : ∀ i, state (2 * (s + 1) + 1) i = decide (i - ((s + 1 : ℕ) : ℤ) ∉ O) := by
      intro i
      rw [show 2 * (s + 1) + 1 = (2 * s + 2) + 1 by ring, state_succ, ih.2, ih.2, ih.2]
      have e1 : i - 1 - ((s : ℤ) + 1) = (i - ((s + 1 : ℕ) : ℤ)) - 1 := by push_cast; ring
      have e2 : i - ((s : ℤ) + 1) = i - ((s + 1 : ℕ) : ℤ) := by push_cast; ring
      have e3 : i + 1 - ((s : ℤ) + 1) = (i - ((s + 1 : ℕ) : ℤ)) + 1 := by push_cast; ring
      rw [e1, e2, e3, stepEO]
    exact ⟨hodd, even_of_odd (s + 1) hodd⟩

lemma state_even (s : ℕ) (hs : 3 ≤ s) (i : ℤ) : state (2 * s) i = decide (i - s ∈ E) := by
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
  have := (pattern r (by omega)).2 i
  rw [show 2 * (r + 1) = 2 * r + 2 by ring, this]
  push_cast
  ring_nf

lemma state_odd (s : ℕ) (hs : 2 ≤ s) (i : ℤ) : state (2 * s + 1) i = decide (i - s ∉ O) :=
  (pattern s hs).1 i

lemma sum_pow_two (m : ℕ) : ∑ k ∈ Finset.range m, (2 : ℤ) ^ k = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

lemma a_even (s : ℕ) (hs : 3 ≤ s) : a (2 * s) = 47 * 2 ^ s := by
  unfold a
  have hf : (Finset.range (2 * (2 * s) + 1)).filter
      (fun k : ℕ => state (2 * s) ((k : ℤ) - ((2 * s : ℕ) : ℤ)) = true) =
      {3 * s - 5, 3 * s - 3, 3 * s - 2, 3 * s - 1, 3 * s} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, state_even s hs, decide_eq_true_eq, E,
      List.mem_cons, List.mem_nil_iff, or_false, Finset.mem_insert, Finset.mem_singleton]
    push_cast
    omega
  rw [← Finset.sum_filter, hf]
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
    Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
    Finset.sum_singleton]
  rw [show 2 * (2 * s) - (3 * s - 5) = s + 5 by omega, show 2 * (2 * s) - (3 * s - 3) = s + 3 by omega,
    show 2 * (2 * s) - (3 * s - 2) = s + 2 by omega, show 2 * (2 * s) - (3 * s - 1) = s + 1 by omega,
    show 2 * (2 * s) - 3 * s = s by omega]
  ring

lemma a_odd (s : ℕ) (hs : 2 ≤ s) : (a (2 * s + 1) : ℤ) = 2 ^ (4 * s + 3) - 1 - 29 * 2 ^ s := by
  set R := Finset.range (2 * (2 * s + 1) + 1) with hR
  set w : ℕ → ℤ := fun k => 2 ^ (2 * (2 * s + 1) - k) with hw
  have hsplit : ∑ k ∈ R, (if state (2 * s + 1) ((k : ℤ) - ((2 * s + 1 : ℕ) : ℤ)) then w k else 0) =
      ∑ k ∈ R, w k - ∑ k ∈ R.filter
        (fun k : ℕ => ¬ state (2 * s + 1) ((k : ℤ) - ((2 * s + 1 : ℕ) : ℤ)) = true), w k := by
    rw [← Finset.sum_filter, eq_sub_iff_add_eq, Finset.sum_filter_add_sum_filter_not]
  have hoff : R.filter
      (fun k : ℕ => ¬ state (2 * s + 1) ((k : ℤ) - ((2 * s + 1 : ℕ) : ℤ)) = true) =
      {3 * s - 2, 3 * s - 1, 3 * s, 3 * s + 2} := by
    ext k
    simp only [hR, Finset.mem_filter, Finset.mem_range, state_odd s hs, decide_eq_true_eq, O,
      List.mem_cons, List.mem_nil_iff, or_false, not_not, Finset.mem_insert,
      Finset.mem_singleton]
    push_cast
    omega
  have htot : ∑ k ∈ R, w k = 2 ^ (4 * s + 3) - 1 := by
    rw [hR, hw, ← Finset.sum_range_reflect]
    have : ∀ k ∈ Finset.range (2 * (2 * s + 1) + 1),
        (2 : ℤ) ^ (2 * (2 * s + 1) - (2 * (2 * s + 1) + 1 - 1 - k)) = 2 ^ k := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show 2 * (2 * s + 1) - (2 * (2 * s + 1) + 1 - 1 - k) = k by omega]
    rw [Finset.sum_congr rfl this, sum_pow_two]
    ring_nf
  have hcast : (a (2 * s + 1) : ℤ) =
      ∑ k ∈ R, (if state (2 * s + 1) ((k : ℤ) - ((2 * s + 1 : ℕ) : ℤ)) then w k else 0) := by
    unfold a
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    split_ifs <;> try simp [hw]
  rw [hcast, hsplit, htot, hoff]
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
    Finset.sum_insert (by simp), Finset.sum_singleton]
  simp only [hw]
  rw [show 2 * (2 * s + 1) - (3 * s - 2) = s + 4 by omega,
    show 2 * (2 * s + 1) - (3 * s - 1) = s + 3 by omega,
    show 2 * (2 * s + 1) - 3 * s = s + 2 by omega,
    show 2 * (2 * s + 1) - (3 * s + 2) = s by omega]
  ring

lemma values : a 0 = 1 ∧ a 1 = 6 ∧ a 2 = 6 ∧ a 3 = 117 ∧ a 4 = 60 := by
  decide

/-- The closed forms on both residue classes, in Z. -/
lemma cf_even (s : ℕ) (hs : 3 ≤ s) : (a (2 * s) : ℤ) = 47 * 2 ^ s := by
  rw [a_even s hs]; push_cast; ring

/-- Barker's recurrence, for n > 10. -/
theorem recurrence (n : ℕ) (hn : 10 < n) :
    (a n : ℤ) = 19 * a (n - 2) - 50 * a (n - 4) + 32 * a (n - 6) := by
  rcases Nat.even_or_odd n with ⟨s, hs⟩ | ⟨s, hs⟩
  · obtain ⟨m, rfl⟩ : ∃ m, s = m + 6 := ⟨s - 6, by omega⟩
    subst hs
    rw [show m + 6 + (m + 6) - 2 = 2 * (m + 5) by omega,
      show m + 6 + (m + 6) - 4 = 2 * (m + 4) by omega,
      show m + 6 + (m + 6) - 6 = 2 * (m + 3) by omega,
      show m + 6 + (m + 6) = 2 * (m + 6) by omega,
      cf_even _ (by omega), cf_even _ (by omega), cf_even _ (by omega), cf_even _ (by omega)]
    ring
  · obtain ⟨m, rfl⟩ : ∃ m, s = m + 5 := ⟨s - 5, by omega⟩
    subst hs
    rw [show 2 * (m + 5) + 1 - 2 = 2 * (m + 4) + 1 by omega,
      show 2 * (m + 5) + 1 - 4 = 2 * (m + 3) + 1 by omega,
      show 2 * (m + 5) + 1 - 6 = 2 * (m + 2) + 1 by omega,
      a_odd _ (by omega), a_odd _ (by omega), a_odd _ (by omega), a_odd _ (by omega)]
    ring

lemma values2 : a 5 = 1931 ∧ a 6 = 376 ∧ a 7 = 32535 ∧ a 8 = 752 ∧ a 9 = 523823 ∧
    a 10 = 1504 := by
  have h5 := a_odd 2 (by norm_num)
  have h7 := a_odd 3 (by norm_num)
  have h9 := a_odd 4 (by norm_num)
  norm_num at h5 h7 h9
  refine ⟨by exact_mod_cast h5, ?_, by exact_mod_cast h7, ?_, by exact_mod_cast h9, ?_⟩
  · have := a_even 3 (by norm_num); norm_num at this; exact this
  · have := a_even 4 (by norm_num); norm_num at this; exact this
  · have := a_even 5 (by norm_num); norm_num at this; exact this

/-- Barker's g.f., as an identity in Q[[x]]. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) =
    (1 + 6 * X - 13 * X ^ 2 + 3 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 496 * X ^ 6 + 1504 * X ^ 7 -
      3584 * X ^ 8 - 1536 * X ^ 9 + 4096 * X ^ 10) *
      ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2))⁻¹ := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have hden : constantCoeff ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2) :
      ℚ⟦X⟧) ≠ 0 := by simp
  have key : A * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2)) =
      (1 + 6 * X - 13 * X ^ 2 + 3 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 496 * X ^ 6 + 1504 * X ^ 7 -
        3584 * X ^ 8 - 1536 * X ^ 9 + 4096 * X ^ 10) := by
    have e1 : A * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2)) =
        A - C 19 * (A * X ^ 2) + C 50 * (A * X ^ 4) - C 32 * (A * X ^ 6) := by
      simp only [map_ofNat]; ring
    have e2 : (1 + 6 * X - 13 * X ^ 2 + 3 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 496 * X ^ 6 +
        1504 * X ^ 7 - 3584 * X ^ 8 - 1536 * X ^ 9 + 4096 * X ^ 10 : ℚ⟦X⟧) =
        1 + X ^ 1 * C 6 - X ^ 2 * C 13 + X ^ 3 * C 3 - X ^ 4 * C 4 + X ^ 5 * C 8 -
          X ^ 6 * C 496 + X ^ 7 * C 1504 - X ^ 8 * C 3584 - X ^ 9 * C 1536 +
          X ^ 10 * C 4096 := by
      simp only [map_ofNat]; ring
    rw [e1, e2]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', coeff_one,
      coeff_X_pow, hA, coeff_mk]
    obtain ⟨v0, v1, v2, v3, v4⟩ := values
    obtain ⟨v5, v6, v7, v8, v9, v10⟩ := values2
    rcases Nat.lt_or_ge n 11 with hn | hn
    · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
        show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega,
        show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega,
        if_false]
      have hr := recurrence n (by omega)
      have : (a n : ℚ) = 19 * a (n - 2) - 50 * a (n - 4) + 32 * a (n - 6) := by exact_mod_cast hr
      rw [this]; ring
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]

/-- Controls: the entry's data a(0..13). -/
theorem controls : a 0 = 1 ∧ a 1 = 6 ∧ a 2 = 6 ∧ a 3 = 117 ∧ a 4 = 60 ∧ a 5 = 1931 ∧
    a 6 = 376 ∧ a 7 = 32535 ∧ a 8 = 752 ∧ a 9 = 523823 ∧ a 10 = 1504 ∧ a 11 = 8387679 ∧
    a 12 = 3008 ∧ a 13 = 134215871 := by
  obtain ⟨v0, v1, v2, v3, v4⟩ := values
  obtain ⟨v5, v6, v7, v8, v9, v10⟩ := values2
  have h11 : (a 11 : ℤ) = 8387679 := by
    rw [show (11 : ℕ) = 2 * 5 + 1 from rfl, a_odd 5 (by norm_num)]; norm_num
  have h13 : (a 13 : ℤ) = 134215871 := by
    rw [show (13 : ℕ) = 2 * 6 + 1 from rfl, a_odd 6 (by norm_num)]; norm_num
  have h12 : a 12 = 3008 := by
    rw [show (12 : ℕ) = 2 * 6 from rfl, a_even 6 (by norm_num)]
    norm_num
  exact ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, by exact_mod_cast h11, h12,
    by exact_mod_cast h13⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 10 < n → (a n : ℤ) = 19 * a (n - 2) - 50 * a (n - 4) + 32 * a (n - 6)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 + 6 * X - 13 * X ^ 2 + 3 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 496 * X ^ 6 + 1504 * X ^ 7 -
        3584 * X ^ 8 - 1536 * X ^ 9 + 4096 * X ^ 10) *
        ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2))⁻¹ :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a267139

theorem OMA.solution : type_of% @OMA.S_oeis_a267139.main :=
  OMA.S_oeis_a267139.conjecture
