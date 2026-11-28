import OMAStatements.S_oeis_a195609

namespace OMA.S_oeis_a195609




/-! ## Thue-Morse -/

/-- Parity of the binary digit sum (the Thue-Morse sequence A010060). -/
def tm (n : ℕ) : ℕ := (Nat.digits 2 n).sum % 2

lemma ds_double_add_one (j : ℕ) :
    (Nat.digits 2 (2 * j + 1)).sum = 1 + (Nat.digits 2 j).sum := by
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * j + 1) % 2 = 1 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  rw [h1, h2, List.sum_cons]

lemma ds_double (j : ℕ) : (Nat.digits 2 (2 * j)).sum = (Nat.digits 2 j).sum := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [Nat.digits_def' (by norm_num) (by omega)]
    have h1 : (2 * j) % 2 = 0 := by omega
    have h2 : (2 * j) / 2 = j := by omega
    rw [h1, h2, List.sum_cons, zero_add]

lemma tm_le_one (n : ℕ) : tm n ≤ 1 := by unfold tm; omega

lemma tm_double (j : ℕ) : tm (2 * j) = tm j := by
  unfold tm; rw [ds_double]

lemma tm_double_add_one (j : ℕ) : tm (2 * j + 1) = 1 - tm j := by
  unfold tm; rw [ds_double_add_one]; omega

lemma tm_zero : tm 0 = 0 := by simp [tm]

/-- No three consecutive equal values. -/
lemma no_three (k : ℕ) (h1 : tm k = tm (k + 1)) (h2 : tm (k + 1) = tm (k + 2)) : False := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have a := tm_double j
    have b := tm_double_add_one j
    have c := tm_le_one j
    omega
  · have e1 : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
    have e2 : 2 * j + 1 + 2 = 2 * (j + 1) + 1 := by ring
    rw [e1] at h1 h2
    rw [e2] at h2
    have a := tm_double (j + 1)
    have b := tm_double_add_one (j + 1)
    have c := tm_le_one (j + 1)
    omega

/-! ## The odious numbers -/

/-- The odious predicate used in `A`. -/
abbrev Od : ℕ → Prop := fun k => (Nat.digits 2 k).sum % 2 = 1

lemma od_iff (k : ℕ) : Od k ↔ tm k = 1 := Iff.rfl

lemma count_double (m : ℕ) : Nat.count Od (2 * m) = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [h, Nat.count_succ, Nat.count_succ, ih]
    have a := tm_double m
    have b := tm_double_add_one m
    have c := tm_le_one m
    by_cases h1 : Od (2 * m) <;> by_cases h2 : Od (2 * m + 1)
    · have h1' : tm (2 * m) = 1 := h1
      have h2' : tm (2 * m + 1) = 1 := h2
      omega
    · have h1' : tm (2 * m) = 1 := h1
      rw [if_pos h1, if_neg h2]
    · have h2' : tm (2 * m + 1) = 1 := h2
      rw [if_neg h1, if_pos h2]
    · have h1' : ¬ tm (2 * m) = 1 := h1
      have h2' : ¬ tm (2 * m + 1) = 1 := h2
      omega

lemma nth_od (k : ℕ) : Nat.nth Od k = 2 * k + (1 - tm k) := by
  have c := tm_le_one k
  have key : Nat.count Od (2 * k + (1 - tm k)) = k ∧ Od (2 * k + (1 - tm k)) := by
    rcases Nat.lt_or_ge (tm k) 1 with h | h
    · have h0 : tm k = 0 := by omega
      rw [h0, Nat.sub_zero]
      have hn : ¬ Od (2 * k) := by
        show ¬ tm (2 * k) = 1
        rw [tm_double]; omega
      refine ⟨?_, ?_⟩
      · rw [Nat.count_succ, count_double, if_neg hn, Nat.add_zero]
      · show tm (2 * k + 1) = 1
        rw [tm_double_add_one]; omega
    · have h1 : tm k = 1 := by omega
      rw [h1, Nat.sub_self, add_zero]
      refine ⟨count_double k, ?_⟩
      show tm (2 * k) = 1
      rw [tm_double]; exact h1
  have := Nat.nth_count key.2
  rw [key.1] at this
  exact this

lemma A_succ (k : ℕ) : A (k + 1) = 2 * k + (1 - tm k) := by
  unfold A
  rw [Nat.add_sub_cancel]
  exact nth_od k

lemma A_odd (m : ℕ) : A (2 * m + 1) = 4 * m + (1 - tm m) := by
  rw [A_succ, tm_double]; ring

lemma A_even (m : ℕ) : A (2 * m + 2) = 4 * m + 2 + tm m := by
  have : 2 * m + 2 = (2 * m + 1) + 1 := by ring
  rw [this, A_succ, tm_double_add_one]
  have := tm_le_one m
  omega

/-! ## Partial sums -/

lemma sum_A (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, A i) + (∑ k ∈ Finset.range n, tm k) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, A_succ]
    have := tm_le_one n
    have e : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    rw [e, ← ih]
    omega

lemma sum_tm_double (m : ℕ) : (∑ k ∈ Finset.range (2 * m), tm k) = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [h, Finset.sum_range_succ, Finset.sum_range_succ, ih, tm_double, tm_double_add_one]
    have := tm_le_one m
    omega

lemma sum_tm_odd (m : ℕ) : (∑ k ∈ Finset.range (2 * m + 1), tm k) = m + tm m := by
  rw [Finset.sum_range_succ, sum_tm_double, tm_double]

/-! ## Characterization of the terms -/

lemma isTerm_iff (n : ℕ) :
    IsTerm n ↔ 1 ≤ n ∧ (∑ i ∈ Finset.Icc 1 n, A i) * 4 = A n * A (n + 1) := by
  unfold IsTerm
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [eq_div_iff (by norm_num : (4 : ℚ) ≠ 0)] at h2
    exact_mod_cast h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [eq_div_iff (by norm_num : (4 : ℚ) ≠ 0)]
    exact_mod_cast h2

lemma term_odd (m : ℕ) : IsTerm (2 * m + 1) ↔ tm m = 1 := by
  rw [isTerm_iff]
  have hs := sum_A (2 * m + 1)
  rw [sum_tm_odd] at hs
  have e : 2 * m + 1 + 1 = 2 * m + 2 := by ring
  rw [e, A_odd, A_even]
  generalize (∑ i ∈ Finset.Icc 1 (2 * m + 1), A i) = S at hs ⊢
  have c := tm_le_one m
  rcases Nat.lt_or_ge (tm m) 1 with h | h
  · have h0 : tm m = 0 := by omega
    rw [h0] at hs ⊢
    constructor
    · rintro ⟨-, h2⟩
      norm_num at h2 hs
      nlinarith
    · intro h; omega
  · have h1 : tm m = 1 := by omega
    rw [h1] at hs ⊢
    constructor
    · intro _; rfl
    · intro _
      refine ⟨by omega, ?_⟩
      norm_num at hs ⊢
      nlinarith

lemma term_even (m : ℕ) : IsTerm (2 * m + 2) ↔ tm m = 1 ∧ tm (m + 1) = 1 := by
  rw [isTerm_iff]
  have hs := sum_A (2 * m + 2)
  have e2 : 2 * m + 2 = 2 * (m + 1) := by ring
  rw [e2, sum_tm_double] at hs
  rw [← e2] at hs
  have e : 2 * m + 2 + 1 = 2 * (m + 1) + 1 := by ring
  rw [e, A_odd, A_even]
  generalize (∑ i ∈ Finset.Icc 1 (2 * m + 2), A i) = S at hs ⊢
  have c := tm_le_one m
  have d := tm_le_one (m + 1)
  rcases Nat.lt_or_ge (tm m) 1 with h | h <;> rcases Nat.lt_or_ge (tm (m + 1)) 1 with h' | h'
  · have h0 : tm m = 0 := by omega
    have h0' : tm (m + 1) = 0 := by omega
    rw [h0, h0']
    constructor
    · rintro ⟨-, h2⟩; norm_num at h2 hs; nlinarith
    · intro h; omega
  · have h0 : tm m = 0 := by omega
    have h1' : tm (m + 1) = 1 := by omega
    rw [h0, h1']
    constructor
    · rintro ⟨-, h2⟩; norm_num at h2 hs; nlinarith
    · intro h; omega
  · have h1 : tm m = 1 := by omega
    have h0' : tm (m + 1) = 0 := by omega
    rw [h1, h0']
    constructor
    · rintro ⟨-, h2⟩; norm_num at h2 hs; nlinarith
    · intro h; omega
  · have h1 : tm m = 1 := by omega
    have h1' : tm (m + 1) = 1 := by omega
    rw [h1, h1']
    constructor
    · intro _; exact ⟨rfl, rfl⟩
    · intro _
      refine ⟨by omega, ?_⟩
      norm_num at hs ⊢
      nlinarith

lemma not_term_zero : ¬ IsTerm 0 := by
  rw [isTerm_iff]; omega

/-! ## The three conjectures -/

lemma tm_vals : tm 1 = 1 ∧ tm 2 = 1 ∧ tm 3 = 0 ∧ tm 4 = 1 ∧ tm 5 = 0 ∧ tm 6 = 0 ∧ tm 7 = 1 := by
  have t1 : tm 1 = 1 := by
    have := tm_double_add_one 0; rw [tm_zero] at this; simpa using this
  have t2 : tm 2 = 1 := by
    have := tm_double 1; rw [t1] at this; simpa using this
  have t3 : tm 3 = 0 := by
    have := tm_double_add_one 1; rw [t1] at this; simpa using this
  have t4 : tm 4 = 1 := by
    have := tm_double 2; rw [t2] at this; simpa using this
  have t5 : tm 5 = 0 := by
    have := tm_double_add_one 2; rw [t2] at this; simpa using this
  have t6 : tm 6 = 0 := by
    have := tm_double 3; rw [t3] at this; simpa using this
  have t7 : tm 7 = 1 := by
    have := tm_double_add_one 3; rw [t3] at this; simpa using this
  exact ⟨t1, t2, t3, t4, t5, t6, t7⟩

lemma tm_eight : tm 8 = 1 := by
  have := tm_double 4; rw [tm_vals.2.2.2.1] at this; simpa using this

/-- Controls from the entry's data: the terms up to 17 are exactly 3, 4, 5, 9, 15, 16, 17. -/
theorem controls : ∀ n, n ≤ 17 → (IsTerm n ↔ n ∈ ({3, 4, 5, 9, 15, 16, 17} : Finset ℕ)) := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := tm_vals
  have t8 := tm_eight
  have t0 := tm_zero
  intro n hn
  interval_cases n
  · simp [not_term_zero]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, term_odd]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (2 : ℕ) = 2 * 0 + 2 from rfl, term_even]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (3 : ℕ) = 2 * 1 + 1 from rfl, term_odd]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (4 : ℕ) = 2 * 1 + 2 from rfl, term_even]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, term_odd]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (6 : ℕ) = 2 * 2 + 2 from rfl, term_even]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (7 : ℕ) = 2 * 3 + 1 from rfl, term_odd]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (8 : ℕ) = 2 * 3 + 2 from rfl, term_even]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (9 : ℕ) = 2 * 4 + 1 from rfl, term_odd]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (10 : ℕ) = 2 * 4 + 2 from rfl, term_even]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (11 : ℕ) = 2 * 5 + 1 from rfl, term_odd]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (12 : ℕ) = 2 * 5 + 2 from rfl, term_even]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (13 : ℕ) = 2 * 6 + 1 from rfl, term_odd]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (14 : ℕ) = 2 * 6 + 2 from rfl, term_even]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (15 : ℕ) = 2 * 7 + 1 from rfl, term_odd]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (16 : ℕ) = 2 * 7 + 2 from rfl, term_even]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show (17 : ℕ) = 2 * 8 + 1 from rfl, term_odd]; simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]

/-- Consecutive terms differ by 1, 4 or 6. -/
lemma diff_cases (m m' : ℕ) (hm : IsTerm m) (hm' : IsTerm m') (hlt : m < m')
    (hgap : ∀ j, m < j → j < m' → ¬ IsTerm j) : m' - m = 1 ∨ m' - m = 4 ∨ m' - m = 6 := by
  -- the first term after m is at m + 1, m + 4 or m + 6
  have next : ∀ j, m < j → IsTerm j → (∀ i, m < i → i < j → ¬ IsTerm i) → m' = j := by
    intro j hj hjt hbelow
    rcases lt_trichotomy m' j with h | h | h
    · exact absurd hm' (hbelow m' hlt h)
    · exact h
    · exact absurd hjt (hgap j hj h)
  rcases Nat.even_or_odd' m with ⟨j, hj | hj⟩
  · -- m even, so m = 2(j-1)+2 and m+1 is a term
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp at hj; subst hj; exact absurd hm not_term_zero
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hm2 : m = 2 * i + 2 := by omega
    subst hm2
    have := (term_even i).1 hm
    have ht : IsTerm (2 * (i + 1) + 1) := (term_odd (i + 1)).2 this.2
    have := next (2 * (i + 1) + 1) (by omega) ht (fun x hx1 hx2 => by omega)
    omega
  · subst hj
    have tj := (term_odd j).1 hm
    have cj1 := tm_le_one (j + 1)
    rcases Nat.lt_or_ge (tm (j + 1)) 1 with h1 | h1
    · have z1 : tm (j + 1) = 0 := by omega
      have n1 : ¬ IsTerm (2 * j + 2) := fun h => by have := (term_even j).1 h; omega
      have n2 : ¬ IsTerm (2 * (j + 1) + 1) := fun h => by have := (term_odd (j + 1)).1 h; omega
      have n3 : ¬ IsTerm (2 * (j + 1) + 2) := fun h => by have := (term_even (j + 1)).1 h; omega
      have cj2 := tm_le_one (j + 2)
      rcases Nat.lt_or_ge (tm (j + 2)) 1 with h2 | h2
      · have z2 : tm (j + 2) = 0 := by omega
        have t3 : tm (j + 3) = 1 := by
          have := tm_le_one (j + 3)
          by_contra hc
          have e1 : j + 1 + 1 = j + 2 := by ring
          have e2 : j + 1 + 2 = j + 3 := by ring
          exact no_three (j + 1) (by rw [e1]; omega) (by rw [e1, e2]; omega)
        have n4 : ¬ IsTerm (2 * (j + 2) + 1) := fun h => by have := (term_odd (j + 2)).1 h; omega
        have n5 : ¬ IsTerm (2 * (j + 2) + 2) := fun h => by have := (term_even (j + 2)).1 h; omega
        have ht : IsTerm (2 * (j + 3) + 1) := (term_odd (j + 3)).2 t3
        have := next (2 * (j + 3) + 1) (by omega) ht (fun x hx1 hx2 => by
          obtain ⟨y, rfl⟩ : ∃ y, x = 2 * j + 2 + y := ⟨x - (2 * j + 2), by omega⟩
          have hy : y < 5 := by omega
          interval_cases y
          · simpa using n1
          · convert n2 using 2 <;> ring
          · convert n3 using 2 <;> ring
          · convert n4 using 2 <;> ring
          · convert n5 using 2 <;> ring)
        omega
      · have t2 : tm (j + 2) = 1 := by omega
        have ht : IsTerm (2 * (j + 2) + 1) := (term_odd (j + 2)).2 t2
        have := next (2 * (j + 2) + 1) (by omega) ht (fun x hx1 hx2 => by
          obtain ⟨y, rfl⟩ : ∃ y, x = 2 * j + 2 + y := ⟨x - (2 * j + 2), by omega⟩
          have hy : y < 3 := by omega
          interval_cases y
          · simpa using n1
          · convert n2 using 2 <;> ring
          · convert n3 using 2 <;> ring)
        omega
    · have t1 : tm (j + 1) = 1 := by omega
      have ht : IsTerm (2 * j + 2) := (term_even j).2 ⟨tj, t1⟩
      have := next (2 * j + 2) (by omega) ht (fun x hx1 hx2 => by omega)
      omega

theorem conjecture :
    {d | IsFirstDiff d} = {1, 4, 6} ∧
    (∀ a b, a ≤ b → (∀ j, a ≤ j → j ≤ b → IsTerm j) → ¬ IsTerm (a - 1) → ¬ IsTerm (b + 1) →
      b - a = 0 ∨ b - a = 2) ∧
    (∀ m, IsTerm m → ¬ IsTerm (m - 1) → (A (m + 1) : ℤ) - A (m - 1) = 5) := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := tm_vals
  refine ⟨?_, ?_, ?_⟩
  · -- conjecture 1
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨m, m', hm, hm', hlt, hgap, rfl⟩
      exact diff_cases m m' hm hm' hlt hgap
    · have T3 : IsTerm 3 := (term_odd 1).2 t1
      have T4 : IsTerm 4 := (term_even 1).2 ⟨t1, t2⟩
      have T5 : IsTerm 5 := (term_odd 2).2 t2
      have T9 : IsTerm 9 := (term_odd 4).2 t4
      have T15 : IsTerm 15 := (term_odd 7).2 t7
      have N6 : ¬ IsTerm 6 := fun h => by
        have := ((term_even 2).1 h).2; norm_num at this; omega
      have N7 : ¬ IsTerm 7 := fun h => by have := (term_odd 3).1 h; omega
      have N8 : ¬ IsTerm 8 := fun h => by have := ((term_even 3).1 h).1; omega
      have N10 : ¬ IsTerm 10 := fun h => by
        have := ((term_even 4).1 h).2; norm_num at this; omega
      have N11 : ¬ IsTerm 11 := fun h => by have := (term_odd 5).1 h; omega
      have N12 : ¬ IsTerm 12 := fun h => by have := ((term_even 5).1 h).1; omega
      have N13 : ¬ IsTerm 13 := fun h => by have := (term_odd 6).1 h; omega
      have N14 : ¬ IsTerm 14 := fun h => by have := ((term_even 6).1 h).1; omega
      rintro (rfl | rfl | rfl)
      · exact ⟨3, 4, T3, T4, by norm_num, fun j h1 h2 => by omega, rfl⟩
      · refine ⟨5, 9, T5, T9, by norm_num, fun j h1 h2 => ?_, rfl⟩
        interval_cases j
        · exact N6
        · exact N7
        · exact N8
      · refine ⟨9, 15, T9, T15, by norm_num, fun j h1 h2 => ?_, rfl⟩
        interval_cases j
        · exact N10
        · exact N11
        · exact N12
        · exact N13
        · exact N14
  · -- conjecture 2
    intro a b hab hall hprev hnext
    rcases Nat.lt_or_ge a b with hlt | hge
    · have ha := hall a le_rfl hab
      have ha1 := hall (a + 1) (by omega) (by omega)
      rcases Nat.even_or_odd' a with ⟨j, hj | hj⟩
      · -- a even: then a - 1 is a term
        exfalso
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · simp at hj; subst hj; exact not_term_zero ha
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e : a = 2 * i + 2 := by omega
        subst e
        have := (term_even i).1 ha
        apply hprev
        have e2 : 2 * i + 2 - 1 = 2 * i + 1 := by omega
        rw [e2]
        exact (term_odd i).2 this.1
      · subst hj
        have hpair := (term_even j).1 (by simpa [show 2 * j + 1 + 1 = 2 * j + 2 by ring] using ha1)
        have h3 : IsTerm (2 * (j + 1) + 1) := (term_odd (j + 1)).2 hpair.2
        rcases Nat.lt_or_ge b (2 * j + 3) with hb | hb
        · exfalso
          have : b = 2 * j + 2 := by omega
          subst this
          exact hnext (by simpa [show 2 * j + 2 + 1 = 2 * (j + 1) + 1 by ring] using h3)
        · rcases Nat.lt_or_ge b (2 * j + 4) with hb' | hb'
          · right; omega
          · exfalso
            have h4 := hall (2 * (j + 1) + 2) (by omega) (by omega)
            have := (term_even (j + 1)).1 h4
            have e1 : j + 1 + 1 = j + 2 := by ring
            rw [e1] at this
            exact no_three j (by omega) (by omega)
    · left; omega
  · -- conjecture 3
    intro m hm hprev
    rcases Nat.even_or_odd' m with ⟨j, hj | hj⟩
    · exfalso
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simp at hj; subst hj; exact not_term_zero hm
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have e : m = 2 * i + 2 := by omega
      subst e
      have := (term_even i).1 hm
      apply hprev
      have e2 : 2 * i + 2 - 1 = 2 * i + 1 := by omega
      rw [e2]
      exact (term_odd i).2 this.1
    · subst hj
      have tj := (term_odd j).1 hm
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · rw [tm_zero] at tj; omega
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hprev' : ¬ IsTerm (2 * i + 2) := by
        have e2 : 2 * (i + 1) + 1 - 1 = 2 * i + 2 := by omega
        rw [e2] at hprev; exact hprev
      have ti : tm i = 0 := by
        have := tm_le_one i
        by_contra hc
        exact hprev' ((term_even i).2 ⟨by omega, tj⟩)
      have e3 : 2 * (i + 1) + 1 + 1 = 2 * (i + 1) + 2 := by ring
      have e4 : 2 * (i + 1) + 1 - 1 = 2 * i + 2 := by omega
      rw [e3, e4, A_even, A_even, tj, ti]
      push_cast
      ring


end OMA.S_oeis_a195609

theorem OMA.solution : type_of% @OMA.S_oeis_a195609.main :=
  OMA.S_oeis_a195609.conjecture
