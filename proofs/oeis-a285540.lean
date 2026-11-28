import OMAStatements.S_oeis_a285540

section Rule35Proof
open OMA.S_oeis_a285540
open PowerSeries

lemma state_swap (t : ℕ) : ∀ x y : ℤ, state t y x = state t x y := by
  induction t with
  | zero =>
    intro x y
    simp only [state, and_comm]
  | succ t ih =>
    intro x y
    change step (state t) y x = step (state t) x y
    unfold step
    rw [ih y x, ih (y - 1) x, ih (y + 1) x, ih y (x - 1), ih y (x + 1)]
    congr 1
    omega

lemma state_neg (t : ℕ) : ∀ x y : ℤ, state t (-x) (-y) = state t x y := by
  induction t with
  | zero =>
    intro x y
    simp only [state, neg_eq_zero]
  | succ t ih =>
    intro x y
    change step (state t) (-x) (-y) = step (state t) x y
    unfold step
    have h1 : -x - 1 = -(x + 1) := by omega
    have h2 : -x + 1 = -(x - 1) := by omega
    have h3 : -y - 1 = -(y + 1) := by omega
    have h4 : -y + 1 = -(y - 1) := by omega
    rw [h1, h2, h3, h4, ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y + 1), ih x (y - 1)]
    congr 1
    omega

lemma abs_step_lb (z : ℤ) : |z| - 1 ≤ |z - 1| ∧ |z| - 1 ≤ |z + 1| := by
  cases abs_cases z <;> cases abs_cases (z - 1) <;> cases abs_cases (z + 1) <;> omega

lemma state_out_cone (t : ℕ) : ∀ x y : ℤ, (t : ℤ) < |x| + |y| → state t x y = decide (t % 2 = 1) := by
  induction t with
  | zero =>
    intro x y h
    have hne : ¬(x = 0 ∧ y = 0) := by
      rintro ⟨rfl, rfl⟩
      simp at h
    simp [state, hne]
  | succ t ih =>
    intro x y h
    change step (state t) x y = decide ((t + 1) % 2 = 1)
    unfold step
    have hx := abs_step_lb x
    have hy := abs_step_lb y
    rw [ih x y (by omega), ih (x - 1) y (by omega), ih (x + 1) y (by omega),
        ih x (y - 1) (by omega), ih x (y + 1) (by omega)]
    rcases Nat.mod_two_eq_zero_or_one t with ht | ht
    · have ht1 : (t + 1) % 2 = 1 := by omega
      simp only [ht, ht1]
      decide
    · have ht1 : (t + 1) % 2 = 0 := by omega
      simp only [ht, ht1]
      decide

lemma step_from_even (g : ℤ → ℤ → Bool) (hg : ∀ x y : ℤ, (x + y) % 2 ≠ 0 → g x y = false)
    (x y : ℤ) (hxy : (x + y) % 2 = 0) : step g x y = true := by
  unfold step
  rw [hg (x - 1) y (by omega), hg (x + 1) y (by omega),
      hg x (y - 1) (by omega), hg x (y + 1) (by omega)]
  cases g x y <;> decide

lemma state_parity (m : ℕ) :
    (∀ x y : ℤ, (x + y) % 2 ≠ 0 → state (2 * m) x y = false) ∧
    (∀ x y : ℤ, (x + y) % 2 = 0 → state (2 * m + 1) x y = true) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hne : ¬(x = 0 ∧ y = 0) := by omega
      simp [state, hne]
    · intro x y hxy
      exact step_from_even (state 0) (fun u v huv => by
        have hne : ¬(u = 0 ∧ v = 0) := by omega
        simp [state, hne]) x y hxy
  | succ m ih =>
    have heven : ∀ x y : ℤ, (x + y) % 2 ≠ 0 → state (2 * (m + 1)) x y = false := by
      intro x y hxy
      have hm : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      rw [hm]
      change step (state (2 * m + 1)) x y = false
      unfold step
      rw [ih.2 (x - 1) y (by omega), ih.2 (x + 1) y (by omega),
          ih.2 x (y - 1) (by omega), ih.2 x (y + 1) (by omega)]
      cases state (2 * m + 1) x y <;> decide
    exact ⟨heven, fun x y hxy => step_from_even (state (2 * (m + 1))) heven x y hxy⟩

lemma state_even_diag_le (m : ℕ) : ∀ i : ℕ, i ≤ m → state (2 * m) (i : ℤ) (i : ℤ) = true := by
  induction m with
  | zero =>
    intro i hi
    have : i = 0 := by omega
    subst this
    decide
  | succ m ih =>
    have h_off : ∀ j : ℕ, j ≤ m → state (2 * m + 1) ((j : ℤ) + 1) (j : ℤ) = false := by
      intro j hj
      change step (state (2 * m)) ((j : ℤ) + 1) (j : ℤ) = false
      unfold step
      have hc : state (2 * m) ((j : ℤ) + 1) (j : ℤ) = false :=
        (state_parity m).1 _ _ (by omega)
      have hl : state (2 * m) ((j : ℤ) + 1 - 1) (j : ℤ) = true := by
        have heq : (j : ℤ) + 1 - 1 = (j : ℤ) := by omega
        rw [heq]
        exact ih j hj
      rw [hc, hl]
      cases state (2 * m) ((j : ℤ) + 1 + 1) (j : ℤ) <;>
        cases state (2 * m) ((j : ℤ) + 1) ((j : ℤ) - 1) <;>
        cases state (2 * m) ((j : ℤ) + 1) ((j : ℤ) + 1) <;> decide
    intro i hi
    have hm : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [hm]
    change step (state (2 * m + 1)) (i : ℤ) (i : ℤ) = true
    unfold step
    have hc : state (2 * m + 1) (i : ℤ) (i : ℤ) = true :=
      (state_parity m).2 _ _ (by omega)
    rw [hc, state_swap (2 * m + 1) ((i : ℤ) - 1) (i : ℤ),
        state_swap (2 * m + 1) ((i : ℤ) + 1) (i : ℤ)]
    by_cases him : i ≤ m
    · rw [h_off i him]
      cases state (2 * m + 1) ((i : ℤ) - 1) (i : ℤ) <;> decide
    · have hieq : i = m + 1 := by omega
      subst hieq
      have hsub : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by omega
      have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by omega
      rw [hsub, hcast, state_swap (2 * m + 1) ((m : ℤ) + 1) (m : ℤ), h_off m (le_refl m)]
      cases state (2 * m + 1) ((m : ℤ) + 1 + 1) ((m : ℤ) + 1) <;> decide

lemma state_even_diag (m i : ℕ) : state (2 * m) (i : ℤ) (i : ℤ) = decide (i ≤ m) := by
  by_cases h : i ≤ m
  · rw [state_even_diag_le m i h, decide_eq_true h]
  · have hout : ((2 * m : ℕ) : ℤ) < |(i : ℤ)| + |(i : ℤ)| := by
      rw [abs_of_nonneg (Nat.cast_nonneg i)]
      omega
    rw [state_out_cone (2 * m) (i : ℤ) (i : ℤ) hout, decide_eq_false h]
    have hmod : (2 * m) % 2 = 0 := by omega
    simp [hmod]

lemma geom_sum_int (b : ℤ) (k : ℕ) :
    (b - 1) * (∑ i ∈ Finset.range k, b ^ i) = b ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

lemma sum_pow_rev_nat (b k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), b ^ (k - i)) = ∑ i ∈ Finset.range (k + 1), b ^ i := by
  have := Finset.sum_range_reflect (fun i => b ^ i) (k + 1)
  simpa [Nat.succ_sub_succ_eq_sub] using this

lemma a_odd_corner_nat (b m : ℕ) :
    (∑ i ∈ Finset.range (2 * m + 1 + 1),
      (state (2 * m + 1) ((i : ℤ) - ↑(2 * m + 1)) ((i : ℤ) - ↑(2 * m + 1))).toNat *
        b ^ (2 * m + 1 - i)) =
    ∑ i ∈ Finset.range (2 * m + 2), b ^ i := by
  have hterm : ∀ i ∈ Finset.range (2 * m + 1 + 1),
      (state (2 * m + 1) ((i : ℤ) - ↑(2 * m + 1)) ((i : ℤ) - ↑(2 * m + 1))).toNat *
        b ^ (2 * m + 1 - i) = b ^ (2 * m + 1 - i) := by
    intro i _
    have hp : state (2 * m + 1) ((i : ℤ) - ↑(2 * m + 1)) ((i : ℤ) - ↑(2 * m + 1)) = true :=
      (state_parity m).2 _ _ (by omega)
    rw [hp]
    simp
  rw [Finset.sum_congr rfl hterm]
  exact sum_pow_rev_nat b (2 * m + 1)

lemma a_odd_origin_nat (b m : ℕ) :
    (∑ i ∈ Finset.range (2 * m + 1 + 1),
      (state (2 * m + 1) (i : ℤ) (i : ℤ)).toNat * b ^ (2 * m + 1 - i)) =
    ∑ i ∈ Finset.range (2 * m + 2), b ^ i := by
  have hterm : ∀ i ∈ Finset.range (2 * m + 1 + 1),
      (state (2 * m + 1) (i : ℤ) (i : ℤ)).toNat * b ^ (2 * m + 1 - i) = b ^ (2 * m + 1 - i) := by
    intro i _
    have hp : state (2 * m + 1) (i : ℤ) (i : ℤ) = true :=
      (state_parity m).2 _ _ (by omega)
    rw [hp]
    simp
  rw [Finset.sum_congr rfl hterm]
  exact sum_pow_rev_nat b (2 * m + 1)

lemma a_even_corner_nat (b m : ℕ) :
    (∑ i ∈ Finset.range (2 * m + 1),
      (state (2 * m) ((i : ℤ) - ↑(2 * m)) ((i : ℤ) - ↑(2 * m))).toNat * b ^ (2 * m - i)) =
    ∑ i ∈ Finset.range (m + 1), b ^ i := by
  have hsplit : 2 * m + 1 = m + (m + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have h1 : ∑ i ∈ Finset.range m,
      (state (2 * m) ((i : ℤ) - ↑(2 * m)) ((i : ℤ) - ↑(2 * m))).toNat * b ^ (2 * m - i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    have hneg : ((i : ℤ) - ↑(2 * m)) = -(((2 * m - i : ℕ) : ℤ)) := by omega
    rw [hneg, state_neg, state_even_diag]
    have : ¬(2 * m - i ≤ m) := by omega
    simp [this]
  have h2 : ∑ j ∈ Finset.range (m + 1),
      (state (2 * m) (((m + j : ℕ) : ℤ) - ↑(2 * m)) (((m + j : ℕ) : ℤ) - ↑(2 * m))).toNat *
        b ^ (2 * m - (m + j)) =
      ∑ j ∈ Finset.range (m + 1), b ^ (m - j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hneg : (((m + j : ℕ) : ℤ) - ↑(2 * m)) = -(((m - j : ℕ) : ℤ)) := by omega
    have hsub : 2 * m - (m + j) = m - j := by omega
    rw [hneg, hsub, state_neg, state_even_diag]
    have : m - j ≤ m := by omega
    simp [this]
  rw [h1, zero_add, h2]
  exact sum_pow_rev_nat b m

lemma a_even_origin_nat (b m : ℕ) :
    (∑ i ∈ Finset.range (2 * m + 1),
      (state (2 * m) (i : ℤ) (i : ℤ)).toNat * b ^ (2 * m - i)) =
    b ^ m * ∑ i ∈ Finset.range (m + 1), b ^ i := by
  have hsplit : 2 * m + 1 = (m + 1) + m := by omega
  rw [hsplit, Finset.sum_range_add]
  have h2 : ∑ j ∈ Finset.range m,
      (state (2 * m) ((m + 1 + j : ℕ) : ℤ) ((m + 1 + j : ℕ) : ℤ)).toNat *
        b ^ (2 * m - (m + 1 + j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [state_even_diag]
    have : ¬(m + 1 + j ≤ m) := by omega
    simp [this]
  have h1 : ∑ i ∈ Finset.range (m + 1),
      (state (2 * m) (i : ℤ) (i : ℤ)).toNat * b ^ (2 * m - i) =
      ∑ i ∈ Finset.range (m + 1), b ^ m * b ^ (m - i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [state_even_diag]
    have him : i ≤ m := by omega
    have hpow : b ^ (2 * m - i) = b ^ m * b ^ (m - i) := by
      rw [← pow_add]
      congr 1
      omega
    simp [him, hpow]
  rw [h2, add_zero, h1, ← Finset.mul_sum, sum_pow_rev_nat b m]

lemma neg_two_pow_even (m : ℕ) : (-2 : ℤ) ^ (2 * m) = 2 ^ (2 * m) := by
  rw [pow_mul, pow_mul]; norm_num

lemma neg_two_pow_odd (m : ℕ) : (-2 : ℤ) ^ (2 * m + 1) = -(2 ^ (2 * m + 1)) := by
  rw [pow_succ, neg_two_pow_even, pow_succ]; ring

lemma neg_one_pow_even (m : ℕ) : (-1 : ℤ) ^ (2 * m) = 1 := by
  rw [pow_mul]; norm_num

lemma neg_one_pow_odd (m : ℕ) : (-1 : ℤ) ^ (2 * m + 1) = -1 := by
  rw [pow_succ, neg_one_pow_even]; norm_num

lemma a_even_val (m : ℕ) : 9 * (a (2 * m) : ℤ) = 10 ^ (m + 1) - 1 := by
  have h := a_even_corner_nat 10 m
  have ha : a (2 * m) = ∑ i ∈ Finset.range (m + 1), 10 ^ i := h
  rw [ha, Nat.cast_sum]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  simpa using geom_sum_int 10 (m + 1)

lemma a_odd_val (m : ℕ) : 9 * (a (2 * m + 1) : ℤ) = 10 ^ (2 * m + 2) - 1 := by
  have h := a_odd_corner_nat 10 m
  have ha : a (2 * m + 1) = ∑ i ∈ Finset.range (2 * m + 2), 10 ^ i := h
  rw [ha, Nat.cast_sum]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  simpa using geom_sum_int 10 (2 * m + 2)

lemma pow_2_5 (k : ℕ) : (2 : ℤ) ^ k * 5 ^ k = 10 ^ k := by
  rw [← mul_pow]; norm_num

lemma closed_form (n : ℕ) :
    (a n : ℤ) =
      (-1 - (-2 : ℤ) ^ n * 5 ^ (1 + n) + 2 ^ n * 5 ^ (1 + n) +
        2 ^ (n / 2) * 5 ^ (1 + n / 2) * (1 + (-1) ^ n)) / 9 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hm : (2 * m) / 2 = m := by omega
    rw [hm, neg_two_pow_even, neg_one_pow_even]
    have hnum : -1 - (2 : ℤ) ^ (2 * m) * 5 ^ (1 + 2 * m) + 2 ^ (2 * m) * 5 ^ (1 + 2 * m) +
        2 ^ m * 5 ^ (1 + m) * (1 + 1) = 9 * (a (2 * m) : ℤ) := by
      have hp : (2 : ℤ) ^ m * 5 ^ (1 + m) * (1 + 1) = 10 ^ (m + 1) := by
        calc (2 : ℤ) ^ m * 5 ^ (1 + m) * 2
          _ = 2 ^ (m + 1) * 5 ^ (m + 1) := by ring
          _ = 10 ^ (m + 1) := pow_2_5 (m + 1)
      linarith [a_even_val m, hp]
    rw [hnum, Int.mul_ediv_cancel_left _ (by norm_num)]
  · rw [neg_two_pow_odd, neg_one_pow_odd]
    have hnum : -1 - -(2 : ℤ) ^ (2 * m + 1) * 5 ^ (1 + (2 * m + 1)) +
        2 ^ (2 * m + 1) * 5 ^ (1 + (2 * m + 1)) +
        2 ^ ((2 * m + 1) / 2) * 5 ^ (1 + (2 * m + 1) / 2) * (1 + -1) =
        9 * (a (2 * m + 1) : ℤ) := by
      have hp : (2 : ℤ) ^ (2 * m + 1) * 5 ^ (1 + (2 * m + 1)) * 2 = 10 ^ (2 * m + 2) := by
        calc (2 : ℤ) ^ (2 * m + 1) * 5 ^ (1 + (2 * m + 1)) * 2
          _ = 2 ^ (2 * m + 2) * 5 ^ (2 * m + 2) := by ring
          _ = 10 ^ (2 * m + 2) := pow_2_5 (2 * m + 2)
      linarith [a_odd_val m, hp]
    rw [hnum, Int.mul_ediv_cancel_left _ (by norm_num)]

lemma rec_rel (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℤ) - a (n - 1) - 110 * a (n - 2) + 110 * a (n - 3) + 1000 * a (n - 4) - 1000 * a (n - 5) = 0 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
    have s0 := a_even_val (k + 3)
    have s1 := a_odd_val (k + 2)
    have s2 := a_even_val (k + 2)
    have s3 := a_odd_val (k + 1)
    have s4 := a_even_val (k + 1)
    have s5 := a_odd_val k
    have i1 : 2 * (k + 3) - 1 = 2 * (k + 2) + 1 := by omega
    have i2 : 2 * (k + 3) - 2 = 2 * (k + 2) := by omega
    have i3 : 2 * (k + 3) - 3 = 2 * (k + 1) + 1 := by omega
    have i4 : 2 * (k + 3) - 4 = 2 * (k + 1) := by omega
    have i5 : 2 * (k + 3) - 5 = 2 * k + 1 := by omega
    rw [i1, i2, i3, i4, i5]
    have h9 : 9 * ((a (2 * (k + 3)) : ℤ) - a (2 * (k + 2) + 1) - 110 * a (2 * (k + 2)) +
        110 * a (2 * (k + 1) + 1) + 1000 * a (2 * (k + 1)) - 1000 * a (2 * k + 1)) = 0 := by
      have p1 : (10 : ℤ) ^ (k + 3 + 1) = 1000 * 10 ^ (k + 1) := by ring
      have p2 : (10 : ℤ) ^ (2 * (k + 2) + 2) = 10000 * 10 ^ (2 * k + 2) := by ring
      have p3 : (10 : ℤ) ^ (k + 2 + 1) = 100 * 10 ^ (k + 1) := by ring
      have p4 : (10 : ℤ) ^ (2 * (k + 1) + 2) = 100 * 10 ^ (2 * k + 2) := by ring
      have p5 : (10 : ℤ) ^ (k + 1 + 1) = 10 * 10 ^ (k + 1) := by ring
      linarith
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have s0 := a_odd_val (k + 2)
    have s1 := a_even_val (k + 2)
    have s2 := a_odd_val (k + 1)
    have s3 := a_even_val (k + 1)
    have s4 := a_odd_val k
    have s5 := a_even_val k
    have i1 : 2 * (k + 2) + 1 - 1 = 2 * (k + 2) := by omega
    have i2 : 2 * (k + 2) + 1 - 2 = 2 * (k + 1) + 1 := by omega
    have i3 : 2 * (k + 2) + 1 - 3 = 2 * (k + 1) := by omega
    have i4 : 2 * (k + 2) + 1 - 4 = 2 * k + 1 := by omega
    have i5 : 2 * (k + 2) + 1 - 5 = 2 * k := by omega
    rw [i1, i2, i3, i4, i5]
    have h9 : 9 * ((a (2 * (k + 2) + 1) : ℤ) - a (2 * (k + 2)) - 110 * a (2 * (k + 1) + 1) +
        110 * a (2 * (k + 1)) + 1000 * a (2 * k + 1) - 1000 * a (2 * k)) = 0 := by
      have p1 : (10 : ℤ) ^ (2 * (k + 2) + 2) = 10000 * 10 ^ (2 * k + 2) := by ring
      have p2 : (10 : ℤ) ^ (k + 2 + 1) = 100 * 10 ^ (k + 1) := by ring
      have p3 : (10 : ℤ) ^ (2 * (k + 1) + 2) = 100 * 10 ^ (2 * k + 2) := by ring
      have p4 : (10 : ℤ) ^ (k + 1 + 1) = 10 * 10 ^ (k + 1) := by ring
      linarith
    linarith

lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2)) =
      1 + 10 * X - 110 * X ^ 2 := by
  let s := PowerSeries.mk (fun n => (a n : ℤ))
  have hring : s * ((1 - X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2)) =
      C (1 : ℤ) * (s * X ^ 0) + C (-1 : ℤ) * (s * X ^ 1) + C (-110 : ℤ) * (s * X ^ 2) +
      C (110 : ℤ) * (s * X ^ 3) + C (1000 : ℤ) * (s * X ^ 4) + C (-1000 : ℤ) * (s * X ^ 5) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [hring]
  have hrhs : (1 + 10 * X - 110 * X ^ 2 : PowerSeries ℤ) =
      C (1 : ℤ) * X ^ 0 + C (10 : ℤ) * X ^ 1 + C (-110 : ℤ) * X ^ 2 := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [hrhs]
  ext n
  simp only [map_add, coeff_C_mul]
  simp only [coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
  by_cases hn : n < 5
  · have v0 : a 0 = 1 := by decide
    have v1 : a 1 = 11 := by decide
    have v2 : a 2 = 11 := by decide
    have v3 : a 3 = 1111 := by decide
    have v4 : a 4 = 111 := by decide
    interval_cases n <;> norm_num [v0, v1, v2, v3, v4]
  · have h5 : 5 ≤ n := by omega
    have hrec := rec_rel n h5
    have n0 : n ≠ 0 := by omega
    have n1 : n ≠ 1 := by omega
    have n2 : n ≠ 2 := by omega
    simp [n0, n1, n2, show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
          show 4 ≤ n by omega, h5]
    linarith

end Rule35Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a285540.main :=
  ⟨gf_eq, closed_form⟩
