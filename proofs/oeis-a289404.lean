import OMAStatements.S_oeis_a289404

section Rule566Proof
open OMA.S_oeis_a289404
open PowerSeries

lemma state_swap (t : ℕ) : ∀ x y : ℤ, state t y x = state t x y := by
  induction t with
  | zero => intro x y; simp only [state, and_comm]
  | succ t ih =>
    intro x y
    change step (state t) y x = step (state t) x y
    unfold step
    rw [ih y x, ih (y - 1) x, ih (y + 1) x, ih y (x - 1), ih y (x + 1)]
    congr 1; omega

lemma state_neg (t : ℕ) : ∀ x y : ℤ, state t (-x) (-y) = state t x y := by
  induction t with
  | zero => intro x y; simp only [state, neg_eq_zero]
  | succ t ih =>
    intro x y
    change step (state t) (-x) (-y) = step (state t) x y
    unfold step
    have h1 : -x - 1 = -(x + 1) := by omega
    have h2 : -x + 1 = -(x - 1) := by omega
    have h3 : -y - 1 = -(y + 1) := by omega
    have h4 : -y + 1 = -(y - 1) := by omega
    rw [h1, h2, h3, h4, ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y + 1), ih x (y - 1)]
    congr 1; omega

lemma abs_step_lb (z : ℤ) : |z| - 1 ≤ |z - 1| ∧ |z| - 1 ≤ |z + 1| := by
  cases abs_cases z <;> cases abs_cases (z - 1) <;> cases abs_cases (z + 1) <;> omega

lemma state_out (t : ℕ) : ∀ x y : ℤ, (t : ℤ) < |x| + |y| → state t x y = false := by
  induction t with
  | zero =>
    intro x y h
    have hne : ¬(x = 0 ∧ y = 0) := by rintro ⟨rfl, rfl⟩; simp at h
    simp [state, hne]
  | succ t ih =>
    intro x y h
    change step (state t) x y = false
    unfold step
    have hx := abs_step_lb x
    have hy := abs_step_lb y
    rw [ih x y (by omega), ih (x - 1) y (by omega), ih (x + 1) y (by omega),
        ih x (y - 1) (by omega), ih x (y + 1) (by omega)]
    decide

lemma state_frontier (t : ℕ) :
    ∀ u v : ℕ, u + v = t → state t (u : ℤ) (v : ℤ) = true := by
  induction t with
  | zero =>
    intro u v h
    obtain ⟨rfl, rfl⟩ : u = 0 ∧ v = 0 := ⟨by omega, by omega⟩
    decide
  | succ t ih =>
    intro u v h
    change step (state t) (u : ℤ) (v : ℤ) = true
    unfold step
    have hc : state t (u : ℤ) (v : ℤ) = false := by
      apply state_out
      rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
      omega
    have he : state t ((u : ℤ) + 1) (v : ℤ) = false := by
      apply state_out; cases abs_cases ((u : ℤ) + 1) <;> cases abs_cases (v : ℤ) <;> omega
    have hs : state t (u : ℤ) ((v : ℤ) + 1) = false := by
      apply state_out; cases abs_cases (u : ℤ) <;> cases abs_cases ((v : ℤ) + 1) <;> omega
    rw [hc, he, hs]
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · have hv : 1 ≤ v := by omega
      have hw : state t ((0 : ℤ) - 1) (v : ℤ) = false := by
        apply state_out; cases abs_cases ((0 : ℤ) - 1) <;> cases abs_cases (v : ℤ) <;> omega
      have hvm1 : ((v : ℤ) - 1) = ((v - 1 : ℕ) : ℤ) := by omega
      have hn : state t 0 ((v : ℤ) - 1) = true := by
        rw [hvm1]; exact ih 0 (v - 1) (by omega)
      simp only [Nat.cast_zero, hw, hn]
      decide
    · have hum1 : ((u : ℤ) - 1) = ((u - 1 : ℕ) : ℤ) := by omega
      have hw : state t ((u : ℤ) - 1) (v : ℤ) = true := by
        rw [hum1]; exact ih (u - 1) v (by omega)
      rcases Nat.eq_zero_or_pos v with rfl | hv
      · have hn : state t (u : ℤ) ((0 : ℤ) - 1) = false := by
          apply state_out; cases abs_cases (u : ℤ) <;> cases abs_cases ((0 : ℤ) - 1) <;> omega
        simp only [Nat.cast_zero] at hw hn ⊢
        rw [hw, hn]
        decide
      · have hvm1 : ((v : ℤ) - 1) = ((v - 1 : ℕ) : ℤ) := by omega
        have hn : state t (u : ℤ) ((v : ℤ) - 1) = true := by
          rw [hvm1]; exact ih u (v - 1) (by omega)
        rw [hw, hn]
        decide

lemma state_diag_stay (t : ℕ) (x : ℤ) (h : state t x x = true) : state (t + 1) x x = true := by
  change step (state t) x x = true
  unfold step
  rw [h, state_swap t x (x - 1), state_swap t x (x + 1)]
  cases state t x (x - 1) <;> cases state t x (x + 1) <;> decide

lemma state_diag_true (k : ℕ) : ∀ t : ℕ, 2 * k ≤ t → state t (k : ℤ) (k : ℤ) = true := by
  intro t ht
  obtain ⟨d, rfl⟩ : ∃ d, t = 2 * k + d := ⟨t - 2 * k, by omega⟩
  induction d with
  | zero =>
    simpa using state_frontier (2 * k) k k (by omega)
  | succ d ih =>
    have heq : 2 * k + (d + 1) = (2 * k + d) + 1 := by omega
    rw [heq]
    exact state_diag_stay (2 * k + d) (k : ℤ) (ih (by omega))

lemma state_diag_nat (t k : ℕ) : state t (k : ℤ) (k : ℤ) = decide (2 * k ≤ t) := by
  by_cases h : 2 * k ≤ t
  · rw [state_diag_true k t h, decide_eq_true h]
  · have hout : (t : ℤ) < |(k : ℤ)| + |(k : ℤ)| := by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]; omega
    rw [state_out t (k : ℤ) (k : ℤ) hout, decide_eq_false h]

lemma geom_sum_int (b : ℤ) (k : ℕ) :
    (b - 1) * (∑ i ∈ Finset.range k, b ^ i) = b ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

lemma sum_pow_rev_nat (b k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), b ^ (k - i)) = ∑ i ∈ Finset.range (k + 1), b ^ i := by
  have := Finset.sum_range_reflect (fun i => b ^ i) (k + 1)
  simpa [Nat.succ_sub_succ_eq_sub] using this

lemma a_nine (n : ℕ) : 9 * (a n : ℤ) = 10 ^ (1 + n / 2) - 1 := by
  have ha : a n = ∑ j ∈ Finset.range (n / 2 + 1), 10 ^ j := by
    unfold a
    have hsplit : n + 1 = (n - n / 2) + (n / 2 + 1) := by omega
    rw [hsplit, Finset.sum_range_add]
    have h1 : ∑ i ∈ Finset.range (n - n / 2),
        (state n ((i : ℤ) - ↑n) ((i : ℤ) - ↑n)).toNat * 10 ^ (n - i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      have hneg : ((i : ℤ) - ↑n) = -(((n - i : ℕ) : ℤ)) := by omega
      rw [hneg, state_neg, state_diag_nat]
      have hno : ¬(2 * (n - i) ≤ n) := by omega
      simp [hno]
    have h2 : ∑ j ∈ Finset.range (n / 2 + 1),
        (state n (((n - n / 2 + j : ℕ) : ℤ) - ↑n) (((n - n / 2 + j : ℕ) : ℤ) - ↑n)).toNat *
          10 ^ (n - (n - n / 2 + j)) =
        ∑ j ∈ Finset.range (n / 2 + 1), 10 ^ (n / 2 - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have hneg : (((n - n / 2 + j : ℕ) : ℤ) - ↑n) = -(((n / 2 - j : ℕ) : ℤ)) := by omega
      have hsub : n - (n - n / 2 + j) = n / 2 - j := by omega
      rw [hneg, hsub, state_neg, state_diag_nat]
      have hok : 2 * (n / 2 - j) ≤ n := by omega
      simp [hok]
    rw [h1, zero_add, h2, sum_pow_rev_nat 10 (n / 2)]
  rw [ha, Nat.cast_sum]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have h1 : 1 + n / 2 = n / 2 + 1 := by omega
  rw [h1]
  simpa using geom_sum_int 10 (n / 2 + 1)

lemma rec_rel (n : ℕ) (hn : 2 < n) :
    (a n : ℤ) = a (n - 1) + 10 * a (n - 2) - 10 * a (n - 3) := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have e0 := a_nine (2 * (k + 2))
    have e1 := a_nine (2 * (k + 2) - 1)
    have e2 := a_nine (2 * (k + 2) - 2)
    have e3 := a_nine (2 * (k + 2) - 3)
    have d0 : (2 * (k + 2)) / 2 = k + 2 := by omega
    have d1 : (2 * (k + 2) - 1) / 2 = k + 1 := by omega
    have d2 : (2 * (k + 2) - 2) / 2 = k + 1 := by omega
    have d3 : (2 * (k + 2) - 3) / 2 = k := by omega
    rw [d0] at e0; rw [d1] at e1; rw [d2] at e2; rw [d3] at e3
    have p1 : (10 : ℤ) ^ (1 + (k + 2)) = 100 * 10 ^ (1 + k) := by ring
    have p2 : (10 : ℤ) ^ (1 + (k + 1)) = 10 * 10 ^ (1 + k) := by ring
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have e0 := a_nine (2 * (k + 1) + 1)
    have e1 := a_nine (2 * (k + 1) + 1 - 1)
    have e2 := a_nine (2 * (k + 1) + 1 - 2)
    have e3 := a_nine (2 * (k + 1) + 1 - 3)
    have d0 : (2 * (k + 1) + 1) / 2 = k + 1 := by omega
    have d1 : (2 * (k + 1) + 1 - 1) / 2 = k + 1 := by omega
    have d2 : (2 * (k + 1) + 1 - 2) / 2 = k := by omega
    have d3 : (2 * (k + 1) + 1 - 3) / 2 = k := by omega
    rw [d0] at e0; rw [d1] at e1; rw [d2] at e2; rw [d3] at e3
    linarith

set_option maxHeartbeats 1000000 in
lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 10 * X ^ 2)) = 1 := by
  let s := PowerSeries.mk (fun n => (a n : ℤ))
  have hring : s * ((1 - X) * (1 - 10 * X ^ 2)) =
      C (1 : ℤ) * (s * X ^ 0) + C (-1 : ℤ) * (s * X ^ 1) +
      C (-10 : ℤ) * (s * X ^ 2) + C (10 : ℤ) * (s * X ^ 3) := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [hring]
  have hrhs : (1 : PowerSeries ℤ) = C (1 : ℤ) * X ^ 0 := by simp
  rw [hrhs]
  ext n
  simp only [map_add, coeff_C_mul]
  simp only [coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
  by_cases hn : n < 3
  · have v0 : a 0 = 1 := by decide
    have v1 : a 1 = 1 := by decide
    have v2 : a 2 = 11 := by decide
    interval_cases n <;> norm_num [v0, v1, v2]
  · have h2 : 2 < n := by omega
    have hrec := rec_rel n h2
    have n0 : n ≠ 0 := by omega
    simp [n0, show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega]
    linarith

lemma floor_half_nat (n : ℕ) : ⌊(n : ℚ) / 2⌋ = ((n / 2 : ℕ) : ℤ) := by
  rw [Int.floor_eq_iff]
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hm : (2 * m) / 2 = m := by omega
    rw [hm]; push_cast; constructor <;> linarith
  · have hm : (2 * m + 1) / 2 = m := by omega
    rw [hm]; push_cast; constructor <;> linarith

lemma floor_closed (n : ℕ) :
    (a n : ℚ) = ((10 : ℚ) ^ (1 + ⌊(n : ℚ) / 2⌋) - 1) / 9 := by
  rw [floor_half_nat]
  have hexp : (1 : ℤ) + ((n / 2 : ℕ) : ℤ) = ((1 + n / 2 : ℕ) : ℤ) := by omega
  rw [hexp, zpow_natCast]
  have h9 : (9 : ℚ) * (a n : ℚ) = (10 : ℚ) ^ (1 + n / 2) - 1 := by
    exact_mod_cast a_nine n
  linarith

lemma sqrt_closed (n : ℕ) :
    (a n : ℝ) =
      (Real.sqrt 10 ^ (n + 1) * ((Real.sqrt 10 - 1) * (-1) ^ n + (Real.sqrt 10 + 1)) - 2) / 18 := by
  have h9 : (9 : ℝ) * (a n : ℝ) = (10 : ℝ) ^ (1 + n / 2) - 1 := by
    exact_mod_cast a_nine n
  have hsq : Real.sqrt 10 ^ 2 = (10 : ℝ) := Real.sq_sqrt (by norm_num)
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hm : (2 * m) / 2 = m := by omega
    rw [hm] at h9
    have hp : Real.sqrt 10 ^ (2 * m + 1) = (10 : ℝ) ^ m * Real.sqrt 10 := by
      rw [pow_succ, pow_mul, hsq]
    have hm1 : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
    rw [hp, hm1]
    have hmul : (10 : ℝ) ^ m * Real.sqrt 10 * ((Real.sqrt 10 - 1) * 1 + (Real.sqrt 10 + 1)) =
        2 * (10 : ℝ) ^ (1 + m) := by
      calc (10 : ℝ) ^ m * Real.sqrt 10 * ((Real.sqrt 10 - 1) * 1 + (Real.sqrt 10 + 1))
        _ = 2 * ((10 : ℝ) ^ m * Real.sqrt 10 ^ 2) := by ring
        _ = 2 * ((10 : ℝ) ^ m * 10) := by rw [hsq]
        _ = 2 * (10 : ℝ) ^ (1 + m) := by rw [pow_add, pow_one]; ring
    linarith
  · have hm : (2 * m + 1) / 2 = m := by omega
    rw [hm] at h9
    have hp : Real.sqrt 10 ^ (2 * m + 1 + 1) = (10 : ℝ) ^ (1 + m) := by
      have heq : 2 * m + 1 + 1 = 2 * (1 + m) := by omega
      rw [heq, pow_mul, hsq]
    have hm1 : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
      rw [pow_succ, pow_mul]; norm_num
    rw [hp, hm1]
    linarith

end Rule566Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a289404.main :=
  ⟨gf_eq, rec_rel, floor_closed, sqrt_closed⟩
