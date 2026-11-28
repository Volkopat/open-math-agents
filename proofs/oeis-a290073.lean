import OMAStatements.S_oeis_a290073

section Proof_a290073
open OMA.S_oeis_a290073
open PowerSeries

def patEven (x y : ℤ) : Bool :=
  decide ((x = 0 ∧ y = 0) ∨ 2 ≤ |x| ∨ 2 ≤ |y|)

def patOdd (x y : ℤ) : Bool :=
  decide (2 ≤ |x| ∨ 2 ≤ |y|)

set_option maxHeartbeats 2000000 in
lemma step_patEven (x y : ℤ) : step patEven x y = patOdd x y := by
  unfold step patEven patOdd
  by_cases h : |x| ≤ 3 ∧ |y| ≤ 3
  · rcases abs_le.mp h.1 with ⟨_, _⟩; rcases abs_le.mp h.2 with ⟨_, _⟩
    interval_cases x <;> interval_cases y <;> decide +kernel
  · have hfar : 4 ≤ |x| ∨ 4 ≤ |y| := by omega
    rcases hfar with hx4 | hy4
    · have hc : 2 ≤ |x| := by omega
      have h1 : 2 ≤ |x - 1| := by cases abs_cases x <;> cases abs_cases (x - 1) <;> omega
      have h2 : 2 ≤ |x + 1| := by cases abs_cases x <;> cases abs_cases (x + 1) <;> omega
      simp only [hc, h1, h2, true_or, or_true, decide_true]; decide
    · have hc : 2 ≤ |y| := by omega
      have h1 : 2 ≤ |y - 1| := by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega
      have h2 : 2 ≤ |y + 1| := by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega
      simp only [hc, h1, h2, or_true, decide_true]; decide

set_option maxHeartbeats 2000000 in
lemma step_patOdd (x y : ℤ) : step patOdd x y = patEven x y := by
  unfold step patOdd patEven
  by_cases h : |x| ≤ 3 ∧ |y| ≤ 3
  · rcases abs_le.mp h.1 with ⟨_, _⟩; rcases abs_le.mp h.2 with ⟨_, _⟩
    interval_cases x <;> interval_cases y <;> decide +kernel
  · have hfar : 4 ≤ |x| ∨ 4 ≤ |y| := by omega
    rcases hfar with hx4 | hy4
    · have hc : 2 ≤ |x| := by omega
      have h1 : 2 ≤ |x - 1| := by cases abs_cases x <;> cases abs_cases (x - 1) <;> omega
      have h2 : 2 ≤ |x + 1| := by cases abs_cases x <;> cases abs_cases (x + 1) <;> omega
      simp only [hc, h1, h2, true_or, or_true, decide_true]; decide
    · have hc : 2 ≤ |y| := by omega
      have h1 : 2 ≤ |y - 1| := by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega
      have h2 : 2 ≤ |y + 1| := by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega
      simp only [hc, h1, h2, or_true, decide_true]; decide

set_option maxHeartbeats 2000000 in
lemma state_two_eq : state 2 = patEven := by
  funext x y
  by_cases h : |x| ≤ 2 ∧ |y| ≤ 2
  · rcases abs_le.mp h.1 with ⟨_, _⟩; rcases abs_le.mp h.2 with ⟨_, _⟩
    interval_cases x <;> interval_cases y <;> decide +kernel
  · have hout2 : ∀ p q : ℤ, 2 < |p| ∨ 2 < |q| → state 2 p q = true := by
      intro p q hpq
      have hout1 : ∀ u v : ℤ, 1 < |u| ∨ 1 < |v| → state 1 u v = true := by
        intro u v huv
        have hout0 : ∀ c d : ℤ, ¬(c = 0 ∧ d = 0) → state 0 c d = false := by
          intro c d hcd; simp [state, hcd]
        change step (state 0) u v = true
        unfold step
        rw [hout0 u v (by cases abs_cases u <;> cases abs_cases v <;> omega),
            hout0 (u - 1) v (by cases abs_cases u <;> cases abs_cases v <;> omega),
            hout0 (u + 1) v (by cases abs_cases u <;> cases abs_cases v <;> omega),
            hout0 u (v - 1) (by cases abs_cases u <;> cases abs_cases v <;> omega),
            hout0 u (v + 1) (by cases abs_cases u <;> cases abs_cases v <;> omega)]
        decide
      change step (state 1) p q = true
      unfold step
      rw [hout1 p q (by omega),
          hout1 (p - 1) q (by cases abs_cases p <;> cases abs_cases (p - 1) <;> omega),
          hout1 (p + 1) q (by cases abs_cases p <;> cases abs_cases (p + 1) <;> omega),
          hout1 p (q - 1) (by cases abs_cases q <;> cases abs_cases (q - 1) <;> omega),
          hout1 p (q + 1) (by cases abs_cases q <;> cases abs_cases (q + 1) <;> omega)]
      decide
    have hfar : 2 < |x| ∨ 2 < |y| := by omega
    rw [hout2 x y hfar]
    unfold patEven
    rcases hfar with hx | hy
    · simp [show 2 ≤ |x| by omega]
    · simp [show 2 ≤ |y| by omega]

lemma state_ge2 (k : ℕ) :
    state (2 * k + 2) = patEven ∧ state (2 * k + 3) = patOdd := by
  induction k with
  | zero =>
    refine ⟨state_two_eq, ?_⟩
    change step (state 2) = patOdd
    rw [state_two_eq]; funext x y; exact step_patEven x y
  | succ k ih =>
    have h1 : state (2 * (k + 1) + 2) = patEven := by
      have heq : 2 * (k + 1) + 2 = (2 * k + 3) + 1 := by omega
      rw [heq]; change step (state (2 * k + 3)) = patEven
      rw [ih.2]; funext x y; exact step_patOdd x y
    have h2 : state (2 * (k + 1) + 3) = patOdd := by
      have heq : 2 * (k + 1) + 3 = (2 * (k + 1) + 2) + 1 := by omega
      rw [heq]; change step (state (2 * (k + 1) + 2)) = patOdd
      rw [h1]; funext x y; exact step_patEven x y
    exact ⟨h1, h2⟩

lemma diag_eq_xaxis_cell (n : ℕ) (hn : 2 ≤ n) (u : ℤ) :
    state n u u = state n u 0 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hst : state (2 * (k + 1)) = patEven := by
      simpa [show 2 * (k + 1) = 2 * k + 2 by omega] using (state_ge2 k).1
    rw [hst]; unfold patEven; simp
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hst : state (2 * (k + 1) + 1) = patOdd := by
      simpa [show 2 * (k + 1) + 1 = 2 * k + 3 by omega] using (state_ge2 k).2
    rw [hst]; unfold patOdd; simp

lemma a_eq_ref (n : ℕ) (hn : 1 < n) : a n = A283506 n := by
  unfold a A283506
  apply Finset.sum_congr rfl
  intro i _
  rw [diag_eq_xaxis_cell n (by omega)]

lemma geom_two_nat (m : ℕ) : (∑ i ∈ Finset.range m, 2 ^ i) + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ]; omega

lemma sum_pow2_high (n : ℕ) (hn : 2 ≤ n) :
    (∑ i ∈ Finset.range (n - 1), 2 ^ (n - i)) = 2 ^ (n + 1) - 4 := by
  have h1 : ∀ i ∈ Finset.range (n - 1), 2 ^ (n - i) = 4 * 2 ^ (n - 2 - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have heq : n - i = 2 + (n - 2 - i) := by omega
    rw [heq, pow_add]; norm_num
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have href : (∑ i ∈ Finset.range (n - 1), 2 ^ (n - 2 - i)) =
      ∑ i ∈ Finset.range (n - 1), 2 ^ i := by
    have := Finset.sum_range_reflect (fun i => 2 ^ i) (n - 1)
    simpa [show n - 1 - 1 = n - 2 by omega] using this
  rw [href]
  have hg := geom_two_nat (n - 1)
  have hp : 4 * 2 ^ (n - 1) = 2 ^ (n + 1) := by
    have heq : n + 1 = 2 + (n - 1) := by omega
    rw [heq, pow_add]; norm_num
  omega

lemma a_even_nat (n : ℕ) (hn : 1 < n) (he : n % 2 = 0) : a n = 2 ^ (n + 1) - 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hst : state (2 * (k + 1)) = patEven := by
    simpa [show 2 * (k + 1) = 2 * k + 2 by omega] using (state_ge2 k).1
  unfold a
  rw [hst]
  have hsplit : 2 * (k + 1) + 1 = (2 * (k + 1) - 1) + 2 := by omega
  conv_lhs => rw [hsplit, Finset.sum_range_add]
  have hhead : ∑ i ∈ Finset.range (2 * (k + 1) - 1),
      (patEven ((i : ℤ) - ↑(2 * (k + 1))) ((i : ℤ) - ↑(2 * (k + 1)))).toNat *
        2 ^ (2 * (k + 1) - i) =
      ∑ i ∈ Finset.range (2 * (k + 1) - 1), 2 ^ (2 * (k + 1) - i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hp : patEven ((i : ℤ) - ↑(2 * (k + 1))) ((i : ℤ) - ↑(2 * (k + 1))) = true := by
      unfold patEven
      exact decide_eq_true (Or.inr (Or.inl (by cases abs_cases ((i : ℤ) - ↑(2 * (k + 1))) <;> omega)))
    rw [hp]; simp
  have htail : ∑ j ∈ Finset.range 2,
      (patEven (((2 * (k + 1) - 1 + j : ℕ) : ℤ) - ↑(2 * (k + 1)))
        (((2 * (k + 1) - 1 + j : ℕ) : ℤ) - ↑(2 * (k + 1)))).toNat *
        2 ^ (2 * (k + 1) - (2 * (k + 1) - 1 + j)) = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have c0 : (((2 * (k + 1) - 1 + 0 : ℕ) : ℤ) - ↑(2 * (k + 1))) = -1 := by omega
    have c1 : (((2 * (k + 1) - 1 + 1 : ℕ) : ℤ) - ↑(2 * (k + 1))) = 0 := by omega
    have s1 : 2 * (k + 1) - (2 * (k + 1) - 1 + 1) = 0 := by omega
    rw [c0, c1, s1]
    have p0 : patEven (-1) (-1) = false := by decide
    have p1 : patEven 0 0 = true := by decide
    simp [p0, p1]
  rw [hhead, htail, sum_pow2_high (2 * (k + 1)) (by omega)]
  have hge : 4 ≤ 2 ^ (2 * (k + 1) + 1) := by
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ (2 * (k + 1) + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

lemma a_even (n : ℕ) (hn : 1 < n) (he : n % 2 = 0) : (a n : ℤ) = 2 ^ (n + 1) - 3 := by
  rw [a_even_nat n hn he]
  have hge : 3 ≤ 2 ^ (n + 1) := by
    calc 3 ≤ 2 ^ 2 := by decide
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.cast_sub hge]
  push_cast
  rfl

lemma a_odd_nat (n : ℕ) (hn : 1 < n) (ho : n % 2 = 1) : a n = 2 ^ (n + 1) - 4 := by
  obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  subst hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hst : state (2 * (k + 1) + 1) = patOdd := by
    simpa [show 2 * (k + 1) + 1 = 2 * k + 3 by omega] using (state_ge2 k).2
  unfold a
  rw [hst]
  have hsplit : (2 * (k + 1) + 1) + 1 = ((2 * (k + 1) + 1) - 1) + 2 := by omega
  conv_lhs => rw [hsplit, Finset.sum_range_add]
  have hhead : ∑ i ∈ Finset.range ((2 * (k + 1) + 1) - 1),
      (patOdd ((i : ℤ) - ↑(2 * (k + 1) + 1)) ((i : ℤ) - ↑(2 * (k + 1) + 1))).toNat *
        2 ^ ((2 * (k + 1) + 1) - i) =
      ∑ i ∈ Finset.range ((2 * (k + 1) + 1) - 1), 2 ^ ((2 * (k + 1) + 1) - i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hp : patOdd ((i : ℤ) - ↑(2 * (k + 1) + 1)) ((i : ℤ) - ↑(2 * (k + 1) + 1)) = true := by
      unfold patOdd
      exact decide_eq_true (Or.inl (by cases abs_cases ((i : ℤ) - ↑(2 * (k + 1) + 1)) <;> omega))
    rw [hp]; simp
  have htail : ∑ j ∈ Finset.range 2,
      (patOdd ((((2 * (k + 1) + 1) - 1 + j : ℕ) : ℤ) - ↑(2 * (k + 1) + 1))
        ((((2 * (k + 1) + 1) - 1 + j : ℕ) : ℤ) - ↑(2 * (k + 1) + 1))).toNat *
        2 ^ ((2 * (k + 1) + 1) - ((2 * (k + 1) + 1) - 1 + j)) = 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have c0 : ((((2 * (k + 1) + 1) - 1 + 0 : ℕ) : ℤ) - ↑(2 * (k + 1) + 1)) = -1 := by omega
    have c1 : ((((2 * (k + 1) + 1) - 1 + 1 : ℕ) : ℤ) - ↑(2 * (k + 1) + 1)) = 0 := by omega
    rw [c0, c1]
    have p0 : patOdd (-1) (-1) = false := by decide
    have p1 : patOdd 0 0 = false := by decide
    simp [p0, p1]
  rw [hhead, htail, add_zero, sum_pow2_high (2 * (k + 1) + 1) (by omega)]

lemma a_odd (n : ℕ) (hn : 1 < n) (ho : n % 2 = 1) : (a n : ℤ) = 2 ^ (n + 1) - 4 := by
  rw [a_odd_nat n hn ho]
  have hge : 4 ≤ 2 ^ (n + 1) := by
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.cast_sub hge]
  push_cast
  rfl

lemma rec_rel (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3) := by
  by_cases he : n % 2 = 0
  · have h0 := a_even n (by omega) he
    have h1 := a_odd (n - 1) (by omega) (by omega)
    have h2 := a_even (n - 2) (by omega) (by omega)
    have h3 := a_odd (n - 3) (by omega) (by omega)
    rw [h0, h1, h2, h3,
        show n + 1 = (n - 3) + 4 by omega,
        show n - 1 + 1 = (n - 3) + 3 by omega,
        show n - 2 + 1 = (n - 3) + 2 by omega,
        show n - 3 + 1 = (n - 3) + 1 by omega]
    simp only [pow_add]; ring
  · have ho : n % 2 = 1 := by omega
    have h0 := a_odd n (by omega) ho
    have h1 := a_even (n - 1) (by omega) (by omega)
    have h2 := a_odd (n - 2) (by omega) (by omega)
    have h3 := a_even (n - 3) (by omega) (by omega)
    rw [h0, h1, h2, h3,
        show n + 1 = (n - 3) + 4 by omega,
        show n - 1 + 1 = (n - 3) + 3 by omega,
        show n - 2 + 1 = (n - 3) + 2 by omega,
        show n - 3 + 1 = (n - 3) + 1 by omega]
    simp only [pow_add]; ring

set_option maxHeartbeats 1000000 in
lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X)) =
      1 + 2 * X ^ 3 + 4 * X ^ 4 := by
  let s := PowerSeries.mk (fun n => (a n : ℤ))
  have hd : s * ((1 - X) * (1 + X) * (1 - 2 * X)) =
      s * X ^ 0 + (-2 : ℤ) • (s * X ^ 1) + (-1 : ℤ) • (s * X ^ 2) +
      (2 : ℤ) • (s * X ^ 3) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have hp : (1 + 2 * X ^ 3 + 4 * X ^ 4 : PowerSeries ℤ) =
      X ^ 0 + (2 : ℤ) • X ^ 3 + (4 : ℤ) • X ^ 4 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [hd, hp]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
  by_cases hn : n < 5
  · have v0 : a 0 = 1 := by decide
    have v1 : a 1 = 2 := by decide
    have v2 : a 2 = 5 := by decide
    have v3 : a 3 = 12 := by decide
    have v4 : a 4 = 29 := by decide
    interval_cases n <;> norm_num [zsmul_eq_mul, v0, v1, v2, v3, v4]
  · have hr := rec_rel n (by omega)
    simp only [if_pos (show 0 ≤ n by omega), Nat.sub_zero, zsmul_eq_mul,
      if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega)]
    norm_num
    linarith only [hr]

end Proof_a290073

theorem OMA.solution : type_of% @OMA.S_oeis_a290073.main :=
  ⟨gf_eq, fun n hn he => ⟨a_even n hn he, a_eq_ref n hn⟩,
   fun n hn ho => ⟨a_odd n hn ho, a_eq_ref n hn⟩, rec_rel⟩
