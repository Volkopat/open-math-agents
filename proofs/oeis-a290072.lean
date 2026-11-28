import OMAStatements.S_oeis_a290072

section Proof_a290072
open OMA.S_oeis_a290072
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

lemma a_eq_ref (n : ℕ) (hn : 4 < n) : a n = A283505 n := by
  unfold a A283505
  apply Finset.sum_congr rfl
  intro i _
  rw [diag_eq_xaxis_cell n (by omega)]

lemma sum_tail10 (n : ℕ) (hn : 2 ≤ n) (f : ℤ → ℤ → Bool)
    (hf : ∀ u : ℤ, 2 ≤ u → f u u = true) :
    ∑ i ∈ Finset.range (n + 1), (f (i : ℤ) (i : ℤ)).toNat * 10 ^ (n - i) =
      (f 0 0).toNat * 10 ^ n + (f 1 1).toNat * 10 ^ (n - 1) +
        ∑ j ∈ Finset.range (n - 1), 10 ^ j := by
  have hsplit : n + 1 = 2 + (n - 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hhead : ∑ i ∈ Finset.range 2, (f (i : ℤ) (i : ℤ)).toNat * 10 ^ (n - i) =
      (f 0 0).toNat * 10 ^ n + (f 1 1).toNat * 10 ^ (n - 1) := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]; simp
  rw [hhead]
  congr 1
  have h1 : ∀ j ∈ Finset.range (n - 1),
      (f ((2 + j : ℕ) : ℤ) ((2 + j : ℕ) : ℤ)).toNat * 10 ^ (n - (2 + j)) =
        10 ^ (n - 2 - j) := by
    intro j hj
    rw [hf ((2 + j : ℕ) : ℤ) (by omega)]
    have he : n - (2 + j) = n - 2 - j := by omega
    simp [he]
  rw [Finset.sum_congr rfl h1]
  have href := Finset.sum_range_reflect (fun j => 10 ^ j) (n - 1)
  simpa [show n - 1 - 1 = n - 2 by omega] using href

lemma sum_pow10_shift2 (m : ℕ) :
    ∑ j ∈ Finset.range (m + 2), 10 ^ j = 11 + 100 * ∑ j ∈ Finset.range m, 10 ^ j := by
  rw [show m + 2 = 2 + m by omega, Finset.sum_range_add,
      Finset.sum_range_succ, Finset.sum_range_one, Finset.mul_sum]
  have htail : ∑ x ∈ Finset.range m, 10 ^ (2 + x) = ∑ x ∈ Finset.range m, 100 * 10 ^ x := by
    apply Finset.sum_congr rfl
    intro j _; rw [pow_add]; ring
  rw [htail]
  omega

lemma a_step2 (n : ℕ) (hn : 4 ≤ n) : a n = 100 * a (n - 2) + 11 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have hst1 : state (2 * (k + 2)) = patEven := by
      simpa [show 2 * (k + 2) = 2 * (k + 1) + 2 by omega] using (state_ge2 (k + 1)).1
    have hst0 : state (2 * (k + 2) - 2) = patEven := by
      simpa [show 2 * (k + 2) - 2 = 2 * k + 2 by omega] using (state_ge2 k).1
    unfold a
    rw [hst1, hst0]
    have hf : ∀ u : ℤ, 2 ≤ u → patEven u u = true := by
      intro u hu; unfold patEven; simp [abs_of_nonneg (by omega : (0 : ℤ) ≤ u), hu]
    rw [sum_tail10 (2 * (k + 2)) (by omega) patEven hf,
        sum_tail10 (2 * (k + 2) - 2) (by omega) patEven hf]
    have p0 : patEven 0 0 = true := by decide
    have p1 : patEven 1 1 = false := by decide
    rw [p0, p1]
    simp only [Bool.toNat_true, Bool.toNat_false, one_mul, zero_mul, add_zero]
    have he1 : 2 * (k + 2) - 1 = (2 * k + 1) + 2 := by omega
    have he2 : 2 * (k + 2) - 2 - 1 = 2 * k + 1 := by omega
    have hp10 : 10 ^ (2 * (k + 2)) = 100 * 10 ^ (2 * (k + 2) - 2) := by
      have he : 2 * (k + 2) = 2 + (2 * (k + 2) - 2) := by omega
      rw [he, pow_add]; norm_num
    rw [he1, he2, sum_pow10_shift2 (2 * k + 1), hp10]
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have hst1 : state (2 * (k + 2) + 1) = patOdd := by
      simpa [show 2 * (k + 2) + 1 = 2 * (k + 1) + 3 by omega] using (state_ge2 (k + 1)).2
    have hst0 : state (2 * (k + 2) + 1 - 2) = patOdd := by
      simpa [show 2 * (k + 2) + 1 - 2 = 2 * k + 3 by omega] using (state_ge2 k).2
    unfold a
    rw [hst1, hst0]
    have hf : ∀ u : ℤ, 2 ≤ u → patOdd u u = true := by
      intro u hu; unfold patOdd; simp [abs_of_nonneg (by omega : (0 : ℤ) ≤ u), hu]
    rw [sum_tail10 (2 * (k + 2) + 1) (by omega) patOdd hf,
        sum_tail10 (2 * (k + 2) + 1 - 2) (by omega) patOdd hf]
    have p0 : patOdd 0 0 = false := by decide
    have p1 : patOdd 1 1 = false := by decide
    rw [p0, p1]
    simp only [Bool.toNat_false, zero_mul, zero_add]
    have he1 : 2 * (k + 2) + 1 - 1 = (2 * k + 2) + 2 := by omega
    have he2 : 2 * (k + 2) + 1 - 2 - 1 = 2 * k + 2 := by omega
    rw [he1, he2, sum_pow10_shift2 (2 * k + 2)]
    ring

lemma rec_rel (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = a (n - 1) + 100 * a (n - 2) - 100 * a (n - 3) := by
  have s0 := a_step2 n (by omega)
  have s1 := a_step2 (n - 1) (by omega)
  rw [show n - 1 - 2 = n - 3 by omega] at s1
  omega

set_option maxHeartbeats 1000000 in
lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 10 * X) * (1 + 10 * X)) =
      1 - 90 * X ^ 3 + 100 * X ^ 4 := by
  let s := PowerSeries.mk (fun n => (a n : ℤ))
  have hd : s * ((1 - X) * (1 - 10 * X) * (1 + 10 * X)) =
      s * X ^ 0 + (-1 : ℤ) • (s * X ^ 1) + (-100 : ℤ) • (s * X ^ 2) +
      (100 : ℤ) • (s * X ^ 3) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have hp : (1 - 90 * X ^ 3 + 100 * X ^ 4 : PowerSeries ℤ) =
      X ^ 0 + (-90 : ℤ) • X ^ 3 + (100 : ℤ) • X ^ 4 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [hd, hp]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
  by_cases hn : n < 5
  · have v0 : a 0 = 1 := by decide
    have v1 : a 1 = 1 := by decide
    have v2 : a 2 = 101 := by decide
    have v3 : a 3 = 11 := by decide
    have v4 : a 4 = 10111 := by decide
    interval_cases n <;> norm_num [zsmul_eq_mul, v0, v1, v2, v3, v4]
  · have hr := rec_rel n (by omega)
    simp only [if_pos (show 0 ≤ n by omega), Nat.sub_zero, zsmul_eq_mul,
      if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega)]
    norm_num
    linarith only [hr]

end Proof_a290072

theorem OMA.solution : type_of% @OMA.S_oeis_a290072.main :=
  ⟨gf_eq, rec_rel, a_eq_ref⟩
