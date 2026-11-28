import OMAStatements.S_oeis_a023408

namespace OMA.S_oeis_a023408





lemma ten_pow (k : ℕ) : 10 ^ k = 2 ^ k * 5 ^ k := by rw [← mul_pow]; norm_num

lemma odd_five_pow (k : ℕ) : Odd (5 ^ k) := Odd.pow (by decide)

/-- Divisibility and the sum invariant: for k >= 1, x56 k + x34 k = 10^k; always 2^k divides
both. -/
lemma invariant (k : ℕ) : 2 ^ k ∣ x56 k ∧ 2 ^ k ∣ x34 k ∧ (1 ≤ k → x56 k + x34 k = 10 ^ k) := by
  induction k with
  | zero => simp [x56, x34]
  | succ k ih =>
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩, hsum⟩ := ih
    have h5 := odd_five_pow k
    have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    have hpos : 0 < 2 ^ k := by positivity
    -- divisibility of x + d * 10^k by 2^(k+1) is the parity of (quotient + d * 5^k)
    have key : ∀ w d : ℕ, (2 ^ (k + 1) ∣ 2 ^ k * w + d * 10 ^ k ↔ 2 ∣ w + d * 5 ^ k) := by
      intro w d
      rw [ten_pow, hpow, show 2 ^ k * w + d * (2 ^ k * 5 ^ k) = 2 ^ k * (w + d * 5 ^ k) by ring]
      exact Nat.mul_dvd_mul_iff_left hpos
    rcases Nat.even_or_odd u with hue | huo
    · -- u even: x56 takes 6
      have c5 : ¬ 2 ^ (k + 1) ∣ x56 k + 5 * 10 ^ k := by
        rw [hu, key]
        rintro h
        have : Odd (u + 5 * 5 ^ k) := hue.add_odd (Odd.mul (by decide) h5)
        exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h)
      have c6 : 2 ^ (k + 1) ∣ x56 k + 6 * 10 ^ k := by
        rw [hu, key]
        exact even_iff_two_dvd.mp (hue.add (Even.mul_right (by decide) _))
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · -- k = 0: x56 1 = 6, x34 1 = 4
        refine ⟨by simp [x56], by simp [x34], fun _ => by simp [x56, x34]⟩
      · have huv : u + v = 5 ^ k := by
          have := hsum hk
          rw [hu, hv, ten_pow, ← mul_add] at this
          exact Nat.eq_of_mul_eq_mul_left hpos this
        have hvo : Odd v := by
          have : Odd (u + v) := by rw [huv]; exact h5
          rcases Nat.even_or_odd v with hve | hvo
          · exact absurd this (Nat.not_odd_iff_even.mpr (hue.add hve))
          · exact hvo
        have c3 : 2 ^ (k + 1) ∣ x34 k + 3 * 10 ^ k := by
          rw [hv, key]
          exact even_iff_two_dvd.mp (hvo.add_odd (Odd.mul (by decide) h5))
        simp only [x56, x34, if_neg c5, if_pos c3]
        refine ⟨c6, c3, fun _ => ?_⟩
        have := hsum hk
        rw [pow_succ]
        nlinarith
    · -- u odd: x56 takes 5
      have c5 : 2 ^ (k + 1) ∣ x56 k + 5 * 10 ^ k := by
        rw [hu, key]
        exact even_iff_two_dvd.mp (huo.add_odd (Odd.mul (by decide) h5))
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · have hu0 : u = 0 := by simp [x56] at hu; omega
        rw [hu0] at huo
        exact absurd huo (by decide)
      · have huv : u + v = 5 ^ k := by
          have := hsum hk
          rw [hu, hv, ten_pow, ← mul_add] at this
          exact Nat.eq_of_mul_eq_mul_left hpos this
        have hve : Even v := by
          have : Odd (u + v) := by rw [huv]; exact h5
          rcases Nat.even_or_odd v with hve | hvo
          · exact hve
          · exact absurd this (Nat.not_odd_iff_even.mpr (huo.add_odd hvo))
        have c3 : ¬ 2 ^ (k + 1) ∣ x34 k + 3 * 10 ^ k := by
          rw [hv, key]
          rintro h
          have : Odd (v + 3 * 5 ^ k) := hve.add_odd (Odd.mul (by decide) h5)
          exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h)
        have c4 : 2 ^ (k + 1) ∣ x34 k + 4 * 10 ^ k := by
          rw [hv, key]
          exact even_iff_two_dvd.mp (hve.add (Even.mul_right (by decide) _))
        simp only [x56, x34, if_pos c5, if_neg c3]
        refine ⟨c5, c4, fun _ => ?_⟩
        have := hsum hk
        rw [pow_succ]
        nlinarith

/-- The digit added at step k is 5 or 6 (resp. 3 or 4), and the numbers stay below 10^k. -/
lemma x56_succ (k : ℕ) : ∃ d, (d = 5 ∨ d = 6) ∧ x56 (k + 1) = x56 k + d * 10 ^ k := by
  simp only [x56]
  split_ifs
  · exact ⟨5, Or.inl rfl, rfl⟩
  · exact ⟨6, Or.inr rfl, rfl⟩

lemma x34_succ (k : ℕ) : ∃ e, (e = 3 ∨ e = 4) ∧ x34 (k + 1) = x34 k + e * 10 ^ k := by
  simp only [x34]
  split_ifs
  · exact ⟨3, Or.inl rfl, rfl⟩
  · exact ⟨4, Or.inr rfl, rfl⟩

lemma x56_lt (k : ℕ) : x56 k < 10 ^ k := by
  induction k with
  | zero => simp [x56]
  | succ k ih =>
    obtain ⟨d, hd, h⟩ := x56_succ k
    rw [h, pow_succ]
    rcases hd with rfl | rfl <;> omega

lemma x34_lt (k : ℕ) : x34 k < 10 ^ k := by
  induction k with
  | zero => simp [x34]
  | succ k ih =>
    obtain ⟨e, he, h⟩ := x34_succ k
    rw [h, pow_succ]
    rcases he with rfl | rfl <;> omega

lemma digit (x d k : ℕ) (hx : x < 10 ^ k) (hd : d < 10) : (x + d * 10 ^ k) / 10 ^ k % 10 = d := by
  have hpos : 0 < 10 ^ k := by positivity
  rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hx, zero_add, Nat.mod_eq_of_lt hd]

/-- Lowell's conjecture: a(n) + A023402(n) = 9 for every n > 1. -/
theorem conjecture (n : ℕ) (hn : 1 < n) : a n + b n = 9 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨d, hd, hx⟩ := x56_succ k
  obtain ⟨e, he, hy⟩ := x34_succ k
  have ha : a (k + 1) = d := by
    unfold a
    rw [Nat.add_sub_cancel, hx]
    exact digit _ _ _ (x56_lt k) (by omega)
  have hb : b (k + 1) = e := by
    unfold b
    rw [Nat.add_sub_cancel, hy]
    exact digit _ _ _ (x34_lt k) (by omega)
  rw [ha, hb]
  have s1 := (invariant k).2.2 (by omega)
  have s2 := (invariant (k + 1)).2.2 (by omega)
  rw [hx, hy, pow_succ] at s2
  have hpos : 0 < 10 ^ k := by positivity
  have : (d + e) * 10 ^ k = 9 * 10 ^ k := by nlinarith
  exact Nat.eq_of_mul_eq_mul_right hpos this

end OMA.S_oeis_a023408

theorem OMA.solution : type_of% @OMA.S_oeis_a023408.main :=
  fun n hn => OMA.S_oeis_a023408.conjecture n hn
