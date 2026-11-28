import OMAStatements.S_oeis_a387426

open OMA.S_oeis_a387426 in
theorem OMA.solution : type_of% @OMA.S_oeis_a387426.main := by
  have refute : ∀ {k} m m', 1 ≤ m → m ≤ k → 1 ≤ m' → m' ≤ k → m ≠ m' → 2 * k % m ≠ 0 →
      2 * k % m' ≠ 0 → 2 * k % m * m' = 2 * k % m' * m → ¬ InSeq k := by
    intro k m m' h1 h2 h3 h4 hne hr hr' heq hin
    exact hne <| hin ⟨h1, h2, hr⟩ ⟨h3, h4, hr'⟩ <| by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      exact_mod_cast heq
  have H : ∀ {A x y : ℕ}, 0 < A → Odd x → Odd y → 3 ≤ x → 4 ≤ y → ¬ InSeq (A * x * y) := by
    intro A x y hA hx hy hx3 hy4
    have e1 : 2 * (A * x * y) % (4 * A) = 2 * A := by
      rw [show 2 * (A * x * y) = 2 * A * (x * y) by ring, show 4 * A = 2 * A * 2 by ring,
        Nat.mul_mod_mul_left, Nat.odd_iff.mp (hx.mul hy), mul_one]
    have e2 : 2 * (A * x * y) % (4 * A * x) = 2 * A * x := by
      rw [show 2 * (A * x * y) = 2 * A * x * y by ring, show 4 * A * x = 2 * A * x * 2 by ring,
        Nat.mul_mod_mul_left, Nat.odd_iff.mp hy, mul_one]
    exact refute (4 * A) (4 * A * x) (by omega) (by nlinarith [Nat.mul_le_mul hx3 hy4])
      (by nlinarith) (by nlinarith [Nat.mul_pos hA (by omega : 0 < x)]) (by nlinarith)
      (by omega) (by rw [e2]; positivity) (by rw [e1, e2]; ring)
  have T : ∀ {B t : ℕ}, 0 < B → ¬ 3 ∣ t → t % 2 = 0 → 12 ≤ t → ¬ InSeq (B * t) := by
    intro B t hB ht3 ht2 ht12
    have e1 : 2 * (B * t) % (B * 3) = B * (2 * t % 3) := by
      rw [show 2 * (B * t) = B * (2 * t) by ring, Nat.mul_mod_mul_left]
    have e2 : 2 * (B * t) % (B * 12) = B * (4 * (2 * t % 3)) := by
      rw [show 2 * (B * t) = B * (2 * t) by ring, Nat.mul_mod_mul_left]; congr 1; omega
    exact refute (B * 3) (B * 12) (by omega) (by nlinarith) (by omega) (by nlinarith) (by omega)
      (by rw [e1]; exact mul_ne_zero (by omega) (by omega))
      (by rw [e2]; exact mul_ne_zero (by omega) (by omega)) (by rw [e1, e2]; ring)
  refine ⟨?_, ?_⟩
  · intro p hp
    rintro a ⟨ha1, hap, hra⟩ b ⟨hb1, hbp, hrb⟩ heq
    have hq : 2 * p % a * b = 2 * p % b * a := by
      rw [div_eq_div_iff (by positivity) (by positivity)] at heq
      exact_mod_cast heq
    clear heq
    by_contra hne
    wlog hab : a < b generalizing a b
    · exact this hb1 hbp hrb ha1 hap hra hq.symm (Ne.symm hne) (by omega)
    have ha3 : 3 ≤ a := by by_contra; interval_cases a <;> omega
    have hbp' : b < p := by rcases hbp.lt_or_eq with h | rfl; exact h; simp at hrb
    have hqle : 2 * p / b ≤ 2 * p / a := Nat.div_le_div_left hab.le (by omega)
    have hEq : a * b * (2 * p / a - 2 * p / b) = p * (2 * (b - a)) := by
      have h1 := Nat.div_add_mod (2 * p) a
      have h2 := Nat.div_add_mod (2 * p) b
      zify [hqle, hab.le] at h1 h2 hq ⊢
      linear_combination (b : ℤ) * h1 - (a : ℤ) * h2 - hq
    have hpos : 0 < 2 * p / a - 2 * p / b :=
      Nat.pos_of_ne_zero fun h => by
        rw [h, mul_zero] at hEq
        exact absurd hEq.symm (mul_ne_zero hp.ne_zero (by omega))
    have hpq : p ∣ 2 * p / a - 2 * p / b := by
      rcases hp.dvd_mul.mp ⟨_, hEq⟩ with h | h
      · rcases hp.dvd_mul.mp h with h | h <;> exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
      · exact h
    have : 3 * b * p ≤ a * b * (2 * p / a - 2 * p / b) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right b ha3) (Nat.le_of_dvd hpos hpq)
    have := hp.pos
    nlinarith [Nat.sub_le b a]
  · intro k hk hnp
    obtain ⟨a, u, hu2, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : k ≠ 0) 2 (by norm_num)
    have huo : Odd u := Nat.odd_iff.mpr (by omega)
    rcases a with _ | a
    · simp only [pow_zero, one_mul] at *
      obtain ⟨d, ⟨e, rfl⟩, hd2, hdu⟩ := Nat.exists_dvd_of_not_prime2 (by omega : 2 ≤ u) hnp
      obtain ⟨hdo, heo⟩ := Nat.odd_mul.mp huo
      rcases le_or_gt 4 e with he4 | he4
      · simpa using H (A := 1) (x := d) (y := e) (by omega) hdo heo
          (by have := Nat.odd_iff.mp hdo; omega) he4
      · rw [mul_comm]
        have he2 : 2 ≤ e := by nlinarith
        simpa using H (A := 1) (x := e) (y := d) (by omega) heo hdo
          (by have := Nat.odd_iff.mp heo; omega) (by nlinarith)
    · have h32 : ¬ 3 ∣ 2 ^ (a + 1) := fun h => by
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h; omega
      by_cases h3 : 3 ∣ u
      · obtain ⟨y, rfl⟩ := h3
        have hyo := (Nat.odd_mul.mp huo).2
        rcases le_or_gt 4 y with hy | hy
        · rw [← mul_assoc]; exact H (by positivity) (by decide) hyo le_rfl hy
        · rcases le_or_gt 3 a with ha3 | ha3
          · rw [mul_comm]
            exact T (by have := Nat.odd_iff.mp hyo; omega) h32 (by rw [pow_succ]; omega)
              (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_succ ha3)))
          · interval_cases a <;> interval_cases y <;> first
              | omega
              | exact refute 5 30 (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide)
      · simpa using T (B := 1) (t := 2 ^ (a + 1) * u) (by omega)
          (fun h => (Nat.prime_three.dvd_mul.mp h).elim h32 h3) (by simp [pow_succ, Nat.mul_mod])
          (by omega)
