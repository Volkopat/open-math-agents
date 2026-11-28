import OMAStatements.S_oeis_a363796

namespace OMA.S_oeis_a363796



/-- Sophie Germain: `X ^ 4 + 4 * 20 ^ 4` is never prime. -/
theorem not_prime_germain (X : ℕ) : ¬ (X ^ 4 + 640000).Prime := by
  have hle : 40 * X ≤ X ^ 2 + 800 := by nlinarith [sq_nonneg ((X : ℤ) - 20)]
  have hfac : X ^ 4 + 640000 = (X ^ 2 + 40 * X + 800) * (X ^ 2 + 800 - 40 * X) := by
    zify [hle]
    ring
  have hB : 400 ≤ X ^ 2 + 800 - 40 * X := by
    have : 40 * X + 400 ≤ X ^ 2 + 800 := by nlinarith [sq_nonneg ((X : ℤ) - 20)]
    omega
  rw [hfac]
  exact Nat.not_prime_mul (by nlinarith) (by omega)

theorem a_320000 : a 320000 = -1 := by
  unfold a
  rw [dif_neg]
  rintro ⟨p, -, hp⟩
  have : p ^ 320000 + 2 * 320000 = (p ^ 80000) ^ 4 + 640000 := by
    rw [← pow_mul]
  rw [this] at hp
  exact not_prime_germain _ hp

theorem prime_dvd_640001 {q : ℕ} (hq : q.Prime) (h : q ∣ 640001) : q = 29 ∨ q = 761 := by
  have h29 : Nat.Prime 29 := by norm_num
  have h761 : Nat.Prime 761 := by norm_num
  rw [show (640001 : ℕ) = 29 * 29 * 761 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hq).mp h1 with h2 | h2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq h29).mp h2)
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq h29).mp h2)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq h761).mp h1)

theorem not_form : ¬ IsForm 320000 := by
  rintro ⟨q, hq, hq2, k, hk⟩
  obtain ⟨r, hr⟩ := hq.odd_of_ne_two hq2
  have hqz : (q : ℤ) = 2 * r + 1 := by rw [hr]; push_cast; ring
  -- with q = 2r + 1, (q^2 - 1)/2 = 2r^2 + 2r
  have hdiv : ((q : ℤ) ^ 2 - 1) / 2 = 2 * (r : ℤ) ^ 2 + 2 * r := by
    rw [hqz, show ((2 * (r : ℤ) + 1) ^ 2 - 1) = 2 * (2 * (r : ℤ) ^ 2 + 2 * r) by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [hdiv] at hk
  push_cast at hk
  have h1 : (640001 : ℤ) = (q : ℤ) * ((q : ℤ) + 2 * k * ((q : ℤ) - 1)) := by
    rw [hqz] at hk ⊢
    linear_combination 2 * hk
  have hqdvd : q ∣ 640001 := by
    have : ((q : ℕ) : ℤ) ∣ ((640001 : ℕ) : ℤ) := ⟨_, by push_cast; exact h1⟩
    exact Int.natCast_dvd_natCast.mp this
  rcases prime_dvd_640001 hq hqdvd with h | h
  · -- q = 29: 320000 = 420 + 812 k has no integer solution
    subst h
    norm_num at hk
    omega
  · -- q = 761: 320000 = 289560 + 579360 k has no integer solution
    subst h
    norm_num at hk
    omega

/-! Controls: the entry's terms a(1) = 3 and a(12) = -1 (Israel's case q = 5, k = 0). -/

theorem a_1 : a 1 = 3 := by
  unfold a
  have h : ∃ p : ℕ, p.Prime ∧ (p ^ 1 + 2 * 1).Prime := ⟨3, by norm_num, by norm_num⟩
  rw [dif_pos h]
  have h3 : Nat.find h = 3 := by
    rw [Nat.find_eq_iff]
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    rintro m hm ⟨hmp, hmq⟩
    interval_cases m
    · norm_num at hmp
    · norm_num at hmp
    · norm_num at hmq
  rw [h3]
  rfl

theorem a_12 : a 12 = -1 := by
  unfold a
  rw [dif_neg]
  rintro ⟨p, hp, hpq⟩
  by_cases h5 : p = 5
  · subst h5
    norm_num at hpq
  · have hp5 : p % 5 ≠ 0 := fun h0 =>
      h5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp (Nat.dvd_of_mod_eq_zero h0)).symm
    have hpow : p ^ 12 % 5 = 1 := by
      rw [Nat.pow_mod]
      have := Nat.mod_lt p (show 5 > 0 by norm_num)
      interval_cases h : p % 5 <;> simp_all
    have hdvd : 5 ∣ p ^ 12 + 2 * 12 := by omega
    exact Nat.not_prime_of_dvd_of_lt hdvd (by norm_num) (by omega) hpq

theorem disproof : ¬ (∀ n : ℕ, 1 ≤ n → a n = -1 → IsForm n) :=
  fun h => not_form (h 320000 (by norm_num) a_320000)

end OMA.S_oeis_a363796

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a363796.main) :=
  OMA.S_oeis_a363796.disproof
