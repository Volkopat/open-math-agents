import OMAStatements.S_oeis_a363798

namespace OMA.S_oeis_a363798



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

theorem term_320000 : IsTerm 320000 := by
  intro p _ hp
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
  rintro ⟨q, hq, hq2, j, hk, -⟩
  obtain ⟨r, hr⟩ := hq.odd_of_ne_two hq2
  subst hr
  -- with q = 2r + 1: (q^2 - 1)/2 = 2r^2 + 2r and q^2 - q = (2r + 1) * 2r
  have h1 : (2 * r + 1) ^ 2 - 1 = 2 * (2 * r ^ 2 + 2 * r) := by
    have : (2 * r + 1) ^ 2 = 2 * (2 * r ^ 2 + 2 * r) + 1 := by ring
    omega
  have h2 : (2 * r + 1) ^ 2 - (2 * r + 1) = (2 * r + 1) * (2 * r) := by
    have : (2 * r + 1) ^ 2 = (2 * r + 1) * (2 * r) + (2 * r + 1) := by ring
    omega
  rw [h1, h2, Nat.mul_div_cancel_left _ (by norm_num)] at hk
  have hqdvd : 2 * r + 1 ∣ 640001 := by
    refine ⟨2 * r + 1 + 4 * j * r, ?_⟩
    have : 640001 = 2 * 320000 + 1 := by norm_num
    rw [this, hk]
    ring
  rcases prime_dvd_640001 hq hqdvd with h | h
  · -- q = 29: 320000 = 420 + 812 j has no solution
    have hr' : r = 14 := by omega
    subst hr'
    omega
  · -- q = 761: 320000 = 289560 + 579360 j has no solution
    have hr' : r = 380 := by omega
    subst hr'
    omega

/-! Controls: 12 and 16 are the entry's first terms (q = 5, j = 0 and q = 3, j = 2). -/

theorem term_12 : IsTerm 12 := by
  intro p hp hpq
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

theorem form_12 : IsForm 12 :=
  ⟨5, by norm_num, by norm_num, 0, by norm_num, by norm_num⟩

theorem disproof : ¬ (∀ k : ℕ, 1 ≤ k → IsTerm k → IsForm k) :=
  fun h => not_form (h 320000 (by norm_num) term_320000)

end OMA.S_oeis_a363798

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a363798.main) :=
  OMA.S_oeis_a363798.disproof
