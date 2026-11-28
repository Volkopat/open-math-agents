import OMAReductions.R_oeis_a067129_R1

-- Step oeis-a067129.R1.H1: hypothesis H1 of reduction oeis-a067129.R1
-- Credit: @sovrana

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

theorem sig_pp_mod (p e : ℕ) (hp : p.Prime) (hodd : p % 2 = 1) :
    (σ 1 (p ^ e)) % 2 = (e + 1) % 2 := by
  rw [sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hodd]
    simp <;> omega

theorem sig_two_pow_odd (e : ℕ) : Odd (σ 1 (2 ^ e)) := by
  rw [sigma_one_apply, Nat.sum_divisors_prime_pow Nat.prime_two, Nat.odd_iff]
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih]
    have : 2 ^ (e + 1) % 2 = 0 := by
      rw [pow_succ]; simp
    rw [this]

theorem odd_sq_sigma_odd : ∀ u : ℕ, Odd u → Odd (σ 1 (u ^ 2)) := by
  intro u
  refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ u
  · intro p n hp hn hodd
    have hpo : Odd p := by
      rcases hp.eq_two_or_odd' with h2 | h2
      · exfalso
        subst h2
        exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hn.ne'⟩)
      · exact h2
    rw [← pow_mul, Nat.odd_iff, sig_pp_mod p (n * 2) hp (Nat.odd_iff.1 hpo)]
    omega
  · intro h; exact absurd h (by decide)
  · intro _; simp
  · intro a b _ _ hcop ha hb hodd
    obtain ⟨hao, hbo⟩ := Nat.odd_mul.1 hodd
    rw [mul_pow, isMultiplicative_sigma.map_mul_of_coprime (Nat.Coprime.pow 2 2 hcop)]
    exact (ha hao).mul (hb hbo)

theorem nonsq_even (N : ℕ) (hN : Odd N) (hns : ¬ IsSquare N) : Even (σ 1 N) := by
  have hN0 : N ≠ 0 := by rintro rfl; exact absurd hN (by decide)
  obtain ⟨a, b, hab, hsq⟩ := Nat.sq_mul_squarefree N
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hns ⟨b, by rw [← hab]; ring⟩
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab; exact hN0 hab.symm
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab; exact hN0 hab.symm
  have hp : (a.minFac).Prime := Nat.minFac_prime ha1
  set p := a.minFac with hpdef
  obtain ⟨a', ha'⟩ : p ∣ a := Nat.minFac_dvd a
  have hpa' : ¬ p ∣ a' := by
    intro h
    obtain ⟨c, hc⟩ := h
    have : p * p ∣ a := ⟨c, by rw [ha', hc]; ring⟩
    have := hsq _ this
    exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)
  obtain ⟨f, b', hb', hbf⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb0 p hp.ne_one
  have hNeq : N = p ^ (2 * f + 1) * (b' ^ 2 * a') := by
    rw [← hab, hbf, ha']; ring
  have hnd : ¬ p ∣ b' ^ 2 * a' := by
    intro h
    rcases hp.dvd_mul.1 h with h | h
    · exact hb' (hp.dvd_of_dvd_pow h)
    · exact hpa' h
  have hcop : Nat.Coprime (p ^ (2 * f + 1)) (b' ^ 2 * a') :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
  have hpodd : p % 2 = 1 := by
    have hpN : p ∣ N := by rw [hNeq]; exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
    rcases hp.eq_two_or_odd with h | h
    · exfalso
      rw [h] at hpN
      obtain ⟨t, ht⟩ := hN
      omega
    · exact h
  rw [hNeq, isMultiplicative_sigma.map_mul_of_coprime hcop]
  apply Even.mul_right
  rw [Nat.even_iff, sig_pp_mod p _ hp hpodd]
  omega

theorem sig2 (c m : ℕ) (hm : 0 < m) : Odd (σ 1 (2 ^ c * m ^ 2)) := by
  obtain ⟨f, u, hu, hm'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' 2 (by norm_num)
  have hE : 2 ^ c * m ^ 2 = 2 ^ (c + 2 * f) * u ^ 2 := by
    rw [hm']; ring
  have hcop : Nat.Coprime (2 ^ (c + 2 * f)) (u ^ 2) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hu)
  have huodd : Odd u := by
    rw [Nat.odd_iff]; omega
  rw [hE, isMultiplicative_sigma.map_mul_of_coprime hcop]
  exact (sig_two_pow_odd _).mul (odd_sq_sigma_odd u huodd)

theorem sqmod8 (r : ℕ) : r * r % 8 = 0 ∨ r * r % 8 = 1 ∨ r * r % 8 = 4 := by
  have h := Nat.mod_lt r (by norm_num : 8 > 0)
  interval_cases hr : r % 8 <;> simp [Nat.mul_mod, hr]

theorem sol : ∀ k m : ℕ, Even k → (k = m ^ 2 ∨ k = 2 * m ^ 2) →
    ¬ (OMA.S_oeis_a067129.IsTerm k) := by
  intro k m hk hform ⟨h4, hsum⟩
  simp only [OMA.S_oeis_a067129.sigma, ← sigma_one_apply] at hsum
  rcases Nat.eq_or_lt_of_le h4 with h | h
  · subst h
    revert hsum
    decide +kernel
  have hk4 : 5 ≤ k := h
  have hm0 : 0 < m := by
    rcases hform with rfl | rfl <;> (rcases Nat.eq_zero_or_pos m with rfl | h' <;> simp_all)
  rcases hform with hf | hf
  · -- k = m^2, m even
    have hme : m % 2 = 0 := by
      obtain ⟨t, ht⟩ := hk
      have : m ^ 2 % 2 = 0 := by omega
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · exact h
      · exfalso; rw [Nat.pow_mod, h] at this; simp at this
    have hodd : Odd (σ 1 (2 * k)) := by
      have := sig2 1 m hm0
      rw [hf]; simpa using this
    have hp : Even (σ 1 (k + 3)) := by
      apply nonsq_even
      · obtain ⟨t, ht⟩ := hk; exact ⟨t + 1, by omega⟩
      · rintro ⟨r, hr⟩
        have h1 := sqmod8 m
        have h2 := sqmod8 r
        have : m * m % 2 = 0 := by rw [Nat.mul_mod, hme]
        have hk' : k = m * m := by rw [hf]; ring
        omega
    have hm' : Even (σ 1 (k - 3)) := by
      apply nonsq_even
      · obtain ⟨t, ht⟩ := hk; exact ⟨t - 2, by omega⟩
      · rintro ⟨r, hr⟩
        have hk' : k = m * m := by rw [hf]; ring
        have e : m * m = r * r + 3 := by omega
        have hlt : r < m := by
          by_contra hc
          push Not at hc
          have := Nat.mul_le_mul hc hc
          omega
        have : r + 1 ≤ m := hlt
        have h5 : r ≤ 1 := by nlinarith
        interval_cases r
        · have : m * m = 3 := by omega
          have : m ≤ 1 := by nlinarith
          interval_cases m <;> omega
        · have : m * m = 4 := by omega
          have : m ≤ 2 := by nlinarith
          interval_cases m <;> omega
    rw [← hsum] at hodd
    have : Even (σ 1 (k - 3) + σ 1 (k + 3)) := hm'.add hp
    exact (Nat.not_even_iff_odd.2 hodd) this
  · -- k = 2 m^2
    have hodd : Odd (σ 1 (2 * k)) := by
      have := sig2 2 m hm0
      rw [hf]; have e : 2 * (2 * m ^ 2) = 2 ^ 2 * m ^ 2 := by ring
      rw [e]; exact this
    have hk' : k = 2 * (m * m) := by rw [hf]; ring
    have h1 := sqmod8 m
    have hp : Even (σ 1 (k + 3)) := by
      apply nonsq_even
      · obtain ⟨t, ht⟩ := hk; exact ⟨t + 1, by omega⟩
      · rintro ⟨r, hr⟩
        have h2 := sqmod8 r
        omega
    have hm' : Even (σ 1 (k - 3)) := by
      apply nonsq_even
      · obtain ⟨t, ht⟩ := hk; exact ⟨t - 2, by omega⟩
      · rintro ⟨r, hr⟩
        have h2 := sqmod8 r
        omega
    rw [← hsum] at hodd
    have : Even (σ 1 (k - 3) + σ 1 (k + 3)) := hm'.add hp
    exact (Nat.not_even_iff_odd.2 hodd) this

theorem OMA.solution : OMA.R_oeis_a067129_R1.H1 := sol
