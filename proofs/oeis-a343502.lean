import OMAStatements.S_oeis_a343502

open OMA.S_oeis_a343502

lemma tau_two_pow (a : ℕ) : tau (2 ^ a) = a + 1 := by
  unfold tau
  rw [Nat.divisors_prime_pow Nat.prime_two, Finset.card_map, Finset.card_range]

/-- If an even number has a prime number of divisors, it is a power of two. -/
lemma even_tau_prime (n : ℕ) (hn : n ≠ 0) (he : 2 ∣ n) (hq : (tau n).Prime) :
    ∃ a : ℕ, n = 2 ^ a ∧ tau n = a + 1 := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hcop : (2 ^ a).Coprime m := (Nat.coprime_two_left.2 hm).pow_left a
  have hmul : tau (2 ^ a * m) = (a + 1) * tau m := by
    unfold tau
    rw [Nat.Coprime.card_divisors_mul hcop]
    rw [← tau, ← tau, tau_two_pow]
  have ha : a ≠ 0 := by
    rintro rfl
    simp only [pow_zero, one_mul] at he
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 he)
  rw [hmul] at hq
  have hm1 : tau m = 1 := by
    rcases Nat.prime_mul_iff.1 hq with ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · omega
  have : m = 1 := (Nat.divisors_card_eq_one_iff m).1 hm1
  subst this
  exact ⟨a, by simp, by rw [mul_one, tau_two_pow]⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a343502.main := by
  intro k h1 h2 hk2 hk3
  have hk1 : 1 < k := by
    rcases (show k = 0 ∨ k = 1 ∨ 1 < k by omega) with rfl | rfl | h
    · exfalso
      simp [tau, Nat.not_prime_zero] at h1
    · exfalso
      simp [tau, Nat.not_prime_one] at h1
    · exact h
  refine ⟨hk1, fun hk => ?_⟩
  have hodd : k % 2 = 1 := by
    rcases hk.eq_two_or_odd with h | h
    · exact absurd h hk2
    · exact h
  obtain ⟨a, ha, hta⟩ := even_tau_prime (k + 1) (by omega) (by omega) h2
  rw [hta] at h2
  have hk' : k = 2 ^ a - 1 := by omega
  have ha1 : a ≠ 1 := by
    rintro rfl
    omega
  have hpa := (Nat.prime_of_pow_sub_one_prime ha1 (hk' ▸ hk)).2
  have ha2 : a = 2 := by
    rcases hpa.eq_two_or_odd with h | h
    · exact h
    · rcases h2.eq_two_or_odd with h' | h'
      · have := hpa.two_le
        omega
      · omega
  subst ha2
  omega
