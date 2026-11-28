import OMAStatements.S_oeis_a269018

-- Problem: A269018: Primes p of the form 2^k + 2*(-1)^k - 1.
-- Upstream: formal-conjectures statements/oeis-a269018.lean:0 (declaration OMA.S_oeis_a269018.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for even k = 2j the form is 2^(2j) + 1; j = 0 gives p = 2, and for j >= 1 primality
-- forces 2j = 2^m (Nat.pow_of_pow_add_prime), so p is a Fermat prime, and p >= 5. For odd
-- k = 2j+1 the form is 2^(2j+1) - 3, which is == 2 (mod 3) because 4^j == 1 (mod 3). Conversely
-- 2 comes from k = 0, a Fermat prime 2^(2^m) + 1 with m >= 1 from the even k = 2^m, and a prime
-- p = 2^n - 3 with p == 2 (mod 3) has n odd (for even n, p + 3 = 4^(n/2) == 1 mod 3), so it
-- comes from k = n.

open OMA.S_oeis_a269018 in
theorem OMA.solution : type_of% @OMA.S_oeis_a269018.main := by
  intro p
  constructor
  · rintro ⟨hp, k, hk⟩
    obtain ⟨j, rfl | rfl⟩ : ∃ j, k = 2 * j ∨ k = 2 * j + 1 := ⟨k / 2, by omega⟩
    · rw [Even.neg_one_pow (even_two_mul j)] at hk
      have hpz : (p : ℤ) = 2 ^ (2 * j) + 1 := by linarith
      have hpn : p = 2 ^ (2 * j) + 1 := by exact_mod_cast hpz
      rcases Nat.eq_zero_or_pos j with hj | hj
      · left
        subst hj
        norm_num [hpn]
      · right
        left
        have hP : (2 ^ (2 * j) + 1).Prime := by
          rw [← hpn]
          exact hp
        obtain ⟨m, hm⟩ :=
          Nat.pow_of_pow_add_prime (by norm_num : 1 < 2) (by omega : 2 * j ≠ 0) hP
        refine ⟨⟨hp, m, by rw [hpn, hm]⟩, ?_⟩
        intro h3
        have h4 : 4 ≤ 2 ^ (2 * j) := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (2 * j) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    · rw [Odd.neg_one_pow (odd_two_mul_add_one j)] at hk
      have hk2 : (p : ℤ) = 2 ^ (2 * j + 1) - 3 := by linarith
      have hpc : ((p + 3 : ℕ) : ℤ) = ((2 ^ (2 * j + 1) : ℕ) : ℤ) := by
        push_cast
        linarith
      have hpn : p + 3 = 2 ^ (2 * j + 1) := by exact_mod_cast hpc
      have h2 : 2 ^ (2 * j + 1) % 3 = 2 := by
        rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
        norm_num
      right
      right
      exact ⟨hp, by omega, 2 * j + 1, hk2⟩
  · rintro (rfl | ⟨⟨hp, m, hm⟩, hne⟩ | ⟨hp, hmod, n, hn⟩)
    · exact ⟨Nat.prime_two, 0, by norm_num⟩
    · refine ⟨hp, 2 ^ m, ?_⟩
      have hm0 : m ≠ 0 := by
        rintro rfl
        apply hne
        norm_num [hm]
      have hev : Even (2 ^ m) := (Nat.even_pow' hm0).mpr even_two
      rw [Even.neg_one_pow hev]
      have hpz : (p : ℤ) = 2 ^ 2 ^ m + 1 := by exact_mod_cast hm
      linarith
    · refine ⟨hp, n, ?_⟩
      obtain ⟨i, rfl | rfl⟩ : ∃ i, n = 2 * i ∨ n = 2 * i + 1 := ⟨n / 2, by omega⟩
      · exfalso
        have hpc : ((p + 3 : ℕ) : ℤ) = ((2 ^ (2 * i) : ℕ) : ℤ) := by
          push_cast
          linarith
        have hpn : p + 3 = 2 ^ (2 * i) := by exact_mod_cast hpc
        have h1 : 2 ^ (2 * i) % 3 = 1 := by
          rw [pow_mul, Nat.pow_mod]
          norm_num
        omega
      · rw [Odd.neg_one_pow (odd_two_mul_add_one i)]
        linarith
