import OMAStatements.S_oeis_a241675

-- Problem: A241675: a(n) = |{0 < k < n/2: k is a Fibonacci number with x^2 == k (mod n) for no integer x}|.
-- Upstream: formal-conjectures statements/oeis-a241675.lean:0 (declaration OMA.S_oeis_a241675.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea (the entry's own argument): a(n) > 0 iff some Fibonacci k with 0 < k < n/2 is not a
-- square modulo n. For a prime n > 4 this is the conjecture of A241568 at n. If 4 divides n, take
-- k = 2 = F(3) (no square is 2 modulo 4). Otherwise a composite n > 4 has an odd prime divisor p
-- with 2p <= n; for p = 3 take k = 2 (no square is 2 modulo 3), for p > 3 the conjecture gives a
-- Fibonacci k <= (p-1)/2 that is not a square modulo p, hence not modulo n.

open OMA.S_oeis_a241675 in
theorem OMA.solution : type_of% @OMA.S_oeis_a241675.main := by
  have hpos : ∀ n : ℕ, 0 < a n ↔ ∃ k : ℕ, 0 < k ∧ 2 * k < n ∧ (∃ i : ℕ, Nat.fib i = k) ∧
      ∀ x : ℤ, ¬ x ^ 2 ≡ (k : ℤ) [ZMOD (n : ℤ)] := by
    intro n
    have hfin : {k : ℕ | 0 < k ∧ 2 * k < n ∧ (∃ i : ℕ, Nat.fib i = k) ∧
        ∀ x : ℤ, ¬ x ^ 2 ≡ (k : ℤ) [ZMOD (n : ℤ)]}.Finite := by
      apply (Set.finite_lt_nat n).subset
      intro k hk
      have hk2 : 2 * k < n := hk.2.1
      show k < n
      omega
    unfold a
    exact Set.ncard_pos hfin
  have hf3 : Nat.fib 3 = 2 := by decide
  constructor
  · intro H p hp hp3
    have hp4 : 4 < p := by
      by_contra h
      have h4 : p = 4 := by omega
      rw [h4] at hp
      norm_num at hp
    obtain ⟨k, hk0, hk2, hkf, hkx⟩ := (hpos p).mp (H p hp4)
    exact ⟨k, by omega, by omega, hkf, hkx⟩
  · intro C n hn
    rw [hpos]
    by_cases hnp : n.Prime
    · obtain ⟨k, hk1, hk2, hkf, hkx⟩ := C n hnp (by omega)
      exact ⟨k, by omega, by omega, hkf, hkx⟩
    · by_cases h4 : 4 ∣ n
      · refine ⟨2, by norm_num, by omega, ⟨3, hf3⟩, ?_⟩
        intro x hx
        have h4' : (4 : ℤ) ∣ (n : ℤ) := by exact_mod_cast h4
        have hx4 := hx.of_dvd h4'
        rw [Int.ModEq, pow_two, Int.mul_emod] at hx4
        have h0 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
        rcases h0 with h | h | h | h
        · rw [h] at hx4
          norm_num at hx4
        · rw [h] at hx4
          norm_num at hx4
        · rw [h] at hx4
          norm_num at hx4
        · rw [h] at hx4
          norm_num at hx4
      · obtain ⟨p, hp, hp2, hpn, h2p⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ n ∧ 2 * p ≤ n := by
          have hn1 : n ≠ 1 := by omega
          have hq := Nat.minFac_prime hn1
          have hqn := Nat.minFac_dvd n
          by_cases hq2 : n.minFac = 2
          · obtain ⟨m, hm⟩ := hqn
            rw [hq2] at hm
            have hm1 : m ≠ 1 := by omega
            have hmodd : ¬ 2 ∣ m := by
              rintro ⟨t, ht⟩
              apply h4
              refine ⟨t, ?_⟩
              rw [hm, ht]
              ring
            refine ⟨m.minFac, Nat.minFac_prime hm1, ?_, ?_, ?_⟩
            · intro h
              apply hmodd
              rw [← h]
              exact Nat.minFac_dvd m
            · rw [hm]
              exact Dvd.dvd.mul_left (Nat.minFac_dvd m) 2
            · have := Nat.minFac_le (show 0 < m by omega)
              omega
          · refine ⟨n.minFac, hq, hq2, hqn, ?_⟩
            obtain ⟨m, hm⟩ := hqn
            have hm1 : m ≠ 1 := by
              intro h
              rw [h, mul_one] at hm
              rw [← hm] at hq
              exact hnp hq
            have hm0 : m ≠ 0 := by
              intro h
              rw [h, mul_zero] at hm
              omega
            have hm2 : 2 ≤ m := by omega
            calc 2 * n.minFac ≤ m * n.minFac := Nat.mul_le_mul_right _ hm2
              _ = n := by
                rw [mul_comm]
                exact hm.symm
        by_cases hp3 : p = 3
        · subst hp3
          refine ⟨2, by norm_num, by omega, ⟨3, hf3⟩, ?_⟩
          intro x hx
          have h3 : (3 : ℤ) ∣ (n : ℤ) := by exact_mod_cast hpn
          have hx3 := hx.of_dvd h3
          rw [Int.ModEq, pow_two, Int.mul_emod] at hx3
          have h0 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
          rcases h0 with h | h | h
          · rw [h] at hx3
            norm_num at hx3
          · rw [h] at hx3
            norm_num at hx3
          · rw [h] at hx3
            norm_num at hx3
        · have hp4 : 3 < p := by
            have := hp.two_le
            omega
          obtain ⟨k, hk1, hk2, hkf, hkx⟩ := C p hp hp4
          refine ⟨k, by omega, by omega, hkf, ?_⟩
          intro x hx
          exact hkx x (hx.of_dvd (by exact_mod_cast hpn))
