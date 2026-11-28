import OMAStatements.S_oeis_a061265

-- Problem: A061265: Number of squares between n-th prime and (n+1)st prime.
-- Upstream: formal-conjectures statements/oeis-a061265.lean:0 (declaration OMA.S_oeis_a061265.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: if two squares u^2 < v^2 lie between prime(n) and prime(n+1), then a prime between
-- u^2 and (u+1)^2 <= v^2 would lie strictly between two consecutive primes. Conversely, if no prime
-- lies between m^2 and (m+1)^2 (so m >= 2), let i be the number of primes below m^2; then
-- prime(i) < m^2 < (m+1)^2 < prime(i+1), since squares are not prime, so a(i) >= 2.

open OMA.S_oeis_a061265 in
theorem OMA.solution : type_of% @OMA.S_oeis_a061265.main := by
  have hinf := Nat.infinite_setOfPred_prime
  have hgap : ∀ i q : ℕ, q.Prime → Nat.nth Nat.Prime i < q →
      Nat.nth Nat.Prime (i + 1) ≤ q := by
    intro i q hq hlt
    by_contra hcon
    have h := Nat.le_nth_of_lt_nth_succ (not_le.mp hcon) hq
    omega
  constructor
  · intro hL n hn
    by_contra hcon0
    have hcon := not_le.mp hcon0
    unfold a at hcon
    obtain ⟨k1, hk1, k2, hk2, hne⟩ := Finset.one_lt_card.mp hcon
    rw [Finset.mem_filter] at hk1 hk2
    have key : ∀ u v : ℕ, u < v → prime n < u ^ 2 → v ^ 2 < prime (n + 1) → False := by
      intro u v huv hu hv
      have hu1 : 1 ≤ u := by
        rcases Nat.eq_zero_or_pos u with h0 | h0
        · rw [h0] at hu
          simp at hu
        · exact h0
      obtain ⟨p, hp, hp1, hp2⟩ := hL u hu1
      have hle : (u + 1) ^ 2 ≤ v ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h1 : prime n < p := by omega
      have h2 : p < prime (n + 1) := by omega
      unfold prime at h1 h2
      rw [show n + 1 - 1 = n - 1 + 1 by omega] at h2
      have h3 := hgap (n - 1) p hp h1
      omega
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key k1 k2 h hk1.2.1 hk2.2.2
    · exact key k2 k1 h hk2.2.1 hk1.2.2
  · intro hA m hm
    by_contra hcon0
    have hcon : ∀ p : ℕ, p.Prime → m ^ 2 < p → (m + 1) ^ 2 ≤ p := by
      intro p hp h1
      by_contra h2
      exact hcon0 ⟨p, hp, h1, not_le.mp h2⟩
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · obtain rfl : m = 1 := by omega
      have h := hcon 2 Nat.prime_two (by norm_num)
      norm_num at h
    · have hm4 : 4 ≤ m ^ 2 := by nlinarith
      have hmlt : m + 1 < m ^ 2 := by nlinarith
      have hsq : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
      obtain ⟨i, hi⟩ : ∃ i, i = Nat.count Nat.Prime (m ^ 2) := ⟨_, rfl⟩
      have hi0 : 0 < i := by
        rw [hi, Nat.lt_nth_iff_count_lt hinf, Nat.nth_prime_zero_eq_two]
        omega
      have hlow : Nat.nth Nat.Prime (i - 1) < m ^ 2 := by
        apply Nat.nth_lt_of_lt_count
        omega
      have hq : m ^ 2 ≤ Nat.nth Nat.Prime i := by
        rw [hi]
        exact Nat.le_nth_count hinf (m ^ 2)
      have hqp : (Nat.nth Nat.Prime i).Prime := Nat.prime_nth_prime i
      have hne1 : Nat.nth Nat.Prime i ≠ m ^ 2 := by
        intro h
        have h' := hqp.pow_eq_iff.mp h.symm
        exact absurd h'.2 (by norm_num)
      have hne2 : Nat.nth Nat.Prime i ≠ (m + 1) ^ 2 := by
        intro h
        have h' := hqp.pow_eq_iff.mp h.symm
        exact absurd h'.2 (by norm_num)
      have hup : (m + 1) ^ 2 < Nat.nth Nat.Prime i := by
        have h := hcon (Nat.nth Nat.Prime i) hqp (by omega)
        omega
      have hcard : 1 < a i := by
        unfold a
        apply Finset.one_lt_card.mpr
        refine ⟨m, ?_, m + 1, ?_, by omega⟩
        · rw [Finset.mem_filter, Finset.mem_range]
          unfold prime
          rw [show i + 1 - 1 = i by omega]
          exact ⟨by omega, hlow, by omega⟩
        · rw [Finset.mem_filter, Finset.mem_range]
          unfold prime
          rw [show i + 1 - 1 = i by omega]
          exact ⟨by omega, by omega, hup⟩
      have h := hA i (by omega)
      omega
