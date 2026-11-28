import OMAStatements.S_oeis_a350878

-- Problem: A350878: Integers m that divide the sum of values d*p < m, where d is a divisor of m, p is a prime, and d*p does not divide m.
-- Upstream: formal-conjectures statements/oeis-a350878.lean:0 (declaration OMA.S_oeis_a350878.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: m = 1..5 by computation (only m = 5 gives the sum m). For m ≥ 6 the sum exceeds m.
-- Bertrand gives a prime q with m/2 < q < m (q < m when m is not prime); q does not divide m, so
-- the pair (1, q) adds more than m/2. If m is composite with least prime factor s and m = s*k,
-- then k ≥ 3 and a Bertrand prime p with k/2 < p < k gives the pair (s, p) with m/2 < s*p < m.
-- If m is prime, the pairs (1, p) are all primes p < m, and their sum is at least m + 1, since the
-- sum of the primes up to x is at least x + 2 for x ≥ 5 (Bertrand and strong induction).

open OMA.S_oeis_a350878 in
theorem OMA.solution : type_of% @OMA.S_oeis_a350878.main := by
  have nodvd : ∀ a b : ℕ, a < b → b < 2 * a → ¬ a ∣ b := by
    intro a b h1 h2 hab
    obtain ⟨j, hj⟩ := hab
    have hj2 : j < 2 := by
      by_contra hc
      have hc' : 2 ≤ j := by omega
      have hmul : a * 2 ≤ a * j := Nat.mul_le_mul_left a hc'
      omega
    interval_cases j <;> omega
  have inner_ge : ∀ m d p : ℕ, 1 ≤ d → p.Prime → d * p < m → ¬ d * p ∣ m →
      d * p ≤ ∑ q ∈ (Finset.range m).filter (fun q => q.Prime ∧ d * q < m ∧ ¬ d * q ∣ m),
        d * q := by
    intro m d p hd hp hlt hnd
    have hpd : p ≤ d * p := Nat.le_mul_of_pos_left p (by omega)
    have hpm : p < m := lt_of_le_of_lt hpd hlt
    exact Finset.single_le_sum (f := fun q => d * q) (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpm, hp, hlt, hnd⟩)
  have two_terms : ∀ m s : ℕ, m ≠ 0 → s ∣ m → s ≠ 1 →
      (∑ q ∈ (Finset.range m).filter (fun q => q.Prime ∧ 1 * q < m ∧ ¬ 1 * q ∣ m), 1 * q) +
      (∑ q ∈ (Finset.range m).filter (fun q => q.Prime ∧ s * q < m ∧ ¬ s * q ∣ m), s * q)
        ≤ sumDP m := by
    intro m s hm hs hs1
    have hsub : ({1, s} : Finset ℕ) ⊆ m.divisors := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact Nat.mem_divisors.mpr ⟨one_dvd _, hm⟩
      · rw [hx]
        exact Nat.mem_divisors.mpr ⟨hs, hm⟩
    have h1 := Finset.sum_le_sum_of_subset (f := fun d =>
      ∑ q ∈ (Finset.range m).filter (fun q => q.Prime ∧ d * q < m ∧ ¬ d * q ∣ m), d * q) hsub
    rw [Finset.sum_pair (Ne.symm hs1)] at h1
    exact h1
  have Pge : ∀ x : ℕ, 5 ≤ x → x + 2 ≤ ∑ q ∈ (Finset.range (x + 1)).filter Nat.Prime, q := by
    intro x
    induction x using Nat.strong_induction_on with
    | h x ih =>
      intro hx
      by_cases hx10 : x < 10
      · interval_cases x <;> decide
      · obtain ⟨q, hq, hq1, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul (x / 2) (by omega)
        have ih' := ih (x / 2) (by omega) (by omega)
        have hnot : q ∉ (Finset.range (x / 2 + 1)).filter Nat.Prime := by
          intro h
          rw [Finset.mem_filter, Finset.mem_range] at h
          exact absurd h.1 (by omega)
        have hsub : insert q ((Finset.range (x / 2 + 1)).filter Nat.Prime) ⊆
            (Finset.range (x + 1)).filter Nat.Prime := by
          intro y hy
          rw [Finset.mem_insert] at hy
          rw [Finset.mem_filter, Finset.mem_range]
          rcases hy with hy | hy
          · rw [hy]
            exact ⟨by omega, hq⟩
          · rw [Finset.mem_filter, Finset.mem_range] at hy
            exact ⟨by omega, hy.2⟩
        have hsum : q + ∑ y ∈ (Finset.range (x / 2 + 1)).filter Nat.Prime, y ≤
            ∑ y ∈ (Finset.range (x + 1)).filter Nat.Prime, y := by
          have h := Finset.sum_le_sum_of_subset (f := fun y => y) hsub
          rw [Finset.sum_insert hnot] at h
          exact h
        omega
  intro m hm
  by_cases h6 : m ≤ 5
  · interval_cases m <;> decide
  · have hgt : m < sumDP m := by
      obtain ⟨q, hq, hq1, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul (m / 2) (by omega)
      have hmq : m < 2 * q := by omega
      by_cases hpr : m.Prime
      · have hm7 : 7 ≤ m := by
          by_contra hc
          have h6' : m = 6 := by omega
          rw [h6'] at hpr
          exact absurd hpr (by decide)
        have hP := Pge (m - 1) (by omega)
        have hrange : m - 1 + 1 = m := by omega
        rw [hrange] at hP
        have hfe : (Finset.range m).filter Nat.Prime =
            (Finset.range m).filter (fun q => q.Prime ∧ 1 * q < m ∧ ¬ 1 * q ∣ m) := by
          apply Finset.filter_congr
          intro r hr
          rw [Finset.mem_range] at hr
          constructor
          · intro hrp
            refine ⟨hrp, by omega, ?_⟩
            intro hd
            rw [one_mul] at hd
            have hre : r = m := (Nat.prime_dvd_prime_iff_eq hrp hpr).mp hd
            omega
          · intro h
            exact h.1
        have hin : ∑ r ∈ (Finset.range m).filter Nat.Prime, r =
            ∑ r ∈ (Finset.range m).filter (fun q => q.Prime ∧ 1 * q < m ∧ ¬ 1 * q ∣ m),
              1 * r := by
          rw [← hfe]
          apply Finset.sum_congr rfl
          intro r _
          exact (one_mul r).symm
        have hle : ∑ r ∈ (Finset.range m).filter (fun q => q.Prime ∧ 1 * q < m ∧ ¬ 1 * q ∣ m),
            1 * r ≤ sumDP m := by
          have h1mem : 1 ∈ m.divisors := Nat.mem_divisors.mpr ⟨one_dvd m, by omega⟩
          exact Finset.single_le_sum (f := fun d => ∑ p ∈ (Finset.range m).filter
            (fun p => p.Prime ∧ d * p < m ∧ ¬ d * p ∣ m), d * p) (fun _ _ => Nat.zero_le _) h1mem
        omega
      · have hqm : q < m := by
          rcases Nat.lt_or_ge q m with h | h
          · exact h
          · exfalso
            have hqe : q = m := by omega
            rw [hqe] at hq
            exact hpr hq
        obtain ⟨s, hs⟩ : ∃ s, s = m.minFac := ⟨_, rfl⟩
        have hsd : s ∣ m := by
          rw [hs]
          exact Nat.minFac_dvd m
        have hsp : s.Prime := by
          rw [hs]
          exact Nat.minFac_prime (by omega)
        have hs2 : 2 ≤ s := hsp.two_le
        have hsq : s ^ 2 ≤ m := by
          rw [hs]
          exact Nat.minFac_sq_le_self (by omega) hpr
        obtain ⟨k, hk⟩ := hsd
        have hsk : s ≤ k := by nlinarith
        have hk2 : 2 ≤ k := le_trans hs2 hsk
        have hk3 : 3 ≤ k := by
          by_contra hc
          have hc' : k < 3 := by omega
          interval_cases k
          omega
        obtain ⟨p, hp, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (k / 2) (by omega)
        have hpk : p < k := by
          by_contra hc
          have hpe : p = k := by omega
          have h2 : 2 ∣ p := ⟨k / 2, by omega⟩
          rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h
          · omega
          · omega
        have hkp : k < 2 * p := by omega
        have hsp1 : s * p < s * k := by nlinarith
        have hsp2 : s * k < 2 * (s * p) := by nlinarith
        have t1 := inner_ge m 1 q (le_refl 1) hq (by omega)
          (by rw [one_mul]; exact nodvd q m hqm hmq)
        have t2 := inner_ge m s p (by omega) hp (by omega)
          (by rw [hk]; exact nodvd (s * p) (s * k) hsp1 hsp2)
        have tt := two_terms m s (by omega) ⟨k, hk⟩ (by omega)
        omega
    constructor
    · intro h
      omega
    · intro h
      omega
