import OMAStatements.S_oeis_a068318

-- Problem: A068318: Sum of prime factors of n-th semiprime.
-- Upstream: formal-conjectures statements/oeis-a068318.lean:0 (declaration OMA.S_oeis_a068318.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the semiprimes are exactly the products p*q of two primes, with prime factor sum
-- p + q, and Nat.nth runs through all of them (there are infinitely many, e.g. 2p), so k is a
-- term iff k = p + q for primes p, q. If k is odd, one of p, q is 2, so k - 2 is prime, and
-- conversely k = 2 + (k - 2). Goldbach gives k = p + q for every even k >= 4.

open OMA.S_oeis_a068318 in
theorem OMA.solution : type_of% @OMA.S_oeis_a068318.main := by
  have pq : ∀ p q : ℕ, p.Prime → q.Prime →
      (p * q).primeFactorsList.length = 2 ∧ (p * q).primeFactorsList.sum = p + q := by
    intro p q hp hq
    have h := Nat.perm_primeFactorsList_mul hp.ne_zero hq.ne_zero
    rw [Nat.primeFactorsList_prime hp, Nat.primeFactorsList_prime hq] at h
    exact ⟨h.length_eq.trans (by simp), h.sum_eq.trans (by simp)⟩
  have dec : ∀ s : ℕ, s.primeFactorsList.length = 2 →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ s.primeFactorsList.sum = p + q := by
    intro s hs
    obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hs
    have hp : p ∈ s.primeFactorsList := by simp [hpq]
    have hq : q ∈ s.primeFactorsList := by simp [hpq]
    exact ⟨p, q, Nat.prime_of_mem_primeFactorsList hp, Nat.prime_of_mem_primeFactorsList hq,
      by simp [hpq]⟩
  have hinf : (Set.ofPred (fun s : ℕ => s.primeFactorsList.length = 2)).Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨M, hM⟩
    obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + 1)
    have h2 : (2 * p).primeFactorsList.length = 2 := (pq 2 p Nat.prime_two hp).1
    have hle : 2 * p ≤ M := mem_upperBounds.mp hM (2 * p) h2
    omega
  have term : ∀ k : ℕ, (∃ n : ℕ, 1 ≤ n ∧ a n = k) ↔
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = k := by
    intro k
    constructor
    · rintro ⟨n, _, hn⟩
      have hs := Nat.nth_mem_of_infinite hinf (n - 1)
      obtain ⟨p, q, hp, hq, hsum⟩ := dec _ hs
      exact ⟨p, q, hp, hq, hsum.symm.trans hn⟩
    · rintro ⟨p, q, hp, hq, rfl⟩
      have h1 := pq p q hp hq
      refine ⟨Nat.count (fun s : ℕ => s.primeFactorsList.length = 2) (p * q) + 1, by omega, ?_⟩
      unfold a
      rw [Nat.add_sub_cancel,
        Nat.nth_count (p := fun s : ℕ => s.primeFactorsList.length = 2) h1.1]
      exact h1.2
  refine ⟨?_, ?_⟩
  · intro k hk
    rw [term k]
    constructor
    · rintro ⟨p, q, hp, hq, rfl⟩
      rcases hp.eq_two_or_odd with h2 | h2
      · rw [h2, show 2 + q - 2 = q by omega]
        exact hq
      · rcases hq.eq_two_or_odd with h3 | h3
        · rw [h3, show p + 2 - 2 = p by omega]
          exact hp
        · exfalso
          obtain ⟨r, hr⟩ := hk
          omega
    · intro hk2
      refine ⟨2, k - 2, Nat.prime_two, hk2, ?_⟩
      have h4 := hk2.two_le
      omega
  · intro hG k hk4 hke
    rw [term k]
    exact hG k (by omega) hke
