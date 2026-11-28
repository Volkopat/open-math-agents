import OMAReductions.R_Erdos820_erdos_820_variants_log_log_exponent_R1_H1_R1

/-! Let q be the least prime factor of E and k the product of the primes up to t other than q.
Then k divides the primorial of t, so k ≤ 4^t; E does not divide k because q does not; and the
products of the subsets of these primes are distinct divisors of k, so k has at least
2^(π(t) - 1) divisors. -/

open Finset in
theorem OMA.solution : OMA.R_Erdos820_erdos_820_variants_log_log_exponent_R1_H1_R1.H2 := by
  intro t E hE
  have hqp : (Nat.minFac E).Prime := Nat.minFac_prime (by omega)
  have hqE : Nat.minFac E ∣ E := Nat.minFac_dvd E
  obtain ⟨q, hq⟩ : ∃ q, q = Nat.minFac E := ⟨_, rfl⟩
  rw [← hq] at hqp hqE
  obtain ⟨P, hP⟩ : ∃ P : Finset ℕ, P = (range (t + 1)).filter Nat.Prime := ⟨_, rfl⟩
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => by rw [hP] at hp; exact (mem_filter.1 hp).2
  have hprime : ∀ p ∈ P.erase q, p.Prime := fun p hp => hPprime p (mem_of_mem_erase hp)
  have hpos : 0 < ∏ p ∈ P.erase q, p := prod_pos fun p hp => (hprime p hp).pos
  refine ⟨∏ p ∈ P.erase q, p, hpos, ?_, ?_, ?_⟩
  · calc ∏ p ∈ P.erase q, p ≤ ∏ p ∈ P, p :=
          Nat.le_of_dvd (prod_pos fun p hp => (hPprime p hp).pos)
            (prod_dvd_prod_of_subset _ _ _ (erase_subset q P))
      _ = primorial t := by rw [hP]; rfl
      _ ≤ 4 ^ t := primorial_le_four_pow t
  · intro hEk
    obtain ⟨p, hp, hqp'⟩ := (Prime.dvd_finset_prod_iff hqp.prime _).1 (hqE.trans hEk)
    exact ne_of_mem_erase hp ((Nat.prime_dvd_prime_iff_eq hqp (hprime p hp)).1 hqp').symm
  · have hmaps : Set.MapsTo (fun S : Finset ℕ => ∏ p ∈ S, p) ((P.erase q).powerset : Set (Finset ℕ))
        ((∏ p ∈ P.erase q, p).divisors : Set ℕ) := by
      intro S hS
      simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hS
      simp only [coe_sort_coe, mem_coe, Nat.mem_divisors]
      exact ⟨prod_dvd_prod_of_subset _ _ _ hS, hpos.ne'⟩
    have hinj : ((P.erase q).powerset : Set (Finset ℕ)).InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) := by
      intro S hS S' hS' h
      simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hS hS'
      have e1 := Nat.primeFactors_prod (fun p hp => hprime p (hS hp))
      have e2 := Nat.primeFactors_prod (fun p hp => hprime p (hS' hp))
      have h' : ∏ p ∈ S, p = ∏ p ∈ S', p := h
      rw [← e1, ← e2, h']
    have hcard := card_le_card_of_injOn _ hmaps hinj
    rw [card_powerset] at hcard
    have hpi : Nat.primeCounting t = P.card := by
      rw [Nat.primeCounting_eq_primeCounting'_succ, ← Nat.primesBelow_card_eq_primeCounting', hP]
      rfl
    have he : P.card - 1 ≤ (P.erase q).card := pred_card_le_card_erase
    calc 2 ^ (Nat.primeCounting t - 1) ≤ 2 ^ (P.erase q).card :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ _ := hcard
