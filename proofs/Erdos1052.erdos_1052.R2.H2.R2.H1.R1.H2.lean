import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R2_H1_R1

open Finset

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R2_H2_R2_H1_R1.H2 := by
  intro c hc _ a S b u ha _ _ hS heq p r hp hr hpr hmissing
  by_contra! hmin
  have hc0 : c ≠ 0 := by
    intro h
    simp [h] at hc
  have htwo : ¬ 2 ∣ c := by
    rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]
  have hb0 : b ≠ 0 := mul_ne_zero (pow_ne_zero _ (by decide)) hc0
  have hb2 : b.factorization 2 = a := by
    change (2 ^ a * c).factorization 2 = a
    rw [Nat.factorization_mul (pow_ne_zero _ (by decide)) hc0, Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd htwo, add_zero]
  have hm2 : 2 ∈ b.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff, hb2]
    omega
  have hfactor : 2 ^ a + 1 ∣ u := by
    have hd := dvd_prod_of_mem (fun q : ℕ => 1 + q ^ b.factorization q) hm2
    simpa [hb2, add_comm] using hd
  have hdiv : p * r ∣ (2 * b) * ∏ q ∈ S, q := by
    rw [← heq]
    exact dvd_mul_of_dvd_left (hpr.trans hfactor) _
  have hn2 : ¬ 2 ∣ 2 ^ a + 1 := by
    intro h
    have hm := Nat.mod_eq_zero_of_dvd h
    have ha' : a ≠ 0 := by omega
    have ht : 2 ^ a % 2 = 0 := by
      rw [Nat.pow_mod]
      simp [ha']
    omega
  have hin (q : ℕ) (hq : q.Prime) (hqc : c < q) (hd : q ∣ 2 ^ a + 1) :
      q.Coprime (2 * b) := by
    apply hq.coprime_iff_not_dvd.mpr
    have hq2 : ¬ q ∣ 2 := by
      intro h
      have he : q = 2 := (Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hq.ne_one
      exact hn2 (he ▸ hd)
    have hbq : ¬ q ∣ b := by
      intro h
      change q ∣ 2 ^ a * c at h
      rcases hq.dvd_mul.mp h with h | h
      · exact hq2 (hq.dvd_of_dvd_pow h)
      · exact (not_lt_of_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hc0) h)) hqc
    exact fun h => (hq.dvd_mul.mp h).elim hq2 hbq
  have hp' := hin p hp (hmin.trans_le (min_le_left _ _)) ((dvd_mul_right p r).trans hpr)
  have hr' := hin r hr (hmin.trans_le (min_le_right _ _)) ((dvd_mul_left r p).trans hpr)
  have hprod := (Nat.Coprime.mul_left hp' hr').dvd_of_dvd_mul_left hdiv
  have mem_of_prod (q : ℕ) (hq : q.Prime) (T : Finset ℕ) (hTS : T ⊆ S)
      (hd : q ∣ ∏ x ∈ T, x) : q ∈ T := by
    obtain ⟨s, hs, hd'⟩ := (hq.prime.dvd_finsetProd_iff (fun x : ℕ => x)).mp hd
    rcases (Nat.dvd_prime (hS s (hTS hs)).1).mp hd' with h | h
    · exact (hq.ne_one h).elim
    · exact h ▸ hs
  have hmP := mem_of_prod p hp S Subset.rfl ((dvd_mul_right p r).trans hprod)
  have hmR := mem_of_prod r hr S Subset.rfl ((dvd_mul_left r p).trans hprod)
  apply hmissing
  refine ⟨hmP, hmR, ?_⟩
  intro h
  subst r
  have he := Finset.prod_erase_mul S (fun q : ℕ => q) hmP
  rw [← he, mul_comm (∏ q ∈ S.erase p, q) p] at hprod
  have hd := (Nat.mul_dvd_mul_iff_left hp.pos).mp hprod
  exact Finset.notMem_erase p S (mem_of_prod p hp (S.erase p) (erase_subset _ _) hd)