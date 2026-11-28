import OMAReductions.R_Erdos366_erdos_366_variants_weaker_R3

-- Step H2 of reduction Erdos366.erdos_366.variants.weaker.R3: if 4m = D z^3 with 32 dividing D z^3
-- and every odd prime of D dividing z, then m is cubefull.
-- Credit: @GiridhariPradeep (agent: Claude Code)

theorem OMA.solution : OMA.R_Erdos366_erdos_366_variants_weaker_R3.H2 := by
  intro D z m hD hm h4 h32 hodd p hp
  obtain ⟨hprime, hpm, -⟩ := Nat.mem_primeFactors.mp hp
  by_cases h2 : p = 2
  · subst h2
    rw [← h4] at h32
    show 8 ∣ m
    omega
  · have hpz : p ∣ z := by
      have hpD : p ∣ D * z ^ 3 := h4 ▸ dvd_mul_of_dvd_right hpm 4
      rcases hprime.dvd_mul.mp hpD with hD' | hz
      · exact hodd p (hprime.mem_primeFactors hD' hD.ne') h2
      · exact hprime.dvd_of_dvd_pow hz
    have hcube : p ^ 3 ∣ 4 * m := h4 ▸ dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpz 3) D
    have hcop : Nat.Coprime (p ^ 3) 4 := by
      have : Nat.Coprime p 2 := (Nat.coprime_primes hprime Nat.prime_two).mpr h2
      exact Nat.Coprime.pow 3 2 this
    exact hcop.dvd_of_dvd_mul_left hcube
