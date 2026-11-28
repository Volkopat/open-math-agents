import OMAReductions.R_mo_332147_R1

theorem OMA.solution : OMA.R_mo_332147_R1.H1 := by
  rintro n hn ⟨m, hm⟩
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have : p ≠ 2 * n := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 ⟨n, h⟩; omega
  refine ⟨p, hp, h1, by omega, ?_⟩
  rw [show 2 * (n : ℤ) = m ^ 2 by rw [sq]; exact_mod_cast hm]
  refine jacobiSym.sq_one' ?_
  rw [Int.gcd_natCast_natCast]
  exact (Nat.coprime_of_lt_prime (by rintro rfl; omega) (by nlinarith) hp).symm
