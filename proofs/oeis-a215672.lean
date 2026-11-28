import OMAStatements.S_oeis_a215672
open OMA.S_oeis_a215672
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a215672.main) := by
  intro h
  have hF : (617093 : ℕ).primeFactors = {43, 113, 127} := by
    rw [show (617093 : ℕ) = 43 * 113 * 127 by decide,
      Nat.primeFactors_mul (by decide) (by decide), Nat.primeFactors_mul (by decide) (by decide),
      (by norm_num : Nat.Prime 43).primeFactors, (by norm_num : Nat.Prime 113).primeFactors,
      (by norm_num : Nat.Prime 127).primeFactors]
    decide
  obtain ⟨q, hq, r, hr⟩ := h 617093 ⟨by decide, fun hp => by
    rcases (Nat.dvd_prime hp).mp (show 43 ∣ 617093 by decide) with h | h <;> norm_num at h,
    (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]; reduce_mod_char)⟩
    (by rw [hF]; decide)
  simp only [hF, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl <;> omega
