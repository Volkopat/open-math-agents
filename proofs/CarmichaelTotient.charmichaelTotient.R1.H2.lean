import OMAReductions.R_CarmichaelTotient_charmichaelTotient_R1

-- Step CarmichaelTotient.charmichaelTotient.R1.H2: hypothesis H2 of reduction
-- CarmichaelTotient.charmichaelTotient.R1
-- Credit: @JamesSlash. Carmichael's exchange of prime factors with equal totient (Bull. AMS 1922),
-- as listed in the reduction: phi (p * k) = p * phi k when p | k and (q - 1) * phi k when q does not divide k.

namespace OMACarmichael

open Nat

theorem tot_dvd {p k : ℕ} (hp : p.Prime) (h : p ∣ k) : φ (p * k) = p * φ k :=
  Nat.totient_mul_of_prime_of_dvd hp h

theorem tot_ndvd {q k : ℕ} (hq : q.Prime) (h : ¬ q ∣ k) : φ (q * k) = (q - 1) * φ k := by
  rw [Nat.totient_mul ((Nat.Prime.coprime_iff_not_dvd hq).mpr h), Nat.totient_prime hq]

end OMACarmichael

open Nat OMACarmichael in
theorem OMA.solution : OMA.R_CarmichaelTotient_charmichaelTotient_R1.H2 := by
  intro n h36 h49
  by_cases h7 : 7 ∣ n
  · obtain ⟨j, rfl⟩ := h7
    have hj7 : ¬ 7 ∣ j := by
      rintro ⟨i, rfl⟩
      exact h49 ⟨i, by ring⟩
    have hj : 36 ∣ j := (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 36 7) h36)
    have hj2 : 2 ∣ 3 * j := dvd_mul_of_dvd_right ((by norm_num : 2 ∣ 36).trans hj) 3
    have hj3 : 3 ∣ j := (by norm_num : 3 ∣ 36).trans hj
    refine ⟨2 * (3 * j), by omega, ?_⟩
    rw [tot_dvd Nat.prime_two hj2, tot_dvd Nat.prime_three hj3, tot_ndvd (by norm_num) hj7]
    ring
  · obtain ⟨k, hk⟩ : 6 ∣ n := (by norm_num : 6 ∣ 36).trans h36
    subst hk
    have hk6 : 6 ∣ k := by omega
    have hk2 : 2 ∣ 3 * k := dvd_mul_of_dvd_right ((by norm_num : 2 ∣ 6).trans hk6) 3
    have hk3 : 3 ∣ k := (by norm_num : 3 ∣ 6).trans hk6
    have hk7 : ¬ 7 ∣ k := fun h => h7 (dvd_mul_of_dvd_right h 6)
    refine ⟨7 * k, by omega, ?_⟩
    rw [show 6 * k = 2 * (3 * k) by ring, tot_dvd Nat.prime_two hk2, tot_dvd Nat.prime_three hk3,
      tot_ndvd (by norm_num) hk7]
    ring
