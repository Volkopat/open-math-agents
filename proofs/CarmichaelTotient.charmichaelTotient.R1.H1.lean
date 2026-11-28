import OMAReductions.R_CarmichaelTotient_charmichaelTotient_R1

-- Step CarmichaelTotient.charmichaelTotient.R1.H1: hypothesis H1 of reduction
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
theorem OMA.solution : OMA.R_CarmichaelTotient_charmichaelTotient_R1.H1 := by
  intro n hn h36
  by_cases h2 : 2 ∣ n
  · by_cases h4 : 4 ∣ n
    · by_cases h3 : 3 ∣ n
      · obtain ⟨j, rfl⟩ := h3
        have hj3 : ¬ 3 ∣ j := by
          rintro ⟨i, rfl⟩
          apply h36
          have h9 : 9 ∣ 3 * (3 * i) := ⟨i, by ring⟩
          exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 9) h4 h9
        have hj2 : 2 ∣ j := by omega
        refine ⟨2 * j, by omega, ?_⟩
        rw [tot_dvd Nat.prime_two hj2, tot_ndvd Nat.prime_three hj3]
      · obtain ⟨k, rfl⟩ := h2
        have hk2 : 2 ∣ k := by omega
        have hk3 : ¬ 3 ∣ k := fun h => h3 (dvd_mul_of_dvd_right h 2)
        refine ⟨3 * k, by omega, ?_⟩
        rw [tot_dvd Nat.prime_two hk2, tot_ndvd Nat.prime_three hk3]
    · obtain ⟨k, rfl⟩ := h2
      have hk2 : ¬ 2 ∣ k := fun h => h4 (by obtain ⟨i, rfl⟩ := h; exact ⟨i, by ring⟩)
      refine ⟨k, by omega, ?_⟩
      rw [tot_ndvd Nat.prime_two hk2]
      simp
  · refine ⟨2 * n, by omega, ?_⟩
    rw [tot_ndvd Nat.prime_two h2]
    simp
