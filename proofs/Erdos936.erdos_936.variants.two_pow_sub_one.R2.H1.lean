import OMAReductions.R_Erdos936_erdos_936_variants_two_pow_sub_one_R2
import Mathlib

-- Step Erdos936.erdos_936.variants.two_pow_sub_one.R2.H1: hypothesis H1 of reduction Erdos936.erdos_936.variants.two_pow_sub_one.R2
-- Credit: @Raimo33

namespace OMAE_LTE

lemma not_dvd_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) : ¬ p ∣ 2 ^ n := by
  intro h
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
  exact hp2 this

lemma dvd_fermat {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p ∣ 2 ^ (p - 1) - 1 := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have h := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime hp] at h
  exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp h.symm

lemma subone (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn : n ≠ 0) (h : p ∣ 2 ^ n - 1) :
    padicValNat p (2 ^ n - 1) = padicValNat p (2 ^ (p - 1) - 1) + padicValNat p n := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hA : 1 < 2 ^ n := Nat.one_lt_two_pow hn
  have hB : 1 < 2 ^ (p - 1) := Nat.one_lt_two_pow (by omega)
  have e1 := padicValNat.pow_sub_pow (p := p) (x := 2 ^ n) (y := 1) hodd hA (by simpa using h)
    (not_dvd_two_pow hp hp2 n) (n := p - 1) (by omega)
  have e2 := padicValNat.pow_sub_pow (p := p) (x := 2 ^ (p - 1)) (y := 1) hodd hB
    (by simpa using dvd_fermat hp hp2) (not_dvd_two_pow hp hp2 _) (n := n) hn
  have hv : padicValNat p (p - 1) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  rw [hv, one_pow, ← pow_mul] at e1
  rw [one_pow, ← pow_mul, mul_comm] at e2
  omega

end OMAE_LTE

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_two_pow_sub_one_R2.H1 := by
  intro p n hp hp2 hn h
  exact OMAE_LTE.subone p n hp hp2 hn h
