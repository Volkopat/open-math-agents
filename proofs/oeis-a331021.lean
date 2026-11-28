import OMAStatements.S_oeis_a331021
import Mathlib

/-! Adapt the factorization and natural-gcd argument from @Sai-yr's proof linked
in #7380. The merged proof is by @Genbox (#7871); @carl2sheriff's #9212 also
uses a gcd of exponents. Use the standard Euler congruence, consecutive-number
coprimality, and divisibility of powers minus one directly. -/

namespace WieferichFactors

private lemma exponent_reduction {k p : ℕ} (hk : 1 < k) (hp : p.Prime)
    (hpk : p ∣ k) (hsq : p^2 ∣ 2^(k-1)-1) : p^2 ∣ 2^(p-1)-1 := by
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    have htwo : 2 ∣ 2^(k-1)-1 := (by decide : 2 ∣ 2^2).trans hsq
    rw [show k-1=(k-2)+1 by omega, pow_succ] at htwo
    have hpos : 0 < 2^(k-2) := by positivity
    omega
  have hcop : Nat.Coprime 2 (p^2) := ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm).pow_right 2
  have heuler := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime_pow_succ hp 1, pow_one] at heuler
  have hE : p^2 ∣ 2^(p*(p-1))-1 := heuler.symm.dvd'
  let d := Nat.gcd (k-1) (p*(p-1))
  have hpow := Nat.dvd_gcd hsq hE
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hpow
  have hc : d.Coprime p :=
    (((Nat.coprime_self_sub_right hk.le).mpr (Nat.coprime_one_right k)).of_dvd_left hpk).symm.of_dvd_left
      (Nat.gcd_dvd_left _ _)
  have hd : d ∣ p-1 := hc.dvd_of_dvd_mul_left (Nat.gcd_dvd_right _ _)
  exact hpow.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hd)

end WieferichFactors

theorem OMA.solution : type_of% @OMA.S_oeis_a331021.main := by
  intro k hk hlarge
  have hk1 : 1 < k := by
    by_contra! h
    have : k=1 := by omega
    simp [this] at hlarge
  let g := Nat.gcd (k^2) (2^(k-1)-1)
  change k < g at hlarge
  obtain ⟨p,hv⟩ := Nat.exists_factorization_lt_of_lt hk.ne' hlarge
  have hvg : 0 < g.factorization p := by omega
  have hp : p.Prime := by
    by_contra hn
    rw [Nat.factorization_eq_zero_of_not_prime g hn] at hvg
    omega
  have hpg := Nat.dvd_of_factorization_pos hvg.ne'
  have hpk := hp.dvd_of_dvd_pow (hpg.trans (Nat.gcd_dvd_left (k^2) (2^(k-1)-1)))
  have hvk := hp.factorization_pos_of_dvd hk.ne' hpk
  have hsq : p^2 ∣ g := (hp.pow_dvd_iff_le_factorization (hk.trans hlarge).ne').mpr (by omega)
  exact ⟨p,hp,hpk,WieferichFactors.exponent_reduction hk1 hp hpk (hsq.trans (Nat.gcd_dvd_right _ _))⟩
