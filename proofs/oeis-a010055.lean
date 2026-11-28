import OMAStatements.S_oeis_a010055
import Mathlib

/-!
# A010055: Yanev's identity for the prime-power indicator

If n = p^k is a prime power, its proper divisors are p^0, ..., p^(k−1), so their lcm is p^(k−1),
and n − p^(k−1) = p^(k−1)(p − 1) = φ(n), giving 1. Otherwise n = p^a·m with p = minFac n, m > 1 and
gcd(p^a, m) = 1; both p^a and m are proper divisors, so the lcm of the proper divisors is n
itself and the quotient is 0.
-/

namespace A010055Proof

theorem lcm_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (p ^ k).properDivisors.lcm id = p ^ (k - 1) := by
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro d hd
    obtain ⟨hdk, hlt⟩ := Nat.mem_properDivisors.mp hd
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdk
    have : i < k := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    exact pow_dvd_pow p (by omega)
  · apply Finset.dvd_lcm (s := (p ^ k).properDivisors) (f := id)
    rw [Nat.mem_properDivisors]
    exact ⟨pow_dvd_pow p (by omega), Nat.pow_lt_pow_right hp.one_lt (by omega)⟩

theorem lcm_not_prime_pow (n : ℕ) (hn : 1 < n) (hnp : ¬ IsPrimePow n) :
    n.properDivisors.lcm id = n := by
  have hn0 : n ≠ 0 := by omega
  apply Nat.dvd_antisymm
  · exact Finset.lcm_dvd fun d hd => (Nat.mem_properDivisors.mp hd).1
  · have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
    set p := n.minFac
    have hapos : 0 < n.factorization p := hp.factorization_pos_of_dvd hn0 (Nat.minFac_dvd n)
    have hAM : p ^ n.factorization p * (n / p ^ n.factorization p) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n p
    have hcop : Nat.Coprime (p ^ n.factorization p) (n / p ^ n.factorization p) :=
      (Nat.coprime_ordCompl hp hn0).pow_left _
    have hA2 : 2 ≤ p ^ n.factorization p := by
      have := Nat.one_lt_pow hapos.ne' hp.one_lt
      omega
    have hM1 : n / p ^ n.factorization p ≠ 1 := by
      intro h
      rw [h, mul_one] at hAM
      exact hnp ((isPrimePow_nat_iff n).mpr ⟨p, n.factorization p, hp, hapos, hAM⟩)
    have hM0 : n / p ^ n.factorization p ≠ 0 := by
      intro h
      rw [h, mul_zero] at hAM
      omega
    generalize p ^ n.factorization p = A at hAM hcop hA2 hM1 hM0
    generalize n / A = M at hAM hcop hM1 hM0
    have hAlt : A < n := by
      have := Nat.mul_lt_mul_of_pos_left (show 1 < M by omega) (show 0 < A by omega)
      omega
    have hMlt : M < n := by
      have := Nat.mul_lt_mul_of_pos_right (show 1 < A by omega) (show 0 < M by omega)
      omega
    have hAd : A ∣ n.properDivisors.lcm id :=
      Finset.dvd_lcm (s := n.properDivisors) (f := id)
        (Nat.mem_properDivisors.mpr ⟨Dvd.intro M hAM, hAlt⟩)
    have hMd : M ∣ n.properDivisors.lcm id :=
      Finset.dvd_lcm (s := n.properDivisors) (f := id)
        (Nat.mem_properDivisors.mpr ⟨Dvd.intro_left A hAM, hMlt⟩)
    have h := hcop.mul_dvd_of_dvd_of_dvd hAd hMd
    rwa [hAM] at h

end A010055Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a010055.main := by
  intro n hn
  unfold OMA.S_oeis_a010055.a OMA.S_oeis_a010055.lcmProper
  by_cases hpp : IsPrimePow n
  · rw [if_pos (Or.inr hpp)]
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    rw [A010055Proof.lcm_prime_pow p k hp hk, Nat.totient_prime_pow hp hk]
    have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
    have hpk : (p : ℚ) ^ (k - 1) ≠ 0 := pow_ne_zero _ (by linarith)
    have e : (p : ℚ) ^ k = (p : ℚ) ^ (k - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    push_cast [Nat.cast_sub hp.one_le, e]
    rw [eq_div_iff (mul_ne_zero hpk (by linarith))]
    ring
  · rw [if_neg (by rintro (h | h) <;> [omega; exact hpp h]),
      A010055Proof.lcm_not_prime_pow n hn hpp]
    simp
