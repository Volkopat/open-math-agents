import OMAStatements.S_oeis_a092067
import Mathlib

/-!
Credit: @ivillar
Proof: the set is nonempty (m = 2 for odd n; m = n + 1 for even n, since n + 1 is odd and
n + 1 divides n^(n+1) + 1). Let m be its least element and suppose m is not prime; let p be
the least prime factor of m, so p < m and gcd(m, p - 1) = 1. If p = 2 then n is odd and 2
divides n^2 + 1, contradicting minimality. Otherwise, in ZMod p, x = n satisfies x^m = -1,
so x ≠ 0, x^(2m) = 1 and x^(p-1) = 1, hence x^gcd(2m, p-1) = 1 with gcd(2m, p-1) = gcd(2, p-1),
so x^2 = 1 and x = 1 or x = -1. The case x = 1 forces 1 = -1, i.e. p = 2; in the case x = -1,
x^p + 1 = 0, so p divides n^p + 1 with 1 < p < m, contradicting minimality.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a092067.main := by
  intro n hn
  show Nat.Prime (sInf {m : ℕ | 1 < m ∧ m ∣ n ^ m + 1})
  have hne : ({m : ℕ | 1 < m ∧ m ∣ n ^ m + 1} : Set ℕ).Nonempty := by
    rcases Nat.even_or_odd n with he | ho
    · refine ⟨n + 1, by omega, ?_⟩
      have h := Odd.nat_add_dvd_pow_add_pow n 1 (show Odd (n + 1) from he.add_one)
      simpa using h
    · exact ⟨2, by norm_num, (ho.pow.add_one).two_dvd⟩
  have hm := Nat.sInf_mem hne
  have hmin : ∀ k < sInf {m : ℕ | 1 < m ∧ m ∣ n ^ m + 1}, ¬ (1 < k ∧ k ∣ n ^ k + 1) :=
    fun k hk => Nat.notMem_of_lt_sInf hk
  generalize sInf {m : ℕ | 1 < m ∧ m ∣ n ^ m + 1} = m at hm hmin ⊢
  obtain ⟨hm1, hmd⟩ := hm
  by_contra hnp
  set p := m.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpm : p < m := (Nat.not_prime_iff_minFac_lt (by omega)).mp hnp
  have hpdvd : p ∣ m := Nat.minFac_dvd m
  have hpn : p ∣ n ^ m + 1 := dvd_trans hpdvd hmd
  by_cases h2 : p = 2
  · -- n must be odd, and then 2 works
    have hodd : Odd n := by
      rcases Nat.even_or_odd n with he | ho
      · exfalso
        have h2n : 2 ∣ n ^ m := dvd_pow (even_iff_two_dvd.mp he) (by omega)
        rw [h2] at hpn
        omega
      · exact ho
    exact hmin 2 (by omega) ⟨by norm_num, (hodd.pow.add_one).two_dvd⟩
  · have hfact : Fact p.Prime := ⟨hp⟩
    have hx : ((n : ZMod p)) ^ m + 1 = 0 := by
      have := (ZMod.natCast_eq_zero_iff (n ^ m + 1) p).mpr hpn
      push_cast at this
      exact this
    have hx0 : (n : ZMod p) ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by omega), zero_add] at hx
      exact one_ne_zero hx
    have hcop : Nat.Coprime m (p - 1) := by
      apply Nat.coprime_of_dvd
      intro q hq hqm hqp
      have hq2 := hq.two_le
      have hqle : q ≤ p - 1 := Nat.le_of_dvd (by have := hp.two_le; omega) hqp
      have := Nat.minFac_le_of_dvd hq2 hqm
      omega
    have hA : ((n : ZMod p)) ^ (m * 2) = 1 := by
      rw [pow_mul, show ((n : ZMod p)) ^ m = -1 by linear_combination hx]
      norm_num
    have hB : ((n : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx0
    have hG : ((n : ZMod p)) ^ (Nat.gcd (m * 2) (p - 1)) = 1 := pow_gcd_eq_one.mpr ⟨hA, hB⟩
    rw [Nat.Coprime.gcd_mul_left_cancel 2 hcop] at hG
    have hsq : ((n : ZMod p)) * (n : ZMod p) = 1 := by
      obtain ⟨c, hc⟩ := Nat.gcd_dvd_left 2 (p - 1)
      rw [← pow_two, hc, pow_mul, hG, one_pow]
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · rw [h1, one_pow] at hx
      have h22 : ((2 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination hx
      have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).mp h22)
      have := hp.two_le
      omega
    · apply hmin p hpm
      refine ⟨hp.one_lt, ?_⟩
      apply (ZMod.natCast_eq_zero_iff (n ^ p + 1) p).mp
      push_cast
      rw [h1, Odd.neg_one_pow (hp.odd_of_ne_two h2)]
      ring
