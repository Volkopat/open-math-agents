import OMAStatements.S_oeis_a262009
import Mathlib

/-!
# A262009: the 2-adic valuation of Hanna's divisor sum

Write n = 2^v m with m odd. The term d = 1 is 2·n² = 2^(2v+1) m². For a divisor d ≥ 2 with
v₂(d) = w, the cofactor (n/d)² is divisible by 2^(2(v−w)), and d² ≥ 2d ≥ 2·2^w ≥ 2w + 2, so
2^(d²)·(n/d)² is divisible by 2^(2v+2). Hence a(n) = 2^(2v+1)(m² + 2K) with m² + 2K odd, which gives
both conjectures: v₂(a(n)) = 2v + 1 and A037227(a(n)) = 2(2v + 1) + 1.
-/

namespace A262009Proof

theorem term_dvd (n d : ℕ) (hn : n ≠ 0) (hd : d ∈ n.divisors.erase 1) :
    2 ^ (2 * padicValNat 2 n + 2) ∣ 2 ^ (d ^ 2) * (n ^ 2 / d ^ 2) := by
  obtain ⟨hd1, hdn'⟩ := Finset.mem_erase.mp hd
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hdn'
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hdn)
  have hd2 : 2 ≤ d := by omega
  set v := padicValNat 2 n
  set w := padicValNat 2 d
  have hwd : 2 ^ w ∣ d := pow_padicValNat_dvd
  have hwv : w ≤ v := (padicValNat_dvd_iff_le hn).mp (hwd.trans hdn)
  have hq : padicValNat 2 (n / d) = v - w := padicValNat.div_of_dvd hdn
  have hqd : 2 ^ (v - w) ∣ n / d := by rw [← hq]; exact pow_padicValNat_dvd
  have h1 : 2 ^ (2 * (v - w)) ∣ n ^ 2 / d ^ 2 := by
    rw [← Nat.div_pow hdn, mul_comm, pow_mul]
    exact pow_dvd_pow_of_dvd hqd 2
  have hw1 : w + 1 ≤ 2 ^ w := Nat.lt_two_pow_self
  have hwle : 2 ^ w ≤ d := Nat.le_of_dvd (by omega) hwd
  have hdd : 2 * d ≤ d ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right d hd2
  have h2 : 2 ^ (2 * w + 2) ∣ 2 ^ (d ^ 2) := pow_dvd_pow 2 (by omega)
  have e : 2 * v + 2 = 2 * w + 2 + 2 * (v - w) := by omega
  rw [e, pow_add]
  exact mul_dvd_mul h2 h1

end A262009Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a262009.main := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  set v := padicValNat 2 n with hv
  have hvf : n.factorization 2 = v := by rw [hv, Nat.factorization_def n Nat.prime_two]
  set m := n / 2 ^ v with hm
  have hnm : n = 2 ^ v * m := by
    rw [hm, ← hvf]; exact (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
  have hmodd : ¬ 2 ∣ m := by
    rw [hm, ← hvf]; exact Nat.not_dvd_ordCompl Nat.prime_two hn0
  have hrest : 2 ^ (2 * v + 2) ∣ ∑ d ∈ n.divisors.erase 1, 2 ^ (d ^ 2) * (n ^ 2 / d ^ 2) :=
    Finset.dvd_sum fun d hd => A262009Proof.term_dvd n d hn0 hd
  obtain ⟨K, hK⟩ := hrest
  have ha : OMA.S_oeis_a262009.a n = 2 ^ (2 * v + 1) * (m ^ 2 + 2 * K) := by
    unfold OMA.S_oeis_a262009.a
    rw [← Finset.add_sum_erase _ _ (Nat.one_mem_divisors.mpr hn0), hK]
    simp only [one_pow, pow_one, Nat.div_one]
    rw [hnm]
    ring
  have hodd : Odd (m ^ 2 + 2 * K) := by
    have : Odd m := Nat.odd_iff.mpr (by omega)
    exact (this.pow).add_even (even_two_mul K)
  have hval : padicValNat 2 (OMA.S_oeis_a262009.a n) = 2 * v + 1 := by
    rw [ha, padicValNat.mul (by positivity) hodd.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (fun h => by
        rcases hodd with ⟨k, hk⟩; omega)]
  refine ⟨?_, m ^ 2 + 2 * K, hodd, ?_⟩
  · unfold OMA.S_oeis_a262009.A037227
    rw [hval, ← hv]
  · unfold OMA.S_oeis_a262009.A037227
    rw [ha, ← hv]
