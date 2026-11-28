import OMAStatements.S_oeis_a262826
import Mathlib

/-!
# A262826: the 2-adic valuation of Hanna's divisor sum

Write n = 2^v m with m odd. The term d = n of the divisor sum is −(−1)^n 2^n n = ∓2^(n+v) m.
Every proper divisor d of n has n²/d = n·(n/d) ≥ 2n ≥ n + v + 1 (since v < 2^v ≤ n), so the
remaining terms are divisible by 2^(n+v+1). Hence a(n) = 2^v 2^n (∓m + 2K) with ∓m + 2K odd.
-/

namespace A262826Proof

theorem big_exp (n d : ℕ) (hd : d ∈ n.properDivisors) : 2 * n ≤ n ^ 2 / d := by
  obtain ⟨hdn, hlt⟩ := Nat.mem_properDivisors.mp hd
  obtain ⟨k, rfl⟩ := hdn
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hlt)
  have hk : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> simp at hlt
    · exact h
  rw [show (d * k) ^ 2 = d * (k * (d * k)) by ring, Nat.mul_div_cancel_left _ hd0]
  calc 2 * (d * k) = 2 * (d * k) := rfl
    _ ≤ k * (d * k) := Nat.mul_le_mul_right _ hk

end A262826Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a262826.main := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  set v := padicValNat 2 n with hv
  have hvf : n.factorization 2 = v := by rw [hv, Nat.factorization_def n Nat.prime_two]
  set m := n / 2 ^ v with hm
  have hnm : n = 2 ^ v * m := by
    rw [hm, ← hvf]; exact (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
  have hmodd : ¬ 2 ∣ m := by
    rw [hm, ← hvf]; exact Nat.not_dvd_ordCompl Nat.prime_two hn0
  have hvn : v + 1 ≤ n := by
    have h1 : 2 ^ v ≤ n := Nat.le_of_dvd (by omega) ⟨m, hnm⟩
    have h2 : v < 2 ^ v := Nat.lt_two_pow_self
    omega
  have hrest : (2 : ℤ) ^ (n + v + 1) ∣
      ∑ d ∈ n.properDivisors, -(-1 : ℤ) ^ d * 2 ^ (n ^ 2 / d) * d := by
    refine Finset.dvd_sum fun d hd => ?_
    have h := A262826Proof.big_exp n d hd
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _) _
  obtain ⟨K, hK⟩ := hrest
  refine ⟨-(-1 : ℤ) ^ n * m + 2 * K, ?_, ?_⟩
  · have hm' : Odd (m : ℤ) := by
      rw [Int.odd_coe_nat]; exact Nat.odd_iff.mpr (by omega)
    have hs : Odd (-(-1 : ℤ) ^ n) := (Odd.pow (by decide)).neg
    exact (hs.mul hm').add_even (even_two_mul K)
  · unfold OMA.S_oeis_a262826.a
    rw [← Nat.insert_self_properDivisors hn0, Finset.sum_insert Nat.self_notMem_properDivisors, hK,
      show n ^ 2 / n = n by rw [sq, Nat.mul_div_cancel _ (by omega)]]
    conv_lhs => rw [show ((n : ℕ) : ℤ) = 2 ^ v * (m : ℤ) by exact_mod_cast hnm]
    ring
