import OMAStatements.S_oeis_a296306
import Mathlib

/-!
# A296306: the three conjectures

Following @ivillar (#27661), retain all three arguments and use the standard
natural subtraction parity and power-product identities for their helpers.

Write n = 2^e·m with m odd. The odd divisors of n are the divisors of m, so the odd power sum is
σ_k(m), and σ_k(n) = σ_k(2^e)·σ_k(m); this gives the divisibility. For k = 2 the quotient is
σ_2(2^e) = Σ_{i≤e} 4^i = (4^(e+1) − 1)/3, the geometric value with j = e + 1, and in particular
a(2^(j−1)) = (4^j − 1)/3. Finally, for 0 < i < 2^h with i = 2^e·m, 2^h − i = 2^e·(2^(h−e) − m) has the
same 2-adic valuation, so a(i) = a(2^h − i).
-/

namespace PA296306
open Finset Nat ArithmeticFunction

theorem core (k e m : ℕ) (hm : Odd m) :
    OMA.S_oeis_a296306.oddSum k (2 ^ e * m) = sigma k m ∧
      sigma k (2 ^ e * m) = sigma k (2 ^ e) * sigma k m := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hcop : Nat.Coprime (2 ^ e) m := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hm)
  refine ⟨?_, isMultiplicative_sigma.map_mul_of_coprime hcop⟩
  unfold OMA.S_oeis_a296306.oddSum
  rw [sigma_apply]
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, -⟩, hdo⟩
    refine ⟨?_, hm0⟩
    have hc : Nat.Coprime d (2 ^ e) := Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hdo)
    exact hc.dvd_of_dvd_mul_left hd
  · rintro ⟨hd, -⟩
    exact ⟨⟨Dvd.dvd.mul_left hd _, by positivity⟩, Odd.of_dvd_nat hm hd⟩

theorem sigma2_pow (e : ℕ) : sigma 2 (2 ^ e) = OMA.S_oeis_a296306.geometric (e + 1) := by
  rw [sigma_apply_prime_pow Nat.prime_two]
  unfold OMA.S_oeis_a296306.geometric
  simp_rw [pow_mul']
  exact Nat.geomSum_eq (by norm_num) (e + 1)

theorem a_core (e m : ℕ) (hm : Odd m) :
    OMA.S_oeis_a296306.a (2 ^ e * m) = OMA.S_oeis_a296306.geometric (e + 1) := by
  obtain ⟨h1, h2⟩ := core 2 e m hm
  have hm0 : m ≠ 0 := hm.pos.ne'
  unfold OMA.S_oeis_a296306.a
  rw [h1, h2, Nat.mul_div_cancel _ ((sigma_pos_iff).mpr (Nat.pos_of_ne_zero hm0)), sigma2_pow]

end PA296306

open ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a296306.main := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro k n hn
    obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
    obtain ⟨h1, h2⟩ := PA296306.core k e m hm
    rw [h1, h2]
    exact Dvd.intro_left _ rfl
  · intro n hn
    obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
    exact ⟨e + 1, by omega, PA296306.a_core e m hm⟩
  · intro j hj
    have := PA296306.a_core (j - 1) 1 odd_one
    rw [mul_one, show j - 1 + 1 = j by omega] at this
    exact this
  · intro h hh i hi0 hih
    obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : i ≠ 0)
    have hm1 : 1 ≤ m := hm.pos
    have heh : e < h := by
      have : 2 ^ e < 2 ^ h := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hm1) hih
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    have hsplit : 2 ^ h = 2 ^ e * 2 ^ (h - e) := by rw [← pow_add]; congr 1; omega
    have hmlt : m < 2 ^ (h - e) := by
      rw [hsplit] at hih
      exact Nat.lt_of_mul_lt_mul_left hih
    have hrest : 2 ^ h - 2 ^ e * m = 2 ^ e * (2 ^ (h - e) - m) := by
      rw [hsplit, Nat.mul_sub]
    have hodd : Odd (2 ^ (h - e) - m) := by
      have he2 : Even (2 ^ (h - e)) := (Nat.even_pow' (by omega)).mpr even_two
      exact Nat.Even.sub_odd hmlt.le he2 hm
    rw [hrest, PA296306.a_core e m hm, PA296306.a_core e _ hodd]
