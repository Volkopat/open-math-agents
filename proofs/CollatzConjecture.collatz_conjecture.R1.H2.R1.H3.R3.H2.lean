import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3

-- Step CollatzConjecture.collatz_conjecture.R1.H2.R1.H3.R3.H2
-- Credit: @justusklocke-cloud

/-!
The fractions 1054/665 and 485/306 have determinant one. A fraction strictly
between them has denominator at least 665 + 306 = 971. Two exact power
comparisons place the required exponential thresholds inside this interval.
-/

namespace OMA.CollatzPowersCorridor

private theorem lower_power : (2 : ℕ) ^ 1054 < 3 ^ 665 := by
  decide +kernel

private theorem upper_power : (300001 : ℕ) ^ 306 < 2 ^ 485 * 100000 ^ 306 := by
  decide +kernel

private theorem lower_cross_product {a b p q o e : ℕ} (hb : 0 < b)
    (ho : o ≠ 0) (hq : q ≠ 0) (hbase : b ^ p < a ^ q) (hpow : a ^ o < b ^ e) :
    p * o < q * e := by
  have h : b ^ (p * o) < b ^ (q * e) := calc
    _ = (b ^ p) ^ o := pow_mul _ _ _
    _ < (a ^ q) ^ o := Nat.pow_lt_pow_left hbase ho
    _ = (a ^ o) ^ q := by rw [← pow_mul, ← pow_mul, Nat.mul_comm q o]
    _ < (b ^ e) ^ q := Nat.pow_lt_pow_left hpow hq
    _ = _ := by rw [← pow_mul, Nat.mul_comm e q]
  by_contra! hge
  exact (not_lt_of_ge (Nat.pow_le_pow_right hb hge)) h

private theorem upper_cross_product {o e : ℕ} (hhi : o < 971) (hl : 1054 * o < 665 * e) :
    485 * o ≤ 306 * e := by
  by_contra! hu
  have hleft : 306 ≤ 306 * (665 * e - 1054 * o) := by omega
  have hright : 665 ≤ 665 * (485 * o - 306 * e) := by omega
  have hdenom : 306 * (665 * e - 1054 * o) + 665 * (485 * o - 306 * e) = o := by omega
  omega

private theorem upper_power_of_cross_product {a b c p q o e : ℕ} (hb : 0 < b)
    (ho : o ≠ 0) (hbase : a ^ q < b ^ p * c ^ q) (hcross : p * o ≤ q * e) :
    a ^ o < b ^ e * c ^ o := by
  have h : (a ^ o) ^ q < (b ^ e * c ^ o) ^ q := calc
    _ = (a ^ q) ^ o := by rw [← pow_mul, ← pow_mul, Nat.mul_comm o q]
    _ < (b ^ p * c ^ q) ^ o := Nat.pow_lt_pow_left hbase ho
    _ = b ^ (p * o) * c ^ (q * o) := by rw [mul_pow, ← pow_mul, ← pow_mul]
    _ ≤ b ^ (q * e) * c ^ (q * o) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hb hcross)
    _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm q e, Nat.mul_comm q o]
  by_contra! hge
  exact (not_lt_of_ge (Nat.pow_le_pow_left hge q)) h

theorem bound {o e : ℕ} (hlo : 1 ≤ o) (hhi : o < 971) (hpow : 3 ^ o < 2 ^ e) :
    300001 ^ o < 2 ^ e * 100000 ^ o := by
  have ho : o ≠ 0 := by omega
  have hl := lower_cross_product (by decide : 0 < (2 : ℕ)) ho (by decide : 665 ≠ 0)
    lower_power hpow
  exact upper_power_of_cross_product (by decide : 0 < (2 : ℕ)) ho
    upper_power (upper_cross_product hhi hl)

end OMA.CollatzPowersCorridor

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3.H2 := by
  intro o e hlo hhi hpow
  exact OMA.CollatzPowersCorridor.bound hlo hhi hpow
