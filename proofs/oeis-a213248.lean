import OMAStatements.S_oeis_a213248
import Mathlib

-- Proof of Colin Barker's conjectures in OEIS A213248 (statement by @ivillar).
-- Idea: the nonzero 13th powers of GF(2^n) form the image of y ↦ y^13 on the cyclic group
-- GF(2^n)ˣ of order M = 2^n - 1, so a(n) = M / gcd(M, 13) (the formula of the OEIS entry); as 13
-- divides 2^12 - 1, gcd(M, 13) is 12-periodic in n, which gives the recurrence and the g.f.

namespace OMAA213248Helpers

open PowerSeries OMA.S_oeis_a213248

theorem card_pow (n : ℕ) (hn : n ≠ 0) :
    a n = (2 ^ n - 1) / Nat.gcd (2 ^ n - 1) 13 := by
  classical
  have e : {x : GaloisField 2 n // x ≠ 0 ∧ ∃ y : GaloisField 2 n, y ^ 13 = x} ≃
      (powMonoidHom 13 : (GaloisField 2 n)ˣ →* (GaloisField 2 n)ˣ).range :=
    { toFun := fun x => ⟨Units.mk0 x.1 x.2.1, by
          obtain ⟨y, hy⟩ := x.2.2
          have hy0 : y ≠ 0 := by
            rintro rfl
            exact x.2.1 (by rw [← hy]; simp)
          exact ⟨Units.mk0 y hy0, Units.ext (by simp [hy])⟩⟩
      invFun := fun u => ⟨(u.1 : GaloisField 2 n), u.1.ne_zero, by
          obtain ⟨v, hv⟩ := u.2
          exact ⟨(v : GaloisField 2 n), by rw [← hv]; simp⟩⟩
      left_inv := fun x => by ext; simp
      right_inv := fun u => by ext; simp }
  unfold a
  rw [Nat.card_congr e, IsCyclic.card_powMonoidHom_range, Nat.card_units, GaloisField.card 2 n hn]

theorem gcd_period (m : ℕ) : Nat.gcd (2 ^ (m + 12) - 1) 13 = Nat.gcd (2 ^ m - 1) 13 := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have e : 2 ^ (m + 12) - 1 = (2 ^ m - 1) + (2 ^ m * 315) * 13 := by
    rw [pow_add]; norm_num; omega
  rw [e, Nat.gcd_add_mul_right_left]

theorem mul_a (n : ℕ) (hn : n ≠ 0) :
    ((Nat.gcd (2 ^ n - 1) 13 : ℕ) : ℤ) * a n = 2 ^ n - 1 := by
  rw [card_pow n hn]
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hd : Nat.gcd (2 ^ n - 1) 13 ∣ 2 ^ n - 1 := Nat.gcd_dvd_left _ _
  rw [← Nat.cast_mul, Nat.mul_div_cancel' hd]
  push_cast [Nat.cast_sub h1]
  ring

theorem recur (n : ℕ) (hn : 24 < n) : (a n : ℤ) = 4097 * a (n - 12) - 4096 * a (n - 24) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 24 := ⟨n - 24, by omega⟩
  rw [show m + 24 - 12 = m + 12 by omega, show m + 24 - 24 = m by omega]
  have hm : m ≠ 0 := by omega
  have g1 := gcd_period m
  have g2 := gcd_period (m + 12)
  rw [show m + 12 + 12 = m + 24 by omega] at g2
  have h0 := mul_a m hm
  have h1 := mul_a (m + 12) (by omega)
  have h2 := mul_a (m + 24) (by omega)
  rw [g2, g1] at h2
  rw [g1] at h1
  have hg : ((Nat.gcd (2 ^ m - 1) 13 : ℕ) : ℤ) ≠ 0 := by
    have : 0 < Nat.gcd (2 ^ m - 1) 13 := Nat.gcd_pos_of_pos_right _ (by norm_num)
    exact_mod_cast this.ne'
  apply mul_left_cancel₀ hg
  rw [h2, mul_sub, mul_left_comm, h1, mul_left_comm, h0, pow_add, pow_add]
  ring

theorem key : mk (fun n => if n = 0 then (0 : ℚ) else a n) * (4096 * X ^ 24 - 4097 * X ^ 12 + 1) = X * (2048 * X ^ 22 + 3072 * X ^ 21 + 3584 * X ^ 20 + 3840 * X ^ 19 + 3968 * X ^ 18 + 4032 * X ^ 17 + 4064 * X ^ 16 + 4080 * X ^ 15 + 4088 * X ^ 14 + 4092 * X ^ 13 + 4094 * X ^ 12 + 315 * X ^ 11 + 2047 * X ^ 10 + 1023 * X ^ 9 + 511 * X ^ 8 + 255 * X ^ 7 + 127 * X ^ 6 + 63 * X ^ 5 + 31 * X ^ 4 + 15 * X ^ 3 + 7 * X ^ 2 + 3 * X + 1) := by
  have e1 : (4096 * X ^ 24 - 4097 * X ^ 12 + 1 : ℚ⟦X⟧) =
      1 - C (4097 : ℚ) * X ^ 12 + C (4096 : ℚ) * X ^ 24 := by
    rw [map_ofNat C 4097, map_ofNat C 4096]
    ring
  have e2 : (X * (2048 * X ^ 22 + 3072 * X ^ 21 + 3584 * X ^ 20 + 3840 * X ^ 19 + 3968 * X ^ 18 + 4032 * X ^ 17 + 4064 * X ^ 16 + 4080 * X ^ 15 + 4088 * X ^ 14 + 4092 * X ^ 13 + 4094 * X ^ 12 + 315 * X ^ 11 + 2047 * X ^ 10 + 1023 * X ^ 9 + 511 * X ^ 8 + 255 * X ^ 7 + 127 * X ^ 6 + 63 * X ^ 5 + 31 * X ^ 4 + 15 * X ^ 3 + 7 * X ^ 2 + 3 * X + 1) : ℚ⟦X⟧) =
      X ^ 1 + C (3 : ℚ) * X ^ 2 + C (7 : ℚ) * X ^ 3 + C (15 : ℚ) * X ^ 4 + C (31 : ℚ) * X ^ 5 + C (63 : ℚ) * X ^ 6 + C (127 : ℚ) * X ^ 7 + C (255 : ℚ) * X ^ 8 + C (511 : ℚ) * X ^ 9 + C (1023 : ℚ) * X ^ 10 + C (2047 : ℚ) * X ^ 11 + C (315 : ℚ) * X ^ 12 + C (4094 : ℚ) * X ^ 13 + C (4092 : ℚ) * X ^ 14 + C (4088 : ℚ) * X ^ 15 + C (4080 : ℚ) * X ^ 16 + C (4064 : ℚ) * X ^ 17 + C (4032 : ℚ) * X ^ 18 + C (3968 : ℚ) * X ^ 19 + C (3840 : ℚ) * X ^ 20 + C (3584 : ℚ) * X ^ 21 + C (3072 : ℚ) * X ^ 22 + C (2048 : ℚ) * X ^ 23 := by
    rw [map_ofNat C 3, map_ofNat C 7, map_ofNat C 15, map_ofNat C 31, map_ofNat C 63, map_ofNat C 127, map_ofNat C 255, map_ofNat C 315, map_ofNat C 511, map_ofNat C 1023, map_ofNat C 2047, map_ofNat C 2048, map_ofNat C 3072, map_ofNat C 3584, map_ofNat C 3840, map_ofNat C 3968, map_ofNat C 4032, map_ofNat C 4064, map_ofNat C 4080, map_ofNat C 4088, map_ofNat C 4092, map_ofNat C 4094]
    ring
  rw [e1, e2]
  have e3 : mk (fun n => if n = 0 then (0 : ℚ) else a n) * (1 - C (4097 : ℚ) * X ^ 12 + C (4096 : ℚ) * X ^ 24) =
      mk (fun n => if n = 0 then (0 : ℚ) else a n) - C (4097 : ℚ) * (X ^ 12 * mk (fun n => if n = 0 then (0 : ℚ) else a n)) + C (4096 : ℚ) * (X ^ 24 * mk (fun n => if n = 0 then (0 : ℚ) else a n)) := by
    ring
  rw [e3]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mk, coeff_X_pow_mul', coeff_X_pow]
  by_cases hn : n ≤ 24
  · interval_cases n <;> norm_num [card_pow]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 25 := ⟨n - 25, by omega⟩
    have := recur (m + 25) (by omega)
    rw [show m + 25 - 12 = m + 13 by omega, show m + 25 - 24 = m + 1 by omega] at this
    have h : ((a (m + 25) : ℤ) : ℚ) = ((4097 * a (m + 13) - 4096 * a (m + 1) : ℤ) : ℚ) := by
      rw [this]
    push_cast at h
    simp [h]
    try ring

end OMAA213248Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a213248.main := by
  refine ⟨OMAA213248Helpers.recur, ?_⟩
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp), OMAA213248Helpers.key]
