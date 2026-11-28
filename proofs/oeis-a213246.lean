import OMAStatements.S_oeis_a213246
import Mathlib

-- Proof of Colin Barker's conjectures in OEIS A213246 (statement by @ivillar).
-- Idea: the nonzero 9th powers of GF(2^n) form the image of y ↦ y^9 on the cyclic group
-- GF(2^n)ˣ of order M = 2^n - 1, so a(n) = M / gcd(M, 9) (the formula of the OEIS entry); as 9
-- divides 2^6 - 1, gcd(M, 9) is 6-periodic in n, which gives the recurrence and the g.f.

namespace OMAA213246Helpers

open PowerSeries OMA.S_oeis_a213246

theorem card_pow (n : ℕ) (hn : n ≠ 0) :
    a n = (2 ^ n - 1) / Nat.gcd (2 ^ n - 1) 9 := by
  classical
  have e : {x : GaloisField 2 n // x ≠ 0 ∧ ∃ y : GaloisField 2 n, y ^ 9 = x} ≃
      (powMonoidHom 9 : (GaloisField 2 n)ˣ →* (GaloisField 2 n)ˣ).range :=
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

theorem gcd_period (m : ℕ) : Nat.gcd (2 ^ (m + 6) - 1) 9 = Nat.gcd (2 ^ m - 1) 9 := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have e : 2 ^ (m + 6) - 1 = (2 ^ m - 1) + (2 ^ m * 7) * 9 := by
    rw [pow_add]; norm_num; omega
  rw [e, Nat.gcd_add_mul_right_left]

theorem mul_a (n : ℕ) (hn : n ≠ 0) :
    ((Nat.gcd (2 ^ n - 1) 9 : ℕ) : ℤ) * a n = 2 ^ n - 1 := by
  rw [card_pow n hn]
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hd : Nat.gcd (2 ^ n - 1) 9 ∣ 2 ^ n - 1 := Nat.gcd_dvd_left _ _
  rw [← Nat.cast_mul, Nat.mul_div_cancel' hd]
  push_cast [Nat.cast_sub h1]
  ring

theorem recur (n : ℕ) (hn : 12 < n) : (a n : ℤ) = 65 * a (n - 6) - 64 * a (n - 12) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
  rw [show m + 12 - 6 = m + 6 by omega, show m + 12 - 12 = m by omega]
  have hm : m ≠ 0 := by omega
  have g1 := gcd_period m
  have g2 := gcd_period (m + 6)
  rw [show m + 6 + 6 = m + 12 by omega] at g2
  have h0 := mul_a m hm
  have h1 := mul_a (m + 6) (by omega)
  have h2 := mul_a (m + 12) (by omega)
  rw [g2, g1] at h2
  rw [g1] at h1
  have hg : ((Nat.gcd (2 ^ m - 1) 9 : ℕ) : ℤ) ≠ 0 := by
    have : 0 < Nat.gcd (2 ^ m - 1) 9 := Nat.gcd_pos_of_pos_right _ (by norm_num)
    exact_mod_cast this.ne'
  apply mul_left_cancel₀ hg
  rw [h2, mul_sub, mul_left_comm, h1, mul_left_comm, h0, pow_add, pow_add]
  ring

theorem key : mk (fun n => if n = 0 then (0 : ℚ) else a n) * ((X - 1) * (X + 1) * (2 * X - 1) * (2 * X + 1) * (X ^ 2 - X + 1) * (X ^ 2 + X + 1) * (4 * X ^ 2 - 2 * X + 1) * (4 * X ^ 2 + 2 * X + 1)) = X * (2 * X ^ 2 - X + 1) * (16 * X ^ 8 + 16 * X ^ 7 + 28 * X ^ 6 + 16 * X ^ 5 + 25 * X ^ 4 + 8 * X ^ 3 + 7 * X ^ 2 + 2 * X + 1) := by
  have e1 : ((X - 1) * (X + 1) * (2 * X - 1) * (2 * X + 1) * (X ^ 2 - X + 1) * (X ^ 2 + X + 1) * (4 * X ^ 2 - 2 * X + 1) * (4 * X ^ 2 + 2 * X + 1) : ℚ⟦X⟧) =
      1 - C (65 : ℚ) * X ^ 6 + C (64 : ℚ) * X ^ 12 := by
    rw [map_ofNat C 65, map_ofNat C 64]
    ring
  have e2 : (X * (2 * X ^ 2 - X + 1) * (16 * X ^ 8 + 16 * X ^ 7 + 28 * X ^ 6 + 16 * X ^ 5 + 25 * X ^ 4 + 8 * X ^ 3 + 7 * X ^ 2 + 2 * X + 1) : ℚ⟦X⟧) =
      X ^ 1 + X ^ 2 + C (7 : ℚ) * X ^ 3 + C (5 : ℚ) * X ^ 4 + C (31 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6 + C (62 : ℚ) * X ^ 7 + C (20 : ℚ) * X ^ 8 + C (56 : ℚ) * X ^ 9 + C (16 : ℚ) * X ^ 10 + C (32 : ℚ) * X ^ 11 := by
    rw [map_ofNat C 5, map_ofNat C 7, map_ofNat C 16, map_ofNat C 20, map_ofNat C 31, map_ofNat C 32, map_ofNat C 56, map_ofNat C 62]
    ring
  rw [e1, e2]
  have e3 : mk (fun n => if n = 0 then (0 : ℚ) else a n) * (1 - C (65 : ℚ) * X ^ 6 + C (64 : ℚ) * X ^ 12) =
      mk (fun n => if n = 0 then (0 : ℚ) else a n) - C (65 : ℚ) * (X ^ 6 * mk (fun n => if n = 0 then (0 : ℚ) else a n)) + C (64 : ℚ) * (X ^ 12 * mk (fun n => if n = 0 then (0 : ℚ) else a n)) := by
    ring
  rw [e3]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mk, coeff_X_pow_mul', coeff_X_pow]
  by_cases hn : n ≤ 12
  · interval_cases n <;> norm_num [card_pow]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 13 := ⟨n - 13, by omega⟩
    have := recur (m + 13) (by omega)
    rw [show m + 13 - 6 = m + 7 by omega, show m + 13 - 12 = m + 1 by omega] at this
    have h : ((a (m + 13) : ℤ) : ℚ) = ((65 * a (m + 7) - 64 * a (m + 1) : ℤ) : ℚ) := by
      rw [this]
    push_cast at h
    simp [h]
    try ring

end OMAA213246Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a213246.main := by
  refine ⟨OMAA213246Helpers.recur, ?_⟩
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp), OMAA213246Helpers.key]
