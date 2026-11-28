import OMAReductions.R_oeis_a228947_R1
import Mathlib

/-
Step H2 of reduction R1 for A228947: for odd `m` with exactly three prime factors,
`σ (m ^ 2) ≠ m ^ 2 + φ (m ^ 2)` (the case `ω (m) = 3` of Iannucci, J. Integer Seq. 20 (2017),
Article 17.6.2, Theorem 4).

Write `m = p ^ a q ^ b r ^ c` with odd primes `p < q < r`, `x = p ^ (2 a - 1)`, `y = q ^ (2 b - 1)`,
`z = r ^ (2 c - 1)`, `B = p q r`, `A = (p - 1) (q - 1) (r - 1)`. The hypothesis becomes the identity
`(B ^ 2 - (B + A) A) x y z = p²q² x y + p²r² x z + q²r² y z - p² x - q² y - r² z + 1`.
So `B / A` exceeds the golden ratio, which forces `p = 3`. A second rearrangement
`z E = (9 x - 1) (q ² y - 1)` rules out every case where `F = D₂ x y - 9 x - q² y + 1 ≥ 0`, where
`D₂ = -q² + 14 q - 4`. What is left is finite: `q = 11, 13` with `x = 3`, and `q = 17, 19, 23`,
each with `r` bounded. Each of these cases is closed by splitting `x, y, z` into exact odd powers
and tails, where the multilinear identity has coefficients of one sign (linarith with product hints).
-/

namespace OMA.P228947H2

open ArithmeticFunction

/-- `x` is an odd power of `b`. -/
def OP (b x : ℤ) : Prop := ∃ k : ℕ, x = b ^ (2 * k + 1)

lemma op_split {b x : ℤ} (j : ℕ) (hb : 1 < b) (hx : OP b x) (hle : b ^ (2 * j + 1) ≤ x) :
    x = b ^ (2 * j + 1) ∨ b ^ (2 * j + 3) ≤ x := by
  obtain ⟨k, rfl⟩ := hx
  have hk : 2 * j + 1 ≤ 2 * k + 1 := (pow_le_pow_iff_right₀ hb).mp hle
  rcases Nat.lt_or_ge j k with h | h
  · right
    exact pow_le_pow_right₀ hb.le (by omega)
  · left
    have : k = j := by omega
    rw [this]

lemma case11 (r y z : ℤ) (hr1 : 13 ≤ r) (hr2 : r ≤ 128) (hro : r % 2 = 1)
    (hyo : OP 11 y) (hzo : OP r z) (hyq : 11 ≤ y) (hzr : r ≤ z)
    (h : (9 * 11 ^ 2 * r ^ 2 - (3 * 11 * r + 2 * (11 - 1) * (r - 1)) * (2 * (11 - 1) * (r - 1))) * (3 * y * z) =
      9 * 11 ^ 2 * (3 * y) + 9 * r ^ 2 * (3 * z) + 11 ^ 2 * r ^ 2 * (y * z) - 9 * 3 - 11 ^ 2 * y - r ^ 2 * z + 1) : False := by
  interval_cases r
  · -- r = 13, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 15, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 17, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 19, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 21, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 23, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 25, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 27, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 29, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 31, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 33, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 35, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 37, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 39, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 41, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 43, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 45, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 47, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 49, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 51, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 53, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 55, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 57, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 59, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 61, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 63, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 65, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 67, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 69, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 71, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 73, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 75, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 77, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 79, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 81, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 83, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 85, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 87, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 89, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 91, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 93, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 95, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 97, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 99, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 101, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 103, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 105, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 107, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 109, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 111, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 113, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 115, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 117, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 119, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 121, leaves 2
    rcases (show y = 11 ∨ 1331 ≤ y by
        have := op_split 0 (by norm_num) hyo (by norm_num; linarith); norm_num at this; exact this) with rfl | hby1
    · linarith
    · linarith [mul_nonneg (sub_nonneg.2 hby1) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 123, leaves 2
    rcases (show y = 11 ∨ 1331 ≤ y by
        have := op_split 0 (by norm_num) hyo (by norm_num; linarith); norm_num at this; exact this) with rfl | hby1
    · linarith
    · linarith [mul_nonneg (sub_nonneg.2 hby1) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 125, leaves 2
    rcases (show y = 11 ∨ 1331 ≤ y by
        have := op_split 0 (by norm_num) hyo (by norm_num; linarith); norm_num at this; exact this) with rfl | hby1
    · linarith
    · linarith [mul_nonneg (sub_nonneg.2 hby1) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 127, leaves 2
    rcases (show y = 11 ∨ 1331 ≤ y by
        have := op_split 0 (by norm_num) hyo (by norm_num; linarith); norm_num at this; exact this) with rfl | hby1
    · linarith
    · linarith [mul_nonneg (sub_nonneg.2 hby1) (sub_nonneg.2 hzr)]
  · norm_num at hro

lemma case13 (r y z : ℤ) (hr1 : 15 ≤ r) (hr2 : r ≤ 44) (hro : r % 2 = 1)
    (_hyo : OP 13 y) (hzo : OP r z) (hyq : 13 ≤ y) (hzr : r ≤ z)
    (h : (9 * 13 ^ 2 * r ^ 2 - (3 * 13 * r + 2 * (13 - 1) * (r - 1)) * (2 * (13 - 1) * (r - 1))) * (3 * y * z) =
      9 * 13 ^ 2 * (3 * y) + 9 * r ^ 2 * (3 * z) + 13 ^ 2 * r ^ 2 * (y * z) - 9 * 3 - 13 ^ 2 * y - r ^ 2 * z + 1) : False := by
  interval_cases r
  · -- r = 15, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 17, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 19, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 21, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 23, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 25, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 27, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 29, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 31, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 33, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 35, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 37, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 39, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 41, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 43, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
  · norm_num at hro

lemma case17 (r x y z : ℤ) (hr1 : 19 ≤ r) (hr2 : r ≤ 66) (hro : r % 2 = 1) (hxo : OP 3 x) (hx3 : 3 ≤ x)
    (hyo : OP 17 y) (hzo : OP r z) (hyq : 17 ≤ y) (hzr : r ≤ z)
    (h : (9 * 17 ^ 2 * r ^ 2 - (3 * 17 * r + 2 * (17 - 1) * (r - 1)) * (2 * (17 - 1) * (r - 1))) * (x * y * z) =
      9 * 17 ^ 2 * (x * y) + 9 * r ^ 2 * (x * z) + 17 ^ 2 * r ^ 2 * (y * z) - 9 * x - 17 ^ 2 * y - r ^ 2 * z + 1) : False := by
  interval_cases r
  · -- r = 19, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hx3) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hx3) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hx3) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 21, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hx3) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hx3) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hx3) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 23, leaves 1
    linarith [mul_nonneg (sub_nonneg.2 hx3) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hx3) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hx3) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 25, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 27, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 29, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 31, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 33, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 35, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 37, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 39, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 41, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 43, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 45, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 47, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 49, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 51, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 53, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 55, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 57, leaves 3
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · rcases (show x = 27 ∨ 243 ≤ x by
          have := op_split 1 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx2
      · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
      · linarith [mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 59, leaves 3
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · rcases (show x = 27 ∨ 243 ≤ x by
          have := op_split 1 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx2
      · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
      · linarith [mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 61, leaves 3
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · rcases (show x = 27 ∨ 243 ≤ x by
          have := op_split 1 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx2
      · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
      · linarith [mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 63, leaves 3
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · rcases (show x = 27 ∨ 243 ≤ x by
          have := op_split 1 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx2
      · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
      · linarith [mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 65, leaves 5
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · rcases (show x = 27 ∨ 243 ≤ x by
          have := op_split 1 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx2
      · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
      · rcases (show x = 243 ∨ 2187 ≤ x by
            have := op_split 2 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx3
        · rcases (show y = 17 ∨ 4913 ≤ y by
              have := op_split 0 (by norm_num) hyo (by norm_num; linarith); norm_num at this; exact this) with rfl | hby4
          · linarith
          · linarith [mul_nonneg (sub_nonneg.2 hby4) (sub_nonneg.2 hzr)]
        · linarith [mul_nonneg (sub_nonneg.2 hbx3) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx3) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx3) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro

lemma case19 (r x y z : ℤ) (hr1 : 21 ≤ r) (hr2 : r ≤ 46) (hro : r % 2 = 1) (hxo : OP 3 x) (hx3 : 3 ≤ x)
    (hyo : OP 19 y) (hzo : OP r z) (hyq : 19 ≤ y) (hzr : r ≤ z)
    (h : (9 * 19 ^ 2 * r ^ 2 - (3 * 19 * r + 2 * (19 - 1) * (r - 1)) * (2 * (19 - 1) * (r - 1))) * (x * y * z) =
      9 * 19 ^ 2 * (x * y) + 9 * r ^ 2 * (x * z) + 19 ^ 2 * r ^ 2 * (y * z) - 9 * x - 19 ^ 2 * y - r ^ 2 * z + 1) : False := by
  interval_cases r
  · -- r = 21, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 23, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 25, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 27, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 29, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 31, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 33, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 35, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 37, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 39, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 41, leaves 4
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · rcases (show x = 27 ∨ 243 ≤ x by
          have := op_split 1 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx2
      · rcases (show y = 19 ∨ 6859 ≤ y by
            have := op_split 0 (by norm_num) hyo (by norm_num; linarith); norm_num at this; exact this) with rfl | hby3
        · linarith
        · linarith [mul_nonneg (sub_nonneg.2 hby3) (sub_nonneg.2 hzr)]
      · linarith [mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 43, leaves 3
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · rcases (show x = 27 ∨ 243 ≤ x by
          have := op_split 1 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx2
      · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
      · linarith [mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 45, leaves 3
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · rcases (show x = 27 ∨ 243 ≤ x by
          have := op_split 1 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx2
      · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
      · linarith [mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro

lemma case23 (r x y z : ℤ) (hr1 : 25 ≤ r) (hr2 : r ≤ 32) (hro : r % 2 = 1) (hxo : OP 3 x) (hx3 : 3 ≤ x)
    (_hyo : OP 23 y) (hzo : OP r z) (hyq : 23 ≤ y) (hzr : r ≤ z)
    (h : (9 * 23 ^ 2 * r ^ 2 - (3 * 23 * r + 2 * (23 - 1) * (r - 1)) * (2 * (23 - 1) * (r - 1))) * (x * y * z) =
      9 * 23 ^ 2 * (x * y) + 9 * r ^ 2 * (x * z) + 23 ^ 2 * r ^ 2 * (y * z) - 9 * x - 23 ^ 2 * y - r ^ 2 * z + 1) : False := by
  interval_cases r
  · -- r = 25, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 27, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 29, leaves 2
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · linarith [mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx1) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro
  · -- r = 31, leaves 3
    rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx1
    · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
    · rcases (show x = 27 ∨ 243 ≤ x by
          have := op_split 1 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this) with rfl | hbx2
      · linarith [mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr)]
      · linarith [mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hyq), mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hzr), mul_nonneg (sub_nonneg.2 hyq) (sub_nonneg.2 hzr), mul_nonneg (mul_nonneg (sub_nonneg.2 hbx2) (sub_nonneg.2 hyq)) (sub_nonneg.2 hzr)]
  · norm_num at hro

lemma one_le_sq_mul {a b : ℤ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a ^ 2 * b := by
  have h1 : 1 ≤ a ^ 2 := by nlinarith
  have h2 : a ^ 2 * 1 ≤ a ^ 2 * b := mul_le_mul_of_nonneg_left hb (by positivity)
  linarith

lemma op_ge {b x : ℤ} (hb : 1 < b) (hx : OP b x) : b ≤ x := by
  obtain ⟨k, rfl⟩ := hx
  calc b = b ^ 1 := (pow_one b).symm
    _ ≤ b ^ (2 * k + 1) := pow_le_pow_right₀ hb.le (by omega)

/-- `B ^ 2 < (B + A) A` as soon as `48 B ≤ 77 A` and `B > 0` (since `77 / 48` is below the golden ratio). -/
lemma sq_lt_of_ratio (A B : ℤ) (hB : 0 < B) (h : 48 * B ≤ 77 * A) : B ^ 2 < (B + A) * A := by
  nlinarith

/-- The same with `161 / 100`. -/
lemma sq_lt_of_ratio' (A B : ℤ) (hB : 0 < B) (h : 100 * B ≤ 161 * A) : B ^ 2 < (B + A) * A := by
  nlinarith

/-- If `F ≥ 0` the identity is impossible (no bound on `r` needed). -/
lemma F_nonneg_false (q r x y z : ℤ) (hq5 : 5 ≤ q) (hqr : q < r) (hx3 : 3 ≤ x) (hyq : q ≤ y)
    (hzr : r ≤ z)
    (h : (9 * q ^ 2 * r ^ 2 - (3 * q * r + 2 * (q - 1) * (r - 1)) * (2 * (q - 1) * (r - 1))) * (x * y * z) =
      9 * q ^ 2 * (x * y) + 9 * r ^ 2 * (x * z) + q ^ 2 * r ^ 2 * (y * z) - 9 * x - q ^ 2 * y - r ^ 2 * z + 1)
    (hF : 0 ≤ (-q ^ 2 + 14 * q - 4) * (x * y) - 9 * x - q ^ 2 * y + 1) : False := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := by linarith
  have hr0 : 0 < r := by linarith
  have hq0 : 0 < q := by linarith
  have hxy : 0 < x * y := mul_pos hx0 hy0
  obtain ⟨E, hEdef⟩ : ∃ E, E = (9 * q ^ 2 * r ^ 2 - (3 * q * r + 2 * (q - 1) * (r - 1)) *
      (2 * (q - 1) * (r - 1))) * (x * y) - r ^ 2 * (9 * x + q ^ 2 * y - 1) := ⟨_, rfl⟩
  have hE : z * E = (9 * x - 1) * (q ^ 2 * y - 1) := by
    rw [hEdef]
    linear_combination h
  have hEx : E = r ^ 2 * ((-q ^ 2 + 14 * q - 4) * (x * y) - 9 * x - q ^ 2 * y + 1) +
      x * y * ((3 * q * (2 * (q - 1)) + 2 * (2 * (q - 1)) ^ 2) * r - (2 * (q - 1)) ^ 2) := by
    rw [hEdef]
    ring
  have hq2 : 25 ≤ q ^ 2 := by nlinarith
  have hqy0 : q ^ 2 * 1 ≤ q ^ 2 * y := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hqy : 25 ≤ q ^ 2 * y := by linarith
  have hM : 0 < (9 * x - 1) * (q ^ 2 * y - 1) := mul_pos (by linarith) (by linarith)
  have hEpos : 0 < E := by
    by_contra hneg
    push Not at hneg
    have := mul_nonpos_of_nonneg_of_nonpos hz0.le hneg
    linarith
  have hEge : x * y * (3 * q * (2 * (q - 1)) * r) ≤ E := by
    rw [hEx]
    have e1 : 0 ≤ r ^ 2 * ((-q ^ 2 + 14 * q - 4) * (x * y) - 9 * x - q ^ 2 * y + 1) :=
      mul_nonneg (sq_nonneg r) hF
    have e2 : 0 ≤ x * y * ((2 * (q - 1)) ^ 2 * (2 * r - 1)) :=
      mul_nonneg hxy.le (mul_nonneg (sq_nonneg _) (by linarith))
    linarith [e1, e2]
  have h1 : r * E ≤ z * E := mul_le_mul_of_nonneg_right hzr hEpos.le
  have h2 : r * (x * y * (3 * q * (2 * (q - 1)) * r)) ≤ r * E :=
    mul_le_mul_of_nonneg_left hEge hr0.le
  have h3 : (9 * x - 1) * (q ^ 2 * y - 1) < 9 * q ^ 2 * (x * y) := by nlinarith
  have hrr : r ≤ r ^ 2 := by nlinarith
  have h4 : 3 * q + 1 ≤ 2 * (q - 1) * r ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hq5) (sq_nonneg r)]
  have h5 : (3 * q + 1) * (3 * q * (x * y)) ≤ 2 * (q - 1) * r ^ 2 * (3 * q * (x * y)) :=
    mul_le_mul_of_nonneg_right h4 (mul_nonneg (by linarith) hxy.le)
  have h6 : 0 < q * (x * y) := mul_pos hq0 hxy
  linarith

/-- `p = 3`. -/
lemma core3 (q r x y z : ℤ) (hq5 : 5 ≤ q) (hqr : q < r) (hqo : q % 2 = 1) (hro : r % 2 = 1)
    (hqc : q ≠ 15 ∧ q ≠ 21 ∧ q ≠ 25 ∧ q ≠ 27)
    (hxo : OP 3 x) (hyo : OP q y) (hzo : OP r z)
    (h : (9 * q ^ 2 * r ^ 2 - (3 * q * r + 2 * (q - 1) * (r - 1)) * (2 * (q - 1) * (r - 1))) * (x * y * z) =
      9 * q ^ 2 * (x * y) + 9 * r ^ 2 * (x * z) + q ^ 2 * r ^ 2 * (y * z) - 9 * x - q ^ 2 * y - r ^ 2 * z + 1) :
    False := by
  have hx3 : 3 ≤ x := op_ge (by norm_num) hxo
  have hyq : q ≤ y := op_ge (by linarith) hyo
  have hzr : r ≤ z := op_ge (by linarith) hzo
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := by linarith
  by_cases hF : 0 ≤ (-q ^ 2 + 14 * q - 4) * (x * y) - 9 * x - q ^ 2 * y + 1
  · exact F_nonneg_false q r x y z hq5 hqr hx3 hyq hzr h hF
  push Not at hF
  rcases (by omega : q ≤ 13 ∨ 15 ≤ q) with hq13 | hq15
  · interval_cases q
    · nlinarith [mul_nonneg (sub_nonneg.2 hx3) (sub_nonneg.2 hyq)]
    · norm_num at hqo
    · nlinarith [mul_nonneg (sub_nonneg.2 hx3) (sub_nonneg.2 hyq)]
    · norm_num at hqo
    · nlinarith [mul_nonneg (sub_nonneg.2 hx3) (sub_nonneg.2 hyq)]
    · norm_num at hqo
    · rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this)
        with rfl | hx27
      · have hr128 : r ≤ 128 := by
          by_contra hr
          push Not at hr
          have hG : -34 * r ^ 2 + 4380 * r - 1200 < 0 := by nlinarith
          have h7 := mul_neg_of_neg_of_pos hG (mul_pos hy0 hz0)
          have h8 : 0 ≤ r ^ 2 * z := mul_nonneg (sq_nonneg r) hz0.le
          linarith
        exact case11 r y z (by omega) hr128 hro hyo hzo hyq hzr (by linear_combination h)
      · nlinarith [mul_nonneg (sub_nonneg.2 hx27) (sub_nonneg.2 hyq)]
    · norm_num at hqo
    · rcases (show x = 3 ∨ 27 ≤ x by
        have := op_split 0 (by norm_num) hxo (by norm_num; linarith); norm_num at this; exact this)
        with rfl | hx27
      · have hr44 : r ≤ 44 := by
          by_contra hr
          push Not at hr
          have hG : -142 * r ^ 2 + 6264 * r - 1728 < 0 := by nlinarith
          have h7 := mul_neg_of_neg_of_pos hG (mul_pos hy0 hz0)
          have h8 : 0 ≤ r ^ 2 * z := mul_nonneg (sq_nonneg r) hz0.le
          linarith
        exact case13 r y z (by omega) hr44 hro hyo hzo hyq hzr (by linear_combination h)
      · nlinarith [mul_nonneg (sub_nonneg.2 hx27) (sub_nonneg.2 hyq)]
  · have hxyz : 0 < x * y * z := mul_pos (mul_pos hx0 hy0) hz0
    have hR : 0 < 9 * q ^ 2 * (x * y) + 9 * r ^ 2 * (x * z) + q ^ 2 * r ^ 2 * (y * z) - 9 * x -
        q ^ 2 * y - r ^ 2 * z + 1 := by
      have e1 : 0 ≤ 9 * x * (q ^ 2 * y - 1) :=
        mul_nonneg (by linarith) (sub_nonneg.2 (one_le_sq_mul (by linarith) (by linarith)))
      have e2 : 0 ≤ q ^ 2 * y * (r ^ 2 * z - 1) :=
        mul_nonneg (mul_nonneg (sq_nonneg q) hy0.le)
          (sub_nonneg.2 (one_le_sq_mul (by linarith) (by linarith)))
      have e3 : 0 ≤ r ^ 2 * z * (9 * x - 1) :=
        mul_nonneg (mul_nonneg (sq_nonneg r) hz0.le) (by linarith)
      linarith
    have hD : 0 < 9 * q ^ 2 * r ^ 2 - (3 * q * r + 2 * (q - 1) * (r - 1)) * (2 * (q - 1) * (r - 1)) := by
      by_contra hD
      push Not at hD
      have := mul_nonpos_of_nonpos_of_nonneg hD hxyz.le
      linarith
    have hq23 : q ≤ 23 := by
      by_contra hq
      push Not at hq
      have hq29 : 29 ≤ q := by omega
      have hr31 : 31 ≤ r := by omega
      have hB : 0 < 3 * q * r := mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
      have hlt := sq_lt_of_ratio' (2 * (q - 1) * (r - 1)) (3 * q * r) hB
        (by nlinarith [mul_nonneg (sub_nonneg.2 hq29) (sub_nonneg.2 hr31)])
      linarith
    interval_cases q
    · exact absurd rfl hqc.1
    · norm_num at hqo
    · have hr66 : r ≤ 66 := by nlinarith
      exact case17 r x y z (by omega) hr66 hro hxo hx3 hyo hzo hyq hzr (by linear_combination h)
    · norm_num at hqo
    · have hr46 : r ≤ 46 := by nlinarith
      exact case19 r x y z (by omega) hr46 hro hxo hx3 hyo hzo hyq hzr (by linear_combination h)
    · norm_num at hqo
    · exact absurd rfl hqc.2.1
    · norm_num at hqo
    · have hr32 : r ≤ 32 := by nlinarith
      exact case23 r x y z (by omega) hr32 hro hxo hx3 hyo hzo hyq hzr (by linear_combination h)

/-- For `p ≥ 5` the golden-ratio condition fails: `B ^ 2 < (B + A) A`. -/
lemma D_neg_p5 (p q r : ℤ) (hp : 5 ≤ p) (hq : 7 ≤ q) (hr : 11 ≤ r) :
    (p * q * r) ^ 2 < (p * q * r + (p - 1) * (q - 1) * (r - 1)) * ((p - 1) * (q - 1) * (r - 1)) := by
  apply sq_lt_of_ratio
  · exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  · have h1 : 4 * p ≤ 5 * (p - 1) := by linarith
    have h2 : 6 * q ≤ 7 * (q - 1) := by linarith
    have h3 : 10 * r ≤ 11 * (r - 1) := by linarith
    have h12 : (4 * p) * (6 * q) ≤ (5 * (p - 1)) * (7 * (q - 1)) :=
      mul_le_mul h1 h2 (by linarith) (by linarith)
    have h123 : (4 * p) * (6 * q) * (10 * r) ≤ (5 * (p - 1)) * (7 * (q - 1)) * (11 * (r - 1)) :=
      mul_le_mul h12 h3 (by linarith) (mul_nonneg (by linarith) (by linarith))
    linarith

/-- The arithmetic core over `ℤ`: `p < q < r` odd, `x = p ^ (2 a - 1)`, `s = σ (p ^ (2 a))`, etc. -/
lemma core (p q r x y z s t u : ℤ) (hp3 : 3 ≤ p) (hpq : p < q) (hqr : q < r) (hpo : p % 2 = 1)
    (hqo : q % 2 = 1) (hro : r % 2 = 1) (hqc : q ≠ 15 ∧ q ≠ 21 ∧ q ≠ 25 ∧ q ≠ 27) (hr9 : r ≠ 9)
    (hxo : OP p x) (hyo : OP q y) (hzo : OP r z)
    (hs : s * (p - 1) + 1 = p * p * x) (ht : t * (q - 1) + 1 = q * q * y)
    (hu : u * (r - 1) + 1 = r * r * z)
    (heq : s * t * u = p * x * (q * y) * (r * z) + x * (p - 1) * (y * (q - 1)) * (z * (r - 1))) :
    False := by
  have hid : ((p * q * r) ^ 2 - (p * q * r + (p - 1) * (q - 1) * (r - 1)) *
      ((p - 1) * (q - 1) * (r - 1))) * (x * y * z) =
      p ^ 2 * q ^ 2 * (x * y) + p ^ 2 * r ^ 2 * (x * z) + q ^ 2 * r ^ 2 * (y * z) - p ^ 2 * x -
        q ^ 2 * y - r ^ 2 * z + 1 := by
    linear_combination (-(q ^ 2 * y - 1) * (r ^ 2 * z - 1)) * hs +
      (-(s * (p - 1)) * (r ^ 2 * z - 1)) * ht + (-(s * (p - 1)) * (t * (q - 1))) * hu +
      ((p - 1) * (q - 1) * (r - 1)) * heq
  rcases (by omega : p = 3 ∨ 5 ≤ p) with rfl | hp5
  · exact core3 q r x y z (by omega) hqr hqo hro hqc hxo hyo hzo (by linear_combination hid)
  · have hq7 : 7 ≤ q := by omega
    have hr11 : 11 ≤ r := by omega
    have hx0 : 0 < x := by have := op_ge (by linarith) hxo; linarith
    have hy0 : 0 < y := by have := op_ge (by linarith) hyo; linarith
    have hz0 : 0 < z := by have := op_ge (by linarith) hzo; linarith
    have hxyz : 0 < x * y * z := mul_pos (mul_pos hx0 hy0) hz0
    have e1 : 0 ≤ p ^ 2 * x * (q ^ 2 * y - 1) :=
      mul_nonneg (mul_nonneg (sq_nonneg p) hx0.le)
        (sub_nonneg.2 (one_le_sq_mul (by linarith) (by linarith)))
    have e2 : 0 ≤ q ^ 2 * y * (r ^ 2 * z - 1) :=
      mul_nonneg (mul_nonneg (sq_nonneg q) hy0.le)
        (sub_nonneg.2 (one_le_sq_mul (by linarith) (by linarith)))
    have e3 : 0 ≤ r ^ 2 * z * (p ^ 2 * x - 1) :=
      mul_nonneg (mul_nonneg (sq_nonneg r) hz0.le)
        (sub_nonneg.2 (one_le_sq_mul (by linarith) (by linarith)))
    have hlt := D_neg_p5 p q r hp5 hq7 hr11
    have := mul_neg_of_neg_of_pos (sub_neg.2 hlt) hxyz
    linarith

/-- `σ (p ^ k) (p - 1) + 1 = p ^ (k + 1)`. -/
lemma sigma_pp (p k : ℕ) (hp : p.Prime) : sigma 1 (p ^ k) * (p - 1) + 1 = p ^ (k + 1) := by
  rw [sigma_one_apply_prime_pow hp]
  have h := geom_sum_mul_add (p - 1) (k + 1)
  rwa [Nat.sub_add_cancel hp.one_le] at h

lemma not_comp {q : ℕ} (hq : q.Prime) (n : ℕ) (hn : ¬ n.Prime) : (q : ℤ) ≠ n := by
  intro h
  have : q = n := by exact_mod_cast h
  subst this
  exact hn hq

/-- The case `m = p ^ a q ^ b r ^ c` with odd primes `p < q < r`. -/
lemma three_primes {p q r a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hp2 : p ≠ 2)
    (hpq : p < q) (hqr : q < r) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    sigma 1 ((p ^ a * q ^ b * r ^ c) ^ 2) ≠
      (p ^ a * q ^ b * r ^ c) ^ 2 + Nat.totient ((p ^ a * q ^ b * r ^ c) ^ 2) := by
  intro h
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have e1 : (p ^ (a' + 1) * q ^ (b' + 1) * r ^ (c' + 1)) ^ 2 =
      p ^ (2 * a' + 2) * q ^ (2 * b' + 2) * r ^ (2 * c' + 2) := by ring
  rw [e1] at h
  have hpq' : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq.ne
  have hpr' : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr (by omega)
  have hqr' : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqr.ne
  have hc1 : Nat.Coprime (p ^ (2 * a' + 2)) (q ^ (2 * b' + 2)) := Nat.Coprime.pow _ _ hpq'
  have hc2 : Nat.Coprime (p ^ (2 * a' + 2) * q ^ (2 * b' + 2)) (r ^ (2 * c' + 2)) :=
    Nat.Coprime.mul_left (Nat.Coprime.pow _ _ hpr') (Nat.Coprime.pow _ _ hqr')
  have hs := sigma_pp p (2 * a' + 2) hp
  have ht := sigma_pp q (2 * b' + 2) hq
  have hu := sigma_pp r (2 * c' + 2) hr
  rw [isMultiplicative_sigma.map_mul_of_coprime hc2, isMultiplicative_sigma.map_mul_of_coprime hc1,
    Nat.totient_mul hc2, Nat.totient_mul hc1, Nat.totient_prime_pow hp (by omega),
    Nat.totient_prime_pow hq (by omega), Nat.totient_prime_pow hr (by omega)] at h
  generalize sigma 1 (p ^ (2 * a' + 2)) = s at h hs
  generalize sigma 1 (q ^ (2 * b' + 2)) = t at h ht
  generalize sigma 1 (r ^ (2 * c' + 2)) = u at h hu
  have ex1 : 2 * a' + 2 - 1 = 2 * a' + 1 := by omega
  have ex2 : 2 * b' + 2 - 1 = 2 * b' + 1 := by omega
  have ex3 : 2 * c' + 2 - 1 = 2 * c' + 1 := by omega
  rw [ex1, ex2, ex3] at h
  have hp1 : p ^ (2 * a' + 2) = p * p ^ (2 * a' + 1) := by ring
  have hq1 : q ^ (2 * b' + 2) = q * q ^ (2 * b' + 1) := by ring
  have hr1 : r ^ (2 * c' + 2) = r * r ^ (2 * c' + 1) := by ring
  have hp3 : p ^ (2 * a' + 2 + 1) = p * p * p ^ (2 * a' + 1) := by ring
  have hq3 : q ^ (2 * b' + 2 + 1) = q * q * q ^ (2 * b' + 1) := by ring
  have hr3 : r ^ (2 * c' + 2 + 1) = r * r * r ^ (2 * c' + 1) := by ring
  rw [hp1, hq1, hr1] at h
  rw [hp3] at hs
  rw [hq3] at ht
  rw [hr3] at hu
  have hxo : OP (p : ℤ) ((p ^ (2 * a' + 1) : ℕ) : ℤ) := ⟨a', Nat.cast_pow p (2 * a' + 1)⟩
  have hyo : OP (q : ℤ) ((q ^ (2 * b' + 1) : ℕ) : ℤ) := ⟨b', Nat.cast_pow q (2 * b' + 1)⟩
  have hzo : OP (r : ℤ) ((r ^ (2 * c' + 1) : ℕ) : ℤ) := ⟨c', Nat.cast_pow r (2 * c' + 1)⟩
  generalize p ^ (2 * a' + 1) = x at h hs hxo
  generalize q ^ (2 * b' + 1) = y at h ht hyo
  generalize r ^ (2 * c' + 1) = z at h hu hzo
  have hp3' : 3 ≤ p := by have := hp.two_le; omega
  have hpo := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hqo := Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))
  have hro := Nat.odd_iff.mp (hr.odd_of_ne_two (by omega))
  have hqc : (q : ℤ) ≠ 15 ∧ (q : ℤ) ≠ 21 ∧ (q : ℤ) ≠ 25 ∧ (q : ℤ) ≠ 27 :=
    ⟨not_comp hq 15 (by norm_num), not_comp hq 21 (by norm_num), not_comp hq 25 (by norm_num),
      not_comp hq 27 (by norm_num)⟩
  have hr9 : (r : ℤ) ≠ 9 := not_comp hr 9 (by norm_num)
  zify [hp.one_le, hq.one_le, hr.one_le] at h hs ht hu
  apply core (p : ℤ) (q : ℤ) (r : ℤ) (x : ℤ) (y : ℤ) (z : ℤ) (s : ℤ) (t : ℤ) (u : ℤ)
    (by exact_mod_cast hp3') (by exact_mod_cast hpq) (by exact_mod_cast hqr) (by omega) (by omega)
    (by omega) hqc hr9 hxo hyo hzo (by linear_combination hs) (by linear_combination ht)
    (by linear_combination hu) (by linear_combination h)

theorem sol : OMA.R_oeis_a228947_R1.H2 := by
  intro m hm hcard
  have hm0 : m ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hm
    omega
  obtain ⟨p, q, r, hpq, hpr, hqr, hpqr⟩ := Finset.card_eq_three.mp hcard
  have hpm : p ∈ m.primeFactors := by rw [hpqr]; simp
  have hqm : q ∈ m.primeFactors := by rw [hpqr]; simp
  have hrm : r ∈ m.primeFactors := by rw [hpqr]; simp
  have hp := Nat.prime_of_mem_primeFactors hpm
  have hq := Nat.prime_of_mem_primeFactors hqm
  have hr := Nat.prime_of_mem_primeFactors hrm
  have hpd := Nat.dvd_of_mem_primeFactors hpm
  have hqd := Nat.dvd_of_mem_primeFactors hqm
  have hrd := Nat.dvd_of_mem_primeFactors hrm
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hpd
    obtain ⟨j, hj⟩ := hm
    omega
  have hq2 : q ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hqd
    obtain ⟨j, hj⟩ := hm
    omega
  have hr2 : r ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hrd
    obtain ⟨j, hj⟩ := hm
    omega
  have ha := hp.factorization_pos_of_dvd hm0 hpd
  have hb := hq.factorization_pos_of_dvd hm0 hqd
  have hc := hr.factorization_pos_of_dvd hm0 hrd
  have hfac := Nat.prod_factorization_pow_eq_self hm0
  rw [Finsupp.prod, Nat.support_factorization, hpqr, Finset.prod_insert (by simp [hpq, hpr]),
    Finset.prod_pair hqr] at hfac
  generalize m.factorization p = a at hfac ha
  generalize m.factorization q = b at hfac hb
  generalize m.factorization r = c at hfac hc
  have key : ∀ P Q R A B C : ℕ, P.Prime → Q.Prime → R.Prime → P ≠ 2 → P < Q → Q < R → 1 ≤ A →
      1 ≤ B → 1 ≤ C → m = P ^ A * Q ^ B * R ^ C →
      sigma 1 (m ^ 2) ≠ m ^ 2 + Nat.totient (m ^ 2) := by
    intro P Q R A B C hP hQ hR hP2 hPQ hQR hA hB hC hm'
    rw [hm']
    exact three_primes hP hQ hR hP2 hPQ hQR hA hB hC
  rcases lt_or_gt_of_ne hpq with h1 | h1 <;> rcases lt_or_gt_of_ne hpr with h2 | h2 <;>
    rcases lt_or_gt_of_ne hqr with h3 | h3
  · exact key p q r a b c hp hq hr hp2 h1 h3 ha hb hc (by rw [← hfac]; ring)
  · exact key p r q a c b hp hr hq hp2 h2 h3 ha hc hb (by rw [← hfac]; ring)
  · omega
  · exact key r p q c a b hr hp hq hr2 h2 h1 hc ha hb (by rw [← hfac]; ring)
  · exact key q p r b a c hq hp hr hq2 h1 h2 hb ha hc (by rw [← hfac]; ring)
  · omega
  · exact key q r p b c a hq hr hp hq2 h3 h2 hb hc ha (by rw [← hfac]; ring)
  · exact key r q p c b a hr hq hp hr2 h3 h1 hc hb ha (by rw [← hfac]; ring)

end OMA.P228947H2

theorem OMA.solution : OMA.R_oeis_a228947_R1.H2 := OMA.P228947H2.sol

