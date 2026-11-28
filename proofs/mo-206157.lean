import OMAStatements.S_mo_206157
import Mathlib

/-!
# MathOverflow 206157: `(p² - 1)/2^k` is never prime for a prime `p ≥ 13` and `1 ≤ k ≤ 4`

Only the fact that `p = 2j + 1` is odd with `j ≥ 6` is used. We have `p² - 1 = 4 j (j + 1)`.

* `k = 1, 2`: the quotient is `2 j (j + 1)` resp. `j (j + 1)`, visibly composite.
* `k = 3`: the quotient is the triangular number `j (j + 1)/2`, which is `s (2s + 1)` for
  `j = 2s` and `(2s + 1)(s + 1)` for `j = 2s + 1`.
* `k = 4`: writing `j = 4t + r`, the quotient `⌊j (j + 1)/4⌋` equals
  `t (4t + 1)`, `t (4t + 3)`, `(4t + 1)(t + 1)`, `(4t + 3)(t + 1)` for `r = 0, 1, 2, 3`.

In every case both factors are at least `2` because `j ≥ 6`.
-/

namespace OMA.MO206157

/-- `(2j + 1)² - 1 = 4 j (j + 1)`. -/
lemma sq_sub_one (j : ℕ) : (2 * j + 1) ^ 2 - 1 = 4 * (j * (j + 1)) := by
  have : (2 * j + 1) ^ 2 = 4 * (j * (j + 1)) + 1 := by ring
  omega

/-- The four cases, for odd `p = 2j + 1` with `j ≥ 6`. -/
lemma not_prime_quot (j : ℕ) (hj : 6 ≤ j) (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    ¬ (((2 * j + 1) ^ 2 - 1) / 2 ^ k).Prime := by
  rw [sq_sub_one]
  have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hk with rfl | rfl | rfl | rfl
  · -- quotient `2 · (j (j + 1))`
    have h : 4 * (j * (j + 1)) / 2 ^ 1 = 2 * (j * (j + 1)) := by
      apply Nat.div_eq_of_eq_mul_left (by norm_num)
      ring
    rw [h]
    exact Nat.not_prime_mul (by norm_num) (by nlinarith)
  · -- quotient `j · (j + 1)`
    have h : 4 * (j * (j + 1)) / 2 ^ 2 = j * (j + 1) := by
      apply Nat.div_eq_of_eq_mul_left (by norm_num)
      ring
    rw [h]
    exact Nat.not_prime_mul (by omega) (by omega)
  · -- quotient `j (j + 1) / 2`
    obtain ⟨s, rfl | rfl⟩ : ∃ s, j = 2 * s ∨ j = 2 * s + 1 := ⟨j / 2, by omega⟩
    · have h : 4 * (2 * s * (2 * s + 1)) / 2 ^ 3 = s * (2 * s + 1) := by
        apply Nat.div_eq_of_eq_mul_left (by norm_num)
        ring
      rw [h]
      exact Nat.not_prime_mul (by omega) (by omega)
    · have h : 4 * ((2 * s + 1) * (2 * s + 1 + 1)) / 2 ^ 3 = (2 * s + 1) * (s + 1) := by
        apply Nat.div_eq_of_eq_mul_left (by norm_num)
        ring
      rw [h]
      exact Nat.not_prime_mul (by omega) (by omega)
  · -- quotient `⌊j (j + 1) / 4⌋`
    obtain ⟨t, rfl | rfl | rfl | rfl⟩ :
        ∃ t, j = 4 * t ∨ j = 4 * t + 1 ∨ j = 4 * t + 2 ∨ j = 4 * t + 3 := ⟨j / 4, by omega⟩
    · have h : 4 * (4 * t * (4 * t + 1)) / 2 ^ 4 = t * (4 * t + 1) := by
        apply Nat.div_eq_of_eq_mul_left (by norm_num)
        ring
      rw [h]
      exact Nat.not_prime_mul (by omega) (by omega)
    · have h : 4 * ((4 * t + 1) * (4 * t + 1 + 1)) / 2 ^ 4 = t * (4 * t + 3) := by
        apply Nat.div_eq_of_lt_le
        · nlinarith
        · nlinarith
      rw [h]
      exact Nat.not_prime_mul (by omega) (by omega)
    · have h : 4 * ((4 * t + 2) * (4 * t + 2 + 1)) / 2 ^ 4 = (4 * t + 1) * (t + 1) := by
        apply Nat.div_eq_of_lt_le
        · nlinarith
        · nlinarith
      rw [h]
      exact Nat.not_prime_mul (by omega) (by omega)
    · have h : 4 * ((4 * t + 3) * (4 * t + 3 + 1)) / 2 ^ 4 = (4 * t + 3) * (t + 1) := by
        apply Nat.div_eq_of_eq_mul_left (by norm_num)
        ring
      rw [h]
      exact Nat.not_prime_mul (by omega) (by omega)

end OMA.MO206157

open OMA.MO206157 in
theorem OMA.solution : type_of% @OMA.S_mo_206157.main := by
  intro p hp hp13 k hk1 hk4
  obtain ⟨j, rfl⟩ : ∃ j, p = 2 * j + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact ⟨p / 2, by omega⟩
  exact not_prime_quot j (by omega) k hk1 hk4
