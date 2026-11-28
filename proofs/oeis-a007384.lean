import OMAStatements.S_oeis_a007384
import Mathlib

/-!
# A007384: recurrence and generating function

The recurrence operator factors as `(1 - S² - S⁵)(1 - S²)²`, where `S` is the shift.

* `c` is annihilated by `1 - S² - S⁵` (its defining recurrence).
* `b` is `1` on odd indices and `n/2 + 1` on even ones, which `(1 - S²)²` annihilates.

Hence `a(n) = c(n + 6) - b(n)` satisfies the recurrence from `n = 9` on.  The generating-function
identity is the same statement read coefficientwise: the coefficients of `A · D` are minus the
recurrence defect, which vanishes for `n ≥ 9`, and the nine coefficients `n = 0, …, 8` are
checked directly.
-/

namespace OMA.S_oeis_a007384

/-- `b` has vanishing second difference in steps of two. -/
lemma b_step (j : ℕ) : b (j + 4) = 2 * b (j + 2) - b j := by
  unfold b
  split_ifs <;> omega

/-- The defining recurrence of `c`. -/
lemma c_step (m : ℕ) : c (m + 5) = c (m + 3) + c m := by
  rw [c]

/-- The recurrence in shifted form. -/
lemma rec_shift (k : ℕ) : a (k + 9) =
    3 * a (k + 7) - 3 * a (k + 5) + a (k + 4) + a (k + 3) - 2 * a (k + 2) + a k := by
  have c1 : c (k + 15) = c (k + 13) + c (k + 10) := c_step (k + 10)
  have c2 : c (k + 13) = c (k + 11) + c (k + 8) := c_step (k + 8)
  have c3 : c (k + 11) = c (k + 9) + c (k + 6) := c_step (k + 6)
  have b1 : b (k + 9) = 2 * b (k + 7) - b (k + 5) := b_step (k + 5)
  have b2 : b (k + 7) = 2 * b (k + 5) - b (k + 3) := b_step (k + 3)
  have b3 : b (k + 4) = 2 * b (k + 2) - b k := b_step k
  have a9 : a (k + 9) = c (k + 15) - b (k + 9) := rfl
  have a7 : a (k + 7) = c (k + 13) - b (k + 7) := rfl
  have a5 : a (k + 5) = c (k + 11) - b (k + 5) := rfl
  have a4 : a (k + 4) = c (k + 10) - b (k + 4) := rfl
  have a3 : a (k + 3) = c (k + 9) - b (k + 3) := rfl
  have a2 : a (k + 2) = c (k + 8) - b (k + 2) := rfl
  have a0 : a k = c (k + 6) - b k := rfl
  linarith

end OMA.S_oeis_a007384

open OMA.S_oeis_a007384 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a007384.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    exact rec_shift k
  · have el : ∀ S : PowerSeries ℤ, S * ((X ^ 5 + X ^ 2 - 1) * (X - 1) ^ 2 * (1 + X) ^ 2) =
        C (-1) * (S * X ^ 0) + C 3 * (S * X ^ 2) + C (-3) * (S * X ^ 4) + C 1 * (S * X ^ 5) +
          C 1 * (S * X ^ 6) + C (-2) * (S * X ^ 7) + C 1 * (S * X ^ 9) := by
      intro S
      simp only [map_neg, map_one, map_ofNat]
      ring
    have er : (-(X ^ 5 : PowerSeries ℤ)) = X ^ 5 * C (-1) := by
      simp only [map_neg, map_one]
      ring
    rw [el, er]
    ext n
    simp only [map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, coeff_mk]
    by_cases hn : n < 9
    · interval_cases n <;> decide
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
      have h := rec_shift k
      simp
      linarith
