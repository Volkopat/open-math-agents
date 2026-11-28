import OMAStatements.S_oeis_a007392
import Mathlib

/-!
# A007392: recurrence (from `n = 13`) and generating function

The recurrence operator factors as `(1 - S² - S⁵)(1 - S²)²`, where `S` is the shift.

* `e` is annihilated by `1 - S² - S⁵` from index `9` on, so applying `(1 - S²)²` needs the three
  instances at `n`, `n - 2`, `n - 4`, i.e. `n ≥ 13`.
* `b` is `n` on odd and `2` on even indices (from `2` on), which `(1 - S²)²` annihilates.

The generating-function identity is the same statement read coefficientwise: the coefficients of
`A · D` are `-(recurrence defect)`, which vanish for `n ≥ 13`, and the thirteen coefficients
`n = 0, …, 12` are checked directly.
-/

namespace OMA.S_oeis_a007392

/-- From index `2` on, `b` has vanishing second difference in steps of two. -/
lemma b_step (j : ℕ) (hj : 2 ≤ j) : b (j + 4) = 2 * b (j + 2) - b j := by
  unfold b
  split_ifs <;> omega

/-- The defining recurrence of `e`. -/
lemma e_step (m : ℕ) : e (m + 9) = e (m + 7) + e (m + 4) := by
  rw [e]

/-- The recurrence in shifted form. -/
lemma rec_shift (k : ℕ) : a (k + 13) =
    3 * a (k + 11) - 3 * a (k + 9) + a (k + 8) + a (k + 7) - 2 * a (k + 6) + a (k + 4) := by
  have e1 : e (k + 13) = e (k + 11) + e (k + 8) := e_step (k + 4)
  have e2 : e (k + 11) = e (k + 9) + e (k + 6) := e_step (k + 2)
  have e3 : e (k + 9) = e (k + 7) + e (k + 4) := e_step k
  have b1 : b (k + 13) = 2 * b (k + 11) - b (k + 9) := b_step (k + 9) (by omega)
  have b2 : b (k + 11) = 2 * b (k + 9) - b (k + 7) := b_step (k + 7) (by omega)
  have b3 : b (k + 8) = 2 * b (k + 6) - b (k + 4) := b_step (k + 4) (by omega)
  unfold a
  linarith

end OMA.S_oeis_a007392

open OMA.S_oeis_a007392 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a007392.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 13 := ⟨n - 13, by omega⟩
    exact rec_shift k
  · have el : ∀ S : PowerSeries ℤ, S * ((X ^ 5 + X ^ 2 - 1) * (X - 1) ^ 2 * (1 + X) ^ 2) =
        C (-1) * (S * X ^ 0) + C 3 * (S * X ^ 2) + C (-3) * (S * X ^ 4) + C 1 * (S * X ^ 5) +
          C 1 * (S * X ^ 6) + C (-2) * (S * X ^ 7) + C 1 * (S * X ^ 9) := by
      intro S
      simp only [map_neg, map_one, map_ofNat]
      ring
    have er : (X ^ 10 * (-5 + 3 * X ^ 2) : PowerSeries ℤ) = X ^ 10 * C (-5) + X ^ 12 * C 3 := by
      simp only [map_neg, map_ofNat]
      ring
    rw [el, er]
    ext n
    simp only [map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, coeff_mk]
    by_cases hn : n < 13
    · interval_cases n <;> decide
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 13 := ⟨n - 13, by omega⟩
      have h := rec_shift k
      simp
      linarith
