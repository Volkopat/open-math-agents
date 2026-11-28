import OMAStatements.S_oeis_a114698
import Mathlib

/-!
# A114698: generating function and recurrence of `1, 18, 38, 58, …`

For `n ≥ 2` the sequence is the linear function `20 n - 22`.  Multiplying the generating
function of `a (k + 1)` by `(1 - X)²` takes second differences, which are `1, 16, 3` for
`k = 0, 1, 2` and `0` afterwards; the recurrence for `k ≥ 3` is the same vanishing second
difference.
-/

open OMA.S_oeis_a114698 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a114698.main := by
  refine ⟨?_, ?_⟩
  · have el : ∀ S : PowerSeries ℚ, S * (1 - X) ^ 2 = S * X ^ 0 - C 2 * (S * X ^ 1) + S * X ^ 2 := by
      intro S
      simp only [map_ofNat]
      ring
    have er : (1 + 16 * X + 3 * X ^ 2 : PowerSeries ℚ) = X ^ 0 + X ^ 1 * C 16 + X ^ 2 * C 3 := by
      simp only [map_ofNat]
      ring
    rw [el, er]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, coeff_mk]
    rcases n with _ | _ | _ | n
    · simp [a]
    · simp [a]
      norm_num
    · simp [a]
      norm_num
    · have h1 : n + 3 - 0 = n + 3 := rfl
      have h2 : n + 3 - 1 = n + 2 := rfl
      have h3 : n + 3 - 2 = n + 1 := rfl
      rw [h1, h2, h3]
      simp [a]
      ring
  · intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    have e1 : m + 3 - 1 = m + 2 := by omega
    rw [e1]
    unfold a
    split_ifs <;> first | omega | (push_cast; ring)
