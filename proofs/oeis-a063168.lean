import OMAStatements.S_oeis_a063168
import Mathlib

/-!
# A063168: recurrence and generating function of `0, 7, 36, 66, 96, …`

For `n ≥ 2` the sequence is the linear function `30 n - 24`, so its second difference vanishes
from `n = 4` on.  For the generating function, `(1 - X)²` takes second differences: the
coefficient of `X ^ n` in `A (1 - X)²` is `a n - 2 a (n - 1) + a (n - 2)`, which is
`0, 7, 22, 1` for `n = 0, 1, 2, 3` and `0` afterwards.
-/

open OMA.S_oeis_a063168 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a063168.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have e1 : m + 4 - 1 = m + 3 := by omega
    have e2 : m + 4 - 2 = m + 2 := by omega
    rw [e1, e2]
    unfold a
    split_ifs <;> first | omega | (push_cast; ring)
  · have el : ∀ S : PowerSeries ℚ, S * (1 - X) ^ 2 = S * X ^ 0 - C 2 * (S * X ^ 1) + S * X ^ 2 := by
      intro S
      simp only [map_ofNat]
      ring
    have er : (X * (X ^ 2 + 22 * X + 7) : PowerSeries ℚ) = X ^ 3 + X ^ 2 * C 22 + X ^ 1 * C 7 := by
      simp only [map_ofNat]
      ring
    rw [el, er]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, coeff_mk]
    rcases n with _ | _ | _ | _ | n
    · simp [a]
    · simp [a]
    · simp [a]
      norm_num
    · simp [a]
      norm_num
    · have h1 : n + 4 - 0 = n + 4 := rfl
      have h2 : n + 4 - 1 = n + 3 := rfl
      have h3 : n + 4 - 2 = n + 2 := rfl
      rw [h1, h2, h3]
      simp [a]
      ring
