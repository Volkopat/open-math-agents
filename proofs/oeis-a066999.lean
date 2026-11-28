import OMAStatements.S_oeis_a066999
import Mathlib

-- Credit: @ivillar (recurrence a(n+1) = 3a(n) + (n+1)^3 and Kotesovec's closed form)

open PowerSeries OMA.S_oeis_a066999 in
theorem OMA.solution : type_of% @OMA.S_oeis_a066999.main := by
  have e (n : ℕ) : a n = (11 * 3 ^ (n + 1) - 4 * n ^ 3 - 18 * n ^ 2 - 36 * n - 33) / 8 := by
    induction n with
    | zero => norm_num [a]
    | succ n ih =>
      have : a (n + 1) = 3 * a n + ((n : ℚ) + 1) ^ 3 := by
        unfold a
        rw [Finset.sum_Icc_succ_top (by omega), pow_succ (3 : ℚ) n]
        push_cast
        field_simp
      rw [this, ih]
      push_cast
      ring
  ring_nf
  ext n
  rcases n with _ | _ | _ | _ | _ | _ | n <;> simp [coeff_mul_X_pow', coeff_X_pow, coeff_X, ← map_ofNat C, coeff_mul_C, coeff_succ_mul_X, e] <;> ring
