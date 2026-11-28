import OMAStatements.S_oeis_a002414
import Mathlib

open PowerSeries OMA.S_oeis_a002414 in
theorem OMA.solution : type_of% @OMA.S_oeis_a002414.main := by
  ring_nf
  ext n
  rcases n with _ | _ | _ | _ | _ | n <;> simp [coeff_mul_X_pow', coeff_X_pow, coeff_X, ← map_ofNat C, coeff_mul_C, coeff_succ_mul_X, a] <;> ring
