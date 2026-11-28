import OMAStatements.S_oeis_a101917
import Mathlib

open PowerSeries OMA.S_oeis_a101917 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a101917.main) := fun h => by
  have := congrArg (coeff 57) h
  simp [mul_add, series, coeff_mul_X_pow', coeff_succ_mul_X, coeff_X_pow] at this
  revert this
  decide +kernel
