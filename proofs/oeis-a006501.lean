import OMAStatements.S_oeis_a006501
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a006501.main := by
  intro n
  have h : OMA.S_oeis_a006501.seriesA = (1 + X ^ 2) * OMA.S_oeis_a006501.seriesB := by
    simp only [OMA.S_oeis_a006501.seriesA, OMA.S_oeis_a006501.seriesB]
    congr 1
    congr 1
    ring
  rw [h, add_mul, one_mul, map_add, PowerSeries.coeff_X_pow_mul']
