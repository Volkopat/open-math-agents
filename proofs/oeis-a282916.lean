import OMAStatements.S_oeis_a282916
import Mathlib

open OMA.S_oeis_a282916 (a)
open PowerSeries

private theorem incompatible (f : ℕ → ℤ)
    (recurrence : f 10 = 100 * f 8 + f 6 - 100 * f 4)
    (series : PowerSeries.mk f *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + X ^ 2)) =
      1 + 1099 * X ^ 4 + 100000 * X ^ 5 - 1098900 * X ^ 6 - 10000000 * X ^ 10) : False := by
  let S := PowerSeries.mk f
  have expanded :
      S - (100 : ℕ) • (S * X^2) - S * X^4 + (100 : ℕ) • (S * X^6) =
      1 + (1099 : ℕ) • X^4 + (100000 : ℕ) • X^5 - (1098900 : ℕ) • X^6 -
        (10000000 : ℕ) • X^10 := by
    simp only [nsmul_eq_mul]
    change S * _ = _ at series
    linear_combination series
  have coeffTen := congrArg (coeff (R := ℤ) 10) expanded
  simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_X_pow, coeff_one, S, coeff_mk] at coeffTen
  norm_num at coeffTen
  omega

/-- The recurrence forces the degree-ten coefficient of the numerator to vanish. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282916.main) := by
  rintro ⟨recurrence, series⟩
  exact incompatible (fun n => (a n : ℤ)) (recurrence 10 (by decide)) series
