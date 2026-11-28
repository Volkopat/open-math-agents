import OMAStatements.S_oeis_a283355

/-!
The recurrence in OEIS A283355 is stated for n > 5. At n = 7 it forces
the coefficient of the numerator to vanish, whereas the stated numerator
has coefficient 100 there. Source: https://oeis.org/A283355.
-/

open PowerSeries
open OMA.S_oeis_a283355 (a)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a283355.main) := by
  intro h
  have hden : (1 - X) * (1 - 10 * X) * (1 + 10 * X) =
      (1 - X ^ 1 - C 100 * X ^ 2 + C 100 * X ^ 3 : PowerSeries ℤ) := by
    simp only [map_ofNat, pow_one]
    ring
  have hnum : (1 + 9 * X - 10 * X ^ 2 + 11 * X ^ 3 - 10 * X ^ 4 +
      9 * X ^ 5 + 100 * X ^ 7 : PowerSeries ℤ) =
      1 + C 9 * X ^ 1 - C 10 * X ^ 2 + C 11 * X ^ 3 - C 10 * X ^ 4 +
        C 9 * X ^ 5 + C 100 * X ^ 7 := by
    simp only [map_ofNat, pow_one]
  have hc := congrArg (coeff (R := ℤ) 7) h.1
  rw [hden, hnum, mul_comm (mk a)] at hc
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk, coeff_one, coeff_X_pow] at hc
  norm_num at hc
  have hr := h.2.2 7 (by decide)
  norm_num at hr
  omega
