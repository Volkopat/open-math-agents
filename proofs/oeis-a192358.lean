import OMAStatements.S_oeis_a192358

-- OEIS A192358: proof of Colin Barker's fourth-order recurrence.
-- Both X + 3 and X - 3 satisfy the quartic (t^2 - 7t + 11)(t^2 + 5t + 5) = 0
-- modulo X^2 - X - 1, so the linear combination of p(k+4), ..., p(k) is divisible
-- by X^2 - X - 1; taking coeff 1 after reduction yields the recurrence.
open Polynomial OMA.S_oeis_a192358

theorem OMA.solution : type_of% @OMA.S_oeis_a192358.main := by
  rintro (_|_|_|_|_|k) _ <;> try omega
  have h n : a n = lcoeff ℚ 1 (modByMonicHom _ (p (n - 1))) := rfl
  simp only [h, ← smul_eq_mul, ← map_smul, ← map_add, ← map_sub]
  congr 1
  exact modByMonic_eq_of_dvd_sub (by monicity!)
    ⟨C (1 / 2) * ((X + 3) ^ k * (X ^ 2 + 11 * X + 29) + (X - 3) ^ k * (X ^ 2 - 13 * X + 41)), by
      simp [p, smul_eq_C_mul, map_ofNat]; ring⟩
