import OMAStatements.S_oeis_a191821
import Mathlib

-- Problem: oeis-a191821
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P191821
open OMA.S_oeis_a191821 PowerSeries

lemma cX (f : ℕ → ℚ) (k n : ℕ) : coeff n (mk f * X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [coeff_mul_X_pow']; simp

theorem sol : type_of% @OMA.S_oeis_a191821.main := by
  have l : mk (fun n => a (n + 1)) * (1 - 3 * X + 2 * X ^ 2) ^ 3 =
      mk (fun n => a (n + 1)) * X ^ 0 - C (9 : ℚ) * (mk (fun n => a (n + 1)) * X ^ 1)
      + C (33 : ℚ) * (mk (fun n => a (n + 1)) * X ^ 2) - C (63 : ℚ) * (mk (fun n => a (n + 1)) * X ^ 3)
      + C (66 : ℚ) * (mk (fun n => a (n + 1)) * X ^ 4) - C (36 : ℚ) * (mk (fun n => a (n + 1)) * X ^ 5)
      + C (8 : ℚ) * (mk (fun n => a (n + 1)) * X ^ 6) := by
    simp only [map_ofNat]; ring
  have r : -(2 * (-1 + 6 * X - 19 * X ^ 2 + 31 * X ^ 3 - 22 * X ^ 4 + 4 * (X : PowerSeries ℚ) ^ 5)) =
      C (2 : ℚ) * X ^ 0 - C (12 : ℚ) * X ^ 1 + C (38 : ℚ) * X ^ 2 - C (62 : ℚ) * X ^ 3
      + C (44 : ℚ) * X ^ 4 - C (8 : ℚ) * X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [l, r]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, cX, coeff_X_pow]
  rcases n with _ | _ | _ | _ | _ | _ | n
  all_goals simp [a]
  all_goals norm_num
  all_goals (simp only [pow_succ]; ring)

end OMA.P191821

theorem OMA.solution : type_of% @OMA.S_oeis_a191821.main := OMA.P191821.sol
