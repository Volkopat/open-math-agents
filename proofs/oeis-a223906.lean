import OMAStatements.S_oeis_a223906
import Mathlib

-- Proof of Colin Barker's conjecture in OEIS A223906 (statement by @ivillar).
-- Idea: the unsigned Stirling numbers of row 3 are 0, 2, 3, 1, so a(n) = 2*2^n + 3*3^n + 4^n;
-- the generating function is then checked coefficientwise after multiplying by its denominator.

namespace OMAA223906Helpers

open PowerSeries OMA.S_oeis_a223906

theorem a_eq (n : ℕ) : a n = 2 ^ (1 + n) + 3 ^ (1 + n) + 4 ^ n := by
  norm_num [a, hatC, Finset.sum_range_succ, Nat.stirlingFirst, zpow_neg, div_inv_eq_mul, pow_add]

def g (n : ℕ) : ℚ := if n = 0 then 0 else 2 ^ (1 + n) + 3 ^ (1 + n) + 4 ^ n

theorem key : mk g * ((2 * X - 1) * (3 * X - 1) * (4 * X - 1)) =
    (-X * (144 * X ^ 2 - 102 * X + 17) : ℚ⟦X⟧) := by
  have e1 : mk g * ((2 * X - 1) * (3 * X - 1) * (4 * X - 1)) =
      C (24 : ℚ) * (mk g * X ^ 3) - C (26 : ℚ) * (mk g * X ^ 2) + C (9 : ℚ) * (mk g * X ^ 1) -
        mk g := by
    simp only [map_ofNat]
    ring
  have e2 : (-X * (144 * X ^ 2 - 102 * X + 17) : ℚ⟦X⟧) =
      C (102 : ℚ) * X ^ 2 - C (144 : ℚ) * X ^ 3 - C (17 : ℚ) * X ^ 1 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mk, coeff_mul_X_pow', coeff_C]
  rcases n with _ | _ | _ | _ | n <;> simp [g] <;> norm_num
  ring

end OMAA223906Helpers

open OMAA223906Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a223906.main := by
  refine ⟨fun n _ => a_eq n, ?_⟩
  simp only [a_eq]
  exact (PowerSeries.eq_mul_inv_iff_mul_eq (by simp)).2 key
