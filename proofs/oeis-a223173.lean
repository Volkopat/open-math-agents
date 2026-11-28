import OMAStatements.S_oeis_a223173
import Mathlib

/-!
Credit: @ivillar
Proof: Stirling1(3,k) = 0, 2, -3, 1 for k = 0..3, so a(n) = 2*2^n - 3*3^n + 4^n (this also gives
a(0) = 0); the denominator (1-2x)(1-3x)(1-4x) annihilates each geometric part from n = 3 on, and
the first coefficients are checked directly (Robert Israel verified the conjecture in the OEIS).
-/

namespace OMAA223173Helpers
open PowerSeries OMA.S_oeis_a223173

def f (n : ℕ) : ℤ := 2 ^ (1 + n) - 3 ^ (1 + n) + 4 ^ n

theorem a_eq (n : ℕ) : a n = f n := by
  have s0 : stirling1 3 0 = 0 := by decide
  have s1 : stirling1 3 1 = 2 := by decide
  have s2 : stirling1 3 2 = -3 := by decide
  have s3 : stirling1 3 3 = 1 := by decide
  simp only [a, Finset.sum_range_succ, Finset.sum_range_zero, s0, s1, s2, s3]
  unfold f
  push_cast
  ring

theorem series_eq : (fun n => if n = 0 then 0 else a n) = f := by
  funext n
  split_ifs with h
  · subst h; decide
  · exact a_eq n

theorem coeff_mk_mul_X_pow (n k : ℕ) :
    coeff n (PowerSeries.mk f * X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem coeff_mk_mul_C_X_pow (r : ℤ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * (if k ≤ n then f (n - k) else 0) := by
  rw [mul_left_comm, coeff_C_mul, coeff_mk_mul_X_pow]

theorem coeff_at (n k j : ℕ) (h : n = j + k) : coeff n (PowerSeries.mk f * X ^ k) = f j := by
  rw [coeff_mk_mul_X_pow, if_pos (by omega), show n - k = j by omega]

theorem coeff_at_C (r : ℤ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * f j := by
  rw [mul_left_comm, coeff_C_mul, coeff_at n k j h]

end OMAA223173Helpers

open PowerSeries OMAA223173Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a223173.main := by
  refine ⟨fun n _ => a_eq n, ?_⟩
  rw [series_eq]
  ext n
  have hD : ((2 * X - 1) * (3 * X - 1) * (4 * X - 1) : PowerSeries ℤ) =
      C 24 * X ^ 3 - C 26 * X ^ 2 + C 9 * X ^ 1 - X ^ 0 := by
    rw [map_ofNat C 24, map_ofNat C 26, map_ofNat C 9]; ring
  have hN : (-X * (6 * X - 1) : PowerSeries ℤ) = X ^ 1 - C 6 * X ^ 2 := by
    rw [map_ofNat C 6]; ring
  rw [hD, hN]
  rcases Nat.lt_or_ge n 3 with h | h
  · simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
      coeff_C_mul, coeff_X_pow]
    interval_cases n <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    simp only [mul_add, mul_sub, map_add, map_sub]
    rw [coeff_at_C 24 (m + 3) 3 m (by omega), coeff_at_C 26 (m + 3) 2 (m + 1) (by omega),
      coeff_at_C 9 (m + 3) 1 (m + 2) (by omega), coeff_at (m + 3) 0 (m + 3) (by omega),
      coeff_C_mul, coeff_X_pow, coeff_X_pow, if_neg (by omega), if_neg (by omega)]
    unfold f
    ring
