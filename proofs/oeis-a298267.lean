import OMAStatements.S_oeis_a298267
import Mathlib

open OMA.S_oeis_a298267 PowerSeries

theorem P298267.rec (m : ℕ) :
    a (m + 9) - 2 * a (m + 8) + a (m + 7) - a (m + 2) + 2 * a (m + 1) - a m = 0 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 7 ∧ m = 7 * q + r :=
    ⟨m / 7, m % 7, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 7).symm⟩
  simp only [a]
  interval_cases r <;> (push_cast; ring_nf; generalize (q : ℤ) ^ 2 = Q; omega)

theorem OMA.solution : type_of% @OMA.S_oeis_a298267.main := by
  refine ⟨?_, ?_⟩
  · have hL : (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X) ^ 3 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) : PowerSeries ℚ) = PowerSeries.mk (fun n => (a n : ℚ)) - C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1) + (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) - (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 7) + C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 8) - (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 9) := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    have hR : (X * (1 + X) * (3 - 2 * X + 4 * X ^ 2 - 2 * X ^ 3 + 3 * X ^ 4) : PowerSeries ℚ) = C (3 : ℚ) * X ^ 1 + X ^ 2 + C (2 : ℚ) * X ^ 3 + C (2 : ℚ) * X ^ 4 + X ^ 5 + C (3 : ℚ) * X ^ 6 := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
      coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · simp only [show n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 10 by omega]
      simp only [show n + 10 - 1 = n + 9 by omega, show n + 10 - 2 = n + 8 by omega, show n + 10 - 3 = n + 7 by omega, show n + 10 - 4 = n + 6 by omega, show n + 10 - 5 = n + 5 by omega, show n + 10 - 6 = n + 4 by omega, show n + 10 - 7 = n + 3 by omega, show n + 10 - 8 = n + 2 by omega, show n + 10 - 9 = n + 1 by omega]
      simp only [show (n + 10 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 10 = 1) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 10 = 2) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 10 = 3) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 10 = 4) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 10 = 5) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 10 = 6) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 10 = 7) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 10 = 8) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 10 = 9) = False by simp only [eq_iff_iff, iff_false]; omega, if_false]
      have h : ((a (n + 10) - 2 * a (n + 9) + a (n + 8) - a (n + 3) + 2 * a (n + 2) - a (n + 1) : ℤ) : ℚ) = 0 := by
        exact_mod_cast P298267.rec (n + 1)
      push_cast at h
      norm_num
      linarith [h]
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    rw [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega, show m + 9 - 7 = m + 2 by omega,
      show m + 9 - 8 = m + 1 by omega, show m + 9 - 9 = m by omega]
    linarith [P298267.rec m]
