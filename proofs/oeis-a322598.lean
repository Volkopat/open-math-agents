import OMAStatements.S_oeis_a322598
import Mathlib

open OMA.S_oeis_a322598 PowerSeries

theorem P322598.rec (m : ℕ) :
    a (m + 7) - a (m + 6) - a (m + 5) + a (m + 3) + a (m + 2) - a (m + 1) = 0 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 6 ∧ m = 6 * q + r :=
    ⟨m / 6, m % 6, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 6).symm⟩
  simp only [a]
  interval_cases r <;> (push_cast; ring_nf; generalize (q : ℤ) ^ 2 = Q; omega)

theorem OMA.solution : type_of% @OMA.S_oeis_a322598.main := by
  refine ⟨?_, ?_⟩
  · have hL : (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) * (1 + X + X ^ 2)) : PowerSeries ℚ) = PowerSeries.mk (fun n => (a n : ℚ)) - (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1) - (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) + (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4) + (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5) - (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 6) := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    have hR : (X * (1 + 2 * X + 4 * X ^ 2 + 2 * X ^ 3) : PowerSeries ℚ) = X ^ 1 + C (2 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 3 + C (2 : ℚ) * X ^ 4 := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
      coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    rcases n with _ | _ | _ | _ | _ | _ | _ | n
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · norm_num [a]
    · simp only [show n + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 7 by omega]
      simp only [show n + 7 - 1 = n + 6 by omega, show n + 7 - 2 = n + 5 by omega, show n + 7 - 3 = n + 4 by omega, show n + 7 - 4 = n + 3 by omega, show n + 7 - 5 = n + 2 by omega, show n + 7 - 6 = n + 1 by omega]
      have h : ((a (n + 7) - a (n + 6) - a (n + 5) + a (n + 3) + a (n + 2) - a (n + 1) : ℤ) : ℚ) = 0 := by
        exact_mod_cast P322598.rec n
      push_cast at h
      simp only [show (n + 7 = 1) = False by simp only [eq_iff_iff, iff_false]; omega, if_false]
      norm_num
      linarith [h]
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega]
    linarith [P322598.rec m]
