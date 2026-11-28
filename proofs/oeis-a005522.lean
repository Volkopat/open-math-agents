import OMAStatements.S_oeis_a005522
import Mathlib

open OMA.S_oeis_a005522 PowerSeries

noncomputable def P005522.f (m : ℕ) : ℚ := (Nat.fib (2 * m + 1) : ℚ)

theorem P005522.hF (m : ℕ) : P005522.f (m + 2) = 3 * P005522.f (m + 1) - P005522.f m := by
  unfold P005522.f
  have e1 : Nat.fib (2 * (m + 2) + 1) = Nat.fib (2 * m + 4) + Nat.fib (2 * m + 3) := by
    rw [show 2 * (m + 2) + 1 = 2 * m + 3 + 2 by ring, Nat.fib_add_two]; ring_nf
  have e2 : Nat.fib (2 * m + 4) = Nat.fib (2 * m + 3) + Nat.fib (2 * m + 2) := by
    rw [show 2 * m + 4 = 2 * m + 2 + 2 by ring, Nat.fib_add_two]; ring_nf
  have e3 : Nat.fib (2 * m + 3) = Nat.fib (2 * m + 2) + Nat.fib (2 * m + 1) := by
    rw [show 2 * m + 3 = 2 * m + 1 + 2 by ring, Nat.fib_add_two]; ring_nf
  rw [e1, show 2 * (m + 1) + 1 = 2 * m + 3 by ring]
  push_cast
  rw [e2, e3]
  push_cast
  ring

theorem P005522.hl (m : ℕ) : (lucas (m + 2) : ℚ) = lucas (m + 1) + lucas m := by
  rw [show lucas (m + 2) = lucas (m + 1) + lucas m from rfl]
  push_cast
  ring

theorem P005522.hb (j : ℕ) : (a (j + 1) : ℚ) = 1 + lucas (j + 1) + P005522.f j := by
  simp only [a, P005522.f, show j + 1 ≠ 0 by omega, if_false, show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
  push_cast
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a005522.main := by
  have hL : (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * ((X - 1) * (X ^ 2 - 3 * X + 1) * (X ^ 2 + X - 1)) : PowerSeries ℚ) = PowerSeries.mk (fun n => (a (n + 1) : ℚ)) - C (5 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (7 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) - (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) - C (3 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4) + (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 5) := by
    (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
  have hR : (-(-3 + 9 * X - X ^ 2 - 10 * X ^ 3 + 4 * X ^ 4) : PowerSeries ℚ) = C (3 : ℚ) - C (9 : ℚ) * X ^ 1 + X ^ 2 + C (10 : ℚ) * X ^ 3 - C (4 : ℚ) * X ^ 4 := by
    (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
  rw [hL, hR]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
    coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
  rcases n with _ | _ | _ | _ | _ | _ | n
  · norm_num [a, lucas]
  · norm_num [a, lucas]
  · norm_num [a, lucas]
  · norm_num [a, lucas]
  · norm_num [a, lucas]
  · norm_num [a, lucas]
  · simp only [show n + 1 + 1 + 1 + 1 + 1 + 1 = n + 6 by omega]
    simp only [show n + 6 - 1 = n + 5 by omega, show n + 6 - 2 = n + 4 by omega, show n + 6 - 3 = n + 3 by omega, show n + 6 - 4 = n + 2 by omega, show n + 6 - 5 = n + 1 by omega]
    try simp only [show (n + 6 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 6 = 1) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 6 = 2) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 6 = 3) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 6 = 4) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 6 = 5) = False by simp only [eq_iff_iff, iff_false]; omega, if_false]
    try simp only [show 1 ≤ n + 6 by omega, show 2 ≤ n + 6 by omega, show 3 ≤ n + 6 by omega, show 4 ≤ n + 6 by omega, show 5 ≤ n + 6 by omega, if_true]
    simp only [P005522.hb]
    have l6 : (lucas (n + 6 + 1) : ℚ) = lucas (n + 5 + 1) + lucas (n + 4 + 1) := P005522.hl (n + 4 + 1)
    have l5 : (lucas (n + 5 + 1) : ℚ) = lucas (n + 4 + 1) + lucas (n + 3 + 1) := P005522.hl (n + 3 + 1)
    have l4 : (lucas (n + 4 + 1) : ℚ) = lucas (n + 3 + 1) + lucas (n + 2 + 1) := P005522.hl (n + 2 + 1)
    have l3 : (lucas (n + 3 + 1) : ℚ) = lucas (n + 2 + 1) + lucas (n + 1 + 1) := P005522.hl (n + 1 + 1)
    have f6 : P005522.f (n + 6) = 3 * P005522.f (n + 5) - P005522.f (n + 4) := P005522.hF (n + 4)
    have f5 : P005522.f (n + 5) = 3 * P005522.f (n + 4) - P005522.f (n + 3) := P005522.hF (n + 3)
    have f4 : P005522.f (n + 4) = 3 * P005522.f (n + 3) - P005522.f (n + 2) := P005522.hF (n + 2)
    have f3 : P005522.f (n + 3) = 3 * P005522.f (n + 2) - P005522.f (n + 1) := P005522.hF (n + 1)
    rw [l6, l5, l4, l3, f6, f5, f4, f3]
    ring_nf
    simp
