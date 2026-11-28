import OMAStatements.S_oeis_a329178
import Mathlib.Tactic

open OMA.S_oeis_a329178
open PowerSeries

private def productAt (n : ℕ) : ℤ := padovan (n + 5) * padovan (n + 7)

private theorem product_recurrence (n : ℕ) :
    productAt (n + 6) - productAt (n + 5) - productAt (n + 4) - productAt (n + 3) +
      productAt (n + 2) - productAt (n + 1) + productAt n = 0 := by
  have step (k : ℕ) : padovan (k + 3) = padovan (k + 1) + padovan k := by
    rw [padovan]
  have h8 : padovan (n + 8) = padovan (n + 6) + padovan (n + 5) := step (n + 5)
  have h9 : padovan (n + 9) = padovan (n + 7) + padovan (n + 6) := step (n + 6)
  have h10 : padovan (n + 10) = padovan (n + 8) + padovan (n + 7) := step (n + 7)
  have h11 : padovan (n + 11) = padovan (n + 9) + padovan (n + 8) := step (n + 8)
  have h12 : padovan (n + 12) = padovan (n + 10) + padovan (n + 9) := step (n + 9)
  have h13 : padovan (n + 13) = padovan (n + 11) + padovan (n + 10) := step (n + 10)
  change padovan (n + 11) * padovan (n + 13) -
    padovan (n + 10) * padovan (n + 12) - padovan (n + 9) * padovan (n + 11) -
    padovan (n + 8) * padovan (n + 10) + padovan (n + 7) * padovan (n + 9) -
    padovan (n + 6) * padovan (n + 8) + padovan (n + 5) * padovan (n + 7) = 0
  rw [h13, h12, h11, h10, h9, h8]
  ring

private theorem sum_succ (n : ℕ) : a (n + 1) = a n + productAt (n + 1) := by
  unfold a productAt
  rw [Finset.sum_range_succ]

private theorem shifted_recurrence (n : ℕ) :
    a (n + 7) - 2 * a (n + 6) + 2 * a (n + 3) - 2 * a (n + 2) + 2 * a (n + 1) - a n = 0 := by
  have h := product_recurrence (n + 1)
  have h0 := sum_succ n
  have h1 := sum_succ (n + 1)
  have h2 := sum_succ (n + 2)
  have h3 := sum_succ (n + 3)
  have h4 := sum_succ (n + 4)
  have h5 := sum_succ (n + 5)
  have h6 := sum_succ (n + 6)
  linear_combination h + h6 - h5 - h4 - h3 + h2 - h1 + h0

private theorem recurrence (n : ℕ) (hn : 6 < n) :
    a n = 2 * a (n - 1) - 2 * a (n - 4) + 2 * a (n - 5) - 2 * a (n - 6) + a (n - 7) := by
  have h := shifted_recurrence (n - 7)
  rw [show n - 7 + 7 = n by omega, show n - 7 + 6 = n - 1 by omega,
    show n - 7 + 3 = n - 4 by omega, show n - 7 + 2 = n - 5 by omega,
    show n - 7 + 1 = n - 6 by omega] at h
  linarith only [h]

private theorem generating_function :
    let x := (PowerSeries.X : PowerSeries ℤ)
    ((1 - x) * (1 - 2 * x + x ^ 2 - x ^ 3) * (1 + x - x ^ 3)) * PowerSeries.mk a =
      1 + x - x ^ 2 + x ^ 3 - x ^ 4 := by
  dsimp only
  let x : PowerSeries ℤ := PowerSeries.X
  change ((1 - x) * (1 - 2 * x + x ^ 2 - x ^ 3) * (1 + x - x ^ 3)) * mk a =
    1 + x - x ^ 2 + x ^ 3 - x ^ 4
  have denominator : (1 - x) * (1 - 2 * x + x ^ 2 - x ^ 3) * (1 + x - x ^ 3) =
      1 - C (2 : ℤ) * x + C (2 : ℤ) * x ^ 4 - C (2 : ℤ) * x ^ 5 + C (2 : ℤ) * x ^ 6 - x ^ 7 := by
    simp only [map_ofNat]
    ring
  rw [denominator]
  ext n
  have shift_one : coeff n (x * mk a) = if 1 ≤ n then a (n - 1) else 0 := by
    simpa only [x, pow_one, coeff_mk] using coeff_X_pow_mul' (mk a) 1 n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add, coeff_C_mul, shift_one,
    x, coeff_mk, coeff_X_pow_mul', coeff_one, coeff_X, coeff_X_pow]
  by_cases hn : n < 7
  · interval_cases n <;> norm_num [a, padovan, Finset.sum_range_succ]
  · have h1 : 1 ≤ n := by omega
    have h4 : 4 ≤ n := by omega
    have h5 : 5 ≤ n := by omega
    have h6 : 6 ≤ n := by omega
    have h7 : 7 ≤ n := by omega
    have e0 : n ≠ 0 := by omega
    have e1 : n ≠ 1 := by omega
    have e2 : n ≠ 2 := by omega
    have e3 : n ≠ 3 := by omega
    have e4 : n ≠ 4 := by omega
    simp only [if_pos h1, if_pos h4, if_pos h5, if_pos h6, if_pos h7,
      if_neg e0, if_neg e1, if_neg e2, if_neg e3, if_neg e4]
    linarith only [recurrence n (by omega)]

theorem OMA.solution : type_of% @OMA.S_oeis_a329178.main := by
  exact ⟨generating_function, recurrence⟩
