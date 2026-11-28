import OMAStatements.S_oeis_a192248
import Mathlib

-- Proof of R. J. Mathar's conjecture in OEIS A192248 (original formalization by @ivillar).
-- Idea: modulo x^2 - x - 1, x^(k+1) reduces to F(k+1)*x + F(k), so the reduction of p(n,x) has constant
-- term cc(n) with cc(n+1) = cc(n) + c(n+2)*F(n). The g.f. identity amounts to the order-11 recurrence
-- with characteristic polynomial (x-1)*(x^2+x-1)^5 for cc (plus the first 11 terms). Writing every F(n+i)
-- as a combination of F(n) and F(n+1) turns that recurrence into a polynomial identity in n.

namespace OMAA192248Helpers

open Polynomial OMA.S_oeis_a192248

/-- Constant part of the reduction of p(n,x). -/
noncomputable def cc : ℕ → ℚ
  | 0 => 1
  | n + 1 => cc n + c (n + 2) * (Nat.fib n : ℚ)

/-- Coefficient of x in the reduction of p(n,x). -/
noncomputable def dd : ℕ → ℚ
  | 0 => 0
  | n + 1 => dd n + c (n + 2) * (Nat.fib (n + 1) : ℚ)

theorem hM : (X ^ 2 - X - 1 : ℚ[X]).Monic := by monicity!

theorem powX (n : ℕ) :
    (X ^ 2 - X - 1 : ℚ[X]) ∣ X ^ (n + 1) - (C (Nat.fib (n + 1) : ℚ) * X + C (Nat.fib n : ℚ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : X ^ (n + 1 + 1) - (C (Nat.fib (n + 1 + 1) : ℚ) * X + C (Nat.fib (n + 1) : ℚ)) =
        X * (X ^ (n + 1) - (C (Nat.fib (n + 1) : ℚ) * X + C (Nat.fib n : ℚ))) +
          C (Nat.fib (n + 1) : ℚ) * (X ^ 2 - X - 1) := by
      rw [Nat.fib_add_two]
      push_cast
      simp only [map_add]
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_left _ _)

theorem dvd_step (n : ℕ) : (X ^ 2 - X - 1 : ℚ[X]) ∣ p n - (C (dd n) * X + C (cc n)) := by
  induction n with
  | zero => simp [p, dd, cc]
  | succ n ih =>
    have e : p (n + 1) - (C (dd (n + 1)) * X + C (cc (n + 1))) =
        (p n - (C (dd n) * X + C (cc n))) +
          C (c (n + 2)) * (X ^ (n + 1) - (C (Nat.fib (n + 1) : ℚ) * X + C (Nat.fib n : ℚ))) := by
      simp only [p, dd, cc, map_add, map_mul]
      ring
    rw [e]
    exact dvd_add ih (dvd_mul_of_dvd_right (powX n) _)

theorem reduce_eq (n : ℕ) : reduce (p n) = C (dd n) * X + C (cc n) := by
  unfold reduce
  rw [modByMonic_eq_of_dvd_sub hM (dvd_step n), (modByMonic_eq_self_iff hM).mpr]
  have h2 : (X ^ 2 - X - 1 : ℚ[X]).degree = 2 := by compute_degree!
  rw [h2]
  exact degree_linear_lt

theorem a_eq (n : ℕ) : a (n + 1) = cc n := by
  unfold a
  rw [Nat.add_sub_cancel, reduce_eq, coeff_add, coeff_C_mul, coeff_X_zero, coeff_C]
  simp

theorem c_rec (j : ℕ) :
    cc (j + 11) - 6 * cc (j + 10) + 10 * cc (j + 9) + 5 * cc (j + 8) - 25 * cc (j + 7) + 4 * cc (j + 6) + 26 * cc (j + 5) - 5 * cc (j + 4) - 15 * cc (j + 3) + 4 * cc (j + 1) + cc j = 0 := by
  have step (k : ℕ) : cc (j + k + 1) =
      cc (j + k) + c (j + k + 2) * (Nat.fib (j + k) : ℚ) := rfl
  have shift (k : ℕ) : (Nat.fib (j + k + 2) : ℚ) =
      (Nat.fib j : ℚ) * Nat.fib (k + 1) + (Nat.fib (j + 1) : ℚ) * Nat.fib (k + 2) := by
    exact_mod_cast Nat.fib_add j (k + 1)
  rw [step 10, step 9, step 8, step 7, step 6, step 5, step 4, step 3, step 2, step 1, step 0]
  rw [shift 8, shift 7, shift 6, shift 5, shift 4, shift 3, shift 2, shift 1, shift 0]
  norm_num [c, Nat.fib_add_two]
  push_cast
  ring

theorem key : PowerSeries.mk cc * ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 + PowerSeries.X - 1) ^ 5) =
    -(-1 + 5 * PowerSeries.X - 20 * PowerSeries.X ^ 2 + 30 * PowerSeries.X ^ 3 -
      25 * PowerSeries.X ^ 4 + 8 * PowerSeries.X ^ 5) := by
  set F := PowerSeries.mk cc
  have e1 : F * ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 + PowerSeries.X - 1) ^ 5) =
      F - PowerSeries.C (6 : ℚ) * (PowerSeries.X ^ 1 * F) + PowerSeries.C (10 : ℚ) * (PowerSeries.X ^ 2 * F) + PowerSeries.C (5 : ℚ) * (PowerSeries.X ^ 3 * F) - PowerSeries.C (25 : ℚ) * (PowerSeries.X ^ 4 * F) + PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 5 * F) + PowerSeries.C (26 : ℚ) * (PowerSeries.X ^ 6 * F) - PowerSeries.C (5 : ℚ) * (PowerSeries.X ^ 7 * F) - PowerSeries.C (15 : ℚ) * (PowerSeries.X ^ 8 * F) + PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 10 * F) + PowerSeries.C (1 : ℚ) * (PowerSeries.X ^ 11 * F) := by
    simp only [map_ofNat, map_one]
    ring
  have e2 : (-(-1 + 5 * PowerSeries.X - 20 * PowerSeries.X ^ 2 + 30 * PowerSeries.X ^ 3 -
      25 * PowerSeries.X ^ 4 + 8 * PowerSeries.X ^ 5) : PowerSeries ℚ) =
      PowerSeries.X ^ 0 - PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 1 +
        PowerSeries.C (20 : ℚ) * PowerSeries.X ^ 2 - PowerSeries.C (30 : ℚ) * PowerSeries.X ^ 3 +
        PowerSeries.C (25 : ℚ) * PowerSeries.X ^ 4 - PowerSeries.C (8 : ℚ) * PowerSeries.X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [F, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 10
  · interval_cases n <;> norm_num [cc, c, Nat.fib_add_two]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 11 := ⟨n - 11, by omega⟩
    have h := c_rec j
    simp
    linear_combination h

end OMAA192248Helpers

open Polynomial OMA.S_oeis_a192248 OMAA192248Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a192248.main := by
  have hX : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) =
      PowerSeries.X * PowerSeries.mk cc := by
    ext n
    rcases n with _ | n
    · simp
    · rw [PowerSeries.coeff_succ_X_mul]
      simp [a_eq]
  rw [hX, G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp), mul_assoc, key]
  ring
