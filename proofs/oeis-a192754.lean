import OMAStatements.S_oeis_a192754
import Mathlib

-- Proof of R. J. Mathar's conjecture in OEIS A192754 (statement by @ivillar).
-- Idea: the reduction of p(n,x) is c(n) + d(n)*x with c(n+1) = d(n) + 5(n+1) + 1 and
-- d(n+1) = c(n) + d(n); hence c(n+2) = c(n+1) + c(n) + 5 and c(n) = F(n+3) + 4F(n+2) - 5.

namespace OMAA192754Helpers

open Polynomial OMA.S_oeis_a192754

def cd : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((cd n).2 + (5 * ((n : ℤ) + 1) + 1), (cd n).1 + (cd n).2)

theorem hM : (X ^ 2 - X - 1 : ℤ[X]).Monic := by monicity!

theorem dvd_step (n : ℕ) : (X ^ 2 - X - 1 : ℤ[X]) ∣ p n - (C (cd n).2 * X + C (cd n).1) := by
  induction n with
  | zero => simp [p, cd]
  | succ n ih =>
    have e : p (n + 1) - (C (cd (n + 1)).2 * X + C (cd (n + 1)).1) =
        X * (p n - (C (cd n).2 * X + C (cd n).1)) + C (cd n).2 * (X ^ 2 - X - 1) := by
      simp only [p, cd, map_add]
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right ih X) (dvd_mul_left _ _)

theorem reduce_eq (n : ℕ) : reduce (p n) = C (cd n).2 * X + C (cd n).1 := by
  unfold reduce
  rw [modByMonic_eq_of_dvd_sub hM (dvd_step n), (modByMonic_eq_self_iff hM).mpr]
  have h2 : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by compute_degree!
  rw [h2]
  exact degree_linear_lt

theorem a_eq (n : ℕ) : a n = (cd n).1 := by
  unfold a
  rw [reduce_eq, coeff_add, coeff_C_mul, coeff_X_zero, coeff_C]
  simp

theorem c_rec (n : ℕ) : (cd (n + 2)).1 = (cd (n + 1)).1 + (cd n).1 + 5 := by
  simp only [cd]
  push_cast
  ring

theorem c_closed (n : ℕ) : (cd n).1 = (Nat.fib (n + 3) : ℤ) + 4 * Nat.fib (n + 2) - 5 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [cd, Nat.fib_add_two]
    · simp [cd, Nat.fib_add_two]
    · rw [c_rec, ih (n + 1) (by omega), ih n (by omega)]
      simp only [Nat.fib_add_two]
      push_cast
      ring

theorem A022095_closed (k : ℕ) : (A022095 k : ℤ) = Nat.fib (k + 1) + 4 * Nat.fib k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · simp [A022095]
    · simp [A022095]
    · simp only [A022095]
      push_cast
      rw [ih (k + 1) (by omega), ih k (by omega)]
      simp only [Nat.fib_add_two]
      push_cast
      ring

theorem psum (n : ℕ) : (cd n).1 = ∑ k ∈ Finset.range (n + 1), (A022095 k : ℤ) := by
  induction n with
  | zero => simp [cd, A022095]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, A022095_closed, c_closed, c_closed]
    rw [show n + 1 + 3 = n + 2 + 2 by ring, show n + 1 + 2 = n + 1 + 2 by ring,
      show n + 1 + 1 = n + 2 by ring, show n + 3 = n + 1 + 2 by ring]
    simp only [Nat.fib_add_two]
    push_cast
    ring

theorem key : PowerSeries.mk (fun n => ((cd n).1 : ℚ)) *
    ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 + PowerSeries.X - 1)) = 1 + 4 * PowerSeries.X := by
  set F := PowerSeries.mk (fun n => ((cd n).1 : ℚ))
  have e1 : F * ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 + PowerSeries.X - 1)) =
      PowerSeries.X ^ 3 * F - PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 1 * F) + F := by
    rw [map_ofNat PowerSeries.C 2]; ring
  have e2 : (1 + 4 * PowerSeries.X : PowerSeries ℚ) =
      PowerSeries.X ^ 0 + PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 1 := by
    rw [map_ofNat PowerSeries.C 4]; ring
  rw [e1, e2]
  ext n
  simp only [F, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 2
  · interval_cases n <;> norm_num [cd]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have q1 : (((cd (m + 3)).1 : ℤ) : ℚ) = (((cd (m + 2)).1 + (cd (m + 1)).1 + 5 : ℤ) : ℚ) := by
      rw [← c_rec (m + 1)]
    have q2 : (((cd (m + 2)).1 : ℤ) : ℚ) = (((cd (m + 1)).1 + (cd m).1 + 5 : ℤ) : ℚ) := by
      rw [← c_rec m]
    push_cast at q1 q2
    simp
    linear_combination q1 - q2

end OMAA192754Helpers

open Polynomial OMA.S_oeis_a192754 OMAA192754Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a192754.main := by
  refine ⟨?_, fun n => by rw [a_eq, psum], fun n => ?_⟩
  · simp only [a_eq]
    rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp), key]
  · rw [a_eq, c_closed, A000071, A000071]
    ring

