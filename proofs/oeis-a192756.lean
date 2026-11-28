import OMAStatements.S_oeis_a192756
import Mathlib

-- Proof of R. J. Mathar's conjecture in OEIS A192756 (statement by @ivillar).
-- Idea: the reduction of p(n,x) is c(n) + d(n)*x with c(n+1) = d(n) + 5(n+1), d(n+1) = c(n) + d(n);
-- hence d(n+2) = d(n+1) + d(n) + 5(n+1), and d(n) = F(n+4) + 3F(n+3) + F(n+2) - 5n - 10.

namespace OMAA192756Helpers

open Polynomial OMA.S_oeis_a192756

def cd : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((cd n).2 + 5 * ((n : ℤ) + 1), (cd n).1 + (cd n).2)

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

theorem a_eq (n : ℕ) : a n = (cd n).2 := by
  unfold a
  rw [reduce_eq, coeff_add, coeff_C_mul, coeff_X_one, coeff_C]
  simp

theorem d_rec (n : ℕ) : (cd (n + 2)).2 = (cd (n + 1)).2 + (cd n).2 + 5 * ((n : ℤ) + 1) := by
  simp only [cd]
  ring

theorem d_closed (n : ℕ) : (cd n).2 = (Nat.fib (n + 4) : ℤ) + 3 * Nat.fib (n + 3) + Nat.fib (n + 2) - 5 * n - 10 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [cd, Nat.fib_add_two]
    · simp [cd, Nat.fib_add_two]
    · rw [d_rec, ih (n + 1) (by omega), ih n (by omega)]
      simp only [Nat.fib_add_two]
      push_cast
      ring

theorem S_closed (k : ℕ) : ((∑ j ∈ Finset.range (k + 1), Nat.fib j : ℕ) : ℤ) = Nat.fib (k + 2) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    push_cast at ih ⊢
    rw [ih, show k + 1 + 2 = k + 3 by ring, Nat.fib_add_two (n := k + 1)]
    push_cast
    ring

theorem A001924_closed (n : ℕ) : (A001924 n : ℤ) = Nat.fib (n + 4) - (n + 3) := by
  induction n with
  | zero => simp [A001924]; decide
  | succ n ih =>
    unfold A001924 at ih ⊢
    rw [Finset.sum_range_succ]
    push_cast at ih ⊢
    rw [ih]
    have := S_closed (n + 1)
    push_cast at this
    rw [this, show n + 1 + 4 = n + 5 by ring, show n + 1 + 2 = n + 3 by ring,
      Nat.fib_add_two (n := n + 3)]
    push_cast
    ring

theorem A166863_closed (k : ℕ) (hk : 1 ≤ k) : (A166863 k : ℤ) = 2 * Nat.fib (k + 3) - 5 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | _ | k
    · omega
    · simp [A166863, Nat.fib_add_two]
    · simp [A166863, Nat.fib_add_two]
    · simp only [A166863]
      push_cast
      rw [ih (k + 2) (by omega) (by omega), ih (k + 1) (by omega) (by omega)]
      rw [show k + 3 + 3 = (k + 4) + 2 by ring, Nat.fib_add_two (n := k + 4),
        show k + 2 + 3 = k + 3 + 2 by ring, show k + 1 + 3 = k + 4 by ring]
      simp only [Nat.fib_add_two]
      push_cast
      ring

theorem psum (n : ℕ) : (cd n).2 = ∑ k ∈ Finset.Icc 1 n, (A166863 k : ℤ) := by
  induction n with
  | zero => simp [cd]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ← ih, A166863_closed (n + 1) (by omega),
      d_closed, d_closed]
    rw [show n + 1 + 4 = n + 3 + 2 by ring, show n + 1 + 3 = n + 2 + 2 by ring,
      show n + 1 + 2 = n + 1 + 2 by ring, show n + 4 = n + 2 + 2 by ring, show n + 3 = n + 1 + 2 by ring]
    simp only [Nat.fib_add_two]
    push_cast
    ring

theorem key : PowerSeries.mk (fun n => ((cd n).2 : ℚ)) *
    ((PowerSeries.X ^ 2 + PowerSeries.X - 1) * (PowerSeries.X - 1) ^ 2) =
    -PowerSeries.X * (1 + 3 * PowerSeries.X + PowerSeries.X ^ 2) := by
  set F := PowerSeries.mk (fun n => ((cd n).2 : ℚ))
  have e1 : F * ((PowerSeries.X ^ 2 + PowerSeries.X - 1) * (PowerSeries.X - 1) ^ 2) =
      PowerSeries.X ^ 4 * F - PowerSeries.X ^ 3 * F - PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 2 * F) +
        PowerSeries.C (3 : ℚ) * (PowerSeries.X ^ 1 * F) - F := by
    rw [map_ofNat PowerSeries.C 2, map_ofNat PowerSeries.C 3]; ring
  have e2 : (-PowerSeries.X * (1 + 3 * PowerSeries.X + PowerSeries.X ^ 2) : PowerSeries ℚ) =
      -(PowerSeries.X ^ 1) - PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 2 - PowerSeries.X ^ 3 := by
    rw [map_ofNat PowerSeries.C 3]; ring
  rw [e1, e2]
  ext n
  simp only [F, map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 3
  · interval_cases n <;> norm_num [cd]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have r1 := d_rec (m + 2)
    have r2 := d_rec (m + 1)
    have r3 := d_rec m
    have q1 : (((cd (m + 4)).2 : ℤ) : ℚ) = (((cd (m + 3)).2 + (cd (m + 2)).2 + 5 * ((((m + 2 : ℕ)) : ℤ) + 1) : ℤ) : ℚ) := by
      rw [← r1]
    have q2 : (((cd (m + 3)).2 : ℤ) : ℚ) = (((cd (m + 2)).2 + (cd (m + 1)).2 + 5 * ((((m + 1 : ℕ)) : ℤ) + 1) : ℤ) : ℚ) := by
      rw [← r2]
    have q3 : (((cd (m + 2)).2 : ℤ) : ℚ) = (((cd (m + 1)).2 + (cd m).2 + 5 * (((m : ℕ) : ℤ) + 1) : ℤ) : ℚ) := by
      rw [← r3]
    push_cast at q1 q2 q3
    simp
    linear_combination -q1 + 2 * q2 - q3

end OMAA192756Helpers

open Polynomial OMA.S_oeis_a192756 OMAA192756Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a192756.main := by
  refine ⟨?_, fun n hn => ?_, fun n => by rw [a_eq, psum]⟩
  · simp only [a_eq]
    rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp), key]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [a_eq, d_closed, show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
      A001924_closed, A001924_closed, A001924_closed]
    rw [show m + 2 + 4 = m + 4 + 2 by ring, show m + 2 + 3 = m + 3 + 2 by ring,
      show m + 1 + 4 = m + 3 + 2 by ring, show m + 2 + 2 = m + 2 + 2 by ring]
    simp only [Nat.fib_add_two]
    push_cast
    ring

