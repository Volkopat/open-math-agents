import OMAStatements.S_oeis_a192382
import Mathlib

-- Proof of Colin Barker's conjectures in OEIS A192382 (statement by @ivillar).
-- Idea: modulo N = x^2 - x - 2 the recurrence of p becomes p(n+2) = 2x*p(n+1), so the reduction
-- c(n) + d(n)*x satisfies c(n+2) = 4d(n+1), d(n+2) = 2c(n+1) + 2d(n+1), hence
-- d(n+3) = 2d(n+2) + 8d(n+1) and 12*d(n) = 2^n*(2*(-1)^n + 2^n) for n ≥ 1.

namespace OMAA192382Helpers

open Polynomial OMA.S_oeis_a192382

def cd : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | 1 => (1, 0)
  | n + 2 => (4 * (cd (n + 1)).2, 2 * (cd (n + 1)).1 + 2 * (cd (n + 1)).2)

theorem hM : (X ^ 2 - X - 2 : ℤ[X]).Monic := by monicity!

theorem dvd_step : ∀ n : ℕ, (X ^ 2 - X - 2 : ℤ[X]) ∣ p n - (C (cd n).2 * X + C (cd n).1)
  | 0 => by simp [p, cd]
  | 1 => by simp [p, cd]
  | n + 2 => by
    have h1 := dvd_step (n + 1)
    have e : p (n + 2) - (C (cd (n + 2)).2 * X + C (cd (n + 2)).1) =
        2 * X * (p (n + 1) - (C (cd (n + 1)).2 * X + C (cd (n + 1)).1)) +
          (X ^ 2 - X - 2) * (C (2 * (cd (n + 1)).2) - p n) := by
      simp only [p, cd, map_add, map_mul, map_ofNat]
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_right _ _)

theorem reduce_eq (n : ℕ) : reduce (p n) = C (cd n).2 * X + C (cd n).1 := by
  unfold reduce
  rw [modByMonic_eq_of_dvd_sub hM (dvd_step n), (modByMonic_eq_self_iff hM).mpr]
  have h2 : (X ^ 2 - X - 2 : ℤ[X]).degree = 2 := by compute_degree!
  rw [h2]
  exact degree_linear_lt

theorem a_eq (n : ℕ) : a n = (cd n).2 := by
  unfold a
  rw [reduce_eq, coeff_add, coeff_C_mul, coeff_X_one, coeff_C]
  simp

theorem d_rec (n : ℕ) : (cd (n + 3)).2 = 2 * (cd (n + 2)).2 + 8 * (cd (n + 1)).2 := by
  have h1 : (cd (n + 3)).2 = 2 * (cd (n + 2)).1 + 2 * (cd (n + 2)).2 := by simp [cd]
  have h2 : (cd (n + 2)).1 = 4 * (cd (n + 1)).2 := by simp [cd]
  rw [h1, h2]; ring

theorem d_closed : ∀ n : ℕ, 12 * (cd (n + 1)).2 = 2 ^ (n + 1) * (2 * (-1) ^ (n + 1) + 2 ^ (n + 1))
  | 0 => by simp [cd]
  | 1 => by simp [cd]
  | n + 2 => by
    have h1 := d_closed (n + 1)
    have h0 := d_closed n
    rw [show n + 2 + 1 = n + 3 by ring, d_rec]
    rw [show n + 1 + 1 = n + 2 by ring] at h1
    linear_combination 2 * h1 + 8 * h0

theorem a_closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = 2 ^ n * (2 * (-1) ^ n + 2 ^ n) / 12 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := d_closed m
  rw [a_eq]
  have h' : ((12 * (cd (m + 1)).2 : ℤ) : ℚ) =
      ((2 ^ (m + 1) * (2 * (-1) ^ (m + 1) + 2 ^ (m + 1)) : ℤ) : ℚ) := by rw [h]
  push_cast at h'
  linear_combination h' / 12

theorem key : PowerSeries.mk (fun n => ((cd n).2 : ℚ)) *
    ((1 + 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X)) = 2 * PowerSeries.X ^ 2 := by
  set F := PowerSeries.mk (fun n => ((cd n).2 : ℚ))
  have e1 : F * ((1 + 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X)) =
      F - PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 1 * F) -
        PowerSeries.C (8 : ℚ) * (PowerSeries.X ^ 2 * F) := by
    simp only [map_ofNat]
    ring
  have e2 : (2 * PowerSeries.X ^ 2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 2 := by
    simp only [map_ofNat]
  rw [e1, e2]
  ext n
  simp only [F, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 2
  · interval_cases n <;> norm_num [cd]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
    have h := d_rec j
    have q : (((cd (j + 3)).2 : ℤ) : ℚ) = ((2 * (cd (j + 2)).2 + 8 * (cd (j + 1)).2 : ℤ) : ℚ) := by
      rw [h]
    push_cast at q
    simp
    linear_combination q

end OMAA192382Helpers

open Polynomial OMA.S_oeis_a192382 OMAA192382Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a192382.main := by
  refine ⟨fun n hn => ?_, fun n hn => ?_, fun n hn => ?_, ?_⟩
  · rw [a_closed n hn, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
    ring
  · rw [a_closed n hn, A003683]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
    ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, a_eq, a_eq, a_eq]
    exact d_rec m
  · have hX : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) =
        PowerSeries.mk (fun n => ((cd n).2 : ℚ)) := by
      ext n
      rcases n with _ | n
      · simp [cd]
      · simp [a_eq]
    rw [hX, G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp), key]
