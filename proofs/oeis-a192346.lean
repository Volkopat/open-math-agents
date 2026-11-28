import OMAStatements.S_oeis_a192346
import Mathlib

-- Proof of Colin Barker's conjectures in OEIS A192346 (statement by @ivillar).
-- Idea: modulo M = x^2 - x - 1 we have x^2 - x - 2 = M - 1, so the reduction c(n) + d(n)*x of
-- p(n,x) satisfies c(n+2) = 2d(n+1) + 1c(n), d(n+2) = 2c(n+1) + 2d(n+1) + 1d(n);
-- eliminating d gives the order-4 recurrence for c, and the g.f. follows.

namespace OMAA192346Helpers

open Polynomial OMA.S_oeis_a192346

def cd : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | n + 2 => (2 * (cd (n + 1)).2 + 1 * (cd n).1,
      2 * (cd (n + 1)).1 + 2 * (cd (n + 1)).2 + 1 * (cd n).2)

theorem hM : (X ^ 2 - X - 1 : ℤ[X]).Monic := by monicity!

theorem dvd_step : ∀ n : ℕ, (X ^ 2 - X - 1 : ℤ[X]) ∣ p n - (C (cd n).2 * X + C (cd n).1)
  | 0 => by simp [p, cd]
  | 1 => by simp [p, cd]
  | n + 2 => by
    have h1 := dvd_step (n + 1)
    have h0 := dvd_step n
    have e : p (n + 2) - (C (cd (n + 2)).2 * X + C (cd (n + 2)).1) =
        2 * X * (p (n + 1) - (C (cd (n + 1)).2 * X + C (cd (n + 1)).1)) +
          1 * (p n - (C (cd n).2 * X + C (cd n).1)) +
          (X ^ 2 - X - 1) * (C (2 * (cd (n + 1)).2) - p n) := by
      simp only [p, cd, map_add, map_mul, map_ofNat, map_one, one_mul]
      ring
    rw [e]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h0 _))
      (dvd_mul_right _ _)

theorem reduce_eq (n : ℕ) : reduce (p n) = C (cd n).2 * X + C (cd n).1 := by
  unfold reduce
  rw [modByMonic_eq_of_dvd_sub hM (dvd_step n), (modByMonic_eq_self_iff hM).mpr]
  have h2 : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by compute_degree!
  rw [h2]
  exact degree_linear_lt

theorem a_eq (n : ℕ) : a (n + 1) = (cd n).1 := by
  unfold a
  rw [Nat.add_sub_cancel, reduce_eq, coeff_add, coeff_C_mul, coeff_X_zero, coeff_C]
  simp

theorem rc (n : ℕ) : (cd (n + 2)).1 = 2 * (cd (n + 1)).2 + 1 * (cd n).1 := by simp [cd]
theorem rd (n : ℕ) : (cd (n + 2)).2 = 2 * (cd (n + 1)).1 + 2 * (cd (n + 1)).2 + 1 * (cd n).2 := by
  simp [cd]

theorem c_rec (n : ℕ) : (cd (n + 4)).1 = 2 * (cd (n + 3)).1 + 6 * (cd (n + 2)).1 -
    2 * (cd (n + 1)).1 - 1 * (cd n).1 := by
  have e1 := rc (n + 2)
  have e2 := rd (n + 1)
  have e3 := rc (n + 1)
  have e4 := rc n
  linear_combination e1 + 2 * e2 - 2 * e3 - 1 * e4

theorem key : PowerSeries.mk (fun n => ((cd n).1 : ℚ)) *
    (PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 3 - 6 * PowerSeries.X ^ 2 - 2 * PowerSeries.X + 1) =
    1 - 2 * PowerSeries.X - 3 * PowerSeries.X ^ 2 := by
  set F := PowerSeries.mk (fun n => ((cd n).1 : ℚ))
  have e1 : F * (PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 3 - 6 * PowerSeries.X ^ 2 - 2 * PowerSeries.X + 1) =
      F - PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 1 * F) -
        PowerSeries.C (6 : ℚ) * (PowerSeries.X ^ 2 * F) +
        PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 3 * F) +
        PowerSeries.C (1 : ℚ) * (PowerSeries.X ^ 4 * F) := by
    simp only [map_ofNat, map_one]
    ring
  have e2 : (1 - 2 * PowerSeries.X - 3 * PowerSeries.X ^ 2 : PowerSeries ℚ) =
      PowerSeries.X ^ 0 - PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 1 -
        PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 2 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [F, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 3
  · interval_cases n <;> norm_num [cd]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    have h := c_rec j
    have q : (((cd (j + 4)).1 : ℤ) : ℚ) = ((2 * (cd (j + 3)).1 + 6 * (cd (j + 2)).1 -
        2 * (cd (j + 1)).1 - 1 * (cd j).1 : ℤ) : ℚ) := by rw [h]
    push_cast at q
    simp
    linear_combination q

end OMAA192346Helpers

open Polynomial OMA.S_oeis_a192346 OMAA192346Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a192346.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
    rw [show j + 5 - 1 = (j + 3) + 1 by omega, show j + 5 - 2 = (j + 2) + 1 by omega,
      show j + 5 - 3 = (j + 1) + 1 by omega, show j + 5 - 4 = j + 1 by omega,
      show j + 5 = (j + 4) + 1 by omega, a_eq, a_eq, a_eq, a_eq, a_eq]
    exact c_rec j
  · have hX : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) =
        PowerSeries.X * PowerSeries.mk (fun n => ((cd n).1 : ℚ)) := by
      ext n
      rcases n with _ | n
      · simp
      · rw [PowerSeries.coeff_succ_X_mul]
        simp [a_eq]
    rw [hX, G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp), mul_assoc, key]
    ring
