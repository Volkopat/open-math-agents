import OMAStatements.S_oeis_a316357
import Mathlib

open OMA.S_oeis_a316357
open PowerSeries

namespace P316357

def E (n : ℕ) : ℤ := shell (n + 6) - shell (n + 5) + shell (n + 4) - 2 * shell (n + 3)
  + shell (n + 2) - shell (n + 1) + shell n

theorem E_per (n : ℕ) : E (n + 12) = E n := by
  unfold E
  have h : ∀ k, shell (n + 12 + k) = shell (n + k) + 40 := fun k => by
    rw [show n + 12 + k = (n + k) + 12 by omega]; rfl
  rw [h 6, h 5, h 4, h 3, h 2, h 1, show n + 12 = n + 0 + 12 by omega,
    show shell (n + 0 + 12) = shell (n + 0) + 40 from rfl]
  simp only [add_zero]
  ring

theorem E_zero : ∀ n, E n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 12 with hn | hn
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
      rw [E_per]
      exact ih m (by omega)

theorem rec (n : ℕ) : total (n+7) = 2*total (n+6) - 2*total (n+5) +
      3*total (n+4) - 3*total (n+3) + 2*total (n+2) - 2*total (n+1) + total n := by
  have e := E_zero n
  unfold E at e
  have t7 : total (n + 7) = total (n + 6) + shell (n + 6) := rfl
  have t6 : total (n + 6) = total (n + 5) + shell (n + 5) := rfl
  have t5 : total (n + 5) = total (n + 4) + shell (n + 4) := rfl
  have t4 : total (n + 4) = total (n + 3) + shell (n + 3) := rfl
  have t3 : total (n + 3) = total (n + 2) + shell (n + 2) := rfl
  have t2 : total (n + 2) = total (n + 1) + shell (n + 1) := rfl
  have t1 : total (n + 1) = total n + shell n := rfl
  linear_combination t7 - t6 + t5 - 2 * t4 + t3 - t2 + t1 + e

end P316357

theorem OMA.solution : type_of% @OMA.S_oeis_a316357.main := by
  refine ⟨P316357.rec, ?_⟩
  have hp : ((1 - X) ^ 3 * (1 + X ^ 2) * (1 + X + X ^ 2) : PowerSeries ℤ) =
      1 - C 2 * X ^ 1 + C 2 * X ^ 2 - C 3 * X ^ 3 + C 3 * X ^ 4 - C 2 * X ^ 5 + C 2 * X ^ 6 - X ^ 7 := by
    simp only [map_ofNat]; ring
  have hq : ∀ F : PowerSeries ℤ, (1 - C 2 * X ^ 1 + C 2 * X ^ 2 - C 3 * X ^ 3 + C 3 * X ^ 4 - C 2 * X ^ 5
      + C 2 * X ^ 6 - X ^ 7) * F = F - C 2 * (F * X ^ 1) + C 2 * (F * X ^ 2) - C 3 * (F * X ^ 3)
      + C 3 * (F * X ^ 4) - C 2 * (F * X ^ 5) + C 2 * (F * X ^ 6) - F * X ^ 7 := fun F => by ring
  have hr : (1 + 3*X + 5*X^2 + 2*X^3 + 5*X^4 + 3*X^5 + X^6 : PowerSeries ℤ) =
      1 + C 3 * X ^ 1 + C 5 * X ^ 2 + C 2 * X ^ 3 + C 5 * X ^ 4 + C 3 * X ^ 5 + X ^ 6 := by
    simp only [map_ofNat, pow_one]
  rw [hp, hq, hr]
  clear hp hq hr
  ext n
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow,
    coeff_X_pow, coeff_one, coeff_C]
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have h := P316357.rec m
    simp (disch := omega) only [if_pos, if_neg]
    rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega, show m + 7 - 7 = m by omega]
    linarith
