import OMAStatements.S_oeis_a192338
import Mathlib

-- Proof of Colin Barker's conjecture in OEIS A192338 (statement by @ivillar).
-- Idea: x^2 - x - 2 = (x - 2)(x + 1), so three times the constant term of the reduction of F is
-- F(2) + 2F(-1). The values u(n) = F(n,2) and t(n) = F(n,-1) satisfy u(n+2) = 2u(n+1) + 4u(n)
-- and t(n+2) = 2t(n+1) + t(n), so u + 2t is annihilated by (T^2-2T-4)(T^2-2T-1)
-- = T^4 - 4T^3 - T^2 + 10T + 4, which is the recurrence; the g.f. follows.

namespace OMAA192338Helpers

open Polynomial OMA.S_oeis_a192338

theorem hq2 : (X ^ 2 - X - 2 : ℤ[X]).natDegree = 2 := by compute_degree!

theorem coeff0_eq (f : ℤ[X]) :
    3 * (f %ₘ (X ^ 2 - X - 2)).coeff 0 = eval 2 f + 2 * eval (-1) f := by
  have hm : (X ^ 2 - X - 2 : ℤ[X]).Monic := by monicity!
  have hne : (X ^ 2 - X - 2 : ℤ[X]) ≠ 1 := by
    intro h
    have := congrArg natDegree h
    rw [hq2, natDegree_one] at this
    omega
  have hdeg : (f %ₘ (X ^ 2 - X - 2)).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt f hm hne
    rw [hq2] at this
    omega
  have q2 : eval 2 (X ^ 2 - X - 2 : ℤ[X]) = 0 := by norm_num
  have qm : eval (-1) (X ^ 2 - X - 2 : ℤ[X]) = 0 := by norm_num
  have h2 : eval 2 (f %ₘ (X ^ 2 - X - 2)) = eval 2 f := by
    conv_rhs => rw [← modByMonic_add_div f (X ^ 2 - X - 2)]
    rw [eval_add, eval_mul, q2, zero_mul, add_zero]
  have h1 : eval (-1) (f %ₘ (X ^ 2 - X - 2)) = eval (-1) f := by
    conv_rhs => rw [← modByMonic_add_div f (X ^ 2 - X - 2)]
    rw [eval_add, eval_mul, qm, zero_mul, add_zero]
  rw [eq_X_add_C_of_natDegree_le_one hdeg] at h2 h1
  simp only [eval_add, eval_mul, eval_C, eval_X] at h2 h1
  linear_combination h2 + 2 * h1

theorem evF (n : ℕ) (x : ℤ) : eval x (F (n + 1)) = (x + 1) * eval x (F n) + eval (-x) (F n) := by
  simp [F, eval_comp]

noncomputable def A (n : ℕ) : ℤ := eval 2 (F n) + 2 * eval (-1) (F n)

theorem u_rec (n : ℕ) : eval 2 (F (n + 2)) = 2 * eval 2 (F (n + 1)) + 4 * eval 2 (F n) := by
  have h1 := evF (n + 1) 2
  have h2 := evF n 2
  have h3 := evF n (-2)
  norm_num at h1 h2 h3
  rw [h1, h3]
  linear_combination h2

theorem t_rec (n : ℕ) : eval (-1) (F (n + 2)) = 2 * eval (-1) (F (n + 1)) + eval (-1) (F n) := by
  have h1 := evF (n + 1) (-1)
  have h2 := evF n 1
  have h3 := evF n (-1)
  norm_num at h1 h2 h3
  rw [h1, h2, h3]

theorem A_rec (n : ℕ) : A (n + 4) = 4 * A (n + 3) + A (n + 2) - 10 * A (n + 1) - 4 * A n := by
  unfold A
  have U2 := u_rec (n + 2)
  have U1 := u_rec (n + 1)
  have U0 := u_rec n
  have T2 := t_rec (n + 2)
  have T1 := t_rec (n + 1)
  have T0 := t_rec n
  linear_combination (U2 - 2 * U1 - U0) + 2 * (T2 - 2 * T1 - 4 * T0)

theorem a_eq (n : ℕ) : 3 * a (n + 1) = A n := by
  unfold a A reduce
  rw [Nat.add_sub_cancel, coeff0_eq]

theorem key : PowerSeries.mk (fun n => ((A n : ℚ) / 3)) *
    ((PowerSeries.X ^ 2 + 2 * PowerSeries.X - 1) * (4 * PowerSeries.X ^ 2 + 2 * PowerSeries.X - 1)) =
    2 * PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 2 - 2 * PowerSeries.X + 1 := by
  set B := PowerSeries.mk (fun n => ((A n : ℚ) / 3))
  have e1 : B * ((PowerSeries.X ^ 2 + 2 * PowerSeries.X - 1) *
      (4 * PowerSeries.X ^ 2 + 2 * PowerSeries.X - 1)) =
      B - PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 1 * B) - PowerSeries.X ^ 2 * B +
        PowerSeries.C (10 : ℚ) * (PowerSeries.X ^ 3 * B) +
        PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 4 * B) := by
    simp only [map_ofNat]
    ring
  have e2 : (2 * PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 2 - 2 * PowerSeries.X + 1 : PowerSeries ℚ) =
      PowerSeries.X ^ 0 - PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 1 -
        PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [B, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 3
  · interval_cases n <;> norm_num [A, F, eval_comp]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    have h := A_rec j
    have q : ((A (j + 4) : ℤ) : ℚ) = ((4 * A (j + 3) + A (j + 2) - 10 * A (j + 1) - 4 * A j : ℤ) : ℚ) := by
      rw [h]
    push_cast at q
    simp
    linear_combination q / 3

end OMAA192338Helpers

open Polynomial OMA.S_oeis_a192338 OMAA192338Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a192338.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
    rw [show j + 5 - 1 = (j + 3) + 1 by omega, show j + 5 - 2 = (j + 2) + 1 by omega,
      show j + 5 - 3 = (j + 1) + 1 by omega, show j + 5 - 4 = j + 1 by omega,
      show j + 5 = (j + 4) + 1 by omega]
    have h4 := a_eq (j + 4)
    have h3 := a_eq (j + 3)
    have h2 := a_eq (j + 2)
    have h1 := a_eq (j + 1)
    have h0 := a_eq j
    have hr := A_rec j
    linarith
  · have hX : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) =
        PowerSeries.X * PowerSeries.mk (fun n => ((A n : ℚ) / 3)) := by
      ext n
      rcases n with _ | n
      · simp
      · rw [PowerSeries.coeff_succ_X_mul]
        simp only [PowerSeries.coeff_mk, Nat.succ_ne_zero, if_false]
        have h := a_eq n
        have h' : ((3 * a (n + 1) : ℤ) : ℚ) = ((A n : ℤ) : ℚ) := by rw [h]
        push_cast at h'
        linarith
    rw [hX, G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp), mul_assoc, key]
