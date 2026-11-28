import OMAStatements.S_oeis_a235804
import Mathlib

-- Problem: A235804: Rectangular array read by upward antidiagonals: A(n,k) = n-2+k*2^(n-3), n>=3, k>=0.
-- Upstream: formal-conjectures statements/oeis-a235804.lean:0 (declaration OMA.S_oeis_a235804.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Both identities are checked coefficient by coefficient. Multiplying a series f by 1 - a x
replaces its coefficients f(m) by f(m) - a f(m-1). Applying this twice with a = 1 kills the part
of A(n,k) that is linear in k beyond degree 1; applying it with a = 2 and twice with a = 1 kills
both m + 1 and 2^m beyond degree 2. -/

namespace A235804Aux

open PowerSeries OMA.S_oeis_a235804

theorem c_succ (f : ℤ⟦X⟧) (a : ℤ) (m : ℕ) :
    coeff (m + 1) (f * (1 - C a * X)) = coeff (m + 1) f - a * coeff m f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C a) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_succ_mul_X]
  ring

theorem c_zero (f : ℤ⟦X⟧) (a : ℤ) : coeff 0 (f * (1 - C a * X)) = coeff 0 f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C a) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_zero_mul_X]
  ring

theorem coeff_quad (a b c : ℤ) (m : ℕ) :
    coeff m (C a + C b * X + C c * X * X : ℤ⟦X⟧) =
      if m = 0 then a else if m = 1 then b else if m = 2 then c else 0 := by
  rcases m with _ | _ | _ | m
  · simp only [map_add, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_zero_C, add_zero, if_true]
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X,
      PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C]
    simp

theorem row (n : ℕ) :
    PowerSeries.mk (fun k => A n k) * (1 - X) ^ 2 =
      C ((n : ℤ) - 2) + C (2 ^ (n - 3) - ((n : ℤ) - 2)) * X := by
  have h1 : (C 1 : ℤ⟦X⟧) = 1 := map_one C
  have hl : PowerSeries.mk (fun k => A n k) * (1 - X) ^ 2 =
      PowerSeries.mk (fun k => A n k) * (1 - C 1 * X) * (1 - C 1 * X) := by
    rw [h1]
    ring
  have hr : C ((n : ℤ) - 2) + C (2 ^ (n - 3) - ((n : ℤ) - 2)) * X =
      C ((n : ℤ) - 2) + C (2 ^ (n - 3) - ((n : ℤ) - 2)) * X + C 0 * X * X := by
    rw [map_zero]
    ring
  rw [hl, hr]
  ext m
  rw [coeff_quad]
  rcases m with _ | _ | m
  · simp only [c_zero, PowerSeries.coeff_mk, A]
    simp
  · simp only [c_succ, c_zero, PowerSeries.coeff_mk, A]
    simp
  · simp only [c_succ, PowerSeries.coeff_mk, A]
    simp
    ring

theorem col (k : ℕ) :
    PowerSeries.mk (fun m => A (m + 3) k) * ((1 - 2 * X) * (1 - X) ^ 2) =
      C ((k : ℤ) + 1) - C (2 * ((k : ℤ) + 1)) * X + C (k : ℤ) * X ^ 2 := by
  have h1 : (C 1 : ℤ⟦X⟧) = 1 := map_one C
  have h2 : (C 2 : ℤ⟦X⟧) = 2 := map_ofNat C 2
  have hl : PowerSeries.mk (fun m => A (m + 3) k) * ((1 - 2 * X) * (1 - X) ^ 2) =
      PowerSeries.mk (fun m => A (m + 3) k) * (1 - C 2 * X) * (1 - C 1 * X) * (1 - C 1 * X) := by
    rw [h1, h2]
    ring
  have hr : C ((k : ℤ) + 1) - C (2 * ((k : ℤ) + 1)) * X + C (k : ℤ) * X ^ 2 =
      C ((k : ℤ) + 1) + C (-(2 * ((k : ℤ) + 1))) * X + C (k : ℤ) * X * X := by
    rw [map_neg]
    ring
  rw [hl, hr]
  ext m
  rw [coeff_quad]
  rcases m with _ | _ | _ | m
  · simp only [c_zero, PowerSeries.coeff_mk, A]
    simp
    ring
  · simp only [c_succ, c_zero, PowerSeries.coeff_mk, A]
    simp
    ring
  · simp only [c_succ, c_zero, PowerSeries.coeff_mk, A]
    simp
    ring
  · simp only [c_succ, PowerSeries.coeff_mk, A]
    simp
    ring

end A235804Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a235804.main :=
  ⟨fun n _ => A235804Aux.row n, A235804Aux.col⟩
