import OMAStatements.S_oeis_a108716
import Mathlib

-- Proof of Colin Barker's conjectures in OEIS A108716 (statement by @ivillar).
-- Idea (Robert Israel's remark in the entry): the three numbers cot(θ)^2 for θ = Pi/14, 3*Pi/14, 5*Pi/14
-- are the roots of t^3 - 21*t^2 + 35*t - 7. Indeed cos(7θ) = c^7 - 21c^5s^2 + 35c^3s^4 - 7cs^6
-- (angle addition) vanishes there, and dividing by c*s^6 gives the cubic in cot(θ)^2. So each power sum
-- obeys the recurrence. The three roots are distinct (cot^2 decreases on (0, Pi/2)), which gives
-- Vieta's relations e1 = 21, e2 = 35, hence a(1) = 21 and a(2) = 371, and the g.f. follows.

namespace OMAA108716Helpers

open Real OMA.S_oeis_a108716

/-- r(θ) = cot(θ)^2. -/
noncomputable def r (θ : ℝ) : ℝ := (tan θ)⁻¹ ^ 2

theorem tpow (θ : ℝ) (n : ℕ) : tan θ ^ (-(2 * n : ℤ)) = r θ ^ n := by
  rw [r, show (-(2 * n : ℤ)) = -((2 * n : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    pow_mul, inv_pow, inv_pow]

theorem a_eq (n : ℕ) : a n = r (π / 14) ^ n + r (3 * π / 14) ^ n + r (5 * π / 14) ^ n := by
  simp only [a, tpow]

theorem cos7 (θ : ℝ) :
    cos (7 * θ) = cos θ ^ 7 - 21 * cos θ ^ 5 * sin θ ^ 2 + 35 * cos θ ^ 3 * sin θ ^ 4 -
      7 * cos θ * sin θ ^ 6 := by
  rw [show 7 * θ = θ + θ + θ + θ + θ + θ + θ by ring]
  simp only [cos_add, sin_add]
  ring

theorem root (θ : ℝ) (h0 : 0 < θ) (h1 : θ < π / 2) (h7 : cos (7 * θ) = 0) :
    r θ ^ 3 - 21 * r θ ^ 2 + 35 * r θ - 7 = 0 := by
  have hc : cos θ ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith, h1⟩).ne'
  have hs : sin θ ≠ 0 := (sin_pos_of_pos_of_lt_pi h0 (by linarith)).ne'
  have hnum : cos θ ^ 6 - 21 * cos θ ^ 4 * sin θ ^ 2 + 35 * cos θ ^ 2 * sin θ ^ 4 -
      7 * sin θ ^ 6 = 0 := by
    have h := cos7 θ
    rw [h7] at h
    have hm : cos θ * (cos θ ^ 6 - 21 * cos θ ^ 4 * sin θ ^ 2 + 35 * cos θ ^ 2 * sin θ ^ 4 -
        7 * sin θ ^ 6) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp hm).resolve_left hc
  have hr : r θ = cos θ ^ 2 / sin θ ^ 2 := by
    rw [r, tan_eq_sin_div_cos, inv_div, div_pow]
  have e : r θ ^ 3 - 21 * r θ ^ 2 + 35 * r θ - 7 =
      (cos θ ^ 6 - 21 * cos θ ^ 4 * sin θ ^ 2 + 35 * cos θ ^ 2 * sin θ ^ 4 - 7 * sin θ ^ 6) /
        sin θ ^ 6 := by
    rw [hr]
    field_simp
  rw [e, hnum, zero_div]

theorem r_anti (x y : ℝ) (hx : 0 < x) (hxy : x < y) (hy : y < π / 2) : r y < r x := by
  have t1 : 0 < tan x := tan_pos_of_pos_of_lt_pi_div_two hx (by linarith)
  have t2 : 0 < tan y := tan_pos_of_pos_of_lt_pi_div_two (by linarith) hy
  have t12 : tan x < tan y := tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) hy hxy
  have i12 : (tan y)⁻¹ < (tan x)⁻¹ := (inv_lt_inv₀ t2 t1).mpr t12
  have i2 : 0 < (tan y)⁻¹ := inv_pos.mpr t2
  unfold r
  nlinarith

theorem h1 : r (π / 14) ^ 3 - 21 * r (π / 14) ^ 2 + 35 * r (π / 14) - 7 = 0 :=
  root _ (by positivity) (by linarith [pi_pos]) (by
    rw [show 7 * (π / 14) = π / 2 by ring]; exact cos_pi_div_two)

theorem h2 : r (3 * π / 14) ^ 3 - 21 * r (3 * π / 14) ^ 2 + 35 * r (3 * π / 14) - 7 = 0 :=
  root _ (by positivity) (by linarith [pi_pos]) (cos_eq_zero_iff.mpr ⟨1, by push_cast; ring⟩)

theorem h3 : r (5 * π / 14) ^ 3 - 21 * r (5 * π / 14) ^ 2 + 35 * r (5 * π / 14) - 7 = 0 :=
  root _ (by positivity) (by linarith [pi_pos]) (cos_eq_zero_iff.mpr ⟨2, by push_cast; ring⟩)

theorem vieta : r (π / 14) + r (3 * π / 14) + r (5 * π / 14) = 21 ∧
    r (π / 14) * r (3 * π / 14) + r (π / 14) * r (5 * π / 14) +
      r (3 * π / 14) * r (5 * π / 14) = 35 := by
  set u := r (π / 14)
  set v := r (3 * π / 14)
  set w := r (5 * π / 14)
  have hvu : v < u := r_anti _ _ (by positivity) (by linarith [pi_pos]) (by linarith [pi_pos])
  have hwv : w < v := r_anti _ _ (by positivity) (by linarith [pi_pos]) (by linarith [pi_pos])
  have q12 : u ^ 2 + u * v + v ^ 2 - 21 * (u + v) + 35 = 0 := by
    have hm : (u - v) * (u ^ 2 + u * v + v ^ 2 - 21 * (u + v) + 35) = 0 := by
      linear_combination h1 - h2
    exact (mul_eq_zero.mp hm).resolve_left (by linarith)
  have q13 : u ^ 2 + u * w + w ^ 2 - 21 * (u + w) + 35 = 0 := by
    have hm : (u - w) * (u ^ 2 + u * w + w ^ 2 - 21 * (u + w) + 35) = 0 := by
      linear_combination h1 - h3
    exact (mul_eq_zero.mp hm).resolve_left (by linarith)
  have e1 : u + v + w = 21 := by
    have hm : (v - w) * (u + v + w - 21) = 0 := by linear_combination q12 - q13
    have := (mul_eq_zero.mp hm).resolve_left (by linarith)
    linarith
  refine ⟨e1, ?_⟩
  have hw : w = 21 - u - v := by linarith
  rw [hw]
  linear_combination -q12

theorem key : PowerSeries.mk a *
    (7 * PowerSeries.X ^ 3 - 35 * PowerSeries.X ^ 2 + 21 * PowerSeries.X - 1) =
    -(35 * PowerSeries.X ^ 2 - 42 * PowerSeries.X + 3) := by
  set F := PowerSeries.mk a
  have e1 : F * (7 * PowerSeries.X ^ 3 - 35 * PowerSeries.X ^ 2 + 21 * PowerSeries.X - 1) =
      PowerSeries.C (7 : ℝ) * (PowerSeries.X ^ 3 * F) -
        PowerSeries.C (35 : ℝ) * (PowerSeries.X ^ 2 * F) +
        PowerSeries.C (21 : ℝ) * (PowerSeries.X ^ 1 * F) - F := by
    simp only [map_ofNat]
    ring
  have e2 : (-(35 * PowerSeries.X ^ 2 - 42 * PowerSeries.X + 3) : PowerSeries ℝ) =
      PowerSeries.C (42 : ℝ) * PowerSeries.X ^ 1 - PowerSeries.C (35 : ℝ) * PowerSeries.X ^ 2 -
        PowerSeries.C (3 : ℝ) * PowerSeries.X ^ 0 := by
    simp only [map_ofNat]
    ring
  obtain ⟨v1, v2⟩ := vieta
  have a0 : a 0 = 3 := by rw [a_eq]; norm_num
  have a1 : a 1 = 21 := by rw [a_eq]; simp only [pow_one]; exact v1
  have a2 : a 2 = 371 := by
    rw [a_eq]
    linear_combination (r (π / 14) + r (3 * π / 14) + r (5 * π / 14) + 21) * v1 - 2 * v2
  rw [e1, e2]
  ext n
  simp only [F, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 2
  · interval_cases n <;> norm_num [a0, a1, a2]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
    have hrec : a (j + 3) = 21 * a (j + 2) - 35 * a (j + 1) + 7 * a j := by
      rw [a_eq, a_eq, a_eq, a_eq]
      linear_combination r (π / 14) ^ j * h1 + r (3 * π / 14) ^ j * h2 + r (5 * π / 14) ^ j * h3
    simp
    linear_combination -hrec

end OMAA108716Helpers

open OMA.S_oeis_a108716 OMAA108716Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a108716.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
    rw [show j + 3 - 1 = j + 2 by omega, show j + 3 - 2 = j + 1 by omega,
      show j + 3 - 3 = j by omega, a_eq, a_eq, a_eq, a_eq]
    linear_combination r (Real.pi / 14) ^ j * h1 +
      r (3 * Real.pi / 14) ^ j * h2 + r (5 * Real.pi / 14) ^ j * h3
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    exact key
