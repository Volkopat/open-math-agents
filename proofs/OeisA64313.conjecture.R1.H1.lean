import OMAReductions.R_OeisA64313_conjecture_R1
import Mathlib

/-! With `x = π / n ≤ π / 5`, the two bounds are equivalent to `0 < D` and `π ^ 3 D < 0.724 x ^ 4 sin x`,
where `D = sin x (1 - x ^ 2 / 3) - x cos x`. Both follow from the Taylor bounds
`1 - x²/2 + x⁴/24 - x⁶/720 ≤ cos x ≤ 1 - x²/2 + x⁴/24` and
`x - x³/6 + x⁵/120 - x⁷/5040 ≤ sin x ≤ x - x³/6 + x⁵/120` (proved by integrating from
`Real.sin_ge_sub_cube`) together with `3.141592 < π < 3.141593`. -/

namespace OMA.Step_OeisA64313_conjecture_R1_H1

open Real

/-- A function vanishing at `0` with nonnegative derivative on `[0, ∞)` is nonnegative there. -/
theorem nonneg_of_deriv {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (h0 : f 0 = 0)
    (hd : ∀ x, 0 ≤ x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun y _ => (hf y).continuousAt.continuousWithinAt
    · exact fun y _ => (hf y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hf y).deriv]
      exact hd y (le_of_lt hy)
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  linarith

theorem cos_le (x : ℝ) (hx : 0 ≤ x) : cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have h := nonneg_of_deriv (f := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - cos x)
    (f' := fun x => -x + x ^ 3 / 6 + sin x) (fun y => by
      have := ((((hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_pow 2 y).div_const 2)).add
        ((hasDerivAt_pow 4 y).div_const 24)).sub (Real.hasDerivAt_cos y))
      convert this using 1 <;> first | rfl | (norm_num; ring)) (by simp) (fun y hy => by have := Real.sin_ge_sub_cube hy; linarith) hx
  linarith

theorem sin_le (x : ℝ) (hx : 0 ≤ x) : sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have h := nonneg_of_deriv (f := fun x => x - x ^ 3 / 6 + x ^ 5 / 120 - sin x)
    (f' := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - cos x) (fun y => by
      have := ((((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 6)).add
        ((hasDerivAt_pow 5 y).div_const 120)).sub (Real.hasDerivAt_sin y))
      convert this using 1 <;> first | rfl | (norm_num; ring)) (by simp) (fun y hy => by have := cos_le y hy; linarith) hx
  linarith

theorem le_cos (x : ℝ) (hx : 0 ≤ x) : 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ cos x := by
  have h := nonneg_of_deriv (f := fun x => cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720))
    (f' := fun x => x - x ^ 3 / 6 + x ^ 5 / 120 - sin x) (fun y => by
      have := (Real.hasDerivAt_cos y).sub ((((hasDerivAt_const y (1 : ℝ)).sub
        ((hasDerivAt_pow 2 y).div_const 2)).add ((hasDerivAt_pow 4 y).div_const 24)).sub
        ((hasDerivAt_pow 6 y).div_const 720))
      convert this using 1 <;> first | rfl | (norm_num; ring)) (by simp) (fun y hy => by have := sin_le y hy; linarith) hx
  linarith

theorem le_sin (x : ℝ) (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ sin x := by
  have h := nonneg_of_deriv (f := fun x => sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040))
    (f' := fun x => cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720)) (fun y => by
      have := (Real.hasDerivAt_sin y).sub ((((hasDerivAt_id y).sub
        ((hasDerivAt_pow 3 y).div_const 6)).add ((hasDerivAt_pow 5 y).div_const 120)).sub
        ((hasDerivAt_pow 7 y).div_const 5040))
      convert this using 1 <;> first | rfl | (norm_num; ring)) (by simp) (fun y hy => by have := le_cos y hy; linarith) hx
  linarith

theorem pi3_lo : 31 < π ^ 3 := by
  have := pow_lt_pow_left₀ Real.pi_gt_d6 (by norm_num) three_ne_zero
  norm_num at this ⊢
  linarith

theorem pi3_hi : π ^ 3 < 31.0063 := by
  have := pow_lt_pow_left₀ Real.pi_lt_d6 Real.pi_pos.le three_ne_zero
  norm_num at this ⊢
  linarith

theorem keyA (x : ℝ) (hx0 : 0 < x) (hx1 : x < 0.62832) :
    0 < sin x * (1 - x ^ 2 / 3) - cos x * x := by
  have L1 := cos_le x hx0.le
  have L4 := le_sin x hx0.le
  have hy : x ^ 2 < 0.39479 := by nlinarith
  have hq : 0 < 1 - x ^ 2 / 3 := by linarith
  have h1 : cos x * x ≤ (1 - x ^ 2 / 2 + x ^ 4 / 24) * x := mul_le_mul_of_nonneg_right L1 hx0.le
  have h2 : (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) * (1 - x ^ 2 / 3) ≤
      sin x * (1 - x ^ 2 / 3) := mul_le_mul_of_nonneg_right L4 hq.le
  have e : (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) * (1 - x ^ 2 / 3) -
      (1 - x ^ 2 / 2 + x ^ 4 / 24) * x = x ^ 5 * (1 / 45 - x ^ 2 / 336 + x ^ 4 / 15120) := by ring
  have hp : 0 < x ^ 5 * (1 / 45 - x ^ 2 / 336 + x ^ 4 / 15120) := by
    apply mul_pos (pow_pos hx0 5)
    have : 0 ≤ x ^ 4 := by positivity
    linarith
  linarith

theorem keyB (x : ℝ) (hx0 : 0 < x) (hx1 : x < 0.62832) :
    π ^ 3 * (sin x * (1 - x ^ 2 / 3) - cos x * x) < 0.724 * sin x * x ^ 4 := by
  have L2 := sin_le x hx0.le
  have L3 := le_cos x hx0.le
  have L5 := Real.sin_ge_sub_cube hx0.le
  have hy : x ^ 2 < 0.39479 := by nlinarith
  have hq : 0 < 1 - x ^ 2 / 3 := by linarith
  have h4 : sin x * (1 - x ^ 2 / 3) ≤ (x - x ^ 3 / 6 + x ^ 5 / 120) * (1 - x ^ 2 / 3) :=
    mul_le_mul_of_nonneg_right L2 hq.le
  have h5 : (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) * x ≤ cos x * x :=
    mul_le_mul_of_nonneg_right L3 hx0.le
  have e2 : (x - x ^ 3 / 6 + x ^ 5 / 120) * (1 - x ^ 2 / 3) -
      (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) * x = x ^ 5 * (1 / 45 - x ^ 2 / 720) := by ring
  have hDle : sin x * (1 - x ^ 2 / 3) - cos x * x ≤ x ^ 5 * (1 / 45 - x ^ 2 / 720) := by linarith
  have hP3lo := pi3_lo
  have hP3hi := pi3_hi
  have hB0 : 0 ≤ 0.724 / 6 - π ^ 3 / 720 := by linarith
  have hB1 : 0.724 / 6 - π ^ 3 / 720 ≤ 0.0777 := by linarith
  have hyB : x ^ 2 * (0.724 / 6 - π ^ 3 / 720) ≤ 0.39479 * 0.0777 :=
    mul_le_mul hy.le hB1 hB0 (by norm_num)
  have hbr : 0 < 0.724 * (1 - x ^ 2 / 6) - π ^ 3 * (1 / 45 - x ^ 2 / 720) := by
    have e3 : 0.724 * (1 - x ^ 2 / 6) - π ^ 3 * (1 / 45 - x ^ 2 / 720) =
        (0.724 - π ^ 3 / 45) - x ^ 2 * (0.724 / 6 - π ^ 3 / 720) := by ring
    rw [e3]
    linarith
  have hx5 : 0 < x ^ 5 := pow_pos hx0 5
  have m1 : π ^ 3 * (sin x * (1 - x ^ 2 / 3) - cos x * x) ≤
      π ^ 3 * (x ^ 5 * (1 / 45 - x ^ 2 / 720)) :=
    mul_le_mul_of_nonneg_left hDle (by positivity)
  have m2 : π ^ 3 * (x ^ 5 * (1 / 45 - x ^ 2 / 720)) < 0.724 * (x - x ^ 3 / 6) * x ^ 4 := by
    have h := mul_pos hx5 hbr
    have e4 : x ^ 5 * (0.724 * (1 - x ^ 2 / 6) - π ^ 3 * (1 / 45 - x ^ 2 / 720)) =
        0.724 * (x - x ^ 3 / 6) * x ^ 4 - π ^ 3 * (x ^ 5 * (1 / 45 - x ^ 2 / 720)) := by ring
    linarith
  have m3 : 0.724 * (x - x ^ 3 / 6) * x ^ 4 ≤ 0.724 * sin x * x ^ 4 := by
    have : 0 ≤ x ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_right L5 this
    linarith
  linarith

theorem bounds (n : ℕ) (hn : 5 ≤ n) :
    (n : ℝ) ^ 2 / (4 * π) - π / 12 - 181 / 1000 / (n : ℝ) ^ 2 < OeisA64313.area n ∧
      OeisA64313.area n < (n : ℝ) ^ 2 / (4 * π) - π / 12 := by
  have hN5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpi2 := Real.pi_lt_d6
  have hpipos := Real.pi_pos
  set N : ℝ := (n : ℝ) with hNdef
  set x : ℝ := π / N with hxdef
  have hNpos : 0 < N := by linarith
  have hx0 : 0 < x := div_pos hpipos hNpos
  have hxle : x ≤ π / 5 := div_le_div_of_nonneg_left hpipos.le (by norm_num) hN5
  have hx1 : x < 0.62832 := by linarith
  have hNx : N = π / x := by rw [hxdef]; field_simp
  have hs : 0 < sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith)
  have hc : 0 < cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have harea : OeisA64313.area n = N * cos x / (4 * sin x) := by
    unfold OeisA64313.area
    rw [← hNdef, ← hxdef, Real.tan_eq_sin_div_cos]
    field_simp
  have kA := keyA x hx0 hx1
  have kB := keyB x hx0 hx1
  constructor
  · have hid : OeisA64313.area n - (N ^ 2 / (4 * π) - π / 12 - 181 / 1000 / N ^ 2) =
        (0.724 * sin x * x ^ 4 - π ^ 3 * (sin x * (1 - x ^ 2 / 3) - cos x * x)) /
          (4 * sin x * x ^ 2 * π ^ 2) := by
      rw [harea, hNx]
      field_simp
      ring
    have : 0 < (0.724 * sin x * x ^ 4 - π ^ 3 * (sin x * (1 - x ^ 2 / 3) - cos x * x)) /
        (4 * sin x * x ^ 2 * π ^ 2) := div_pos (by linarith) (by positivity)
    linarith
  · have hid : N ^ 2 / (4 * π) - π / 12 - OeisA64313.area n =
        π * (sin x * (1 - x ^ 2 / 3) - cos x * x) / (4 * sin x * x ^ 2) := by
      rw [harea, hNx]
      field_simp
      ring
    have : 0 < π * (sin x * (1 - x ^ 2 / 3) - cos x * x) / (4 * sin x * x ^ 2) :=
      div_pos (mul_pos hpipos kA) (by positivity)
    linarith

end OMA.Step_OeisA64313_conjecture_R1_H1

theorem OMA.solution : OMA.R_OeisA64313_conjecture_R1.H1 :=
  OMA.Step_OeisA64313_conjecture_R1_H1.bounds
