import OMAReductions.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R2
import Mathlib

/-
The certified critical-line zero in (14.13, 14.14) is adapted from
https://github.com/teal-sea/zeta-lab/tree/91848c0c0c387179a54784e3c3b7d4252414bb43/hunts/hardy_first_zero.
Its supporting modules are combined here for the challenge's single-file checker.
The final minimum-height argument follows the reduction in open-math-agents PR 2872.

MIT License

Copyright (c) 2026 Thomas Lince

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
section








open Complex
open scoped ComplexConjugate

/--
Hardy's Z function.

Defined using the completed Riemann zeta function `Λ(s)` to avoid
needing a continuous branch of `log Γ` along the critical line.
Since `Λ(1/2 + it)` is real, we divide by the positive real factor
`π^(-1/4) * ‖Γ(1/4 + I*t/2)‖` to obtain `Z(t)`.

Note: The goal is to eventually type this as `ℝ → ℝ` if preferred by Mathlib,
but here we start with the definition over `ℂ` or returning `ℂ` for easier
algebra before extracting the real part or proving it's real.
-/
noncomputable def hardyZ (t : ℝ) : ℂ :=
  completedRiemannZeta (1/2 + t * I) /
    ( (Real.pi : ℂ) ^ (-(1/4 : ℝ) : ℂ) * ‖Gamma (1/4 + t / 2 * I)‖ )

lemma Gammaℝ_conj (s : ℂ) : conj (Gammaℝ s) = Gammaℝ (conj s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Gamma_conj]
  have hpi : (↑Real.pi : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_pos.ne
  have h1 := (cpow_conj (↑Real.pi) (-s/2) hpi).symm
  rw [conj_ofReal] at h1
  rw [h1]
  congr 1
  · congr 1
    rw [map_div₀, map_neg]
    congr 2
    exact map_ofNat (starRingEnd ℂ) 2
  · congr 1
    rw [map_div₀]
    congr 1
    exact map_ofNat (starRingEnd ℂ) 2

lemma completedRiemannZeta_conj_half (t : ℝ) :
    conj (completedRiemannZeta (1/2 + t * I)) = completedRiemannZeta (1/2 - t * I) := by
  let s : ℂ := 1/2 + t * I
  have hs_re : 0 < s.re := by
    dsimp [s]; simp
  have hcs_re : 0 < (conj s).re := by
    rw [conj_re]; exact hs_re
  have H1 : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    have h_s_ne_zero : s ≠ 0 := by
      intro h
      have : s.re = 0 := by rw [h, zero_re]
      linarith
    rw [riemannZeta_def_of_ne_zero h_s_ne_zero]
    exact (div_mul_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hs_re)).symm
  have H2 : completedRiemannZeta (conj s) = riemannZeta (conj s) * Gammaℝ (conj s) := by
    have h_s_ne_zero : conj s ≠ 0 := by
      intro h
      have : (conj s).re = 0 := by rw [h, zero_re]
      linarith
    rw [riemannZeta_def_of_ne_zero h_s_ne_zero]
    exact (div_mul_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hcs_re)).symm
  have h_conj_s : conj (1/2 + (t:ℂ) * I) = 1/2 - t * I := by
    apply Complex.ext <;> simp
  rw [← h_conj_s]
  change conj (completedRiemannZeta s) = completedRiemannZeta (conj s)
  rw [H1, H2, map_mul, ← riemannZeta_conj, Gammaℝ_conj]

/-- `Z t` is strictly real. -/
lemma hardyZ_is_real (t : ℝ) : ∃ (r : ℝ), hardyZ t = r := by
  use (hardyZ t).re
  symm
  apply conj_eq_iff_re.mp
  dsimp [hardyZ]
  rw [map_div₀, completedRiemannZeta_conj_half]
  congr 1
  · have h_symm : 1/2 - (t:ℂ) * I = 1 - (1/2 + (t:ℂ) * I) := by ring
    rw [h_symm, completedRiemannZeta_one_sub]
  · rw [map_mul]
    congr 1
    · have hpi : (↑Real.pi : ℂ).arg ≠ Real.pi := by
        rw [arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_pos.ne
      have h1 := (cpow_conj (↑Real.pi) (-(1/4:ℝ)) hpi).symm
      rw [conj_ofReal, map_neg, conj_ofReal] at h1
      exact h1
    · exact conj_ofReal _

/-- The absolute value of `Z t` is exactly the absolute value of `ζ(1/2 + it)`. -/
lemma abs_hardyZ_eq_abs_zeta (t : ℝ) : ‖hardyZ t‖ = ‖riemannZeta (1/2 + t * I)‖ := by
  dsimp [hardyZ]
  rw [norm_div]
  let s : ℂ := 1/2 + t * I
  have hs_re : 0 < s.re := by
    dsimp [s]
    norm_num
  have h_s_ne_zero : s ≠ 0 := by
    intro h
    have h_re : s.re = 0 := by rw [h, zero_re]
    dsimp [s] at h_re
    norm_num at h_re
  have H1 : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    rw [riemannZeta_def_of_ne_zero h_s_ne_zero]
    exact (div_mul_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hs_re)).symm
  rw [H1, norm_mul]
  have H3 : ‖(↑Real.pi : ℂ) ^ (-(1/4 : ℝ) : ℂ) * (‖Gamma (1/4 + ↑t / 2 * I)‖ : ℂ)‖ = ‖Gammaℝ s‖ := by
    rw [Gammaℝ_def, norm_mul, norm_mul]
    congr 1
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      congr 1
      have H_re : (-(1/4 : ℝ) : ℂ).re = (-s/2).re := by
        dsimp [s]; simp; norm_num
      exact H_re
    · rw [Complex.norm_of_nonneg (norm_nonneg _)]
      congr 1
      have H_eq : 1/4 + (t:ℂ) / 2 * I = s / 2 := by
        dsimp [s]; apply Complex.ext <;> simp <;> ring
      rw [H_eq]
  rw [H3, mul_div_cancel_right₀]
  rw [norm_ne_zero_iff]
  exact Gammaℝ_ne_zero_of_re_pos hs_re

/-- `Z t` is an even function. -/
lemma hardyZ_even (t : ℝ) : hardyZ (-t) = hardyZ t := by
  unfold hardyZ
  push_cast
  have H_num : completedRiemannZeta (1/2 + -(t:ℂ) * I) = completedRiemannZeta (1/2 + t * I) := by
    have H : 1/2 + -(t:ℂ) * I = 1 - (1/2 + (t:ℂ) * I) := by ring
    rw [H, completedRiemannZeta_one_sub]
  rw [H_num]
  congr 1
  congr 1
  have H_den : 1/4 + -(t:ℂ) / 2 * I = conj (1/4 + (t:ℂ) / 2 * I) := by
    apply Complex.ext_iff.mpr
    constructor
    · rw [Complex.conj_re]
      simp
    · rw [Complex.conj_im]
      simp; ring
  rw [H_den, Gamma_conj, Complex.norm_conj]

/-- `Z t` is zero if and only if `ζ(1/2 + it)` is zero. -/
lemma hardyZ_zero_iff (t : ℝ) : hardyZ t = 0 ↔ riemannZeta (1/2 + t * I) = 0 := by
  have h1 : hardyZ t = 0 ↔ ‖hardyZ t‖ = 0 := norm_eq_zero.symm
  have h2 : riemannZeta (1/2 + (t:ℂ) * I) = 0 ↔ ‖riemannZeta (1/2 + (t:ℂ) * I)‖ = 0 := norm_eq_zero.symm
  rw [h1, h2, abs_hardyZ_eq_abs_zeta]

/-- `Z t` is continuous. -/
lemma continuous_hardyZ : Continuous hardyZ := by
  apply continuous_iff_continuousAt.mpr
  intro x
  unfold hardyZ
  apply ContinuousAt.div
  · let f (t : ℝ) : ℂ := 1/2 + (t : ℂ) * I
    have h1 : ContinuousAt f x := by
      have h_cont : Continuous f := by
        refine continuous_const.add ?_
        refine Continuous.mul continuous_ofReal continuous_const
      exact h_cont.continuousAt
    have hs0 : f x ≠ 0 := by
      intro h; have h_re : (f x).re = 0 := by rw [h, zero_re]
      dsimp [f] at h_re; norm_num at h_re
    have hs1 : f x ≠ 1 := by
      intro h; have h_re : (f x).re = 1 := by rw [h, one_re]
      dsimp [f] at h_re; norm_num at h_re
    exact (differentiableAt_completedZeta hs0 hs1).continuousAt.comp h1
  · have H_const : ContinuousAt (fun (t : ℝ) => (↑Real.pi : ℂ) ^ (-(1 / 4 : ℝ) : ℂ)) x := continuousAt_const
    let f (t : ℝ) : ℂ := 1 / 4 + (t : ℂ) / 2 * I
    have H_arg : ContinuousAt f x := by
      have h_cont : Continuous f := by
        refine continuous_const.add ?_
        refine Continuous.mul ?_ continuous_const
        refine Continuous.div continuous_ofReal continuous_const ?_
        intro _; exact two_ne_zero
      exact h_cont.continuousAt
    have H_gamma : ContinuousAt (fun (t : ℝ) => (‖Gamma (f t)‖ : ℂ)) x := by
      have hc1 : ContinuousAt Gamma (f x) := by
        apply continuousAt_Gamma
        intro m h_eq
        have h_re : (f x).re = (-m : ℂ).re := by rw [h_eq]
        dsimp [f] at h_re; simp at h_re
        have hm : (m : ℝ) ≥ 0 := Nat.cast_nonneg m
        linarith
      exact continuous_ofReal.continuousAt.comp (continuous_norm.continuousAt.comp (hc1.comp H_arg))
    exact H_const.mul H_gamma
  · intro h
    let f (t : ℝ) : ℂ := 1 / 4 + (t : ℂ) / 2 * I
    have h_mul : (↑Real.pi : ℂ) ^ (-(1 / 4 : ℝ) : ℂ) * (‖Gamma (f x)‖ : ℂ) = 0 := h
    rw [mul_eq_zero] at h_mul
    cases h_mul with
    | inl h_pi =>
      have H_pi_ne : (↑Real.pi : ℂ) ^ (-(1 / 4 : ℝ) : ℂ) ≠ 0 := by
        intro h_eq
        have h_norm : ‖(↑Real.pi : ℂ) ^ (-(1 / 4 : ℝ) : ℂ)‖ = 0 := by rw [h_eq, norm_zero]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos] at h_norm
        have h_re : (-(1 / 4 : ℝ) : ℂ).re = -1 / 4 := by norm_num
        rw [h_re] at h_norm
        have h_pos : (Real.pi : ℝ) ^ (-1/4 : ℝ) > 0 := Real.rpow_pos_of_pos Real.pi_pos _
        linarith
      exact H_pi_ne h_pi
    | inr h_gamma =>
      have H_g_norm_zero : ‖Gamma (f x)‖ = 0 := by
        exact (Complex.ofReal_eq_zero).mp h_gamma
      rw [norm_eq_zero] at H_g_norm_zero
      have H_g_ne_zero : Gamma (f x) ≠ 0 := by
        apply Gamma_ne_zero
        intro m h_eq
        have h_re : (f x).re = (-m : ℂ).re := by rw [h_eq]
        dsimp [f] at h_re; simp at h_re
        have hm : (m : ℝ) ≥ 0 := Nat.cast_nonneg m
        linarith
      exact H_g_ne_zero H_g_norm_zero

/-!
### The real-valued Z

`hardyZ_is_real` proves every value of `hardyZ` equals some real number, but
`hardyZ` itself is still typed `ℝ → ℂ`: the docstring at the top of this file
flagged that as provisional (“the goal is to eventually type this as
`ℝ → ℝ`”). This section meets that goal, purely additively: `hardyZReal` and
everything below are *derived* from the five lemmas above via the coercion
`ℝ → ℂ`, without editing a single one of them, so nothing already
kernel-checked is put at risk by this section existing.
-/

/-- Hardy's Z, retyped `ℝ → ℝ` now that `hardyZ_is_real` is proved. -/
noncomputable def hardyZReal (t : ℝ) : ℝ := (hardyZ t).re

/-- `hardyZReal` and `hardyZ` agree under the standard `ℝ → ℂ` coercion. -/
lemma hardyZReal_eq_hardyZ (t : ℝ) : (hardyZReal t : ℂ) = hardyZ t := by
  obtain ⟨r, hr⟩ := hardyZ_is_real t
  unfold hardyZReal
  rw [hr, Complex.ofReal_re]

/-- The real-valued Z has the same magnitude as `ζ(1/2 + it)`. -/
lemma abs_hardyZReal_eq_abs_zeta (t : ℝ) :
    |hardyZReal t| = ‖riemannZeta (1/2 + t * I)‖ := by
  rw [← abs_hardyZ_eq_abs_zeta t, ← hardyZReal_eq_hardyZ t, Complex.norm_real,
    Real.norm_eq_abs]

/-- `hardyZReal` is even. -/
lemma hardyZReal_even (t : ℝ) : hardyZReal (-t) = hardyZReal t := by
  have h : (hardyZReal (-t) : ℂ) = (hardyZReal t : ℂ) := by
    rw [hardyZReal_eq_hardyZ, hardyZReal_eq_hardyZ, hardyZ_even]
  exact_mod_cast h

/-- `hardyZReal t = 0` iff `ζ(1/2 + it) = 0`. -/
lemma hardyZReal_zero_iff (t : ℝ) :
    hardyZReal t = 0 ↔ riemannZeta (1/2 + t * I) = 0 := by
  rw [← hardyZ_zero_iff t, ← hardyZReal_eq_hardyZ t, Complex.ofReal_eq_zero]

/-- `hardyZReal` is continuous. -/
lemma continuous_hardyZReal : Continuous hardyZReal :=
  Complex.continuous_re.comp continuous_hardyZ

end

section






/-!
# The sign test behind the first zero (hunt `hardy_first_zero`)

The reduction this hunt's Lean plan rests on, kernel-checked: a zero of `ζ` on
the critical line between `a` and `b` follows from two inequalities, and neither
of them asks for the value of the Riemann-Siegel phase.

* `hX`: `Re (ζ(1/2 + ia) · conj ζ(1/2 + ib)) < 0`, a statement about two values
  of `ζ` that an Euler-Maclaurin enclosure can decide;
* `hG`: `0 < Re (Γℝ(1/2 + ia) · conj Γℝ(1/2 + ib))`, which says only that the
  phase of `Γℝ` turns by less than a quarter turn between `a` and `b`.

Why that suffices: `hardyZ t = Λ(1/2 + it) / d(t)` with `d(t) > 0`
(`ZetaLean/HardyZ.lean`), and `Λ = ζ · Γℝ` off the poles, so
`Z(a) Z(b) d(a) d(b) = X G` with `X` and `G` the two products above. The left
side is real, so multiplying by `conj X` and taking real parts gives
`Z(a) Z(b) d(a) d(b) Re X = ‖X‖² Re G > 0`, hence `Z(a) Z(b) < 0`, and the
intermediate value theorem on the continuous real `hardyZReal` finishes.

Nothing here is numerical. The two hypotheses are the open work: `hX` needs an
evaluation of `ζ` with a proved error bound, `hG` a crude bound on the phase
of `Γ` (`RESULTS.md`, routes E and P).
-/

open Complex
open scoped ComplexConjugate

namespace HardyFirstZero

/-- The critical-line point `1/2 + it`. -/
noncomputable abbrev sOf (t : ℝ) : ℂ := 1 / 2 + t * I

lemma sOf_re (t : ℝ) : (sOf t).re = 1 / 2 := by simp [sOf]

lemma sOf_ne_zero (t : ℝ) : sOf t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [sOf_re, Complex.zero_re] at this
  norm_num at this

/-- `Λ(1/2 + it) = ζ(1/2 + it) · Γℝ(1/2 + it)`. -/
lemma completed_eq (t : ℝ) :
    completedRiemannZeta (sOf t) = riemannZeta (sOf t) * Gammaℝ (sOf t) := by
  have hre : 0 < (sOf t).re := by rw [sOf_re]; norm_num
  rw [riemannZeta_def_of_ne_zero (sOf_ne_zero t)]
  exact (div_mul_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hre)).symm

/-- The positive real denominator of `hardyZ`. -/
noncomputable def den (t : ℝ) : ℝ := Real.pi ^ (-(1 / 4 : ℝ)) * ‖Gamma (1 / 4 + t / 2 * I)‖

lemma den_pos (t : ℝ) : 0 < den t := by
  unfold den
  refine mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (norm_pos_iff.mpr ?_)
  apply Gamma_ne_zero_of_re_pos
  simp

lemma hardyZ_eq (t : ℝ) : hardyZ t = completedRiemannZeta (sOf t) / ((den t : ℝ) : ℂ) := by
  unfold hardyZ den sOf
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_cpow Real.pi_pos.le, Complex.ofReal_neg]

/-- `Z(a) Z(b) d(a) d(b) = (ζ_a conj ζ_b) (Γℝ_a conj Γℝ_b)`, as complex numbers. -/
lemma hardyZReal_mul (a b : ℝ) :
    ((hardyZReal a * hardyZReal b : ℝ) : ℂ) * ((den a * den b : ℝ) : ℂ)
      = (riemannZeta (sOf a) * conj (riemannZeta (sOf b)))
        * (Gammaℝ (sOf a) * conj (Gammaℝ (sOf b))) := by
  have hb : ((hardyZReal b : ℝ) : ℂ) = conj (hardyZ b) := by
    rw [← hardyZReal_eq_hardyZ b, Complex.conj_ofReal]
  have hda : ((den a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (den_pos a).ne'
  have hdb : ((den b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (den_pos b).ne'
  rw [Complex.ofReal_mul, Complex.ofReal_mul, hb, hardyZReal_eq_hardyZ a, hardyZ_eq a,
    hardyZ_eq b, map_div₀, Complex.conj_ofReal, completed_eq a, completed_eq b, map_mul]
  field_simp

/-- The algebraic core: a real `P` with `P d = X G`, `d > 0`, `Re X < 0` and
`Re G > 0` is negative. -/
lemma neg_of_mul_eq {P d : ℝ} {X G : ℂ} (hd : 0 < d) (h : (P : ℂ) * (d : ℂ) = X * G)
    (hX : X.re < 0) (hG : 0 < G.re) : P < 0 := by
  have h2 : (P : ℂ) * (d : ℂ) * conj X = ((‖X‖ ^ 2 : ℝ) : ℂ) * G := by
    rw [h, Complex.ofReal_pow, ← Complex.mul_conj']
    ring
  have h3 := congrArg Complex.re h2
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, zero_mul, mul_zero, add_zero, sub_zero] at h3
  have hX0 : X ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hX
    exact lt_irrefl 0 hX
  have hn : 0 < ‖X‖ ^ 2 := by positivity
  have hrhs : 0 < ‖X‖ ^ 2 * G.re := mul_pos hn hG
  -- `P d Re X > 0` with `d > 0` and `Re X < 0` forces `P < 0`
  by_contra hP
  replace hP := not_lt.mp hP
  have : P * d * X.re ≤ 0 := by
    have hPd : 0 ≤ P * d := mul_nonneg hP hd.le
    exact mul_nonpos_of_nonneg_of_nonpos hPd hX.le
  linarith

/-- **The sign test.** Two inequalities, one about `ζ` and one about `Γℝ`,
give a zero of `ζ` on the critical line strictly between `a` and `b`. -/
theorem exists_zero_of_sign_data {a b : ℝ} (hab : a < b)
    (hX : (riemannZeta (sOf a) * conj (riemannZeta (sOf b))).re < 0)
    (hG : 0 < (Gammaℝ (sOf a) * conj (Gammaℝ (sOf b))).re) :
    ∃ t ∈ Set.Ioo a b, riemannZeta (1 / 2 + t * I) = 0 := by
  have hP : hardyZReal a * hardyZReal b < 0 :=
    neg_of_mul_eq (mul_pos (den_pos a) (den_pos b)) (hardyZReal_mul a b) hX hG
  have hc : ContinuousOn hardyZReal (Set.Icc a b) := continuous_hardyZReal.continuousOn
  rcases mul_neg_iff.mp hP with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo' hab.le hc ⟨hb, ha⟩
    exact ⟨t, ht, (hardyZReal_zero_iff t).mp h0⟩
  · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo hab.le hc ⟨ha, hb⟩
    exact ⟨t, ht, (hardyZReal_zero_iff t).mp h0⟩

end HardyFirstZero

end

section









/-!
# The phase of `Γℝ` turns slowly (hunt `hardy_first_zero`, route P)

`Spine.lean` reduces the first zero to two inequalities. This file proves the one
about `Γ`, for any `0 < a < b` whose gap is small enough, with no evaluation of
`Γ` anywhere:

    0 < Re (Γℝ(1/2 + ia) · conj Γℝ(1/2 + ib)).

**The route.** Write `z = 1/4 + ia/2`, `w = 1/4 - ib/2`, `δ = (b - a)/2`,
`K = ab/4` and `c_j = j + 1/4`. Up to the positive factor `π^{-1/2}`, the
product is `V = π^{iδ} Γ(z) Γ(w)`, and Euler's limit (`Complex.GammaSeq_tendsto_Gamma`)
gives `V = lim V_n` with `V_n = π^{iδ} GammaSeq z n · GammaSeq w n`. Each `V_n` is
explicit: `(z + j)(w + j) = (c_j² + K) - i δ c_j`, so

    V_n = R_n · exp(i φ_n),   φ_n = δ log π - δ log n + Σ_{j ≤ n} arctan(δ c_j / (c_j² + K)),

with `R_n > 0`. Elementary bounds (`arctan x ≤ x`, `arctan x ≥ x - x³`, the
harmonic-number bounds of `Mathlib.NumberTheory.Harmonic.Bounds`, `Σ 1/j² ≤ 2`)
confine every `φ_n`, `n ≥ 1`, to `[-(δ(1 + 2K) + 66 δ³), δ(π + 4)]`, so
`Re V_n ≥ cos L · ‖V_n‖` with `L < π/2`, and the inequality survives the limit.

The window is crude on purpose: at `a = 14.13`, `b = 14.14` the true phase
increment is `-0.00405` while the window is `[-0.5045, 0.0357]`. Nothing here
needs the digamma function or Stirling's formula.
-/

open Complex Finset Filter
open scoped ComplexConjugate Topology

namespace HardyFirstZero

/-! ### One factor in polar form -/

/-- `A - iB = √(A² + B²) · exp(-i · arctan(B/A))` for `A > 0`. -/
lemma polar_of_re_pos {A B : ℝ} (hA : 0 < A) :
    ((A : ℂ) - (B : ℂ) * I)
      = ((Real.sqrt (A ^ 2 + B ^ 2) : ℝ) : ℂ) * exp (-(Real.arctan (B / A) : ℂ) * I) := by
  set θ := Real.arctan (B / A) with hθ
  have hsq : Real.sqrt (A ^ 2 + B ^ 2) = A * Real.sqrt (1 + (B / A) ^ 2) := by
    rw [show A ^ 2 + B ^ 2 = A ^ 2 * (1 + (B / A) ^ 2) by field_simp,
      Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA.le]
  have hs1 : 0 < Real.sqrt (1 + (B / A) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hcos : Real.cos θ = 1 / Real.sqrt (1 + (B / A) ^ 2) := Real.cos_arctan _
  have hsin : Real.sin θ = B / A / Real.sqrt (1 + (B / A) ^ 2) := Real.sin_arctan _
  have hexp : exp (-(θ : ℂ) * I) = ((Real.cos θ : ℝ) : ℂ) - ((Real.sin θ : ℝ) : ℂ) * I := by
    rw [show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hexp, hcos, hsin, hsq]
  apply Complex.ext <;> simp <;> field_simp

/-! ### The data of the partial products -/

/-- `δ = (b - a)/2`. -/
noncomputable def dl (a b : ℝ) : ℝ := (b - a) / 2

/-- `c_j = j + 1/4`. -/
noncomputable def cj (j : ℕ) : ℝ := j + 1 / 4

/-- `A_j = c_j² + ab/4`, the real part of `(z + j)(w + j)`. -/
noncomputable def Aj (a b : ℝ) (j : ℕ) : ℝ := cj j ^ 2 + a * b / 4

/-- The phase contributed by the `j`-th factor. -/
noncomputable def psi (a b : ℝ) (j : ℕ) : ℝ := Real.arctan (dl a b * cj j / Aj a b j)

/-- The modulus of the `j`-th factor. -/
noncomputable def rj (a b : ℝ) (j : ℕ) : ℝ := Real.sqrt (Aj a b j ^ 2 + (dl a b * cj j) ^ 2)

/-- The partial phase `φ_n = δ log π - δ log n + Σ_{j ≤ n} ψ_j`. -/
noncomputable def phi (a b : ℝ) (n : ℕ) : ℝ :=
  dl a b * Real.log Real.pi - dl a b * Real.log n + ∑ j ∈ range (n + 1), psi a b j

/-- `z = 1/4 + ia/2`, half of `1/2 + ia`. -/
noncomputable def zA (a : ℝ) : ℂ := 1 / 4 + ((a / 2 : ℝ) : ℂ) * I

/-- `w = 1/4 - ib/2`, the conjugate of half of `1/2 + ib`. -/
noncomputable def wB (b : ℝ) : ℂ := 1 / 4 - ((b / 2 : ℝ) : ℂ) * I

/-- The constant `π^{-1/2 + iδ}`, written as an exponential. -/
noncomputable def cpi (a b : ℝ) : ℂ :=
  exp ((Real.log Real.pi : ℂ) * (-(1 / 2) + (dl a b : ℂ) * I))

lemma cj_pos (j : ℕ) : 0 < cj j := by unfold cj; positivity

lemma Aj_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (j : ℕ) : 0 < Aj a b j := by
  unfold Aj; have := cj_pos j; positivity

lemma zA_re (a : ℝ) : (zA a).re = 1 / 4 := by simp [zA]

lemma wB_re (b : ℝ) : (wB b).re = 1 / 4 := by simp [wB]

/-- `(z + j)(w + j) = A_j - i δ c_j`. -/
lemma factor_eq (a b : ℝ) (j : ℕ) :
    (zA a + j) * (wB b + j) = (Aj a b j : ℂ) - ((dl a b * cj j : ℝ) : ℂ) * I := by
  unfold zA wB Aj dl cj
  push_cast
  linear_combination (-(a : ℂ) * b / 4) * Complex.I_sq

/-- Each factor in polar form. -/
lemma factor_polar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (j : ℕ) :
    (zA a + j) * (wB b + j) = (rj a b j : ℂ) * exp (-(psi a b j : ℂ) * I) := by
  rw [factor_eq]
  exact polar_of_re_pos (Aj_pos ha hb j)

/-- The product of the factors in polar form. -/
lemma prod_polar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (∏ j ∈ range (n + 1), (zA a + j)) * (∏ j ∈ range (n + 1), (wB b + j))
      = ((∏ j ∈ range (n + 1), rj a b j : ℝ) : ℂ)
        * exp (-(((∑ j ∈ range (n + 1), psi a b j : ℝ)) : ℂ) * I) := by
  rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun j _ => factor_polar ha hb j),
    Finset.prod_mul_distrib, Complex.ofReal_prod]
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]

/-- `n^z n^w = exp(log n · (1/2 - iδ))` for `n ≥ 1`. -/
lemma cpow_pair {n : ℕ} (hn : n ≠ 0) (a b : ℝ) :
    (n : ℂ) ^ zA a * (n : ℂ) ^ wB b
      = exp ((Real.log n : ℂ) * (1 / 2 - (dl a b : ℂ) * I)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [← cpow_add _ _ hn', cpow_def_of_ne_zero hn', ← Complex.natCast_log]
  congr 1
  unfold zA wB dl
  push_cast
  ring

/-- The partial product `V_n = π^{-1/2+iδ} GammaSeq z n · GammaSeq w n`. -/
noncomputable def Vn (a b : ℝ) (n : ℕ) : ℂ :=
  cpi a b * (GammaSeq (zA a) n * GammaSeq (wB b) n)

lemma factor_ne_zero_A (a : ℝ) (j : ℕ) : zA a + j ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [zA] at this
  linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

lemma factor_ne_zero_B (b : ℝ) (j : ℕ) : wB b + j ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [wB] at this
  linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-- **`V_n` in polar form**: a positive real times `exp(x + iφ_n)`. -/
lemma Vn_polar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {n : ℕ} (hn : n ≠ 0) :
    Vn a b n = (((n.factorial : ℝ) ^ 2 / ∏ j ∈ range (n + 1), rj a b j : ℝ) : ℂ)
      * exp (((Real.log n - Real.log Real.pi) / 2 : ℝ) + (phi a b n : ℂ) * I) := by
  have hPA : (∏ j ∈ range (n + 1), (zA a + j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => factor_ne_zero_A a j
  have hPB : (∏ j ∈ range (n + 1), (wB b + j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => factor_ne_zero_B b j
  have hr : (((∏ j ∈ range (n + 1), rj a b j : ℝ)) : ℂ) ≠ 0 := by
    have hpp := prod_polar ha hb n
    intro h0
    rw [h0, zero_mul] at hpp
    exact mul_ne_zero hPA hPB hpp
  have hsplit : Vn a b n
      = cpi a b * ((n : ℂ) ^ zA a * (n : ℂ) ^ wB b) * ((n.factorial : ℂ) ^ 2)
        / ((∏ j ∈ range (n + 1), (zA a + j)) * (∏ j ∈ range (n + 1), (wB b + j))) := by
    unfold Vn GammaSeq
    field_simp
  rw [hsplit, cpow_pair hn, prod_polar ha hb n]
  have hE : ((((Real.log n - Real.log Real.pi) / 2 : ℝ) : ℂ) + (phi a b n : ℂ) * I)
      = (Real.log Real.pi : ℂ) * (-(1 / 2) + (dl a b : ℂ) * I)
        + ((Real.log n : ℂ) * (1 / 2 - (dl a b : ℂ) * I)
        + ((∑ j ∈ range (n + 1), psi a b j : ℝ) : ℂ) * I) := by
    unfold phi
    push_cast
    ring
  rw [hE, Complex.exp_add, Complex.exp_add, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_natCast]
  unfold cpi
  set X := exp ((Real.log Real.pi : ℂ) * (-(1 / 2) + (dl a b : ℂ) * I))
  set Y := exp ((Real.log n : ℂ) * (1 / 2 - (dl a b : ℂ) * I))
  set Θ : ℂ := ((∑ j ∈ range (n + 1), psi a b j : ℝ) : ℂ)
  set P : ℂ := ((∏ j ∈ range (n + 1), rj a b j : ℝ) : ℂ)
  have hinv : exp (Θ * I) = (exp (-Θ * I))⁻¹ := by
    rw [← Complex.exp_neg, neg_mul, neg_neg]
  have hne : exp (-Θ * I) ≠ 0 := Complex.exp_ne_zero _
  rw [hinv]
  field_simp

/-- `Re (R e^{x + iy}) = ‖R e^{x + iy}‖ cos y` for `R ≥ 0`. -/
lemma re_eq_norm_mul_cos {R : ℝ} (hR : 0 ≤ R) (x y : ℝ) :
    ((R : ℂ) * exp ((x : ℂ) + (y : ℂ) * I)).re
      = ‖(R : ℂ) * exp ((x : ℂ) + (y : ℂ) * I)‖ * Real.cos y := by
  rw [Complex.re_ofReal_mul, Complex.exp_re, norm_mul, Complex.norm_exp, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hR]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
    Complex.mul_im, zero_add]
  ring

lemma Vn_re {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {n : ℕ} (hn : n ≠ 0) :
    (Vn a b n).re = ‖Vn a b n‖ * Real.cos (phi a b n) := by
  have hR : 0 ≤ (n.factorial : ℝ) ^ 2 / ∏ j ∈ range (n + 1), rj a b j :=
    div_nonneg (by positivity)
      (Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _)
  rw [Vn_polar ha hb hn]
  exact re_eq_norm_mul_cos hR _ _

/-! ### Elementary bounds on the partial phase -/

lemma arctan_ge_sub_cube {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 ≤ Real.arctan x := by
  have h1 : Real.sin (Real.arctan x) ≤ Real.arctan x :=
    Real.sin_le (Real.arctan_nonneg.mpr hx)
  rw [Real.sin_arctan] at h1
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hs : Real.sqrt (1 + x ^ 2) ≤ 1 + x ^ 2 :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by nlinarith [sq_nonneg x]))
  have hspos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr hpos
  have h2 : x / (1 + x ^ 2) ≤ x / Real.sqrt (1 + x ^ 2) :=
    div_le_div_of_nonneg_left hx hspos hs
  have h3 : x - x ^ 3 ≤ x / (1 + x ^ 2) := by
    rw [le_div_iff₀ hpos]
    nlinarith [pow_nonneg hx 5, sq_nonneg x]
  linarith

/-- `x_j = δ c_j / A_j`, the argument of the `j`-th arctangent. -/
noncomputable def xj (a b : ℝ) (j : ℕ) : ℝ := dl a b * cj j / Aj a b j

lemma xj_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (j : ℕ) : 0 ≤ xj a b j := by
  unfold xj dl
  have := Aj_pos ha (ha.trans hab) j
  have := cj_pos j
  have : 0 ≤ b - a := by linarith
  positivity

lemma xj_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (j : ℕ) : xj a b j ≤ dl a b / cj j := by
  have hc := cj_pos j
  have hA := Aj_pos ha (ha.trans hab) j
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  unfold xj
  rw [div_le_div_iff₀ hA hc]
  have : cj j ^ 2 ≤ Aj a b j := by
    unfold Aj; have : 0 ≤ a * b := mul_nonneg ha (ha.trans hab); linarith
  nlinarith

/-- `x_j ≥ δ (1/c_j - K/c_j³)`. -/
lemma xj_ge {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (j : ℕ) :
    dl a b * (1 / cj j - (a * b / 4) / cj j ^ 3) ≤ xj a b j := by
  have hc := cj_pos j
  have hA := Aj_pos ha (ha.trans hab) j
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  have hK : 0 ≤ a * b / 4 := by have := mul_nonneg ha (ha.trans hab); linarith
  have hx : xj a b j = dl a b * (cj j / Aj a b j) := by unfold xj; ring
  rw [hx]
  refine mul_le_mul_of_nonneg_left ?_ hd
  have hA' : Aj a b j = cj j ^ 2 + a * b / 4 := rfl
  have he : 1 / cj j - (a * b / 4) / cj j ^ 3 = (cj j ^ 2 - a * b / 4) / cj j ^ 3 := by
    field_simp
  rw [he, div_le_div_iff₀ (pow_pos hc 3) hA, hA']
  nlinarith [sq_nonneg (a * b / 4), pow_pos hc 4]

lemma psi_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (j : ℕ) : psi a b j ≤ xj a b j :=
  by
    change Real.arctan (xj a b j) ≤ xj a b j
    simpa only [Real.tan_arctan] using Real.le_tan (Real.arctan_nonneg.mpr (xj_nonneg ha hab j)) (Real.arctan_lt_pi_div_two _)

lemma psi_ge {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (j : ℕ) :
    xj a b j - xj a b j ^ 3 ≤ psi a b j :=
  arctan_ge_sub_cube (xj_nonneg ha hab j)

/-- `Σ_{j<n} 1/(j+1)² ≤ 2`, in the form the induction wants. -/
lemma sum_inv_sq_le_aux (n : ℕ) :
    ∑ j ∈ range (n + 1), 1 / ((j : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have key : 1 / (((n + 1 : ℕ) : ℝ) + 1) ^ 2
        ≤ 1 / ((n : ℝ) + 1) - 1 / (((n + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      rw [div_sub_div _ _ h1.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast at key ⊢
    linarith

lemma sum_inv_sq_le (n : ℕ) : ∑ j ∈ range n, 1 / ((j : ℝ) + 1) ^ 2 ≤ 2 := by
  rcases n with _ | n
  · simp
  · have := sum_inv_sq_le_aux n
    have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- `Σ_{j ≤ n} 1/c_j ≤ 5 + log n`. -/
lemma sum_inv_cj_le (n : ℕ) : ∑ j ∈ range (n + 1), 1 / cj j ≤ 5 + Real.log n := by
  rw [Finset.sum_range_succ']
  have h0 : 1 / cj 0 = 4 := by unfold cj; norm_num
  have hterm : ∀ j ∈ range n, 1 / cj (j + 1) ≤ 1 / ((j : ℝ) + 1) := by
    intro j _
    unfold cj
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hH : ∑ j ∈ range n, 1 / ((j : ℝ) + 1) = (harmonic n : ℝ) := by
    simp [harmonic]
  have := harmonic_le_one_add_log n
  have := Finset.sum_le_sum hterm
  rw [h0]
  linarith

/-- `Σ_{j ≤ n} 1/c_j³ ≤ 66`. -/
lemma sum_inv_cj_cube_le (n : ℕ) : ∑ j ∈ range (n + 1), 1 / cj j ^ 3 ≤ 66 := by
  rw [Finset.sum_range_succ']
  have h0 : 1 / cj 0 ^ 3 = 64 := by unfold cj; norm_num
  have hterm : ∀ j ∈ range n, 1 / cj (j + 1) ^ 3 ≤ 1 / ((j : ℝ) + 1) ^ 2 := by
    intro j _
    unfold cj
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    have h1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
    have h2 : (j : ℝ) + 1 ≤ (j : ℝ) + 1 + 1 / 4 := by linarith
    calc ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1) ^ 3 := by
          nlinarith [pow_le_pow_right₀ h1 (show 2 ≤ 3 by norm_num)]
      _ ≤ ((j : ℝ) + 1 + 1 / 4) ^ 3 := pow_le_pow_left₀ (by positivity) h2 3
  have := Finset.sum_le_sum hterm
  have := sum_inv_sq_le n
  rw [h0]
  linarith

/-- `Σ_{j<n} 1/c_{j+1} ≥ log n - 1` for `n ≥ 1`. -/
lemma sum_inv_cj_succ_ge {n : ℕ} (hn : n ≠ 0) :
    Real.log n - 1 ≤ ∑ j ∈ range n, 1 / cj (j + 1) := by
  have hterm : ∀ j ∈ range n, 1 / ((j : ℝ) + 2) ≤ 1 / cj (j + 1) := by
    intro j _
    unfold cj
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hH : (harmonic (n + 1) : ℝ) = 1 + ∑ j ∈ range n, 1 / ((j : ℝ) + 2) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [Finset.sum_range_succ']
    push_cast
    rw [add_comm]
    congr 1
    · norm_num
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [one_div]
      ring_nf
  have hlog := log_add_one_le_harmonic (n + 1)
  have hmono : Real.log n ≤ Real.log (((n + 1 : ℕ) : ℝ) + 1) := by
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have := Finset.sum_le_sum hterm
  push_cast at hlog hmono
  linarith

/-- **Upper end of the window**: `φ_n ≤ δ(log π + 5)`. -/
lemma phi_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    phi a b n ≤ dl a b * (Real.log Real.pi + 5) := by
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  have h1 : ∑ j ∈ range (n + 1), psi a b j ≤ ∑ j ∈ range (n + 1), dl a b * (1 / cj j) :=
    Finset.sum_le_sum fun j _ =>
      (psi_le ha hab j).trans ((xj_le ha hab j).trans (by rw [mul_one_div]))
  rw [← Finset.mul_sum] at h1
  have h2 := mul_le_mul_of_nonneg_left (sum_inv_cj_le n) hd
  unfold phi
  nlinarith

/-- **Lower end of the window**: `φ_n ≥ δ(log π - 1 - 2K) - 66 δ³` for `n ≥ 1`. -/
lemma le_phi {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {n : ℕ} (hn : n ≠ 0) :
    dl a b * (Real.log Real.pi - 1 - 2 * (a * b / 4)) - 66 * dl a b ^ 3 ≤ phi a b n := by
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  have hK : 0 ≤ a * b / 4 := by have := mul_nonneg ha (ha.trans hab); linarith
  -- the arctangents against the linear terms, minus the cubes
  have h1 : ∑ j ∈ range (n + 1), (xj a b j - xj a b j ^ 3) ≤ ∑ j ∈ range (n + 1), psi a b j :=
    Finset.sum_le_sum fun j _ => psi_ge ha hab j
  rw [Finset.sum_sub_distrib] at h1
  -- the cubes
  have h2 : ∑ j ∈ range (n + 1), xj a b j ^ 3 ≤ dl a b ^ 3 * 66 := by
    have : ∀ j ∈ range (n + 1), xj a b j ^ 3 ≤ dl a b ^ 3 * (1 / cj j ^ 3) := by
      intro j _
      have hx := xj_le ha hab j
      have hx0 := xj_nonneg ha hab j
      calc xj a b j ^ 3 ≤ (dl a b / cj j) ^ 3 := pow_le_pow_left₀ hx0 hx 3
        _ = dl a b ^ 3 * (1 / cj j ^ 3) := by rw [div_pow]; ring
    calc ∑ j ∈ range (n + 1), xj a b j ^ 3
        ≤ ∑ j ∈ range (n + 1), dl a b ^ 3 * (1 / cj j ^ 3) := Finset.sum_le_sum this
      _ = dl a b ^ 3 * ∑ j ∈ range (n + 1), 1 / cj j ^ 3 := by rw [Finset.mul_sum]
      _ ≤ dl a b ^ 3 * 66 :=
          mul_le_mul_of_nonneg_left (sum_inv_cj_cube_le n) (pow_nonneg hd 3)
  -- the linear terms, dropping `j = 0`
  have h3 : ∑ j ∈ range n, xj a b (j + 1) ≤ ∑ j ∈ range (n + 1), xj a b j := by
    rw [Finset.sum_range_succ' (fun j => xj a b j)]
    linarith [xj_nonneg ha hab 0]
  have h4 : ∑ j ∈ range n, dl a b * (1 / cj (j + 1) - (a * b / 4) / cj (j + 1) ^ 3)
      ≤ ∑ j ∈ range n, xj a b (j + 1) :=
    Finset.sum_le_sum fun j _ => xj_ge ha hab (j + 1)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at h4
  have h5 : ∑ j ∈ range n, (a * b / 4) / cj (j + 1) ^ 3 ≤ (a * b / 4) * 2 := by
    have : ∀ j ∈ range n, (a * b / 4) / cj (j + 1) ^ 3 ≤ (a * b / 4) * (1 / ((j : ℝ) + 1) ^ 2) := by
      intro j _
      rw [div_eq_mul_one_div]
      refine mul_le_mul_of_nonneg_left ?_ hK
      unfold cj
      push_cast
      apply one_div_le_one_div_of_le (by positivity)
      have h1' : (1 : ℝ) ≤ (j : ℝ) + 1 := by
        have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
      calc ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1) ^ 3 := by
            nlinarith [pow_le_pow_right₀ h1' (show 2 ≤ 3 by norm_num)]
        _ ≤ ((j : ℝ) + 1 + 1 / 4) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    calc ∑ j ∈ range n, (a * b / 4) / cj (j + 1) ^ 3
        ≤ ∑ j ∈ range n, (a * b / 4) * (1 / ((j : ℝ) + 1) ^ 2) := Finset.sum_le_sum this
      _ = (a * b / 4) * ∑ j ∈ range n, 1 / ((j : ℝ) + 1) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (a * b / 4) * 2 := mul_le_mul_of_nonneg_left (sum_inv_sq_le n) hK
  have h6 := sum_inv_cj_succ_ge hn
  have h7 : dl a b * (Real.log n - 1 - (a * b / 4) * 2)
      ≤ dl a b * (∑ j ∈ range n, 1 / cj (j + 1) - ∑ j ∈ range n, (a * b / 4) / cj (j + 1) ^ 3) :=
    mul_le_mul_of_nonneg_left (by linarith) hd
  unfold phi
  nlinarith

/-! ### From the partial products to `Γℝ` -/

lemma sOf_half (t : ℝ) : sOf t / 2 = zA t := by
  unfold sOf zA; push_cast; ring

lemma conj_sOf_half (t : ℝ) : conj (sOf t / 2) = wB t := by
  unfold sOf wB
  rw [map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
    map_div₀, map_one, map_ofNat]
  push_cast
  ring

/-- `Γℝ(1/2 + ia) · conj Γℝ(1/2 + ib) = π^{-1/2 + iδ} Γ(z) Γ(w)`. -/
lemma gammaR_prod (a b : ℝ) :
    Gammaℝ (sOf a) * conj (Gammaℝ (sOf b)) = cpi a b * (Gamma (zA a) * Gamma (wB b)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hlog : Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) :=
    (Complex.ofReal_log Real.pi_pos.le).symm
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Complex.Gamma_conj, sOf_half, conj_sOf_half,
    cpow_def_of_ne_zero hpi, cpow_def_of_ne_zero hpi, hlog, ← Complex.exp_conj]
  have hc : exp ((Real.log Real.pi : ℂ) * (-sOf a / 2))
      * exp (conj ((Real.log Real.pi : ℂ) * (-sOf b / 2))) = cpi a b := by
    rw [← Complex.exp_add]
    unfold cpi
    congr 1
    rw [map_mul, Complex.conj_ofReal, map_div₀, map_neg, map_ofNat]
    unfold sOf dl
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one, map_ofNat]
    push_cast
    ring
  rw [← hc]
  ring

lemma tendsto_Vn (a b : ℝ) :
    Tendsto (Vn a b) atTop (𝓝 (cpi a b * (Gamma (zA a) * Gamma (wB b)))) :=
  ((GammaSeq_tendsto_Gamma _).mul (GammaSeq_tendsto_Gamma _)).const_mul _

/-- **The phase lemma.** If the explicit window `[-L, L]` with `L < π/2` holds the
two ends of the partial-phase bounds, the product of the two `Γℝ` values has
positive real part. No value of `Γ` is used. -/
theorem gammaR_re_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {L : ℝ}
    (hL : L < Real.pi / 2)
    (hup : dl a b * (Real.log Real.pi + 5) ≤ L)
    (hlo : -L ≤ dl a b * (Real.log Real.pi - 1 - 2 * (a * b / 4)) - 66 * dl a b ^ 3) :
    0 < (Gammaℝ (sOf a) * conj (Gammaℝ (sOf b))).re := by
  rw [gammaR_prod]
  set V := cpi a b * (Gamma (zA a) * Gamma (wB b)) with hVdef
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hL0 : 0 ≤ L := le_trans (mul_nonneg hd (by linarith)) hup
  have hcosL : 0 < Real.cos L :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hL⟩
  have hev : ∀ᶠ n in atTop, Real.cos L * ‖Vn a b n‖ ≤ (Vn a b n).re := by
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn0 : n ≠ 0 := by omega
    rw [Vn_re ha (ha.trans hab) hn0]
    have hphi : |phi a b n| ≤ L :=
      abs_le.mpr ⟨hlo.trans (le_phi ha hab hn0), (phi_le ha hab n).trans hup⟩
    have hcos : Real.cos L ≤ Real.cos (phi a b n) := by
      rw [← Real.cos_abs (phi a b n)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
        (by linarith [Real.pi_pos]) hphi
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hcos (norm_nonneg _)
  have hlim := tendsto_Vn a b
  have hre : Tendsto (fun n => (Vn a b n).re) atTop (𝓝 V.re) :=
    (Complex.continuous_re.tendsto _).comp hlim
  have hnorm : Tendsto (fun n => Real.cos L * ‖Vn a b n‖) atTop (𝓝 (Real.cos L * ‖V‖)) :=
    hlim.norm.const_mul _
  have hle : Real.cos L * ‖V‖ ≤ V.re := le_of_tendsto_of_tendsto hnorm hre hev
  have hV : V ≠ 0 := by
    refine mul_ne_zero (by unfold cpi; exact Complex.exp_ne_zero _) (mul_ne_zero ?_ ?_)
    · exact Gamma_ne_zero_of_re_pos (by rw [zA_re]; norm_num)
    · exact Gamma_ne_zero_of_re_pos (by rw [wB_re]; norm_num)
  have : 0 < Real.cos L * ‖V‖ := mul_pos hcosL (norm_pos_iff.mpr hV)
  linarith

/-- **The phase lemma at the planned endpoints** `a = 14.13`, `b = 14.14`, with
`L = 11/20`: the window is `[-0.5045, 0.0357]` against the true increment
`-0.00405` (`sizing.py`). -/
theorem gammaR_re_pos_first :
    0 < (Gammaℝ (sOf (1413 / 100)) * conj (Gammaℝ (sOf (707 / 50)))).re := by
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogpi' : Real.log Real.pi ≤ Real.pi - 1 := Real.log_le_sub_one_of_pos Real.pi_pos
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  refine gammaR_re_pos (L := 11 / 20) (by norm_num) (by norm_num) (by linarith) ?_ ?_
  · unfold dl; nlinarith
  · unfold dl; nlinarith

/-- **The target, conditional on one inequality.** A zero of `ζ` on the critical line
with ordinate strictly between `14.13` and `14.14`, given only that
`ζ(1/2 + 14.13i) · conj ζ(1/2 + 14.14i)` has negative real part. That hypothesis is
the open work of the hunt (`RESULTS.md`, section 5); this theorem is not the target
until it is discharged. -/
theorem first_zero_on_line_of_zeta_product
    (hX : (riemannZeta (sOf (1413 / 100)) * conj (riemannZeta (sOf (707 / 50)))).re < 0) :
    ∃ t ∈ Set.Ioo (1413 / 100 : ℝ) (707 / 50), riemannZeta (1 / 2 + t * I) = 0 :=
  exists_zero_of_sign_data (by norm_num) hX gammaR_re_pos_first

end HardyFirstZero

end

section









/-!
# The corrected trapezoid rule with a fourth-derivative remainder (hunt `hardy_first_zero`)

Item 1 of `RESULTS.md` section 5, the domain-independent half of the order-4
Euler-Maclaurin representation the plan uses for `ζ` on the critical line:

    ∫_a^{a+1} g = (g(a) + g(a+1))/2 - (g'(a+1) - g'(a))/12 + ∫_a^{a+1} k g'''',
    0 ≤ k,  ∫_a^{a+1} k = 1/720,

with the quartic kernel `k(t) = (t-a)²(a+1-t)²/24`. One fundamental-theorem step
does all four integrations by parts at once: since `k'''' = 1`, the function
`k g''' - k' g'' + k'' g' - k''' g` has derivative `k g'''' - g`, and at both ends
`k = k' = 0`, `k'' = 1/12`, `k''' = ∓1/2`.

The lab's `ZetaLean/DHTailBound2.lean` proves the order-2 version
(`norm_trapezoid_sub_integral_le`); at `t = 14.13` the order-2 remainder needs 471
terms of the zeta partial sum where this one needs 15 (`sizing.py`).
-/

open intervalIntegral MeasureTheory Complex

namespace HardyFirstZero

/-- The quartic kernel on `[a, a+1]` and its first three derivatives. -/
noncomputable def kq (a t : ℝ) : ℝ := (t - a) ^ 2 * (a + 1 - t) ^ 2 / 24
noncomputable def kq1 (a t : ℝ) : ℝ := (t - a) * (a + 1 - t) * (2 * a + 1 - 2 * t) / 12
noncomputable def kq2 (a t : ℝ) : ℝ := (1 - 6 * (t - a) + 6 * (t - a) ^ 2) / 12
noncomputable def kq3 (a t : ℝ) : ℝ := (t - a) - 1 / 2

lemma hasDerivAt_kq (a t : ℝ) : HasDerivAt (kq a) (kq1 a t) t := by
  have h1 : HasDerivAt (fun x : ℝ => x - a) 1 t := (hasDerivAt_id' t).sub_const a
  have h2 : HasDerivAt (fun x : ℝ => a + 1 - x) (-1) t := (hasDerivAt_id' t).const_sub (a + 1)
  have h := ((h1.fun_pow 2).fun_mul (h2.fun_pow 2)).div_const 24
  unfold kq kq1
  convert h using 1 <;> first | rfl | (push_cast; ring)

lemma hasDerivAt_kq1 (a t : ℝ) : HasDerivAt (kq1 a) (kq2 a t) t := by
  have h1 : HasDerivAt (fun x : ℝ => x - a) 1 t := (hasDerivAt_id' t).sub_const a
  have h2 : HasDerivAt (fun x : ℝ => a + 1 - x) (-1) t := (hasDerivAt_id' t).const_sub (a + 1)
  have h3 : HasDerivAt (fun x : ℝ => 2 * a + 1 - 2 * x) (-(2 * 1)) t :=
    ((hasDerivAt_id' t).const_mul 2).const_sub (2 * a + 1)
  have h := ((h1.fun_mul h2).fun_mul h3).div_const 12
  unfold kq1 kq2
  convert h using 1 <;> first | rfl | ring

lemma hasDerivAt_kq2 (a t : ℝ) : HasDerivAt (kq2 a) (kq3 a t) t := by
  have h1 : HasDerivAt (fun x : ℝ => x - a) 1 t := (hasDerivAt_id' t).sub_const a
  have h := (((h1.const_mul 6).const_sub 1).fun_add ((h1.fun_pow 2).const_mul 6)).div_const 12
  unfold kq2 kq3
  convert h using 1 <;> first | rfl | (push_cast; ring)

lemma hasDerivAt_kq3 (a t : ℝ) : HasDerivAt (kq3 a) 1 t :=
  ((hasDerivAt_id' t).sub_const a).sub_const (1 / 2 : ℝ)

lemma kq_nonneg (a t : ℝ) : 0 ≤ kq a t := by unfold kq; positivity

lemma integral_kq (a : ℝ) : ∫ t in a..a + 1, kq a t = 1 / 720 := by
  have hQ : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt
      (fun t => ((t - a) ^ 3 / 3 - (t - a) ^ 4 / 2 + (t - a) ^ 5 / 5) / 24) (kq a t) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => x - a) 1 t := (hasDerivAt_id' t).sub_const a
    have h := ((((h1.fun_pow 3).div_const 3).sub ((h1.fun_pow 4).div_const 2)).add
      ((h1.fun_pow 5).div_const 5)).div_const 24
    convert h using 1 <;> first | rfl | (dsimp [kq]; ring)
  rw [integral_eq_sub_of_hasDerivAt hQ
    ((continuous_iff_continuousAt.mpr fun t => (hasDerivAt_kq a t).continuousAt).intervalIntegrable _ _)]
  norm_num

/-- **The corrected trapezoid rule.** For a `C⁴` function on `[a, a+1]` whose fourth
derivative is bounded by `M`, the endpoint average corrected by the first
Bernoulli term misses the integral by at most `M/720`. -/
theorem corrected_trapezoid {g g1 g2 g3 g4 : ℝ → ℂ} {a M : ℝ}
    (h0 : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt g (g1 t) t)
    (h1 : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt g1 (g2 t) t)
    (h2 : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt g2 (g3 t) t)
    (h3 : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt g3 (g4 t) t)
    (hc : ContinuousOn g4 (Set.uIcc a (a + 1)))
    (hM : ∀ t ∈ Set.Icc a (a + 1), ‖g4 t‖ ≤ M) :
    ‖(∫ t in a..a + 1, g t) - ((g a + g (a + 1)) / 2 - (g1 (a + 1) - g1 a) / 12)‖
      ≤ M / 720 := by
  have hab : a ≤ a + 1 := by linarith
  have hcg : ContinuousOn g (Set.uIcc a (a + 1)) := fun t ht =>
    (h0 t ht).continuousAt.continuousWithinAt
  have hck : Continuous fun t => ((kq a t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_kq a t).continuousAt)
  -- the one fundamental-theorem step
  have hF : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt
      (fun t => ((kq a t : ℝ) : ℂ) * g3 t - ((kq1 a t : ℝ) : ℂ) * g2 t
        + ((kq2 a t : ℝ) : ℂ) * g1 t - ((kq3 a t : ℝ) : ℂ) * g t)
      (((kq a t : ℝ) : ℂ) * g4 t - g t) t := by
    intro t ht
    have e0 := (hasDerivAt_kq a t).ofReal_comp.mul (h3 t ht)
    have e1 := (hasDerivAt_kq1 a t).ofReal_comp.mul (h2 t ht)
    have e2 := (hasDerivAt_kq2 a t).ofReal_comp.mul (h1 t ht)
    have e3 := (hasDerivAt_kq3 a t).ofReal_comp.mul (h0 t ht)
    convert ((e0.sub e1).add e2).sub e3 using 1 <;> first | rfl | (push_cast; ring)
  have hint : IntervalIntegrable (fun t => ((kq a t : ℝ) : ℂ) * g4 t - g t) volume a (a + 1) :=
    ((hck.continuousOn.mul hc).sub hcg).intervalIntegrable
  have hftc := integral_eq_sub_of_hasDerivAt hF hint
  have hkg : IntervalIntegrable (fun t => ((kq a t : ℝ) : ℂ) * g4 t) volume a (a + 1) :=
    (hck.continuousOn.mul hc).intervalIntegrable
  rw [integral_sub hkg hcg.intervalIntegrable] at hftc
  have hend : ((kq a (a + 1) : ℝ) : ℂ) = 0 ∧ ((kq1 a (a + 1) : ℝ) : ℂ) = 0
      ∧ ((kq2 a (a + 1) : ℝ) : ℂ) = 1 / 12 ∧ ((kq3 a (a + 1) : ℝ) : ℂ) = 1 / 2
      ∧ ((kq a a : ℝ) : ℂ) = 0 ∧ ((kq1 a a : ℝ) : ℂ) = 0
      ∧ ((kq2 a a : ℝ) : ℂ) = 1 / 12 ∧ ((kq3 a a : ℝ) : ℂ) = -1 / 2 := by
    simp only [kq, kq1, kq2, kq3]; push_cast; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hend
  simp only [e1, e2, e3, e4, e5, e6, e7, e8] at hftc
  have hkey : (∫ t in a..a + 1, g t) - ((g a + g (a + 1)) / 2 - (g1 (a + 1) - g1 a) / 12)
      = ∫ t in a..a + 1, ((kq a t : ℝ) : ℂ) * g4 t := by
    linear_combination (-1 : ℂ) * hftc
  rw [hkey]
  calc ‖∫ t in a..a + 1, ((kq a t : ℝ) : ℂ) * g4 t‖
      ≤ ∫ t in a..a + 1, ‖((kq a t : ℝ) : ℂ) * g4 t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..a + 1, kq a t * M := by
        refine intervalIntegral.integral_mono_on hab hkg.norm ?_ fun t ht => ?_
        · exact ((continuous_iff_continuousAt.mpr fun t =>
            (hasDerivAt_kq a t).continuousAt).mul continuous_const).intervalIntegrable _ _
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kq_nonneg a t)]
          exact mul_le_mul_of_nonneg_left (hM t ht) (kq_nonneg a t)
    _ = M / 720 := by
        rw [intervalIntegral.integral_mul_const, integral_kq]
        ring

/-! ### The zeta block -/

/-- The order-4 block on `[x, x+1]`: the integral of `t^{-s}` minus its corrected
trapezoid, in closed form. -/
noncomputable def eBlock (s : ℂ) (x : ℝ) : ℂ :=
  (((x + 1 : ℝ) : ℂ) ^ (1 - s) - ((x : ℝ) : ℂ) ^ (1 - s)) / (1 - s)
    - (((x : ℝ) : ℂ) ^ (-s) + ((x + 1 : ℝ) : ℂ) ^ (-s)) / 2
    - s / 12 * (((x + 1 : ℝ) : ℂ) ^ (-s - 1) - ((x : ℝ) : ℂ) ^ (-s - 1))

/-- `P(s) = s(s+1)(s+2)(s+3)`, the constant of the fourth derivative of `t^{-s}`. -/
noncomputable def P4 (s : ℂ) : ℂ := s * (s + 1) * (s + 2) * (s + 3)

private lemma ne_zero_of_re_neg {r : ℂ} (h : r.re < 0) : r ≠ 0 := by
  rintro rfl; simp at h

/-- **The block bound**: `‖e(s, x)‖ ≤ ‖P(s)‖ x^{-σ-4} / 720` for `x ≥ 1`, `Re s > 0`, `s ≠ 1`. -/
theorem norm_eBlock_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖eBlock s x‖ ≤ ‖P4 s‖ * x ^ (-s.re - 4) / 720 := by
  have hx0 : 0 < x := by linarith
  have hpos : ∀ t ∈ Set.uIcc x (x + 1), 0 < t := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    linarith [ht.1]
  have r0 : (-s : ℂ) ≠ 0 := ne_zero_of_re_neg (by simp; linarith)
  have r1 : (-s - 1 : ℂ) ≠ 0 := ne_zero_of_re_neg (by simp; linarith)
  have r2 : (-s - 1 - 1 : ℂ) ≠ 0 := ne_zero_of_re_neg (by simp; linarith)
  have r3 : (-s - 1 - 1 - 1 : ℂ) ≠ 0 := ne_zero_of_re_neg (by simp; linarith)
  set g : ℝ → ℂ := fun t => (t : ℂ) ^ (-s)
  set g1 : ℝ → ℂ := fun t => -s * (t : ℂ) ^ (-s - 1)
  set g2 : ℝ → ℂ := fun t => -s * (-s - 1) * (t : ℂ) ^ (-s - 1 - 1)
  set g3 : ℝ → ℂ := fun t => -s * (-s - 1) * (-s - 1 - 1) * (t : ℂ) ^ (-s - 1 - 1 - 1)
  set g4 : ℝ → ℂ := fun t =>
    -s * (-s - 1) * (-s - 1 - 1) * (-s - 1 - 1 - 1) * (t : ℂ) ^ (-s - 1 - 1 - 1 - 1)
  have d0 : ∀ t ∈ Set.uIcc x (x + 1), HasDerivAt g (g1 t) t := fun t ht =>
    hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r0
  have d1 : ∀ t ∈ Set.uIcc x (x + 1), HasDerivAt g1 (g2 t) t := fun t ht => by
    have := (hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r1).const_mul (-s)
    convert this using 1 <;> first | rfl | (dsimp [g2]; ring)
  have d2 : ∀ t ∈ Set.uIcc x (x + 1), HasDerivAt g2 (g3 t) t := fun t ht => by
    have := (hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r2).const_mul (-s * (-s - 1))
    convert this using 1 <;> first | rfl | (dsimp [g3]; ring)
  have d3 : ∀ t ∈ Set.uIcc x (x + 1), HasDerivAt g3 (g4 t) t := fun t ht => by
    have := (hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r3).const_mul
      (-s * (-s - 1) * (-s - 1 - 1))
    convert this using 1 <;> first | rfl | (dsimp [g4]; ring)
  have r4 : (-s - 1 - 1 - 1 - 1 : ℂ) ≠ 0 := ne_zero_of_re_neg (by simp; linarith)
  have hc4 : ContinuousOn g4 (Set.uIcc x (x + 1)) := fun t ht =>
    ((hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r4).continuousAt.const_mul
      _).continuousWithinAt
  have hM : ∀ t ∈ Set.Icc x (x + 1), ‖g4 t‖ ≤ ‖P4 s‖ * x ^ (-s.re - 4) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    simp only [g4]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hP : ‖-s * (-s - 1) * (-s - 1 - 1) * (-s - 1 - 1 - 1)‖ = ‖P4 s‖ := by
      rw [show -s * (-s - 1) * (-s - 1 - 1) * (-s - 1 - 1 - 1) = P4 s by unfold P4; ring]
    rw [hP]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hre : (-s - 1 - 1 - 1 - 1).re = -s.re - 4 := by simp; ring
    rw [hre]
    exact Real.rpow_le_rpow_of_nonpos hx0 ht.1 (by linarith)
  have hT := corrected_trapezoid d0 d1 d2 d3 hc4 hM
  -- the integral in closed form
  have h0 : (0 : ℝ) ∉ Set.uIcc x (x + 1) := fun h => (lt_irrefl 0) (hpos 0 h)
  have hI : ∫ t in x..x + 1, g t
      = ((((x + 1 : ℝ) : ℂ) ^ (-s + 1) - ((x : ℝ) : ℂ) ^ (-s + 1)) / (-s + 1)) := by
    simp only [g]
    rw [integral_cpow (Or.inr ⟨fun h => hs1 (by linear_combination -h), h0⟩)]
  have hE : eBlock s x
      = (∫ t in x..x + 1, g t) - ((g x + g (x + 1)) / 2 - (g1 (x + 1) - g1 x) / 12) := by
    rw [hI]
    simp only [eBlock, g, g1]
    rw [show (-s + 1 : ℂ) = 1 - s by ring]
    push_cast
    ring
  rw [hE]
  calc _ ≤ ‖P4 s‖ * x ^ (-s.re - 4) / 720 := hT
    _ = _ := rfl

/-! ### The representation where everything converges: `Re s > 2` -/

/-- The block at a natural point, written with natural-number casts. -/
lemma eBlock_nat (s : ℂ) (n : ℕ) :
    eBlock s (n : ℝ)
      = (((n + 1 : ℕ) : ℂ) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (1 - s)
        - ((n : ℂ) ^ (-s) + ((n + 1 : ℕ) : ℂ) ^ (-s)) / 2
        - s / 12 * (((n + 1 : ℕ) : ℂ) ^ (-s - 1) - (n : ℂ) ^ (-s - 1)) := by
  simp only [eBlock]
  push_cast
  ring

/-- The shifted Dirichlet series `Σ_k (k + N)^{-w}`, for `Re w > 1`. -/
lemma hasSum_shift {w : ℂ} (hw : 1 < w.re) (N : ℕ) :
    HasSum (fun k : ℕ => ((k + N : ℕ) : ℂ) ^ (-w))
      (riemannZeta w - ∑ i ∈ Finset.range N, (i : ℂ) ^ (-w)) := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ w) := Complex.summable_one_div_nat_cpow.mpr hw
  have h : HasSum (fun n : ℕ => (n : ℂ) ^ (-w)) (riemannZeta w) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hw]
    convert hsum.hasSum using 1
    funext n; rw [Complex.cpow_neg, one_div]
  exact (hasSum_nat_add_iff' N).mpr h

/-- The same series with one more shift. -/
lemma hasSum_shift_succ {w : ℂ} (hw : 1 < w.re) (N : ℕ) :
    HasSum (fun k : ℕ => ((k + 1 + N : ℕ) : ℂ) ^ (-w))
      (riemannZeta w - ∑ i ∈ Finset.range N, (i : ℂ) ^ (-w) - (N : ℂ) ^ (-w)) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_shift hw N)
  simpa [Finset.sum_range_one, add_comm, add_left_comm, add_assoc] using h

/-- **The order-4 representation on `Re s > 2`**, by absolute convergence. -/
theorem zeta_em4_of_two_lt {s : ℂ} (hs : 2 < s.re) (N : ℕ) :
    riemannZeta s
      = ∑ i ∈ Finset.range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
        + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1)
        - ∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ) := by
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have h1s : (1 - s : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hA := hasSum_shift (w := s) (by linarith) N
  have hA1 := hasSum_shift_succ (w := s) (by linarith) N
  have hC := hasSum_shift (w := s - 1) (by simp; linarith) N
  have hC1 := hasSum_shift_succ (w := s - 1) (by simp; linarith) N
  have hD := hasSum_shift (w := s + 1) (by simp; linarith) N
  have hD1 := hasSum_shift_succ (w := s + 1) (by simp; linarith) N
  have hE := (((hC1.sub hC).div_const (1 - s)).sub ((hA.add hA1).div_const 2)).sub
    ((hD1.sub hD).mul_left (s / 12))
  have hfun : (fun k : ℕ => eBlock s ((k + N : ℕ) : ℝ))
      = fun k : ℕ =>
        (((k + 1 + N : ℕ) : ℂ) ^ (-(s - 1)) - ((k + N : ℕ) : ℂ) ^ (-(s - 1))) / (1 - s)
        - (((k + N : ℕ) : ℂ) ^ (-s) + ((k + 1 + N : ℕ) : ℂ) ^ (-s)) / 2
        - s / 12 * (((k + 1 + N : ℕ) : ℂ) ^ (-(s + 1)) - ((k + N : ℕ) : ℂ) ^ (-(s + 1))) := by
    funext k
    rw [eBlock_nat]
    have e1 : (k + N + 1 : ℕ) = k + 1 + N := by omega
    rw [e1, show (-(s - 1) : ℂ) = 1 - s by ring, show (-(s + 1) : ℂ) = -s - 1 by ring]
  rw [← hfun] at hE
  rw [hE.tsum_eq]
  rw [show (-(s - 1) : ℂ) = 1 - s by ring, show (-(s + 1) : ℂ) = -s - 1 by ring]
  field_simp
  ring

/-! ### Continuation to the quarter plane `Re s > 0, Im s > 0` -/

/-- The right side of the representation, as a function of `s`. -/
noncomputable def emRHS (N : ℕ) (s : ℂ) : ℂ :=
  ∑ i ∈ Finset.range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
    + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1)
    - ∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)

/-- The open quarter plane; it contains the critical line above the axis and
avoids the pole at `1`. -/
def QP : Set ℂ := {z | 0 < z.re ∧ 0 < z.im}

lemma isOpen_QP : IsOpen QP :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

lemma convex_QP : Convex ℝ QP := by
  have hre : IsLinearMap ℝ (fun z : ℂ => z.re) :=
    ⟨fun x y => Complex.add_re x y, fun c x => by simp [Complex.real_smul, Complex.mul_re]⟩
  have him : IsLinearMap ℝ (fun z : ℂ => z.im) :=
    ⟨fun x y => Complex.add_im x y, fun c x => by simp [Complex.real_smul, Complex.mul_im]⟩
  exact (convex_halfSpace_gt hre 0).inter (convex_halfSpace_gt him 0)

lemma ne_one_of_QP {z : ℂ} (hz : z ∈ QP) : z ≠ 1 := by
  rintro rfl; simp [QP] at hz

lemma differentiableAt_eBlock {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (fun w => eBlock w x) s := by
  have hb0 : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hb1 : ((x + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hl : DifferentiableAt ℂ (fun w : ℂ => 1 - w) s :=
    (differentiableAt_const _).sub differentiableAt_id
  have hn : DifferentiableAt ℂ (fun w : ℂ => -w) s := differentiableAt_id.neg
  have hn1 : DifferentiableAt ℂ (fun w : ℂ => -w - 1) s := hn.sub (differentiableAt_const _)
  unfold eBlock
  refine (((hl.const_cpow (Or.inl hb1)).sub (hl.const_cpow (Or.inl hb0))).div hl
    (sub_ne_zero.mpr (Ne.symm hs))).sub
    (((hn.const_cpow (Or.inl hb0)).add (hn.const_cpow (Or.inl hb1))).div_const 2) |>.sub
    ((differentiableAt_id.div_const 12).mul
      ((hn1.const_cpow (Or.inl hb1)).sub (hn1.const_cpow (Or.inl hb0))))

private lemma summable_shift_rpow {p : ℝ} (hp : 1 < p) (N : ℕ) :
    Summable (fun k : ℕ => (((k + N : ℕ) : ℝ)) ^ (-p)) := by
  have hbase : Summable (fun k : ℕ => ((k : ℝ)) ^ (-p)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact (summable_nat_add_iff (f := fun k : ℕ => ((k : ℝ)) ^ (-p)) N).mpr hbase |>.congr
    fun k => by push_cast; ring_nf

lemma differentiableOn_tail {N : ℕ} (hN : 1 ≤ N) :
    DifferentiableOn ℂ (fun s => ∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)) QP := by
  intro s₀ hs₀
  obtain ⟨hre0, him0⟩ := hs₀
  set δ : ℝ := min s₀.re s₀.im / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδre : δ ≤ s₀.re / 2 := by rw [hδ]; linarith [min_le_left s₀.re s₀.im]
  have hδim : δ ≤ s₀.im / 2 := by rw [hδ]; linarith [min_le_right s₀.re s₀.im]
  have hball : ∀ w ∈ Metric.ball s₀ δ, s₀.re / 2 ≤ w.re ∧ 0 < w.im ∧ ‖w‖ ≤ ‖s₀‖ + δ := by
    intro w hw
    have hd : ‖w - s₀‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have h1 := Complex.abs_re_le_norm (w - s₀)
    have h2 := Complex.abs_im_le_norm (w - s₀)
    rw [Complex.sub_re] at h1
    rw [Complex.sub_im] at h2
    refine ⟨by linarith [(abs_le.mp h1).1], by linarith [(abs_le.mp h2).1], ?_⟩
    calc ‖w‖ = ‖s₀ + (w - s₀)‖ := by ring_nf
      _ ≤ ‖s₀‖ + ‖w - s₀‖ := norm_add_le _ _
      _ ≤ ‖s₀‖ + δ := by linarith
  set R : ℝ := ‖s₀‖ + δ + 3 with hR
  have hsub : Metric.ball s₀ δ ⊆ QP := fun w hw => by
    obtain ⟨h1, h2, -⟩ := hball w hw
    exact ⟨by linarith, h2⟩
  have hu : Summable (fun k : ℕ => R ^ 4 * (((k + N : ℕ) : ℝ)) ^ (-(s₀.re / 2 + 4)) / 720) :=
    ((summable_shift_rpow (p := s₀.re / 2 + 4) (by linarith) N).mul_left (R ^ 4)).div_const 720
  have hF_le : ∀ (k : ℕ) (w : ℂ), w ∈ Metric.ball s₀ δ →
      ‖eBlock w ((k + N : ℕ) : ℝ)‖ ≤ R ^ 4 * (((k + N : ℕ) : ℝ)) ^ (-(s₀.re / 2 + 4)) / 720 := by
    intro k w hw
    obtain ⟨h1, h2, h3⟩ := hball w hw
    have hx1 : (1 : ℝ) ≤ ((k + N : ℕ) : ℝ) := by
      have : 1 ≤ k + N := by omega
      exact_mod_cast this
    refine (norm_eBlock_le (by linarith) (ne_one_of_QP (hsub hw)) hx1).trans ?_
    have hP : ‖P4 w‖ ≤ R ^ 4 := by
      unfold P4
      have e1 : ‖w + 1‖ ≤ R := by
        calc ‖w + 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ ≤ R := by simp; linarith
      have e2 : ‖w + 2‖ ≤ R := by
        calc ‖w + 2‖ ≤ ‖w‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
          _ ≤ R := by simp; linarith
      have e3 : ‖w + 3‖ ≤ R := by
        calc ‖w + 3‖ ≤ ‖w‖ + ‖(3 : ℂ)‖ := norm_add_le _ _
          _ ≤ R := by simp; linarith
      have e0 : ‖w‖ ≤ R := by linarith
      rw [norm_mul, norm_mul, norm_mul]
      calc ‖w‖ * ‖w + 1‖ * ‖w + 2‖ * ‖w + 3‖ ≤ R * R * R * R := by gcongr
        _ = R ^ 4 := by ring
    have hpow : (((k + N : ℕ) : ℝ)) ^ (-w.re - 4) ≤ (((k + N : ℕ) : ℝ)) ^ (-(s₀.re / 2 + 4)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hnn : 0 ≤ (((k + N : ℕ) : ℝ)) ^ (-w.re - 4) := Real.rpow_nonneg (by linarith) _
    have := mul_le_mul hP hpow hnn (by positivity)
    linarith
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ (fun w => eBlock w ((k + N : ℕ) : ℝ)) (Metric.ball s₀ δ) :=
    fun k w hw => (differentiableAt_eBlock (by
      have : 1 ≤ k + N := by omega
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one this))
      (ne_one_of_QP (hsub hw))).differentiableWithinAt
  have hD := differentiableOn_tsum_of_summable_norm hu hdiff Metric.isOpen_ball hF_le
  exact (hD.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ0))).differentiableWithinAt

lemma differentiableOn_emRHS {N : ℕ} (hN : 1 ≤ N) : DifferentiableOn ℂ (emRHS N) QP := by
  intro s hs
  have hs0 : s ≠ 0 := by rintro rfl; simp [QP] at hs
  have hs1 := ne_one_of_QP hs
  have hn : DifferentiableAt ℂ (fun w : ℂ => -w) s := differentiableAt_id.neg
  have hsum : DifferentiableAt ℂ (fun w => ∑ i ∈ Finset.range N, (i : ℂ) ^ (-w)) s :=
    DifferentiableAt.fun_sum fun i _ => hn.const_cpow (Or.inr (neg_ne_zero.mpr hs0))
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : DifferentiableAt ℂ (fun w : ℂ => (N : ℂ) ^ (1 - w) / (w - 1)) s :=
    (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hNne)).div
      (differentiableAt_id.sub (differentiableAt_const _)) (sub_ne_zero.mpr hs1)
  have h3 : DifferentiableAt ℂ (fun w : ℂ => (N : ℂ) ^ (-w) / 2) s :=
    (hn.const_cpow (Or.inl hNne)).div_const 2
  have h4 : DifferentiableAt ℂ (fun w : ℂ => w / 12 * (N : ℂ) ^ (-w - 1)) s :=
    (differentiableAt_id.div_const 12).mul
      ((hn.sub (differentiableAt_const _)).const_cpow (Or.inl hNne))
  have h5 : DifferentiableAt ℂ (fun s => ∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)) s :=
    (differentiableOn_tail hN).differentiableAt (isOpen_QP.mem_nhds hs)
  exact ((((hsum.add h2).add h3).add h4).sub h5).differentiableWithinAt

/-- **The order-4 representation on the quarter plane**, by the identity theorem. -/
theorem zeta_em4 {s : ℂ} (hs : s ∈ QP) {N : ℕ} (hN : 1 ≤ N) : riemannZeta s = emRHS N s := by
  have hzd : DifferentiableOn ℂ riemannZeta QP := fun z hz =>
    (differentiableAt_riemannZeta (ne_one_of_QP hz)).differentiableWithinAt
  have hz : AnalyticOnNhd ℂ riemannZeta QP := hzd.analyticOnNhd isOpen_QP
  have he : AnalyticOnNhd ℂ (emRHS N) QP := (differentiableOn_emRHS hN).analyticOnNhd isOpen_QP
  have hmem : (3 + I : ℂ) ∈ QP := by simp [QP]
  have hev : riemannZeta =ᶠ[nhds (3 + I : ℂ)] emRHS N := by
    have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds (by simp; norm_num)) fun z hz => ?_
    exact zeta_em4_of_two_lt hz N
  exact hz.eqOn_of_preconnected_of_eventuallyEq he convex_QP.isPreconnected hmem hev hs

/-! ### The tail, by the integral test -/

theorem norm_tail_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 2 ≤ N) :
    ‖∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)‖
      ≤ ‖P4 s‖ * (((N : ℝ) - 1) ^ (-s.re - 3) / (s.re + 3)) / 720 := by
  set p : ℝ := s.re + 4 with hp
  have hsumb : Summable (fun k : ℕ => (((k + N : ℕ) : ℝ)) ^ (-p)) :=
    summable_shift_rpow (by linarith) N
  have hb : ∀ k : ℕ, ‖eBlock s ((k + N : ℕ) : ℝ)‖
      ≤ ‖P4 s‖ * (((k + N : ℕ) : ℝ)) ^ (-p) / 720 := by
    intro k
    have hx1 : (1 : ℝ) ≤ ((k + N : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + N)
    have := norm_eBlock_le hs hs1 hx1
    rwa [show -s.re - 4 = -p by rw [hp]; ring] at this
  have hg : Summable (fun k : ℕ => ‖P4 s‖ * (((k + N : ℕ) : ℝ)) ^ (-p) / 720) :=
    (hsumb.mul_left _).div_const _
  have hnorm : Summable (fun k : ℕ => ‖eBlock s ((k + N : ℕ) : ℝ)‖) :=
    hg.of_nonneg_of_le (fun k => norm_nonneg _) hb
  have hKR : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N - 1)
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-p)) (Set.Ici ((N - 1 : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hKR hx) hxy (by linarith)
  have hintg : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-p)) (Set.Ioi ((N - 1 : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hKR
  have hnonneg : ∀ t ∈ Set.Ioi ((N - 1 : ℕ) : ℝ), 0 ≤ (fun t : ℝ => t ^ (-p)) t := fun t ht =>
    Real.rpow_nonneg (le_of_lt (lt_of_le_of_lt hKR.le ht)) _
  have htail := AntitoneOn.tsum_comp_add_le_integral (N - 1) hanti hintg hnonneg
  have hidx : ∀ n : ℕ, n + (N - 1) + 1 = n + N := fun n => by omega
  simp only [hidx] at htail
  have hint : ∫ t in Set.Ioi ((N - 1 : ℕ) : ℝ), t ^ (-p)
      = ((N : ℝ) - 1) ^ (-s.re - 3) / (s.re + 3) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) hKR, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one,
      show -p + 1 = -(s.re + 3) by rw [hp]; ring, neg_div_neg_eq]
    congr 1
    ring_nf
  rw [hint] at htail
  calc ‖∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)‖
      ≤ ∑' k : ℕ, ‖eBlock s ((k + N : ℕ) : ℝ)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, ‖P4 s‖ * (((k + N : ℕ) : ℝ)) ^ (-p) / 720 := hnorm.tsum_le_tsum hb hg
    _ = ‖P4 s‖ * (∑' k : ℕ, (((k + N : ℕ) : ℝ)) ^ (-p)) / 720 := by
        rw [tsum_div_const, tsum_mul_left]
    _ ≤ ‖P4 s‖ * (((N : ℝ) - 1) ^ (-s.re - 3) / (s.re + 3)) / 720 := by
        gcongr

/-- **The order-4 Euler-Maclaurin remainder for zeta**, on the quarter plane:
for `Re s > 0`, `Im s > 0` and `N ≥ 2`,

    ‖ζ(s) - (Σ_{n<N} n^{-s} + N^{1-s}/(s-1) + N^{-s}/2 + s N^{-s-1}/12)‖
      ≤ ‖s(s+1)(s+2)(s+3)‖ (N-1)^{-σ-3} / (720 (σ+3)). -/
theorem zeta_em4_error {s : ℂ} (hs : s ∈ QP) {N : ℕ} (hN : 2 ≤ N) :
    ‖riemannZeta s - (∑ i ∈ Finset.range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
        + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1))‖
      ≤ ‖P4 s‖ * (((N : ℝ) - 1) ^ (-s.re - 3) / (s.re + 3)) / 720 := by
  rw [zeta_em4 hs (N := N) (by omega)]
  have h : emRHS N s - (∑ i ∈ Finset.range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
        + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1))
      = -∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ) := by
    unfold emRHS; ring
  rw [h, norm_neg]
  exact norm_tail_le hs.1 (ne_one_of_QP hs) hN

end HardyFirstZero

end

section






/-!
# Certified Interval Evaluation

Exact rational interval arithmetic with kernel-checked soundness. This is the
Lean analogue of `zeta/rigor.py`'s ball arithmetic: every operation returns an
interval **together with a proved containment lemma**, so a chain of
operations carries its enclosure by construction and nothing is ever silently
upgraded to a certificate.

Two layers:

* `Interval`: closed rational intervals `[lo, hi]` regarded as sets of reals
  via `Interval.contains`, with sound `exact` / `add` / `neg` / `sub` / `mul`.
* `ComplexInterval`: axis-aligned rational rectangles in `ℂ`, componentwise
  on `re` / `im`, with the complex product routed through the real layer via
  `Complex.mul_re` / `Complex.mul_im`.

The only genuinely mathematical step is interval multiplication: the product
of `a ∈ [xl, xu]` and `b ∈ [yl, yu]` is bounded by the four corner products,
in every sign configuration. That is `mul_corners_le` / `le_mul_corners`
below, proved once over `ℝ` and reused by both layers.

Supports Rung 3 Phase B (rigorous evaluation of Dirichlet partial sums for
the Davenport–Heilbronn certificate, `ZetaLean/DirichletEval.lean`).
-/

namespace ZetaLean

/-- Lower corner bound: if `a ∈ [xl, xu]` and `b ∈ [yl, yu]` then `a * b` is
at least the smallest of the four corner products. -/
theorem mul_corners_le {a b xl xu yl yu : ℝ}
    (hx1 : xl ≤ a) (hx2 : a ≤ xu) (hy1 : yl ≤ b) (hy2 : b ≤ yu) :
    min (min (xl * yl) (xl * yu)) (min (xu * yl) (xu * yu)) ≤ a * b := by
  rcases le_total 0 b with hb | hb
  · -- 0 ≤ b: a * b ≥ xl * b, and xl * b is over a corner of the xl row
    refine le_trans (le_trans (min_le_left _ _) ?_)
      (mul_le_mul_of_nonneg_right hx1 hb)
    rcases le_total 0 xl with h | h
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hy1 h)
    · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hy2 h)
  · -- b ≤ 0: a * b ≥ xu * b, and xu * b is over a corner of the xu row
    refine le_trans (le_trans (min_le_right _ _) ?_)
      (mul_le_mul_of_nonpos_right hx2 hb)
    rcases le_total 0 xu with h | h
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hy1 h)
    · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hy2 h)

/-- Upper corner bound: if `a ∈ [xl, xu]` and `b ∈ [yl, yu]` then `a * b` is
at most the largest of the four corner products. -/
theorem le_mul_corners {a b xl xu yl yu : ℝ}
    (hx1 : xl ≤ a) (hx2 : a ≤ xu) (hy1 : yl ≤ b) (hy2 : b ≤ yu) :
    a * b ≤ max (max (xl * yl) (xl * yu)) (max (xu * yl) (xu * yu)) := by
  rcases le_total 0 b with hb | hb
  · -- 0 ≤ b: a * b ≤ xu * b, bounded by a corner of the xu row
    refine le_trans (mul_le_mul_of_nonneg_right hx2 hb)
      (le_trans ?_ (le_max_right _ _))
    rcases le_total 0 xu with h | h
    · exact le_trans (mul_le_mul_of_nonneg_left hy2 h) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_left hy1 h) (le_max_left _ _)
  · -- b ≤ 0: a * b ≤ xl * b, bounded by a corner of the xl row
    refine le_trans (mul_le_mul_of_nonpos_right hx1 hb)
      (le_trans ?_ (le_max_left _ _))
    rcases le_total 0 xl with h | h
    · exact le_trans (mul_le_mul_of_nonneg_left hy2 h) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_left hy1 h) (le_max_left _ _)

/-- A closed rational interval `[lo, hi]`, the certified enclosure primitive. -/
structure Interval where
  lo : ℚ
  hi : ℚ
  le : lo ≤ hi
  deriving Repr, DecidableEq

namespace Interval

/-- The set of reals an interval encloses. -/
def contains (x : Interval) (r : ℝ) : Prop :=
  (x.lo : ℝ) ≤ r ∧ r ≤ (x.hi : ℝ)

/-- The degenerate interval `[q, q]`. -/
def exact (q : ℚ) : Interval :=
  { lo := q, hi := q, le := le_refl q }

theorem contains_exact (q : ℚ) : (exact q).contains (q : ℝ) :=
  ⟨le_refl _, le_refl _⟩

def add (x y : Interval) : Interval :=
  { lo := x.lo + y.lo,
    hi := x.hi + y.hi,
    le := add_le_add x.le y.le }

theorem contains_add {x y : Interval} {a b : ℝ}
    (hx : x.contains a) (hy : y.contains b) : (x.add y).contains (a + b) := by
  refine ⟨?_, ?_⟩ <;> simp only [add] <;> push_cast
  · exact add_le_add hx.1 hy.1
  · exact add_le_add hx.2 hy.2

def neg (x : Interval) : Interval :=
  { lo := -x.hi,
    hi := -x.lo,
    le := neg_le_neg x.le }

theorem contains_neg {x : Interval} {a : ℝ}
    (hx : x.contains a) : x.neg.contains (-a) := by
  refine ⟨?_, ?_⟩ <;> simp only [neg] <;> push_cast
  · exact neg_le_neg hx.2
  · exact neg_le_neg hx.1

def sub (x y : Interval) : Interval :=
  x.add y.neg

theorem contains_sub {x y : Interval} {a b : ℝ}
    (hx : x.contains a) (hy : y.contains b) : (x.sub y).contains (a - b) :=
  sub_eq_add_neg a b ▸ contains_add hx (contains_neg hy)

/-- Interval product: the enclosure is the min/max of the four corner
products, which is sound in every sign configuration (`mul_corners_le`,
`le_mul_corners`). -/
def mul (x y : Interval) : Interval :=
  { lo := min (min (x.lo * y.lo) (x.lo * y.hi)) (min (x.hi * y.lo) (x.hi * y.hi)),
    hi := max (max (x.lo * y.lo) (x.lo * y.hi)) (max (x.hi * y.lo) (x.hi * y.hi)),
    le := le_trans (le_trans (min_le_left _ _) (min_le_left _ _))
      (le_trans (le_max_left _ _) (le_max_left _ _)) }

theorem contains_mul {x y : Interval} {a b : ℝ}
    (hx : x.contains a) (hy : y.contains b) : (x.mul y).contains (a * b) := by
  refine ⟨?_, ?_⟩ <;> simp only [mul] <;> push_cast
  · exact mul_corners_le hx.1 hx.2 hy.1 hy.2
  · exact le_mul_corners hx.1 hx.2 hy.1 hy.2

end Interval

/-- An axis-aligned rational rectangle in `ℂ`: certified enclosures for the
real and imaginary parts. -/
structure ComplexInterval where
  re : Interval
  im : Interval
  deriving Repr, DecidableEq

namespace ComplexInterval

/-- The set of complex numbers a rectangle encloses. -/
def contains (x : ComplexInterval) (z : ℂ) : Prop :=
  x.re.contains z.re ∧ x.im.contains z.im

/-- The degenerate rectangle `{q + r*I}`. -/
def exact (q r : ℚ) : ComplexInterval :=
  { re := Interval.exact q, im := Interval.exact r }

theorem contains_exact (q r : ℚ) :
    (exact q r).contains ⟨(q : ℝ), (r : ℝ)⟩ :=
  ⟨Interval.contains_exact q, Interval.contains_exact r⟩

theorem contains_zero : (exact 0 0).contains 0 := by
  constructor <;> simp [exact, Interval.contains, Interval.exact]

def add (x y : ComplexInterval) : ComplexInterval :=
  { re := x.re.add y.re, im := x.im.add y.im }

theorem contains_add {x y : ComplexInterval} {z w : ℂ}
    (hx : x.contains z) (hy : y.contains w) : (x.add y).contains (z + w) :=
  ⟨Interval.contains_add hx.1 hy.1, Interval.contains_add hx.2 hy.2⟩

def neg (x : ComplexInterval) : ComplexInterval :=
  { re := x.re.neg, im := x.im.neg }

theorem contains_neg {x : ComplexInterval} {z : ℂ}
    (hx : x.contains z) : x.neg.contains (-z) :=
  ⟨Interval.contains_neg hx.1, Interval.contains_neg hx.2⟩

def sub (x y : ComplexInterval) : ComplexInterval :=
  { re := x.re.sub y.re, im := x.im.sub y.im }

theorem contains_sub {x y : ComplexInterval} {z w : ℂ}
    (hx : x.contains z) (hy : y.contains w) : (x.sub y).contains (z - w) :=
  ⟨Interval.contains_sub hx.1 hy.1, Interval.contains_sub hx.2 hy.2⟩

/-- Complex product, routed through the real layer:
`(z*w).re = z.re*w.re − z.im*w.im` and `(z*w).im = z.re*w.im + z.im*w.re`. -/
def mul (x y : ComplexInterval) : ComplexInterval :=
  { re := (x.re.mul y.re).sub (x.im.mul y.im),
    im := (x.re.mul y.im).add (x.im.mul y.re) }

theorem contains_mul {x y : ComplexInterval} {z w : ℂ}
    (hx : x.contains z) (hy : y.contains w) : (x.mul y).contains (z * w) := by
  refine ⟨?_, ?_⟩
  · have h := Interval.contains_sub
      (Interval.contains_mul hx.1 hy.1) (Interval.contains_mul hx.2 hy.2)
    simpa [mul, Complex.mul_re] using h
  · have h := Interval.contains_add
      (Interval.contains_mul hx.1 hy.2) (Interval.contains_mul hx.2 hy.1)
    simpa [mul, Complex.mul_im] using h

end ComplexInterval

end ZetaLean

end

section







/-!
# Certified interval `exp` and `log`

The first stone of rung 3's numeric half.  `ZetaLean/DHZeroCriterion.lean`
reduced the Davenport-Heilbronn theorem to two interval inequalities about
`DH`; discharging them inside the kernel requires evaluating terms
`n^{-s} = exp(-s·log n)` with certified enclosures.  This file supplies the
real elementary functions that evaluation is made of, on the `Interval`
layer of `ZetaLean/Rigor.lean`:

* `Interval.exp1`, certified `exp` on intervals inside `[-1, 1]`: Taylor
  partial sums at the rational endpoints, inflated by the Lagrange remainder
  of Mathlib's `Real.exp_bound`, tightened by monotonicity (endpoints
  suffice; no interval Taylor needed).
* `Interval.expI`: `exp` on intervals inside `[-2^k, 2^k]`, by `k`
  halvings and certified squarings (`exp t = exp(t/2)²`).
* `Interval.log1`: certified `log` on intervals inside `(0, 2)`, from the
  alternating series bound `Real.abs_log_sub_add_sum_range_le`, again
  tightened by monotonicity.
* `Interval.log2I`: an enclosure of `log 2 = -log(1/2)`, the anchor for
  extending `log1` to all positive rationals by binary reduction
  (`log q = k·log 2 + log(q/2^k)`, future work).

Every operation returns an interval together with a containment theorem; the
smoke tests at the bottom (`exp_one_gt`, …) kernel-check concrete digits of
`e` and `log 2` end-to-end, which is the point: the same pipeline, pointed
at `DH`, is what will eventually discharge the two hypotheses of
`davenport_heilbronn_of_certified_disk`.
-/

namespace ZetaLean.Interval

open Finset

/-! ### Certified `exp` on `[-1, 1]` -/

/-- Rational Taylor partial sum of `exp`. -/
def expSum (n : ℕ) (q : ℚ) : ℚ :=
  ∑ i ∈ Finset.range n, q ^ i / i.factorial

/-- Rational Lagrange remainder bound, matching `Real.exp_bound`. -/
def expRem (n : ℕ) (q : ℚ) : ℚ :=
  |q| ^ n * ((n + 1) / (n.factorial * n))

private lemma expSum_cast (n : ℕ) (q : ℚ) :
    ((expSum n q : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (q : ℝ) ^ i / i.factorial := by
  unfold expSum
  push_cast
  rfl

private lemma expRem_cast (n : ℕ) (q : ℚ) :
    ((expRem n q : ℚ) : ℝ) = |(q : ℝ)| ^ n * ((n + 1) / (n.factorial * n)) := by
  unfold expRem
  push_cast
  rfl

/-- Taylor lower bound for `exp` at a rational point. -/
theorem exp_lower {n : ℕ} (hn : 0 < n) {q : ℚ} (hq : |q| ≤ 1) :
    ((expSum n q - expRem n q : ℚ) : ℝ) ≤ Real.exp q := by
  have hq' : |(q : ℝ)| ≤ 1 := by exact_mod_cast hq
  have h := Real.exp_bound hq' hn
  have h1 := (abs_sub_le_iff.mp h).1
  have h2 := (abs_sub_le_iff.mp h).2
  push_cast
  rw [expSum_cast, expRem_cast]
  have hsucc : (n.succ : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hsucc] at h1 h2
  linarith

/-- Taylor upper bound for `exp` at a rational point. -/
theorem exp_upper {n : ℕ} (hn : 0 < n) {q : ℚ} (hq : |q| ≤ 1) :
    Real.exp q ≤ ((expSum n q + expRem n q : ℚ) : ℝ) := by
  have hq' : |(q : ℝ)| ≤ 1 := by exact_mod_cast hq
  have h := Real.exp_bound hq' hn
  have h1 := (abs_sub_le_iff.mp h).1
  have h2 := (abs_sub_le_iff.mp h).2
  push_cast
  rw [expSum_cast, expRem_cast]
  have hsucc : (n.succ : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hsucc] at h1 h2
  linarith

/-- Certified `exp` on an interval inside `[-1, 1]`: Taylor at the two
endpoints plus monotonicity.  The `max` in `hi` only discharges the
`lo ≤ hi` obligation; soundness never routes through it. -/
def exp1 (n : ℕ) (x : Interval) : Interval :=
  { lo := expSum n x.lo - expRem n x.lo,
    hi := max (expSum n x.hi + expRem n x.hi) (expSum n x.lo - expRem n x.lo),
    le := le_max_right _ _ }

theorem contains_exp1 {n : ℕ} (hn : 0 < n) {x : Interval} {t : ℝ}
    (hx : x.contains t) (hlo : -1 ≤ x.lo) (hhi : x.hi ≤ 1) :
    (exp1 n x).contains (Real.exp t) := by
  have hqlo : |x.lo| ≤ 1 := abs_le.mpr ⟨hlo, x.le.trans hhi⟩
  have hqhi : |x.hi| ≤ 1 := abs_le.mpr ⟨hlo.trans x.le, hhi⟩
  refine ⟨?_, ?_⟩
  · exact (exp_lower hn hqlo).trans (Real.exp_le_exp.mpr hx.1)
  · have h2 : Real.exp t ≤ ((expSum n x.hi + expRem n x.hi : ℚ) : ℝ) :=
      (Real.exp_le_exp.mpr hx.2).trans (exp_upper hn hqhi)
    refine h2.trans ?_
    change ((expSum n x.hi + expRem n x.hi : ℚ) : ℝ) ≤ ((exp1 n x).hi : ℝ)
    rw [exp1, Rat.cast_max]
    exact le_max_left _ _

/-! ### Range extension by halving and squaring -/

/-- Exact halving (tighter than routing through `mul`). -/
def halve (x : Interval) : Interval :=
  { lo := x.lo / 2, hi := x.hi / 2,
    le := by have := x.le; linarith }

theorem contains_halve {x : Interval} {t : ℝ} (hx : x.contains t) :
    x.halve.contains (t / 2) := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩ <;> simp only [halve] <;> push_cast <;> linarith

/-- Certified `exp` on an interval inside `[-2^k, 2^k]`: halve `k` times
into `[-1, 1]`, take `exp1`, square back up (`exp t = exp(t/2)²`). -/
def expI (n : ℕ) : ℕ → Interval → Interval
  | 0, x => exp1 n x
  | k + 1, x =>
    let y := expI n k x.halve
    y.mul y

theorem contains_expI (n : ℕ) (hn : 0 < n) :
    ∀ (k : ℕ) (x : Interval) (t : ℝ), x.contains t →
      -(2 ^ k : ℚ) ≤ x.lo → x.hi ≤ (2 ^ k : ℚ) →
      (expI n k x).contains (Real.exp t)
  | 0, x, t, hx, hlo, hhi => by
    refine contains_exp1 hn hx ?_ ?_
    · simpa using hlo
    · simpa using hhi
  | k + 1, x, t, hx, hlo, hhi => by
    rw [pow_succ] at hlo hhi
    have hy : (expI n k x.halve).contains (Real.exp (t / 2)) := by
      refine contains_expI n hn k x.halve (t / 2) (contains_halve hx) ?_ ?_
      · simp only [halve]; linarith
      · simp only [halve]; linarith
    have hmul := Interval.contains_mul hy hy
    rw [show Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t by
      rw [← Real.exp_add]; ring_nf] at hmul
    exact hmul

/-! ### Certified `log` on `(0, 2)` -/

/-- Rational partial sum of the series for `-log(1-q)`. -/
def logSum (n : ℕ) (q : ℚ) : ℚ :=
  ∑ i ∈ Finset.range n, q ^ (i + 1) / (i + 1)

/-- Rational tail bound, matching `Real.abs_log_sub_add_sum_range_le`. -/
def logRem (n : ℕ) (q : ℚ) : ℚ :=
  |q| ^ (n + 1) / (1 - |q|)

private lemma logSum_cast (n : ℕ) (q : ℚ) :
    ((logSum n q : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (q : ℝ) ^ (i + 1) / (i + 1) := by
  unfold logSum
  push_cast
  rfl

private lemma logRem_cast (n : ℕ) (q : ℚ) :
    ((logRem n q : ℚ) : ℝ) = |(q : ℝ)| ^ (n + 1) / (1 - |(q : ℝ)|) := by
  unfold logRem
  push_cast
  rfl

/-- Series lower bound for `log (1 - q)` at a rational point. -/
theorem log_one_sub_lower {n : ℕ} {q : ℚ} (hq : |q| < 1) :
    ((-logSum n q - logRem n q : ℚ) : ℝ) ≤ Real.log (1 - q) := by
  have hq' : |(q : ℝ)| < 1 := by exact_mod_cast hq
  have h := Real.abs_log_sub_add_sum_range_le hq' n
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  push_cast
  rw [logSum_cast, logRem_cast]
  linarith

/-- Series upper bound for `log (1 - q)` at a rational point. -/
theorem log_one_sub_upper {n : ℕ} {q : ℚ} (hq : |q| < 1) :
    Real.log (1 - q) ≤ ((-logSum n q + logRem n q : ℚ) : ℝ) := by
  have hq' : |(q : ℝ)| < 1 := by exact_mod_cast hq
  have h := Real.abs_log_sub_add_sum_range_le hq' n
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  push_cast
  rw [logSum_cast, logRem_cast]
  linarith

/-- Certified `log` on an interval inside `(0, 2)`: the series for
`log(1-x)` at the endpoints `x = 1 - lo`, `x = 1 - hi`, plus monotonicity. -/
def log1 (n : ℕ) (x : Interval) : Interval :=
  { lo := -logSum n (1 - x.lo) - logRem n (1 - x.lo),
    hi := max (-logSum n (1 - x.hi) + logRem n (1 - x.hi))
      (-logSum n (1 - x.lo) - logRem n (1 - x.lo)),
    le := le_max_right _ _ }

theorem contains_log1 {n : ℕ} {x : Interval} {t : ℝ}
    (hx : x.contains t) (hlo : 0 < x.lo) (hhi : x.hi < 2) :
    (log1 n x).contains (Real.log t) := by
  have hlo2 : x.lo < 2 := lt_of_le_of_lt x.le hhi
  have hhi0 : 0 < x.hi := lt_of_lt_of_le hlo x.le
  have hq1 : |(1 - x.lo : ℚ)| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hq2 : |(1 - x.hi : ℚ)| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by exact_mod_cast hlo) hx.1
  have hxlo : (0 : ℝ) < (x.lo : ℝ) := by exact_mod_cast hlo
  have hxhi : (0 : ℝ) < (x.hi : ℝ) := by exact_mod_cast hhi0
  have hcast_lo : (1 : ℝ) - ((1 - x.lo : ℚ) : ℝ) = (x.lo : ℝ) := by push_cast; ring
  have hcast_hi : (1 : ℝ) - ((1 - x.hi : ℚ) : ℝ) = (x.hi : ℝ) := by push_cast; ring
  refine ⟨?_, ?_⟩
  · have h1 := log_one_sub_lower (n := n) hq1
    rw [hcast_lo] at h1
    exact h1.trans ((Real.log_le_log_iff hxlo ht0).mpr hx.1)
  · have h2 := log_one_sub_upper (n := n) hq2
    rw [hcast_hi] at h2
    have h3 : Real.log t ≤ ((-logSum n (1 - x.hi) + logRem n (1 - x.hi) : ℚ) : ℝ) :=
      ((Real.log_le_log_iff ht0 hxhi).mpr hx.2).trans h2
    refine h3.trans ?_
    change _ ≤ (((log1 n x).hi : ℚ) : ℝ)
    rw [log1, Rat.cast_max]
    exact le_max_left _ _

/-- An enclosure of `log 2 = -log(1/2)`. -/
def log2I (n : ℕ) : Interval :=
  (log1 n (Interval.exact (1 / 2))).neg

theorem contains_log2I (n : ℕ) : (log2I n).contains (Real.log 2) := by
  have h := contains_log1 (n := n) (Interval.contains_exact (1 / 2))
    (by norm_num [Interval.exact]) (by norm_num [Interval.exact])
  have h2 := Interval.contains_neg h
  rw [show -Real.log ((1 / 2 : ℚ) : ℝ) = Real.log 2 by
    rw [← Real.log_inv]; norm_num] at h2
  exact h2

/-! ### `log` of any positive rational -/

/-- Certified `log q` for a positive rational, by the binary reduction the
module docstring promised: `log q = k·log 2 + log (q / 2^k)`, with the second
summand landed in the domain of `log1`.  The caller picks `k`;
`contains_logQ` demands exactly the side conditions that make the choice
correct, and both are `norm_num`-decidable at any concrete call site. -/
def logQ (n k : ℕ) (q : ℚ) : Interval :=
  ((Interval.exact (k : ℚ)).mul (log2I n)).add (log1 n (Interval.exact (q / 2 ^ k)))

theorem contains_logQ {n k : ℕ} {q : ℚ} (h0 : 0 < q / 2 ^ k) (h2 : q / 2 ^ k < 2) :
    (logQ n k q).contains (Real.log q) := by
  have h2k : (0 : ℚ) < 2 ^ k := by positivity
  have hq0 : (0 : ℚ) < q := by
    have := mul_pos h0 h2k
    rwa [div_mul_cancel₀ _ h2k.ne'] at this
  have hid : Real.log q = (k : ℝ) * Real.log 2 + Real.log ((q : ℝ) / 2 ^ k) := by
    rw [Real.log_div (by exact_mod_cast hq0.ne') (by positivity), Real.log_pow]
    ring
  have hA := Interval.contains_mul (Interval.contains_exact (k : ℚ)) (contains_log2I n)
  have hB := contains_log1 (n := n) (Interval.contains_exact (q / 2 ^ k)) h0 h2
  have hC := Interval.contains_add hA hB
  have hcast : ((q / 2 ^ k : ℚ) : ℝ) = (q : ℝ) / 2 ^ k := by push_cast; ring
  rw [hcast] at hC
  rw [hid, show ((k : ℝ)) = (((k : ℚ) : ℝ)) by push_cast; rfl]
  exact hC

/-! ### Smoke tests: kernel-checked digits of `e` and `log 2`

These are the end-to-end proof that the pipeline computes: the same
machinery, pointed at `DH`'s Dirichlet terms, is what will discharge the
hypotheses of `davenport_heilbronn_of_certified_disk`. -/

theorem exp_one_gt : (2.71828 : ℝ) < Real.exp 1 := by
  obtain ⟨h1, -⟩ := contains_exp1 (n := 10) (by norm_num) (x := Interval.exact 1)
    (Interval.contains_exact 1) (by norm_num [Interval.exact]) (by norm_num [Interval.exact])
  push_cast at h1
  refine lt_of_lt_of_le ?_ h1
  norm_num [exp1, Interval.exact, expSum, expRem, Finset.sum_range_succ, Nat.factorial]

theorem exp_one_lt : Real.exp 1 < (2.71829 : ℝ) := by
  obtain ⟨-, h2⟩ := contains_exp1 (n := 10) (by norm_num) (x := Interval.exact 1)
    (Interval.contains_exact 1) (by norm_num [Interval.exact]) (by norm_num [Interval.exact])
  push_cast at h2
  refine lt_of_le_of_lt h2 ?_
  norm_num [exp1, Interval.exact, expSum, expRem, Finset.sum_range_succ, Nat.factorial]

theorem exp_four_lt : Real.exp 4 < (54.6 : ℝ) := by
  have h := contains_expI 8 (by norm_num) 2 (Interval.exact 4) ((4 : ℚ) : ℝ)
    (Interval.contains_exact 4) (by norm_num [Interval.exact]) (by norm_num [Interval.exact])
  obtain ⟨-, h2⟩ := h
  push_cast at h2
  refine lt_of_le_of_lt h2 ?_
  norm_num [expI, exp1, halve, Interval.exact, Interval.mul, expSum, expRem,
    Finset.sum_range_succ, Nat.factorial]

theorem log_two_gt : (0.6931 : ℝ) < Real.log 2 := by
  obtain ⟨h1, -⟩ := contains_log2I 20
  refine lt_of_lt_of_le ?_ h1
  norm_num [log2I, log1, Interval.exact, Interval.neg, logSum, logRem,
    Finset.sum_range_succ]

theorem log_two_lt : Real.log 2 < (0.6932 : ℝ) := by
  obtain ⟨-, h2⟩ := contains_log2I 20
  refine lt_of_le_of_lt h2 ?_
  norm_num [log2I, log1, Interval.exact, Interval.neg, logSum, logRem,
    Finset.sum_range_succ]

theorem log_ten_gt : (2.30257 : ℝ) < Real.log 10 := by
  obtain ⟨h1, -⟩ := contains_logQ (n := 20) (k := 3) (q := 10)
    (by norm_num) (by norm_num)
  refine lt_of_lt_of_le ?_ h1
  norm_num [logQ, log2I, log1, Interval.exact, Interval.neg, Interval.mul,
    Interval.add, logSum, logRem, Finset.sum_range_succ]

theorem log_ten_lt : Real.log 10 < (2.30259 : ℝ) := by
  obtain ⟨-, h2⟩ := contains_logQ (n := 20) (k := 3) (q := 10)
    (by norm_num) (by norm_num)
  refine lt_of_le_of_lt h2 ?_
  norm_num [logQ, log2I, log1, Interval.exact, Interval.neg, Interval.mul,
    Interval.add, logSum, logRem, Finset.sum_range_succ]

end ZetaLean.Interval

end

section


/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/






/-!
# Certified complex `exp`, and the Dirichlet term `n^{-s}`

The second and third stones of rung 3's numeric half.  `IntervalExp.lean`
certified the real elementary functions; this file lifts `exp` to `ℂ` on the
`ComplexInterval` layer of `ZetaLean/Rigor.lean` and then ties the Dirichlet
term `n^{-s} = exp(-s · log n)` to a kernel-checked enclosure, the gap
`ZetaLean/OracleDH.lean` names as “nothing here is kernel-checked about
`n^{-s}` itself”.

* `ComplexInterval.expSumC`: the Taylor partial sum `∑_{i<n} z^i/i!` as
  rectangle arithmetic, sound by induction from `Rigor.lean`.
* `ComplexInterval.expSmall`, `exp` on a box with `normBound ≤ 1`: the
  Taylor sum inflated by the Lagrange-style remainder of Mathlib's
  `Complex.exp_bound`.  Since `exp(it)` has real part `cos t` and imaginary
  part `sin t`, this is simultaneously certified sin/cos, no separate
  trigonometric development is needed.
* `ComplexInterval.expC`: `exp` on a box with `normBound ≤ 2^k`, by `k`
  halvings and certified squarings (`exp z = exp(z/2)²`), mirroring
  `Interval.expI`.
* `ComplexInterval.dirichletTerm`: the enclosure of `m^{-s}` for natural
  `m ≥ 1` and rational `s`, composed from `Interval.logQ` and `expC` through
  Mathlib's `cpow_def_of_ne_zero` bridge.  `contains_dirichletTerm` is the
  theorem the oracle could not fake: the box is computed by kernel-reducible
  rational arithmetic and provably contains `(m : ℂ) ^ (-s)`.

What remains open of rung 3 Phase B after this file: the tail bound for the
analytic continuation (the series does not converge absolutely at
`Re s ≈ 0.808`; see the note at the bottom of `OracleDH.lean`), and the
assembly of the two disk inequalities of
`davenport_heilbronn_of_certified_disk` from term enclosures.

The smoke tests kernel-check digits of `cos 1`, `sin 1` and `cos 2`
end-to-end through the complex pipeline.
-/

namespace ZetaLean

/-- `|t| ≤ max |lo| |hi|` for `t ∈ [lo, hi]`: the endpoint bound that turns
interval containment into a norm bound. -/
private theorem abs_le_max_abs_endpoints {lo t hi : ℝ} (h1 : lo ≤ t) (h2 : t ≤ hi) :
    |t| ≤ max |lo| |hi| := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · calc -(max |lo| |hi|) ≤ -|lo| := neg_le_neg (le_max_left _ _)
      _ ≤ lo := neg_abs_le lo
      _ ≤ t := h1
  · calc t ≤ hi := h2
      _ ≤ |hi| := le_abs_self hi
      _ ≤ max |lo| |hi| := le_max_right _ _

namespace ComplexInterval

open Finset

/-! ### Powers, rational scaling, Taylor partial sums -/

/-- Interval power by iterated corner multiplication. -/
def powI (x : ComplexInterval) : ℕ → ComplexInterval
  | 0 => exact 1 0
  | m + 1 => (powI x m).mul x

theorem contains_powI {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
    ∀ m, (powI x m).contains (z ^ m)
  | 0 => by
    rw [pow_zero]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      norm_num [powI, exact, Interval.exact, Interval.contains]
  | m + 1 => by
    rw [pow_succ]
    exact contains_mul (contains_powI hx m) hx

/-- Scale a box by a rational scalar (viewed in `ℂ` through `ℝ`). -/
def smulQ (q : ℚ) (x : ComplexInterval) : ComplexInterval :=
  (exact q 0).mul x

theorem contains_smulQ {q : ℚ} {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
    (smulQ q x).contains ((((q : ℚ) : ℝ) : ℂ) * z) := by
  have hq : (exact q 0).contains (((q : ℝ) : ℂ)) := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      norm_num [exact, Interval.exact, Interval.contains]
  exact contains_mul hq hx

/-- The Taylor partial sum `∑_{i<m} z^i / i!` as rectangle arithmetic. -/
def expSumC (x : ComplexInterval) : ℕ → ComplexInterval
  | 0 => exact 0 0
  | m + 1 => (expSumC x m).add (smulQ (1 / m.factorial) (powI x m))

theorem contains_expSumC {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
    ∀ m, (expSumC x m).contains (∑ i ∈ range m, z ^ i / i.factorial)
  | 0 => by simpa [expSumC] using contains_zero
  | m + 1 => by
    rw [Finset.sum_range_succ]
    have h := contains_smulQ (q := 1 / m.factorial) (contains_powI hx m)
    rw [show ((((1 / m.factorial : ℚ) : ℝ)) : ℂ) * z ^ m = z ^ m / m.factorial by
      push_cast; ring] at h
    exact contains_add (contains_expSumC hx m) h

/-! ### Norm bound and remainder inflation -/

/-- A rational bound on `‖z‖` valid for every `z` in the box: endpoint bounds
per component, combined by the triangle inequality `‖z‖ ≤ |re z| + |im z|`. -/
def normBound (x : ComplexInterval) : ℚ :=
  max |x.re.lo| |x.re.hi| + max |x.im.lo| |x.im.hi|

theorem norm_le_normBound {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
    ‖z‖ ≤ (normBound x : ℝ) := by
  have hre : |z.re| ≤ ((max |x.re.lo| |x.re.hi| : ℚ) : ℝ) := by
    push_cast
    exact abs_le_max_abs_endpoints hx.1.1 hx.1.2
  have him : |z.im| ≤ ((max |x.im.lo| |x.im.hi| : ℚ) : ℝ) := by
    push_cast
    exact abs_le_max_abs_endpoints hx.2.1 hx.2.2
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ _ := add_le_add hre him
    _ = ((normBound x : ℚ) : ℝ) := by rw [normBound]; push_cast; ring

/-- Widen a box by `|r|` in every direction. -/
def inflate (x : ComplexInterval) (r : ℚ) : ComplexInterval :=
  { re := { lo := x.re.lo - |r|, hi := x.re.hi + |r|,
            le := by have h1 := x.re.le; have h2 := abs_nonneg r; linarith },
    im := { lo := x.im.lo - |r|, hi := x.im.hi + |r|,
            le := by have h1 := x.im.le; have h2 := abs_nonneg r; linarith } }

/-- Soundness of `inflate`: if the box contains `z` and `‖w - z‖ ≤ r`, the
inflated box contains `w`. -/
theorem contains_inflate {x : ComplexInterval} {z w : ℂ} {r : ℚ}
    (hx : x.contains z) (hw : ‖w - z‖ ≤ (r : ℝ)) : (x.inflate r).contains w := by
  have hre : |w.re - z.re| ≤ |(r : ℝ)| :=
    calc |w.re - z.re| = |(w - z).re| := by rw [Complex.sub_re]
      _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
      _ ≤ (r : ℝ) := hw
      _ ≤ |(r : ℝ)| := le_abs_self _
  have him : |w.im - z.im| ≤ |(r : ℝ)| :=
    calc |w.im - z.im| = |(w - z).im| := by rw [Complex.sub_im]
      _ ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      _ ≤ (r : ℝ) := hw
      _ ≤ |(r : ℝ)| := le_abs_self _
  obtain ⟨hre1, hre2⟩ := abs_le.mp hre
  obtain ⟨him1, him2⟩ := abs_le.mp him
  obtain ⟨⟨ha, hb⟩, hc, hd⟩ := hx
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [inflate] <;> push_cast <;> linarith

/-! ### `exp` on a small box, then on any box by halving and squaring -/

/-- Certified `exp` on a box with `normBound ≤ 1`: Taylor sum plus the
remainder of `Complex.exp_bound`, which is monotone in `‖z‖` and therefore
bounded by the same expression in `normBound`. -/
def expSmall (n : ℕ) (x : ComplexInterval) : ComplexInterval :=
  (expSumC x n).inflate (normBound x ^ n * ((n + 1) / (n.factorial * n)))

theorem contains_expSmall {n : ℕ} (hn : 0 < n) {x : ComplexInterval} {z : ℂ}
    (hx : x.contains z) (hb : normBound x ≤ 1) :
    (expSmall n x).contains (Complex.exp z) := by
  have hzb : ‖z‖ ≤ (normBound x : ℝ) := norm_le_normBound hx
  have hz1 : ‖z‖ ≤ 1 := hzb.trans (by exact_mod_cast hb)
  have h := Complex.exp_bound hz1 hn
  refine contains_inflate (contains_expSumC hx n) (h.trans ?_)
  have h1 : ‖z‖ ^ n ≤ (normBound x : ℝ) ^ n :=
    pow_le_pow_left₀ (norm_nonneg z) hzb n
  have h2 : (0 : ℝ) ≤ (n.succ : ℝ) * ((n.factorial * n : ℝ))⁻¹ := by positivity
  calc ‖z‖ ^ n * ((n.succ : ℝ) * ((n.factorial * n : ℝ))⁻¹)
      ≤ (normBound x : ℝ) ^ n * ((n.succ : ℝ) * ((n.factorial * n : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = ((normBound x ^ n * ((n + 1) / (n.factorial * n)) : ℚ) : ℝ) := by
        push_cast [Nat.succ_eq_add_one]
        ring

/-- Componentwise exact halving. -/
def halveC (x : ComplexInterval) : ComplexInterval :=
  { re := x.re.halve, im := x.im.halve }

theorem contains_halveC {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
    (halveC x).contains (z / 2) := by
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  constructor
  · rw [show (z / 2).re = z.re / 2 by rw [h2, Complex.div_ofReal_re]]
    exact Interval.contains_halve hx.1
  · rw [show (z / 2).im = z.im / 2 by rw [h2, Complex.div_ofReal_im]]
    exact Interval.contains_halve hx.2

theorem normBound_halveC (x : ComplexInterval) :
    normBound (halveC x) = normBound x / 2 := by
  simp only [normBound, halveC, Interval.halve, abs_div, abs_two]
  rw [max_div_div_right (by norm_num : (0 : ℚ) ≤ 2),
    max_div_div_right (by norm_num : (0 : ℚ) ≤ 2)]
  ring

/-- Certified `exp` on a box with `normBound ≤ 2^k`: halve `k` times into
the domain of `expSmall`, square back up (`exp z = exp(z/2)²`). -/
def expC (n : ℕ) : ℕ → ComplexInterval → ComplexInterval
  | 0, x => expSmall n x
  | k + 1, x =>
    let y := expC n k (halveC x)
    y.mul y

theorem contains_expC (n : ℕ) (hn : 0 < n) :
    ∀ (k : ℕ) (x : ComplexInterval) (z : ℂ), x.contains z →
      normBound x ≤ 2 ^ k → (expC n k x).contains (Complex.exp z)
  | 0, x, z, hx, hb => by
    exact contains_expSmall hn hx (by simpa using hb)
  | k + 1, x, z, hx, hb => by
    have hy : (expC n k (halveC x)).contains (Complex.exp (z / 2)) := by
      refine contains_expC n hn k (halveC x) (z / 2) (contains_halveC hx) ?_
      rw [normBound_halveC]
      rw [pow_succ] at hb
      linarith
    have h := contains_mul hy hy
    rwa [show Complex.exp (z / 2) * Complex.exp (z / 2) = Complex.exp z by
      rw [← Complex.exp_add]; ring_nf] at h

/-! ### The Dirichlet term `m^{-s}` -/

/-- The enclosure of `m^{-s}`: `logQ` for `log m`, a corner product with the
exact rectangle for `-s`, and `expC` on the result.  `kL` steers the log
reduction (`m / 2^kL ∈ (0, 2)`), `kE` the exp range reduction
(`normBound ≤ 2^kE`); both side conditions are hypotheses of the containment
theorem, decidable by `norm_num` at any concrete call site. -/
def dirichletTerm (n kL kE : ℕ) (m : ℕ) (sre sim : ℚ) : ComplexInterval :=
  expC n kE ((exact (-sre) (-sim)).mul
    { re := Interval.logQ n kL (m : ℚ), im := Interval.exact 0 })

/-- **The oracle gap, closed for individual terms**: the box computed by
`dirichletTerm` provably contains `(m : ℂ) ^ (-s)`.  Every arithmetic step
is kernel-reducible rational interval arithmetic; the analytic inputs are
Mathlib's `Complex.exp_bound`, the `log` series bound, and the `cpow`
definition, no step is an oracle claim. -/
theorem contains_dirichletTerm {n kL kE : ℕ} (hn : 0 < n) {m : ℕ} (hm : 0 < m)
    {sre sim : ℚ}
    (h0 : 0 < (m : ℚ) / 2 ^ kL) (h2 : (m : ℚ) / 2 ^ kL < 2)
    (hb : normBound ((exact (-sre) (-sim)).mul
      { re := Interval.logQ n kL (m : ℚ), im := Interval.exact 0 }) ≤ 2 ^ kE) :
    (dirichletTerm n kL kE m sre sim).contains
      ((m : ℂ) ^ (-(⟨(sre : ℝ), (sim : ℝ)⟩ : ℂ))) := by
  -- the log box contains `log m`, viewed in `ℂ`
  have hlogQ := Interval.contains_logQ (n := n) (k := kL) (q := (m : ℚ)) h0 h2
  rw [show (((m : ℚ) : ℝ)) = ((m : ℕ) : ℝ) by push_cast; rfl] at hlogQ
  have hL : ({ re := Interval.logQ n kL (m : ℚ), im := Interval.exact 0 } :
      ComplexInterval).contains ((Real.log m : ℝ) : ℂ) := by
    constructor
    · rw [Complex.ofReal_re]; exact hlogQ
    · rw [Complex.ofReal_im]; norm_num [Interval.contains, Interval.exact]
  -- the exact rectangle contains `-s`
  have hs : (exact (-sre) (-sim)).contains (-(⟨(sre : ℝ), (sim : ℝ)⟩ : ℂ)) := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      norm_num [exact, Interval.exact, Interval.contains, Complex.neg_re, Complex.neg_im]
  -- multiply and exponentiate
  have hexp := contains_expC n hn kE _ _ (contains_mul hs hL) hb
  -- bridge to `cpow`
  have hm0 : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [show ((m : ℂ) ^ (-(⟨(sre : ℝ), (sim : ℝ)⟩ : ℂ))) =
      Complex.exp (-(⟨(sre : ℝ), (sim : ℝ)⟩ : ℂ) * ((Real.log m : ℝ) : ℂ)) by
    rw [Complex.cpow_def_of_ne_zero hm0,
      show Complex.log ((m : ℕ) : ℂ) = ((Real.log m : ℝ) : ℂ) by
        rw [show ((m : ℕ) : ℂ) = (((m : ℕ) : ℝ) : ℂ) by push_cast; rfl,
          Complex.ofReal_log (by positivity : (0 : ℝ) ≤ ((m : ℕ) : ℝ))]
    , mul_comm]]
  exact hexp

/-! ### Outward rounding

Exact rational interval arithmetic doubles digit counts at every squaring:
one Dirichlet term at the oracle point, evaluated without rounding, has
560000-bit endpoints.  `coarsen` is the primitive Arb has and the exact
layer lacked: round the endpoints outward to `p` dyadic bits.  Containment
is preserved, the box only grows, by at most `2^{-p}` per side. -/

/-- Round an interval's endpoints outward to `p` dyadic bits. -/
def _root_.ZetaLean.Interval.coarsen (p : ℕ) (x : Interval) : Interval :=
  { lo := (⌊x.lo * 2 ^ p⌋ : ℤ) / 2 ^ p,
    hi := (⌈x.hi * 2 ^ p⌉ : ℤ) / 2 ^ p,
    le := by
      have h2 : (0 : ℚ) < 2 ^ p := by positivity
      rw [div_le_div_iff_of_pos_right h2]
      calc ((⌊x.lo * 2 ^ p⌋ : ℤ) : ℚ) ≤ x.lo * 2 ^ p := Int.floor_le _
        _ ≤ x.hi * 2 ^ p := by nlinarith [x.le]
        _ ≤ ((⌈x.hi * 2 ^ p⌉ : ℤ) : ℚ) := Int.le_ceil _ }

theorem _root_.ZetaLean.Interval.contains_coarsen (p : ℕ) {x : Interval} {t : ℝ}
    (hx : x.contains t) : (x.coarsen p).contains t := by
  obtain ⟨h1, h2⟩ := hx
  have h2p : (0 : ℝ) < 2 ^ p := by positivity
  constructor
  · show (((⌊x.lo * 2 ^ p⌋ : ℤ) / 2 ^ p : ℚ) : ℝ) ≤ t
    rw [show (((⌊x.lo * 2 ^ p⌋ : ℤ) / 2 ^ p : ℚ) : ℝ)
        = ((⌊x.lo * 2 ^ p⌋ : ℤ) : ℝ) / 2 ^ p by push_cast; ring,
      div_le_iff₀ h2p]
    calc ((⌊x.lo * 2 ^ p⌋ : ℤ) : ℝ) ≤ ((x.lo * 2 ^ p : ℚ) : ℝ) := by
          exact_mod_cast Int.floor_le _
      _ = (x.lo : ℝ) * 2 ^ p := by push_cast; ring
      _ ≤ t * 2 ^ p := by nlinarith
  · show t ≤ (((⌈x.hi * 2 ^ p⌉ : ℤ) / 2 ^ p : ℚ) : ℝ)
    rw [show (((⌈x.hi * 2 ^ p⌉ : ℤ) / 2 ^ p : ℚ) : ℝ)
        = ((⌈x.hi * 2 ^ p⌉ : ℤ) : ℝ) / 2 ^ p by push_cast; ring,
      le_div_iff₀ h2p]
    calc t * 2 ^ p ≤ (x.hi : ℝ) * 2 ^ p := by nlinarith
      _ = ((x.hi * 2 ^ p : ℚ) : ℝ) := by push_cast; ring
      _ ≤ ((⌈x.hi * 2 ^ p⌉ : ℤ) : ℝ) := by exact_mod_cast Int.le_ceil _

/-- Componentwise outward rounding of a rectangle. -/
def coarsen (p : ℕ) (x : ComplexInterval) : ComplexInterval :=
  { re := x.re.coarsen p, im := x.im.coarsen p }

theorem contains_coarsen (p : ℕ) {x : ComplexInterval} {z : ℂ}
    (hx : x.contains z) : (x.coarsen p).contains z :=
  ⟨Interval.contains_coarsen p hx.1, Interval.contains_coarsen p hx.2⟩

/-- `expC` with outward rounding to `p` bits after every squaring, the
digit-growth-free evaluator.  Identical enclosure semantics, boxes wider by
at most `2^{-p}` per level. -/
def expCr (n p : ℕ) : ℕ → ComplexInterval → ComplexInterval
  | 0, x => (expSmall n x).coarsen p
  | k + 1, x =>
    let y := expCr n p k (halveC x)
    (y.mul y).coarsen p

theorem contains_expCr (n p : ℕ) (hn : 0 < n) :
    ∀ (k : ℕ) (x : ComplexInterval) (z : ℂ), x.contains z →
      normBound x ≤ 2 ^ k → (expCr n p k x).contains (Complex.exp z)
  | 0, x, z, hx, hb =>
    contains_coarsen p (contains_expSmall hn hx (by simpa using hb))
  | k + 1, x, z, hx, hb => by
    have hy : (expCr n p k (halveC x)).contains (Complex.exp (z / 2)) := by
      refine contains_expCr n p hn k (halveC x) (z / 2) (contains_halveC hx) ?_
      rw [normBound_halveC]
      rw [pow_succ] at hb
      linarith
    have h := contains_mul hy hy
    rw [show Complex.exp (z / 2) * Complex.exp (z / 2) = Complex.exp z by
      rw [← Complex.exp_add]; ring_nf] at h
    exact contains_coarsen p h

/-! ### The boxed-`s` Dirichlet term

The square-contour boundary segments range over sets of `s`, so the
enclosure must accept a rectangle for `s`, not only an exact point.  Same
pipeline; only the `-s` factor changes from an exact rectangle to `S.neg`. -/

/-- The enclosure of `m^{-s}` for every `s` in the box `S`, computed with
outward rounding to `p` bits (`expCr`) so endpoints stay `p`-bit dyadics
instead of doubling digits at every squaring. -/
def dirichletTermBox (n p kL kE : ℕ) (m : ℕ) (S : ComplexInterval) : ComplexInterval :=
  expCr n p kE (S.neg.mul { re := Interval.logQ n kL (m : ℚ), im := Interval.exact 0 })

theorem contains_dirichletTermBox {n p kL kE : ℕ} (hn : 0 < n) {m : ℕ} (hm : 0 < m)
    {S : ComplexInterval} {s : ℂ} (hS : S.contains s)
    (h0 : 0 < (m : ℚ) / 2 ^ kL) (h2 : (m : ℚ) / 2 ^ kL < 2)
    (hb : normBound (S.neg.mul
      { re := Interval.logQ n kL (m : ℚ), im := Interval.exact 0 }) ≤ 2 ^ kE) :
    (dirichletTermBox n p kL kE m S).contains ((m : ℂ) ^ (-s)) := by
  have hlogQ := Interval.contains_logQ (n := n) (k := kL) (q := (m : ℚ)) h0 h2
  rw [show (((m : ℚ) : ℝ)) = ((m : ℕ) : ℝ) by push_cast; rfl] at hlogQ
  have hL : ({ re := Interval.logQ n kL (m : ℚ), im := Interval.exact 0 } :
      ComplexInterval).contains ((Real.log m : ℝ) : ℂ) := by
    constructor
    · rw [Complex.ofReal_re]; exact hlogQ
    · rw [Complex.ofReal_im]; norm_num [Interval.contains, Interval.exact]
  have hexp := contains_expCr n p hn kE _ _ (contains_mul (contains_neg hS) hL) hb
  have hm0 : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [show ((m : ℂ) ^ (-s)) = Complex.exp (-s * ((Real.log m : ℝ) : ℂ)) by
    rw [Complex.cpow_def_of_ne_zero hm0,
      show Complex.log ((m : ℕ) : ℂ) = ((Real.log m : ℝ) : ℂ) by
        rw [show ((m : ℕ) : ℂ) = (((m : ℕ) : ℝ) : ℂ) by push_cast; rfl,
          Complex.ofReal_log (by positivity : (0 : ℝ) ≤ ((m : ℕ) : ℝ))]
    , mul_comm]]
  exact hexp

/-! ### Separating the two Taylor orders

`dirichletTermBox` uses one order `n` for both series it runs: the logarithm
`Interval.logQ n kL m` and the exponential `expCr n p kE`.  Measured on plan v2's
worst grid site, that coupling is what makes the plan infeasible, and the two
orders want opposite things:

* The **width** is set almost entirely by the log.  `logRem n q ≈ q^{n+1}/(1-q)`
  with `q ≤ 1/2`, so at `n = 20` the log carries width `7.6e-6`, which `|s| ≈ 86`
  amplifies to `6.6e-4` and the squaring tower to `3.0e-3`.  Multiplied over the
  `5K` terms of one site that is a box width of `1.5` against a `β` of `0.038`,
  infeasible by a factor of 30, before any Lean is generated.  Raising `kE` or
  the coarsening precision does not touch it: at `kE = 18` and `p = 128` the
  final width is still `3.0e-3`.  Raising the log order does: `n = 28` gives
  `3.0e-8` and `n = 32` gives `1.9e-9`.
* The **literal size** is set almost entirely by the exponential.  `expSmall`
  forms `powI x i` up to `i = n`, so `n` multiplies the endpoint bit-width by
  `n`; that is where the “multi-thousand-bit rationals” that defeated one-shot
  `norm_num` evaluation come from.  The log's own endpoints are small and stay
  small, order 20 to 32 takes them from 91 to 158 bits.

So the orders are split.  `nLog` is raised until the width fits; `nExp` stays
small so the generated literals stay evaluable.  Nothing else changes: the two
series are independent and the containment proof is the same argument. -/

/-- `dirichletTermBox` with the logarithm's Taylor order separated from the
exponential's.  `dirichletTermBox n p kL kE m S` is the `nLog = nExp = n` case. -/
def dirichletTermBox2 (nLog nExp p kL kE : ℕ) (m : ℕ) (S : ComplexInterval) :
    ComplexInterval :=
  expCr nExp p kE (S.neg.mul { re := Interval.logQ nLog kL (m : ℚ), im := Interval.exact 0 })

theorem contains_dirichletTermBox2 {nLog nExp p kL kE : ℕ} (hnL : 0 < nLog)
    (hnE : 0 < nExp) {m : ℕ} (hm : 0 < m) {S : ComplexInterval} {s : ℂ}
    (hS : S.contains s) (h0 : 0 < (m : ℚ) / 2 ^ kL) (h2 : (m : ℚ) / 2 ^ kL < 2)
    (hb : normBound (S.neg.mul
      { re := Interval.logQ nLog kL (m : ℚ), im := Interval.exact 0 }) ≤ 2 ^ kE) :
    (dirichletTermBox2 nLog nExp p kL kE m S).contains ((m : ℂ) ^ (-s)) := by
  have hlogQ := Interval.contains_logQ (n := nLog) (k := kL) (q := (m : ℚ)) h0 h2
  rw [show (((m : ℚ) : ℝ)) = ((m : ℕ) : ℝ) by push_cast; rfl] at hlogQ
  have hL : ({ re := Interval.logQ nLog kL (m : ℚ), im := Interval.exact 0 } :
      ComplexInterval).contains ((Real.log m : ℝ) : ℂ) := by
    constructor
    · rw [Complex.ofReal_re]; exact hlogQ
    · rw [Complex.ofReal_im]; norm_num [Interval.contains, Interval.exact]
  have hexp := contains_expCr nExp p hnE kE _ _ (contains_mul (contains_neg hS) hL) hb
  have hm0 : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [show ((m : ℂ) ^ (-s)) = Complex.exp (-s * ((Real.log m : ℝ) : ℂ)) by
    rw [Complex.cpow_def_of_ne_zero hm0,
      show Complex.log ((m : ℕ) : ℂ) = ((Real.log m : ℝ) : ℂ) by
        rw [show ((m : ℕ) : ℂ) = (((m : ℕ) : ℝ) : ℂ) by push_cast; rfl,
          Complex.ofReal_log (by positivity : (0 : ℝ) ≤ ((m : ℕ) : ℝ))]
    , mul_comm]]
  exact hexp

theorem dirichletTermBox2_self (n p kL kE m : ℕ) (S : ComplexInterval) :
    dirichletTermBox2 n n p kL kE m S = dirichletTermBox n p kL kE m S := rfl

/-! ### Reading a norm lower bound off a computed box -/

/-- The distance from `0` to an interval, `0` when the interval straddles
the origin, otherwise the nearer endpoint's magnitude. -/
def _root_.ZetaLean.Interval.distToZero (x : Interval) : ℚ :=
  max 0 (max x.lo (-x.hi))

theorem _root_.ZetaLean.Interval.distToZero_le_abs {x : Interval} {t : ℝ}
    (hx : x.contains t) : ((x.distToZero : ℚ) : ℝ) ≤ |t| := by
  obtain ⟨h1, h2⟩ := hx
  have ha : t ≤ |t| := le_abs_self t
  have hb : -t ≤ |t| := neg_le_abs t
  rw [Interval.distToZero]
  push_cast
  refine max_le (abs_nonneg t) (max_le ?_ ?_) <;> linarith

/-- The rational lower bound on `‖v‖` a rectangle certifies: the larger of
the two componentwise distances from zero. -/
def normLower (B : ComplexInterval) : ℚ :=
  max B.re.distToZero B.im.distToZero

/-- Reading the bound off the box: if `B` contains `v`, then
`normLower B ≤ ‖v‖`.  Together with `contains_dirichletTermBox` and the
tail bound this is how a boundary segment certifies `ε ≤ ‖DH z‖`. -/
theorem normLower_le_norm {B : ComplexInterval} {v : ℂ} (hB : B.contains v) :
    ((normLower B : ℚ) : ℝ) ≤ ‖v‖ := by
  have hre : ((B.re.distToZero : ℚ) : ℝ) ≤ ‖v‖ :=
    (Interval.distToZero_le_abs hB.1).trans (Complex.abs_re_le_norm v)
  have him : ((B.im.distToZero : ℚ) : ℝ) ≤ ‖v‖ :=
    (Interval.distToZero_le_abs hB.2).trans (Complex.abs_im_le_norm v)
  rw [normLower]
  push_cast
  exact max_le hre him

/-! ### Smoke tests: kernel-checked digits of `cos 1`, `sin 1`, `cos 2`

`exp(it)` has real part `cos t` and imaginary part `sin t`, so the complex
pipeline certifies trigonometric digits with no trigonometric code.  `cos 2`
routes through one halving-and-squaring step, exercising `expC`'s recursion
end-to-end. -/

private lemma exact01_contains_I : (exact 0 1).contains Complex.I := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    norm_num [exact, Interval.exact, Interval.contains, Complex.I_re, Complex.I_im]

theorem cos_one_gt : (0.5402 : ℝ) < Real.cos 1 := by
  obtain ⟨⟨h1, -⟩, -⟩ := contains_expSmall (n := 8) (by norm_num)
    exact01_contains_I (by norm_num [normBound, exact, Interval.exact])
  rw [show (Complex.exp Complex.I).re = Real.cos 1 by
    rw [Complex.exp_re]; norm_num [Complex.I_re, Complex.I_im]] at h1
  refine lt_of_lt_of_le ?_ h1
  norm_num [expSmall, expSumC, smulQ, powI, inflate, normBound, mul, add, exact,
    Interval.exact, Interval.mul, Interval.add, Interval.neg, Interval.sub,
    Nat.factorial]

theorem cos_one_lt : Real.cos 1 < (0.5404 : ℝ) := by
  obtain ⟨⟨-, h2⟩, -⟩ := contains_expSmall (n := 8) (by norm_num)
    exact01_contains_I (by norm_num [normBound, exact, Interval.exact])
  rw [show (Complex.exp Complex.I).re = Real.cos 1 by
    rw [Complex.exp_re]; norm_num [Complex.I_re, Complex.I_im]] at h2
  refine lt_of_le_of_lt h2 ?_
  norm_num [expSmall, expSumC, smulQ, powI, inflate, normBound, mul, add, exact,
    Interval.exact, Interval.mul, Interval.add, Interval.neg, Interval.sub,
    Nat.factorial]

theorem sin_one_gt : (0.8414 : ℝ) < Real.sin 1 := by
  obtain ⟨-, h1, -⟩ := contains_expSmall (n := 8) (by norm_num)
    exact01_contains_I (by norm_num [normBound, exact, Interval.exact])
  rw [show (Complex.exp Complex.I).im = Real.sin 1 by
    rw [Complex.exp_im]; norm_num [Complex.I_re, Complex.I_im]] at h1
  refine lt_of_lt_of_le ?_ h1
  norm_num [expSmall, expSumC, smulQ, powI, inflate, normBound, mul, add, exact,
    Interval.exact, Interval.mul, Interval.add, Interval.neg, Interval.sub,
    Nat.factorial]

theorem sin_one_lt : Real.sin 1 < (0.8415 : ℝ) := by
  obtain ⟨-, -, h2⟩ := contains_expSmall (n := 8) (by norm_num)
    exact01_contains_I (by norm_num [normBound, exact, Interval.exact])
  rw [show (Complex.exp Complex.I).im = Real.sin 1 by
    rw [Complex.exp_im]; norm_num [Complex.I_re, Complex.I_im]] at h2
  refine lt_of_le_of_lt h2 ?_
  norm_num [expSmall, expSumC, smulQ, powI, inflate, normBound, mul, add, exact,
    Interval.exact, Interval.mul, Interval.add, Interval.neg, Interval.sub,
    Nat.factorial]

private lemma exact02_contains_2I : (exact 0 2).contains ((2 : ℂ) * Complex.I) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    norm_num [exact, Interval.exact, Interval.contains, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]

theorem cos_two_gt : (-0.4163 : ℝ) < Real.cos 2 := by
  obtain ⟨⟨h1, -⟩, -⟩ := contains_expC 8 (by norm_num) 1 (exact 0 2)
    ((2 : ℂ) * Complex.I) exact02_contains_2I
    (by norm_num [normBound, exact, Interval.exact])
  rw [show (Complex.exp ((2 : ℂ) * Complex.I)).re = Real.cos 2 by
    rw [Complex.exp_re]
    norm_num [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]] at h1
  refine lt_of_lt_of_le ?_ h1
  norm_num [expC, expSmall, expSumC, smulQ, powI, inflate, normBound, halveC, mul,
    add, exact, Interval.exact, Interval.mul, Interval.add, Interval.neg,
    Interval.sub, Interval.halve, Nat.factorial]

theorem cos_two_lt : Real.cos 2 < (-0.4159 : ℝ) := by
  obtain ⟨⟨-, h2⟩, -⟩ := contains_expC 8 (by norm_num) 1 (exact 0 2)
    ((2 : ℂ) * Complex.I) exact02_contains_2I
    (by norm_num [normBound, exact, Interval.exact])
  rw [show (Complex.exp ((2 : ℂ) * Complex.I)).re = Real.cos 2 by
    rw [Complex.exp_re]
    norm_num [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]] at h2
  refine lt_of_le_of_lt h2 ?_
  norm_num [expC, expSmall, expSumC, smulQ, powI, inflate, normBound, halveC, mul,
    add, exact, Interval.exact, Interval.mul, Interval.add, Interval.neg,
    Interval.sub, Interval.halve, Nat.factorial]

/-- `1^{-s} = 1` runs the whole `dirichletTerm` pipeline and lands on the
exact value, so the enclosure must contain `1`. -/
example : (dirichletTerm 8 0 1 1 (1 / 2) 1).contains 1 := by
  have h := contains_dirichletTerm (n := 8) (kL := 0) (kE := 1)
    (by norm_num) (by norm_num : 0 < 1) (sre := 1 / 2) (sim := 1)
    (by norm_num) (by norm_num)
    (by norm_num [normBound, mul, exact, Interval.logQ, Interval.log2I,
      Interval.log1, Interval.exact, Interval.mul, Interval.add, Interval.neg,
      Interval.sub, Interval.logSum, Interval.logRem, Finset.sum_range_succ])
  rwa [show ((1 : ℕ) : ℂ) ^ (-(⟨((1 / 2 : ℚ) : ℝ), ((1 : ℚ) : ℝ)⟩ : ℂ)) = 1 by
    rw [Nat.cast_one, Complex.one_cpow]] at h

end ComplexInterval

end ZetaLean

end

section







/-!
# Support for the two term-box tables (hunt `hardy_first_zero`)

Generic pieces between `EulerMaclaurin.lean` (the remainder) and the generated
`Boxes.lean` (the term boxes at the two endpoints):

* `lit`, `sumBoxes`, `contains_sumBoxes`: literal rectangles and their running sum;
* `ptBox`, `ptBox_contains`: the exact rectangle of `1/2 + it`;
* `main_eq`: the order-4 main term as `Σ_{i<N} i^{-s} + N^{-s} · c_N(s)` with
  `c_N(s) = N/(s-1) + 1/2 + s/(12N)`, so that it needs `N` term boxes and one
  exact product;
* `em30_bound`: the remainder at `N = 30` on the critical line, bounded by an
  explicit rational function of the height.
-/

open Complex Finset ZetaLean ZetaLean.ComplexInterval
open scoped ComplexConjugate

namespace HardyFirstZero

/-- A literal rectangle. -/
def lit (a b c d : ℚ) (h1 : a ≤ b) (h2 : c ≤ d) : ComplexInterval := ⟨⟨a, b, h1⟩, ⟨c, d, h2⟩⟩

/-- The running sum `B 0 + ⋯ + B (n-1)` of rectangles. -/
def sumBoxes (B : ℕ → ComplexInterval) : ℕ → ComplexInterval
  | 0 => ComplexInterval.exact 0 0
  | n + 1 => (sumBoxes B n).add (B n)

theorem contains_sumBoxes {B : ℕ → ComplexInterval} {f : ℕ → ℂ} :
    ∀ {N : ℕ}, (∀ m < N, (B m).contains (f m)) →
      (sumBoxes B N).contains (∑ m ∈ range N, f m)
  | 0, _ => by simpa [sumBoxes] using contains_zero
  | n + 1, h => by
    rw [Finset.sum_range_succ]
    exact contains_add (contains_sumBoxes fun m hm => h m (by omega)) (h n (by omega))

/-- The exact rectangle of `1/2 + it`. -/
def ptBox (t : ℚ) : ComplexInterval := ComplexInterval.exact (1 / 2) t

theorem ptBox_contains (t : ℚ) : (ptBox t).contains (sOf (t : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp [ptBox, ComplexInterval.exact, Interval.exact, sOf]

/-- The order-4 main term, regrouped around the single power `N^{-s}`. -/
theorem main_eq (s : ℂ) {N : ℕ} (hN : N ≠ 0) :
    ∑ i ∈ range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
        + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1)
      = ∑ i ∈ range N, (i : ℂ) ^ (-s)
        + (N : ℂ) ^ (-s) * ((N : ℂ) / (s - 1) + 1 / 2 + s / (12 * N)) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have h1 : (N : ℂ) ^ (1 - s) = N * (N : ℂ) ^ (-s) := by
    rw [show (1 - s) = 1 + (-s) by ring, cpow_add _ _ hN', cpow_one]
  have h2 : (N : ℂ) ^ (-s - 1) = (N : ℂ) ^ (-s) * (N : ℂ)⁻¹ := by
    rw [show (-s - 1) = -s + (-1) by ring, cpow_add _ _ hN', cpow_neg_one]
  rw [h1, h2]
  ring

/-- `‖z + j‖ ≤ (1/2 + j) + t` on the critical line. -/
private lemma norm_add_le_of_sOf {t : ℝ} (ht : 0 ≤ t) (j : ℝ) (hj : 0 ≤ j) :
    ‖sOf t + j‖ ≤ 1 / 2 + j + t := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
  have hre : (sOf t + j).re = 1 / 2 + j := by simp [sOf]
  have him : (sOf t + j).im = t := by simp [sOf]
  rw [hre, him, abs_of_nonneg (by linarith), abs_of_nonneg ht]

/-- **The remainder at `N = 30` on the critical line**, for `0 < t ≤ T`:
`‖ζ(1/2+it) - M_30‖ ≤ (1/2+T)(3/2+T)(5/2+T)(7/2+T) / (24389 · 5 · (7/2) · 720)`,
from `zeta_em4_error`, `‖z‖ ≤ |Re z| + |Im z|` and `29^{-7/2} ≤ 1/(29³ · 5)`. -/
theorem em30_bound {t T : ℝ} (ht : 0 < t) (hT : t ≤ T) :
    ‖riemannZeta (sOf t) - (∑ i ∈ range 30, (i : ℂ) ^ (-sOf t) + ((30 : ℕ) : ℂ) ^ (1 - sOf t)
        / (sOf t - 1) + ((30 : ℕ) : ℂ) ^ (-sOf t) / 2
        + sOf t / 12 * ((30 : ℕ) : ℂ) ^ (-sOf t - 1))‖
      ≤ (1 / 2 + T) * (3 / 2 + T) * (5 / 2 + T) * (7 / 2 + T) / (24389 * 5 * (7 / 2) * 720) := by
  have hQP : sOf t ∈ QP := ⟨by simp [sOf], by simp [sOf, ht]⟩
  have h := zeta_em4_error hQP (N := 30) (by norm_num)
  refine h.trans ?_
  have hre : (sOf t).re = 1 / 2 := sOf_re t
  rw [hre]
  -- the four norms
  have e0 : ‖sOf t‖ ≤ 1 / 2 + T := by
    have := norm_add_le_of_sOf ht.le 0 le_rfl; simp at this; linarith
  have e1 : ‖sOf t + 1‖ ≤ 3 / 2 + T := by
    have := norm_add_le_of_sOf ht.le 1 zero_le_one; push_cast at this; linarith
  have e2 : ‖sOf t + 2‖ ≤ 5 / 2 + T := by
    have := norm_add_le_of_sOf ht.le 2 zero_le_two; push_cast at this; linarith
  have e3 : ‖sOf t + 3‖ ≤ 7 / 2 + T := by
    have := norm_add_le_of_sOf ht.le 3 (by norm_num); push_cast at this; linarith
  have hT0 : 0 ≤ T := by linarith
  have hP : ‖P4 (sOf t)‖ ≤ (1 / 2 + T) * (3 / 2 + T) * (5 / 2 + T) * (7 / 2 + T) := by
    unfold P4
    rw [norm_mul, norm_mul, norm_mul]
    have a1 := mul_le_mul e0 e1 (norm_nonneg _) (by linarith)
    have a2 := mul_le_mul a1 e2 (norm_nonneg _) (mul_nonneg (by linarith) (by linarith))
    exact mul_le_mul a2 e3 (norm_nonneg _)
      (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
  -- the power of 29
  have h29 : ((30 : ℕ) : ℝ) - 1 = 29 := by norm_num
  rw [h29]
  have hpow : (29 : ℝ) ^ (-(1 / 2 : ℝ) - 3) ≤ 1 / (24389 * 5) := by
    rw [show (-(1 / 2 : ℝ) - 3) = -(1 / 2) + (-3 : ℝ) by ring,
      Real.rpow_add (by norm_num), Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num),
      ← Real.sqrt_eq_rpow, show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hs : (5 : ℝ) ≤ Real.sqrt 29 := Real.le_sqrt_of_sq_le (by norm_num)
    have hs0 : 0 < Real.sqrt 29 := by positivity
    rw [show (1 : ℝ) / (24389 * 5) = (5 : ℝ)⁻¹ * ((29 : ℝ) ^ 3)⁻¹ by norm_num]
    gcongr
  have hnn : 0 ≤ (29 : ℝ) ^ (-(1 / 2 : ℝ) - 3) := Real.rpow_nonneg (by norm_num) _
  have hQ0 : 0 ≤ (1 / 2 + T) * (3 / 2 + T) * (5 / 2 + T) * (7 / 2 + T) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) (by linarith)
  calc ‖P4 (sOf t)‖ * ((29 : ℝ) ^ (-(1 / 2 : ℝ) - 3) / (1 / 2 + 3)) / 720
      ≤ ((1 / 2 + T) * (3 / 2 + T) * (5 / 2 + T) * (7 / 2 + T))
          * ((1 / (24389 * 5)) / (1 / 2 + 3)) / 720 :=
        div_le_div_of_nonneg_right (mul_le_mul hP
          (div_le_div_of_nonneg_right hpow (by norm_num)) (by positivity) hQ0) (by norm_num)
    _ = _ := by ring

end HardyFirstZero

end

section






/-!
# The term-box tables at `t = 1413/100` and `t = 707/50` (generated)

Generated by `hunts/hardy_first_zero/gen_boxes.py` from the lab's bit-exact rational
mirror of the interval layer; do not edit by hand. Every literal is checked by the
kernel against `dirichletTermBox2` itself (`decide +kernel`), so the mirror is not
trusted. Parameters: `nLog = 40`, `nExp = 24`, `p = 96`, `kE = 8`, `kL` the bit
length of `m`.
-/

open Complex ZetaLean ZetaLean.ComplexInterval

namespace HardyFirstZero



/- Term boxes `m^(-s)` at `s = 1/2 + i · 1413/100`, `1 ≤ m ≤ 30`. -/
set_option maxRecDepth 100000 in
def tA : ℕ → ComplexInterval
  | 1 => lit (79228162514192279999479885307 / 79228162514264337593543950336 : ℚ) (79228162514336395187608080645 / 79228162514264337593543950336 : ℚ)
      (-127271725469605983 / 4951760157141521099596496896 : ℚ) (127271725469605983 / 4951760157141521099596496896 : ℚ) (by norm_num) (by norm_num)
  | 2 => lit (-3265242190802629529759108251 / 4951760157141521099596496896 : ℚ) (-52243875041974136066060479175 / 79228162514264337593543950336 : ℚ)
      (20226922343841466287171781983 / 79228162514264337593543950336 : ℚ) (10113461177369513466105374921 / 39614081257132168796771975168 : ℚ) (by norm_num) (by norm_num)
  | 3 => lit (-2810341521717817063327738697 / 4951760157141521099596496896 : ℚ) (-44965464340557772098093879997 / 79228162514264337593543950336 : ℚ)
      (-8394894967397569280129677265 / 79228162514264337593543950336 : ℚ) (-2098723740118738348761116551 / 19807040628566084398385987584 : ℚ) (by norm_num) (by norm_num)
  | 4 => lit (29286228761137521261720263453 / 79228162514264337593543950336 : ℚ) (14643114387228614781478272717 / 39614081257132168796771975168 : ℚ)
      (-3334460785594491179487753267 / 9903520314283042199192993792 : ℚ) (-13337843135710095928822016273 / 39614081257132168796771975168 : ℚ) (by norm_num) (by norm_num)
  | 5 => lit (-6480020957272638570240429575 / 19807040628566084398385987584 : ℚ) (-6480020954998386017633865585 / 19807040628566084398385987584 : ℚ)
      (1509824080949385872639306687 / 4951760157141521099596496896 : ℚ) (24157185304296327605610911977 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 6 => lit (31793908997839001620103519953 / 79228162514264337593543950336 : ℚ) (7948477250464484688790543947 / 19807040628566084398385987584 : ℚ)
      (-2971993148452365699435427995 / 39614081257132168796771975168 : ℚ) (-371499143305010589856994501 / 4951760157141521099596496896 : ℚ) (by norm_num) (by norm_num)
  | 7 => lit (-21317581505885999169984919827 / 79228162514264337593543950336 : ℚ) (-333087210897608084135300649 / 1237940039285380274899124224 : ℚ)
      (-5257670220961567324690999233 / 19807040628566084398385987584 : ℚ) (-657208777356658089723942751 / 2475880078570760549798248448 : ℚ) (by norm_num) (by norm_num)
  | 8 => lit (-12501350663933768525959970973 / 79228162514264337593543950336 : ℚ) (-12501350647367668182453120639 / 79228162514264337593543950336 : ℚ)
      (25066989214751116014483957939 / 79228162514264337593543950336 : ℚ) (6266747307830664909171501735 / 19807040628566084398385987584 : ℚ) (by norm_num) (by norm_num)
  | 9 => lit (12315183515039557416621989055 / 39614081257132168796771975168 : ℚ) (24630367039491270932123861487 / 79228162514264337593543950336 : ℚ)
      (9528943698987775562627519059 / 79228162514264337593543950336 : ℚ) (4764471854197783622467201843 / 39614081257132168796771975168 : ℚ) (by norm_num) (by norm_num)
  | 10 => lit (10924652059946820146233864017 / 79228162514264337593543950336 : ℚ) (10924652072445832441435057193 / 79228162514264337593543950336 : ℚ)
      (-11273443917600810623206292611 / 39614081257132168796771975168 : ℚ) (-5636721955674829751448827293 / 19807040628566084398385987584 : ℚ) (by norm_num) (by norm_num)
  | 11 => lit (-9322904587353814025539704965 / 39614081257132168796771975168 : ℚ) (-18645809162329602899033380971 / 79228162514264337593543950336 : ℚ)
      (-14932495201536062751724150377 / 79228162514264337593543950336 : ℚ) (-14932495189161650508252836507 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 12 => lit (-19447736907777523150173768459 / 79228162514264337593543950336 : ℚ) (-9723868448343488631356348513 / 39614081257132168796771975168 : ℚ)
      (6018250171982964569207058761 / 39614081257132168796771975168 : ℚ) (12036500355059750506597104363 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 13 => lit (2508751648508056559818294835 / 79228162514264337593543950336 : ℚ) (1254375829488090205946553427 / 39614081257132168796771975168 : ℚ)
      (10915128773364434099717926463 / 39614081257132168796771975168 : ℚ) (21830257557196204194094237117 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 14 => lit (303533760181170284091189521 / 1237940039285380274899124224 : ℚ) (9713080329056459277575744473 / 39614081257132168796771975168 : ℚ)
      (4212739364933333364627369355 / 39614081257132168796771975168 : ℚ) (8425478736381005853857128251 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 15 => lit (17270445186724315440204817955 / 79228162514264337593543950336 : ℚ) (2158805649206432200755960931 / 9903520314283042199192993792 : ℚ)
      (-10963811929913875974417200499 / 79228162514264337593543950336 : ℚ) (-2740952980745706466260405277 / 19807040628566084398385987584 : ℚ) (by norm_num) (by norm_num)
  | 16 => lit (460981776653402268759530055 / 19807040628566084398385987584 : ℚ) (1843927120890014507609315521 / 79228162514264337593543950336 : ℚ)
      (-19721024099737660944201543731 / 79228162514264337593543950336 : ℚ) (-9860512042730227019971535763 / 39614081257132168796771975168 : ℚ) (by norm_num) (by norm_num)
  | 17 => lit (-6642651859712205702896121405 / 39614081257132168796771975168 : ℚ) (-13285303707094064112453783269 / 79228162514264337593543950336 : ℚ)
      (-54231072982957590408883785 / 309485009821345068724781056 : ℚ) (-6941577335655042407421185873 / 39614081257132168796771975168 : ℚ) (by norm_num) (by norm_num)
  | 18 => lit (-18674256420050032289326115507 / 79228162514264337593543950336 : ℚ) (-18674256410499862777271236395 / 79228162514264337593543950336 : ℚ)
      (2319736238216033248945605 / 39614081257132168796771975168 : ℚ) (2319741013301743663507873 / 39614081257132168796771975168 : ℚ) (by norm_num) (by norm_num)
  | 19 => lit (-13121816715496002643082806605 / 79228162514264337593543950336 : ℚ) (-13121816703390005058668785595 / 79228162514264337593543950336 : ℚ)
      (12577428260108975104425183219 / 79228162514264337593543950336 : ℚ) (6288714136108893541659383513 / 39614081257132168796771975168 : ℚ) (by norm_num) (by norm_num)
  | 20 => lit (-1447616668037912346476196885 / 79228162514264337593543950336 : ℚ) (-90476040986804564216737939 / 4951760157141521099596496896 : ℚ)
      (2207089049210356163794241097 / 9903520314283042199192993792 : ℚ) (17656712405932312486718751443 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 21 => lit (9870285624193137767395758969 / 79228162514264337593543950336 : ℚ) (9870285634634353209000411841 / 79228162514264337593543950336 : ℚ)
      (3548653511303924721552786975 / 19807040628566084398385987584 : ℚ) (14194614055654229392317933695 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 22 => lit (16107501478739551929958114721 / 79228162514264337593543950336 : ℚ) (16107501486288473893584337673 / 79228162514264337593543950336 : ℚ)
      (5086374161069364823645784621 / 79228162514264337593543950336 : ℚ) (5086374168616145798856530437 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 23 => lit (15669912468359363001750571505 / 79228162514264337593543950336 : ℚ) (15669912475649190390106859315 / 79228162514264337593543950336 : ℚ)
      (-1307939933489089836100573967 / 19807040628566084398385987584 : ℚ) (-5231759726664343546124252063 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 24 => lit (9751125784989309219083929427 / 79228162514264337593543950336 : ℚ) (9751125794029572229485176201 / 79228162514264337593543950336 : ℚ)
      (-12901994093742868224954652983 / 79228162514264337593543950336 : ℚ) (-12901994084699931033190401339 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 25 => lit (278566171037384316234909885 / 19807040628566084398385987584 : ℚ) (34820771683436132663244451 / 2475880078570760549798248448 : ℚ)
      (-7903203207750177628913217811 / 39614081257132168796771975168 : ℚ) (-15806406405779592180519663477 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 26 => lit (-7227554123299420357640871811 / 79228162514264337593543950336 : ℚ) (-1806888528491260054164433191 / 19807040628566084398385987584 : ℚ)
      (-13754615640329481701036763897 / 79228162514264337593543950336 : ℚ) (-3438653907749275415353056349 / 19807040628566084398385987584 : ℚ) (by norm_num) (by norm_num)
  | 27 => lit (-1621142938454124551316786593 / 9903520314283042199192993792 : ℚ) (-12969143499546487233193728831 / 79228162514264337593543950336 : ℚ)
      (-8017890390053030419124342669 / 79228162514264337593543950336 : ℚ) (-1002236297746113818463152431 / 9903520314283042199192993792 : ℚ) (by norm_num) (by norm_num)
  | 28 => lit (-14960834337526044813516483213 / 79228162514264337593543950336 : ℚ) (-14960834331241806210629187449 / 79228162514264337593543950336 : ℚ)
      (-149089079523256750184705957 / 19807040628566084398385987584 : ℚ) (-298178155904524742948074475 / 39614081257132168796771975168 : ℚ) (by norm_num) (by norm_num)
  | 29 => lit (-6604506116562973888698852869 / 39614081257132168796771975168 : ℚ) (-3302253056575471610305984323 / 19807040628566084398385987584 : ℚ)
      (6478717454088944482358833461 / 79228162514264337593543950336 : ℚ) (1619679365228822316810575425 / 19807040628566084398385987584 : ℚ) (by norm_num) (by norm_num)
  | 30 => lit (-4294626978079917572585867539 / 39614081257132168796771975168 : ℚ) (-8589253949239917517701433811 / 79228162514264337593543950336 : ℚ)
      (2909697589187446226696481233 / 19807040628566084398385987584 : ℚ) (11638790363672308667189496331 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | _ => ComplexInterval.exact 0 0

def klog (m : ℕ) : ℕ := if m < 2 then 1 else if m < 4 then 2 else if m < 8 then 3 else if m < 16 then 4 else 5

theorem tmem {m : ℕ} {q : ℚ} {T : ComplexInterval} (hm : 0 < m)
    (h : dirichletTermBox2 40 24 96 (klog m) 8 m (ptBox q) = T)
    (h0 : 0 < (m : ℚ) / 2 ^ klog m) (h2 : (m : ℚ) / 2 ^ klog m < 2)
    (hb : normBound ((ptBox q).neg.mul
      { re := Interval.logQ 40 (klog m) (m : ℚ), im := Interval.exact 0 }) ≤ 2 ^ 8) :
    T.contains ((m : ℂ) ^ (-sOf (q : ℝ))) := by
  rw [← h]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) hm (ptBox_contains _) h0 h2 hb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tA_mem : ∀ m < 31,
    (tA m).contains ((m : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  intro m hm
  interval_cases m
  · rw [Nat.cast_zero, zero_cpow (neg_ne_zero.mpr (sOf_ne_zero _))]
    exact contains_zero
  all_goals refine tmem ?_ ?_ ?_ ?_ ?_
  all_goals first | decide +kernel | norm_num [klog]

/- `c_30(s)` at `s = 1/2 + i · 1413/100`, exactly. -/
set_option maxRecDepth 100000 in
def cA : ComplexInterval := ComplexInterval.exact (613663909 / 1439329680 : ℚ) (-16642146167 / 7996276000 : ℚ)

/- The remainder bound at `t = 1413/100`, rounded up. -/
set_option maxRecDepth 100000 in
def epsA : ℚ := (1091 / 5000000 : ℚ)

/- Term boxes `m^(-s)` at `s = 1/2 + i · 707/50`, `1 ≤ m ≤ 30`. -/
set_option maxRecDepth 100000 in
def tB : ℕ → ComplexInterval
  | 1 => lit (19807040628548069999869962033 / 19807040628566084398385987584 : ℚ) (19807040628584098796902029455 / 19807040628566084398385987584 : ℚ)
      (-509447189848613879 / 19807040628566084398385987584 : ℚ) (509447189848613879 / 19807040628566084398385987584 : ℚ) (by norm_num) (by norm_num)
  | 2 => lit (-52102418802217544929411817195 / 79228162514264337593543950336 : ℚ) (-52102418791318782370261627953 / 79228162514264337593543950336 : ℚ)
      (20588560488644666406399026943 / 79228162514264337593543950336 : ℚ) (20588560499573437056816994415 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 3 => lit (-45054976316221652535070984349 / 79228162514264337593543950336 : ℚ) (-11263744077328714113993511753 / 19807040628566084398385987584 : ℚ)
      (-3950201091065087846429853093 / 39614081257132168796771975168 : ℚ) (-7900402175227813652542631255 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 4 => lit (28913622984895495417012846499 / 79228162514264337593543950336 : ℚ) (28913622998293848857028606879 / 79228162514264337593543950336 : ℚ)
      (-3384887922142683280078172095 / 9903520314283042199192993792 : ℚ) (-13539551681863565463661458901 / 39614081257132168796771975168 : ℚ) (by norm_num) (by norm_num)
  | 5 => lit (-12763974380104333091560810239 / 39614081257132168796771975168 : ℚ) (-6381987187773543870169723837 / 19807040628566084398385987584 : ℚ)
      (24571206302948865428536800967 / 79228162514264337593543950336 : ℚ) (24571206312072504565518433227 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 6 => lit (31682309334085611673573318869 / 79228162514264337593543950336 : ℚ) (31682309338167890308350463209 / 79228162514264337593543950336 : ℚ)
      (-3256336043819667195975183165 / 39614081257132168796771975168 : ℚ) (-6512672083551005607389813323 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 7 => lit (-21722757938796638947908139315 / 79228162514264337593543950336 : ℚ) (-21722757930357543254267192679 / 79228162514264337593543950336 : ℚ)
      (-20611904502752908545577289797 / 79228162514264337593543950336 : ℚ) (-5152976123579920220465894481 / 19807040628566084398385987584 : ℚ) (by norm_num) (by norm_num)
  | 8 => lit (-5988716049416538909879488001 / 39614081257132168796771975168 : ℚ) (-2924177754446455226733853 / 19342813113834066795298816 : ℚ)
      (25321509374824247487262381591 / 79228162514264337593543950336 : ℚ) (25321509391449899420848355207 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 9 => lit (12416888598394929724876455061 / 39614081257132168796771975168 : ℚ) (12416888603051538850186663183 / 39614081257132168796771975168 : ℚ)
      (4492751334138960756849434427 / 39614081257132168796771975168 : ℚ) (2246375669396735794218237111 / 19807040628566084398385987584 : ℚ) (by norm_num) (by norm_num)
  | 10 => lit (10402640714621139047655451441 / 79228162514264337593543950336 : ℚ) (10402640727204111561923502501 / 79228162514264337593543950336 : ℚ)
      (-22792438216592829794968686439 / 79228162514264337593543950336 : ℚ) (-11396219102003354625558699801 / 39614081257132168796771975168 : ℚ) (by norm_num) (by norm_num)
  | 11 => lit (-18998480136355880535815718399 / 79228162514264337593543950336 : ℚ) (-9499240062017313842229928017 / 39614081257132168796771975168 : ℚ)
      (-14481138257363592472740285749 / 79228162514264337593543950336 : ℚ) (-14481138245045928646571634397 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 12 => lit (-9571333971274056651496445741 / 39614081257132168796771975168 : ℚ) (-19142667931397086712552232971 / 79228162514264337593543950336 : ℚ)
      (12515992785131429803592227529 / 79228162514264337593543950336 : ℚ) (12515992796285793165851276487 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 13 => lit (1533900050281223339636314663 / 39614081257132168796771975168 : ℚ) (3067800110978245456195779985 / 79228162514264337593543950336 : ℚ)
      (21758735761288913011656695103 / 79228162514264337593543950336 : ℚ) (10879367885851872993230130895 / 39614081257132168796771975168 : ℚ) (by norm_num) (by norm_num)
  | 14 => lit (9820861827136840558059829643 / 39614081257132168796771975168 : ℚ) (9820861830342796529043916381 / 39614081257132168796771975168 : ℚ)
      (7909936876045922188969444617 / 79228162514264337593543950336 : ℚ) (7909936882454279382381029425 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 15 => lit (8483621829692995201277964159 / 39614081257132168796771975168 : ℚ) (8483621833212180685937140323 / 39614081257132168796771975168 : ℚ)
      (-5713713582029962601006094325 / 39614081257132168796771975168 : ℚ) (-5713713578508806450375522777 / 39614081257132168796771975168 : ℚ) (by norm_num) (by norm_num)
  | 16 => lit (648252788682980629325666073 / 39614081257132168796771975168 : ℚ) (648252795867362252736296913 / 39614081257132168796771975168 : ℚ)
      (-19764562530320137554833580861 / 79228162514264337593543950336 : ℚ) (-19764562515950812746370049819 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 17 => lit (-13673258724548789256947949009 / 79228162514264337593543950336 : ℚ) (-6836629356122336767097860843 / 39614081257132168796771975168 : ℚ)
      (-6750616170729548768231733105 / 39614081257132168796771975168 : ℚ) (-13501232329158283138096275001 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 18 => lit (-18666322414396136147158896733 / 79228162514264337593543950336 : ℚ) (-18666322404692843922810124981 / 79228162514264337593543950336 : ℚ)
      (272158908471728063839736421 / 39614081257132168796771975168 : ℚ) (544317826646968826909719155 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 19 => lit (-1593230976365015409721345515 / 9903520314283042199192993792 : ℚ) (-12745847798742496691553992307 / 79228162514264337593543950336 : ℚ)
      (6479142287466424986139725927 / 39614081257132168796771975168 : ℚ) (6479142293556639294200055881 / 39614081257132168796771975168 : ℚ) (by norm_num) (by norm_num)
  | 20 => lit (-918098422434097187552906877 / 79228162514264337593543950336 : ℚ) (-918098410206275360187514415 / 79228162514264337593543950336 : ℚ)
      (17692150289068233650254562001 / 79228162514264337593543950336 : ℚ) (17692150301296325500845800765 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 21 => lit (10297802986743819629813747129 / 79228162514264337593543950336 : ℚ) (10297802997088473325891984835 / 79228162514264337593543950336 : ℚ)
      (13887579337057855464873473665 / 79228162514264337593543950336 : ℚ) (6943789673699870444561206687 / 39614081257132168796771975168 : ℚ) (by norm_num) (by norm_num)
  | 22 => lit (16257004049898416571997203825 / 79228162514264337593543950336 : ℚ) (8128502028654862829492606717 / 39614081257132168796771975168 : ℚ)
      (2293067013907989318897706029 / 39614081257132168796771975168 : ℚ) (4586134035225301759076074693 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 23 => lit (7749097827035240068581143253 / 39614081257132168796771975168 : ℚ) (15498195661485835396075869609 / 79228162514264337593543950336 : ℚ)
      (-5720436884682049260137957953 / 79228162514264337593543950336 : ℚ) (-2860218438632182881705038353 / 39614081257132168796771975168 : ℚ) (by norm_num) (by norm_num)
  | 24 => lit (1167029821197964808984575009 / 9903520314283042199192993792 : ℚ) (9336238578705569731967353105 / 79228162514264337593543950336 : ℚ)
      (-13205322981596661566291477101 / 79228162514264337593543950336 : ℚ) (-13205322972472211215672897773 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 25 => lit (302493370775299921552278135 / 39614081257132168796771975168 : ℚ) (604986751294126187280806715 / 79228162514264337593543950336 : ℚ)
      (-15834079089307039768670138943 / 79228162514264337593543950336 : ℚ) (-15834079079563326575189763961 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 26 => lit (-3835888871954840377443492203 / 39614081257132168796771975168 : ℚ) (-7671777734611668975038908757 / 79228162514264337593543950336 : ℚ)
      (-13511876859547694243148558887 / 79228162514264337593543950336 : ℚ) (-211123075785184027314799233 / 1237940039285380274899124224 : ℚ) (by norm_num) (by norm_num)
  | 27 => lit (-13226309000949170124124903827 / 79228162514264337593543950336 : ℚ) (-13226308992948677144182405039 / 79228162514264337593543950336 : ℚ)
      (-7586171619248705895802188555 / 79228162514264337593543950336 : ℚ) (-7586171611250544906760376943 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 28 => lit (-14972397294536110035786693863 / 79228162514264337593543950336 : ℚ) (-14972397288371110704899637901 / 79228162514264337593543950336 : ℚ)
      (-97591919425428102254212389 / 79228162514264337593543950336 : ℚ) (-97591913260472389261558607 / 79228162514264337593543950336 : ℚ) (by norm_num) (by norm_num)
  | 29 => lit (-6491703971822442552708985645 / 39614081257132168796771975168 : ℚ) (-6491703968390205539153607123 / 39614081257132168796771975168 : ℚ)
      (1729936815850884553976292307 / 19807040628566084398385987584 : ℚ) (216242102195949910003092943 / 2475880078570760549798248448 : ℚ) (by norm_num) (by norm_num)
  | 30 => lit (-8188504433911391641142113715 / 79228162514264337593543950336 : ℚ) (-1023563053374373511520145439 / 9903520314283042199192993792 : ℚ)
      (5962070102381763385956261599 / 39614081257132168796771975168 : ℚ) (5962070105841239484579370171 / 39614081257132168796771975168 : ℚ) (by norm_num) (by norm_num)
  | _ => ComplexInterval.exact 0 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tB_mem : ∀ m < 31,
    (tB m).contains ((m : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  intro m hm
  interval_cases m
  · rw [Nat.cast_zero, zero_cpow (neg_ne_zero.mpr (sOf_ne_zero _))]
    exact contains_zero
  all_goals refine tmem ?_ ?_ ?_ ?_ ?_
  all_goals first | decide +kernel | norm_num [klog]

/- `c_30(s)` at `s = 1/2 + i · 707/50`, exactly. -/
set_option maxRecDepth 100000 in
def cB : ComplexInterval := ComplexInterval.exact (76835557 / 180170640 : ℚ) (-9367582441 / 4504266000 : ℚ)

/- The remainder bound at `t = 707/50`, rounded up. -/
set_option maxRecDepth 100000 in
def epsB : ℚ := (547 / 2500000 : ℚ)

end HardyFirstZero

end

section






/-!
# A zero of zeta on the critical line between 14.13 and 14.14 (hunt `hardy_first_zero`)

The assembly. `Boxes.lean` encloses every term `m^{-s}`, `1 ≤ m ≤ 30`, at the two
endpoints in a kernel-checked rational rectangle; `main_eq` regroups the order-4
main term around `30^{-s}`; `em30_bound` bounds the remainder; the rectangles,
inflated by that bound, contain `ζ(1/2 + 14.13i)` and `ζ(1/2 + 14.14i)`; one interval
product shows `Re(ζ_a · conj ζ_b) < 0`; and `first_zero_on_line_of_zeta_product`
(`Phase.lean`, which also carries the phase lemma) turns that into the zero.
-/

open Complex Finset ZetaLean ZetaLean.ComplexInterval
open scoped ComplexConjugate

namespace HardyFirstZero



/- The rectangle for the order-4 main term at `t = 1413/100`. -/
set_option maxRecDepth 100000 in
def MA : ComplexInterval := (sumBoxes tA 30).add ((tA 30).mul cA)

/- The rectangle for the order-4 main term at `t = 707/50`. -/
set_option maxRecDepth 100000 in
def MB : ComplexInterval := (sumBoxes tB 30).add ((tB 30).mul cB)

set_option maxRecDepth 100000 in
lemma cA_mem : cA.contains (((30 : ℕ) : ℂ) / (sOf ((1413 / 100 : ℚ) : ℝ) - 1) + 1 / 2
    + sOf ((1413 / 100 : ℚ) : ℝ) / (12 * ((30 : ℕ) : ℂ))) := by
  have h := contains_exact (613663909 / 1439329680 : ℚ) (-16642146167 / 7996276000 : ℚ)
  unfold cA
  convert h using 1
  apply Complex.ext <;>
    simp [sOf, Complex.div_re, Complex.div_im, Complex.normSq] <;> norm_num

set_option maxRecDepth 100000 in
lemma cB_mem : cB.contains (((30 : ℕ) : ℂ) / (sOf ((707 / 50 : ℚ) : ℝ) - 1) + 1 / 2
    + sOf ((707 / 50 : ℚ) : ℝ) / (12 * ((30 : ℕ) : ℂ))) := by
  have h := contains_exact (76835557 / 180170640 : ℚ) (-9367582441 / 4504266000 : ℚ)
  unfold cB
  convert h using 1
  apply Complex.ext <;>
    simp [sOf, Complex.div_re, Complex.div_im, Complex.normSq] <;> norm_num

/- `ζ(1/2 + 14.13i)` lies in `MA` inflated by `epsA`. -/
set_option maxRecDepth 100000 in
theorem zetaA_mem : (MA.inflate epsA).contains (riemannZeta (sOf ((1413 / 100 : ℚ) : ℝ))) := by
  set s := sOf ((1413 / 100 : ℚ) : ℝ)
  have hM : MA.contains (∑ i ∈ range 30, (i : ℂ) ^ (-s) + ((30 : ℕ) : ℂ) ^ (1 - s) / (s - 1)
      + ((30 : ℕ) : ℂ) ^ (-s) / 2 + s / 12 * ((30 : ℕ) : ℂ) ^ (-s - 1)) := by
    rw [main_eq s (by norm_num)]
    exact contains_add (contains_sumBoxes fun m hm => tA_mem m (by omega))
      (contains_mul (tA_mem 30 (by norm_num)) cA_mem)
  refine contains_inflate hM ((em30_bound (T := 1413 / 100) (by norm_num) (by norm_num)).trans ?_)
  simp only [epsA]
  norm_num

/- `ζ(1/2 + 14.14i)` lies in `MB` inflated by `epsB`. -/
set_option maxRecDepth 100000 in
theorem zetaB_mem : (MB.inflate epsB).contains (riemannZeta (sOf ((707 / 50 : ℚ) : ℝ))) := by
  set s := sOf ((707 / 50 : ℚ) : ℝ)
  have hM : MB.contains (∑ i ∈ range 30, (i : ℂ) ^ (-s) + ((30 : ℕ) : ℂ) ^ (1 - s) / (s - 1)
      + ((30 : ℕ) : ℂ) ^ (-s) / 2 + s / 12 * ((30 : ℕ) : ℂ) ^ (-s - 1)) := by
    rw [main_eq s (by norm_num)]
    exact contains_add (contains_sumBoxes fun m hm => tB_mem m (by omega))
      (contains_mul (tB_mem 30 (by norm_num)) cB_mem)
  refine contains_inflate hM ((em30_bound (T := 707 / 50) (by norm_num) (by norm_num)).trans ?_)
  simp only [epsB]
  norm_num

/- The interval product decides the sign: its upper end is negative. -/
set_option maxRecDepth 100000 in
theorem product_hi_neg :
    (((MA.inflate epsA).re.mul (MB.inflate epsB).re).add
      ((MA.inflate epsA).im.mul (MB.inflate epsB).im)).hi < 0 := by
  decide +kernel

/- **`hX` at the planned endpoints**: `Re(ζ(1/2 + 14.13i) · conj ζ(1/2 + 14.14i)) < 0`. -/
set_option maxRecDepth 100000 in
theorem zeta_product_re_neg :
    (riemannZeta (sOf (1413 / 100)) * conj (riemannZeta (sOf (707 / 50)))).re < 0 := by
  have ha : ((1413 / 100 : ℚ) : ℝ) = 1413 / 100 := by norm_num
  have hb : ((707 / 50 : ℚ) : ℝ) = 707 / 50 := by norm_num
  have hA := zetaA_mem
  have hB := zetaB_mem
  rw [ha] at hA
  rw [hb] at hB
  set z := riemannZeta (sOf (1413 / 100))
  set w := riemannZeta (sOf (707 / 50))
  have hre : (z * conj w).re = z.re * w.re + z.im * w.im := by
    simp [Complex.mul_re]
  have hc := Interval.contains_add (Interval.contains_mul hA.1 hB.1)
    (Interval.contains_mul hA.2 hB.2)
  rw [hre]
  have hneg : ((((MA.inflate epsA).re.mul (MB.inflate epsB).re).add
      ((MA.inflate epsA).im.mul (MB.inflate epsB).im)).hi : ℝ) < 0 := by
    exact_mod_cast product_hi_neg
  exact lt_of_le_of_lt hc.2 hneg

/- `ζ` has a zero `1/2 + it` with `14.13 < t < 14.14`. No minimality is asserted. -/
set_option maxRecDepth 100000 in
theorem first_zero_on_line :
    ∃ t ∈ Set.Ioo (1413 / 100 : ℝ) (707 / 50), riemannZeta (1 / 2 + t * I) = 0 :=
  first_zero_on_line_of_zeta_product zeta_product_re_neg

end HardyFirstZero



/-!
Landau oscillation proof of `SkewesNumber.littlewood_pi_minus_li_infinite_sign_changes.R2.H2`.
Adapts the holomorphic logarithm and Landau ball/Tonelli engine from the merged
`ChebyshevBias.littlewood_mod_four_sign_changes.R1.H2` proof in this repository, and uses the
MIT-licensed critical-line zeta zero `HardyFirstZero.first_zero_on_line` by Thomas Lince (@teal-sea).
-/

namespace SkewesH2Proof

open Complex Filter MeasureTheory Set Topology ArithmeticFunction
open scoped BigOperators Nat

/-! ### Section 1: Regularized zeta `(s - 1) * ζ(s)` and real-axis nonvanishing -/

noncomputable def zetaReg (s : ℂ) : ℂ :=
  Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1 s

lemma zetaReg_one : zetaReg 1 = 1 := by
  simp [zetaReg]

lemma zetaReg_of_ne_one {s : ℂ} (hs : s ≠ 1) : zetaReg s = (s - 1) * riemannZeta s := by
  simp [zetaReg, hs]

lemma zetaReg_differentiable : Differentiable ℂ zetaReg := by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · have h1 : DifferentiableAt ℂ (fun z : ℂ => (z - 1) * riemannZeta z) s :=
      (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact zetaReg_of_ne_one hz
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z ≠ 1 := hz
      have h1 : DifferentiableAt ℂ (fun w : ℂ => (w - 1) * riemannZeta w) z :=
        (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hz')
      exact h1.congr_of_eventuallyEq (Filter.eventually_of_mem (isOpen_ne.mem_nhds hz')
        fun w hw => zetaReg_of_ne_one hw)
    · change ContinuousAt (Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1) 1
      rw [continuousAt_update_same]
      exact riemannZeta_residue_one

lemma zetaReg_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : zetaReg s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hne
  · simp [zetaReg]
  · rw [zetaReg_of_ne_one hne]
    exact mul_ne_zero (sub_ne_zero.mpr hne) (riemannZeta_ne_zero_of_one_le_re hs)

noncomputable def etaTerm (k : ℕ) (s : ℂ) : ℂ :=
  ((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s)

lemma etaTerm_eq_integral (k : ℕ) (s : ℂ) :
    etaTerm k s = s * ∫ t in ((2 * k + 1 : ℕ) : ℝ)..((2 * k + 2 : ℕ) : ℝ), (t : ℂ) ^ (-(s + 1)) := by
  have ha : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  have hab : ((2 * k + 1 : ℕ) : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * k + 2)
  have hderiv : ∀ t ∈ Set.uIcc ((2 * k + 1 : ℕ) : ℝ) ((2 * k + 2 : ℕ) : ℝ),
      HasDerivAt (fun u : ℝ => -((u : ℂ) ^ (-s))) (s * (t : ℂ) ^ (-(s + 1))) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    have h2 : HasDerivAt (fun u : ℝ => (u : ℂ) ^ (-s)) ((-s) * (t : ℂ) ^ (-s - 1) * 1) t :=
      ((hasDerivAt_id (t : ℂ)).cpow_const (Or.inl (by simp [htpos]))).comp_ofReal
    have h3 := h2.neg
    refine h3.congr_deriv ?_
    have hexp : -s - 1 = -(s + 1) := by ring
    rw [hexp]; ring
  have hcont : ContinuousOn (fun t : ℝ => s * (t : ℂ) ^ (-(s + 1)))
      (Set.uIcc ((2 * k + 1 : ℕ) : ℝ) ((2 * k + 2 : ℕ) : ℝ)) := by
    rw [Set.uIcc_of_le hab]
    refine continuousOn_const.mul fun t ht => ?_
    exact (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (lt_of_lt_of_le ha ht.1).ne')).continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [intervalIntegral.integral_const_mul] at hftc
  rw [hftc]; unfold etaTerm; simp only [Complex.ofReal_natCast]; ring

lemma norm_etaTerm_le (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖etaTerm k s‖ ≤ ‖s‖ * ((2 * k + 1 : ℕ) : ℝ) ^ (-(s.re + 1)) := by
  rw [etaTerm_eq_integral, norm_mul]
  have ha : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  have hab : ((2 * k + 1 : ℕ) : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * k + 2)
  have hlen : |((2 * k + 2 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ)| = 1 := by
    have : ((2 * k + 2 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) = 1 := by push_cast; ring
    rw [this, abs_one]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (C := ((2 * k + 1 : ℕ) : ℝ) ^ (-(s.re + 1)))
    (a := ((2 * k + 1 : ℕ) : ℝ)) (b := ((2 * k + 2 : ℕ) : ℝ))
    (f := fun t : ℝ => (t : ℂ) ^ (-(s + 1))) fun t ht => by
      rw [Set.uIoc_of_le hab] at ht
      have htpos : 0 < t := lt_trans ha ht.1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, add_re, one_re]
      exact Real.rpow_le_rpow_of_nonpos ha ht.1.le (by linarith)
  rw [hlen, mul_one] at hbd
  exact hbd

lemma summable_etaTerm_bound {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun k : ℕ => ((2 * k + 1 : ℕ) : ℝ) ^ (-(δ + 1))) := by
  have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ (-(δ + 1)))) := by
    have := Real.summable_nat_rpow_inv.mpr (show 1 < δ + 1 by linarith)
    refine this.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
  exact h1.comp_injective (fun a b h => by omega)

lemma etaSum_differentiableOn :
    DifferentiableOn ℂ (fun s : ℂ => ∑' k : ℕ, etaTerm k s) {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hre0 : 0 < s₀.re := hs₀
  set δ := s₀.re / 2 with hδ_def
  have hδ : 0 < δ := by positivity
  let U : Set ℂ := Metric.ball s₀ δ
  have hU_open : IsOpen U := Metric.isOpen_ball
  have hU_mem : s₀ ∈ U := Metric.mem_ball_self hδ
  have hM : Summable (fun k : ℕ => (‖s₀‖ + δ) * ((2 * k + 1 : ℕ) : ℝ) ^ (-(δ + 1))) :=
    (summable_etaTerm_bound hδ).mul_left (‖s₀‖ + δ)
  have hdiff_k : ∀ k : ℕ, DifferentiableOn ℂ (etaTerm k) U := by
    intro k z _
    have h1 : 0 < (((2 * k + 1 : ℕ) : ℂ)).re := by simp; positivity
    have h2 : 0 < (((2 * k + 2 : ℕ) : ℂ)).re := by simp; positivity
    exact (((differentiableAt_const _).cpow differentiableAt_id.neg (Or.inl h1)).sub
      ((differentiableAt_const _).cpow differentiableAt_id.neg (Or.inl h2))).differentiableWithinAt
  have hbd : ∀ k : ℕ, ∀ z ∈ U, ‖etaTerm k z‖ ≤ (‖s₀‖ + δ) * ((2 * k + 1 : ℕ) : ℝ) ^ (-(δ + 1)) := by
    intro k z hz
    have hdist : ‖z - s₀‖ < δ := by simpa [U, Metric.mem_ball, dist_eq_norm] using hz
    have hzre : δ < z.re := by
      have h1 := Complex.abs_re_le_norm (z - s₀)
      simp only [Complex.sub_re] at h1
      have hlt := (abs_lt.mp (lt_of_le_of_lt h1 hdist)).1
      linarith [hδ_def]
    have hznorm : ‖z‖ ≤ ‖s₀‖ + δ := by
      calc ‖z‖ = ‖(z - s₀) + s₀‖ := by ring_nf
        _ ≤ ‖z - s₀‖ + ‖s₀‖ := norm_add_le _ _
        _ ≤ ‖s₀‖ + δ := by linarith
    have hpow : ((2 * k + 1 : ℕ) : ℝ) ^ (-(z.re + 1)) ≤ ((2 * k + 1 : ℕ) : ℝ) ^ (-(δ + 1)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ 2 * k + 1)) (by linarith)
    exact (norm_etaTerm_le k (lt_trans hδ hzre)).trans
      (mul_le_mul hznorm hpow (Real.rpow_nonneg (by positivity) _) (by positivity))
  have hhol : DifferentiableOn ℂ (fun s : ℂ => ∑' k : ℕ, etaTerm k s) U :=
    differentiableOn_tsum_of_summable_norm hM hdiff_k hU_open hbd
  exact (hhol.differentiableAt (hU_open.mem_nhds hU_mem)).differentiableWithinAt

lemma eta_eq_tsum_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = ∑' k : ℕ, etaTerm k s := by
  have hζ : riemannZeta s = ∑' n : ℕ, (n : ℂ) ^ (-s) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs]
    refine tsum_congr fun n => ?_
    rw [one_div, Complex.cpow_neg]
  have hsum_all : Summable (fun n : ℕ => (n : ℂ) ^ (-s)) := by
    have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ (-s.re))) := by
      simpa [Real.rpow_neg (Nat.cast_nonneg _)] using Real.summable_nat_rpow_inv.mpr hs
    refine Summable.of_norm_bounded h1 fun n => ?_
    rcases n with _ | n
    · rw [Nat.cast_zero, Nat.cast_zero, Complex.zero_cpow (by intro h; have := congrArg Complex.re h; simp at this; linarith),
        norm_zero]; exact Real.rpow_nonneg (le_refl 0) _
    · rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re]
  have hsum_odd : Summable (fun k : ℕ => ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) :=
    hsum_all.comp_injective (fun a b h => by omega)
  have hsum_even : Summable (fun k : ℕ => ((2 * k + 2 : ℕ) : ℂ) ^ (-s)) :=
    hsum_all.comp_injective (fun a b h => by omega)
  have h0 : ((0 : ℕ) : ℂ) ^ (-s) = 0 := by
    rw [Nat.cast_zero]
    exact Complex.zero_cpow (by intro h; have := congrArg Complex.re h; simp at this; linarith)
  have hsplit : ∑' n : ℕ, (n : ℂ) ^ (-s) =
      (∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) + (∑' k : ℕ, ((2 * k + 2 : ℕ) : ℂ) ^ (-s)) := by
    rw [hsum_all.tsum_eq_zero_add, h0, zero_add]
    have hshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s)) :=
      hsum_all.comp_injective Nat.succ_injective
    have heven_odd := tsum_even_add_odd
      (f := fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s))
      (hshift.comp_injective (fun a b h => by omega))
      (hshift.comp_injective (fun a b h => by omega))
    rw [← heven_odd]
  have heven_eq : ∑' k : ℕ, ((2 * k + 2 : ℕ) : ℂ) ^ (-s) =
      (2 : ℂ) ^ (-s) * ∑' n : ℕ, (n : ℂ) ^ (-s) := by
    rw [hsum_all.tsum_eq_zero_add, h0, zero_add, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    have h2 : ((2 * k + 2 : ℕ) : ℂ) = ((2 : ℝ) : ℂ) * (((k + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
    rw [h2, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    simp only [Complex.ofReal_ofNat, Complex.ofReal_natCast]
  have htsum_sub : ∑' k : ℕ, etaTerm k s =
      (∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) - (∑' k : ℕ, ((2 * k + 2 : ℕ) : ℂ) ^ (-s)) :=
    hsum_odd.tsum_sub hsum_even
  have h2pow : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
  rw [hζ, htsum_sub, h2pow]
  have hodd_eq : (∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) =
      (∑' n : ℕ, (n : ℂ) ^ (-s)) - (∑' k : ℕ, ((2 * k + 2 : ℕ) : ℂ) ^ (-s)) := by
    rw [hsplit]; ring
  rw [hodd_eq, heven_eq]; ring

lemma zetaReg_real_ne_zero {σ : ℝ} (hσ : 0 < σ) : zetaReg (σ : ℂ) ≠ 0 := by
  by_cases h1 : 1 ≤ σ
  · exact zetaReg_ne_zero_of_one_le_re (by simp [h1])
  · push Not at h1
    let lhs : ℂ → ℂ := Function.update (fun s : ℂ => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) 1 (Real.log 2 : ℂ)
    have hlhs_diff : DifferentiableOn ℂ lhs {s : ℂ | 0 < s.re} := by
      intro s _
      rcases ne_or_eq s 1 with hs | rfl
      · have h1' : DifferentiableAt ℂ (fun z : ℂ => (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z) s :=
          ((differentiableAt_const 1).sub ((differentiableAt_const _).cpow
            ((differentiableAt_const 1).sub differentiableAt_id) (Or.inl (by simp)))).mul
            (differentiableAt_riemannZeta hs)
        exact (h1'.congr_of_eventuallyEq (Filter.eventually_of_mem (isOpen_ne.mem_nhds hs)
          fun z hz => Function.update_of_ne (show z ≠ 1 from hz) _ _)).differentiableWithinAt
      · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt.differentiableWithinAt
        · filter_upwards [self_mem_nhdsWithin] with z hz
          have hz' : z ≠ 1 := hz
          have h1' : DifferentiableAt ℂ (fun w : ℂ => (1 - (2 : ℂ) ^ (1 - w)) * riemannZeta w) z :=
            ((differentiableAt_const 1).sub ((differentiableAt_const _).cpow
              ((differentiableAt_const 1).sub differentiableAt_id) (Or.inl (by simp)))).mul
              (differentiableAt_riemannZeta hz')
          exact h1'.congr_of_eventuallyEq (Filter.eventually_of_mem (isOpen_ne.mem_nhds hz')
            fun w hw => Function.update_of_ne (show w ≠ 1 from hw) _ _)
        · change ContinuousAt (Function.update (fun s : ℂ => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) 1 (Real.log 2 : ℂ)) 1
          rw [continuousAt_update_same]
          have hd : HasDerivAt (fun z : ℂ => -(2 : ℂ) ^ (1 - z)) (Real.log 2 : ℂ) 1 := by
            have hsub : HasDerivAt (fun z : ℂ => (1 : ℂ) - z) (-1) 1 :=
              ((hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub (hasDerivAt_id (1 : ℂ))).congr_deriv (by ring)
            have hc := (hsub.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))).neg
            refine hc.congr_deriv ?_
            rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]; simp
          have hslope : Tendsto (fun z : ℂ => (1 - (2 : ℂ) ^ (1 - z)) / (z - 1)) (𝓝[≠] 1) (𝓝 (Real.log 2 : ℂ)) := by
            have h2' := hasDerivAt_iff_tendsto_slope.mp hd
            refine h2'.congr' ?_
            filter_upwards [self_mem_nhdsWithin] with z hz
            simp only [slope_def_field, sub_self, Complex.cpow_zero, sub_neg_eq_add]
            ring
          have hprod := hslope.mul riemannZeta_residue_one
          rw [mul_one] at hprod
          refine hprod.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with z hz
          have hz0 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
          field_simp [hz0]
    have heq_all : ∀ s : ℂ, 0 < s.re → lhs s = ∑' k : ℕ, etaTerm k s := by
      have hopen : IsOpen {s : ℂ | 0 < s.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
      have hconn : IsPreconnected {s : ℂ | 0 < s.re} := (convex_halfSpace_re_gt 0).isPreconnected
      have han1 : AnalyticOnNhd ℂ lhs {s : ℂ | 0 < s.re} := hlhs_diff.analyticOnNhd hopen
      have han2 : AnalyticOnNhd ℂ (fun s => ∑' k : ℕ, etaTerm k s) {s : ℂ | 0 < s.re} :=
        etaSum_differentiableOn.analyticOnNhd hopen
      have hev : lhs =ᶠ[𝓝 (2 : ℂ)] (fun s => ∑' k : ℕ, etaTerm k s) := by
        filter_upwards [(continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)] with z hz
        have hz1 : z ≠ 1 := fun h => by rw [h] at hz; simp at hz
        simp only [lhs, Function.update_of_ne hz1]
        exact eta_eq_tsum_of_one_lt_re hz
      exact fun s hs => han1.eqOn_of_preconnected_of_eventuallyEq han2 hconn (by simp : (2 : ℂ) ∈ {s : ℂ | 0 < s.re}) hev hs
    have hσ_eq := heq_all (σ : ℂ) (by simp [hσ])
    have hσ_ne1 : (σ : ℂ) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    simp only [lhs, Function.update_of_ne hσ_ne1] at hσ_eq
    have hre_pos : 0 < (∑' k : ℕ, etaTerm k (σ : ℂ)).re := by
      have hterm_re : ∀ k : ℕ, (etaTerm k (σ : ℂ)).re =
          ((2 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * k + 2 : ℕ) : ℝ) ^ (-σ) := by
        intro k; unfold etaTerm
        rw [Complex.sub_re, ← Complex.ofReal_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
          ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_cpow (by positivity),
          Complex.ofReal_re, Complex.ofReal_re]
      have hsumm : Summable (fun k : ℕ => etaTerm k (σ : ℂ)) := by
        refine Summable.of_norm_bounded (g := fun k => ‖(σ : ℂ)‖ * ((2 * k + 1 : ℕ) : ℝ) ^ (-(σ + 1)))
          ((summable_etaTerm_bound hσ).mul_left _) fun k => ?_
        have h1 := norm_etaTerm_le k (by rw [Complex.ofReal_re]; exact hσ)
        rw [Complex.ofReal_re] at h1
        exact h1
      rw [Complex.re_tsum hsumm]
      simp_rw [hterm_re]
      have hnn : ∀ k : ℕ, 0 ≤ ((2 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * k + 2 : ℕ) : ℝ) ^ (-σ) := fun k => by
        have hle : ((2 * k + 2 : ℕ) : ℝ) ^ (-σ) ≤ ((2 * k + 1 : ℕ) : ℝ) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * k + 2)) (by linarith)
        linarith
      have h0pos : 0 < ((2 * 0 + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * 0 + 2 : ℕ) : ℝ) ^ (-σ) := by
        have hlt : ((2 : ℝ) ^ (-σ)) < (1 : ℝ) ^ (-σ) := by
          rw [Real.one_rpow, Real.rpow_neg (by norm_num)]
          exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) hσ)
        simpa using sub_pos.mpr hlt
      have hre_summ : Summable (fun k : ℕ => ((2 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * k + 2 : ℕ) : ℝ) ^ (-σ)) := by
        simpa [hterm_re] using Complex.reCLM.summable hsumm
      exact lt_of_lt_of_le h0pos (hre_summ.le_tsum 0 fun k _ => hnn k)
    intro hzero
    rw [zetaReg_of_ne_one hσ_ne1] at hzero
    rcases mul_eq_zero.mp hzero with hsub | hζ0
    · exact hσ_ne1 (sub_eq_zero.mp hsub)
    · rw [hζ0, mul_zero] at hσ_eq
      rw [← hσ_eq, Complex.zero_re] at hre_pos
      exact lt_irrefl 0 hre_pos

lemma exists_zetaReg_zero_half : ∃ s : ℂ, s.re = 1 / 2 ∧ zetaReg s = 0 := by
  obtain ⟨t, _, hzero⟩ := HardyFirstZero.first_zero_on_line
  refine ⟨1 / 2 + (t : ℂ) * I, by simp, ?_⟩
  have hne1 : (1 / 2 : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [zetaReg_of_ne_one hne1, hzero, mul_zero]

/-! ### Section 2: Holomorphic antiderivative and logarithm on convex open sets -/

lemma exists_holomorphic_antideriv_on_convex {U : Set ℂ} (hU : IsOpen U)
    (hconv : Convex ℝ U) {c : ℂ} (hc : c ∈ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ F : ℂ → ℂ, F c = 0 ∧ ∀ z ∈ U, HasDerivAt F (f z) z := by
  let F : ℂ → ℂ := fun z => ∫ t in (0 : ℝ)..1, f (c + (t : ℂ) * (z - c)) * (z - c)
  refine ⟨F, by simp [F], fun z0 hz0 => ?_⟩
  obtain ⟨r, hrpos, hball⟩ := Metric.isOpen_iff.mp hU z0 hz0
  have hball_half : Metric.closedBall z0 (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  let K : Set ℂ := (fun p : ℝ × ℂ => c + (p.1 : ℂ) * (p.2 - c)) ''
    (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall z0 (r / 2))
  have hK_sub : K ⊆ U := by
    rintro _ ⟨⟨t, w⟩, ⟨ht, hw⟩, rfl⟩
    dsimp only
    have h1 : c + (t : ℂ) * (w - c) = (1 - t) • c + t • w := by
      rw [Complex.real_smul, Complex.real_smul]; push_cast; ring
    rw [h1]
    exact hconv hc (hball_half hw) (by linarith [ht.2]) ht.1 (by ring)
  have hK_comp : IsCompact K :=
    (isCompact_Icc.prod (isCompact_closedBall z0 (r / 2))).image (by fun_prop)
  have hfc_cont : ContinuousOn f K := (hf.continuousOn).mono hK_sub
  have hdf_diff : DifferentiableOn ℂ (deriv f) U := hf.deriv hU
  have hdf_cont : ContinuousOn (deriv f) K := (hdf_diff.continuousOn).mono hK_sub
  obtain ⟨M1, hM1⟩ := hK_comp.exists_bound_of_continuousOn hfc_cont
  obtain ⟨M2, hM2⟩ := hK_comp.exists_bound_of_continuousOn hdf_cont
  let B : ℝ := max 0 M2 * (‖z0 - c‖ + r / 2) + max 0 M1
  let G : ℂ → ℝ → ℂ := fun z t => f (c + (t : ℂ) * (z - c)) * (z - c)
  let G' : ℂ → ℝ → ℂ := fun z t =>
    deriv f (c + (t : ℂ) * (z - c)) * (t : ℂ) * (z - c) + f (c + (t : ℂ) * (z - c))
  have hmemK : ∀ z ∈ Metric.ball z0 (r / 2), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      c + (t : ℂ) * (z - c) ∈ K := fun z hz t ht =>
    ⟨(t, z), ⟨ht, Metric.ball_subset_closedBall hz⟩, rfl⟩
  have hG_deriv : ∀ z ∈ Metric.ball z0 (r / 2), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun w => G w t) (G' z t) z := by
    intro z hz t ht
    have hpt : c + (t : ℂ) * (z - c) ∈ U := hK_sub (hmemK z hz t ht)
    have hf_at : HasDerivAt f (deriv f (c + (t : ℂ) * (z - c))) (c + (t : ℂ) * (z - c)) :=
      (hf.differentiableAt (hU.mem_nhds hpt)).hasDerivAt
    have hin : HasDerivAt (fun w => c + (t : ℂ) * (w - c)) (t : ℂ) z := by
      have h1 := ((hasDerivAt_id z).sub_const c).const_mul (t : ℂ)
      simpa using h1.const_add c
    have hcomp := hf_at.comp z hin
    have hsub : HasDerivAt (fun w => w - c) 1 z := (hasDerivAt_id z).sub_const c
    have hmul := hcomp.mul hsub
    refine hmul.congr_deriv ?_
    dsimp [G']; ring
  have hG_bound : ∀ z ∈ Metric.ball z0 (r / 2), ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖G' z t‖ ≤ B := by
    intro z hz t ht
    have hpt := hmemK z hz t ht
    have h1 : ‖deriv f (c + (t : ℂ) * (z - c))‖ ≤ max 0 M2 :=
      le_trans (hM2 _ hpt) (le_max_right _ _)
    have h2 : ‖f (c + (t : ℂ) * (z - c))‖ ≤ max 0 M1 :=
      le_trans (hM1 _ hpt) (le_max_right _ _)
    have h3 : ‖(t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg ht.1]; exact ht.2
    have h4 : ‖z - c‖ ≤ ‖z0 - c‖ + r / 2 := by
      have hzdist : ‖z - z0‖ < r / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      calc ‖z - c‖ = ‖(z - z0) + (z0 - c)‖ := by ring_nf
        _ ≤ ‖z - z0‖ + ‖z0 - c‖ := norm_add_le _ _
        _ ≤ ‖z0 - c‖ + r / 2 := by linarith
    dsimp [G']
    calc
      ‖deriv f (c + (t : ℂ) * (z - c)) * (t : ℂ) * (z - c) + f (c + (t : ℂ) * (z - c))‖
          ≤ ‖deriv f (c + (t : ℂ) * (z - c)) * (t : ℂ) * (z - c)‖ +
              ‖f (c + (t : ℂ) * (z - c))‖ := norm_add_le _ _
      _ = ‖deriv f (c + (t : ℂ) * (z - c))‖ * ‖(t : ℂ)‖ * ‖z - c‖ +
              ‖f (c + (t : ℂ) * (z - c))‖ := by rw [norm_mul, norm_mul]
      _ ≤ (max 0 M2) * 1 * (‖z0 - c‖ + r / 2) + max 0 M1 := by
            have hmul1 : ‖deriv f (c + (t : ℂ) * (z - c))‖ * ‖(t : ℂ)‖ ≤ max 0 M2 * 1 :=
              mul_le_mul h1 h3 (norm_nonneg _) (le_max_left _ _)
            exact add_le_add (mul_le_mul hmul1 h4 (norm_nonneg _) (by positivity)) h2
      _ = B := by dsimp [B]; ring
  have hcont_G : ∀ z ∈ Metric.ball z0 (r / 2), ContinuousOn (G z) (Set.Icc 0 1) := fun z hz =>
    (hfc_cont.comp (by fun_prop) (fun t ht => hmemK z hz t ht)).mul continuousOn_const
  have hcont_G' : ContinuousOn (G' z0) (Set.Icc 0 1) := by
    have hz0m : z0 ∈ Metric.ball z0 (r / 2) := Metric.mem_ball_self (by positivity)
    exact (((hdf_cont.comp (by fun_prop) (fun t ht => hmemK z0 hz0m t ht)).mul
      (Complex.continuous_ofReal.continuousOn)).mul continuousOn_const).add
      (hfc_cont.comp (by fun_prop) (fun t ht => hmemK z0 hz0m t ht))
  have hz0m : z0 ∈ Metric.ball z0 (r / 2) := Metric.mem_ball_self (by positivity)
  have hciB : IntervalIntegrable (fun _ : ℝ => B) volume 0 1 := intervalIntegrable_const
  have hdiff_int := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball z0 (r / 2)) (bound := fun _ => B)
    (Metric.isOpen_ball.mem_nhds hz0m)
    (Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz0m) fun z hz =>
      ((hcont_G z hz).mono (by rw [Set.uIoc_of_le zero_le_one]; exact Set.Ioc_subset_Icc_self)).aestronglyMeasurable
        measurableSet_uIoc)
    ((hcont_G z0 hz0m).intervalIntegrable_of_Icc zero_le_one)
    ((hcont_G'.mono (by rw [Set.uIoc_of_le zero_le_one]; exact Set.Ioc_subset_Icc_self)).aestronglyMeasurable
      measurableSet_uIoc)
    (Filter.Eventually.of_forall fun t ht z hz =>
      hG_bound z hz t (Set.Ioc_subset_Icc_self (by rwa [Set.uIoc_of_le zero_le_one] at ht)))
    hciB
    (Filter.Eventually.of_forall fun t ht z hz =>
      hG_deriv z hz t (Set.Ioc_subset_Icc_self (by rwa [Set.uIoc_of_le zero_le_one] at ht)))).2
  have hftc_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => (s : ℂ) * f (c + (s : ℂ) * (z0 - c))) (G' z0 t) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hpt : c + (t : ℂ) * (z0 - c) ∈ U := hK_sub (hmemK z0 hz0m t ht)
    have hf_at : HasDerivAt f (deriv f (c + (t : ℂ) * (z0 - c))) (c + (t : ℂ) * (z0 - c)) :=
      (hf.differentiableAt (hU.mem_nhds hpt)).hasDerivAt
    have hin : HasDerivAt (fun s : ℝ => c + (s : ℂ) * (z0 - c)) (z0 - c) t := by
      have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have h1 := (h0.mul_const (z0 - c)).const_add c
      simpa using h1
    have hcomp := hf_at.comp t hin
    have hmul := (Complex.ofRealCLM.hasDerivAt (x := t)).mul hcomp
    refine hmul.congr_deriv ?_
    dsimp [G']; ring
  have hint_ftc : IntervalIntegrable (G' z0) volume 0 1 :=
    hcont_G'.intervalIntegrable_of_Icc zero_le_one
  have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt hftc_deriv hint_ftc
  have hval : ∫ t in (0 : ℝ)..1, G' z0 t = f z0 := by
    rw [heval]; simp
  exact hdiff_int.congr_deriv hval

lemma exists_holomorphic_log_on_convex {U : Set ℂ} (hU : IsOpen U)
    (hconv : Convex ℝ U) {c : ℂ} (hc : c ∈ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hne : ∀ z ∈ U, f z ≠ 0) (v0 : ℂ) (hv0 : Complex.exp v0 = f c) :
    ∃ L : ℂ → ℂ, L c = v0 ∧ (∀ z ∈ U, HasDerivAt L (deriv f z / f z) z) ∧
      ∀ z ∈ U, Complex.exp (L z) = f z := by
  have hld : DifferentiableOn ℂ (fun z => deriv f z / f z) U :=
    (hf.deriv hU).div hf hne
  obtain ⟨F, hFc, hFderiv⟩ := exists_holomorphic_antideriv_on_convex hU hconv hc hld
  let L : ℂ → ℂ := fun z => v0 + F z
  have hLderiv : ∀ z ∈ U, HasDerivAt L (deriv f z / f z) z := fun z hz =>
    (hFderiv z hz).const_add v0
  have hconst : ∀ z ∈ U, f z * Complex.exp (-L z) = 1 := by
    have hQd : ∀ z ∈ U, HasDerivAt (fun w => f w * Complex.exp (-L w)) 0 z := by
      intro z hz
      have hf' := (hf.differentiableAt (hU.mem_nhds hz)).hasDerivAt
      have hE' : HasDerivAt (fun w => Complex.exp (-L w))
          (Complex.exp (-L z) * -(deriv f z / f z)) z := ((hLderiv z hz).neg).cexp
      have hmul : HasDerivAt (fun w => f w * Complex.exp (-L w))
          (deriv f z * Complex.exp (-L z) + f z * (Complex.exp (-L z) * -(deriv f z / f z))) z :=
        hf'.mul hE'
      have hzero : deriv f z * Complex.exp (-L z) +
          f z * (Complex.exp (-L z) * -(deriv f z / f z)) = 0 := by
        have hfz := hne z hz
        field_simp [hfz]; ring
      exact hmul.congr_deriv hzero
    intro z hz
    have hQeq := hconv.is_const_of_fderivWithin_eq_zero
      (f := fun w => f w * Complex.exp (-L w))
      (fun w hw => (hQd w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => by rw [fderivWithin_of_isOpen hU hw, (hQd w hw).hasFDerivAt.fderiv]; simp)
      hz hc
    rw [hQeq]
    simp [L, hFc, ← hv0, ← Complex.exp_add]
  refine ⟨L, by simp [L, hFc], hLderiv, fun z hz => ?_⟩
  have h1 := hconst z hz
  calc
    Complex.exp (L z) = 1 * Complex.exp (L z) := (one_mul _).symm
    _ = (f z * Complex.exp (-L z)) * Complex.exp (L z) := by rw [h1]
    _ = f z * (Complex.exp (-L z) * Complex.exp (L z)) := by ring
    _ = f z := by rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

lemma exists_holomorphic_log_on_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball c R)) (hne : ∀ z ∈ Metric.ball c R, f z ≠ 0)
    (v0 : ℂ) (hv0 : Complex.exp v0 = f c) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball c R) ∧
      F c = v0 ∧ ∀ z ∈ Metric.ball c R, Complex.exp (F z) = f z := by
  obtain ⟨F, hFc, hFd, hFexp⟩ := exists_holomorphic_log_on_convex Metric.isOpen_ball
    (convex_ball c R) (Metric.mem_ball_self hR) hf hne v0 hv0
  exact ⟨F, fun z hz => (hFd z hz).differentiableAt.differentiableWithinAt, hFc, hFexp⟩

/-! ### Section 3: Mellin transforms of `piWeight` and `Real.logIntegral` -/

noncomputable def piWeight (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, vonMangoldt k / Real.log (k : ℝ)

noncomputable def Hfun (t : ℝ) : ℝ :=
  piWeight t + (Real.log 2)⁻¹ - Real.logIntegral t

lemma measurable_piWeight : Measurable piWeight := by
  have : piWeight = (fun n : ℕ => ∑ k ∈ Finset.Ioc 0 n, vonMangoldt k / Real.log (k : ℝ)) ∘ Nat.floor := rfl
  rw [this]
  exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor

lemma hasDerivAt_logIntegral {x : ℝ} (hx : 1 < x) :
    HasDerivAt Real.logIntegral (1 / Real.log x) x := by
  have hcont : ContinuousOn (fun u : ℝ => 1 / Real.log u) (Set.Ioi (1 : ℝ)) := by
    refine continuousOn_const.div (Real.continuousOn_log.mono ?_) ?_
    · intro u hu; exact (zero_lt_one.trans hu).ne'
    · intro u hu; exact (Real.log_pos hu).ne'
  have hint : IntervalIntegrable (fun u : ℝ => 1 / Real.log u) volume 2 x := by
    refine (hcont.mono ?_).intervalIntegrable
    intro u hu
    rcases le_total 2 x with h2x | hx2
    · rw [Set.uIcc_of_le h2x] at hu; exact lt_of_lt_of_le one_lt_two hu.1
    · rw [Set.uIcc_comm, Set.uIcc_of_le hx2] at hu; exact lt_of_lt_of_le hx hu.1
  have hderiv := intervalIntegral.integral_hasDerivAt_right hint
    (by
      rw [← nhdsWithin_eq_nhds.mpr (isOpen_Ioi.mem_nhds hx)]
      exact hcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi x)
    (hcont.continuousAt (isOpen_Ioi.mem_nhds hx))
  have heq : Real.logIntegral = fun u : ℝ => Real.logIntegralTwo + ∫ t in (2 : ℝ)..u, 1 / Real.log t :=
    funext fun _ => rfl
  rw [heq]
  exact hderiv.const_add Real.logIntegralTwo

lemma continuousOn_logIntegral_Ioi : ContinuousOn Real.logIntegral (Set.Ioi (1 : ℝ)) :=
  fun _ hx => (hasDerivAt_logIntegral hx).continuousAt.continuousWithinAt

lemma aestronglyMeasurable_Hfun {N : ℕ} (hN : 3 ≤ N) :
    AEStronglyMeasurable Hfun (volume.restrict (Set.Ioi (N : ℝ))) := by
  have hsub : Set.Ioi (N : ℝ) ⊆ Set.Ioi (1 : ℝ) := Set.Ioi_subset_Ioi (by exact_mod_cast (by omega : 1 ≤ N))
  have hli : AEStronglyMeasurable Real.logIntegral (volume.restrict (Set.Ioi (N : ℝ))) :=
    (continuousOn_logIntegral_Ioi.mono hsub).aestronglyMeasurable measurableSet_Ioi
  exact ((measurable_piWeight.aestronglyMeasurable).add aestronglyMeasurable_const).sub hli

lemma abs_piWeight_le {t : ℝ} (ht : 0 ≤ t) : |piWeight t| ≤ t := by
  have hnn : 0 ≤ piWeight t := Finset.sum_nonneg fun k _ =>
    div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg k)
  rw [abs_of_nonneg hnn]
  have hle : piWeight t ≤ (⌊t⌋₊ : ℝ) := by
    calc piWeight t ≤ ∑ _k ∈ Finset.Ioc 0 ⌊t⌋₊, (1 : ℝ) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk1 : 1 ≤ k := (Finset.mem_Ioc.mp hk).1
          by_cases hk2 : k = 1
          · subst hk2; simp
          · have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
            exact (div_le_one hlogpos).mpr vonMangoldt_le_log
      _ = (⌊t⌋₊ : ℝ) := by simp
  exact hle.trans (Nat.floor_le ht)

lemma abs_logIntegral_le {t : ℝ} (ht : 2 ≤ t) :
    |Real.logIntegral t| ≤ (|Real.logIntegralTwo| + 2) * t := by
  have hcont : ContinuousOn (fun u : ℝ => 1 / Real.log u) (Set.Icc 2 t) := by
    refine continuousOn_const.div (Real.continuousOn_log.mono ?_) ?_
    · intro u hu; exact ne_of_gt (by linarith [hu.1])
    · intro u hu; exact (Real.log_pos (by linarith [hu.1])).ne'
  have hint_nn : 0 ≤ ∫ u in (2 : ℝ)..t, 1 / Real.log u :=
    intervalIntegral.integral_nonneg ht fun u hu =>
      one_div_nonneg.mpr (Real.log_nonneg (by linarith [hu.1]))
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmono := intervalIntegral.integral_mono_on ht (hcont.intervalIntegrable_of_Icc ht)
    (intervalIntegrable_const (μ := volume) (c := (2 : ℝ))) fun u hu => by
      have hlu : (1 / 2 : ℝ) < Real.log u := lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) hu.1)
      rw [div_le_iff₀ (by linarith)]; linarith
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hint_le : |∫ u in (2 : ℝ)..t, 1 / Real.log u| ≤ 2 * t := by
    rw [abs_of_nonneg hint_nn]; linarith
  have h1 : |Real.logIntegralTwo| ≤ |Real.logIntegralTwo| * t :=
    le_mul_of_one_le_right (abs_nonneg _) (by linarith)
  rw [Real.logIntegral]
  calc |Real.logIntegralTwo + ∫ u in (2 : ℝ)..t, 1 / Real.log u|
      ≤ |Real.logIntegralTwo| + |∫ u in (2 : ℝ)..t, 1 / Real.log u| := abs_add_le _ _
    _ ≤ |Real.logIntegralTwo| * t + 2 * t := add_le_add h1 hint_le
    _ = (|Real.logIntegralTwo| + 2) * t := by ring

lemma abs_Hfun_le {t : ℝ} (ht : 2 ≤ t) : |Hfun t| ≤ (|Real.logIntegralTwo| + 4) * t := by
  have h1 := abs_piWeight_le (by linarith : 0 ≤ t)
  have h2 := abs_logIntegral_le ht
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hinv : (Real.log 2)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ (by linarith)]; linarith
  have hinv_nn : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (by linarith)
  dsimp [Hfun]
  calc |piWeight t + (Real.log 2)⁻¹ - Real.logIntegral t|
      ≤ |piWeight t + (Real.log 2)⁻¹| + |Real.logIntegral t| := abs_sub _ _
    _ ≤ |piWeight t| + |(Real.log 2)⁻¹| + |Real.logIntegral t| := by gcongr; exact abs_add_le _ _
    _ = |piWeight t| + (Real.log 2)⁻¹ + |Real.logIntegral t| := by rw [abs_of_nonneg hinv_nn]
    _ ≤ t + 2 + (|Real.logIntegralTwo| + 2) * t := by linarith
    _ ≤ (|Real.logIntegralTwo| + 4) * t := by linarith

lemma riemannZeta_eq_exp_mul_integral {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = Complex.exp (s * ∫ t in Set.Ioi (1 : ℝ),
      (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
  have h1 : riemannZeta s = (1 : DirichletCharacter ℂ 1).LFunction s := by
    rw [DirichletCharacter.LFunction_modOne_eq]
  rw [h1, DirichletCharacter.LFunction_eq_LSeries (1 : DirichletCharacter ℂ 1) hs,
    ← DirichletCharacter.LSeries_eq_exp_LSeries (1 : DirichletCharacter ℂ 1) hs]
  congr 1
  have hcongr : (fun n : ℕ => (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (vonMangoldt n : ℂ) /
      (Real.log n : ℂ)) = (fun n : ℕ => ((vonMangoldt n / Real.log (n : ℝ) : ℝ) : ℂ)) := by
    ext n
    have h1n : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
      have hu : IsUnit (n : ZMod 1) := isUnit_of_subsingleton _
      exact MulChar.one_apply hu
    rw [h1n, one_mul]; push_cast; rfl
  rw [hcongr]
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖((vonMangoldt k / Real.log (k : ℝ) : ℝ) : ℂ)‖) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.isBigO_of_le atTop fun n => ?_
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _), Real.rpow_one,
      Real.norm_of_nonneg (Nat.cast_nonneg n)]
    calc ∑ k ∈ Finset.Icc 1 n, ‖((vonMangoldt k / Real.log (k : ℝ) : ℝ) : ℂ)‖
        ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg k))]
          have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          by_cases hk2 : k = 1
          · subst hk2; simp
          · exact (div_le_one (Real.log_pos (by exact_mod_cast (by omega : 1 < k)))).mpr vonMangoldt_le_log
      _ = (n : ℝ) := by simp
  rw [LSeries_eq_mul_integral' (fun n => ((vonMangoldt n / Real.log (n : ℝ) : ℝ) : ℂ)) zero_le_one hs hO]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have hIcc : Finset.Icc 1 ⌊t⌋₊ = Finset.Ioc 0 ⌊t⌋₊ := by ext k; simp; omega
  rw [hIcc, ← Complex.ofReal_sum]; rfl

lemma integrableOn_piWeight_cpow {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    have h1 : Measurable (fun t : ℝ => (piWeight t : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp measurable_piWeight
    have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := fun t ht =>
      (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (zero_lt_one.trans ht).ne')).continuousWithinAt
    exact h1.aestronglyMeasurable.mul (h2.aestronglyMeasurable measurableSet_Ioi)
  have hint : IntegrableOn (fun t : ℝ => t ^ (-s.re)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  refine hint.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := zero_lt_one.trans ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, add_re, one_re]
  calc |piWeight t| * t ^ (-(s.re + 1))
      ≤ t * t ^ (-(s.re + 1)) := mul_le_mul_of_nonneg_right (abs_piWeight_le htpos.le) (Real.rpow_nonneg htpos.le _)
    _ = t ^ (1 : ℝ) * t ^ (-(s.re + 1)) := by rw [Real.rpow_one]
    _ = t ^ (-s.re) := by rw [← Real.rpow_add htpos]; congr 1; ring

lemma integral_Ioc_piWeight_eq_sum (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    s * ∫ t in Set.Ioc (1 : ℝ) (N : ℝ), (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      ∑ m ∈ Finset.Ico 1 N, (piWeight (m : ℝ) : ℂ) * (((m : ℂ) ^ (-s)) - (((m + 1 : ℕ) : ℂ) ^ (-s))) := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; exact lt_irrefl 0 hs
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h1m : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm1 : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
    have hpiece : s * ∫ t in Set.Ioc (m : ℝ) ((m + 1 : ℕ) : ℝ), (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        (piWeight (m : ℝ) : ℂ) * (((m : ℂ) ^ (-s)) - (((m + 1 : ℕ) : ℂ) ^ (-s))) := by
      have hcongr : ∫ t in Set.Ioc (m : ℝ) ((m + 1 : ℕ) : ℝ), (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
          (piWeight (m : ℝ) : ℂ) * ∫ t in (m : ℝ)..((m + 1 : ℕ) : ℝ), (t : ℂ) ^ (-(s + 1)) := by
        rw [← intervalIntegral.integral_of_le hm1, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr_ae ?_
        have hne : ∀ᵐ t ∂volume, t ≠ ((m + 1 : ℕ) : ℝ) := by
          rw [ae_iff]; simp
        filter_upwards [hne] with t ht hmem
        rw [Set.uIoc_of_le hm1] at hmem
        have hfl : ⌊t⌋₊ = m := by
          have hlt : t < ((m + 1 : ℕ) : ℝ) := lt_of_le_of_ne hmem.2 ht
          exact (Nat.floor_eq_iff (by linarith [hmem.1])).mpr ⟨hmem.1.le, by simpa using hlt⟩
        simp [piWeight, hfl]
      rw [hcongr]
      have hderiv : ∀ t ∈ Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ),
          HasDerivAt (fun u : ℝ => -((u : ℂ) ^ (-s))) (s * (t : ℂ) ^ (-(s + 1))) t := by
        intro t ht
        rw [Set.uIcc_of_le hm1] at ht
        have htpos : 0 < t := by linarith [ht.1]
        have h2 : HasDerivAt (fun u : ℝ => (u : ℂ) ^ (-s)) ((-s) * (t : ℂ) ^ (-s - 1) * 1) t :=
          ((hasDerivAt_id (t : ℂ)).cpow_const (Or.inl (by simp [htpos]))).comp_ofReal
        refine h2.neg.congr_deriv ?_
        have : -s - 1 = -(s + 1) := by ring
        rw [this]; ring
      have hcont : ContinuousOn (fun t : ℝ => s * (t : ℂ) ^ (-(s + 1))) (Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ)) := by
        rw [Set.uIcc_of_le hm1]
        refine continuousOn_const.mul fun t ht => ?_
        exact (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (by linarith [ht.1]))).continuousWithinAt
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
      rw [intervalIntegral.integral_const_mul] at hftc
      calc s * ((piWeight (m : ℝ) : ℂ) * ∫ t in (m : ℝ)..((m + 1 : ℕ) : ℝ), (t : ℂ) ^ (-(s + 1)))
          = (piWeight (m : ℝ) : ℂ) * (s * ∫ t in (m : ℝ)..((m + 1 : ℕ) : ℝ), (t : ℂ) ^ (-(s + 1))) := by ring
        _ = (piWeight (m : ℝ) : ℂ) * ((((m : ℂ) ^ (-s)) - (((m + 1 : ℕ) : ℂ) ^ (-s)))) := by
            rw [hftc]; simp only [Complex.ofReal_natCast]; ring
    have hint1 : IntegrableOn (fun t : ℝ => (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioc (1 : ℝ) (m : ℝ)) := by
      have hmeas : AEStronglyMeasurable (fun t : ℝ => (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1)))
          (volume.restrict (Set.Ioc (1 : ℝ) (m : ℝ))) := by
        have h1 : Measurable (fun t : ℝ => (piWeight t : ℂ)) :=
          Complex.continuous_ofReal.measurable.comp measurable_piWeight
        have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioc (1 : ℝ) (m : ℝ)) := fun t ht =>
          (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (zero_lt_one.trans ht.1).ne')).continuousWithinAt
        exact h1.aestronglyMeasurable.mul (h2.aestronglyMeasurable measurableSet_Ioc)
      refine (integrableOn_const (C := (m : ℝ)) (hs := measure_Ioc_lt_top.ne)).mono' hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht1 : 1 < t := ht.1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht1), neg_re, add_re, one_re]
      calc |piWeight t| * t ^ (-(s.re + 1))
          ≤ t * 1 := mul_le_mul (abs_piWeight_le (by linarith))
            (Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by linarith))
            (Real.rpow_nonneg (by linarith) _) (by linarith)
        _ ≤ (m : ℝ) := by linarith [ht.2]
    have hint2 : IntegrableOn (fun t : ℝ => (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioc (m : ℝ) ((m + 1 : ℕ) : ℝ)) := by
      have hmeas : AEStronglyMeasurable (fun t : ℝ => (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1)))
          (volume.restrict (Set.Ioc (m : ℝ) ((m + 1 : ℕ) : ℝ))) := by
        have h1 : Measurable (fun t : ℝ => (piWeight t : ℂ)) :=
          Complex.continuous_ofReal.measurable.comp measurable_piWeight
        have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioc (m : ℝ) ((m + 1 : ℕ) : ℝ)) := fun t ht =>
          (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (by linarith [ht.1]))).continuousWithinAt
        exact h1.aestronglyMeasurable.mul (h2.aestronglyMeasurable measurableSet_Ioc)
      refine (integrableOn_const (C := ((m + 1 : ℕ) : ℝ)) (hs := measure_Ioc_lt_top.ne)).mono' hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht1 : 1 < t := by linarith [ht.1]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht1), neg_re, add_re, one_re]
      calc |piWeight t| * t ^ (-(s.re + 1))
          ≤ t * 1 := mul_le_mul (abs_piWeight_le (by linarith))
            (Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by linarith))
            (Real.rpow_nonneg (by linarith) _) (by linarith)
        _ ≤ ((m + 1 : ℕ) : ℝ) := by linarith [ht.2]
    rw [← Set.Ioc_union_Ioc_eq_Ioc h1m hm1,
      setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hint1 hint2,
      mul_add, ih, hpiece, Finset.sum_Ico_succ_top hm]

lemma integral_Ioi_const_cpow {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    s * ∫ t in Set.Ioi (N : ℝ), (t : ℂ) ^ (-(s + 1)) = (N : ℂ) ^ (-s) := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; exact lt_irrefl 0 hs
  have hre : (-(s + 1)).re < -1 := by simp only [neg_re, add_re, one_re]; linarith
  have h1 := integral_Ioi_cpow_of_lt hre (by exact_mod_cast (show 0 < N by omega) : (0 : ℝ) < (N : ℝ))
  have hexp : -(s + 1) + 1 = -s := by ring
  rw [h1, hexp]
  simp only [Complex.ofReal_natCast]
  field_simp [hs0]

lemma integrableOn_logIntegral_cpow {N : ℕ} (hN : 3 ≤ N) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (Real.logIntegral t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (N : ℝ)) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (Real.logIntegral t : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (volume.restrict (Set.Ioi (N : ℝ))) := by
    have h1 : ContinuousOn (fun t : ℝ => (Real.logIntegral t : ℂ)) (Set.Ioi (N : ℝ)) :=
      Complex.continuous_ofReal.comp_continuousOn (continuousOn_logIntegral_Ioi.mono (Set.Ioi_subset_Ioi hN1.le))
    have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi (N : ℝ)) := fun t ht =>
      (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (ne_of_gt (by linarith [hN1, ht.out])))).continuousWithinAt
    exact (h1.mul h2).aestronglyMeasurable measurableSet_Ioi
  have hint : IntegrableOn (fun t : ℝ => (|Real.logIntegralTwo| + 2) * t ^ (-s.re)) (Set.Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by positivity : (0 : ℝ) < (N : ℝ))).const_mul (|Real.logIntegralTwo| + 2)
  refine hint.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht2 : 2 ≤ t := le_trans (by exact_mod_cast (show 2 ≤ N by omega)) ht.le
  have htpos : 0 < t := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, add_re, one_re]
  calc |Real.logIntegral t| * t ^ (-(s.re + 1))
      ≤ ((|Real.logIntegralTwo| + 2) * t) * t ^ (-(s.re + 1)) := mul_le_mul_of_nonneg_right (abs_logIntegral_le ht2) (Real.rpow_nonneg htpos.le _)
    _ = (|Real.logIntegralTwo| + 2) * (t ^ (1 : ℝ) * t ^ (-(s.re + 1))) := by rw [Real.rpow_one]; ring
    _ = (|Real.logIntegralTwo| + 2) * t ^ (-s.re) := by rw [← Real.rpow_add htpos]; congr 2; ring

lemma integrableOn_cpow_div_log {N : ℕ} (hN : 3 ≤ N) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s) / (Real.log t : ℂ)) (Set.Ioi (N : ℝ)) := by
  have hN2 : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-s) / (Real.log t : ℂ))
      (volume.restrict (Set.Ioi (N : ℝ))) := by
    have h1 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Set.Ioi (N : ℝ)) := fun t ht =>
      (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (ne_of_gt (by linarith [hN2, ht.out])))).continuousWithinAt
    have h2 : ContinuousOn (fun t : ℝ => (Real.log t : ℂ)) (Set.Ioi (N : ℝ)) :=
      Complex.continuous_ofReal.comp_continuousOn (Real.continuousOn_log.mono fun t ht => ne_of_gt (by linarith [hN2, ht.out]))
    exact (h1.div h2 fun t ht => Complex.ofReal_ne_zero.mpr (Real.log_pos (by linarith [hN2, ht.out])).ne').aestronglyMeasurable measurableSet_Ioi
  have hint : IntegrableOn (fun t : ℝ => 2 * t ^ (-s.re)) (Set.Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by positivity : (0 : ℝ) < (N : ℝ))).const_mul 2
  refine hint.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht2 : 2 < t := lt_trans hN2 ht
  have htpos : 0 < t := by linarith
  have hlog2 : (1 / 2 : ℝ) < Real.log t := lt_trans (by linarith [Real.log_two_gt_d9]) (Real.log_lt_log (by norm_num) ht2)
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re,
    Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Real.rpow_nonneg htpos.le (-s.re)]

lemma integral_Ioi_logIntegral_eq {N : ℕ} (hN : 3 ≤ N) {s : ℂ} (hs : 1 < s.re) :
    s * ∫ t in Set.Ioi (N : ℝ), (Real.logIntegral t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (Real.logIntegral N : ℂ) * (N : ℂ) ^ (-s) +
      ∫ t in Set.Ioi (N : ℝ), (t : ℂ) ^ (-s) / (Real.log t : ℂ) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 2 ≤ N by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  -- Integration by parts on [N, R] for R ≥ N
  have hibp : ∀ R : ℝ, (N : ℝ) ≤ R →
      s * ∫ t in (N : ℝ)..R, (Real.logIntegral t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        (Real.logIntegral N : ℂ) * (N : ℂ) ^ (-s) - (Real.logIntegral R : ℂ) * (R : ℂ) ^ (-s) +
        ∫ t in (N : ℝ)..R, (t : ℂ) ^ (-s) / (Real.log t : ℂ) := by
    intro R hNR
    have hderiv : ∀ t ∈ Set.uIcc (N : ℝ) R,
        HasDerivAt (fun u : ℝ => -(Real.logIntegral u : ℂ) * (u : ℂ) ^ (-s))
          (-(t : ℂ) ^ (-s) / (Real.log t : ℂ) + s * ((Real.logIntegral t : ℂ) * (t : ℂ) ^ (-(s + 1)))) t := by
      intro t ht
      rw [Set.uIcc_of_le hNR] at ht
      have ht1 : 1 < t := lt_of_lt_of_le hN1 ht.1
      have htpos : 0 < t := zero_lt_one.trans ht1
      have hli_d : HasDerivAt (fun u : ℝ => (Real.logIntegral u : ℂ)) ((1 / Real.log t : ℝ) : ℂ) t :=
        (hasDerivAt_logIntegral ht1).ofReal_comp
      have hpow_d : HasDerivAt (fun u : ℝ => (u : ℂ) ^ (-s)) ((-s) * (t : ℂ) ^ (-s - 1) * 1) t :=
        ((hasDerivAt_id (t : ℂ)).cpow_const (Or.inl (by simp [htpos]))).comp_ofReal
      have hmul := (hli_d.neg).mul hpow_d
      refine hmul.congr_deriv ?_
      have h1 : (Real.log t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos ht1).ne'
      have hexp : -s - 1 = -(s + 1) := by ring
      simp only [Pi.neg_apply]
      rw [hexp]; push_cast; field_simp [h1]
    have hcont1 : ContinuousOn (fun t : ℝ => -(t : ℂ) ^ (-s) / (Real.log t : ℂ)) (Set.uIcc (N : ℝ) R) := by
      rw [Set.uIcc_of_le hNR]
      have ha : ContinuousOn (fun t : ℝ => -(t : ℂ) ^ (-s)) (Set.Icc (N : ℝ) R) := fun t ht =>
        (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (ne_of_gt (by linarith [hN1, ht.1])))).neg.continuousWithinAt
      have hb : ContinuousOn (fun t : ℝ => (Real.log t : ℂ)) (Set.Icc (N : ℝ) R) :=
        Complex.continuous_ofReal.comp_continuousOn (Real.continuousOn_log.mono fun t ht => ne_of_gt (by linarith [hN1, ht.1]))
      exact ha.div hb fun t ht => Complex.ofReal_ne_zero.mpr (Real.log_pos (by linarith [hN1, ht.1])).ne'
    have hcont2 : ContinuousOn (fun t : ℝ => s * ((Real.logIntegral t : ℂ) * (t : ℂ) ^ (-(s + 1)))) (Set.uIcc (N : ℝ) R) := by
      rw [Set.uIcc_of_le hNR]
      have ha : ContinuousOn (fun t : ℝ => (Real.logIntegral t : ℂ)) (Set.Icc (N : ℝ) R) :=
        Complex.continuous_ofReal.comp_continuousOn (continuousOn_logIntegral_Ioi.mono fun t ht => show (1 : ℝ) < t by linarith [hN1, ht.1])
      have hb : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Icc (N : ℝ) R) := fun t ht =>
        (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (ne_of_gt (by linarith [hN1, ht.1])))).continuousWithinAt
      exact continuousOn_const.mul (ha.mul hb)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont1.add hcont2).intervalIntegrable
    rw [intervalIntegral.integral_add hcont1.intervalIntegrable hcont2.intervalIntegrable,
      intervalIntegral.integral_const_mul] at hftc
    have hneg_int : ∫ t in (N : ℝ)..R, -(t : ℂ) ^ (-s) / (Real.log t : ℂ) =
        -(∫ t in (N : ℝ)..R, (t : ℂ) ^ (-s) / (Real.log t : ℂ)) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ => by ring
    rw [hneg_int] at hftc
    simp only [Complex.ofReal_natCast] at hftc
    linear_combination hftc
  -- Take R → ∞
  have hLHS : Tendsto (fun R : ℝ => s * ∫ t in (N : ℝ)..R, (Real.logIntegral t : ℂ) * (t : ℂ) ^ (-(s + 1)))
      atTop (𝓝 (s * ∫ t in Set.Ioi (N : ℝ), (Real.logIntegral t : ℂ) * (t : ℂ) ^ (-(s + 1)))) :=
    (intervalIntegral_tendsto_integral_Ioi (N : ℝ) (integrableOn_logIntegral_cpow hN hs) tendsto_id).const_mul s
  have hInt2 : Tendsto (fun R : ℝ => ∫ t in (N : ℝ)..R, (t : ℂ) ^ (-s) / (Real.log t : ℂ))
      atTop (𝓝 (∫ t in Set.Ioi (N : ℝ), (t : ℂ) ^ (-s) / (Real.log t : ℂ))) :=
    intervalIntegral_tendsto_integral_Ioi (N : ℝ) (integrableOn_cpow_div_log hN hs) tendsto_id
  have hbdry : Tendsto (fun R : ℝ => (Real.logIntegral R : ℂ) * (R : ℂ) ^ (-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hpow : Tendsto (fun R : ℝ => (|Real.logIntegralTwo| + 2) * R ^ (1 - s.re)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun R : ℝ => (|Real.logIntegralTwo| + 2) * R ^ (-(s.re - 1))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < s.re - 1)).const_mul (|Real.logIntegralTwo| + 2)
      refine h1.congr fun R => by congr 2; ring
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hpow
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    have hRpos : 0 < R := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hRpos, neg_re]
    calc |Real.logIntegral R| * R ^ (-s.re)
        ≤ ((|Real.logIntegralTwo| + 2) * R) * R ^ (-s.re) := mul_le_mul_of_nonneg_right (abs_logIntegral_le hR) (Real.rpow_nonneg hRpos.le _)
      _ = (|Real.logIntegralTwo| + 2) * (R ^ (1 : ℝ) * R ^ (-s.re)) := by rw [Real.rpow_one]; ring
      _ = (|Real.logIntegralTwo| + 2) * R ^ (1 - s.re) := by rw [← Real.rpow_add hRpos, sub_eq_add_neg]
  have hRHS : Tendsto (fun R : ℝ => (Real.logIntegral N : ℂ) * (N : ℂ) ^ (-s) -
      (Real.logIntegral R : ℂ) * (R : ℂ) ^ (-s) +
      ∫ t in (N : ℝ)..R, (t : ℂ) ^ (-s) / (Real.log t : ℂ))
      atTop (𝓝 ((Real.logIntegral N : ℂ) * (N : ℂ) ^ (-s) +
      ∫ t in Set.Ioi (N : ℝ), (t : ℂ) ^ (-s) / (Real.log t : ℂ))) := by
    simpa using ((tendsto_const_nhds.sub hbdry).add hInt2)
  have hev : (fun R : ℝ => s * ∫ t in (N : ℝ)..R, (Real.logIntegral t : ℂ) * (t : ℂ) ^ (-(s + 1))) =ᶠ[atTop]
      (fun R : ℝ => (Real.logIntegral N : ℂ) * (N : ℂ) ^ (-s) - (Real.logIntegral R : ℂ) * (R : ℂ) ^ (-s) +
      ∫ t in (N : ℝ)..R, (t : ℂ) ^ (-s) / (Real.log t : ℂ)) :=
    Filter.eventually_of_mem (eventually_ge_atTop (N : ℝ)) hibp
  exact tendsto_nhds_unique (hLHS.congr' hev) hRHS

lemma hasDerivAt_integral_cpow_div_log {N : ℕ} (hN : 3 ≤ N) {s₀ : ℂ} (hs₀ : 1 < s₀.re) :
    HasDerivAt (fun s : ℂ => ∫ t in Set.Ioi (N : ℝ), (t : ℂ) ^ (-s) / (Real.log t : ℂ))
      (-(N : ℂ) ^ (1 - s₀) / (s₀ - 1)) s₀ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN2 : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
  set δ := (s₀.re - 1) / 2 with hδ_def
  have hδ : 0 < δ := by positivity
  let μ := volume.restrict (Set.Ioi (N : ℝ))
  let F : ℂ → ℝ → ℂ := fun s t => (t : ℂ) ^ (-s) / (Real.log t : ℂ)
  let F' : ℂ → ℝ → ℂ := fun s t => -((t : ℂ) ^ (-s))
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (F s) μ := fun s => by
    have h1 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Set.Ioi (N : ℝ)) := fun t ht =>
      (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (ne_of_gt (by linarith [hN2, ht.out])))).continuousWithinAt
    have h2 : ContinuousOn (fun t : ℝ => (Real.log t : ℂ)) (Set.Ioi (N : ℝ)) :=
      Complex.continuous_ofReal.comp_continuousOn (Real.continuousOn_log.mono fun t ht => ne_of_gt (by linarith [hN2, ht.out]))
    exact (h1.div h2 fun t ht => Complex.ofReal_ne_zero.mpr (Real.log_pos (by linarith [hN2, ht.out])).ne').aestronglyMeasurable measurableSet_Ioi
  have hmeas' : AEStronglyMeasurable (F' s₀) μ := by
    have h1 : ContinuousOn (fun t : ℝ => -((t : ℂ) ^ (-s₀))) (Set.Ioi (N : ℝ)) := fun t ht =>
      (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (ne_of_gt (by linarith [hN2, ht.out])))).neg.continuousWithinAt
    exact h1.aestronglyMeasurable measurableSet_Ioi
  have hbound_int : Integrable (fun t : ℝ => t ^ (-(1 + δ))) μ :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hNpos
  have hbound : ∀ᵐ t ∂μ, ∀ s ∈ Metric.ball s₀ δ, ‖F' s t‖ ≤ t ^ (-(1 + δ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s hs
    have ht1 : 1 < t := by linarith [hN2, ht.out]
    have htpos : 0 < t := zero_lt_one.trans ht1
    have hsre : 1 + δ ≤ s.re := by
      have h1 := Complex.abs_re_le_norm (s - s₀)
      simp only [Complex.sub_re, Complex.re_ofNat] at h1
      have h2 : ‖s - s₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hs
      have h3 := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
      linarith [hδ_def]
    dsimp [F']
    rw [norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re]
    exact Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
  have hdiff : ∀ᵐ t ∂μ, ∀ s ∈ Metric.ball s₀ δ, HasDerivAt (F · t) (F' s t) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s _
    have htpos : 0 < t := lt_trans hNpos ht
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htpos.ne'
    have hlogne : (Real.log t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos (by linarith [hN2, ht.out])).ne'
    have h1 : HasDerivAt (fun z : ℂ => (t : ℂ) ^ (-z)) ((t : ℂ) ^ (-s) * Complex.log (t : ℂ) * (-1)) s :=
      (hasDerivAt_id s).neg.const_cpow (Or.inl htne)
    rw [← Complex.ofReal_log htpos.le] at h1
    have h2 := h1.div_const (Real.log t : ℂ)
    refine h2.congr_deriv ?_
    dsimp [F']; field_simp [hlogne]
  have hres := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
    (Eventually.of_forall hmeas) (integrableOn_cpow_div_log hN hs₀) hmeas' hbound hbound_int hdiff).2
  have hval : ∫ t, F' s₀ t ∂μ = -(N : ℂ) ^ (1 - s₀) / (s₀ - 1) := by
    have hre : (-s₀).re < -1 := by simp only [neg_re]; linarith
    have hint := integral_Ioi_cpow_of_lt hre hNpos
    have hneg : ∫ t, F' s₀ t ∂μ = -(∫ t in Set.Ioi (N : ℝ), (t : ℂ) ^ (-s₀)) := by
      dsimp [F', μ]; rw [integral_neg]
    rw [hneg, hint]
    have h1 : -s₀ + 1 = 1 - s₀ := by ring
    have hne : s₀ - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
    have hne2 : 1 - s₀ ≠ 0 := fun h => hne (by linear_combination -h)
    rw [h1]; simp only [Complex.ofReal_natCast]; field_simp [hne, hne2]; ring
  rw [hval] at hres
  exact hres

lemma exists_entire_logIntegral_mellin (N : ℕ) (hN : 3 ≤ N) :
    ∃ E : ℂ → ℂ, Differentiable ℂ E ∧
      ∀ s : ℂ, 1 < s.re →
        Complex.exp (s * ∫ t in Set.Ioi (N : ℝ), (Real.logIntegral t : ℂ) * (t : ℂ) ^ (-(s + 1))) =
          (s - 1)⁻¹ * Complex.exp (E s) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hNne : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hNpos.ne'
  let h : ℂ → ℂ := Function.update (fun z : ℂ => (1 - (N : ℂ) ^ (1 - z)) / (z - 1)) 1 (Real.log N : ℂ)
  have hh_diff : Differentiable ℂ h := by
    intro s
    rcases ne_or_eq s 1 with hs | rfl
    · have h1 : DifferentiableAt ℂ (fun z : ℂ => (1 - (N : ℂ) ^ (1 - z)) / (z - 1)) s :=
        ((differentiableAt_const 1).sub ((differentiableAt_const _).cpow
          ((differentiableAt_const 1).sub differentiableAt_id) (Or.inl (by simp [hNpos])))).div
          (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs)
      exact h1.congr_of_eventuallyEq (Filter.eventually_of_mem (isOpen_ne.mem_nhds hs)
        fun z hz => Function.update_of_ne (show z ≠ 1 from hz) _ _)
    · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      · filter_upwards [self_mem_nhdsWithin] with z hz
        have hz' : z ≠ 1 := hz
        have h1 : DifferentiableAt ℂ (fun w : ℂ => (1 - (N : ℂ) ^ (1 - w)) / (w - 1)) z :=
          ((differentiableAt_const 1).sub ((differentiableAt_const _).cpow
            ((differentiableAt_const 1).sub differentiableAt_id) (Or.inl (by simp [hNpos])))).div
            (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hz')
        exact h1.congr_of_eventuallyEq (Filter.eventually_of_mem (isOpen_ne.mem_nhds hz')
          fun w hw => Function.update_of_ne (show w ≠ 1 from hw) _ _)
      · change ContinuousAt (Function.update (fun z : ℂ => (1 - (N : ℂ) ^ (1 - z)) / (z - 1)) 1 (Real.log N : ℂ)) 1
        rw [continuousAt_update_same]
        have hd : HasDerivAt (fun z : ℂ => -(N : ℂ) ^ (1 - z)) (Real.log N : ℂ) 1 := by
          have hsub : HasDerivAt (fun z : ℂ => (1 : ℂ) - z) (-1) 1 :=
            ((hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub (hasDerivAt_id (1 : ℂ))).congr_deriv (by ring)
          have hc := (hsub.const_cpow (Or.inl hNne)).neg
          refine hc.congr_deriv ?_
          rw [Complex.ofReal_log hNpos.le]; simp
        have h2 := hasDerivAt_iff_tendsto_slope.mp hd
        refine h2.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        simp only [slope_def_field, sub_self, Complex.cpow_zero, sub_neg_eq_add]
        ring
  obtain ⟨E₁, hE₁_zero, hE₁_deriv⟩ := exists_holomorphic_antideriv_on_convex isOpen_univ convex_univ
    (Set.mem_univ (2 : ℂ)) hh_diff.differentiableOn
  let J : ℂ → ℂ := fun s => ∫ t in Set.Ioi (N : ℝ), (t : ℂ) ^ (-s) / (Real.log t : ℂ)
  let E : ℂ → ℂ := fun s => (Real.logIntegral N : ℂ) * (N : ℂ) ^ (-s) + J 2 + E₁ s
  have hE_diff : Differentiable ℂ E := fun s =>
    (((differentiableAt_const _).mul ((differentiableAt_const _).cpow differentiableAt_id.neg
      (Or.inl (by simp [hNpos])))).add (differentiableAt_const _)).add (hE₁_deriv s (Set.mem_univ s)).differentiableAt
  refine ⟨E, hE_diff, fun s hs => ?_⟩
  rw [integral_Ioi_logIntegral_eq hN hs]
  have hQ_eq : (s - 1) * Complex.exp (J s - (J 2 + E₁ s)) = 1 := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
    have hconv : Convex ℝ {z : ℂ | 1 < z.re} := convex_halfSpace_re_gt 1
    have hQd : ∀ z ∈ {w : ℂ | 1 < w.re}, HasDerivAt (fun w : ℂ => (w - 1) * Complex.exp (J w - (J 2 + E₁ w))) 0 z := by
      intro z hz
      have hz1 : z ≠ 1 := fun heq => by rw [heq] at hz; simp at hz
      have hzsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
      have hJd : HasDerivAt J (-(N : ℂ) ^ (1 - z) / (z - 1)) z := hasDerivAt_integral_cpow_div_log hN hz
      have hEd : HasDerivAt (fun w => J 2 + E₁ w) (h z) z := (hE₁_deriv z (Set.mem_univ z)).const_add (J 2)
      have hexp_d := (hJd.sub hEd).cexp
      have hmul := ((hasDerivAt_id z).sub_const 1).mul hexp_d
      refine hmul.congr_deriv ?_
      have hhz : h z = (1 - (N : ℂ) ^ (1 - z)) / (z - 1) := by simp [h, hz1]
      rw [hhz]; dsimp only [id_eq]; field_simp [hzsub]; ring
    have hconst := hconv.is_const_of_fderivWithin_eq_zero
      (f := fun w : ℂ => (w - 1) * Complex.exp (J w - (J 2 + E₁ w)))
      (fun w hw => (hQd w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => by rw [fderivWithin_of_isOpen hopen hw, (hQd w hw).hasFDerivAt.fderiv]; simp)
      hs (by simp : (2 : ℂ) ∈ {w : ℂ | 1 < w.re})
    rw [hconst, hE₁_zero]
    simp; norm_num
  have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hJexp : Complex.exp (J s) = (s - 1)⁻¹ * Complex.exp (J 2 + E₁ s) := by
    have h1 : Complex.exp (J s) = Complex.exp (J s - (J 2 + E₁ s)) * Complex.exp (J 2 + E₁ s) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h2 : Complex.exp (J s - (J 2 + E₁ s)) = (s - 1)⁻¹ :=
      eq_inv_of_mul_eq_one_right hQ_eq
    rw [h1, h2]
  dsimp only [E, J] at hJexp ⊢
  rw [Complex.exp_add, hJexp, Complex.exp_add, Complex.exp_add, Complex.exp_add]
  ring

/-! ### Section 4: Landau's theorem on `Hfun` and final contradiction -/

noncomputable def gDeriv (N k : ℕ) (s : ℂ) : ℂ :=
  (-1 : ℂ) ^ k * ∫ t in Set.Ioi (N : ℝ), (Hfun t : ℂ) * ((Real.log t : ℂ) ^ k) * (t : ℂ) ^ (-(s + 1))

lemma integrableOn_Hfun_log_pow {N : ℕ} (hN : 3 ≤ N) (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun t : ℝ => |Hfun t| * (Real.log t) ^ k * t ^ (-(σ + 1))) (Set.Ioi (N : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 2 ≤ N by omega)
  set δ := (σ - 1) / 2
  have hδ : 0 < δ := by positivity
  have hmeas : AEStronglyMeasurable (fun t : ℝ => |Hfun t| * (Real.log t) ^ k * t ^ (-(σ + 1)))
      (volume.restrict (Set.Ioi (N : ℝ))) :=
    ((continuous_abs.comp_aestronglyMeasurable (aestronglyMeasurable_Hfun hN)).mul
      (Real.measurable_log.pow_const k).aestronglyMeasurable).mul
      (measurable_id.pow_const _).aestronglyMeasurable
  let C : ℝ := (|Real.logIntegralTwo| + 4) * ((k : ℝ) / δ) ^ k
  have hint : IntegrableOn (fun t : ℝ => C * t ^ (-(1 + δ))) (Set.Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hNpos).const_mul C
  refine hint.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht2 : 2 ≤ t := le_trans hN2 ht.le
  have ht1 : 1 < t := by linarith
  have htpos : 0 < t := zero_lt_one.trans ht1
  have hlog_nn : 0 ≤ Real.log t := Real.log_nonneg ht1.le
  have hpow_le : (Real.log t) ^ k ≤ ((k : ℝ) / δ) ^ k * t ^ δ := by
    by_cases hk0 : k = 0
    · subst hk0; simp [Real.one_le_rpow ht1.le hδ.le]
    · have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
      have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos htpos (δ / (k : ℝ)))
      rw [Real.log_rpow htpos] at h1
      have h2 : Real.log t ≤ ((k : ℝ) / δ) * t ^ (δ / (k : ℝ)) := by
        have h3 : (δ / (k : ℝ)) * Real.log t ≤ t ^ (δ / (k : ℝ)) := by linarith
        have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ (k : ℝ) / δ)
        have hsimp : ((k : ℝ) / δ) * ((δ / (k : ℝ)) * Real.log t) = Real.log t := by
          field_simp [hδ.ne', hkpos.ne']
        linarith
      calc (Real.log t) ^ k
          ≤ (((k : ℝ) / δ) * t ^ (δ / (k : ℝ))) ^ k := pow_le_pow_left₀ hlog_nn h2 k
        _ = ((k : ℝ) / δ) ^ k * (t ^ (δ / (k : ℝ))) ^ k := mul_pow _ _ _
        _ = ((k : ℝ) / δ) ^ k * t ^ δ := by
            congr 1; rw [← Real.rpow_natCast, ← Real.rpow_mul htpos.le]
            congr 1; field_simp [hkpos.ne']
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hlog_nn k)) (Real.rpow_nonneg htpos.le _))]
  calc |Hfun t| * (Real.log t) ^ k * t ^ (-(σ + 1))
      ≤ ((|Real.logIntegralTwo| + 4) * t) * (((k : ℝ) / δ) ^ k * t ^ δ) * t ^ (-(σ + 1)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul (abs_Hfun_le ht2) hpow_le (pow_nonneg hlog_nn k) (by positivity))
          (Real.rpow_nonneg htpos.le _)
    _ = C * (t ^ (1 : ℝ) * t ^ δ * t ^ (-(σ + 1))) := by dsimp [C]; rw [Real.rpow_one]; ring
    _ = C * t ^ (-(1 + δ)) := by
        congr 1; rw [← Real.rpow_add htpos, ← Real.rpow_add htpos]
        congr 1; dsimp [δ]; ring

lemma hasDerivAt_gDeriv {N : ℕ} (hN : 3 ≤ N) (k : ℕ) {s₀ : ℂ} (hs₀ : 1 < s₀.re) :
    HasDerivAt (gDeriv N k) (gDeriv N (k + 1) s₀) s₀ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  set δ := (s₀.re - 1) / 2 with hδ_def
  have hδ : 0 < δ := by positivity
  let μ := volume.restrict (Set.Ioi (N : ℝ))
  let F : ℂ → ℝ → ℂ := fun s t => (Hfun t : ℂ) * ((Real.log t : ℂ) ^ k) * (t : ℂ) ^ (-(s + 1))
  let F' : ℂ → ℝ → ℂ := fun s t => -(Hfun t : ℂ) * ((Real.log t : ℂ) ^ (k + 1)) * (t : ℂ) ^ (-(s + 1))
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (F s) μ := fun s => by
    have h1 : AEStronglyMeasurable (fun t : ℝ => (Hfun t : ℂ) * ((Real.log t : ℂ) ^ k)) μ :=
      (Complex.continuous_ofReal.comp_aestronglyMeasurable (aestronglyMeasurable_Hfun hN)).mul
        ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).pow_const k).aestronglyMeasurable
    have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi (N : ℝ)) := fun t ht =>
      (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (hNpos.trans ht).ne')).continuousWithinAt
    exact h1.mul (h2.aestronglyMeasurable measurableSet_Ioi)
  have hmeas' : AEStronglyMeasurable (F' s₀) μ := by
    have h1 : AEStronglyMeasurable (fun t : ℝ => -(Hfun t : ℂ) * ((Real.log t : ℂ) ^ (k + 1))) μ :=
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable (aestronglyMeasurable_Hfun hN)).neg).mul
        ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).pow_const (k + 1)).aestronglyMeasurable
    have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s₀ + 1))) (Set.Ioi (N : ℝ)) := fun t ht =>
      (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (hNpos.trans ht).ne')).continuousWithinAt
    exact h1.mul (h2.aestronglyMeasurable measurableSet_Ioi)
  have hF_int : Integrable (F s₀) μ := by
    refine (integrableOn_Hfun_log_pow hN k hs₀).mono' (hmeas s₀) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 < t := lt_of_le_of_lt (by exact_mod_cast (show 1 ≤ N by omega)) ht
    have htpos : 0 < t := zero_lt_one.trans ht1
    dsimp [F]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg ht1.le), Complex.norm_cpow_eq_rpow_re_of_pos htpos,
      neg_re, add_re, one_re]
  have hbound_int : Integrable (fun t : ℝ => |Hfun t| * (Real.log t) ^ (k + 1) * t ^ (-((1 + δ) + 1))) μ :=
    integrableOn_Hfun_log_pow hN (k + 1) (by linarith)
  have hbound : ∀ᵐ t ∂μ, ∀ s ∈ Metric.ball s₀ δ,
      ‖F' s t‖ ≤ |Hfun t| * (Real.log t) ^ (k + 1) * t ^ (-((1 + δ) + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s hs
    have ht1 : 1 < t := lt_of_le_of_lt (by exact_mod_cast (show 1 ≤ N by omega)) ht
    have htpos : 0 < t := zero_lt_one.trans ht1
    have hsre : 1 + δ ≤ s.re := by
      have h1 := Complex.abs_re_le_norm (s - s₀)
      simp only [Complex.sub_re, Complex.re_ofNat] at h1
      have h2 : ‖s - s₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hs
      have h3 := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
      linarith [hδ_def]
    dsimp [F']
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg ht1.le), Complex.norm_cpow_eq_rpow_re_of_pos htpos,
      neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith))
      (mul_nonneg (abs_nonneg _) (pow_nonneg (Real.log_nonneg ht1.le) (k + 1)))
  have hdiff : ∀ᵐ t ∂μ, ∀ s ∈ Metric.ball s₀ δ, HasDerivAt (F · t) (F' s t) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s _
    have htpos : 0 < t := lt_trans hNpos ht
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htpos.ne'
    have h1 : HasDerivAt (fun z : ℂ => -(z + 1)) (-1) s := ((hasDerivAt_id s).add_const (1 : ℂ)).neg
    have hcpow := h1.const_cpow (Or.inl htne)
    rw [← Complex.ofReal_log htpos.le] at hcpow
    have hmul := hcpow.const_mul ((Hfun t : ℂ) * ((Real.log t : ℂ) ^ k))
    refine hmul.congr_deriv ?_
    dsimp [F']; rw [pow_succ]; ring
  have hres := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
    (Eventually.of_forall hmeas) hF_int hmeas' hbound hbound_int hdiff).2
  have hmul := hres.const_mul ((-1 : ℂ) ^ k)
  have hrew : (-1 : ℂ) ^ k * ∫ t, F' s₀ t ∂μ = gDeriv N (k + 1) s₀ := by
    dsimp [gDeriv, F', μ]
    have hneg : ∫ t in Set.Ioi (N : ℝ), -(Hfun t : ℂ) * (Real.log t : ℂ) ^ (k + 1) * (t : ℂ) ^ (-(s₀ + 1)) =
        -(∫ t in Set.Ioi (N : ℝ), (Hfun t : ℂ) * (Real.log t : ℂ) ^ (k + 1) * (t : ℂ) ^ (-(s₀ + 1))) := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
    rw [hneg, pow_succ]; ring
  exact hmul.congr_deriv hrew

lemma iteratedDeriv_gDeriv_zero {N : ℕ} (hN : 3 ≤ N) (k : ℕ) :
    ∀ s : ℂ, 1 < s.re → iteratedDeriv k (gDeriv N 0) s = gDeriv N k s := by
  induction k with
  | zero => intro s _; simp [iteratedDeriv_zero]
  | succ k ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (gDeriv N 0) =ᶠ[𝓝 s] gDeriv N k :=
      Filter.eventually_of_mem ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs)
        fun z hz => ih z hz
    rw [hev.deriv_eq]
    exact (hasDerivAt_gDeriv hN k hs).deriv

lemma differentiableOn_g0_of_integrableOn {N : ℕ} (hN : 3 ≤ N) {σ₁ : ℝ}
    (hH_nonneg : ∀ t ∈ Set.Ioi (N : ℝ), 0 ≤ Hfun t)
    (hInt : IntegrableOn (fun t : ℝ => Hfun t * t ^ (-σ₁ - 1)) (Set.Ioi (N : ℝ))) :
    DifferentiableOn ℂ (gDeriv N 0) {s : ℂ | σ₁ < s.re} := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  intro s₀ hs₀
  have hs₀gt : σ₁ < s₀.re := hs₀
  set δ := (s₀.re - σ₁) / 2 with hδ_def
  have hδ : 0 < δ := by linarith
  let μ := volume.restrict (Set.Ioi (N : ℝ))
  let F : ℂ → ℝ → ℂ := fun s t => (Hfun t : ℂ) * (t : ℂ) ^ (-(s + 1))
  let F' : ℂ → ℝ → ℂ := fun s t => -(Hfun t : ℂ) * (Real.log t : ℂ) * (t : ℂ) ^ (-(s + 1))
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (F s) μ := fun s => by
    have h1 : AEStronglyMeasurable (fun t : ℝ => (Hfun t : ℂ)) μ :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable (aestronglyMeasurable_Hfun hN)
    have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi (N : ℝ)) := fun t ht =>
      (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (hNpos.trans ht).ne')).continuousWithinAt
    exact h1.mul (h2.aestronglyMeasurable measurableSet_Ioi)
  have hmeas' : AEStronglyMeasurable (F' s₀) μ := by
    have h1 : AEStronglyMeasurable (fun t : ℝ => -(Hfun t : ℂ) * (Real.log t : ℂ)) μ :=
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable (aestronglyMeasurable_Hfun hN)).neg).mul
        (Complex.continuous_ofReal.measurable.comp Real.measurable_log).aestronglyMeasurable
    have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s₀ + 1))) (Set.Ioi (N : ℝ)) := fun t ht =>
      (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (hNpos.trans ht).ne')).continuousWithinAt
    exact h1.mul (h2.aestronglyMeasurable measurableSet_Ioi)
  have hF_int : Integrable (F s₀) μ := by
    refine hInt.mono' (hmeas s₀) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 < t := lt_of_le_of_lt hN1 ht
    have htpos : 0 < t := zero_lt_one.trans ht1
    dsimp [F]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hH_nonneg t ht),
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)) (hH_nonneg t ht)
  have hbound_int : Integrable (fun t : ℝ => (1 / δ) * (Hfun t * t ^ (-σ₁ - 1))) μ :=
    hInt.const_mul (1 / δ)
  have hbound : ∀ᵐ t ∂μ, ∀ s ∈ Metric.ball s₀ δ,
      ‖F' s t‖ ≤ (1 / δ) * (Hfun t * t ^ (-σ₁ - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s hs
    have ht1 : 1 < t := lt_of_le_of_lt hN1 ht
    have htpos : 0 < t := zero_lt_one.trans ht1
    have hH0 : 0 ≤ Hfun t := hH_nonneg t ht
    have hsre : σ₁ + δ ≤ s.re := by
      have h1 := Complex.abs_re_le_norm (s - s₀)
      simp only [Complex.sub_re, Complex.re_ofNat] at h1
      have h2 : ‖s - s₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hs
      have h3 := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
      linarith [hδ_def]
    have hlog_le : Real.log t ≤ (1 / δ) * t ^ δ := by
      have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos htpos δ)
      rw [Real.log_rpow htpos] at h1
      have h2 : δ * Real.log t ≤ t ^ δ := by linarith
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hδ]
      linarith
    dsimp [F']
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hH0, Real.norm_of_nonneg (Real.log_nonneg ht1.le),
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, add_re, one_re]
    calc Hfun t * Real.log t * t ^ (-(s.re + 1))
        ≤ Hfun t * ((1 / δ) * t ^ δ) * t ^ (-(σ₁ + δ + 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlog_le hH0)
            (Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith))
            (Real.rpow_nonneg htpos.le _)
            (mul_nonneg hH0 (mul_nonneg (by positivity) (Real.rpow_nonneg htpos.le _)))
      _ = (1 / δ) * (Hfun t * (t ^ δ * t ^ (-(σ₁ + δ + 1)))) := by ring
      _ = (1 / δ) * (Hfun t * t ^ (-σ₁ - 1)) := by
          congr 2; rw [← Real.rpow_add htpos]; congr 1; ring
  have hdiff : ∀ᵐ t ∂μ, ∀ s ∈ Metric.ball s₀ δ, HasDerivAt (F · t) (F' s t) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s _
    have htpos : 0 < t := hNpos.trans ht
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htpos.ne'
    have h1 : HasDerivAt (fun z : ℂ => -(z + 1)) (-1) s := ((hasDerivAt_id s).add_const (1 : ℂ)).neg
    have hcpow := h1.const_cpow (Or.inl htne)
    rw [← Complex.ofReal_log htpos.le] at hcpow
    have hmul := hcpow.const_mul (Hfun t : ℂ)
    exact hmul.congr_deriv (by dsimp [F']; ring)
  have hres := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
    (Eventually.of_forall hmeas) hF_int hmeas' hbound hbound_int hdiff).2
  have hrew : (fun s : ℂ => ∫ t, F s t ∂μ) = gDeriv N 0 := by ext s; simp [gDeriv, F, μ]
  rw [hrew] at hres
  exact hres.differentiableAt.differentiableWithinAt

set_option maxHeartbeats 800000 in
theorem skewes_R2_H2 : OMA.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R2.H2 := by
  unfold OMA.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R2.H2
  by_contra hnot
  push Not at hnot
  obtain ⟨X, hX⟩ := hnot
  let N : ℕ := max ⌈X⌉₊ 3
  have hN3 : 3 ≤ N := le_max_right _ _
  have hN1 : 1 ≤ N := by omega
  have hNpos : 0 < N := by omega
  have hH_nonneg : ∀ t ∈ Set.Ioi (N : ℝ), 0 ≤ Hfun t := by
    intro t ht
    have ht2 : 2 ≤ t := le_trans (by exact_mod_cast (show 2 ≤ N by omega)) ht.le
    have htX : X ≤ t := (Nat.le_ceil X).trans ((by exact_mod_cast (le_max_left ⌈X⌉₊ 3) : (⌈X⌉₊ : ℝ) ≤ (N : ℝ)).trans ht.le)
    have hge := hX t (max_le ht2 htX)
    dsimp [Hfun, piWeight]
    linarith
  -- Entire pieces: finite part P(s), constant part C(s), and logIntegral entire part Eli(s)
  let P : ℂ → ℂ := fun s =>
    ∑ m ∈ Finset.Ico 1 N, (piWeight (m : ℝ) : ℂ) * (((m : ℂ) ^ (-s)) - (((m + 1 : ℕ) : ℂ) ^ (-s)))
  have hP_diff : Differentiable ℂ P := by
    intro z
    refine DifferentiableAt.fun_sum fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
    have hmz : 0 < (m : ℂ).re := by simp; omega
    have hm1z : 0 < ((m + 1 : ℕ) : ℂ).re := by simp; positivity
    exact (differentiableAt_const _).mul
      (((differentiableAt_const _).cpow differentiableAt_id.neg (Or.inl hmz)).sub
        ((differentiableAt_const _).cpow differentiableAt_id.neg (Or.inl hm1z)))
  obtain ⟨Eli, hEli_diff, hEli_eq⟩ := exists_entire_logIntegral_mellin N hN3
  let Etot : ℂ → ℂ := fun s =>
    -P s + ((Real.log 2)⁻¹ : ℂ) * (N : ℂ) ^ (-s) - Eli s
  have hEtot_diff : Differentiable ℂ Etot := fun z =>
    ((hP_diff z).neg.add ((differentiableAt_const _).mul
      ((differentiableAt_const _).cpow differentiableAt_id.neg (Or.inl (by simp; positivity))))).sub
      (hEli_diff z)
  let Ψ : ℂ → ℂ := fun s => s * gDeriv N 0 s - Etot s
  have hzeta_eq_exp_Ψ : ∀ s : ℂ, 1 < s.re → zetaReg s = Complex.exp (Ψ s) := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
    rw [zetaReg_of_ne_one hs1, riemannZeta_eq_exp_mul_integral hs]
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hint_pi := integrableOn_piWeight_cpow hs
    have hsplit_pi : ∫ t in Set.Ioi (1 : ℝ), (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        (∫ t in Set.Ioc (1 : ℝ) (N : ℝ), (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1))) +
        (∫ t in Set.Ioi (N : ℝ), (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi h1N, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint_pi.mono_set Set.Ioc_subset_Ioi_self) (hint_pi.mono_set (Set.Ioi_subset_Ioi h1N))]
    have hint_c : IntegrableOn (fun t : ℝ => ((Real.log 2)⁻¹ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (N : ℝ)) := by
      have hre : (-(s + 1)).re < -1 := by simp only [neg_re, add_re, one_re]; linarith
      exact (integrableOn_Ioi_cpow_of_lt hre (by positivity : (0 : ℝ) < (N : ℝ))).const_mul _
    have hint_li := integrableOn_logIntegral_cpow hN3 hs
    have hint_piN := hint_pi.mono_set (Set.Ioi_subset_Ioi h1N)
    have hg0_eq : s * gDeriv N 0 s =
        (s * ∫ t in Set.Ioi (N : ℝ), (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1))) +
        ((Real.log 2)⁻¹ : ℂ) * (N : ℂ) ^ (-s) -
        (s * ∫ t in Set.Ioi (N : ℝ), (Real.logIntegral t : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
      have h1 : gDeriv N 0 s = ∫ t in Set.Ioi (N : ℝ),
          (((piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1))) +
           (((Real.log 2)⁻¹ : ℂ) * (t : ℂ) ^ (-(s + 1))) -
           ((Real.logIntegral t : ℂ) * (t : ℂ) ^ (-(s + 1)))) := by
        simp only [gDeriv, pow_zero, one_mul, mul_one]
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        dsimp [Hfun]; push_cast; ring
      have hint_sum : IntegrableOn (fun t : ℝ =>
          ((piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1))) +
          (((Real.log 2)⁻¹ : ℂ) * (t : ℂ) ^ (-(s + 1)))) (Set.Ioi (N : ℝ)) :=
        hint_piN.add hint_c
      rw [h1, integral_sub hint_sum hint_li, integral_add hint_piN hint_c,
        mul_sub, mul_add, integral_const_mul]
      have hc_eq : s * (((Real.log 2)⁻¹ : ℂ) * ∫ t in Set.Ioi (N : ℝ), (t : ℂ) ^ (-(s + 1))) =
          ((Real.log 2)⁻¹ : ℂ) * (N : ℂ) ^ (-s) := by
        rw [← mul_assoc, mul_comm s, mul_assoc, integral_Ioi_const_cpow hN1 (by linarith)]
      rw [hc_eq]
    have hPi_full : s * ∫ t in Set.Ioi (1 : ℝ), (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        P s + s * ∫ t in Set.Ioi (N : ℝ), (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      rw [hsplit_pi, mul_add, integral_Ioc_piWeight_eq_sum N hN1 (by linarith)]
    have hΨ_eq : Ψ s = (s * ∫ t in Set.Ioi (1 : ℝ), (piWeight t : ℂ) * (t : ℂ) ^ (-(s + 1))) -
        (s * ∫ t in Set.Ioi (N : ℝ), (Real.logIntegral t : ℂ) * (t : ℂ) ^ (-(s + 1))) + Eli s := by
      dsimp only [Ψ, Etot]
      rw [hg0_eq, hPi_full]; ring
    rw [hΨ_eq, Complex.exp_add, Complex.exp_sub, hEli_eq s hs]
    have hsub0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hexp0 : Complex.exp (Eli s) ≠ 0 := Complex.exp_ne_zero _
    field_simp [hsub0, hexp0]
  -- Define σ₀ = sup of real parts of zeros of zetaReg
  let S : Set ℝ := {σ : ℝ | ∃ t : ℝ, zetaReg ((σ : ℂ) + (t : ℂ) * I) = 0}
  obtain ⟨s_bad, hs_bad_re, hs_bad_zero⟩ := exists_zetaReg_zero_half
  have hs_bad_eq : ((1 / 2 : ℝ) : ℂ) + (s_bad.im : ℂ) * I = s_bad := by
    rw [← hs_bad_re]; exact Complex.re_add_im s_bad
  have hS_nonempty : S.Nonempty := ⟨1 / 2, s_bad.im, by rwa [hs_bad_eq]⟩
  have hS_bdd : BddAbove S := ⟨1, fun σ ⟨t, hz⟩ => by
    by_contra hgt; push Not at hgt
    exact zetaReg_ne_zero_of_one_le_re (by simp [hgt.le]) hz⟩
  set σ₀ := sSup S with hσ₀_def
  have hσ₀_ge : 1 / 2 ≤ σ₀ := le_csSup hS_bdd ⟨s_bad.im, by rwa [hs_bad_eq]⟩
  have hσ₀_le : σ₀ ≤ 1 := csSup_le hS_nonempty fun σ ⟨t, hz⟩ => by
    by_contra hgt; push Not at hgt
    exact zetaReg_ne_zero_of_one_le_re (by simp [hgt.le]) hz
  -- Since zetaReg(σ₀) ≠ 0, zetaReg is nonzero on a ball around σ₀
  have hZσ₀ : zetaReg (σ₀ : ℂ) ≠ 0 := zetaReg_real_ne_zero (by linarith)
  have hopen_nz : IsOpen {z : ℂ | zetaReg z ≠ 0} :=
    isOpen_ne_fun zetaReg_differentiable.continuous continuous_const
  obtain ⟨r₀, hr₀pos, hr₀ball⟩ := Metric.isOpen_iff.mp hopen_nz (σ₀ : ℂ) hZσ₀
  let r : ℝ := min r₀ (1 / 4)
  have hrpos : 0 < r := lt_min hr₀pos (by norm_num)
  have hr_sub : ∀ z ∈ Metric.ball (σ₀ : ℂ) r, zetaReg z ≠ 0 :=
    fun z hz => hr₀ball (Metric.ball_subset_ball (min_le_left _ _) hz)
  let ε : ℝ := min (r / 2) (r ^ 2 / 8)
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  have hε_lt_r : ε < r := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hrpos)
  let R : ℝ := 2 - σ₀ + ε
  have hRpos : 0 < R := by linarith
  have hball_re : ∀ z ∈ Metric.ball (2 : ℂ) R, 1 / 4 < z.re := by
    intro z hz
    have h1 := Complex.abs_re_le_norm (z - 2)
    simp only [Complex.sub_re, Complex.re_ofNat] at h1
    have h2 : ‖z - 2‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have h3 := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
    have hrle : r ≤ 1 / 4 := min_le_right _ _
    linarith
  have hball_nz : ∀ z ∈ Metric.ball (2 : ℂ) R, zetaReg z ≠ 0 := by
    intro z hz
    by_cases hgt : σ₀ < z.re
    · intro hzero
      exact (not_le_of_gt hgt) (le_csSup hS_bdd ⟨z.im, by simpa [Complex.re_add_im] using hzero⟩)
    · push Not at hgt
      refine hr_sub z ?_
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      have hre_gt : σ₀ - ε < z.re := by
        have h1 := Complex.abs_re_le_norm (z - 2)
        simp only [Complex.sub_re, Complex.re_ofNat] at h1
        have h3 := (abs_lt.mp (lt_of_le_of_lt h1 hz)).1
        linarith
      have hnorm2 : ‖z - 2‖ ^ 2 < R ^ 2 := by nlinarith [norm_nonneg (z - 2)]
      have hsq2 : ‖z - 2‖ ^ 2 = (z.re - 2) ^ 2 + z.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
      have hsqσ : ‖z - (σ₀ : ℂ)‖ ^ 2 = (z.re - σ₀) ^ 2 + z.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
      have hre_sq : (2 - σ₀) ^ 2 ≤ (z.re - 2) ^ 2 := by nlinarith
      have him_sq : z.im ^ 2 < 2 * ε * (2 - σ₀) + ε ^ 2 := by dsimp [R] at hnorm2; nlinarith
      have hdiff_sq : (z.re - σ₀) ^ 2 < ε ^ 2 := by nlinarith
      have hε_le1 : ε ≤ r / 2 := min_le_left _ _
      have hε_le2 : ε ≤ r ^ 2 / 8 := min_le_right _ _
      have h2σ : 2 - σ₀ ≤ 3 / 2 := by linarith
      have htot : ‖z - (σ₀ : ℂ)‖ ^ 2 < r ^ 2 := by
        rw [hsqσ]
        have h3 : 2 * ε * (2 - σ₀) ≤ 3 * ε := by nlinarith
        have h4 : 2 * ε ^ 2 ≤ r ^ 2 / 2 := by nlinarith
        have h5 : 3 * ε ≤ 3 * r ^ 2 / 8 := by linarith
        nlinarith
      nlinarith [norm_nonneg (z - (σ₀ : ℂ))]
  -- Construct holomorphic log F of zetaReg on Metric.ball 2 R with F 2 = Ψ 2
  obtain ⟨F, hF_diff, hF_two, hF_exp⟩ :=
    exists_holomorphic_log_on_ball hRpos zetaReg_differentiable.differentiableOn hball_nz
      (Ψ 2) (hzeta_eq_exp_Ψ 2 (by simp)).symm
  let gTilde : ℂ → ℂ := fun z => (F z + Etot z) / z
  have hgTilde_diff : DifferentiableOn ℂ gTilde (Metric.ball (2 : ℂ) R) := by
    intro z hz
    have hzre := hball_re z hz
    have hz0 : z ≠ 0 := fun h => by rw [h, zero_re] at hzre; linarith
    exact ((hF_diff z hz).add (hEtot_diff z).differentiableWithinAt).div differentiableWithinAt_id hz0
  have hR_gt_half : (1 / 2 : ℝ) < R := by dsimp [R]; linarith
  have hΨ_diff_half : DifferentiableOn ℂ Ψ (Metric.ball (2 : ℂ) (1 / 2)) := by
    intro z hz
    have hzre : 1 < z.re := by
      have h1 := Complex.abs_re_le_norm (z - 2)
      simp only [Complex.sub_re, Complex.re_ofNat] at h1
      have h2 : ‖z - 2‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      linarith [(abs_lt.mp (lt_of_le_of_lt h1 h2)).1]
    have hg0 : DifferentiableAt ℂ (gDeriv N 0) z := (hasDerivAt_gDeriv hN3 0 hzre).differentiableAt
    exact ((differentiableAt_id.mul hg0).sub (hEtot_diff z)).differentiableWithinAt
  have hF_eq_Ψ : ∀ z ∈ Metric.ball (2 : ℂ) (1 / 2), F z = Ψ z := by
    have hsub : Metric.ball (2 : ℂ) (1 / 2) ⊆ Metric.ball (2 : ℂ) R :=
      Metric.ball_subset_ball hR_gt_half.le
    have hexp_eq : ∀ z ∈ Metric.ball (2 : ℂ) (1 / 2), Complex.exp (F z - Ψ z) = 1 := by
      intro z hz
      have hzre : 1 < z.re := by
        have h1 := Complex.abs_re_le_norm (z - 2)
        simp only [Complex.sub_re, Complex.re_ofNat] at h1
        have h2 : ‖z - 2‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
        linarith [(abs_lt.mp (lt_of_le_of_lt h1 h2)).1]
      rw [Complex.exp_sub, hF_exp z (hsub hz), ← hzeta_eq_exp_Ψ z hzre, div_self (hball_nz z (hsub hz))]
    have hD : ∀ z ∈ Metric.ball (2 : ℂ) (1 / 2), deriv (fun w => F w - Ψ w) z = 0 := by
      intro z hz
      have hdiff_sub : DifferentiableAt ℂ (fun w => F w - Ψ w) z :=
        ((hF_diff.mono hsub).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).sub
          (hΨ_diff_half.differentiableAt (Metric.isOpen_ball.mem_nhds hz))
      have h1 : HasDerivAt (fun w => Complex.exp (F w - Ψ w))
          (Complex.exp (F z - Ψ z) * deriv (fun w => F w - Ψ w) z) z := hdiff_sub.hasDerivAt.cexp
      have h2 : HasDerivAt (fun w => Complex.exp (F w - Ψ w)) 0 z :=
        (hasDerivAt_const z (1 : ℂ)).congr_of_eventuallyEq
          (Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) fun w hw => hexp_eq w hw)
      have heq := h1.unique h2
      rw [hexp_eq z hz, one_mul] at heq
      exact heq
    intro z hz
    have h2mem : (2 : ℂ) ∈ Metric.ball (2 : ℂ) (1 / 2) := Metric.mem_ball_self (by norm_num)
    have h0 : F z - Ψ z = F 2 - Ψ 2 :=
      (convex_ball (2 : ℂ) (1 / 2)).is_const_of_fderivWithin_eq_zero
        (f := fun w => F w - Ψ w) ((hF_diff.mono hsub).sub hΨ_diff_half)
        (fun w hw => by
          have hdiff_sub : DifferentiableAt ℂ (fun u => F u - Ψ u) w :=
            ((hF_diff.mono hsub).differentiableAt (Metric.isOpen_ball.mem_nhds hw)).sub
              (hΨ_diff_half.differentiableAt (Metric.isOpen_ball.mem_nhds hw))
          rw [fderivWithin_of_isOpen Metric.isOpen_ball hw, hdiff_sub.hasDerivAt.hasFDerivAt.fderiv, hD w hw]
          simp)
        hz h2mem
    rw [hF_two, sub_self] at h0
    exact sub_eq_zero.mp h0
  have hgTilde_eq_g0 : gTilde =ᶠ[𝓝 (2 : ℂ)] gDeriv N 0 := by
    refine Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))) ?_
    intro z hz
    have hzre : 1 < z.re := by
      have h1 := Complex.abs_re_le_norm (z - 2)
      simp only [Complex.sub_re, Complex.re_ofNat] at h1
      have h2 : ‖z - 2‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      linarith [(abs_lt.mp (lt_of_le_of_lt h1 h2)).1]
    have hz0 : z ≠ 0 := fun h => by rw [h, zero_re] at hzre; linarith
    dsimp [gTilde]
    rw [hF_eq_Ψ z hz]
    dsimp [Ψ]; field_simp [hz0]; ring
  -- Taylor series at σ₁ = σ₀ - ε / 2 ∈ Metric.ball 2 R
  let σ₁ : ℝ := σ₀ - ε / 2
  have hσ₁_mem : (σ₁ : ℂ) ∈ Metric.ball (2 : ℂ) R := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : ((σ₁ : ℂ) - 2) = ((σ₁ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by dsimp [σ₁]; linarith)]
    dsimp [σ₁, R]; linarith
  have hTaylor := Complex.hasSum_taylorSeries_on_ball hgTilde_diff hσ₁_mem
  let c : ℕ → ℝ := fun k =>
    ((2 - σ₁) ^ k / (k ! : ℝ)) * ∫ t in Set.Ioi (N : ℝ), Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ)
  have hc_term : ∀ k : ℕ,
      (k ! : ℂ)⁻¹ • ((σ₁ : ℂ) - 2) ^ k • iteratedDeriv k gTilde 2 = (c k : ℂ) := by
    intro k
    rw [hgTilde_eq_g0.iteratedDeriv_eq k, iteratedDeriv_gDeriv_zero hN3 k 2 (by simp)]
    dsimp [gDeriv, c]
    have hsub : ((σ₁ : ℂ) - 2) ^ k = (-1 : ℂ) ^ k * ((2 - σ₁ : ℝ) : ℂ) ^ k := by
      rw [← mul_pow]; congr 1; push_cast; ring
    have hint_real : ∫ t in Set.Ioi (N : ℝ),
        (Hfun t : ℂ) * ((Real.log t : ℂ) ^ k) * (t : ℂ) ^ (-((2 : ℂ) + 1)) =
        ((∫ t in Set.Ioi (N : ℝ), Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ) : ℝ) : ℂ) := by
      have hof : ((∫ t in Set.Ioi (N : ℝ), Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ) : ℝ) : ℂ) =
          ∫ t in Set.Ioi (N : ℝ), ((Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ) : ℝ) : ℂ) :=
        (integral_ofReal (𝕜 := ℂ)).symm
      rw [hof]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have htpos : 0 < t := lt_trans (by positivity) ht
      have h3 : -((2 : ℂ) + 1) = ((-3 : ℝ) : ℂ) := by norm_num
      rw [h3, ← Complex.ofReal_cpow htpos.le]
      push_cast; ring
    have hneg1 : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; norm_num
    rw [hsub, hint_real]
    push_cast
    calc (k ! : ℂ)⁻¹ * ((-1 : ℂ) ^ k * (2 - (σ₁ : ℂ)) ^ k *
            ((-1 : ℂ) ^ k * ↑(∫ t in Set.Ioi (N : ℝ), Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ))))
        = ((k ! : ℂ)⁻¹ * (2 - (σ₁ : ℂ)) ^ k *
            ↑(∫ t in Set.Ioi (N : ℝ), Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ))) *
            ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) := by ring
      _ = (2 - (σ₁ : ℂ)) ^ k / (k ! : ℂ) *
            ↑(∫ t in Set.Ioi (N : ℝ), Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ)) := by
            rw [hneg1, mul_one, div_eq_mul_inv]; ring
  simp_rw [hc_term] at hTaylor
  have hc_summable : Summable c := by
    have hre := Complex.reCLM.summable hTaylor.summable
    refine hre.congr fun k => by simp
  have hc_nonneg : ∀ k : ℕ, 0 ≤ c k := fun k => by
    dsimp [c]
    refine mul_nonneg (div_nonneg (pow_nonneg (by dsimp [σ₁]; linarith) k) (by positivity)) ?_
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have ht1 : 1 < t := lt_of_le_of_lt (by exact_mod_cast hN1) ht
    exact mul_nonneg (mul_nonneg (hH_nonneg t ht) (pow_nonneg (Real.log_nonneg ht1.le) k))
      (Real.rpow_nonneg (zero_lt_one.trans ht1).le _)
  -- Tonelli (lintegral_tsum) gives integrability of H(t) * t^(-σ₁ - 1) on Ioi N
  let μ := volume.restrict (Set.Ioi (N : ℝ))
  let psi : ℕ → ℝ → ENNReal := fun k t =>
    ENNReal.ofReal (((2 - σ₁) ^ k / (k ! : ℝ)) * (Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ)))
  have hpsi_meas : ∀ k : ℕ, AEMeasurable (psi k) μ := fun k =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      (aemeasurable_const.mul ((((aestronglyMeasurable_Hfun hN3).aemeasurable).mul
        (Real.measurable_log.pow_const k).aemeasurable).mul (measurable_id.pow_const _).aemeasurable))
  have hpsi_lint : ∀ k : ℕ, ∫⁻ t, psi k t ∂μ = ENNReal.ofReal (c k) := by
    intro k
    have hint_k : IntegrableOn (fun t : ℝ =>
        ((2 - σ₁) ^ k / (k ! : ℝ)) * (Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ))) (Set.Ioi (N : ℝ)) := by
      have h1 := (integrableOn_Hfun_log_pow hN3 k (σ := 2) (by norm_num)).const_mul ((2 - σ₁) ^ k / (k ! : ℝ))
      refine IntegrableOn.congr_fun h1 (fun t ht => ?_) measurableSet_Ioi
      rw [abs_of_nonneg (hH_nonneg t ht), show -((2 : ℝ) + 1) = (-3 : ℝ) by norm_num]
    have hnn : 0 ≤ᵐ[μ] fun t : ℝ =>
        ((2 - σ₁) ^ k / (k ! : ℝ)) * (Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 < t := lt_of_le_of_lt (by exact_mod_cast hN1) ht
      exact mul_nonneg (div_nonneg (pow_nonneg (by dsimp [σ₁]; linarith) k) (by positivity))
        (mul_nonneg (mul_nonneg (hH_nonneg t ht) (pow_nonneg (Real.log_nonneg ht1.le) k))
          (Real.rpow_nonneg (zero_lt_one.trans ht1).le _))
    rw [← ofReal_integral_eq_lintegral_ofReal hint_k hnn, integral_const_mul]
  have htonelli : ∫⁻ t, ENNReal.ofReal (Hfun t * t ^ (-σ₁ - 1)) ∂μ =
      ENNReal.ofReal (∑' k : ℕ, c k) := by
    have hpt : ∀ᵐ t ∂μ, ENNReal.ofReal (Hfun t * t ^ (-σ₁ - 1)) = ∑' k : ℕ, psi k t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 < t := lt_of_le_of_lt (by exact_mod_cast hN1) ht
      have htpos : 0 < t := zero_lt_one.trans ht1
      have h2σ : 0 ≤ 2 - σ₁ := by dsimp [σ₁]; linarith
      have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1.le
      have hexp : HasSum (fun k : ℕ => ((2 - σ₁) * Real.log t) ^ k / (k ! : ℝ))
          (Real.exp ((2 - σ₁) * Real.log t)) := by
        simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp ((2 - σ₁) * Real.log t)
      have hmul : HasSum (fun k : ℕ =>
          ((2 - σ₁) ^ k / (k ! : ℝ)) * (Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ)))
          (Hfun t * t ^ (-σ₁ - 1)) := by
        have h1 := (hexp.mul_left (Hfun t)).mul_right (t ^ (-3 : ℝ))
        have hval : Hfun t * Real.exp ((2 - σ₁) * Real.log t) * t ^ (-3 : ℝ) =
            Hfun t * t ^ (-σ₁ - 1) := by
          rw [mul_comm (2 - σ₁), ← Real.rpow_def_of_pos htpos, mul_assoc, ← Real.rpow_add htpos]
          congr 2; ring
        rw [hval] at h1
        refine h1.congr_fun fun k => by rw [mul_pow]; ring
      rw [← hmul.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k =>
        mul_nonneg (div_nonneg (pow_nonneg h2σ k) (by positivity))
          (mul_nonneg (mul_nonneg (hH_nonneg t ht) (pow_nonneg hlog0 k))
            (Real.rpow_nonneg htpos.le _))) hmul.summable]
    rw [lintegral_congr_ae hpt, lintegral_tsum hpsi_meas]
    simp_rw [hpsi_lint]
    rw [ENNReal.ofReal_tsum_of_nonneg hc_nonneg hc_summable]
  have hInt_σ₁ : IntegrableOn (fun t : ℝ => Hfun t * t ^ (-σ₁ - 1)) (Set.Ioi (N : ℝ)) := by
    have hmeas : AEStronglyMeasurable (fun t : ℝ => Hfun t * t ^ (-σ₁ - 1)) μ :=
      (aestronglyMeasurable_Hfun hN3).mul (measurable_id.pow_const _).aestronglyMeasurable
    refine ⟨hmeas, ?_⟩
    rw [HasFiniteIntegral]
    have heq : ∀ᵐ t ∂μ, ‖Hfun t * t ^ (-σ₁ - 1)‖ₑ = ENNReal.ofReal (Hfun t * t ^ (-σ₁ - 1)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := lt_trans (by positivity) ht
      rw [Real.enorm_eq_ofReal (mul_nonneg (hH_nonneg t ht) (Real.rpow_nonneg htpos.le _))]
    rw [lintegral_congr_ae heq, htonelli]
    exact ENNReal.ofReal_lt_top
  -- Holomorphic extension of exp(Ψ(s)) to {s | σ₁ < s.re}
  have hg0_diff : DifferentiableOn ℂ (gDeriv N 0) {s : ℂ | σ₁ < s.re} :=
    differentiableOn_g0_of_integrableOn hN3 hH_nonneg hInt_σ₁
  have hΨ_diff : DifferentiableOn ℂ Ψ {s : ℂ | σ₁ < s.re} := fun s hs =>
    (differentiableWithinAt_id.mul (hg0_diff s hs)).sub (hEtot_diff s).differentiableWithinAt
  have hzeta_ext : ∀ s : ℂ, σ₁ < s.re → zetaReg s = Complex.exp (Ψ s) := by
    have hopen : IsOpen {z : ℂ | σ₁ < z.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
    have hconn : IsPreconnected {z : ℂ | σ₁ < z.re} := (convex_halfSpace_re_gt σ₁).isPreconnected
    have han1 : AnalyticOnNhd ℂ zetaReg {z : ℂ | σ₁ < z.re} :=
      zetaReg_differentiable.differentiableOn.analyticOnNhd hopen
    have han2 : AnalyticOnNhd ℂ (fun z => Complex.exp (Ψ z)) {z : ℂ | σ₁ < z.re} :=
      hΨ_diff.cexp.analyticOnNhd hopen
    have hev : zetaReg =ᶠ[𝓝 (2 : ℂ)] (fun z => Complex.exp (Ψ z)) :=
      Filter.eventually_of_mem ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re))
        fun z hz => hzeta_eq_exp_Ψ z hz
    exact fun s hs => han1.eqOn_of_preconnected_of_eventuallyEq han2 hconn
      (show σ₁ < (2 : ℂ).re by dsimp [σ₁]; linarith) hev hs
  -- Contradiction: σ₁ < σ₀ = sSup S, so there is σ ∈ S with σ₁ < σ
  have hlt_sup : σ₁ < σ₀ := by dsimp [σ₁]; linarith
  obtain ⟨σ, ⟨t, hzero⟩, hσ_gt⟩ := exists_lt_of_lt_csSup hS_nonempty hlt_sup
  have hne : zetaReg ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    rw [hzeta_ext ((σ : ℂ) + (t : ℂ) * I) (by simp [hσ_gt])]
    exact Complex.exp_ne_zero _
  exact hne hzero

end SkewesH2Proof

theorem OMA.solution : OMA.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R2.H2 :=
  SkewesH2Proof.skewes_R2_H2
