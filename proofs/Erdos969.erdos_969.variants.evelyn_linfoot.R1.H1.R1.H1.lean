import OMAReductions.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1_H1_R1
import Mathlib
/-
Step Erdos969.erdos_969.variants.evelyn_linfoot.R1.H1.R1.H1: hypothesis H1 of reduction
Erdos969.erdos_969.variants.evelyn_linfoot.R1.H1.R1 (credit: @marcusbuffett).
Credit: @Albin0903

The existence of a nonreal critical-strip zero is certified here by the Hardy Z sign change,
which is the content of the merged proof of Erdos969.erdos_969.variants.evelyn_linfoot.R1.H1.
That development (Hardy Z function, the order-4 Euler-Maclaurin expansion of zeta on the
critical strip, kernel-checked rational interval arithmetic, and the phase lemma) is adapted
from https://github.com/teal-sea/zeta-lab/tree/91848c0c0c387179a54784e3c3b7d4252414bb43/hunts/hardy_first_zero
and is reproduced below under the MIT license.

MIT License

Copyright (c) 2026 Thomas Lince

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the Software), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED AS IS, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
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
flagged that as provisional ("the goal is to eventually type this as
`ℝ → ℝ`"). This section meets that goal, purely additively: `hardyZReal` and
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
`ZetaLean/OracleDH.lean` names as "nothing here is kernel-checked about
`n^{-s}` itself".

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
  `n`; that is where the "multi-thousand-bit rationals" that defeated one-shot
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
  | 1 => lit ((79228162514192 * 1000000000000000 + 279999479885307) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((79228162514336 * 1000000000000000 + 395187608080645) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-127271725469605983 / (49517601571415 * 100000000000000 + 21099596496896) : ℚ) (127271725469605983 / (49517601571415 * 100000000000000 + 21099596496896) : ℚ) (by norm_num) (by norm_num)
  | 2 => lit (-(32652421908026 * 100000000000000 + 29529759108251) / (49517601571415 * 100000000000000 + 21099596496896) : ℚ) (-(52243875041974 * 1000000000000000 + 136066060479175) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      ((20226922343841 * 1000000000000000 + 466287171781983) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((10113461177369 * 1000000000000000 + 513466105374921) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (by norm_num) (by norm_num)
  | 3 => lit (-(28103415217178 * 100000000000000 + 17063327738697) / (49517601571415 * 100000000000000 + 21099596496896) : ℚ) (-(44965464340557 * 1000000000000000 + 772098093879997) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(83948949673975 * 100000000000000 + 69280129677265) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(20987237401187 * 100000000000000 + 38348761116551) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) (by norm_num) (by norm_num)
  | 4 => lit ((29286228761137 * 1000000000000000 + 521261720263453) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((14643114387228 * 1000000000000000 + 614781478272717) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ)
      (-(33344607855944 * 100000000000000 + 91179487753267) / (99035203142830 * 100000000000000 + 42199192993792) : ℚ) (-(13337843135710 * 1000000000000000 + 95928822016273) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (by norm_num) (by norm_num)
  | 5 => lit (-(64800209572726 * 100000000000000 + 38570240429575) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) (-(64800209549983 * 100000000000000 + 86017633865585) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ)
      ((15098240809493 * 100000000000000 + 85872639306687) / (49517601571415 * 100000000000000 + 21099596496896) : ℚ) ((24157185304296 * 1000000000000000 + 327605610911977) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 6 => lit ((31793908997839 * 1000000000000000 + 1620103519953) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((79484772504644 * 100000000000000 + 84688790543947) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ)
      (-(29719931484523 * 100000000000000 + 65699435427995) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (-(3714991433050 * 100000000000000 + 10589856994501) / (49517601571415 * 100000000000000 + 21099596496896) : ℚ) (by norm_num) (by norm_num)
  | 7 => lit (-(21317581505885 * 1000000000000000 + 999169984919827) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(3330872108976 * 100000000000000 + 8084135300649) / (12379400392853 * 100000000000000 + 80274899124224) : ℚ)
      (-(52576702209615 * 100000000000000 + 67324690999233) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) (-(6572087773566 * 100000000000000 + 58089723942751) / (24758800785707 * 100000000000000 + 60549798248448) : ℚ) (by norm_num) (by norm_num)
  | 8 => lit (-(12501350663933 * 1000000000000000 + 768525959970973) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(12501350647367 * 1000000000000000 + 668182453120639) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      ((25066989214751 * 1000000000000000 + 116014483957939) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((62667473078306 * 100000000000000 + 64909171501735) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) (by norm_num) (by norm_num)
  | 9 => lit ((12315183515039 * 1000000000000000 + 557416621989055) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((24630367039491 * 1000000000000000 + 270932123861487) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      ((95289436989877 * 100000000000000 + 75562627519059) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((47644718541977 * 100000000000000 + 83622467201843) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (by norm_num) (by norm_num)
  | 10 => lit ((10924652059946 * 1000000000000000 + 820146233864017) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((10924652072445 * 1000000000000000 + 832441435057193) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(11273443917600 * 1000000000000000 + 810623206292611) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (-(56367219556748 * 100000000000000 + 29751448827293) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) (by norm_num) (by norm_num)
  | 11 => lit (-(93229045873538 * 100000000000000 + 14025539704965) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (-(18645809162329 * 1000000000000000 + 602899033380971) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(14932495201536 * 1000000000000000 + 62751724150377) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(14932495189161 * 1000000000000000 + 650508252836507) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 12 => lit (-(19447736907777 * 1000000000000000 + 523150173768459) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(97238684483434 * 100000000000000 + 88631356348513) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ)
      ((60182501719829 * 100000000000000 + 64569207058761) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((12036500355059 * 1000000000000000 + 750506597104363) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 13 => lit ((25087516485080 * 100000000000000 + 56559818294835) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((12543758294880 * 100000000000000 + 90205946553427) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ)
      ((10915128773364 * 1000000000000000 + 434099717926463) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((21830257557196 * 1000000000000000 + 204194094237117) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 14 => lit ((3035337601811 * 100000000000000 + 70284091189521) / (12379400392853 * 100000000000000 + 80274899124224) : ℚ) ((97130803290564 * 100000000000000 + 59277575744473) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ)
      ((42127393649333 * 100000000000000 + 33364627369355) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((84254787363810 * 100000000000000 + 5853857128251) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 15 => lit ((17270445186724 * 1000000000000000 + 315440204817955) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((21588056492064 * 100000000000000 + 32200755960931) / (99035203142830 * 100000000000000 + 42199192993792) : ℚ)
      (-(10963811929913 * 1000000000000000 + 875974417200499) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(27409529807457 * 100000000000000 + 6466260405277) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) (by norm_num) (by norm_num)
  | 16 => lit ((4609817766534 * 100000000000000 + 2268759530055) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) ((18439271208900 * 100000000000000 + 14507609315521) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(19721024099737 * 1000000000000000 + 660944201543731) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(98605120427302 * 100000000000000 + 27019971535763) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (by norm_num) (by norm_num)
  | 17 => lit (-(66426518597122 * 100000000000000 + 5702896121405) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (-(13285303707094 * 1000000000000000 + 64112453783269) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(5423107298295 * 10000000000000 + 7590408883785) / (3094850098213 * 100000000000000 + 45068724781056) : ℚ) (-(69415773356550 * 100000000000000 + 42407421185873) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (by norm_num) (by norm_num)
  | 18 => lit (-(18674256420050 * 1000000000000000 + 32289326115507) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(18674256410499 * 1000000000000000 + 862777271236395) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      ((231973623821 * 10000000000000 + 6033248945605) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((231974101330 * 10000000000000 + 1743663507873) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (by norm_num) (by norm_num)
  | 19 => lit (-(13121816715496 * 1000000000000000 + 2643082806605) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(13121816703390 * 1000000000000000 + 5058668785595) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      ((12577428260108 * 1000000000000000 + 975104425183219) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((62887141361088 * 100000000000000 + 93541659383513) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (by norm_num) (by norm_num)
  | 20 => lit (-(14476166680379 * 100000000000000 + 12346476196885) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(9047604098680 * 10000000000000 + 4564216737939) / (49517601571415 * 100000000000000 + 21099596496896) : ℚ)
      ((22070890492103 * 100000000000000 + 56163794241097) / (99035203142830 * 100000000000000 + 42199192993792) : ℚ) ((17656712405932 * 1000000000000000 + 312486718751443) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 21 => lit ((98702856241931 * 100000000000000 + 37767395758969) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((98702856346343 * 100000000000000 + 53209000411841) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      ((35486535113039 * 100000000000000 + 24721552786975) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) ((14194614055654 * 1000000000000000 + 229392317933695) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 22 => lit ((16107501478739 * 1000000000000000 + 551929958114721) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((16107501486288 * 1000000000000000 + 473893584337673) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      ((50863741610693 * 100000000000000 + 64823645784621) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((50863741686161 * 100000000000000 + 45798856530437) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 23 => lit ((15669912468359 * 1000000000000000 + 363001750571505) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((15669912475649 * 1000000000000000 + 190390106859315) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(13079399334890 * 100000000000000 + 89836100573967) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) (-(52317597266643 * 100000000000000 + 43546124252063) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 24 => lit ((97511257849893 * 100000000000000 + 9219083929427) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((97511257940295 * 100000000000000 + 72229485176201) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(12901994093742 * 1000000000000000 + 868224954652983) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(12901994084699 * 1000000000000000 + 931033190401339) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 25 => lit ((2785661710373 * 100000000000000 + 84316234909885) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) ((3482077168343 * 10000000000000 + 6132663244451) / (24758800785707 * 100000000000000 + 60549798248448) : ℚ)
      (-(79032032077501 * 100000000000000 + 77628913217811) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (-(15806406405779 * 1000000000000000 + 592180519663477) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 26 => lit (-(72275541232994 * 100000000000000 + 20357640871811) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(18068885284912 * 100000000000000 + 60054164433191) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ)
      (-(13754615640329 * 1000000000000000 + 481701036763897) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(34386539077492 * 100000000000000 + 75415353056349) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) (by norm_num) (by norm_num)
  | 27 => lit (-(16211429384541 * 100000000000000 + 24551316786593) / (99035203142830 * 100000000000000 + 42199192993792) : ℚ) (-(12969143499546 * 1000000000000000 + 487233193728831) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(80178903900530 * 100000000000000 + 30419124342669) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(10022362977461 * 100000000000000 + 13818463152431) / (99035203142830 * 100000000000000 + 42199192993792) : ℚ) (by norm_num) (by norm_num)
  | 28 => lit (-(14960834337526 * 1000000000000000 + 44813516483213) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(14960834331241 * 1000000000000000 + 806210629187449) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(1490890795232 * 100000000000000 + 56750184705957) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) (-(2981781559045 * 100000000000000 + 24742948074475) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (by norm_num) (by norm_num)
  | 29 => lit (-(66045061165629 * 100000000000000 + 73888698852869) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (-(33022530565754 * 100000000000000 + 71610305984323) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ)
      ((64787174540889 * 100000000000000 + 44482358833461) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((16196793652288 * 100000000000000 + 22316810575425) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) (by norm_num) (by norm_num)
  | 30 => lit (-(42946269780799 * 100000000000000 + 17572585867539) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (-(85892539492399 * 100000000000000 + 17517701433811) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      ((29096975891874 * 100000000000000 + 46226696481233) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) ((11638790363672 * 1000000000000000 + 308667189496331) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | _ => ComplexInterval.exact 0 0

set_option maxRecDepth 100000 in
theorem tA_eq_1 :
    dirichletTermBox2 40 24 96 1 8 1 (ptBox (1413 / 100 : ℚ)) = tA 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_1 :
    (tA 1).contains (((1 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_1]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_2 :
    dirichletTermBox2 40 24 96 2 8 2 (ptBox (1413 / 100 : ℚ)) = tA 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_2 :
    (tA 2).contains (((2 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_2]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_3 :
    dirichletTermBox2 40 24 96 2 8 3 (ptBox (1413 / 100 : ℚ)) = tA 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_3 :
    (tA 3).contains (((3 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_3]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_4 :
    dirichletTermBox2 40 24 96 3 8 4 (ptBox (1413 / 100 : ℚ)) = tA 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_4 :
    (tA 4).contains (((4 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_4]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_5 :
    dirichletTermBox2 40 24 96 3 8 5 (ptBox (1413 / 100 : ℚ)) = tA 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_5 :
    (tA 5).contains (((5 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_5]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_6 :
    dirichletTermBox2 40 24 96 3 8 6 (ptBox (1413 / 100 : ℚ)) = tA 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_6 :
    (tA 6).contains (((6 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_6]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_7 :
    dirichletTermBox2 40 24 96 3 8 7 (ptBox (1413 / 100 : ℚ)) = tA 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_7 :
    (tA 7).contains (((7 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_7]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_8 :
    dirichletTermBox2 40 24 96 4 8 8 (ptBox (1413 / 100 : ℚ)) = tA 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_8 :
    (tA 8).contains (((8 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_8]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_9 :
    dirichletTermBox2 40 24 96 4 8 9 (ptBox (1413 / 100 : ℚ)) = tA 9 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_9 :
    (tA 9).contains (((9 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_9]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_10 :
    dirichletTermBox2 40 24 96 4 8 10 (ptBox (1413 / 100 : ℚ)) = tA 10 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_10 :
    (tA 10).contains (((10 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_10]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_11 :
    dirichletTermBox2 40 24 96 4 8 11 (ptBox (1413 / 100 : ℚ)) = tA 11 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_11 :
    (tA 11).contains (((11 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_11]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_12 :
    dirichletTermBox2 40 24 96 4 8 12 (ptBox (1413 / 100 : ℚ)) = tA 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_12 :
    (tA 12).contains (((12 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_12]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_13 :
    dirichletTermBox2 40 24 96 4 8 13 (ptBox (1413 / 100 : ℚ)) = tA 13 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_13 :
    (tA 13).contains (((13 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_13]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_14 :
    dirichletTermBox2 40 24 96 4 8 14 (ptBox (1413 / 100 : ℚ)) = tA 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_14 :
    (tA 14).contains (((14 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_14]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_15 :
    dirichletTermBox2 40 24 96 4 8 15 (ptBox (1413 / 100 : ℚ)) = tA 15 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_15 :
    (tA 15).contains (((15 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_15]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_16 :
    dirichletTermBox2 40 24 96 5 8 16 (ptBox (1413 / 100 : ℚ)) = tA 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_16 :
    (tA 16).contains (((16 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_16]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_17 :
    dirichletTermBox2 40 24 96 5 8 17 (ptBox (1413 / 100 : ℚ)) = tA 17 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_17 :
    (tA 17).contains (((17 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_17]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_18 :
    dirichletTermBox2 40 24 96 5 8 18 (ptBox (1413 / 100 : ℚ)) = tA 18 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_18 :
    (tA 18).contains (((18 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_18]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_19 :
    dirichletTermBox2 40 24 96 5 8 19 (ptBox (1413 / 100 : ℚ)) = tA 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_19 :
    (tA 19).contains (((19 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_19]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_20 :
    dirichletTermBox2 40 24 96 5 8 20 (ptBox (1413 / 100 : ℚ)) = tA 20 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_20 :
    (tA 20).contains (((20 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_20]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_21 :
    dirichletTermBox2 40 24 96 5 8 21 (ptBox (1413 / 100 : ℚ)) = tA 21 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_21 :
    (tA 21).contains (((21 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_21]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_22 :
    dirichletTermBox2 40 24 96 5 8 22 (ptBox (1413 / 100 : ℚ)) = tA 22 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_22 :
    (tA 22).contains (((22 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_22]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_23 :
    dirichletTermBox2 40 24 96 5 8 23 (ptBox (1413 / 100 : ℚ)) = tA 23 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_23 :
    (tA 23).contains (((23 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_23]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_24 :
    dirichletTermBox2 40 24 96 5 8 24 (ptBox (1413 / 100 : ℚ)) = tA 24 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_24 :
    (tA 24).contains (((24 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_24]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_25 :
    dirichletTermBox2 40 24 96 5 8 25 (ptBox (1413 / 100 : ℚ)) = tA 25 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_25 :
    (tA 25).contains (((25 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_25]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_26 :
    dirichletTermBox2 40 24 96 5 8 26 (ptBox (1413 / 100 : ℚ)) = tA 26 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_26 :
    (tA 26).contains (((26 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_26]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_27 :
    dirichletTermBox2 40 24 96 5 8 27 (ptBox (1413 / 100 : ℚ)) = tA 27 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_27 :
    (tA 27).contains (((27 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_27]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_28 :
    dirichletTermBox2 40 24 96 5 8 28 (ptBox (1413 / 100 : ℚ)) = tA 28 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_28 :
    (tA 28).contains (((28 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_28]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_29 :
    dirichletTermBox2 40 24 96 5 8 29 (ptBox (1413 / 100 : ℚ)) = tA 29 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_29 :
    (tA 29).contains (((29 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_29]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_eq_30 :
    dirichletTermBox2 40 24 96 5 8 30 (ptBox (1413 / 100 : ℚ)) = tA 30 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tA_mem_30 :
    (tA 30).contains (((30 : ℕ) : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_30]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tA_mem : ∀ m < 31,
    (tA m).contains ((m : ℂ) ^ (-sOf (((1413 / 100 : ℚ) : ℚ) : ℝ))) := by
  intro m hm
  interval_cases m
  · rw [Nat.cast_zero, zero_cpow (neg_ne_zero.mpr (sOf_ne_zero _))]
    exact contains_zero
  · exact tA_mem_1
  · exact tA_mem_2
  · exact tA_mem_3
  · exact tA_mem_4
  · exact tA_mem_5
  · exact tA_mem_6
  · exact tA_mem_7
  · exact tA_mem_8
  · exact tA_mem_9
  · exact tA_mem_10
  · exact tA_mem_11
  · exact tA_mem_12
  · exact tA_mem_13
  · exact tA_mem_14
  · exact tA_mem_15
  · exact tA_mem_16
  · exact tA_mem_17
  · exact tA_mem_18
  · exact tA_mem_19
  · exact tA_mem_20
  · exact tA_mem_21
  · exact tA_mem_22
  · exact tA_mem_23
  · exact tA_mem_24
  · exact tA_mem_25
  · exact tA_mem_26
  · exact tA_mem_27
  · exact tA_mem_28
  · exact tA_mem_29
  · exact tA_mem_30

/- `c_30(s)` at `s = 1/2 + i · 1413/100`, exactly. -/
set_option maxRecDepth 100000 in
def cA : ComplexInterval := ComplexInterval.exact (613663909 / 1439329680 : ℚ) (-16642146167 / 7996276000 : ℚ)

/- The remainder bound at `t = 1413/100`, rounded up. -/
set_option maxRecDepth 100000 in
def epsA : ℚ := (1091 / 5000000 : ℚ)

/- Term boxes `m^(-s)` at `s = 1/2 + i · 707/50`, `1 ≤ m ≤ 30`. -/
set_option maxRecDepth 100000 in
def tB : ℕ → ComplexInterval
  | 1 => lit ((19807040628548 * 1000000000000000 + 69999869962033) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) ((19807040628584 * 1000000000000000 + 98796902029455) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ)
      (-509447189848613879 / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) (509447189848613879 / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) (by norm_num) (by norm_num)
  | 2 => lit (-(52102418802217 * 1000000000000000 + 544929411817195) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(52102418791318 * 1000000000000000 + 782370261627953) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      ((20588560488644 * 1000000000000000 + 666406399026943) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((20588560499573 * 1000000000000000 + 437056816994415) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 3 => lit (-(45054976316221 * 1000000000000000 + 652535070984349) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(11263744077328 * 1000000000000000 + 714113993511753) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ)
      (-(39502010910650 * 100000000000000 + 87846429853093) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (-(79004021752278 * 100000000000000 + 13652542631255) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 4 => lit ((28913622984895 * 1000000000000000 + 495417012846499) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((28913622998293 * 1000000000000000 + 848857028606879) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(33848879221426 * 100000000000000 + 83280078172095) / (99035203142830 * 100000000000000 + 42199192993792) : ℚ) (-(13539551681863 * 1000000000000000 + 565463661458901) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (by norm_num) (by norm_num)
  | 5 => lit (-(12763974380104 * 1000000000000000 + 333091560810239) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (-(63819871877735 * 100000000000000 + 43870169723837) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ)
      ((24571206302948 * 1000000000000000 + 865428536800967) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((24571206312072 * 1000000000000000 + 504565518433227) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 6 => lit ((31682309334085 * 1000000000000000 + 611673573318869) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((31682309338167 * 1000000000000000 + 890308350463209) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(32563360438196 * 100000000000000 + 67195975183165) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (-(65126720835510 * 100000000000000 + 5607389813323) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 7 => lit (-(21722757938796 * 1000000000000000 + 638947908139315) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(21722757930357 * 1000000000000000 + 543254267192679) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(20611904502752 * 1000000000000000 + 908545577289797) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(51529761235799 * 100000000000000 + 20220465894481) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) (by norm_num) (by norm_num)
  | 8 => lit (-(59887160494165 * 100000000000000 + 38909879488001) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (-(292417775444 * 10000000000000 + 6455226733853) / (1934281311383 * 10000000000000 + 4066795298816) : ℚ)
      ((25321509374824 * 1000000000000000 + 247487262381591) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((25321509391449 * 1000000000000000 + 899420848355207) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 9 => lit ((12416888598394 * 1000000000000000 + 929724876455061) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((12416888603051 * 1000000000000000 + 538850186663183) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ)
      ((44927513341389 * 100000000000000 + 60756849434427) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((22463756693967 * 100000000000000 + 35794218237111) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) (by norm_num) (by norm_num)
  | 10 => lit ((10402640714621 * 1000000000000000 + 139047655451441) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((10402640727204 * 1000000000000000 + 111561923502501) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(22792438216592 * 1000000000000000 + 829794968686439) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(11396219102003 * 1000000000000000 + 354625558699801) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (by norm_num) (by norm_num)
  | 11 => lit (-(18998480136355 * 1000000000000000 + 880535815718399) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(94992400620173 * 100000000000000 + 13842229928017) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ)
      (-(14481138257363 * 1000000000000000 + 592472740285749) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(14481138245045 * 1000000000000000 + 928646571634397) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 12 => lit (-(95713339712740 * 100000000000000 + 56651496445741) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (-(19142667931397 * 1000000000000000 + 86712552232971) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      ((12515992785131 * 1000000000000000 + 429803592227529) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((12515992796285 * 1000000000000000 + 793165851276487) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 13 => lit ((15339000502812 * 100000000000000 + 23339636314663) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((30678001109782 * 100000000000000 + 45456195779985) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      ((21758735761288 * 1000000000000000 + 913011656695103) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((10879367885851 * 1000000000000000 + 872993230130895) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (by norm_num) (by norm_num)
  | 14 => lit ((98208618271368 * 100000000000000 + 40558059829643) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((98208618303427 * 100000000000000 + 96529043916381) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ)
      ((79099368760459 * 100000000000000 + 22188969444617) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((79099368824542 * 100000000000000 + 79382381029425) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 15 => lit ((84836218296929 * 100000000000000 + 95201277964159) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((84836218332121 * 100000000000000 + 80685937140323) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ)
      (-(57137135820299 * 100000000000000 + 62601006094325) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (-(57137135785088 * 100000000000000 + 6450375522777) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (by norm_num) (by norm_num)
  | 16 => lit ((6482527886829 * 100000000000000 + 80629325666073) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((6482527958673 * 100000000000000 + 62252736296913) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ)
      (-(19764562530320 * 1000000000000000 + 137554833580861) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(19764562515950 * 1000000000000000 + 812746370049819) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 17 => lit (-(13673258724548 * 1000000000000000 + 789256947949009) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(68366293561223 * 100000000000000 + 36767097860843) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ)
      (-(67506161707295 * 100000000000000 + 48768231733105) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (-(13501232329158 * 1000000000000000 + 283138096275001) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 18 => lit (-(18666322414396 * 1000000000000000 + 136147158896733) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(18666322404692 * 1000000000000000 + 843922810124981) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      ((2721589084717 * 100000000000000 + 28063839736421) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((5443178266469 * 100000000000000 + 68826909719155) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 19 => lit (-(15932309763650 * 100000000000000 + 15409721345515) / (99035203142830 * 100000000000000 + 42199192993792) : ℚ) (-(12745847798742 * 1000000000000000 + 496691553992307) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      ((64791422874664 * 100000000000000 + 24986139725927) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((64791422935566 * 100000000000000 + 39294200055881) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (by norm_num) (by norm_num)
  | 20 => lit (-(9180984224340 * 100000000000000 + 97187552906877) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(9180984102062 * 100000000000000 + 75360187514415) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      ((17692150289068 * 1000000000000000 + 233650254562001) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((17692150301296 * 1000000000000000 + 325500845800765) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 21 => lit ((10297802986743 * 1000000000000000 + 819629813747129) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((10297802997088 * 1000000000000000 + 473325891984835) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      ((13887579337057 * 1000000000000000 + 855464873473665) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((69437896736998 * 100000000000000 + 70444561206687) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (by norm_num) (by norm_num)
  | 22 => lit ((16257004049898 * 1000000000000000 + 416571997203825) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) ((81285020286548 * 100000000000000 + 62829492606717) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ)
      ((22930670139079 * 100000000000000 + 89318897706029) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((45861340352253 * 100000000000000 + 1759076074693) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 23 => lit ((77490978270352 * 100000000000000 + 40068581143253) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((15498195661485 * 1000000000000000 + 835396075869609) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(57204368846820 * 100000000000000 + 49260137957953) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(28602184386321 * 100000000000000 + 82881705038353) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (by norm_num) (by norm_num)
  | 24 => lit ((11670298211979 * 100000000000000 + 64808984575009) / (99035203142830 * 100000000000000 + 42199192993792) : ℚ) ((93362385787055 * 100000000000000 + 69731967353105) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(13205322981596 * 1000000000000000 + 661566291477101) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(13205322972472 * 1000000000000000 + 211215672897773) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 25 => lit ((3024933707752 * 100000000000000 + 99921552278135) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((6049867512941 * 100000000000000 + 26187280806715) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(15834079089307 * 1000000000000000 + 39768670138943) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(15834079079563 * 1000000000000000 + 326575189763961) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 26 => lit (-(38358888719548 * 100000000000000 + 40377443492203) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (-(76717777346116 * 100000000000000 + 68975038908757) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(13511876859547 * 1000000000000000 + 694243148558887) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(2111230757851 * 100000000000000 + 84027314799233) / (12379400392853 * 100000000000000 + 80274899124224) : ℚ) (by norm_num) (by norm_num)
  | 27 => lit (-(13226309000949 * 1000000000000000 + 170124124903827) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(13226308992948 * 1000000000000000 + 677144182405039) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(75861716192487 * 100000000000000 + 5895802188555) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(75861716112505 * 100000000000000 + 44906760376943) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 28 => lit (-(14972397294536 * 1000000000000000 + 110035786693863) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(14972397288371 * 1000000000000000 + 110704899637901) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ)
      (-(9759191942542 * 10000000000000 + 8102254212389) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(9759191326047 * 10000000000000 + 2389261558607) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (by norm_num) (by norm_num)
  | 29 => lit (-(64917039718224 * 100000000000000 + 42552708985645) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (-(64917039683902 * 100000000000000 + 5539153607123) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ)
      ((17299368158508 * 100000000000000 + 84553976292307) / (19807040628566 * 1000000000000000 + 84398385987584) : ℚ) ((2162421021959 * 100000000000000 + 49910003092943) / (24758800785707 * 100000000000000 + 60549798248448) : ℚ) (by norm_num) (by norm_num)
  | 30 => lit (-(81885044339113 * 100000000000000 + 91641142113715) / (79228162514264 * 1000000000000000 + 337593543950336) : ℚ) (-(10235630533743 * 100000000000000 + 73511520145439) / (99035203142830 * 100000000000000 + 42199192993792) : ℚ)
      ((59620701023817 * 100000000000000 + 63385956261599) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) ((59620701058412 * 100000000000000 + 39484579370171) / (39614081257132 * 1000000000000000 + 168796771975168) : ℚ) (by norm_num) (by norm_num)
  | _ => ComplexInterval.exact 0 0

set_option maxRecDepth 100000 in
theorem tB_eq_1 :
    dirichletTermBox2 40 24 96 1 8 1 (ptBox (707 / 50 : ℚ)) = tB 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_1 :
    (tB 1).contains (((1 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_1]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_2 :
    dirichletTermBox2 40 24 96 2 8 2 (ptBox (707 / 50 : ℚ)) = tB 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_2 :
    (tB 2).contains (((2 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_2]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_3 :
    dirichletTermBox2 40 24 96 2 8 3 (ptBox (707 / 50 : ℚ)) = tB 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_3 :
    (tB 3).contains (((3 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_3]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_4 :
    dirichletTermBox2 40 24 96 3 8 4 (ptBox (707 / 50 : ℚ)) = tB 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_4 :
    (tB 4).contains (((4 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_4]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_5 :
    dirichletTermBox2 40 24 96 3 8 5 (ptBox (707 / 50 : ℚ)) = tB 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_5 :
    (tB 5).contains (((5 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_5]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_6 :
    dirichletTermBox2 40 24 96 3 8 6 (ptBox (707 / 50 : ℚ)) = tB 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_6 :
    (tB 6).contains (((6 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_6]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_7 :
    dirichletTermBox2 40 24 96 3 8 7 (ptBox (707 / 50 : ℚ)) = tB 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_7 :
    (tB 7).contains (((7 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_7]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_8 :
    dirichletTermBox2 40 24 96 4 8 8 (ptBox (707 / 50 : ℚ)) = tB 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_8 :
    (tB 8).contains (((8 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_8]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_9 :
    dirichletTermBox2 40 24 96 4 8 9 (ptBox (707 / 50 : ℚ)) = tB 9 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_9 :
    (tB 9).contains (((9 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_9]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_10 :
    dirichletTermBox2 40 24 96 4 8 10 (ptBox (707 / 50 : ℚ)) = tB 10 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_10 :
    (tB 10).contains (((10 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_10]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_11 :
    dirichletTermBox2 40 24 96 4 8 11 (ptBox (707 / 50 : ℚ)) = tB 11 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_11 :
    (tB 11).contains (((11 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_11]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_12 :
    dirichletTermBox2 40 24 96 4 8 12 (ptBox (707 / 50 : ℚ)) = tB 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_12 :
    (tB 12).contains (((12 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_12]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_13 :
    dirichletTermBox2 40 24 96 4 8 13 (ptBox (707 / 50 : ℚ)) = tB 13 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_13 :
    (tB 13).contains (((13 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_13]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_14 :
    dirichletTermBox2 40 24 96 4 8 14 (ptBox (707 / 50 : ℚ)) = tB 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_14 :
    (tB 14).contains (((14 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_14]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_15 :
    dirichletTermBox2 40 24 96 4 8 15 (ptBox (707 / 50 : ℚ)) = tB 15 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_15 :
    (tB 15).contains (((15 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_15]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_16 :
    dirichletTermBox2 40 24 96 5 8 16 (ptBox (707 / 50 : ℚ)) = tB 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_16 :
    (tB 16).contains (((16 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_16]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_17 :
    dirichletTermBox2 40 24 96 5 8 17 (ptBox (707 / 50 : ℚ)) = tB 17 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_17 :
    (tB 17).contains (((17 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_17]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_18 :
    dirichletTermBox2 40 24 96 5 8 18 (ptBox (707 / 50 : ℚ)) = tB 18 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_18 :
    (tB 18).contains (((18 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_18]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_19 :
    dirichletTermBox2 40 24 96 5 8 19 (ptBox (707 / 50 : ℚ)) = tB 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_19 :
    (tB 19).contains (((19 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_19]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_20 :
    dirichletTermBox2 40 24 96 5 8 20 (ptBox (707 / 50 : ℚ)) = tB 20 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_20 :
    (tB 20).contains (((20 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_20]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_21 :
    dirichletTermBox2 40 24 96 5 8 21 (ptBox (707 / 50 : ℚ)) = tB 21 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_21 :
    (tB 21).contains (((21 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_21]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_22 :
    dirichletTermBox2 40 24 96 5 8 22 (ptBox (707 / 50 : ℚ)) = tB 22 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_22 :
    (tB 22).contains (((22 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_22]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_23 :
    dirichletTermBox2 40 24 96 5 8 23 (ptBox (707 / 50 : ℚ)) = tB 23 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_23 :
    (tB 23).contains (((23 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_23]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_24 :
    dirichletTermBox2 40 24 96 5 8 24 (ptBox (707 / 50 : ℚ)) = tB 24 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_24 :
    (tB 24).contains (((24 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_24]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_25 :
    dirichletTermBox2 40 24 96 5 8 25 (ptBox (707 / 50 : ℚ)) = tB 25 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_25 :
    (tB 25).contains (((25 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_25]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_26 :
    dirichletTermBox2 40 24 96 5 8 26 (ptBox (707 / 50 : ℚ)) = tB 26 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_26 :
    (tB 26).contains (((26 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_26]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_27 :
    dirichletTermBox2 40 24 96 5 8 27 (ptBox (707 / 50 : ℚ)) = tB 27 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_27 :
    (tB 27).contains (((27 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_27]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_28 :
    dirichletTermBox2 40 24 96 5 8 28 (ptBox (707 / 50 : ℚ)) = tB 28 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_28 :
    (tB 28).contains (((28 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_28]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_29 :
    dirichletTermBox2 40 24 96 5 8 29 (ptBox (707 / 50 : ℚ)) = tB 29 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_29 :
    (tB 29).contains (((29 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_29]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_eq_30 :
    dirichletTermBox2 40 24 96 5 8 30 (ptBox (707 / 50 : ℚ)) = tB 30 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tB_mem_30 :
    (tB 30).contains (((30 : ℕ) : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_30]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tB_mem : ∀ m < 31,
    (tB m).contains ((m : ℂ) ^ (-sOf (((707 / 50 : ℚ) : ℚ) : ℝ))) := by
  intro m hm
  interval_cases m
  · rw [Nat.cast_zero, zero_cpow (neg_ne_zero.mpr (sOf_ne_zero _))]
    exact contains_zero
  · exact tB_mem_1
  · exact tB_mem_2
  · exact tB_mem_3
  · exact tB_mem_4
  · exact tB_mem_5
  · exact tB_mem_6
  · exact tB_mem_7
  · exact tB_mem_8
  · exact tB_mem_9
  · exact tB_mem_10
  · exact tB_mem_11
  · exact tB_mem_12
  · exact tB_mem_13
  · exact tB_mem_14
  · exact tB_mem_15
  · exact tB_mem_16
  · exact tB_mem_17
  · exact tB_mem_18
  · exact tB_mem_19
  · exact tB_mem_20
  · exact tB_mem_21
  · exact tB_mem_22
  · exact tB_mem_23
  · exact tB_mem_24
  · exact tB_mem_25
  · exact tB_mem_26
  · exact tB_mem_27
  · exact tB_mem_28
  · exact tB_mem_29
  · exact tB_mem_30

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

end

open Complex in
theorem OMA.solution : OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1_H1_R1.H1 := by
  obtain ⟨t, ht, hzero⟩ := HardyFirstZero.first_zero_on_line
  have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1413 / 100) ht.1
  let a : ℂ := 1 / 2 + t * I
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · norm_num [a]
  · norm_num [a]
  · rw [show a.im = t by norm_num [a]]
    exact ht0.ne'
  · simpa [a] using hzero
