import OMAReductions.R_PowerfulNumbersDensity_error_term_improvement_R1
import Mathlib

/-! # The truncated powerful-number convolution at a variable cutoff

This adapts the short-divisor and Möbius-tail estimates of Sky (ChironTheCentaur),
rh-lab-powerful-numbers at 467faf0ee95603cd28ff806134bd3e0de330747d, and the
Bateman–Grosswald port by senamakel. The final proof keeps the exponent t free
and bounds the lattice error and the two Dirichlet tails separately.
-/

/-
Ported from an existing public Lean proof; the mathematics and the Lean proof are the original author's.
Original: https://github.com/ChironTheCentaur/rh-lab-powerful-numbers/blob/467faf0ee95603cd28ff806134bd3e0de330747d/PowerfulFC/BatemanGrosswald.lean  (theorem PowerfulNumbersDensity.asymptotic_bateman_grosswald)
Original author: Sky (GitHub: ChironTheCentaur)   Licence: Apache-2.0 (LICENSE; Zeta23 parts: LICENSE.zeta23)
Submitted to lefttosolve.com by @senamakel; ported to Lean v4.33.1 / formal-conjectures 9097e2f.
Changes: the import closure of BatemanGrosswald.lean flattened into one file (each module in its own section) and
pruned to the declarations the result depends on; the copies of formal-conjectures' Q, A, B, Nat.Full and
Nat.Powerful dropped in favour of the imported ones; the scoped LSeries notation (unused) no longer opened.
No proof needed changing for the pin.

NOTICE of the original package, retained as Apache-2.0 requires:

  PowerfulNumbers (standalone package)
  Copyright 2026 Sky (GitHub: ChironTheCentaur)

  The original work in this package (PowerfulFC/, LeanClassics/, PowerfulNumbers.lean, check.py, AxiomAudit.lean,
  PlantedSorry.lean, controls/) is licensed under the Apache License, Version 2.0 (see LICENSE).

  The statements of asymptotic_erdos_szekeres, asymptotic_bateman_grosswald and the conclusion of
  error_term_improvement, and the definitions Q, A, B and Nat.Full / Nat.Powerful are copied verbatim from
  google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/PowerfulNumbersDensity.lean and
  FormalConjecturesForMathlib/Data/Nat/Full.lean, commit ea8e3e19), Copyright The Formal Conjectures Authors,
  licensed under the Apache License, Version 2.0.

  Zeta23/ is a subset of zeta-23-lean, Copyright 2026 Anthropic, PBC, licensed under the Apache License,
  Version 2.0 (LICENSE.zeta23, NOTICE.zeta23), as ported to Lean v4.35.0 / Mathlib 56a005855ea1.

The LeanClassics.DHEMZeta* modules below carry their own notice (ported from DrMurphyIsIn/Arda, Apache-2.0).
-/

-- ===== LeanClassics.DHEMZeta =====
section
/-
Ported from DrMurphyIsIn/Arda, telperion/examples/zeta_reflection/lean/EMZeta.lean at commit
6fa9a1d29c877779fd3657265a20924c8032c026 (Lean 4.32 / Mathlib v4.32.0) to Lean 4.35 / Mathlib 56a00585 for rh-lab.

Copyright of the original: the Arda authors. Licensed under the Apache License, Version 2.0
(the "License"); you may not use this file except in compliance with the License. You may obtain
a copy of the License at http://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable
law or agreed to in writing, software distributed under the License is distributed on an "AS IS"
BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for
the specific language governing permissions and limitations under the License.

Changes from upstream: namespace ZetaReflection -> LeanClassics.DavenportHeilbronn.EM, imports
renamed to the LeanClassics module names, and API-drift fixes listed in DHEMZeta_DRIFT.md.
-/
/-  EMZeta.lean -- A2 Theorem 1: the Euler-Maclaurin representation of ζ with explicit
    remainder.

    Euler-Maclaurin summation is ABSENT from Mathlib (confirmed: `find Mathlib -iname
    '*maclaurin*'` is empty; `Mathlib/Analysis/SumIntegralComparisons.lean` has only crude
    monotone sum/integral bounds).  This file builds it bottom-up and is upstreamable.

    Architecture (proven bottom-up; only fully-proven lemmas live here, WIP in EMZetaWip.lean):

      A.  Periodized ("saw") Bernoulli  `sawBernoulli k x := bernoulliFun k (Int.fract x)`.
          Reuses `Mathlib.NumberTheory.ZetaValues.bernoulliFun` and its derivative/integral
          API (`hasDerivAt_bernoulliFun`, `integral_bernoulliFun`, `contDiff_bernoulliFun`).

      B.  One-step Euler-Maclaurin over `[m, m+1]` for a C^1 function f:
              ∫ f = (f m + f (m+1))/2 - ∫ B̃₁(x) f'(x) dx
          via integration by parts (`intervalIntegral.integral_mul_deriv_eq_deriv_mul`)
          with the saw-1 antiderivative.  This is `em_unit_step`.

      C.  Summed over `m = 0 .. N-1`: the classical first-order Euler-Maclaurin formula
              ∑_{n=1}^{N} f n = ∫_0^N f + (f N - f 0)/2 + ∫_0^N B̃₁(x) f'(x) dx
          (`euler_maclaurin_one`).  Telescoping of the integral (`intervalIntegral.sum_integral_
          adjacent_intervals`) + telescoping of the trapezoid endpoints.

      D.  Specialisation to `f x = x^{-s}` on `[1, N]` (real `s`) and the tail limit `N → ∞`
          giving the K=1 Euler-Maclaurin representation of `ζ` for real `s > 1`
          (`em_zeta_real_K1`), matching the Mathlib fractional-part representation route
          used in `Mathlib.NumberTheory.Harmonic.ZetaAsymp`.

    NOT YET in this file (see EMZetaWip.lean, never imported by a guard, no placeholder proofs here):
      - the general order-K induction (periodized `bernoulliFun k` for k ≥ 2);
      - the complex interval-σ form valid `Re s > 1 - 2K` by analytic continuation
        (`AnalyticOnNhd.eqOn`);
      - the explicit remainder BOUND `|R_K| ≤ (|B_{2K}|/(2K)!) ∫ |f^{(2K)}|`.

    conjecture1_proved = False.  This is NOT a proof of RH; it is a classical analysis lemma.
-/

open MeasureTheory intervalIntegral Set Filter Topology
open scoped Real

namespace LeanClassics.DavenportHeilbronn.EM

/- ## A. The periodized ("saw") Bernoulli functions -/

/-- The periodized Bernoulli function `B̃ₖ(x) = Bₖ({x})` on `ℝ`, where `{x} = Int.fract x`.
    For `k = 1` this is the classical sawtooth `{x} - 1/2` (away from integers).  We build EM
    on this `ℝ → ℝ` form rather than Mathlib's `AddCircle`-valued `periodizedBernoulli`, since
    the finite-sum induction wants a plain real function with `bernoulliFun`'s derivative and
    integral API directly available. -/
noncomputable def sawBernoulli (k : ℕ) (x : ℝ) : ℝ := bernoulliFun k (Int.fract x)

/-- The saw is measurable: `bernoulliFun k` is continuous and `Int.fract` is measurable. -/
lemma sawBernoulli_measurable (k : ℕ) : Measurable (sawBernoulli k) :=
  (contDiff_bernoulliFun (k := k)).continuous.measurable.comp measurable_fract

/-- The order-1 saw is bounded by `1/2` (it is `{x} − 1/2` with `{x} ∈ [0, 1)`). -/
lemma abs_sawBernoulli_one_le (x : ℝ) : |sawBernoulli 1 x| ≤ 1 / 2 := by
  rw [sawBernoulli, bernoulliFun_one, abs_le]
  have h0 : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  constructor <;> linarith

/-- On the half-open unit cell starting at an integer, the saw agrees with the raw Bernoulli
    function shifted to that cell. -/
lemma sawBernoulli_eq_on_Ico (k : ℕ) {m : ℤ} {x : ℝ} (hx : x ∈ Ico (m : ℝ) (m + 1)) :
    sawBernoulli k x = bernoulliFun k (x - m) := by
  have hfloor : ⌊x⌋ = m := by
    rw [Int.floor_eq_iff]
    exact ⟨hx.1, by push_cast; linarith [hx.2]⟩
  have hfract : Int.fract x = x - m := by
    rw [Int.fract, hfloor]
  rw [sawBernoulli, hfract]

/-- The order-1 saw on the cell `[m, m+1)` is the affine sawtooth `x - m - 1/2`. -/
lemma sawBernoulli_one_eq_on_Ico {m : ℤ} {x : ℝ} (hx : x ∈ Ico (m : ℝ) (m + 1)) :
    sawBernoulli 1 x = x - m - 1 / 2 := by
  rw [sawBernoulli_eq_on_Ico 1 hx, bernoulliFun_one]

/- ## B. One-step Euler-Maclaurin over a unit cell

    For a `C¹` function `f` on `[m, m+1]` (real, integer `m`), integration by parts with the
    order-1 antiderivative `w x = x - m - 1/2` of the constant `1` (equal to `sawBernoulli 1`
    on the cell) yields the trapezoidal Euler-Maclaurin step
        ∫_m^{m+1} f = (f m + f(m+1))/2 − ∫_m^{m+1} (sawBernoulli 1 x) · f'(x) dx.
-/

/- ## C. Summed first-order Euler-Maclaurin over `[0, N]`

    Summing `em_unit_step` over the cells `[0,1], [1,2], …, [N-1,N]` and telescoping the two
    integrals with `intervalIntegral.sum_integral_adjacent_intervals` gives the classical
    first-order Euler-Maclaurin formula (sum indexed `1..N`, integral over `[0,N]`)
        ∑_{n=1}^{N} f n = ∫_0^N f + (f N − f 0)/2 + ∫_0^N (sawBernoulli 1 x)·f'(x) dx.
    (Equivalently `∑_{n=0}^{N} f n = ∫_0^N f + (f 0 + f N)/2 + remainder`, the textbook form.)
-/

/- ## D. Zeta base case: first-order Euler-Maclaurin for `f x = x^{-s}` on `[1, N]`

    The reusable finite-`N` statement.  Specialising the general `[M, N]` machinery below to
    `M = 1`, `f x = x^{-s}` with derivative `f' x = -s · x^{-s-1}` (valid for `x ≠ 0`, hence on
    all of `[1, N]`), we get the classical finite Euler-Maclaurin representation of the partial
    zeta sum.  Taking `N → ∞` (real `s > 1`) matches the fractional-part representation in
    `Mathlib.NumberTheory.Harmonic.ZetaAsymp` (`zeta_limit_aux1`, `termTSum`).
-/

end LeanClassics.DavenportHeilbronn.EM
end

-- ===== LeanClassics.DHEMZetaComplex =====
section
/-
Ported from DrMurphyIsIn/Arda, telperion/examples/zeta_reflection/lean/EMZetaComplex.lean at commit
6fa9a1d29c877779fd3657265a20924c8032c026 (Lean 4.32 / Mathlib v4.32.0) to Lean 4.35 / Mathlib 56a00585 for rh-lab.

Copyright of the original: the Arda authors. Licensed under the Apache License, Version 2.0
(the "License"); you may not use this file except in compliance with the License. You may obtain
a copy of the License at http://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable
law or agreed to in writing, software distributed under the License is distributed on an "AS IS"
BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for
the specific language governing permissions and limitations under the License.

Changes from upstream: namespace ZetaReflection -> LeanClassics.DavenportHeilbronn.EM, imports
renamed to the LeanClassics module names, and API-drift fixes listed in DHEMZeta_DRIFT.md.
-/
/-  EMZetaComplex.lean -- A2 Theorem 1, E-track: the COMPLEX Euler-Maclaurin representation of ζ
    and its K=1 analytic continuation into the critical strip.

    Builds on `EMZeta.lean` (real-s EM chain, Parts A-D', kernel-clean).  This file is the
    complex lift and the analytic continuation:

      E1.  `em_unit_step_cpow`   -- one-step EM over [m,m+1] for a ℂ-valued C¹ function.
           `em_cpow_partial`      -- finite-N EM for `f x = (x:ℂ)^(-s)`, s : ℂ, on [1,N].
      E2.  `em_zeta_cpow`         -- N→∞ complex representation, valid Re s > 1, tied to riemannZeta.
      E3.  `em_zeta_strip`        -- K=1 analytic continuation to 0 < Re s (s ≠ 1) with explicit
                                     remainder bound (THE PRIZE — covers the critical strip).
      E4.  `em_zeta_strip_enclosure` -- evaluator-facing finite-sum + explicit-tail enclosure shape.

    Only fully-proven lemmas live here.  General-K (K ≥ 2) stays in EMZetaWip.lean.

    conjecture1_proved = False.  This is a classical analysis lemma (Euler-Maclaurin + identity
    theorem), NOT a proof of RH.
-/

open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real

namespace LeanClassics.DavenportHeilbronn.EM

/- ## E1a. One-step Euler-Maclaurin over a unit cell, ℂ-valued integrand.

    Direct lift of `em_unit_step`: the saw antiderivative `w x = x - m - 1/2` is real, cast to ℂ,
    and the IBP `intervalIntegral.integral_deriv_mul_eq_sub` runs in the `NormedRing ℂ`. -/

/-- **One-step Euler-Maclaurin over `[m, m+1]`, ℂ-valued `f`.**  Same statement as `em_unit_step`
    but `f, f' : ℝ → ℂ`; the saw factor `sawBernoulli 1 x` is cast to ℂ. -/
theorem em_unit_step_cpow {f f' : ℝ → ℂ} (m : ℤ)
    (hf : ∀ x ∈ Icc (m : ℝ) (m + 1), HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume (m : ℝ) (m + 1)) :
    (∫ x in (m : ℝ)..(m + 1), f x)
      = (f m + f (m + 1)) / 2
        - ∫ x in (m : ℝ)..(m + 1), (sawBernoulli 1 x : ℂ) * f' x := by
  -- The affine antiderivative `w x = x - m - 1/2` of the constant `1`, valued in ℂ.
  set w : ℝ → ℂ := fun x => (x : ℂ) - m - 1 / 2 with hw
  have hcc : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hw' : ∀ x, HasDerivAt w 1 x := by
    intro x
    have hbase : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
    have := (hbase.sub_const (m : ℂ)).sub_const (1 / 2 : ℂ)
    simpa [hw] using this
  have hwcont : Continuous w := by fun_prop
  have huv : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt w (1 : ℂ) x := fun x _ => hw' x
  have hfd : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt f (f' x) x := by
    intro x hx
    rw [uIcc_of_le hcc] at hx
    exact hf x hx
  have hw'int : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume (m : ℝ) (m + 1) :=
    intervalIntegrable_const
  have hIBP := integral_deriv_mul_eq_sub huv hfd hw'int hf'
  have hwL : w (m : ℝ) = -(1 / 2) := by simp only [hw]; push_cast; ring
  have hwR : w ((m : ℝ) + 1) = 1 / 2 := by simp only [hw]; push_cast; ring
  have hwf'int : IntervalIntegrable (fun x => w x * f' x) volume (m : ℝ) (m + 1) :=
    hf'.continuousOn_mul hwcont.continuousOn
  have hsplit :
      (∫ x in (m : ℝ)..(m + 1), (1 : ℂ) * f x + w x * f' x)
        = (∫ x in (m : ℝ)..(m + 1), f x) + ∫ x in (m : ℝ)..(m + 1), w x * f' x := by
    have hfcont : ContinuousOn f (uIcc (m : ℝ) (m + 1)) := fun x hx =>
      (hfd x hx).continuousAt.continuousWithinAt
    have hfint : IntervalIntegrable f volume (m : ℝ) (m + 1) :=
      hfcont.intervalIntegrable
    rw [intervalIntegral.integral_add (by simpa using hfint) hwf'int]
    simp
  -- Identify `(sawBernoulli 1 · : ℂ) · f'` with `w · f'` a.e. on the cell.
  have hsaw : (∫ x in (m : ℝ)..(m + 1), (sawBernoulli 1 x : ℂ) * f' x)
      = ∫ x in (m : ℝ)..(m + 1), w x * f' x := by
    apply intervalIntegral.integral_congr_ae
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨le_of_lt hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
    rw [sawBernoulli_one_eq_on_Ico hxIco]
    simp only [hw]; push_cast; ring
  rw [hsaw]
  have key : (∫ x in (m : ℝ)..(m + 1), f x) + ∫ x in (m : ℝ)..(m + 1), w x * f' x
      = w ((m : ℝ) + 1) * f ((m : ℝ) + 1) - w (m : ℝ) * f (m : ℝ) := by
    rw [← hsplit]; exact hIBP
  rw [hwL, hwR] at key
  -- Solve for `∫ f` (ℂ is not ordered — use `linear_combination`).
  linear_combination key

/- ## E1b. Summed complex EM over an integer window, and the partial-ζ identity.

    Lift of `euler_maclaurin_one_window` to ℂ-valued `f`.  The telescoping and per-cell
    integrability arguments are identical to the real proof; the trapezoid bookkeeping is over ℂ. -/

/-- Complex trapezoid-sum bookkeeping over `[M, N)`.  ℂ version of `trapezoid_sum_window`. -/
private lemma trapezoid_sum_window_cpow (f : ℝ → ℂ) {M N : ℕ} (hMN : M ≤ N) :
    (∑ k ∈ Finset.Ico M N, (f (k : ℝ) + f ((k : ℝ) + 1)) / 2)
      = (∑ n ∈ Finset.Ico M N, f (n : ℝ)) + (f N - f M) / 2 := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ p hp ih =>
      rw [Finset.sum_Ico_succ_top hp (fun k => (f (k : ℝ) + f ((k : ℝ) + 1)) / 2),
          Finset.sum_Ico_succ_top hp (fun n => f (n : ℝ)), ih]
      push_cast; ring

/-- **Complex first-order Euler-Maclaurin over the integer window `[M, N]`.**  ℂ version of
    `euler_maclaurin_one_window`. -/
theorem euler_maclaurin_one_window_cpow {f f' : ℝ → ℂ} (M N : ℕ) (hMN : M ≤ N)
    (hf : ∀ x ∈ Icc (M : ℝ) N, HasDerivAt f (f' x) x)
    (hf' : ∀ k ∈ Finset.Ico M N, IntervalIntegrable f' volume (k : ℝ) (k + 1)) :
    (∑ n ∈ Finset.Ico M N, f (n : ℝ))
      = (∫ x in (M : ℝ)..N, f x) - (f N - f M) / 2
        + ∫ x in (M : ℝ)..N, (sawBernoulli 1 x : ℂ) * f' x := by
  have hcell : ∀ k ∈ Finset.Ico M N, ∀ x ∈ Icc (k : ℝ) (k + 1), HasDerivAt f (f' x) x := by
    intro k hk x hx
    rw [Finset.mem_Ico] at hk
    refine hf x ⟨?_, ?_⟩
    · exact le_trans (by exact_mod_cast hk.1) hx.1
    · have : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk.2
      linarith [hx.2]
  have hstep : ∀ k ∈ Finset.Ico M N,
      (∫ x in (k : ℝ)..(k + 1), f x)
        = (f k + f (k + 1)) / 2 - ∫ x in (k : ℝ)..(k + 1), (sawBernoulli 1 x : ℂ) * f' x := by
    intro k hk
    have hcast : (((k : ℤ)) : ℝ) = (k : ℝ) := by push_cast; ring
    have hstepZ := em_unit_step_cpow (f := f) (f' := f') (k : ℤ)
      (by intro x hx; rw [hcast] at hx; exact hcell k hk x hx)
      (by rw [hcast]; exact hf' k hk)
    simp only [hcast] at hstepZ
    exact hstepZ
  have hsum := Finset.sum_congr rfl hstep
  have hfint_cell : ∀ k ∈ Finset.Ico M N, IntervalIntegrable f volume (k : ℝ) (k + 1) := by
    intro k hk
    have hcont : ContinuousOn f (uIcc (k : ℝ) (k + 1)) := by
      rw [uIcc_of_le (by linarith)]
      exact fun x hx => (hcell k hk x hx).continuousAt.continuousWithinAt
    exact hcont.intervalIntegrable
  have htel_f : (∑ k ∈ Finset.Ico M N, ∫ x in (k : ℝ)..(k + 1), f x)
      = ∫ x in (M : ℝ)..N, f x := by
    have hint : ∀ k ∈ Set.Ico M N,
        IntervalIntegrable f volume ((fun k : ℕ => (k : ℝ)) k) ((fun k : ℕ => (k : ℝ)) (k + 1)) := by
      intro k hk
      simpa [Nat.cast_succ] using hfint_cell k (Finset.mem_Ico.mpr hk)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun k : ℕ => (k : ℝ)) (f := f) (μ := volume) hMN hint
    simpa using this
  have hsawf'_cell : ∀ k ∈ Finset.Ico M N,
      IntervalIntegrable (fun x => (sawBernoulli 1 x : ℂ) * f' x) volume (k : ℝ) (k + 1) := by
    intro k hk
    have hcc : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have hcont : IntervalIntegrable (fun x => ((x - k - 1 / 2 : ℝ) : ℂ) * f' x) volume
        (k : ℝ) (k + 1) := (hf' k hk).continuousOn_mul (by fun_prop)
    refine (intervalIntegrable_congr_ae ?_).mpr hcont
    have hnull : ∀ᵐ x, x ≠ ((k : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico ((k : ℤ) : ℝ) (((k : ℤ) : ℝ) + 1) := by
      refine ⟨?_, ?_⟩
      · have : (k : ℝ) < x := hxmem.1
        push_cast; linarith
      · have hlt : x < (k : ℝ) + 1 := lt_of_le_of_ne hxmem.2 hxne
        push_cast; linarith
    rw [sawBernoulli_one_eq_on_Ico hxIco]
    push_cast; ring_nf
  have htel_saw : (∑ k ∈ Finset.Ico M N, ∫ x in (k : ℝ)..(k + 1), (sawBernoulli 1 x : ℂ) * f' x)
      = ∫ x in (M : ℝ)..N, (sawBernoulli 1 x : ℂ) * f' x := by
    have hint : ∀ k ∈ Set.Ico M N,
        IntervalIntegrable (fun x => (sawBernoulli 1 x : ℂ) * f' x) volume
          ((fun k : ℕ => (k : ℝ)) k) ((fun k : ℕ => (k : ℝ)) (k + 1)) := by
      intro k hk
      simpa [Nat.cast_succ] using hsawf'_cell k (Finset.mem_Ico.mpr hk)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun k : ℕ => (k : ℝ)) (f := fun x => (sawBernoulli 1 x : ℂ) * f' x) (μ := volume)
      hMN hint
    simpa using this
  rw [Finset.sum_sub_distrib, htel_f, htel_saw, trapezoid_sum_window_cpow f hMN] at hsum
  -- `hsum : ∑ f = (∫ f - ∑ saw) - (∑ f + (fN - fM)/2)` rearranged; finish over ℂ.
  linear_combination -hsum

/-- The complex-power derivative on the positive reals (E1's `hasDerivAt_cpow_neg_wip`):
    `HasDerivAt (fun x:ℝ => (x:ℂ)^(-s)) (-s·(x:ℂ)^(-s-1)) x` for `x > 0` and `s ≠ 0`.
    Anchored on `hasDerivAt_ofReal_cpow_const`. -/
theorem hasDerivAt_cpow_neg {s : ℂ} (hs : s ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hneg : (-s : ℂ) ≠ 0 := neg_ne_zero.mpr hs
  have := hasDerivAt_ofReal_cpow_const (x := x) hx0 (r := -s) hneg
  simpa using this

/-- **Complex finite-`N` Euler-Maclaurin representation of the partial ζ sum.**  For `s : ℂ`,
    `s ≠ 0`, `N ≥ 1`, applying `euler_maclaurin_one_window_cpow` to `f x = (x:ℂ)^(-s)`:
        ∑_{n=1}^{N-1} n^{-s} = ∫_1^N x^{-s} − (N^{-s} − 1^{-s})/2
                               + ∫_1^N (sawBernoulli 1 x)·(−s·x^{−s−1}). -/
theorem em_cpow_partial {s : ℂ} (hs : s ≠ 0) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
      = (∫ x in (1 : ℝ)..N, (x : ℂ) ^ (-s))
        - (((N : ℝ) : ℂ) ^ (-s) - ((1 : ℝ) : ℂ) ^ (-s)) / 2
        + ∫ x in (1 : ℝ)..N, (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
  have hderiv : ∀ x ∈ Icc ((1 : ℕ) : ℝ) N,
      HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := by have := hx.1; push_cast at this; linarith
    exact hasDerivAt_cpow_neg hs (lt_of_lt_of_le zero_lt_one hx1)
  have hf'int : ∀ k ∈ Finset.Ico 1 N,
      IntervalIntegrable (fun x => -s * (x : ℂ) ^ (-s - 1)) volume (k : ℝ) (k + 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    apply ContinuousOn.mul continuousOn_const
    -- `x ↦ (x:ℂ)^(-s-1)` is continuous on `[k, k+1]` (arg bounded away from 0, in slitPlane).
    apply ContinuousOn.cpow_const
    · exact Complex.continuous_ofReal.continuousOn
    · intro x hx
      have hx1 : (1 : ℝ) ≤ x := le_trans hk1 hx.1
      exact Or.inl (by simp only [Complex.ofReal_re]; linarith)
  have hEM := euler_maclaurin_one_window_cpow (f := fun x => (x : ℂ) ^ (-s))
    (f' := fun x => -s * (x : ℂ) ^ (-s - 1)) 1 N hN hderiv hf'int
  simpa using hEM

/- ## E2. The `N → ∞` complex representation for `Re s > 1`, tied to `riemannZeta`.

    Lift of `em_zeta_real` (Part D').  The three limits: partial sum → tsum (`summable_one_div_
    nat_cpow`), the two finite integrals → improper (`intervalIntegral_tendsto_integral_Ioi`),
    endpoint `N^{-s} → 0` (norm → 0).  Then `zeta_eq_tsum_one_div_nat_cpow` ties it to `ζ`. -/

/-- The complex `x^{-s}` is integrable on `(1, ∞)` for `Re s > 1`: its norm is `x^{-Re s}`,
    integrable there since `-Re s < -1`. -/
theorem cpow_neg_integrableOn_Ioi {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioi 1) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ (-s)) (volume.restrict (Ioi 1)) := by
    apply Measurable.aestronglyMeasurable
    exact (Complex.measurable_ofReal.pow_const _)
  have hbase : IntegrableOn (fun x : ℝ => x ^ (-s.re)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (a := -s.re) (c := (1 : ℝ)) (by linarith) (by norm_num)
  refine (integrable_norm_iff hmeas).mp ?_
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hxpos : (0 : ℝ) < x := lt_trans zero_lt_one hx
  simp only [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.neg_re]

/-- The complex saw remainder integrand is integrable on `(1, ∞)` for `Re s > 1`: dominate its
    norm by `(‖s‖/2)·x^{−Re s−1}`, integrable there since `−Re s − 1 < −1`. -/
theorem em_cpow_remainder_integrableOn {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))) (Ioi 1) := by
  have hbase : IntegrableOn (fun x : ℝ => (‖s‖ * (1 / 2)) * x ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (a := -s.re - 1) (c := (1 : ℝ)) (by linarith)
      (by norm_num)).const_mul _
  refine Integrable.mono' hbase ?_ ?_
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · exact Complex.measurable_ofReal.comp (sawBernoulli_measurable 1)
    · exact measurable_const.mul (Complex.measurable_ofReal.pow_const _)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hxpos : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hsaw := abs_sawBernoulli_one_le x
    have hnormcpow : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.sub_re, Complex.neg_re,
        Complex.one_re]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow, norm_neg]
    have hrpownn : (0 : ℝ) ≤ x ^ (-s.re - 1) := Real.rpow_nonneg hxpos.le _
    calc |sawBernoulli 1 x| * (‖s‖ * x ^ (-s.re - 1))
        ≤ (1 / 2) * (‖s‖ * x ^ (-s.re - 1)) := by
          gcongr
      _ = (‖s‖ * (1 / 2)) * x ^ (-s.re - 1) := by ring

/-- **Complex first-order Euler-Maclaurin representation of the ζ series** (`Re s > 1`).
        ∑' n, n^{-s} = ∫_1^∞ x^{-s} + 1^{-s}/2 + ∫_1^∞ (sawBernoulli 1 x)·(−s·x^{−s−1}). -/
theorem em_zeta_cpow {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (n : ℂ) ^ (-s))
      = (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s)) + ((1 : ℝ) : ℂ) ^ (-s) / 2
        + ∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hI : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioi 1) := cpow_neg_integrableOn_Ioi hs
  have hR := em_cpow_remainder_integrableOn hs
  have hsummable : Summable (fun n : ℕ => (n : ℂ) ^ (-s)) := by
    have hsm := (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
    refine hsm.congr (fun n => ?_)
    rw [Complex.cpow_neg, one_div]
  have h0 : ((0 : ℕ) : ℂ) ^ (-s) = 0 := by
    rw [Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  -- LHS: partial sum over `Ico 1 N` → the tsum.
  have hLHS : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) atTop
      (𝓝 (∑' n : ℕ, (n : ℂ) ^ (-s))) := by
    have hrange : (fun N : ℕ => ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
        = (fun N : ℕ => ∑ n ∈ Finset.range N, (n : ℂ) ^ (-s)) := by
      funext N
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN; simp
      · rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive (fun n => (n : ℂ) ^ (-s))
            (Nat.zero_le 1) (by lia : 1 ≤ N), Nat.Ico_zero_eq_range, Finset.sum_range_one,
            h0, zero_add]
    rw [hrange]; exact hsummable.hasSum.tendsto_sum_nat
  -- RHS component limits.
  have hA : Tendsto (fun N : ℕ => ∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s)) atTop
      (𝓝 (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s))) :=
    intervalIntegral_tendsto_integral_Ioi 1 hI tendsto_natCast_atTop_atTop
  have hEnd : Tendsto (fun N : ℕ => -((((N : ℝ) : ℂ) ^ (-s) - ((1 : ℝ) : ℂ) ^ (-s)) / 2)) atTop
      (𝓝 (((1 : ℝ) : ℂ) ^ (-s) / 2)) := by
    have hz : Tendsto (fun N : ℕ => (((N : ℝ) : ℂ)) ^ (-s)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hnorm : (fun N : ℕ => ‖(((N : ℝ) : ℂ)) ^ (-s)‖)
          =ᶠ[atTop] (fun N : ℕ => (N : ℝ) ^ (-s.re)) := by
        filter_upwards [eventually_gt_atTop 0] with N hN
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hN), Complex.neg_re]
      refine Tendsto.congr' hnorm.symm ?_
      exact (tendsto_rpow_neg_atTop (y := s.re) (by linarith)).comp tendsto_natCast_atTop_atTop
    have h2 := ((hz.sub_const (((1 : ℝ) : ℂ) ^ (-s))).div_const 2).neg
    convert h2 using 2; ring
  have hRem : Tendsto
      (fun N : ℕ => ∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      atTop
      (𝓝 (∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))) :=
    intervalIntegral_tendsto_integral_Ioi 1 hR tendsto_natCast_atTop_atTop
  have hEq : ∀ᶠ N : ℕ in atTop, (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
      = (∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s))
        + -((((N : ℝ) : ℂ) ^ (-s) - ((1 : ℝ) : ℂ) ^ (-s)) / 2)
        + ∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hp := em_cpow_partial hs0 (N := N) hN
    rw [hp]; ring
  have hRHS := (hA.add hEnd).add hRem
  have hLHS' : Tendsto (fun N : ℕ =>
      (∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s))
        + -((((N : ℝ) : ℂ) ^ (-s) - ((1 : ℝ) : ℂ) ^ (-s)) / 2)
        + ∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))) atTop
      (𝓝 (∑' n : ℕ, (n : ℂ) ^ (-s))) := hLHS.congr' hEq
  exact tendsto_nhds_unique hLHS' hRHS

/-- **Euler-Maclaurin representation of `riemannZeta`** for `Re s > 1`, via
    `zeta_eq_tsum_one_div_nat_cpow`. -/
theorem em_zeta_cpow_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s
      = (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s)) + ((1 : ℝ) : ℂ) ^ (-s) / 2
        + ∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs, ← em_zeta_cpow hs]
  refine tsum_congr (fun n => ?_)
  rw [Complex.cpow_neg, one_div]

/- ## E3. K=1 analytic continuation into the critical strip (THE PRIZE).

    Define the EM closed form on `{Re s > 0}`:
        emZetaRemainder s := ∫_1^∞ (sawBernoulli 1 x)·(−s·x^{−s−1})   -- converges for Re s > 0
        emZetaClosed s     := 1/(s−1) + 1/2 + emZetaRemainder s
    For `Re s > 1`, `∫_1^∞ x^{−s} = 1/(s−1)` and `1^{−s} = 1`, so `emZetaClosed s = riemannZeta s`
    (from `em_zeta_cpow_riemannZeta`).  Both `riemannZeta` and `emZetaClosed` are analytic on
    `{Re s > 0} \ {1}`, agree on the open set `{Re s > 1}` (which has accumulation points in the
    larger strip), so by the identity theorem they agree on all of `{Re s > 0} \ {1}`.  That is
    `em_zeta_strip`, which covers the whole critical strip. -/

/-- The EM remainder integral `R(s) = ∫_1^∞ (sawBernoulli 1 x)·(−s·x^{−s−1})`.  Converges
    absolutely for `Re s > 0` (integrand norm ≤ `(‖s‖/2)·x^{−Re s−1}`). -/
noncomputable def emZetaRemainder (s : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))

/-- The EM closed form `1/(s−1) + 1/2 + R(s)` — analytic on `{Re s > 0} \ {1}`, agreeing with
    `riemannZeta` there.  For `Re s > 1` the `1/(s−1)` is exactly `∫_1^∞ x^{−s}` and `1/2` is
    `1^{−s}/2`. -/
noncomputable def emZetaClosed (s : ℂ) : ℂ :=
  1 / (s - 1) + 1 / 2 + emZetaRemainder s

/-- The saw remainder integrand is integrable on `(1, ∞)` for the *weaker* hypothesis `Re s > 0`
    (not just `Re s > 1`): the same domination `‖·‖ ≤ (‖s‖/2)·x^{−Re s−1}` works, integrable since
    `−Re s − 1 < −1 ⇔ Re s > 0`.  This is the convergence that powers the continuation. -/
theorem em_cpow_remainder_integrableOn_strip {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))) (Ioi 1) := by
  have hbase : IntegrableOn (fun x : ℝ => (‖s‖ * (1 / 2)) * x ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (a := -s.re - 1) (c := (1 : ℝ)) (by linarith)
      (by norm_num)).const_mul _
  refine Integrable.mono' hbase ?_ ?_
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · exact Complex.measurable_ofReal.comp (sawBernoulli_measurable 1)
    · exact measurable_const.mul (Complex.measurable_ofReal.pow_const _)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hxpos : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hsaw := abs_sawBernoulli_one_le x
    have hnormcpow : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.sub_re, Complex.neg_re,
        Complex.one_re]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow, norm_neg]
    have hrpownn : (0 : ℝ) ≤ x ^ (-s.re - 1) := Real.rpow_nonneg hxpos.le _
    calc |sawBernoulli 1 x| * (‖s‖ * x ^ (-s.re - 1))
        ≤ (1 / 2) * (‖s‖ * x ^ (-s.re - 1)) := by gcongr
      _ = (‖s‖ * (1 / 2)) * x ^ (-s.re - 1) := by ring

/-- For `Re s > 1`, `emZetaClosed s = riemannZeta s` (unconditional identity in the region of
    convergence).  The `1/(s−1)` is `∫_1^∞ x^{−s}` and `1/2` is `1^{−s}/2`. -/
theorem emZetaClosed_eq_riemannZeta_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    emZetaClosed s = riemannZeta s := by
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  -- ∫_1^∞ x^{−s} = 1/(s−1)
  have hIntClosed : (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s)) = 1 / (s - 1) := by
    have hI := integral_Ioi_cpow_of_lt (a := -s) (by rw [Complex.neg_re]; linarith)
      (c := (1 : ℝ)) (by norm_num)
    rw [hI, Complex.ofReal_one, Complex.one_cpow]
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [div_eq_div_iff (by simpa [neg_add_eq_sub] using sub_ne_zero.mpr (Ne.symm hs1)) hs1']
    ring
  have hone : ((1 : ℝ) : ℂ) ^ (-s) = 1 := by
    rw [Complex.ofReal_one, Complex.one_cpow]
  rw [emZetaClosed, emZetaRemainder, em_zeta_cpow_riemannZeta hs, hIntClosed, hone]

/- ### E3 helpers for the analytic continuation. -/

/-- Elementary global bound `log x ≤ x^δ / δ` for `x ≥ 1`, `δ > 0` (log grows slower than any
    positive power).  `δ·log x = log(x^δ) ≤ x^δ − 1 ≤ x^δ`. -/
theorem log_le_rpow_div {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ x ^ δ / δ := by
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : δ * Real.log x = Real.log (x ^ δ) := (Real.log_rpow hxpos δ).symm
  have hxδpos : (0 : ℝ) < x ^ δ := Real.rpow_pos_of_pos hxpos δ
  have hle : Real.log (x ^ δ) ≤ x ^ δ - 1 := Real.log_le_sub_one_of_pos hxδpos
  rw [le_div_iff₀ hδ]
  calc Real.log x * δ = δ * Real.log x := by ring
    _ = Real.log (x ^ δ) := hlog
    _ ≤ x ^ δ - 1 := hle
    _ ≤ x ^ δ := by linarith

/-- The `s`-derivative of the EM remainder integrand at fixed real `x > 0`:
        ∂_s [ ↑(saw x)·(−s·x^{−s−1}) ] = ↑(saw x)·((−1 + s·log(x:ℂ))·x^{−s−1}).
    From `HasDerivAt.const_cpow` (derivative in the exponent) and the product/const-mul rules. -/
theorem hasDerivAt_emIntegrand (x : ℝ) (hx : 0 < x) (s : ℂ) :
    HasDerivAt (fun s : ℂ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      ((sawBernoulli 1 x : ℂ) * ((-1 + s * Complex.log (x : ℂ)) * (x : ℂ) ^ (-s - 1))) s := by
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  -- exponent map e s = -s - 1, derivative -1.
  have he : HasDerivAt (fun s : ℂ => -s - 1) (-1) s := by
    simpa using ((hasDerivAt_id s).neg.sub_const (1 : ℂ))
  -- (x:ℂ)^(e s) via const_cpow: derivative (x:ℂ)^(e s)·log(x:ℂ)·(-1).
  have hcpow : HasDerivAt (fun s : ℂ => (x : ℂ) ^ (-s - 1))
      ((x : ℂ) ^ (-s - 1) * Complex.log (x : ℂ) * (-1)) s :=
    he.const_cpow (Or.inl hxc)
  -- -s, derivative -1.
  have hlin : HasDerivAt (fun s : ℂ => -s) (-1) s := (hasDerivAt_id s).neg
  -- product (-s)·(x:ℂ)^(e s), then const-mul by ↑(saw x); package as the target function.
  have hfull : HasDerivAt (fun s : ℂ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      ((sawBernoulli 1 x : ℂ)
        * (-1 * (x : ℂ) ^ (-s - 1) + -s * ((x : ℂ) ^ (-s - 1) * Complex.log (x : ℂ) * -1))) s :=
    (hlin.mul hcpow).const_mul (sawBernoulli 1 x : ℂ)
  -- reconcile the derivative value algebraically.
  have hval : (sawBernoulli 1 x : ℂ)
        * (-1 * (x : ℂ) ^ (-s - 1) + -s * ((x : ℂ) ^ (-s - 1) * Complex.log (x : ℂ) * -1))
      = (sawBernoulli 1 x : ℂ) * ((-1 + s * Complex.log (x : ℂ)) * (x : ℂ) ^ (-s - 1)) := by
    ring
  rw [hval] at hfull
  exact hfull

/-- Integrability on `(1,∞)` of the dominating bound `C · x^{−σ−1} + D · x^{δ−σ−1}` used for
    differentiation under the integral, when `0 < δ < σ` (so both exponents are `< −1`). -/
private theorem bound_integrableOn {C D σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ < σ) :
    IntegrableOn (fun x : ℝ => C * x ^ (-σ - 1) + D * x ^ (δ - σ - 1)) (Ioi 1) := by
  have h1 : IntegrableOn (fun x : ℝ => C * x ^ (-σ - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (a := -σ - 1) (by linarith) (by norm_num : (0:ℝ) < 1)).const_mul _
  have h2 : IntegrableOn (fun x : ℝ => D * x ^ (δ - σ - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (a := δ - σ - 1) (by linarith) (by norm_num : (0:ℝ) < 1)).const_mul _
  exact h1.add h2

-- port: upstream compiled at the default 200000 heartbeats on Mathlib v4.32.0; on 56a00585 it times out at `whnf`.
set_option maxHeartbeats 800000 in
/-- **The EM remainder integral is complex-differentiable on `{Re s > 0}`** (E3 analytic core).
    Differentiation under the integral sign via `hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
    with the local uniform domination `‖∂_s integrand‖ ≤ bound x` on a ball inside the half-plane
    and `bound` integrable by `bound_integrableOn`. -/
theorem emZetaRemainder_hasDerivAt {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    HasDerivAt emZetaRemainder
      (∫ x in Ioi (1 : ℝ),
        (sawBernoulli 1 x : ℂ) * ((-1 + s₀ * Complex.log (x : ℂ)) * (x : ℂ) ^ (-s₀ - 1))) s₀ := by
  set σ : ℝ := s₀.re / 2 with hσdef
  set ε : ℝ := s₀.re / 2 with hεdef
  set δ : ℝ := σ / 2 with hδdef
  have hσpos : 0 < σ := by rw [hσdef]; linarith
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδσ : δ < σ := by rw [hδdef]; linarith
  -- The ball `s` region and the re-lower-bound on it.
  set S : Set ℂ := Metric.ball s₀ ε with hSdef
  have hS_nhds : S ∈ 𝓝 s₀ := Metric.ball_mem_nhds s₀ hεpos
  have hre_lb : ∀ s ∈ S, σ ≤ s.re := by
    intro s hs
    rw [hSdef, Metric.mem_ball] at hs
    have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      simpa using Complex.abs_re_le_norm (s - s₀)
    have h2 : ‖s - s₀‖ < ε := by rwa [Complex.dist_eq] at hs
    have : |s.re - s₀.re| < ε := lt_of_le_of_lt h1 h2
    have := (abs_lt.mp this).1
    rw [hσdef, hεdef]; rw [hεdef] at this; linarith
  -- Integrand F and derivative F'.
  set F : ℂ → ℝ → ℂ := fun s x => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) with hFdef
  set F' : ℂ → ℝ → ℂ := fun s x =>
    (sawBernoulli 1 x : ℂ) * ((-1 + s * Complex.log (x : ℂ)) * (x : ℂ) ^ (-s - 1)) with hF'def
  -- The dominating bound.
  set bnd : ℝ → ℝ := fun x => (1 / 2) * x ^ (-σ - 1)
    + ((1 / 2) * (‖s₀‖ + ε) * (1 / δ)) * x ^ (δ - σ - 1) with hbnddef
  -- (a) measurability of F near s₀
  have hF_meas : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable (F s) (volume.restrict (Ioi 1)) := by
    filter_upwards with s
    apply Measurable.aestronglyMeasurable
    rw [hFdef]
    exact (Complex.measurable_ofReal.comp (sawBernoulli_measurable 1)).mul
      (measurable_const.mul (Complex.measurable_ofReal.pow_const _))
  -- (b) F s₀ integrable
  have hF_int : Integrable (F s₀) (volume.restrict (Ioi 1)) :=
    em_cpow_remainder_integrableOn_strip hs₀
  -- (c) F' s₀ measurable
  have hF'_meas : AEStronglyMeasurable (F' s₀) (volume.restrict (Ioi 1)) := by
    apply Measurable.aestronglyMeasurable
    rw [hF'def]
    apply (Complex.measurable_ofReal.comp (sawBernoulli_measurable 1)).mul
    apply Measurable.mul
    · exact measurable_const.add (measurable_const.mul
        (Complex.measurable_log.comp Complex.measurable_ofReal))
    · exact Complex.measurable_ofReal.pow_const _
  -- (d) uniform bound on S
  have h_bound : ∀ᵐ x ∂(volume.restrict (Ioi 1)), ∀ s ∈ S, ‖F' s x‖ ≤ bnd x := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx s hs
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
    have hsre : σ ≤ s.re := hre_lb s hs
    have hslt : ‖s‖ ≤ ‖s₀‖ + ε := by
      have : ‖s - s₀‖ < ε := by rw [hSdef, Metric.mem_ball, Complex.dist_eq] at hs; exact hs
      calc ‖s‖ = ‖s₀ + (s - s₀)‖ := by ring_nf
        _ ≤ ‖s₀‖ + ‖s - s₀‖ := norm_add_le _ _
        _ ≤ ‖s₀‖ + ε := by linarith
    -- ‖F' s x‖ = |saw|·‖(-1 + s log x)·x^{-s-1}‖ ≤ (1/2)·(1 + ‖s‖ log x)·x^{-σ-1}
    have hlogeq : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := (Complex.ofReal_log hxpos.le).symm
    have hnormcpow : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.sub_re, Complex.neg_re,
        Complex.one_re]
    have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hcpownn : (0 : ℝ) ≤ x ^ (-s.re - 1) := Real.rpow_nonneg hxpos.le _
    have hsaw := abs_sawBernoulli_one_le x
    -- factor bound
    have hfac : ‖(-1 + s * Complex.log (x : ℂ)) * (x : ℂ) ^ (-s - 1)‖
        ≤ (1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1) := by
      rw [norm_mul, hnormcpow]
      gcongr
      calc ‖(-1 + s * Complex.log (x : ℂ))‖
          ≤ ‖(-1 : ℂ)‖ + ‖s * Complex.log (x : ℂ)‖ := norm_add_le _ _
        _ = 1 + ‖s‖ * ‖Complex.log (x : ℂ)‖ := by rw [norm_mul]; norm_num
        _ = 1 + ‖s‖ * Real.log x := by
            rw [hlogeq, Complex.norm_real, Real.norm_of_nonneg hlognn]
    -- log bound: log x ≤ x^δ / δ
    have hlogbd : Real.log x ≤ x ^ δ / δ := log_le_rpow_div hδpos hx1
    have hxδdivnn : (0 : ℝ) ≤ x ^ δ / δ := by positivity
    have hs₀εnn : (0 : ℝ) ≤ ‖s₀‖ + ε := by positivity
    have hexpmono : x ^ (-s.re - 1) ≤ x ^ (-σ - 1) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hcpowσnn : (0 : ℝ) ≤ x ^ (-σ - 1) := Real.rpow_nonneg hxpos.le _
    rw [hF'def, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |sawBernoulli 1 x| * ‖(-1 + s * Complex.log (x : ℂ)) * (x : ℂ) ^ (-s - 1)‖
        ≤ (1 / 2) * ((1 + ‖s‖ * Real.log x) * x ^ (-s.re - 1)) := by
          gcongr
      _ ≤ (1 / 2) * ((1 + (‖s₀‖ + ε) * (x ^ δ / δ)) * x ^ (-σ - 1)) := by
          gcongr
      _ = bnd x := by
          have hxadd : x ^ (δ - σ - 1) = x ^ δ * x ^ (-σ - 1) := by
            rw [← Real.rpow_add hxpos]; congr 1; ring
          have hδne : δ ≠ 0 := ne_of_gt hδpos
          simp only [hbnddef, hxadd]
          field_simp
  -- Assemble via the parametric-integral differentiation lemma.
  have hbnd_int : Integrable bnd (volume.restrict (Ioi 1)) := by
    rw [hbnddef]
    exact bound_integrableOn (C := 1 / 2) (D := (1 / 2) * (‖s₀‖ + ε) * (1 / δ))
      hσpos hδpos hδσ
  have h_diff : ∀ᵐ x ∂(volume.restrict (Ioi 1)), ∀ s ∈ S, HasDerivAt (fun s => F s x) (F' s x) s := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx s _
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one (le_of_lt hx)
    exact hasDerivAt_emIntegrand x hxpos s
  obtain ⟨_, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := bnd) (F := F) (F' := F') hS_nhds hF_meas hF_int hF'_meas h_bound hbnd_int h_diff
  exact hderiv

/-- `emZetaRemainder` is differentiable at every `s` with `Re s > 0`. -/
theorem emZetaRemainder_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ emZetaRemainder s :=
  (emZetaRemainder_hasDerivAt hs).differentiableAt

/- ### The critical-strip half-plane, slit at `1`, is preconnected. -/

/-- The open right half-plane `{Re s > 0}`. -/
def rightHalfPlane : Set ℂ := {s : ℂ | 0 < s.re}

/-- The half-plane slit at `1` is preconnected: cover by four convex half-space intersections
    (im>0, im<0, re<1, re>1), each avoiding `1` (whose im=0, re=1), chained by shared points. -/
theorem isPreconnected_rightHalfPlane_diff_one :
    IsPreconnected (rightHalfPlane \ {1}) := by
  have hHconv : Convex ℝ rightHalfPlane := convex_halfSpace_re_gt 0
  -- Four convex pieces.
  set U₁ : Set ℂ := rightHalfPlane ∩ {s : ℂ | 0 < s.im} with hU₁
  set U₂ : Set ℂ := rightHalfPlane ∩ {s : ℂ | s.im < 0} with hU₂
  set U₃ : Set ℂ := rightHalfPlane ∩ {s : ℂ | s.re < 1} with hU₃
  set U₄ : Set ℂ := rightHalfPlane ∩ {s : ℂ | 1 < s.re} with hU₄
  have pc₁ : IsPathConnected U₁ :=
    (hHconv.inter (convex_halfSpace_im_gt 0)).isPathConnected ⟨1 + I, by
      constructor <;> simp [rightHalfPlane]⟩
  have pc₂ : IsPathConnected U₂ :=
    (hHconv.inter (convex_halfSpace_im_lt 0)).isPathConnected ⟨1 - I, by
      constructor <;> simp [rightHalfPlane]⟩
  have pc₃ : IsPathConnected U₃ :=
    (hHconv.inter (convex_halfSpace_re_lt 1)).isPathConnected ⟨1/2, by
      constructor <;> simp [rightHalfPlane] <;> norm_num⟩
  have pc₄ : IsPathConnected U₄ :=
    (hHconv.inter (convex_halfSpace_re_gt 1)).isPathConnected ⟨2, by
      constructor <;> simp [rightHalfPlane] <;> norm_num⟩
  -- Shared points to chain: (U₃∪U₄ region) ∪ (U₁) ∪ (U₂).
  -- First glue U₃ and U₁ via 1/2 + I; then that with U₂ via 1/2 - I; then with U₄ via 2 - I... but
  -- U₄ meets U₂ via 2 - I.  Chain: ((U₃ ∪ U₁) ∪ U₂) ∪ U₄.
  have g31 : IsPathConnected (U₃ ∪ U₁) :=
    pc₃.union pc₁ ⟨1/2 + I, by
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp [rightHalfPlane] <;> norm_num⟩
  have g312 : IsPathConnected ((U₃ ∪ U₁) ∪ U₂) :=
    g31.union pc₂ ⟨1/2 - I, by
      refine ⟨Or.inl ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp [rightHalfPlane] <;> norm_num⟩
  have g3124 : IsPathConnected (((U₃ ∪ U₁) ∪ U₂) ∪ U₄) :=
    g312.union pc₄ ⟨2 - I, by
      refine ⟨Or.inr ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp [rightHalfPlane] <;> norm_num⟩
  -- The union equals `H \ {1}`.
  have hcover : ((U₃ ∪ U₁) ∪ U₂) ∪ U₄ = rightHalfPlane \ {1} := by
    ext z
    simp only [hU₁, hU₂, hU₃, hU₄, Set.mem_union, Set.mem_inter_iff, Set.mem_diff,
      Set.mem_singleton_iff, Set.mem_setOf_eq, rightHalfPlane]
    constructor
    · rintro (((⟨hz, _⟩ | ⟨hz, _⟩) | ⟨hz, _⟩) | ⟨hz, _⟩) <;>
        exact ⟨hz, by
          rintro rfl <;> simp_all⟩
    · rintro ⟨hz, hz1⟩
      by_cases him : z.im = 0
      · -- on real axis, re ≠ 1
        have hre1 : z.re ≠ 1 := by
          intro h; exact hz1 (by apply Complex.ext <;> simp [h, him])
        rcases lt_or_gt_of_ne hre1 with h | h
        · exact Or.inl (Or.inl (Or.inl ⟨hz, h⟩))
        · exact Or.inr ⟨hz, h⟩
      · rcases lt_or_gt_of_ne him with h | h
        · exact Or.inl (Or.inr ⟨hz, h⟩)
        · exact Or.inl (Or.inl (Or.inr ⟨hz, h⟩))
  rw [← hcover]
  exact g3124.isConnected.isPreconnected

/- ### E3 capstone: the identity theorem transfer. -/

/-- `emZetaClosed` is analytic on the slit half-plane `{Re s > 0} \ {1}`. -/
theorem emZetaClosed_analyticOnNhd :
    AnalyticOnNhd ℂ emZetaClosed (rightHalfPlane \ {1}) := by
  apply DifferentiableOn.analyticOnNhd _ ?_
  · intro s hs
    have hs0 : 0 < s.re := hs.1
    have hs1 : s ≠ 1 := by simpa using hs.2
    have hpole : DifferentiableAt ℂ (fun s : ℂ => 1 / (s - 1)) s := by
      apply DifferentiableAt.div (differentiableAt_const _)
        ((differentiableAt_id).sub (differentiableAt_const _))
      exact sub_ne_zero.mpr hs1
    have hrem : DifferentiableAt ℂ emZetaRemainder s := emZetaRemainder_differentiableAt hs0
    have : DifferentiableAt ℂ emZetaClosed s := by
      unfold emZetaClosed
      exact (hpole.add (differentiableAt_const _)).add hrem
    exact this.differentiableWithinAt
  · -- the slit half-plane is open
    apply IsOpen.sdiff _ isClosed_singleton
    exact (isOpen_lt continuous_const Complex.continuous_re)

/-- `riemannZeta` is analytic on the slit half-plane `{Re s > 0} \ {1}` (it is analytic on all of
    `{1}ᶜ`). -/
theorem riemannZeta_analyticOnNhd_strip :
    AnalyticOnNhd ℂ riemannZeta (rightHalfPlane \ {1}) := by
  apply DifferentiableOn.analyticOnNhd _ ?_
  · intro s hs
    have hs1 : s ≠ 1 := by simpa using hs.2
    exact (differentiableAt_riemannZeta hs1).differentiableWithinAt
  · apply IsOpen.sdiff _ isClosed_singleton
    exact (isOpen_lt continuous_const Complex.continuous_re)

/-- **THE PRIZE (E3): K=1 analytic continuation of the Euler-Maclaurin representation of ζ into
    the critical strip.**  For every `s` with `0 < Re s` and `s ≠ 1`,
        riemannZeta s = 1/(s−1) + 1/2 + ∫_1^∞ (sawBernoulli 1 x)·(−s·x^{−s−1}) dx,
    with the remainder integral converging absolutely and bounded by `‖s‖/(2·Re s)`
    (`emZetaRemainder_bound`).  This covers the entire critical strip `0 < Re s < 1`.

    Proof: both sides are analytic on the (preconnected) slit half-plane and agree on the open
    subset `{Re s > 1}` (where the series converges), so by the identity theorem
    (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, anchored at `s = 2`) they agree on the
    whole slit half-plane. -/
theorem em_zeta_strip {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s
      = 1 / (s - 1) + 1 / 2
        + ∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
  -- reduce to `emZetaClosed s = riemannZeta s`.
  suffices h : Set.EqOn emZetaClosed riemannZeta (rightHalfPlane \ {1}) by
    have hmem : s ∈ rightHalfPlane \ {1} := ⟨hs, by simpa using hs1⟩
    have heq := h hmem
    rw [emZetaClosed, emZetaRemainder] at heq
    exact heq.symm
  -- identity theorem, anchored at s = 2.
  have h2mem : (2 : ℂ) ∈ rightHalfPlane \ {1} := by
    refine ⟨?_, ?_⟩ <;> simp [rightHalfPlane]
  have hevent : emZetaClosed =ᶠ[𝓝 (2 : ℂ)] riemannZeta := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hnhds : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      hopen.mem_nhds (by simp)
    filter_upwards [hnhds] with z hz
    exact emZetaClosed_eq_riemannZeta_of_one_lt hz
  exact emZetaClosed_analyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    riemannZeta_analyticOnNhd_strip isPreconnected_rightHalfPlane_diff_one h2mem hevent

/- ## E4. Evaluator-facing enclosure (the A4 `checkBand` consumer shape).

    The A4 interval evaluator needs: an EXPLICIT finite part it can box with `DIntv` arithmetic,
    plus a RATIONAL error envelope on the (unevaluated) remainder.  `em_zeta_strip` already
    delivers exactly this at `K = 1`: the finite part is the elementary closed form
    `1/(s−1) + 1/2` (a reciprocal + a constant — directly boxable), and the remainder envelope is
    `‖s‖/(2·Re s)`.  We package it as a single norm enclosure, and give the `σ = 1/2 + it`
    critical-line specialization (the band the evaluator sweeps).

    Interface for A4 (`DIntvDef.DIntv.memR`): supplied dyadic-interval enclosures of `Re(1/(s−1))`,
    `Im(1/(s−1))`, the constant `1/2`, and the scalar envelope `‖s‖/(2·Re s)`, the evaluator boxes
    `Re(ζ s)` and `Im(ζ s)` within
        [Re(finite) − env, Re(finite) + env]  ×  [Im(finite) − env, Im(finite) + env].
    (`stirlingFinite`-style, mirroring `StirlingBinet.logDeriv_gammaR_enclosure`.) -/

end LeanClassics.DavenportHeilbronn.EM
end

-- ===== LeanClassics.DHEMZetaTail =====
section
/-
Ported from DrMurphyIsIn/Arda, telperion/examples/zeta_reflection/lean/EMZetaTail.lean at commit
6fa9a1d29c877779fd3657265a20924c8032c026 (Lean 4.32 / Mathlib v4.32.0) to Lean 4.35 / Mathlib 56a00585 for rh-lab.

Copyright of the original: the Arda authors. Licensed under the Apache License, Version 2.0
(the "License"); you may not use this file except in compliance with the License. You may obtain
a copy of the License at http://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable
law or agreed to in writing, software distributed under the License is distributed on an "AS IS"
BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for
the specific language governing permissions and limitations under the License.

Changes from upstream: namespace ZetaReflection -> LeanClassics.DavenportHeilbronn.EM, imports
renamed to the LeanClassics module names, and API-drift fixes listed in DHEMZeta_DRIFT.md.
-/
/-  EMZetaTail.lean -- A2 Theorem 1, TAIL track: the order-K Euler-Maclaurin tail engine.

    The blocker of PROGRAM ANDÚRIL's reflection track.  Builds on `EMZeta.lean` /
    `EMZetaComplex.lean` (the K=1 chain).  The K=1 remainder envelope `‖s‖/(2·Re s)` proven in
    `EMZetaComplex.em_zeta_strip_enclosure` is sign-LOOSE (≈14 at s=1/2+14i), so the G2 reflected
    band could not be made sign-tight from it.  This file raises the Euler-Maclaurin order and cuts
    the sum at a finite `N`, producing a remainder that DECAYS like `N^{-Re s - K + 1}`, small enough
    to make `gLine` boxes sign-tight.

    Architecture (bottom-up), ALL kernel-clean (AxiomGuardEMTail):

      F.  Order-2/3 periodized "saw" Bernoulli sup bounds: `|sawBernoulli 2| ≤ 1/6`,
          `|sawBernoulli 3| ≤ 1/12` (via `B₃ = y(1−y)(1/2−y)`), and `bernoulliFun_three` closed form.
      G.  `em_saw_step` — the one IBP step raising the saw order by one over a unit cell (the proven
          form of `EMZetaWip.em_saw_step_wip`), via the continuous polynomial surrogate
          `B_{k+1}(x−m)/(k+1)`.  Endpoint saw values `B_{k+1}(0)`, `B_{k+1}(1)` (equal for `k+1≠1`).
      G'. `em_saw_step_window` — sum `em_saw_step` over `[M,N]`; interior boundary terms telescope
          (`bernoulliFun_endpoints_eq_of_ne_one`), leaving only `B_{k+1}(0)(fk N − fk M)/(k+1)`.
      H.  `em_tail_integral_bound` — the reusable engine: `‖∫_N^∞ saw_k · c·x^{−s−k}‖`
          ≤ `B·‖c‖·N^{−(Re s+k−1)}/(Re s+k−1)`, the `N`-decay that makes gLine boxes sign-tight.
      I.  `em_tail3_bound` (order-3, `B = 1/12`) and `em_tail3_number` — THE NUMBER: at the G2 pilot
          `s = 1/2 + 14i`, `N = 200`, the order-3 remainder is `≤ 10⁻³` (kernel-decided).  Clears the
          go/no-go the K=1 envelope `‖s‖/(2·Re s) ≈ 14` failed.

    REMAINING for the full ζ-order-K identity: tie `em_saw_step_window` to `riemannZeta` by
    raising the K=1 remainder `∫_1^∞ saw₁·(−s x^{−s−1})` (from `EMZetaComplex.em_zeta_strip`) to
    order 3 over `[N,∞)` — apply `em_saw_step_window` on `[N,M]` (complex cpow orders 2,3, derivative
    coefficients `s(s+1)…`), then `M → ∞` (boundary terms → 0; integral → `∫_N^∞`), reusing the
    `intervalIntegral_tendsto_integral_Ioi` limit pattern from `em_zeta_cpow`.  The remainder BOUND at
    the endpoint is already `em_tail3_bound`; only the identity plumbing remains.

    conjecture1_proved = False.  This is a classical analysis lemma (Euler-Maclaurin tail bound),
    NOT a proof of RH.
-/

open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real

namespace LeanClassics.DavenportHeilbronn.EM

/- ## F. Order-k periodized Bernoulli: derivative tower and explicit sup bounds. -/

/-- Explicit sup bound for the order-2 saw: `|sawBernoulli 2 x| ≤ 1/6`.
    On the unit cell `y := {x} ∈ [0,1)`, `B₂(y) = y² − y + 1/6 = (y − 1/2)² − 1/12 ∈ [−1/12, 1/6]`. -/
lemma abs_sawBernoulli_two_le (x : ℝ) : |sawBernoulli 2 x| ≤ 1 / 6 := by
  have h0 : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  rw [sawBernoulli, bernoulliFun_two, abs_le]
  constructor <;> nlinarith [sq_nonneg (Int.fract x - 1/2), h0, h1]

/- ## G. The saw-order-raising IBP step over a unit cell.

    The antiderivative tower: `sawBernoulli (k+1) / (k+1)` has derivative `sawBernoulli k` on the
    OPEN cell `(m, m+1)` (from `antideriv_bernoulliFun`, since `Int.fract` has derivative `1` off
    ℤ and `bernoulliFun (k+1)/(k+1)` has derivative `bernoulliFun k`).  IBP with this antiderivative
    turns `∫ sawBernoulli k · fk` into a boundary term plus `∫ sawBernoulli (k+1) · fk'`, exactly
    one order higher.  The endpoint saw values are `bernoulliFun (k+1) 0` and `bernoulliFun (k+1) 1`
    (the cell is `[m, m+1]`), which for `k+1 ≠ 1` are EQUAL by `bernoulliFun_endpoints_eq_of_ne_one`
    — the mechanism that makes the interior Bernoulli boundary terms telescope to zero. -/

/-- The continuous polynomial surrogate `W y = bernoulliFun (k+1) (y - m) / (k+1)` for the shifted
    saw antiderivative on the cell `[m, m+1]`.  It is C¹ everywhere with derivative
    `bernoulliFun k (y - m)`, and agrees with `sawBernoulli (k+1) ·/(k+1)` on `[m, m+1)`. -/
private noncomputable def sawSurrogate (k : ℕ) (m : ℤ) (y : ℝ) : ℝ :=
  bernoulliFun (k + 1) (y - m) / (k + 1)

private lemma sawSurrogate_hasDerivAt (k : ℕ) (m : ℤ) (y : ℝ) :
    HasDerivAt (sawSurrogate k m) (bernoulliFun k (y - m)) y := by
  have hshift : HasDerivAt (fun z : ℝ => z - (m : ℝ)) 1 y := by
    simpa using (hasDerivAt_id y).sub_const (m : ℝ)
  have hanti := antideriv_bernoulliFun k (y - m)
  have hcomp := hanti.comp y hshift
  rw [mul_one] at hcomp
  have hfun : ((fun z => bernoulliFun (k + 1) z / (↑k + 1)) ∘ (fun z : ℝ => z - (m : ℝ)))
      = sawSurrogate k m := by
    funext z; simp [Function.comp, sawSurrogate]
  rw [hfun] at hcomp
  exact hcomp

/-- ℂ-valued telescoping sum of first differences. -/
private lemma sum_telescope_diff_cpow (g : ℝ → ℂ) {M N : ℕ} (hMN : M ≤ N) :
    (∑ j ∈ Finset.Ico M N, (g ((j : ℝ) + 1) - g (j : ℝ))) = g (N : ℝ) - g (M : ℝ) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ p hp ih => rw [Finset.sum_Ico_succ_top hp, ih]; push_cast; ring

/- ## G'. Summed saw-order-raising over an integer window `[M, N]`.

    Summing `em_saw_step` over the cells `[M,M+1], …, [N-1,N]` and telescoping via
    `sum_integral_adjacent_intervals_Ico`, the interior boundary terms cancel (for `k+1 ≠ 1` the
    saw endpoint values `B_{k+1}(0) = B_{k+1}(1)` agree, so adjacent cells contribute
    `+B_{k+1}(0)·f(j)` and `−B_{k+1}(0)·f(j)`), leaving only the two outer endpoints:
        ∫_M^N saw_k · fk
          = B_{k+1}(0)·(fk N − fk M)/(k+1)  −  (∫_M^N saw_{k+1} · fk1)/(k+1).
    (Here `k ≥ 1` so `k + 1 ≠ 1`, which is what makes the telescoping clean.) -/

/- ## H. The order-K tail remainder integrals and their explicit `N`-decaying bounds.

    The consumer needs a remainder over the TAIL `[N, ∞)` whose norm decays in `N`.  We work with
    the complex integrand `sawBernoulli k x · (c · (x:ℂ)^(-s-k))` where `c` is the falling-factorial
    coefficient `(-1)^k s(s+1)…(s+k-1)` (the k-th derivative coefficient of `x^{-s}`).  The norm
    bound is the clean product form
        ‖∫_N^∞ saw_k · c·x^{-s-k}‖ ≤ Bsup_k · ‖c‖ · N^{-Re s - k + 1} / (Re s + k - 1),
    from `‖saw_k‖ ≤ Bsup_k`, `‖x^{-s-k}‖ = x^{-Re s - k}`, and `∫_N^∞ x^{-Re s -k} = N^{-Re s -k+1}/(Re s+k-1)`. -/

/-- Generic explicit tail bound for a saw-weighted power integrand on `[N, ∞)`.
    If `‖sawBernoulli k x‖ ≤ B` for all `x` (as a real bound on the real saw) and the integrand is
    `sawBernoulli k x · (c · (x:ℂ)^(-s-k))`, then over `[N,∞)` with `N ≥ 1` and `Re s + k > 1`,
        ‖∫‖ ≤ B · ‖c‖ · N^{-(Re s + k - 1)} / (Re s + k - 1).
    This is the single reusable engine for all K. -/
theorem em_tail_integral_bound {k : ℕ} {s c : ℂ} {B : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hexp : 1 < s.re + k) (hB : 0 ≤ B)
    (hsawB : ∀ x : ℝ, |sawBernoulli k x| ≤ B) :
    ‖∫ x in Ioi (N : ℝ), (sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k))‖
      ≤ B * ‖c‖ * (N : ℝ) ^ (-(s.re + k - 1)) / (s.re + k - 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hσk1 : 0 < s.re + k - 1 := by linarith
  -- exponent for the norm: -(Re s + k) < -1.
  have hexplt : -(s.re + (k : ℝ)) < -1 := by
    have : (1 : ℝ) < s.re + k := hexp
    linarith
  -- integrand norm domination: ‖·‖ ≤ (B·‖c‖) · x^{-(Re s + k)} on (N,∞).
  have hdom : IntegrableOn (fun x : ℝ => (B * ‖c‖) * x ^ (-(s.re + (k : ℝ)))) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(s.re + (k : ℝ))) hexplt hNpos).const_mul _
  have hInt : IntegrableOn (fun x : ℝ => (sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k)))
      (Ioi (N : ℝ)) := by
    refine Integrable.mono' hdom ?_ ?_
    · apply Measurable.aestronglyMeasurable
      exact (Complex.measurable_ofReal.comp (sawBernoulli_measurable k)).mul
        (measurable_const.mul (Complex.measurable_ofReal.pow_const _))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hxpos : (0 : ℝ) < x := lt_trans hNpos hx
      have hnormcpow : ‖(x : ℂ) ^ (-s - k)‖ = x ^ (-(s.re + (k : ℝ))) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
        congr 1
        rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
        ring
      have hrpownn : (0 : ℝ) ≤ x ^ (-(s.re + (k : ℝ))) := Real.rpow_nonneg hxpos.le _
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow]
      calc |sawBernoulli k x| * (‖c‖ * x ^ (-(s.re + (k : ℝ))))
          ≤ B * (‖c‖ * x ^ (-(s.re + (k : ℝ)))) := by
            gcongr; exact hsawB x
        _ = (B * ‖c‖) * x ^ (-(s.re + (k : ℝ))) := by ring
  -- ‖∫‖ ≤ ∫‖·‖ ≤ ∫ dom = (B‖c‖)·N^{-(σ+k-1)}/(σ+k-1).
  calc ‖∫ x in Ioi (N : ℝ), (sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k))‖
      ≤ ∫ x in Ioi (N : ℝ), ‖(sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi (N : ℝ), (B * ‖c‖) * x ^ (-(s.re + (k : ℝ))) := by
        apply setIntegral_mono_on hInt.norm hdom measurableSet_Ioi
        intro x hx
        have hxpos : (0 : ℝ) < x := lt_trans hNpos hx
        have hnormcpow : ‖(x : ℂ) ^ (-s - k)‖ = x ^ (-(s.re + (k : ℝ))) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
          congr 1
          rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; ring
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow]
        calc |sawBernoulli k x| * (‖c‖ * x ^ (-(s.re + (k : ℝ))))
            ≤ B * (‖c‖ * x ^ (-(s.re + (k : ℝ)))) := by
              gcongr; exact hsawB x
          _ = (B * ‖c‖) * x ^ (-(s.re + (k : ℝ))) := by ring
    _ = B * ‖c‖ * (N : ℝ) ^ (-(s.re + k - 1)) / (s.re + k - 1) := by
        rw [MeasureTheory.integral_const_mul,
          integral_Ioi_rpow_of_lt (a := -(s.re + (k : ℝ))) hexplt hNpos]
        have hexp1 : -(s.re + (k : ℝ)) + 1 = -(s.re + k - 1) := by ring
        rw [hexp1]
        have hne : s.re + (k : ℝ) - 1 ≠ 0 := ne_of_gt hσk1
        field_simp

/- ## H'. The SHIFTED-BASE tail engine `(w + x)^{-a}` (the Binet / Γℝ substrate).

    The base-1 engine `em_tail_integral_bound` bounds saw-weighted `x^{-s-k}` tails.  The Binet
    remainder `μ_K(w)` (Stirling series for `ψ`) is, up to the finite Bernoulli peel, an
    Euler–Maclaurin tail of the trigamma power series `Σ (w+n)^{-2-k}` — a SHIFTED-BASE `(w+x)^{-a}`
    tail.  This subsection generalizes the engine to that base.  Crucially the exponent is kept REAL
    (`a : ℝ`, `a > 1`) — which is exactly the form the trigamma tail needs (`a = 2 + k ∈ ℕ`) — so
    the norm is `‖(w+x)^{-a}‖ = ‖w+x‖^{-a}` (`Complex.norm_cpow_real`, no `exp(arg·im)` factor), and
    the honest `N`-decay is driven by the base lower bound `‖w+x‖ ≥ Re(w+x) = Re w + x ≥ Re w + N`. -/

/- ## I. The K = 3 instance and THE NUMBER (the go/no-go for full reflection).

    The order-3 tail remainder integrand is `sawBernoulli 3 x · (c₃(s) · x^{-s-3})` where
    `c₃(s) = -s(s+1)(s+2)` is the coefficient of `x^{-s-3}` in `d³/dx³(x^{-s})`.  `em_tail_integral_bound`
    bounds this integral for ANY complex `c`; here we record it with the honest falling-factorial
    coefficient and the proven saw-3 sup bound `1/12`, then evaluate the numeric envelope at the G2
    pilot point `s = 1/2 + 14i` and certify a tail cut making it `< 10⁻³` (the K = 1 envelope
    `‖s‖/(2·Re s) ≈ 14` did NOT — see EMZetaComplex.em_zeta_strip_enclosure). -/

/- ## J. The order-2 windowed EM identity for the ζ integrand (complex).

    We raise the K=1 windowed complex EM identity (`euler_maclaurin_one_window_cpow` applied to
    `f x = (x:ℂ)^(-s)`) to order 2 using `em_saw_step_window` (real coefficients, applied to the
    real and imaginary parts — but here directly to the ℂ integrand via linearity of the identity
    over the real saw).  The order-2 remainder integrand carries the coefficient `c₂(s) = s(s+1)`.

    We give the complex σ-direction derivatives to order 2 (the inputs `em_saw_step_window` needs),
    then the windowed order-2 identity.  This is the reusable step; iterating once more gives order 3,
    and the `[N,∞)` limit yields the ζ representation. -/

/-- Second σ-direction derivative of `x^{-s}`: `d/dx(-s·x^{-s-1}) = s(s+1)·x^{-s-2}` for `x > 0`
    and `s ≠ -1` (so the intermediate exponent `-s-1 ≠ 0`; always holds on `Re s > 0`). -/
theorem hasDerivAt_cpow_neg2 {s : ℂ} (hs : s ≠ -1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => -s * (x : ℂ) ^ (-s - 1)) (s * (s + 1) * (x : ℂ) ^ (-s - 2)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hr : (-s - 1 : ℂ) ≠ 0 := by
    intro h; apply hs; linear_combination -h
  have hstep : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s - 1))
      ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) x := hasDerivAt_ofReal_cpow_const hx0 hr
  have hfull := hstep.const_mul (-s)
  have hval : (-s) * ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) = s * (s + 1) * (x : ℂ) ^ (-s - 2) := by
    rw [show (-s - 1 - 1 : ℂ) = -s - 2 by ring]; ring
  rw [hval] at hfull
  exact hfull

/- ### ℂ-valued saw-order-raising over a window (for the ζ integrand).

    The ℂ lift of `em_saw_step` and `em_saw_step_window`.  The saw factor `sawBernoulli k x` stays
    REAL (cast to ℂ); `fk, fk1` are ℂ-valued.  Proof structure is identical to the real versions
    with `linear_combination` in place of `linarith` for the final ℂ arithmetic. -/

/-- ℂ-valued one-step saw-order-raising over the unit cell `[m, m+1]`. -/
theorem em_saw_step_cpow (k : ℕ) (m : ℤ) (fk fk1 : ℝ → ℂ)
    (hd : ∀ x ∈ Icc (m : ℝ) (m + 1), HasDerivAt fk (fk1 x) x)
    (hi : IntervalIntegrable fk1 volume (m : ℝ) (m + 1)) :
    (∫ x in (m : ℝ)..(m + 1), (sawBernoulli k x : ℂ) * fk x)
      = ((bernoulliFun (k + 1) 1 : ℂ) * fk (m + 1) - (bernoulliFun (k + 1) 0 : ℂ) * fk m) / (k + 1)
        - (∫ x in (m : ℝ)..(m + 1), (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1) := by
  have hcc : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  -- ℂ-cast polynomial surrogate W x = B_{k+1}(x-m)/(k+1).
  set W : ℝ → ℂ := fun y => (bernoulliFun (k + 1) (y - m) / (k + 1) : ℝ) with hWdef
  have hW' : ∀ x, HasDerivAt W ((bernoulliFun k (x - m) : ℂ)) x := by
    intro x
    have hreal := sawSurrogate_hasDerivAt k m x
    have := hreal.ofReal_comp
    simpa [hWdef, sawSurrogate, Function.comp] using this
  have hWcont : Continuous W := by
    rw [hWdef]; fun_prop
  have huv : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt W ((bernoulliFun k (x - m) : ℂ)) x :=
    fun x _ => hW' x
  have hfd : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt fk (fk1 x) x := by
    intro x hx; rw [uIcc_of_le hcc] at hx; exact hd x hx
  have hW'int : IntervalIntegrable (fun x => (bernoulliFun k (x - m) : ℂ)) volume (m : ℝ) (m + 1) := by
    apply Continuous.intervalIntegrable; fun_prop
  have hIBP := integral_deriv_mul_eq_sub huv hfd hW'int hi
  have hWL : W (m : ℝ) = (bernoulliFun (k + 1) 0 : ℂ) / (k + 1) := by
    simp [hWdef]
  have hWR : W ((m : ℝ) + 1) = (bernoulliFun (k + 1) 1 : ℂ) / (k + 1) := by
    simp only [hWdef, add_sub_cancel_left]; push_cast; ring
  have hWfk1int : IntervalIntegrable (fun x => W x * fk1 x) volume (m : ℝ) (m + 1) :=
    hi.continuousOn_mul hWcont.continuousOn
  have hW'fkint : IntervalIntegrable (fun x => (bernoulliFun k (x - m) : ℂ) * fk x) volume (m : ℝ) (m + 1) := by
    have hfkcont : ContinuousOn fk (uIcc (m : ℝ) (m + 1)) := fun x hx =>
      (hfd x hx).continuousAt.continuousWithinAt
    exact (hfkcont.intervalIntegrable).continuousOn_mul (by fun_prop)
  have hsplit :
      (∫ x in (m : ℝ)..(m + 1), (bernoulliFun k (x - m) : ℂ) * fk x + W x * fk1 x)
        = (∫ x in (m : ℝ)..(m + 1), (bernoulliFun k (x - m) : ℂ) * fk x)
          + ∫ x in (m : ℝ)..(m + 1), W x * fk1 x := by
    rw [intervalIntegral.integral_add hW'fkint hWfk1int]
  have hsaw_k : (∫ x in (m : ℝ)..(m + 1), (sawBernoulli k x : ℂ) * fk x)
      = ∫ x in (m : ℝ)..(m + 1), (bernoulliFun k (x - m) : ℂ) * fk x := by
    apply intervalIntegral.integral_congr_ae
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨le_of_lt hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
    rw [sawBernoulli_eq_on_Ico k hxIco]
  have hsaw_k1 : (∫ x in (m : ℝ)..(m + 1), (sawBernoulli (k + 1) x : ℂ) * fk1 x)
      = ∫ x in (m : ℝ)..(m + 1), ((k + 1 : ℂ) * W x) * fk1 x := by
    apply intervalIntegral.integral_congr_ae
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨le_of_lt hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by
      have : ((k : ℝ) + 1) ≠ 0 := by positivity
      exact_mod_cast this
    rw [sawBernoulli_eq_on_Ico (k + 1) hxIco, hWdef]
    push_cast
    field_simp
  rw [hsaw_k]
  have key : (∫ x in (m : ℝ)..(m + 1), (bernoulliFun k (x - m) : ℂ) * fk x)
      + ∫ x in (m : ℝ)..(m + 1), W x * fk1 x
      = W ((m : ℝ) + 1) * fk ((m : ℝ) + 1) - W (m : ℝ) * fk (m : ℝ) := by
    rw [← hsplit]; exact hIBP
  rw [hWL, hWR] at key
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by
    have : ((k : ℝ) + 1) ≠ 0 := by positivity
    exact_mod_cast this
  rw [hsaw_k1]
  have hpull : (∫ x in (m : ℝ)..(m + 1), ((k + 1 : ℂ) * W x) * fk1 x)
      = ((k : ℂ) + 1) * ∫ x in (m : ℝ)..(m + 1), W x * fk1 x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _; push_cast; ring
  rw [hpull]
  have hcancel : (((k : ℂ) + 1) * ∫ x in (m : ℝ)..(m + 1), W x * fk1 x) / ((k : ℂ) + 1)
      = ∫ x in (m : ℝ)..(m + 1), W x * fk1 x := by
    rw [mul_comm]; exact mul_div_cancel_right₀ _ hk1
  rw [hcancel]
  push_cast
  linear_combination key

/-- ℂ-valued summed saw-order-raising over `[M, N]` (`k ≥ 1`).  ℂ lift of `em_saw_step_window`. -/
theorem em_saw_step_window_cpow {k : ℕ} (hk : 1 ≤ k) (M N : ℕ) (hMN : M ≤ N) (fk fk1 : ℝ → ℂ)
    (hd : ∀ x ∈ Icc (M : ℝ) N, HasDerivAt fk (fk1 x) x)
    (hi : ∀ j ∈ Finset.Ico M N, IntervalIntegrable fk1 volume (j : ℝ) (j + 1)) :
    (∫ x in (M : ℝ)..N, (sawBernoulli k x : ℂ) * fk x)
      = (bernoulliFun (k + 1) 0 : ℂ) * (fk N - fk M) / (k + 1)
        - (∫ x in (M : ℝ)..N, (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1) := by
  have hk1ne : k + 1 ≠ 1 := by omega
  have hendeq : (bernoulliFun (k + 1) 1 : ℂ) = (bernoulliFun (k + 1) 0 : ℂ) := by
    exact_mod_cast bernoulliFun_endpoints_eq_of_ne_one hk1ne
  have hcell : ∀ j ∈ Finset.Ico M N, ∀ x ∈ Icc (j : ℝ) (j + 1), HasDerivAt fk (fk1 x) x := by
    intro j hj x hx
    rw [Finset.mem_Ico] at hj
    refine hd x ⟨le_trans (by exact_mod_cast hj.1) hx.1, ?_⟩
    have : (j : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hj.2
    linarith [hx.2]
  have hstep : ∀ j ∈ Finset.Ico M N,
      (∫ x in (j : ℝ)..(j + 1), (sawBernoulli k x : ℂ) * fk x)
        = ((bernoulliFun (k + 1) 1 : ℂ) * fk (j + 1) - (bernoulliFun (k + 1) 0 : ℂ) * fk j) / (k + 1)
          - (∫ x in (j : ℝ)..(j + 1), (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1) := by
    intro j hj
    have hcast : (((j : ℤ)) : ℝ) = (j : ℝ) := by push_cast; ring
    have := em_saw_step_cpow k (j : ℤ) fk fk1
      (by intro x hx; rw [hcast] at hx; exact hcell j hj x hx)
      (by rw [hcast]; exact hi j hj)
    simpa [hcast] using this
  have hsum := Finset.sum_congr rfl hstep
  -- Integrability per cell (ℂ).
  have hint_k : ∀ j ∈ Finset.Ico M N,
      IntervalIntegrable (fun x => (sawBernoulli k x : ℂ) * fk x) volume (j : ℝ) (j + 1) := by
    intro j hj
    have hcc : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
    have hfkcont : ContinuousOn fk (Icc (j : ℝ) (j + 1)) :=
      fun x hx => (hcell j hj x hx).continuousAt.continuousWithinAt
    have hcont : IntervalIntegrable (fun x => (bernoulliFun k (x - j) : ℂ) * fk x) volume (j : ℝ) (j + 1) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hcc]
      exact (Continuous.continuousOn (by fun_prop)).mul hfkcont
    refine (intervalIntegrable_congr_ae ?_).mpr hcont
    have hnull : ∀ᵐ x, x ≠ ((j : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico ((j : ℤ) : ℝ) (((j : ℤ) : ℝ) + 1) := by
      refine ⟨?_, ?_⟩
      · have : (j : ℝ) < x := hxmem.1; push_cast; linarith
      · have hlt : x < (j : ℝ) + 1 := lt_of_le_of_ne hxmem.2 hxne; push_cast; linarith
    rw [sawBernoulli_eq_on_Ico k hxIco]; norm_num
  have htel_k : (∑ j ∈ Finset.Ico M N, ∫ x in (j : ℝ)..(j + 1), (sawBernoulli k x : ℂ) * fk x)
      = ∫ x in (M : ℝ)..N, (sawBernoulli k x : ℂ) * fk x := by
    have hint : ∀ j ∈ Set.Ico M N,
        IntervalIntegrable (fun x => (sawBernoulli k x : ℂ) * fk x) volume
          ((fun j : ℕ => (j : ℝ)) j) ((fun j : ℕ => (j : ℝ)) (j + 1)) := by
      intro j hj; simpa [Nat.cast_succ] using hint_k j (Finset.mem_Ico.mpr hj)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun j : ℕ => (j : ℝ)) (f := fun x => (sawBernoulli k x : ℂ) * fk x) (μ := volume) hMN hint
    simpa using this
  have hint_k1 : ∀ j ∈ Finset.Ico M N,
      IntervalIntegrable (fun x => (sawBernoulli (k + 1) x : ℂ) * fk1 x) volume (j : ℝ) (j + 1) := by
    intro j hj
    have hcc : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
    have hcont : IntervalIntegrable (fun x => (bernoulliFun (k + 1) (x - j) : ℂ) * fk1 x) volume
        (j : ℝ) (j + 1) := (hi j hj).continuousOn_mul (by fun_prop)
    refine (intervalIntegrable_congr_ae ?_).mpr hcont
    have hnull : ∀ᵐ x, x ≠ ((j : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico ((j : ℤ) : ℝ) (((j : ℤ) : ℝ) + 1) := by
      refine ⟨?_, ?_⟩
      · have : (j : ℝ) < x := hxmem.1; push_cast; linarith
      · have hlt : x < (j : ℝ) + 1 := lt_of_le_of_ne hxmem.2 hxne; push_cast; linarith
    rw [sawBernoulli_eq_on_Ico (k + 1) hxIco]; norm_num
  have htel_k1 : (∑ j ∈ Finset.Ico M N, ∫ x in (j : ℝ)..(j + 1), (sawBernoulli (k + 1) x : ℂ) * fk1 x)
      = ∫ x in (M : ℝ)..N, (sawBernoulli (k + 1) x : ℂ) * fk1 x := by
    have hint : ∀ j ∈ Set.Ico M N,
        IntervalIntegrable (fun x => (sawBernoulli (k + 1) x : ℂ) * fk1 x) volume
          ((fun j : ℕ => (j : ℝ)) j) ((fun j : ℕ => (j : ℝ)) (j + 1)) := by
      intro j hj; simpa [Nat.cast_succ] using hint_k1 j (Finset.mem_Ico.mpr hj)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun j : ℕ => (j : ℝ)) (f := fun x => (sawBernoulli (k + 1) x : ℂ) * fk1 x) (μ := volume) hMN hint
    simpa using this
  -- Boundary telescoping (ℂ).
  have hbdry : (∑ j ∈ Finset.Ico M N,
        ((bernoulliFun (k + 1) 1 : ℂ) * fk (j + 1) - (bernoulliFun (k + 1) 0 : ℂ) * fk j)) / (k + 1)
      = (bernoulliFun (k + 1) 0 : ℂ) * (fk N - fk M) / (k + 1) := by
    congr 1
    rw [hendeq]
    have hcongr : (∑ j ∈ Finset.Ico M N,
        ((bernoulliFun (k + 1) 0 : ℂ) * fk (j + 1) - (bernoulliFun (k + 1) 0 : ℂ) * fk j))
        = (∑ j ∈ Finset.Ico M N,
            (bernoulliFun (k + 1) 0 : ℂ) * (fk ((j : ℝ) + 1) - fk (j : ℝ))) := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hcongr, ← Finset.mul_sum, sum_telescope_diff_cpow fk hMN]
  rw [Finset.sum_sub_distrib] at hsum
  rw [← Finset.sum_div, ← Finset.sum_div, htel_k1, htel_k, hbdry] at hsum
  exact hsum

/- ## K. The order-2 tail identity for the ζ integrand, and its `[N, ∞)` form.

    Raising the K=1 saw remainder integrand `saw₁·(−s x^{−s−1})` to order 2 on the tail `[N, ∞)`.
    Over a finite window `[N, M]` this is `em_saw_step_window_cpow` (k=1); taking `M → ∞` (the K=1
    endpoint value `−s·M^{−s−1} → 0`, and both integrals converge for `Re s > 0`) yields
        ∫_N^∞ saw₁·(−s x^{−s−1})
          = B₂(0)·(s·N^{−s−1})/2  −  (∫_N^∞ saw₂·(s(s+1) x^{−s−2}))/2,
    with `B₂(0) = bernoulli 2 = 1/6`.  This is the order-2 tail EM step in closed form. -/

/-- Integrability of the order-2 tail integrand `saw₂·(s(s+1) x^{−s−2})` on `(N, ∞)` for
    `Re s > 0` (dominated by `(‖s(s+1)‖·(1/6)) x^{−Re s−2}`, exponent `< −1`). -/
theorem em_tail2_integrableOn {s : ℂ} {N : ℕ} (hN : 1 ≤ N) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (sawBernoulli 2 x : ℂ) * (s * (s + 1) * (x : ℂ) ^ (-s - 2))) (Ioi (N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hbase : IntegrableOn (fun x : ℝ => (‖s * (s + 1)‖ * (1 / 6)) * x ^ (-s.re - 2)) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -s.re - 2) (by linarith) hNpos).const_mul _
  refine Integrable.mono' hbase ?_ ?_
  · apply Measurable.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp (sawBernoulli_measurable 2)).mul
      (measurable_const.mul (Complex.measurable_ofReal.pow_const _))
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hxpos : (0 : ℝ) < x := lt_trans hNpos hx
    have hnormcpow : ‖(x : ℂ) ^ (-s - 2)‖ = x ^ (-s.re - 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      congr 1
    have hsaw := abs_sawBernoulli_two_le x
    have hrpownn : (0 : ℝ) ≤ x ^ (-s.re - 2) := Real.rpow_nonneg hxpos.le _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow]
    calc |sawBernoulli 2 x| * (‖s * (s + 1)‖ * x ^ (-s.re - 2))
        ≤ (1 / 6) * (‖s * (s + 1)‖ * x ^ (-s.re - 2)) := by gcongr
      _ = (‖s * (s + 1)‖ * (1 / 6)) * x ^ (-s.re - 2) := by ring

/-- The K=1 saw remainder integrand `saw₁·(−s x^{−s−1})` is integrable on `(N, ∞)` for `Re s > 0`
    (the `Ioi 1` version is `EMZetaComplex.em_cpow_remainder_integrableOn_strip`; the `Ioi N`
    version follows since `(N,∞) ⊆ (1,∞)` — but we reprove directly for a clean `N`-based form). -/
theorem em_tail1_integrableOn {s : ℂ} {N : ℕ} (hN : 1 ≤ N) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))) (Ioi (N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hbase : IntegrableOn (fun x : ℝ => (‖s‖ * (1 / 2)) * x ^ (-s.re - 1)) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -s.re - 1) (by linarith) hNpos).const_mul _
  refine Integrable.mono' hbase ?_ ?_
  · apply Measurable.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp (sawBernoulli_measurable 1)).mul
      (measurable_const.mul (Complex.measurable_ofReal.pow_const _))
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hxpos : (0 : ℝ) < x := lt_trans hNpos hx
    have hnormcpow : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.sub_re, Complex.neg_re, Complex.one_re]
    have hsaw := abs_sawBernoulli_one_le x
    have hrpownn : (0 : ℝ) ≤ x ^ (-s.re - 1) := Real.rpow_nonneg hxpos.le _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow, norm_neg]
    calc |sawBernoulli 1 x| * (‖s‖ * x ^ (-s.re - 1))
        ≤ (1 / 2) * (‖s‖ * x ^ (-s.re - 1)) := by gcongr
      _ = (‖s‖ * (1 / 2)) * x ^ (-s.re - 1) := by ring

/-- **Order-2 tail EM step** (closed form).  For `Re s > 0`, `N ≥ 1`, `s ≠ -1`:
        ∫_N^∞ saw₁·(−s x^{−s−1})
          = (bernoulli 2 : ℂ)·(s·N^{−s−1})/2  −  (∫_N^∞ saw₂·(s(s+1) x^{−s−2}))/2.
    Proven by `em_saw_step_window_cpow` (k=1) over `[N,M]` and `M → ∞`. -/
theorem em_tail2_step {s : ℂ} {N : ℕ} (hN : 1 ≤ N) (hs : 0 < s.re) (hs1 : s ≠ -1) :
    (∫ x in Ioi (N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      = (bernoulli 2 : ℂ) * (s * (N : ℝ) ^ (-s - 1)) / 2
        - (∫ x in Ioi (N : ℝ), (sawBernoulli 2 x : ℂ) * (s * (s + 1) * (x : ℂ) ^ (-s - 2))) / 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  set fk : ℝ → ℂ := fun x => -s * (x : ℂ) ^ (-s - 1) with hfk
  set fk1 : ℝ → ℂ := fun x => s * (s + 1) * (x : ℂ) ^ (-s - 2) with hfk1
  have hI1 := em_tail1_integrableOn hN hs
  have hI2 := em_tail2_integrableOn hN hs
  -- Finite-window identity for M ≥ N.
  have hwin : ∀ M : ℕ, N ≤ M →
      (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 1 x : ℂ) * fk x)
        = (6⁻¹ : ℂ) * (fk M - fk N) / (1 + 1)
          - (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 2 x : ℂ) * fk1 x) / (1 + 1) := by
    intro M hM
    have hd : ∀ x ∈ Icc (N : ℝ) M, HasDerivAt fk (fk1 x) x := by
      intro x hx
      have hx1 : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hN) hx.1
      exact hasDerivAt_cpow_neg2 hs1 (lt_of_lt_of_le zero_lt_one hx1)
    have hi : ∀ j ∈ Finset.Ico N M, IntervalIntegrable fk1 volume (j : ℝ) (j + 1) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast le_trans hN hj.1
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by linarith)]
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
      intro x hx
      have : (1 : ℝ) ≤ x := le_trans hj1 hx.1
      exact Or.inl (by simp only [Complex.ofReal_re]; linarith)
    have hstep := em_saw_step_window_cpow (k := 1) le_rfl N M hM fk fk1 hd hi
    have hb2 : (bernoulliFun (1 + 1) 0 : ℂ) = 6⁻¹ := by
      norm_num [bernoulliFun_eval_zero]
    rw [hb2] at hstep
    have h2 : (1 : ℕ) + 1 = 2 := rfl
    rw [h2] at hstep
    convert hstep using 3 <;> norm_num
  -- Limits as M → ∞ (over ℕ).
  have hA : Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 1 x : ℂ) * fk x) atTop
      (𝓝 (∫ x in Ioi (N : ℝ), (sawBernoulli 1 x : ℂ) * fk x)) :=
    intervalIntegral_tendsto_integral_Ioi N hI1 tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 2 x : ℂ) * fk1 x) atTop
      (𝓝 (∫ x in Ioi (N : ℝ), (sawBernoulli 2 x : ℂ) * fk1 x)) :=
    intervalIntegral_tendsto_integral_Ioi N hI2 tendsto_natCast_atTop_atTop
  -- endpoint `fk M = -s·M^{-s-1} → 0`.
  have hEnd0 : Tendsto (fun M : ℕ => fk (M : ℝ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : (fun M : ℕ => ‖fk (M : ℝ)‖) =ᶠ[atTop] (fun M : ℕ => ‖s‖ * (M : ℝ) ^ (-s.re - 1)) := by
      filter_upwards [eventually_gt_atTop 0] with M hM
      have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
      rw [hfk, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hMpos,
        Complex.sub_re, Complex.neg_re, Complex.one_re]
    refine Tendsto.congr' hnorm.symm ?_
    have hz : Tendsto (fun M : ℕ => (M : ℝ) ^ (-s.re - 1)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun M : ℕ => (M : ℝ) ^ (-(s.re + 1))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (y := s.re + 1) (by linarith)).comp tendsto_natCast_atTop_atTop
      refine h0.congr (fun M => ?_)
      rw [show -(s.re + 1) = -s.re - 1 by ring]
    simpa using hz.const_mul ‖s‖
  -- The RHS of the finite identity converges to the claimed limit.
  have hRHS : Tendsto (fun M : ℕ =>
      (6⁻¹ : ℂ) * (fk M - fk N) / (1 + 1)
        - (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 2 x : ℂ) * fk1 x) / (1 + 1)) atTop
      (𝓝 ((6⁻¹ : ℂ) * (0 - fk N) / (1 + 1)
        - (∫ x in Ioi (N : ℝ), (sawBernoulli 2 x : ℂ) * fk1 x) / (1 + 1))) := by
    apply Tendsto.sub
    · apply Tendsto.div_const
      apply Tendsto.const_mul
      exact hEnd0.sub_const (fk N)
    · exact hB.div_const (1 + 1)
  have hEq : ∀ᶠ M : ℕ in atTop,
      (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 1 x : ℂ) * fk x)
        = (6⁻¹ : ℂ) * (fk M - fk N) / (1 + 1)
          - (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 2 x : ℂ) * fk1 x) / (1 + 1) := by
    filter_upwards [eventually_ge_atTop N] with M hM using hwin M hM
  have hlim := tendsto_nhds_unique (hA.congr' hEq) hRHS
  rw [hlim, hfk]
  have hbern2 : (bernoulli 2 : ℂ) = 6⁻¹ := by norm_num
  rw [hbern2]
  push_cast
  ring

/- ## L. The assembled order-3 tail identity and the ζ enclosure (checkBand consumer form). -/

end LeanClassics.DavenportHeilbronn.EM
end

-- ===== PowerfulFC.ZetaPartial =====
section
/-
# Partial sums of `n^{-s}` against `ζ(s)` in the strip, second order (rung BG0)

For `Re s > 0`, `s ≠ 1` and real `z ≥ 1`,

  `∑_{1 ≤ n ≤ z} n^{-s} = ζ(s) + z^{1-s}/(1-s) − ψ(z) z^{-s} + R`,   `ψ(z) = {z} − 1/2`,
  `‖R‖ ≤ (7‖s‖/12 + ‖s(s+1)‖/(12(Re s + 1))) z^{-Re s - 1}`,

with `ζ` Mathlib's `riemannZeta` (analytic continuation). For real `σ` the bound is `(2σ/3) z^{-σ-1}`
and `ζ(σ)` is real. At `σ = 2/3` this identifies Bateman–Grosswald's second constant: `ζ(2/3)` is the
constant term of `∑_{a ≤ z} a^{-2/3} − 3 z^{1/3}` (`sum_two_thirds`); at `σ = 3/2` it gives
`∑_{b ≤ z} b^{-3/2} = ζ(3/2) − 2 z^{-1/2} − ψ(z) z^{-3/2} + O(z^{-5/2})` (`sum_three_halves`).

Proof. With `M = ⌊z⌋ + 1`: Euler–Maclaurin on `[1, M]` (`em_cpow_partial`), `ζ(s) = 1/(s−1) + 1/2 +
∫_1^∞ saw₁ (−s x^{−s−1})` (`em_zeta_strip`, continuation by the identity theorem), and one more
integration by parts on `[M, ∞)` (`em_tail2_step`) give the identity at the integer `M` with remainder
`O(M^{−σ−1})`. The function `G(t) = t^{1−s}/(1−s) − (t − M + 1/2) t^{−s}` has `G'(t) = s (t − M + 1/2)
t^{−s−1}`, so moving from `M` down to `z ∈ [M − 1, M)` costs at most `(‖s‖/2) z^{−σ−1}` (mean value
theorem). The second order (the `ψ(z) z^{-s}` term) is what Bateman–Grosswald needs: a first-order
`O(z^{-σ})` would leave an `O(y^{1/5})` error in each hyperbola count.
-/

open Complex MeasureTheory Set Filter
open LeanClassics.DavenportHeilbronn.EM

noncomputable section

namespace PowerfulFC.ZetaPartial

/-- `ζ(σ)` is real for real `σ`. -/
theorem riemannZeta_ofReal_im (σ : ℝ) : (riemannZeta σ).im = 0 := by
  have h := riemannZeta_conj (σ : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

theorem riemannZeta_ofReal_eq (σ : ℝ) : riemannZeta σ = ((riemannZeta σ).re : ℂ) := by
  apply Complex.ext <;> simp [riemannZeta_ofReal_im]

/-- The identity at an integer `M ≥ 1`: `∑_{n < M} n^{-s} = ζ(s) + M^{1−s}/(1−s) − M^{−s}/2 − T(M)`,
`T(M) = ∫_M^∞ saw₁ · (−s x^{−s−1})`. -/
theorem partial_eq_integer {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {M : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-s))
      = riemannZeta s + ((M : ℝ) : ℂ) ^ (1 - s) / (1 - s) - ((M : ℝ) : ℂ) ^ (-s) / 2
        - ∫ x in Ioi (M : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hP := em_cpow_partial hs0 hM
  have hZ := em_zeta_strip hs hs1
  have h1M : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hI1_Ioi : IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))) (Ioi 1) :=
    em_cpow_remainder_integrableOn_strip hs
  have hsplit : (∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      = (∫ x in (1 : ℝ)..(M : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
        + ∫ x in Ioi (M : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
    have hIcc : IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
        (Ioc 1 M) := hI1_Ioi.mono_set Ioc_subset_Ioi_self
    have hIoiM : IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
        (Ioi M) := hI1_Ioi.mono_set (Ioi_subset_Ioi h1M)
    rw [← Set.Ioc_union_Ioi_eq_Ioi h1M,
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIcc hIoiM,
      intervalIntegral.integral_of_le h1M]
  have hpow : (∫ x in (1 : ℝ)..(M : ℝ), (x : ℂ) ^ (-s))
      = (((M : ℝ) : ℂ) ^ (1 - s) - 1) / (1 - s) := by
    have hr : (-s) ≠ -1 := by intro h; exact hs1 (by linear_combination -h)
    have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (M : ℝ) := by
      rw [uIcc_of_le h1M]; intro h; linarith [h.1]
    rw [integral_cpow (Or.inr ⟨hr, h0⟩)]
    have e : -s + 1 = 1 - s := by ring
    rw [e]; simp
  have hsm1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hsm1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [hP, hpow, hZ, hsplit]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  field_simp
  ring

/-- `‖T(M)‖ ≤ (‖s‖/12 + ‖s(s+1)‖/(12(σ+1))) M^{−σ−1}` (one more integration by parts). -/
theorem norm_tail_le {s : ℂ} (hs : 0 < s.re) {M : ℕ} (hM : 1 ≤ M) :
    ‖∫ x in Ioi (M : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))‖
      ≤ (‖s‖ / 12 + ‖s * (s + 1)‖ / (12 * (s.re + 1))) * (M : ℝ) ^ (-s.re - 1) := by
  have hs1 : s ≠ -1 := by rintro rfl; norm_num at hs
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  rw [em_tail2_step hM hs hs1]
  have hB := em_tail_integral_bound (k := 2) (s := s) (c := s * (s + 1)) (B := 1 / 6) hM
    (by push_cast; linarith) (by norm_num) abs_sawBernoulli_two_le
  have e2 : ((2 : ℕ) : ℂ) = 2 := by norm_num
  simp only [e2, Nat.cast_ofNat] at hB
  have hpowM : ‖((M : ℝ) : ℂ) ^ (-s - 1)‖ = (M : ℝ) ^ (-s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hMpos]; simp
  have hexp : -(s.re + 2 - 1) = -s.re - 1 := by ring
  rw [hexp] at hB
  have hb2 : (bernoulli 2 : ℂ) = 6⁻¹ := by norm_num
  calc ‖(bernoulli 2 : ℂ) * (s * ((M : ℝ) : ℂ) ^ (-s - 1)) / 2
          - (∫ x in Ioi (M : ℝ), (sawBernoulli 2 x : ℂ) * (s * (s + 1) * (x : ℂ) ^ (-s - 2))) / 2‖
        ≤ ‖(bernoulli 2 : ℂ) * (s * ((M : ℝ) : ℂ) ^ (-s - 1)) / 2‖
          + ‖(∫ x in Ioi (M : ℝ), (sawBernoulli 2 x : ℂ) * (s * (s + 1) * (x : ℂ) ^ (-s - 2))) / 2‖ :=
          norm_sub_le _ _
    _ ≤ ‖s‖ / 12 * (M : ℝ) ^ (-s.re - 1)
          + (1 / 6 * ‖s * (s + 1)‖ * (M : ℝ) ^ (-s.re - 1) / (s.re + 2 - 1)) / 2 := by
          gcongr
          · rw [hb2, norm_div, norm_mul, norm_mul, hpowM]; simp; ring_nf; rfl
          · rw [norm_div]; simp only [Complex.norm_ofNat]; gcongr
    _ = (‖s‖ / 12 + ‖s * (s + 1)‖ / (12 * (s.re + 1))) * (M : ℝ) ^ (-s.re - 1) := by
          have : s.re + 1 ≠ 0 := by linarith
          rw [show s.re + 2 - 1 = s.re + 1 by ring]
          generalize ‖s * (s + 1)‖ = C
          generalize (M : ℝ) ^ (-s.re - 1) = P
          field_simp
          ring

/-- The interpolation function `G(t) = t^{1−s}/(1−s) − (t − M + 1/2) t^{−s}`. -/
def G (s : ℂ) (M : ℝ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (1 - s) / (1 - s) - ((t : ℂ) - M + 1 / 2) * (t : ℂ) ^ (-s)

theorem hasDerivAt_G {s : ℂ} (hs1 : s ≠ 1) (M : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (G s M) (s * ((t : ℂ) - M + 1 / 2) * (t : ℂ) ^ (-s - 1)) t := by
  have hsm1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have ht0 : t ≠ 0 := ht.ne'
  have h1 := hasDerivAt_ofReal_cpow_const (x := t) ht0 (r := 1 - s) hsm1
  have h2 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s)) (-s * (t : ℂ) ^ (-s - 1)) t := by
    by_cases hs0 : s = 0
    · subst hs0; simpa using hasDerivAt_const t (1 : ℂ)
    · exact hasDerivAt_cpow_neg hs0 ht
  have h3 : HasDerivAt (fun x : ℝ => (x : ℂ) - M + 1 / 2) 1 t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).sub_const (M : ℂ)).add_const (1 / 2 : ℂ)
  have h : HasDerivAt (G s M) _ t := (h1.div_const (1 - s)).sub (h3.mul h2)
  convert h using 1
  have e : (1 - s - 1) = -s := by ring
  rw [e]
  field_simp
  ring

/-- Moving from the integer `M` down to `z ∈ [M − 1, M]`. -/
theorem norm_G_sub_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {M z : ℝ} (hz0 : 0 < z)
    (hzM : z ≤ M) (hMz : M - 1 ≤ z) :
    ‖G s M M - G s M z‖ ≤ ‖s‖ / 2 * z ^ (-s.re - 1) := by
  have hderiv : ∀ x ∈ Icc z M, HasDerivWithinAt (G s M)
      (s * ((x : ℂ) - M + 1 / 2) * (x : ℂ) ^ (-s - 1)) (Icc z M) x :=
    fun x hx => (hasDerivAt_G hs1 M (lt_of_lt_of_le hz0 hx.1)).hasDerivWithinAt
  have hbound : ∀ x ∈ Ico z M, ‖s * ((x : ℂ) - M + 1 / 2) * (x : ℂ) ^ (-s - 1)‖
      ≤ ‖s‖ / 2 * z ^ (-s.re - 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hz0 hx.1
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    have hmid : ‖(x : ℂ) - M + 1 / 2‖ ≤ 1 / 2 := by
      have : (x : ℂ) - M + 1 / 2 = ((x - M + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have hpow : x ^ (-s.re - 1) ≤ z ^ (-s.re - 1) :=
      Real.rpow_le_rpow_of_nonpos hz0 hx.1 (by linarith)
    calc ‖s‖ * ‖(x : ℂ) - M + 1 / 2‖ * x ^ (-s.re - 1)
        ≤ ‖s‖ * (1 / 2) * z ^ (-s.re - 1) := by gcongr
      _ = ‖s‖ / 2 * z ^ (-s.re - 1) := by ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound M ⟨hzM, le_rfl⟩
  calc ‖G s M M - G s M z‖ ≤ ‖s‖ / 2 * z ^ (-s.re - 1) * (M - z) := h
    _ ≤ ‖s‖ / 2 * z ^ (-s.re - 1) * 1 := by
        gcongr
        linarith
    _ = ‖s‖ / 2 * z ^ (-s.re - 1) := mul_one _

/-- **BG0, complex form.** For `Re s > 0`, `s ≠ 1`, real `z ≥ 1`:
`‖∑_{1 ≤ n ≤ z} n^{-s} − (ζ(s) + z^{1−s}/(1−s) − ({z} − 1/2) z^{−s})‖
  ≤ (7‖s‖/12 + ‖s(s+1)‖/(12(Re s + 1))) z^{−Re s − 1}`. -/
theorem norm_sum_sub_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {z : ℝ} (hz : 1 ≤ z) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊z⌋₊, (n : ℂ) ^ (-s))
        - (riemannZeta s + (z : ℂ) ^ (1 - s) / (1 - s) - ((Int.fract z : ℝ) - 1 / 2 : ℂ) * (z : ℂ) ^ (-s))‖
      ≤ (7 * ‖s‖ / 12 + ‖s * (s + 1)‖ / (12 * (s.re + 1))) * z ^ (-s.re - 1) := by
  set N := ⌊z⌋₊ with hN
  have hz0 : 0 < z := by linarith
  have hN1 : 1 ≤ N := Nat.le_floor (by simpa using hz)
  have hNz : (N : ℝ) ≤ z := Nat.floor_le hz0.le
  have hzN : z < (N : ℝ) + 1 := Nat.lt_floor_add_one z
  have hM : 1 ≤ N + 1 := by omega
  have hId := partial_eq_integer hs hs1 hM
  have hIco : Finset.Ico 1 (N + 1) = Finset.Icc 1 N := rfl
  rw [hIco] at hId
  have hfract : Int.fract z = z - N := by
    rw [Int.fract, show (⌊z⌋ : ℝ) = (N : ℝ) by rw [hN, ← Int.natCast_floor_eq_floor hz0.le]; rfl]
  have hGM : G s ((N + 1 : ℕ) : ℝ) ((N + 1 : ℕ) : ℝ)
      = (((N + 1 : ℕ) : ℝ) : ℂ) ^ (1 - s) / (1 - s) - (((N + 1 : ℕ) : ℝ) : ℂ) ^ (-s) / 2 := by
    unfold G; ring
  have hGz : G s ((N + 1 : ℕ) : ℝ) z
      = (z : ℂ) ^ (1 - s) / (1 - s) - ((Int.fract z : ℝ) - 1 / 2 : ℂ) * (z : ℂ) ^ (-s) := by
    unfold G; rw [hfract]; push_cast; ring
  have hkey : (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s))
      - (riemannZeta s + (z : ℂ) ^ (1 - s) / (1 - s) - ((Int.fract z : ℝ) - 1 / 2 : ℂ) * (z : ℂ) ^ (-s))
      = (G s ((N + 1 : ℕ) : ℝ) ((N + 1 : ℕ) : ℝ) - G s ((N + 1 : ℕ) : ℝ) z)
        - ∫ x in Ioi ((N + 1 : ℕ) : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
    rw [hId, hGM, hGz]; ring
  rw [hkey]
  have hMz : ((N + 1 : ℕ) : ℝ) - 1 ≤ z := by push_cast; linarith
  have hzM : z ≤ ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
  have h1 := norm_G_sub_le hs hs1 hz0 hzM hMz
  have h2 := norm_tail_le hs hM
  have hpow : ((N + 1 : ℕ) : ℝ) ^ (-s.re - 1) ≤ z ^ (-s.re - 1) :=
    Real.rpow_le_rpow_of_nonpos hz0 hzM (by linarith)
  have hc : 0 ≤ ‖s‖ / 12 + ‖s * (s + 1)‖ / (12 * (s.re + 1)) := by
    have : 0 < s.re + 1 := by linarith
    positivity
  calc _ ≤ ‖G s ((N + 1 : ℕ) : ℝ) ((N + 1 : ℕ) : ℝ) - G s ((N + 1 : ℕ) : ℝ) z‖
          + ‖∫ x in Ioi ((N + 1 : ℕ) : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))‖ :=
        norm_sub_le _ _
    _ ≤ ‖s‖ / 2 * z ^ (-s.re - 1)
          + (‖s‖ / 12 + ‖s * (s + 1)‖ / (12 * (s.re + 1))) * z ^ (-s.re - 1) := by
        gcongr
        exact h2.trans (mul_le_mul_of_nonneg_left hpow hc)
    _ = (7 * ‖s‖ / 12 + ‖s * (s + 1)‖ / (12 * (s.re + 1))) * z ^ (-s.re - 1) := by ring

/-- **BG0, real form.** For real `σ > 0`, `σ ≠ 1`, real `z ≥ 1`:
`|∑_{1 ≤ n ≤ z} n^{-σ} − (ζ(σ) + z^{1−σ}/(1−σ) − ({z} − 1/2) z^{−σ})| ≤ (2σ/3) z^{−σ−1}`. -/
theorem abs_sum_sub_le {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) {z : ℝ} (hz : 1 ≤ z) :
    |(∑ n ∈ Finset.Icc 1 ⌊z⌋₊, (n : ℝ) ^ (-σ))
        - ((riemannZeta σ).re + z ^ (1 - σ) / (1 - σ) - (Int.fract z - 1 / 2) * z ^ (-σ))|
      ≤ 2 * σ / 3 * z ^ (-σ - 1) := by
  have hz0 : 0 < z := by linarith
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ1
  have h := norm_sum_sub_le hs hs1 hz
  have hcast : (∑ n ∈ Finset.Icc 1 ⌊z⌋₊, (n : ℂ) ^ (-(σ : ℂ)))
      - (riemannZeta σ + (z : ℂ) ^ (1 - (σ : ℂ)) / (1 - σ)
          - ((Int.fract z : ℝ) - 1 / 2 : ℂ) * (z : ℂ) ^ (-(σ : ℂ)))
      = (((∑ n ∈ Finset.Icc 1 ⌊z⌋₊, (n : ℝ) ^ (-σ))
        - ((riemannZeta σ).re + z ^ (1 - σ) / (1 - σ) - (Int.fract z - 1 / 2) * z ^ (-σ)) : ℝ) : ℂ) := by
    rw [riemannZeta_ofReal_eq σ]
    push_cast
    congr 1
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; push_cast; rfl
    · rw [Complex.ofReal_cpow hz0.le, Complex.ofReal_cpow hz0.le]; push_cast; rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  have hn : ‖(σ : ℂ)‖ = σ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]
  have hn2 : ‖(σ : ℂ) * ((σ : ℂ) + 1)‖ = σ * (σ + 1) := by
    rw [show (σ : ℂ) * ((σ : ℂ) + 1) = ((σ * (σ + 1) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hn, hn2]
  simp only [Complex.ofReal_re]
  have : σ + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **ζ(2/3) identification** (Bateman–Grosswald's second constant): for real `z ≥ 1`,
`|∑_{1 ≤ a ≤ z} a^{-2/3} − (3 z^{1/3} + ζ(2/3) − ({z} − 1/2) z^{-2/3})| ≤ (4/9) z^{-5/3}`. -/
theorem sum_two_thirds {z : ℝ} (hz : 1 ≤ z) :
    |(∑ n ∈ Finset.Icc 1 ⌊z⌋₊, (n : ℝ) ^ (-(2 / 3 : ℝ)))
        - (3 * z ^ ((1 : ℝ) / 3) + (riemannZeta (2 / 3)).re - (Int.fract z - 1 / 2) * z ^ (-(2 / 3 : ℝ)))|
      ≤ 4 / 9 * z ^ (-(5 / 3 : ℝ)) := by
  have h := abs_sum_sub_le (σ := 2 / 3) (by norm_num) (by norm_num) hz
  rw [show ((2 / 3 : ℝ) : ℂ) = 2 / 3 by push_cast; ring] at h
  rw [show (1 : ℝ) - 2 / 3 = 1 / 3 by norm_num, show -(2 / 3 : ℝ) - 1 = -(5 / 3) by norm_num] at h
  convert h using 2
  · ring
  · norm_num

/-- `∑_{1 ≤ b ≤ z} b^{-3/2} = ζ(3/2) − 2 z^{-1/2} − ({z} − 1/2) z^{-3/2} + O(z^{-5/2})`, constant 1. -/
theorem sum_three_halves {z : ℝ} (hz : 1 ≤ z) :
    |(∑ n ∈ Finset.Icc 1 ⌊z⌋₊, (n : ℝ) ^ (-(3 / 2 : ℝ)))
        - ((riemannZeta (3 / 2)).re - 2 * z ^ (-(1 / 2 : ℝ)) - (Int.fract z - 1 / 2) * z ^ (-(3 / 2 : ℝ)))|
      ≤ z ^ (-(5 / 2 : ℝ)) := by
  have h := abs_sum_sub_le (σ := 3 / 2) (by norm_num) (by norm_num) hz
  rw [show ((3 / 2 : ℝ) : ℂ) = 3 / 2 by push_cast; ring] at h
  rw [show (1 : ℝ) - 3 / 2 = -(1 / 2) by norm_num, show -(3 / 2 : ℝ) - 1 = -(5 / 2) by norm_num] at h
  refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
  · congr 2; ring
  · norm_num

end PowerfulFC.ZetaPartial
end
end


-- ===== PowerfulFC.Decomp =====
section
/-
# Powerful numbers are exactly `a² b³` with `b` squarefree, uniquely
-/

namespace PowerfulFC

lemma powerful_sq_mul_cube (a b : ℕ) : (a ^ 2 * b ^ 3).Powerful := by
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ a ^ 2 * b ^ 3 := Nat.dvd_of_mem_primeFactors hp
  rcases (Nat.Prime.dvd_mul hpp).1 hdvd with h | h
  · exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (hpp.dvd_of_dvd_pow h) 2) _
  · refine Dvd.dvd.mul_left ?_ _
    exact (pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans (pow_dvd_pow_of_dvd (hpp.dvd_of_dvd_pow h) 3)

/-- The exponent of `p` in `m² s` with `s` squarefree has parity `s.factorization p`. -/
lemma factorization_sq_mul_sqfree {m s : ℕ} (hm : m ≠ 0) (hs : Squarefree s) (p : ℕ) :
    s.factorization p = (m ^ 2 * s).factorization p % 2 := by
  have hs0 : s ≠ 0 := hs.ne_zero
  rw [Nat.factorization_mul (pow_ne_zero 2 hm) hs0, Nat.factorization_pow]
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : s.factorization p ≤ 1 := hs.natFactorization_le_one p
  omega

lemma sqfree_unique {m s m' s' : ℕ} (hm : m ≠ 0) (hm' : m' ≠ 0) (hs : Squarefree s)
    (hs' : Squarefree s') (h : m ^ 2 * s = m' ^ 2 * s') : s = s' := by
  apply Nat.eq_of_factorization_eq hs.ne_zero hs'.ne_zero
  intro p
  rw [factorization_sq_mul_sqfree hm hs, factorization_sq_mul_sqfree hm' hs', h]

lemma decomp_unique {a b c d : ℕ} (ha : a ≠ 0) (hc : c ≠ 0) (hb : Squarefree b) (hd : Squarefree d)
    (h : a ^ 2 * b ^ 3 = c ^ 2 * d ^ 3) : a = c ∧ b = d := by
  have hb0 : b ≠ 0 := hb.ne_zero
  have hd0 : d ≠ 0 := hd.ne_zero
  have hbd : b = d := by
    refine sqfree_unique (m := a * b) (m' := c * d) (mul_ne_zero ha hb0) (mul_ne_zero hc hd0) hb hd ?_
    calc (a * b) ^ 2 * b = a ^ 2 * b ^ 3 := by ring
      _ = c ^ 2 * d ^ 3 := h
      _ = (c * d) ^ 2 * d := by ring
  subst hbd
  refine ⟨?_, rfl⟩
  have h2 : a ^ 2 = c ^ 2 := Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.pos_of_ne_zero hb0) 3) h
  exact Nat.pow_left_injective (by norm_num) h2

lemma exists_decomp {n : ℕ} (hn : n ≠ 0) (hP : n.Powerful) :
    ∃ a b : ℕ, 0 < a ∧ Squarefree b ∧ a ^ 2 * b ^ 3 = n := by
  obtain ⟨s, m, hs0, hm0, hmn, hs⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hn)
  -- every prime factor of `s` divides `m`
  have hsm : s ∣ m := by
    rw [← Nat.factorization_le_iff_dvd hs0.ne' hm0.ne']
    intro p
    have h1 : s.factorization p ≤ 1 := hs.natFactorization_le_one p
    rcases Nat.lt_or_ge (s.factorization p) 1 with h0 | h0
    · omega
    · have hps : p ∣ s := Nat.dvd_of_factorization_pos (by omega)
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization s ▸
        Finsupp.mem_support_iff.2 (by omega))
      have hpn : p ∣ n := hmn ▸ Dvd.dvd.mul_left hps _
      have hp2 : p ^ 2 ∣ m ^ 2 * s := hmn ▸ hP p (Nat.mem_primeFactors.2 ⟨hpp, hpn, hn⟩)
      have hpm : p ∣ m := by
        by_contra hpm
        have hcop : (p ^ 2).Coprime (m ^ 2) :=
          Nat.Coprime.pow 2 2 ((Nat.Prime.coprime_iff_not_dvd hpp).2 hpm)
        have : p * p ∣ s := by
          rw [← pow_two]; exact hcop.dvd_of_dvd_mul_left hp2
        exact hpp.one_lt.ne' (Nat.isUnit_iff.1 (hs p this))
      have := (Nat.Prime.factorization_pos_of_dvd hpp hm0.ne' hpm)
      omega
  obtain ⟨c, rfl⟩ := hsm
  refine ⟨c, s, Nat.pos_of_ne_zero (by rintro rfl; simp at hm0), hs, ?_⟩
  rw [← hmn]; ring

end PowerfulFC
end

-- ===== PowerfulFC.Count =====
section
/-
# `#{n ≤ N powerful} = ∑_{b ≤ K squarefree} ⌊√(N / b³)⌋`
-/

open Finset

namespace PowerfulFC

lemma card_filter_sq_mul_cube_le (N b : ℕ) (hb : 0 < b) :
    #{a ∈ Icc 1 N | a ^ 2 * b ^ 3 ≤ N} = Nat.sqrt (N / b ^ 3) := by
  have hb3 : 0 < b ^ 3 := pow_pos hb 3
  have : ({a ∈ Icc 1 N | a ^ 2 * b ^ 3 ≤ N} : Finset ℕ) = Icc 1 (Nat.sqrt (N / b ^ 3)) := by
    ext a
    simp only [mem_filter, mem_Icc]
    rw [Nat.le_sqrt', Nat.le_div_iff_mul_le hb3]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      calc a ≤ a ^ 2 := by nlinarith
        _ ≤ a ^ 2 * b ^ 3 := Nat.le_mul_of_pos_right _ hb3
        _ ≤ N := h3
  rw [this, Nat.card_Icc]; omega

/-- The count of powerful numbers in `[1, N]`, given any `K` with `b³ ≤ N → b ≤ K`. -/
theorem card_powerful_eq_sum (N K : ℕ) (hK : ∀ b, 1 ≤ b → b ^ 3 ≤ N → b ≤ K) :
    #{n ∈ Icc 1 N | n.Powerful} =
      ∑ b ∈ {b ∈ Icc 1 K | Squarefree b}, Nat.sqrt (N / b ^ 3) := by
  set T : Finset (ℕ × ℕ) :=
    {p ∈ Icc 1 N ×ˢ Icc 1 K | Squarefree p.2 ∧ p.1 ^ 2 * p.2 ^ 3 ≤ N} with hT
  have himage : T.image (fun p => p.1 ^ 2 * p.2 ^ 3) = {n ∈ Icc 1 N | n.Powerful} := by
    ext n
    simp only [hT, mem_image, mem_filter, mem_product, mem_Icc, Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨⟨⟨ha1, _⟩, hb1, _⟩, _, hle⟩, rfl⟩
      refine ⟨⟨?_, hle⟩, powerful_sq_mul_cube a b⟩
      exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega)))
    · rintro ⟨⟨hn1, hnN⟩, hP⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := exists_decomp (by omega) hP
      have hb0 : 0 < b := Nat.pos_of_ne_zero hb.ne_zero
      have hb3 : 0 < b ^ 3 := pow_pos hb0 3
      have ha2 : 0 < a ^ 2 := pow_pos ha 2
      refine ⟨a, b, ⟨⟨⟨ha, ?_⟩, hb0, hK b hb0 ?_⟩, hb, hnN⟩, rfl⟩
      · calc a ≤ a ^ 2 := by nlinarith
          _ ≤ a ^ 2 * b ^ 3 := Nat.le_mul_of_pos_right _ hb3
          _ ≤ N := hnN
      · calc b ^ 3 ≤ a ^ 2 * b ^ 3 := Nat.le_mul_of_pos_left _ ha2
          _ ≤ N := hnN
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 ^ 2 * p.2 ^ 3) T := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
    simp only [hT, coe_filter, mem_product, mem_Icc, Set.mem_ofPred_eq] at hab hcd
    obtain ⟨h1, h2⟩ := decomp_unique (by omega) (by omega) hab.2.1 hcd.2.1 h
    exact Prod.ext h1 h2
  rw [← himage, card_image_of_injOn hinj]
  rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := {b ∈ Icc 1 K | Squarefree b})]
  · refine sum_congr rfl fun b hb => ?_
    simp only [mem_filter, mem_Icc] at hb
    rw [← card_filter_sq_mul_cube_le N b (by omega)]
    refine card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      simp only [hT, mem_filter, mem_product, mem_Icc] at hp ⊢
      obtain ⟨⟨⟨⟨h1, h2⟩, _⟩, _, h4⟩, h5⟩ := hp
      exact ⟨⟨h1, h2⟩, h5 ▸ h4⟩
    · intro p hp q hq h
      simp only [hT, mem_filter] at hp hq
      exact Prod.ext h (hp.2.trans hq.2.symm)
    · intro a ha
      simp only [mem_filter, mem_Icc] at ha
      refine ⟨(a, b), ?_, rfl⟩
      simp only [hT, mem_filter, mem_product, mem_Icc]
      exact ⟨⟨⟨ha.1, hb.1⟩, hb.2, ha.2⟩, trivial⟩
  · intro p hp
    simp only [hT, coe_filter, mem_product, mem_Icc, Set.mem_ofPred_eq] at hp
    simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq]
    exact ⟨hp.1.2, hp.2.1⟩

end PowerfulFC
end

-- ===== PowerfulFC.Analytic =====
section
/-
# The two real estimates behind Erdős–Szekeres

* `sqrt_floor_div_cube`: with `N = ⌊x⌋₊` and `b ≥ 1`, `⌊√(N / b³)⌋ ≤ √x / (b √b) ≤ ⌊√(N / b³)⌋ + 1`.
* `tail_le`: `∑_{b > K} g(b) ≤ 2 / √K` for `0 ≤ g(b) ≤ 1 / (b √b)` and `K ≥ 1`, by telescoping
  `1 / ((m+1) √(m+1)) ≤ 2 (1/√m − 1/√(m+1))`.
-/

open Finset Real

namespace PowerfulFC

end PowerfulFC
end

-- ===== LeanClassics.SquarefreeCount =====
section
/-
# Squarefree numbers: `#{n ≤ N squarefree} = 6N/π² + O(√N)`

`abs_card_squarefree_sub_le`: for `N ≥ 1`, `|#{1 ≤ n ≤ N : n squarefree} − 6N/π²| ≤ 5 √N`.

Proof. `μ(n)² = ∑_{d² ∣ n} μ(d)` (`sum_moebius_sq_dvd`, writing `n = b² a` with `a` squarefree,
so that `d² ∣ n ↔ d ∣ b`), hence `∑_{n ≤ N} μ(n)² = ∑_{d ≤ √N} μ(d) ⌊N/d²⌋`
(`sum_moebius_sq_eq`). Then `∑_d μ(d)/d² = 1/ζ(2) = 6/π²` (`tsum_moebius_div_sq`, from Mathlib's
`LSeries_zeta_mul_Lseries_moebius` and `riemannZeta_two`), whose tail beyond `M` is at most `1/M`
(`tail_le`).
-/

open Real Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace LeanClassics.SquarefreeCount

/-- With `a` squarefree, `d² ∣ b² a ↔ d ∣ b`. -/
lemma sq_dvd_iff {a b d : ℕ} (ha : Squarefree a) (hb : b ≠ 0) (hd : d ≠ 0) :
    d * d ∣ b ^ 2 * a ↔ d ∣ b := by
  have ha0 : a ≠ 0 := ha.ne_zero
  constructor
  · intro h
    rw [← Nat.factorization_le_iff_dvd hd hb]
    rw [← Nat.factorization_le_iff_dvd (by positivity) (by positivity)] at h
    intro p
    have hp := h p
    have h1 := ha.natFactorization_le_one p
    rw [Nat.factorization_mul hd hd, Nat.factorization_mul (pow_ne_zero 2 hb) ha0,
      Nat.factorization_pow] at hp
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hp
    omega
  · intro h
    exact (Nat.mul_dvd_mul h h).trans (by rw [sq]; exact Dvd.intro a rfl)

/-- `∑_{d² ∣ n} μ(d) = μ(n)²` for `n ≠ 0`. -/
lemma sum_moebius_sq_dvd {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors with d * d ∣ n, (μ d : ℤ) = μ n ^ 2 := by
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n
  have hb : b ≠ 0 := by rintro rfl; simp at hab; exact hn hab.symm
  have hfil : n.divisors.filter (fun d => d * d ∣ n) = b.divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨-, -⟩, h⟩
      have hd : d ≠ 0 := by rintro rfl; simp at h; exact hn h
      exact ⟨(sq_dvd_iff ha hb hd).mp (hab ▸ h), hb⟩
    · rintro ⟨h, -⟩
      have hd : d ≠ 0 := by rintro rfl; simp at h; exact hb h
      have h2 := (sq_dvd_iff ha hb hd).mpr h
      rw [hab] at h2
      exact ⟨⟨(Dvd.intro d rfl).trans h2, hn⟩, h2⟩
  rw [hfil, moebius_sq]
  have hz : ∑ d ∈ b.divisors, (μ d : ℤ) = if b = 1 then 1 else 0 := by
    have := congrArg (fun f : ArithmeticFunction ℤ => f b) moebius_mul_coe_zeta
    simp only [coe_mul_zeta_apply, one_apply] at this
    exact this
  rw [hz]
  by_cases hb1 : b = 1
  · subst hb1
    simp only [one_pow, one_mul] at hab
    simp [hab ▸ ha]
  · have hns : ¬ Squarefree n := fun hs => hb1 (Nat.isUnit_iff.mp
      (hs b (by rw [← hab, sq]; exact Dvd.intro a rfl)))
    simp [hb1, hns]

end LeanClassics.SquarefreeCount
end
end

-- ===== LeanClassics.TotientSum =====
section
/-
# `∑_{n ≤ N} φ(n) = 3N²/π² + O(N log N)`

`abs_sum_totient_sub_le`: for `N ≥ 1`, `|∑_{1 ≤ n ≤ N} φ(n) − 3N²/π²| ≤ N (log N + 1)`.

Proof. Möbius inversion of `∑_{d ∣ n} φ(d) = n` (Mathlib's `Nat.sum_totient` and
`sum_eq_iff_sum_mul_moebius_eq`) gives `φ = μ * id`, so
`∑_{n ≤ N} φ(n) = ∑_{a ≤ N} μ(a) K_a(K_a + 1)/2` with `K_a = ⌊N/a⌋` (Mathlib's
`sum_Ioc_mul_eq_sum_sum`). Each term is `μ(a) N²/(2a²)` up to `N/(2a)`; the sum of these
errors is at most `(N/2)(1 + log N)` (Mathlib's `harmonic_le_one_add_log`), and
`(N²/2) |6/π² − ∑_{a ≤ N} μ(a)/a²| ≤ N/2` (`SquarefreeCount.tail_le`).
-/

open Real Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace LeanClassics.TotientSum


end LeanClassics.TotientSum
end
end

-- ===== LeanClassics.SigmaSum =====
section
/-
# `∑_{n ≤ N} σ(n) = π²N²/12 + O(N log N)`

`abs_sum_sigma_one_sub_le`: for `N ≥ 1`, `|∑_{1 ≤ n ≤ N} σ(n) − π²N²/12| ≤ N (log N + 1)`,
where `σ(n) = ∑_{d ∣ n} d` is Mathlib's `ArithmeticFunction.sigma 1`.

Proof. `σ = ζ * id` (Mathlib's `zeta_mul_pow_eq_sigma`), so
`∑_{n ≤ N} σ(n) = ∑_{a ≤ N} K_a(K_a + 1)/2` with `K_a = ⌊N/a⌋` (Mathlib's
`sum_Ioc_mul_eq_sum_sum`). Each term is `N²/(2a²)` up to `N/(2a)` (`TotientSum.term_le`);
the sum of these errors is at most `(N/2)(1 + log N)` (Mathlib's `harmonic_le_one_add_log`),
and `(N²/2) |π²/6 − ∑_{a ≤ N} 1/a²| ≤ N/2` (`tail_le`, from Mathlib's `hasSum_zeta_two`).
-/

open Real Finset

noncomputable section

namespace LeanClassics.SigmaSum


end LeanClassics.SigmaSum
end
end

-- ===== LeanClassics.RatioSums =====
section
/-
# `∑_{n ≤ N} φ(n)/n = 6N/π² + O(log N)` and `∑_{n ≤ N} σ(n)/n = π²N/6 + O(log N)`

`abs_sum_totient_div_sub_le`: for `N ≥ 1`, `|∑_{1 ≤ n ≤ N} φ(n)/n − 6N/π²| ≤ log N + 2`.

`abs_sum_sigma_div_sub_le`: for `N ≥ 1`, `|∑_{1 ≤ n ≤ N} σ(n)/n − π²N/6| ≤ log N + 2`,
where `σ(n) = ∑_{d ∣ n} d` is Mathlib's `ArithmeticFunction.sigma 1`.

Proof. `φ(n)/n = ∑_{d ∣ n} μ(d)/d` (Möbius inversion of Mathlib's `Nat.sum_totient`) and
`σ(n)/n = ∑_{d ∣ n} 1/d` (Mathlib's `sigma_eq_sum_div`). For `|g(d)| ≤ 1/d`,
`∑_{n ≤ N} ∑_{d ∣ n} g(d) = ∑_{d ≤ N} g(d) ⌊N/d⌋` (Mathlib's `sum_Ioc_mul_eq_sum_sum`) is
`N ∑_{d ≤ N} g(d)/d` up to `∑_{d ≤ N} 1/d ≤ 1 + log N` (`floor_sum_le`). The remaining
`N |c − ∑_{d ≤ N} g(d)/d| ≤ 1` comes from `SquarefreeCount.tail_le` and `SigmaSum.tail_le`.
-/

open Real Finset

noncomputable section

namespace LeanClassics.RatioSums

end LeanClassics.RatioSums
end
end

-- ===== LeanClassics.TotientLogSum =====
section
/-
# `∑_{n ≤ N} φ(n)/n² = (6/π²) log N + O(1)`

`abs_sum_totient_div_sq_sub_le`: there is a constant `C` such that for every natural `N ≥ 1`,
`|∑_{1 ≤ n ≤ N} φ(n)/n² − (6/π²) log N| ≤ C`.

Proof. `φ(n)/n² = ∑_{d ∣ n} (μ(d)/d²)(1/(n/d))` (`RatioSums.totient_div_eq`), so
`∑_{n ≤ N} φ(n)/n² = ∑_{d ≤ N} (μ(d)/d²) H(⌊N/d⌋)` with `H` the harmonic numbers (Mathlib's
`sum_Ioc_mul_eq_sum_sum`). `|H(⌊N/d⌋) − log(N/d)| ≤ 1` (Mathlib's `log_le_harmonic_floor` and
`harmonic_le_one_add_log`), `∑ log d/d²` converges (Mathlib's `log_le_rpow_div` and
`summable_nat_rpow_inv`), and `log N |6/π² − ∑_{d ≤ N} μ(d)/d²| ≤ log N / N ≤ 1`
(`SquarefreeCount.tail_le`). The constant is `π²/6 + 1 + ∑' log d/d²`.
-/

open Real Finset

noncomputable section

namespace LeanClassics.TotientLogSum

end LeanClassics.TotientLogSum
end
end

-- ===== LeanClassics.SquarefreeHarmonic =====
section
/-
# `∑_{n ≤ N} μ(n)²/n = (6/π²) log N + O(1)`

`abs_sum_moebius_sq_div_sub_le`: there is a constant `C` such that for every natural `N ≥ 1`,
`|∑_{1 ≤ n ≤ N, n squarefree} 1/n − (6/π²) log N| ≤ C`, written with `μ(n)²` as the indicator
of squarefree `n`.

Proof. `μ(n)² = ∑_{k² ∣ n} μ(k)` (`SquarefreeCount.sum_moebius_sq_dvd`) and
`∑_{n ≤ N, m ∣ n} 1/n = H(⌊N/m⌋)/m` (`sum_dvd_inv`) give
`∑_{n ≤ N} μ(n)²/n = ∑_{k ≤ N} (μ(k)/k²) H(⌊N/k²⌋)`. For `k² ≤ N`,
`|H(⌊N/k²⌋) − log(N/k²)| ≤ 1` (`TotientLogSum.harmonic_sub_log_le`); for `k² > N` the term is
`0` and `|log(N/k²)| ≤ 2 log k`. With `∑ log k/k²` convergent
(`TotientLogSum.summable_log_div_sq`) and `log N |6/π² − ∑_{k ≤ N} μ(k)/k²| ≤ 1`
(`SquarefreeCount.tail_le`), the constant is `π²/6 + 4 ∑' log k/k² + 1`.
-/

open Real Finset

noncomputable section

namespace LeanClassics.SquarefreeHarmonic


end LeanClassics.SquarefreeHarmonic
end
end

-- ===== LeanClassics.TwoPowOmega =====
section
/-
# `∑_{n ≤ N} 2^{ω(n)} = (6/π²) N log N + O(N)`

`abs_sum_two_pow_omega_sub_le`: there is a constant `C` such that for every natural `N ≥ 1`,
`|∑_{1 ≤ n ≤ N} 2^{ω(n)} − (6/π²) N log N| ≤ C N`, where `ω(n)` is the number of distinct
prime factors (Mathlib's `ArithmeticFunction.cardDistinctFactors`).

Proof. `2^{ω(n)}` counts the squarefree divisors of `n` (Mathlib's
`sum_divisors_filter_squarefree`), so `2^{ω(n)} = ∑_{d ∣ n} μ(d)²` (`two_pow_omega_eq`) and
`∑_{n ≤ N} 2^{ω(n)} = ∑_{d ≤ N} μ(d)² ⌊N/d⌋` (`RatioSums.sum_sum_divisors`). This is
`N ∑_{d ≤ N} μ(d)²/d` up to at most `N`, and
`SquarefreeHarmonic.abs_sum_moebius_sq_div_sub_le` finishes.
-/

open Real Finset

noncomputable section

namespace LeanClassics.TwoPowOmega

end LeanClassics.TwoPowOmega
end
end

-- ===== LeanClassics.SquarefreeLSeries =====
section
/-
# `∑ μ(n)²/n^s = ζ(s)/ζ(2s)` and `∑ 2^{ω(n)}/n^s = ζ(s)²/ζ(2s)` for `Re s > 1`

`LSeries_moebius_sq`: for `Re s > 1`, `∑_{n ≥ 1} μ(n)² n^{−s} = ζ(s)/ζ(2s)` (the Dirichlet series of
the squarefree indicator).

`LSeries_two_pow_omega`: for `Re s > 1`, `∑_{n ≥ 1} 2^{ω(n)} n^{−s} = ζ(s)²/ζ(2s)`, where `ω(n)` is
the number of distinct prime factors (Mathlib's `ArithmeticFunction.cardDistinctFactors`).

Proof. `μ² = ζ * Q` with `Q(k²) = μ(k)` and `Q = 0` off the squares
(`SquarefreeCount.sum_moebius_sq_dvd`), and `∑ Q(n) n^{−s} = ∑ μ(k) k^{−2s} = 1/ζ(2s)` (Mathlib's
`LSeries_zeta_mul_Lseries_moebius` at `2s`). `2^ω = ζ * μ²` (`TwoPowOmega.two_pow_omega_eq`).
Then Mathlib's `LSeries_mul'`.
-/

open Complex ArithmeticFunction LSeries
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

noncomputable section

namespace LeanClassics.SquarefreeLSeries

lemma LSeries_moebius {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (μ n : ℂ)) s = (riemannZeta s)⁻¹ := by
  have h1 := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs] at h1
  exact eq_inv_of_mul_eq_one_right h1

end LeanClassics.SquarefreeLSeries
end
end

-- ===== PowerfulFC.Main =====
section
/-
# Erdős–Szekeres: `Q(x) = (ζ(3/2)/ζ(3)) x^{1/2} + O(x^{1/3})`, in formal-conjectures' wording

The definitions `Q`, `A`, `B` and the statement `asymptotic_erdos_szekeres` are copied token for token from
google-deepmind/formal-conjectures `FormalConjectures/Wikipedia/PowerfulNumbersDensity.lean` (commit `ea8e3e19`),
under the same `open` line.

Proof. Every powerful `n ≥ 1` is `a² b³` with `b` squarefree, uniquely (`PowerfulFC.Decomp`), so
`Q(x) = ∑_{b ≤ x^{1/3}} μ²(b) ⌊√(x/b³)⌋` (`PowerfulFC.Count`). Each floor is within 1 of `√x / b^{3/2}`
(`sqrt_floor_div_cube`), and `∑_{b > K} b^{-3/2} ≤ 2/√K` (`tail_le`), so with `K = ⌊x^{1/3}⌋`,
`|Q(x) − √x ∑_b μ²(b) b^{-3/2}| ≤ 5 x^{1/3}` for `x ≥ 1`. Finally `∑ μ²(b) b^{-3/2} = ζ(3/2)/ζ(3)`
(`LeanClassics.SquarefreeLSeries.LSeries_moebius_sq` at `s = 3/2`).
-/

open Filter Asymptotics Real


namespace PowerfulFC

open PowerfulNumbersDensity Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

lemma Q_eq_card {x : ℝ} (hx : 0 ≤ x) : Q x = #{n ∈ Icc 1 ⌊x⌋₊ | n.Powerful} := by
  unfold Q
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq]
  rw [Nat.le_floor_iff hx, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  tauto

end PowerfulFC

end

-- ===== PowerfulFC.Hyperbola =====
section
/-
# Rung BG1: the hyperbola count of `a² b³ ≤ y`, and Möbius over sixth powers

`S N = #{(a, b) ≥ 1 : a² b³ ≤ N}` and `ψ t = {t} − 1/2`.

1. `S_hyperbola`: for real `z, w ≥ 1` with `y = z³ w²`,
   `S ⌊y⌋ = ∑_{b ≤ z} ⌊√(y/b³)⌋ + ∑_{a ≤ w} ⌊(y/a²)^{1/3}⌋ − ⌊z⌋⌊w⌋`.
2. `S_eq_main_sub_psi`: inserting `⌊t⌋ = t − 1/2 − ψ(t)` and BG0, the `zw`, `ψ(z) w`, `ψ(w) z`, `z/2`, `w/2` terms
   cancel exactly and
   `S ⌊y⌋ = ζ(3/2) √y + ζ(2/3) y^{1/3} − ∑_{b ≤ z} ψ(√(y/b³)) − ∑_{a ≤ w} ψ((y/a²)^{1/3}) + E`,
   `E = 1/4 − ψ(z) ψ(w) + √y R₁ + y^{1/3} R₂` (`R₁`, `R₂` the BG0 remainders), so
   `|E| ≤ 1/2 + w/z + (4/9) z/w`; at `z = w` (`y = z⁵`), `|E| ≤ 2` (`abs_S_sub_main_le_two`).
3. `Q_eq_sum_moebius_S`: `#{n ≤ N powerful} = ∑_{d ≥ 1} μ(d) S(N / d⁶)` (from `card_powerful_eq_sum` and
   `μ²(b) = ∑_{d² ∣ b} μ(d)`, then `b = d² c`).
-/

open Finset Real

noncomputable section

namespace PowerfulFC.BG1

/-- `S N = #{(a, b) : a, b ≥ 1, a² b³ ≤ N}`. -/
def S (N : ℕ) : ℕ := #{p ∈ Icc 1 N ×ˢ Icc 1 N | p.1 ^ 2 * p.2 ^ 3 ≤ N}

/-- The sawtooth `ψ(t) = {t} − 1/2`. -/
def ψ (t : ℝ) : ℝ := Int.fract t - 1 / 2

lemma floor_eq_sub_psi {t : ℝ} (ht : 0 ≤ t) : (⌊t⌋₊ : ℝ) = t - 1 / 2 - ψ t := by
  unfold ψ
  rw [natCast_floor_eq_intCast_floor ht, Int.fract]
  ring

lemma abs_psi_le (t : ℝ) : |ψ t| ≤ 1 / 2 := by
  unfold ψ
  rw [abs_le]
  constructor <;> linarith [Int.fract_nonneg t, Int.fract_lt_one t]

/-- A count `#{b ∈ [1, N] : P b}` is `⌊t⌋` when `P b ↔ b ≤ t` for `b ≥ 1` and `P b → b ≤ N`. -/
lemma card_filter_eq_floor {N : ℕ} {P : ℕ → Prop} [DecidablePred P] {t : ℝ} (ht : 0 ≤ t)
    (hP : ∀ b, 1 ≤ b → (P b ↔ (b : ℝ) ≤ t)) (hPN : ∀ b, 1 ≤ b → P b → b ≤ N) :
    #{b ∈ Icc 1 N | P b} = ⌊t⌋₊ := by
  have : ({b ∈ Icc 1 N | P b} : Finset ℕ) = Icc 1 ⌊t⌋₊ := by
    ext b
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, hb⟩
      exact ⟨h1, (Nat.le_floor_iff ht).2 ((hP b h1).1 hb)⟩
    · rintro ⟨h1, hb⟩
      have hb' : P b := (hP b h1).2 ((Nat.le_floor_iff ht).1 hb)
      exact ⟨⟨h1, hPN b h1 hb'⟩, hb'⟩
  rw [this, Nat.card_Icc]; omega

section hyperbola

variable {z w : ℝ}

/-- `#{a : a² b³ ≤ ⌊y⌋} = ⌊√(y/b³)⌋`. -/
lemma card_a {y : ℝ} (hy : 0 ≤ y) {b : ℕ} (hb : 1 ≤ b) :
    #{a ∈ Icc 1 ⌊y⌋₊ | a ^ 2 * b ^ 3 ≤ ⌊y⌋₊} = ⌊√(y / (b : ℝ) ^ 3)⌋₊ := by
  have hb3 : (0 : ℝ) < (b : ℝ) ^ 3 := by positivity
  refine card_filter_eq_floor (Real.sqrt_nonneg _) (fun a _ => ?_) (fun a ha h => ?_)
  · rw [Nat.le_floor_iff hy, Real.le_sqrt (Nat.cast_nonneg a) (div_nonneg hy hb3.le), le_div_iff₀ hb3]
    push_cast; rfl
  · calc a ≤ a ^ 2 := by nlinarith
      _ ≤ a ^ 2 * b ^ 3 := Nat.le_mul_of_pos_right _ (by positivity)
      _ ≤ _ := h

/-- `#{b : a² b³ ≤ ⌊y⌋} = ⌊(y/a²)^{1/3}⌋`. -/
lemma card_b {y : ℝ} (hy : 0 ≤ y) {a : ℕ} (ha : 1 ≤ a) :
    #{b ∈ Icc 1 ⌊y⌋₊ | a ^ 2 * b ^ 3 ≤ ⌊y⌋₊} = ⌊(y / (a : ℝ) ^ 2) ^ ((1 : ℝ) / 3)⌋₊ := by
  have ha2 : (0 : ℝ) < (a : ℝ) ^ 2 := by positivity
  have hq : 0 ≤ y / (a : ℝ) ^ 2 := div_nonneg hy ha2.le
  refine card_filter_eq_floor (by positivity) (fun b _ => ?_) (fun b hb h => ?_)
  · rw [Nat.le_floor_iff hy]
    have key : (b : ℝ) ≤ (y / (a : ℝ) ^ 2) ^ ((1 : ℝ) / 3) ↔ (b : ℝ) ^ 3 ≤ y / (a : ℝ) ^ 2 := by
      constructor
      · intro h
        calc (b : ℝ) ^ 3 ≤ ((y / (a : ℝ) ^ 2) ^ ((1 : ℝ) / 3)) ^ 3 := by gcongr
          _ = y / (a : ℝ) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hq]; norm_num
      · intro h
        calc (b : ℝ) = ((b : ℝ) ^ 3) ^ ((1 : ℝ) / 3) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg b)]; norm_num
          _ ≤ _ := by gcongr
    rw [key, le_div_iff₀ ha2]
    push_cast; ring_nf
  · calc b ≤ b ^ 3 := Nat.le_self_pow (by norm_num) b
      _ ≤ a ^ 2 * b ^ 3 := Nat.le_mul_of_pos_left _ (by positivity)
      _ ≤ _ := h

lemma card_T1 {N Z : ℕ} (hZ : Z ≤ N) :
    #{p ∈ Icc 1 N ×ˢ Icc 1 N | p.1 ^ 2 * p.2 ^ 3 ≤ N ∧ p.2 ≤ Z}
      = ∑ b ∈ Icc 1 Z, #{a ∈ Icc 1 N | a ^ 2 * b ^ 3 ≤ N} := by
  rw [card_filter, sum_product_right,
    show Icc 1 Z = ({b ∈ Icc 1 N | b ≤ Z} : Finset ℕ) by ext; simp only [mem_Icc, mem_filter]; omega,
    sum_filter]
  refine sum_congr rfl fun b _ => ?_
  rw [card_filter]
  split_ifs with h <;> simp [h]

lemma card_T2 {N W : ℕ} (hW : W ≤ N) :
    #{p ∈ Icc 1 N ×ˢ Icc 1 N | p.1 ^ 2 * p.2 ^ 3 ≤ N ∧ p.1 ≤ W}
      = ∑ a ∈ Icc 1 W, #{b ∈ Icc 1 N | a ^ 2 * b ^ 3 ≤ N} := by
  rw [card_filter, sum_product,
    show Icc 1 W = ({a ∈ Icc 1 N | a ≤ W} : Finset ℕ) by ext; simp only [mem_Icc, mem_filter]; omega,
    sum_filter]
  refine sum_congr rfl fun a _ => ?_
  rw [card_filter]
  split_ifs with h <;> simp [h]

/-- **Hyperbola identity** (natural form): for real `z, w ≥ 1` and `y = z³ w²`,
`S ⌊y⌋ + ⌊z⌋⌊w⌋ = ∑_{b ≤ z} ⌊√(y/b³)⌋ + ∑_{a ≤ w} ⌊(y/a²)^{1/3}⌋`. -/
theorem S_hyperbola_nat {y z w : ℝ} (hz : 1 ≤ z) (hw : 1 ≤ w) (hy : y = z ^ 3 * w ^ 2) :
    S ⌊y⌋₊ + ⌊z⌋₊ * ⌊w⌋₊
      = ∑ b ∈ Icc 1 ⌊z⌋₊, ⌊√(y / (b : ℝ) ^ 3)⌋₊
        + ∑ a ∈ Icc 1 ⌊w⌋₊, ⌊(y / (a : ℝ) ^ 2) ^ ((1 : ℝ) / 3)⌋₊ := by
  set N := ⌊y⌋₊ with hN
  set Z := ⌊z⌋₊ with hZ
  set W := ⌊w⌋₊ with hW
  have hz0 : 0 ≤ z := by linarith
  have hw0 : 0 ≤ w := by linarith
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hzy : z ≤ y := by
    rw [hy]
    have : (1 : ℝ) ≤ z ^ 2 * w ^ 2 := by nlinarith [one_le_pow₀ (n := 2) hz, one_le_pow₀ (n := 2) hw]
    nlinarith
  have hwy : w ≤ y := by
    rw [hy]
    have h1 : (1 : ℝ) ≤ z ^ 3 * w := by nlinarith [one_le_pow₀ (n := 3) hz]
    nlinarith
  have hZN : Z ≤ N := Nat.floor_le_floor hzy
  have hWN : W ≤ N := Nat.floor_le_floor hwy
  -- a pair with `a ≤ W` and `b ≤ Z` lies under the curve
  have hin : ∀ a b : ℕ, a ≤ W → b ≤ Z → a ^ 2 * b ^ 3 ≤ N := by
    intro a b ha hb
    rw [hN, Nat.le_floor_iff hy0, hy]
    have ha' : (a : ℝ) ≤ w := (Nat.le_floor_iff hw0).1 ha
    have hb' : (b : ℝ) ≤ z := (Nat.le_floor_iff hz0).1 hb
    push_cast
    calc (a : ℝ) ^ 2 * (b : ℝ) ^ 3 ≤ w ^ 2 * z ^ 3 := by gcongr
      _ = z ^ 3 * w ^ 2 := by ring
  -- a pair under the curve has `b ≤ Z` or `a ≤ W`
  have hout : ∀ a b : ℕ, a ^ 2 * b ^ 3 ≤ N → b ≤ Z ∨ a ≤ W := by
    intro a b h
    by_contra hc
    push Not at hc
    have hb' : z < (b : ℝ) := (Nat.floor_lt hz0).1 hc.1
    have ha' : w < (a : ℝ) := (Nat.floor_lt hw0).1 hc.2
    have h' : ((a ^ 2 * b ^ 3 : ℕ) : ℝ) ≤ y := (Nat.le_floor_iff hy0).1 h
    push_cast at h'
    have : w ^ 2 * z ^ 3 < (a : ℝ) ^ 2 * (b : ℝ) ^ 3 := by
      have h2 : w ^ 2 < (a : ℝ) ^ 2 := by gcongr
      have h3 : z ^ 3 < (b : ℝ) ^ 3 := by gcongr
      calc w ^ 2 * z ^ 3 < (a : ℝ) ^ 2 * z ^ 3 := by gcongr
        _ ≤ (a : ℝ) ^ 2 * (b : ℝ) ^ 3 := by gcongr
    nlinarith
  have hunion : ({p ∈ Icc 1 N ×ˢ Icc 1 N | p.1 ^ 2 * p.2 ^ 3 ≤ N ∧ p.2 ≤ Z} ∪
      {p ∈ Icc 1 N ×ˢ Icc 1 N | p.1 ^ 2 * p.2 ^ 3 ≤ N ∧ p.1 ≤ W} : Finset (ℕ × ℕ))
      = {p ∈ Icc 1 N ×ˢ Icc 1 N | p.1 ^ 2 * p.2 ^ 3 ≤ N} := by
    ext ⟨a, b⟩
    simp only [mem_union, mem_filter]
    constructor
    · rintro (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩) <;> exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hout a b h2 with h | h
      · exact Or.inl ⟨h1, h2, h⟩
      · exact Or.inr ⟨h1, h2, h⟩
  have hinter : ({p ∈ Icc 1 N ×ˢ Icc 1 N | p.1 ^ 2 * p.2 ^ 3 ≤ N ∧ p.2 ≤ Z} ∩
      {p ∈ Icc 1 N ×ˢ Icc 1 N | p.1 ^ 2 * p.2 ^ 3 ≤ N ∧ p.1 ≤ W} : Finset (ℕ × ℕ))
      = Icc 1 W ×ˢ Icc 1 Z := by
    ext ⟨a, b⟩
    simp only [mem_inter, mem_filter, mem_product, mem_Icc]
    constructor
    · rintro ⟨⟨⟨⟨h1, _⟩, h2, _⟩, _, hb⟩, _, _, ha⟩
      exact ⟨⟨h1, ha⟩, h2, hb⟩
    · rintro ⟨⟨h1, ha⟩, h2, hb⟩
      have := hin a b ha hb
      exact ⟨⟨⟨⟨h1, by omega⟩, h2, by omega⟩, this, hb⟩, ⟨⟨h1, by omega⟩, h2, by omega⟩, this, ha⟩
  have key := card_union_add_card_inter
    ({p ∈ Icc 1 N ×ˢ Icc 1 N | p.1 ^ 2 * p.2 ^ 3 ≤ N ∧ p.2 ≤ Z} : Finset (ℕ × ℕ))
    {p ∈ Icc 1 N ×ˢ Icc 1 N | p.1 ^ 2 * p.2 ^ 3 ≤ N ∧ p.1 ≤ W}
  rw [hunion, hinter, card_product, Nat.card_Icc, Nat.card_Icc, card_T1 hZN, card_T2 hWN] at key
  unfold S
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel] at key
  rw [mul_comm Z W, key]
  congr 1
  · exact sum_congr rfl fun b hb => card_a hy0 (mem_Icc.1 hb).1
  · exact sum_congr rfl fun a ha => card_b hy0 (mem_Icc.1 ha).1

end hyperbola

section cancel

open PowerfulFC.ZetaPartial

lemma sqrt_div_cube (y : ℝ) {b : ℝ} (hb : 0 < b) :
    √(y / b ^ 3) = √y * b ^ (-(3 / 2 : ℝ)) := by
  rw [Real.sqrt_div' _ (by positivity), Real.rpow_neg hb.le, div_eq_mul_inv]
  congr 2
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hb.le]; norm_num

lemma cbrt_div_sq {y : ℝ} (hy : 0 ≤ y) {a : ℝ} (ha : 0 < a) :
    (y / a ^ 2) ^ ((1 : ℝ) / 3) = y ^ ((1 : ℝ) / 3) * a ^ (-(2 / 3 : ℝ)) := by
  rw [Real.div_rpow hy (by positivity), Real.rpow_neg ha.le, div_eq_mul_inv]
  congr 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]; norm_num

lemma sqrt_y {z w : ℝ} (hz : 0 < z) (hw : 0 ≤ w) : √(z ^ 3 * w ^ 2) = z ^ ((3 : ℝ) / 2) * w := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hw, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hz.le]; norm_num

lemma cbrt_y {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    (z ^ 3 * w ^ 2) ^ ((1 : ℝ) / 3) = z * w ^ ((2 : ℝ) / 3) := by
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast z, ← Real.rpow_mul hz.le,
    ← Real.rpow_natCast w, ← Real.rpow_mul hw.le]; norm_num

/-- The sum of the floors `⌊√(y/b³)⌋` over `b ≤ z`: `√y ∑ b^{-3/2} − ⌊z⌋/2 − ∑ ψ(√(y/b³))`. -/
lemma sum_floor_b (y : ℝ) (Z : ℕ) :
    ∑ b ∈ Icc 1 Z, (⌊√(y / (b : ℝ) ^ 3)⌋₊ : ℝ)
      = √y * ∑ b ∈ Icc 1 Z, (b : ℝ) ^ (-(3 / 2 : ℝ)) - Z / 2 - ∑ b ∈ Icc 1 Z, ψ (√(y / (b : ℝ) ^ 3)) := by
  rw [sum_congr rfl fun (b : ℕ) _ => floor_eq_sub_psi (Real.sqrt_nonneg (y / (b : ℝ) ^ 3)),
    sum_sub_distrib, sum_sub_distrib, sum_const, Nat.card_Icc, mul_sum]
  congr 1
  rw [Nat.add_sub_cancel, nsmul_eq_mul]
  congr 1
  · refine sum_congr rfl fun b hb => sqrt_div_cube y (by exact_mod_cast (mem_Icc.1 hb).1)
  · ring

lemma sum_floor_a {y : ℝ} (hy : 0 ≤ y) (W : ℕ) :
    ∑ a ∈ Icc 1 W, (⌊(y / (a : ℝ) ^ 2) ^ ((1 : ℝ) / 3)⌋₊ : ℝ)
      = y ^ ((1 : ℝ) / 3) * ∑ a ∈ Icc 1 W, (a : ℝ) ^ (-(2 / 3 : ℝ)) - W / 2
        - ∑ a ∈ Icc 1 W, ψ ((y / (a : ℝ) ^ 2) ^ ((1 : ℝ) / 3)) := by
  rw [sum_congr rfl fun (a : ℕ) _ => floor_eq_sub_psi (Real.rpow_nonneg (div_nonneg hy (sq_nonneg (a : ℝ))) _),
    sum_sub_distrib, sum_sub_distrib, sum_const, Nat.card_Icc, mul_sum]
  congr 1
  rw [Nat.add_sub_cancel, nsmul_eq_mul]
  congr 1
  · refine sum_congr rfl fun a ha => cbrt_div_sq hy (by exact_mod_cast (mem_Icc.1 ha).1)
  · ring

/-- **BG1, exact form.** For real `z, w ≥ 1` and `y = z³ w²`, with `ψ(t) = {t} − 1/2`,
`S ⌊y⌋ − (ζ(3/2) √y + ζ(2/3) y^{1/3} − ∑_{b ≤ z} ψ(√(y/b³)) − ∑_{a ≤ w} ψ((y/a²)^{1/3}))`
`= 1/4 − ψ(z) ψ(w) + √y R₁ + y^{1/3} R₂`, where `R₁`, `R₂` are the BG0 remainders of `∑_{b ≤ z} b^{-3/2}` and
`∑_{a ≤ w} a^{-2/3}`. -/
theorem S_eq_main_sub_psi {y z w : ℝ} (hz : 1 ≤ z) (hw : 1 ≤ w) (hy : y = z ^ 3 * w ^ 2) :
    (S ⌊y⌋₊ : ℝ)
        - ((riemannZeta (3 / 2)).re * √y + (riemannZeta (2 / 3)).re * y ^ ((1 : ℝ) / 3)
          - ∑ b ∈ Icc 1 ⌊z⌋₊, ψ (√(y / (b : ℝ) ^ 3))
          - ∑ a ∈ Icc 1 ⌊w⌋₊, ψ ((y / (a : ℝ) ^ 2) ^ ((1 : ℝ) / 3)))
      = 1 / 4 - ψ z * ψ w
        + √y * ((∑ n ∈ Icc 1 ⌊z⌋₊, (n : ℝ) ^ (-(3 / 2 : ℝ)))
            - ((riemannZeta (3 / 2)).re - 2 * z ^ (-(1 / 2 : ℝ)) - (Int.fract z - 1 / 2) * z ^ (-(3 / 2 : ℝ))))
        + y ^ ((1 : ℝ) / 3) * ((∑ n ∈ Icc 1 ⌊w⌋₊, (n : ℝ) ^ (-(2 / 3 : ℝ)))
            - (3 * w ^ ((1 : ℝ) / 3) + (riemannZeta (2 / 3)).re
              - (Int.fract w - 1 / 2) * w ^ (-(2 / 3 : ℝ)))) := by
  have hz0 : 0 < z := by linarith
  have hw0 : 0 < w := by linarith
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hH : (S ⌊y⌋₊ : ℝ) + (⌊z⌋₊ : ℝ) * (⌊w⌋₊ : ℝ)
      = ∑ b ∈ Icc 1 ⌊z⌋₊, (⌊√(y / (b : ℝ) ^ 3)⌋₊ : ℝ)
        + ∑ a ∈ Icc 1 ⌊w⌋₊, (⌊(y / (a : ℝ) ^ 2) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) := by
    exact_mod_cast S_hyperbola_nat hz hw hy
  have hF1 := sum_floor_b y ⌊z⌋₊
  have hF2 := sum_floor_a hy0 ⌊w⌋₊
  have hZ := floor_eq_sub_psi hz0.le
  have hW := floor_eq_sub_psi hw0.le
  have hP : √y = z ^ ((3 : ℝ) / 2) * w := by rw [hy]; exact sqrt_y hz0 hw0.le
  have hY : y ^ ((1 : ℝ) / 3) = z * w ^ ((2 : ℝ) / 3) := by rw [hy]; exact cbrt_y hz0 hw0
  have r1 : √y * z ^ (-(1 / 2 : ℝ)) = z * w := by
    rw [hP, mul_right_comm, ← Real.rpow_add hz0]; norm_num
  have r2 : √y * z ^ (-(3 / 2 : ℝ)) = w := by
    rw [hP, mul_right_comm, ← Real.rpow_add hz0]; norm_num
  have r3 : y ^ ((1 : ℝ) / 3) * w ^ ((1 : ℝ) / 3) = z * w := by
    rw [hY, mul_assoc, ← Real.rpow_add hw0]; norm_num
  have r4 : y ^ ((1 : ℝ) / 3) * w ^ (-(2 / 3 : ℝ)) = z := by
    rw [hY, mul_assoc, ← Real.rpow_add hw0]; norm_num
  unfold ψ at *
  linear_combination hH + hF1 + hF2 - 2 * r1 - (Int.fract z - 1 / 2) * r2 + 3 * r3
    - (Int.fract w - 1 / 2) * r4 - (⌊w⌋₊ : ℝ) * hZ - (z - 1 / 2 - (Int.fract z - 1 / 2)) * hW
    - hZ / 2 - hW / 2

/-- **BG1, bound.** For real `z, w ≥ 1` and `y = z³ w²`,
`|S ⌊y⌋ − (ζ(3/2) √y + ζ(2/3) y^{1/3} − ∑_{b ≤ z} ψ(√(y/b³)) − ∑_{a ≤ w} ψ((y/a²)^{1/3}))| ≤ 1/2 + w/z + (4/9) z/w`. -/
theorem abs_S_sub_main_le {y z w : ℝ} (hz : 1 ≤ z) (hw : 1 ≤ w) (hy : y = z ^ 3 * w ^ 2) :
    |(S ⌊y⌋₊ : ℝ)
        - ((riemannZeta (3 / 2)).re * √y + (riemannZeta (2 / 3)).re * y ^ ((1 : ℝ) / 3)
          - ∑ b ∈ Icc 1 ⌊z⌋₊, ψ (√(y / (b : ℝ) ^ 3))
          - ∑ a ∈ Icc 1 ⌊w⌋₊, ψ ((y / (a : ℝ) ^ 2) ^ ((1 : ℝ) / 3)))|
      ≤ 1 / 2 + w / z + 4 / 9 * (z / w) := by
  have hz0 : 0 < z := by linarith
  have hw0 : 0 < w := by linarith
  rw [S_eq_main_sub_psi hz hw hy]
  have hP : √y = z ^ ((3 : ℝ) / 2) * w := by rw [hy]; exact sqrt_y hz0 hw0.le
  have hY : y ^ ((1 : ℝ) / 3) = z * w ^ ((2 : ℝ) / 3) := by rw [hy]; exact cbrt_y hz0 hw0
  have r5 : √y * z ^ (-(5 / 2 : ℝ)) = w / z := by
    rw [hP, mul_right_comm, ← Real.rpow_add hz0]; norm_num; rw [Real.rpow_neg_one]; ring
  have r6 : y ^ ((1 : ℝ) / 3) * w ^ (-(5 / 3 : ℝ)) = z / w := by
    rw [hY, mul_assoc, ← Real.rpow_add hw0]; norm_num; rw [Real.rpow_neg_one]; ring
  have h1 := sum_three_halves hz
  have h2 := sum_two_thirds hw
  have hψ : |1 / 4 - ψ z * ψ w| ≤ 1 / 2 := by
    have := abs_psi_le z
    have := abs_psi_le w
    calc |1 / 4 - ψ z * ψ w| ≤ |(1 / 4 : ℝ)| + |ψ z| * |ψ w| := by rw [← abs_mul]; exact abs_sub _ _
      _ ≤ 1 / 4 + 1 / 2 * (1 / 2) := by
          rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]; gcongr
      _ = 1 / 2 := by norm_num
  have hPn : 0 ≤ √y := Real.sqrt_nonneg y
  have hYn : 0 ≤ y ^ ((1 : ℝ) / 3) := by rw [hY]; positivity
  refine (abs_add_three _ _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hPn, abs_of_nonneg hYn]
  have e1 := mul_le_mul_of_nonneg_left h1 hPn
  have e2 := mul_le_mul_of_nonneg_left h2 hYn
  rw [r5] at e1
  rw [mul_left_comm, r6] at e2
  linarith

/-- **BG1 at `z = w = y^{1/5}`.** For real `y ≥ 1`, with `z = y^{1/5}`:
`|S ⌊y⌋ − (ζ(3/2) √y + ζ(2/3) y^{1/3} − ∑_{b ≤ z} ψ(√(y/b³)) − ∑_{a ≤ z} ψ((y/a²)^{1/3}))| ≤ 2`. -/
theorem abs_S_sub_main_le_two {y : ℝ} (hy : 1 ≤ y) :
    |(S ⌊y⌋₊ : ℝ)
        - ((riemannZeta (3 / 2)).re * √y + (riemannZeta (2 / 3)).re * y ^ ((1 : ℝ) / 3)
          - ∑ b ∈ Icc 1 ⌊y ^ ((1 : ℝ) / 5)⌋₊, ψ (√(y / (b : ℝ) ^ 3))
          - ∑ a ∈ Icc 1 ⌊y ^ ((1 : ℝ) / 5)⌋₊, ψ ((y / (a : ℝ) ^ 2) ^ ((1 : ℝ) / 3)))|
      ≤ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have hz : 1 ≤ y ^ ((1 : ℝ) / 5) := Real.one_le_rpow hy (by norm_num)
  have hz0 : 0 < y ^ ((1 : ℝ) / 5) := by linarith
  have h5 : y = (y ^ ((1 : ℝ) / 5)) ^ 3 * (y ^ ((1 : ℝ) / 5)) ^ 2 := by
    rw [← pow_add, ← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
  refine (abs_S_sub_main_le hz hz h5).trans ?_
  rw [div_self hz0.ne']
  norm_num

end cancel

section moebius

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- `S M = ∑_{c ≤ M} ⌊√(M / c³)⌋`. -/
lemma S_eq_sum (M : ℕ) : S M = ∑ c ∈ Icc 1 M, Nat.sqrt (M / c ^ 3) := by
  unfold S
  rw [card_filter, sum_product_right]
  refine sum_congr rfl fun c hc => ?_
  rw [← card_filter_sq_mul_cube_le M c (mem_Icc.1 hc).1, card_filter]

lemma sqrt_ne_zero_imp {N b : ℕ} (h : Nat.sqrt (N / b ^ 3) ≠ 0) : b ^ 3 ≤ N := by
  by_contra hc
  push Not at hc
  exact h (by rw [Nat.div_eq_of_lt hc]; rfl)

/-- **Möbius over sixth powers.** `#{n ∈ [1, N] powerful} = ∑_{d ≤ N} μ(d) S(N / d⁶)`. -/
theorem card_powerful_eq_sum_moebius (N : ℕ) :
    (#{n ∈ Icc 1 N | n.Powerful} : ℤ) = ∑ d ∈ Icc 1 N, μ d * S (N / d ^ 6) := by
  have hK : ∀ b, 1 ≤ b → b ^ 3 ≤ N → b ≤ N := fun b _ h => (Nat.le_self_pow (by norm_num) b).trans h
  rw [card_powerful_eq_sum N N hK, sum_filter]
  push_cast
  -- `1[b squarefree] = μ(b)² = ∑_{d² ∣ b} μ(d)`
  have h1 : ∀ b ∈ Icc 1 N, ((if Squarefree b then (Nat.sqrt (N / b ^ 3) : ℤ) else 0))
      = ∑ d ∈ b.divisors with d * d ∣ b, μ d * (Nat.sqrt (N / b ^ 3) : ℤ) := by
    intro b hb
    have hb0 : b ≠ 0 := by have := (mem_Icc.1 hb).1; omega
    rw [← sum_mul, LeanClassics.SquarefreeCount.sum_moebius_sq_dvd hb0]
    split_ifs with h
    · have := abs_moebius_eq_one_of_squarefree h
      have h2 : (μ b) ^ 2 = 1 := by rw [← sq_abs, this]; norm_num
      rw [h2, one_mul]
    · rw [moebius_eq_zero_of_not_squarefree h]; simp
  rw [sum_congr rfl h1, sum_sigma']
  simp_rw [S_eq_sum, Nat.cast_sum, mul_sum]
  rw [sum_sigma']
  refine sum_bij_ne_zero (fun x _ _ => ⟨x.2, x.1 / (x.2 * x.2)⟩) ?_ ?_ ?_ ?_
  · rintro ⟨b, d⟩ hx hne
    simp only [mem_sigma, mem_Icc, mem_filter, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hb1, hbN⟩, ⟨hdb, -⟩, hdd⟩ := hx
    have hb0 : 0 < b := by omega
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdb hb0
    have hb3 : b ^ 3 ≤ N := sqrt_ne_zero_imp (right_ne_zero_of_mul hne |> fun h => by exact_mod_cast h)
    obtain ⟨c, rfl⟩ := hdd
    have hdd0 : 0 < d * d := Nat.mul_pos hd0 hd0
    rw [Nat.mul_div_cancel_left c hdd0]
    have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hb0)
    refine ⟨⟨hd0, (Nat.le_of_dvd hb0 hdb).trans hbN⟩, hc0, ?_⟩
    rw [Nat.le_div_iff_mul_le (by positivity)]
    calc c * d ^ 6 ≤ c ^ 3 * d ^ 6 := Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) c)
      _ = (d * d * c) ^ 3 := by ring
      _ ≤ N := hb3
  · rintro ⟨b, d⟩ hx hne ⟨b', d'⟩ hx' hne' h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simp only [mem_sigma, mem_filter] at hx hx'
    have e1 := Nat.div_mul_cancel hx.2.2
    have e2 := Nat.div_mul_cancel hx'.2.2
    have : b = b' := by
      rw [← e1, ← e2]; exact congrArg (· * (d * d)) (eq_of_heq h2)
    subst this; rfl
  · rintro ⟨d, c⟩ hx hne
    simp only [mem_sigma, mem_Icc] at hx
    obtain ⟨⟨hd1, -⟩, hc1, hcN⟩ := hx
    have hd0 : 0 < d := hd1
    have hb0 : 0 < d * d * c := by positivity
    have hne' : Nat.sqrt (N / d ^ 6 / c ^ 3) ≠ 0 := by
      intro h; apply hne; simp [h]
    rw [Nat.div_div_eq_div_mul] at hne'
    have hb3 : (d * d * c) ^ 3 ≤ N := by
      exact sqrt_ne_zero_imp (b := d * d * c) (N := N) (by
        rw [show (d * d * c) ^ 3 = d ^ 6 * c ^ 3 by ring]; exact hne')
    refine ⟨⟨d * d * c, d⟩, ?_, ?_, ?_⟩
    · simp only [mem_sigma, mem_Icc, mem_filter, Nat.mem_divisors]
      refine ⟨⟨hb0, (Nat.le_self_pow (by norm_num) _).trans hb3⟩, ⟨⟨c * d, by ring⟩, hb0.ne'⟩,
        ⟨c, by ring⟩⟩
    · simp only at hne ⊢
      refine mul_ne_zero (left_ne_zero_of_mul hne) ?_
      rw [show (d * d * c) ^ 3 = d ^ 6 * c ^ 3 by ring]
      exact_mod_cast hne'
    · simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
      exact Nat.mul_div_cancel_left c (Nat.mul_pos hd0 hd0)
  · rintro ⟨b, d⟩ hx hne
    simp only [mem_sigma, mem_filter, mem_Icc, Nat.mem_divisors] at hx
    obtain ⟨⟨hb1, -⟩, ⟨hdb, -⟩, c, rfl⟩ := hx
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdb (by omega)
    simp only
    rw [Nat.mul_div_cancel_left c (Nat.mul_pos hd0 hd0), Nat.div_div_eq_div_mul]
    congr 4
    ring

/-- **Möbius over sixth powers, FC's `Q`.** For real `x ≥ 0`, `Q(x) = ∑_{d ≤ x} μ(d) S⌊x / d⁶⌋`
(terms with `d⁶ > x` vanish). -/
theorem Q_eq_sum_moebius_S {x : ℝ} (hx : 0 ≤ x) :
    (PowerfulNumbersDensity.Q x : ℤ) = ∑ d ∈ Icc 1 ⌊x⌋₊, μ d * S ⌊x / ((d ^ 6 : ℕ) : ℝ)⌋₊ := by
  rw [Q_eq_card hx, card_powerful_eq_sum_moebius]
  refine sum_congr rfl fun d _ => ?_
  rw [Nat.floor_div_natCast]

end moebius

end PowerfulFC.BG1
end
end

-- ===== LeanClassics.VanDerCorput =====
section
/-
# Van der Corput estimates, rung V1: the Kusmin–Landau first-derivative test

`e x = exp(2πix)`.

`kusmin_landau_discrete`: let `x : ℕ → ℝ` have differences `δₙ = x(n+1) − x(n)` that are nondecreasing
and lie in `[k + λ, k + 1 − λ]` for one integer `k` and `0 < λ ≤ 1/2`, for every `n + 1 < N`. Then
`‖∑_{n<N} e(x n)‖ ≤ cot(πλ/2)`.

`kusmin_landau`: let `f` be differentiable with derivative `f'` on `[m, m + N − 1]` (`m : ℤ`), `f'` monotone
(nondecreasing or nonincreasing) there and `k + λ ≤ f' ≤ k + 1 − λ` there. Then
`‖∑_{n<N} e(f(m + n))‖ ≤ cot(πλ/2)`, and `kusmin_landau_inv` gives `≤ 1/λ`.

This is Graham–Kolesnik, *Van der Corput's method of exponential sums*, Theorem 2.1 (there `‖f'‖ ≥ λ` with
`f'` monotone; for a derivative that never reaches a near-integer value the two hypotheses are the same, since
`f'` has the intermediate value property), with Kusmin's and Landau's constant `cot(πλ/2)`. Only the integers
of the closed interval on which the hypotheses hold are summed.

Proof (Kusmin–Landau). Subtract `k n` from `x n` (it does not change `e(x n)`), so `λ ≤ δₙ ≤ 1 − λ`. With
`zₙ = e(xₙ)` and `cₙ = −1/2 − (i/2) cot(πδₙ)` one has `cₙ (e(δₙ) − 1) = 1`, so `zₙ = cₙ (zₙ₊₁ − zₙ)`.
Abel summation gives `∑_{n ≤ L+1} zₙ = (1 + c_L) z_{L+1} − c₀ z₀ + ∑_{n<L} (cₙ − cₙ₊₁) zₙ₊₁`. Here
`‖c₀‖, ‖1 + c_L‖ ≤ 1/(2 sin πλ)`, and `cₙ − cₙ₊₁ = (i/2)(cot πδₙ₊₁ − cot πδₙ)` telescopes because `cot` is
decreasing on `(0, π)`, to at most `cot πλ`. The total is `1/sin πλ + cot πλ = cot(πλ/2)`.
-/

namespace LeanClassics.VanDerCorput

open Real Finset

/-- `e(x) = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (((2 * π * x : ℝ) : ℂ) * Complex.I)

theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  exact Complex.norm_exp_ofReal_mul_I _

theorem e_eq (x : ℝ) : e x = (Real.cos (2 * π * x) : ℂ) + (Real.sin (2 * π * x) : ℂ) * Complex.I := by
  unfold e
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem e_intCast_mul (k : ℤ) (n : ℕ) : e ((k : ℝ) * n) = 1 := by
  unfold e
  have : (((2 * π * ((k : ℝ) * n) : ℝ) : ℂ) * Complex.I) = ((k * n : ℤ) : ℂ) * (2 * π * Complex.I) := by
    push_cast
    ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem e_neg (x : ℝ) : e (-x) = (starRingEnd ℂ) (e x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `cot` is nonincreasing on `(0, π)`: for `0 < πa ≤ πb < π`, `cot πb ≤ cot πa` (as `cos/sin`). -/
theorem cot_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    Real.cos (π * b) / Real.sin (π * b) ≤ Real.cos (π * a) / Real.sin (π * a) := by
  have hsa : 0 < Real.sin (π * a) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hsb : 0 < Real.sin (π * b) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  rw [div_le_div_iff₀ hsb hsa]
  have h := Real.sin_sub (π * b) (π * a)
  have hnn : 0 ≤ Real.sin (π * b - π * a) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  linarith

/-- On `[λ, 1 − λ]`, `sin(πδ) ≥ sin(πλ)`. -/
theorem sin_ge {lam δ : ℝ} (h1 : lam ≤ δ) (h2 : δ ≤ 1 - lam) (hlam : 0 < lam) :
    Real.sin (π * lam) ≤ Real.sin (π * δ) := by
  rcases le_total δ (1 / 2) with hd | hd
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  · have : Real.sin (π * δ) = Real.sin (π * (1 - δ)) := by
      rw [show π * (1 - δ) = π - π * δ by ring, Real.sin_pi_sub]
    rw [this]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-- The Kusmin–Landau coefficient `c(δ) = −1/2 − (i/2) cot(πδ)`. -/
noncomputable def cKL (δ : ℝ) : ℂ :=
  -1 / 2 - Complex.I / 2 * ((Real.cos (π * δ) / Real.sin (π * δ) : ℝ) : ℂ)

theorem cKL_mul (δ : ℝ) (h : Real.sin (π * δ) ≠ 0) : cKL δ * (e δ - 1) = 1 := by
  have h2 : 2 * π * δ = 2 * (π * δ) := by ring
  rw [e_eq, h2, Real.cos_two_mul, Real.sin_two_mul]
  unfold cKL
  have hpy := Real.sin_sq_add_cos_sq (π * δ)
  have hgs : Real.cos (π * δ) / Real.sin (π * δ) * Real.sin (π * δ) = Real.cos (π * δ) := by
    field_simp
  generalize Real.cos (π * δ) / Real.sin (π * δ) = g at *
  generalize hq : Real.cos (π * δ) ^ 2 = q at *
  generalize Real.sin (π * δ) = s at *
  generalize Real.cos (π * δ) = co at *
  apply Complex.ext
  · simp
    linear_combination co * hgs + hq
  · simp
    linear_combination s * hgs - g * hpy

theorem norm_cKL_aux (s co g : ℝ) (hs : 0 < s) (hpy : s ^ 2 + co ^ 2 = 1) (hg : g = co / s) :
    ‖(-1 / 2 - Complex.I / 2 * (g : ℂ) : ℂ)‖ = 1 / (2 * s) ∧
      ‖(1 + (-1 / 2 - Complex.I / 2 * (g : ℂ)) : ℂ)‖ = 1 / (2 * s) := by
  have hr : 0 ≤ 1 / (2 * s) := by positivity
  constructor
  · rw [← sq_eq_sq₀ (norm_nonneg _) hr, Complex.sq_norm, Complex.normSq_apply]
    simp
    rw [hg]
    field_simp
    linear_combination hpy
  · rw [← sq_eq_sq₀ (norm_nonneg _) hr, Complex.sq_norm, Complex.normSq_apply]
    simp
    rw [hg]
    field_simp
    linear_combination hpy

theorem norm_cKL (δ : ℝ) (h : 0 < Real.sin (π * δ)) : ‖cKL δ‖ = 1 / (2 * Real.sin (π * δ)) :=
  (norm_cKL_aux _ (Real.cos (π * δ)) _ h (Real.sin_sq_add_cos_sq _) rfl).1

theorem norm_one_add_cKL (δ : ℝ) (h : 0 < Real.sin (π * δ)) :
    ‖1 + cKL δ‖ = 1 / (2 * Real.sin (π * δ)) :=
  (norm_cKL_aux _ (Real.cos (π * δ)) _ h (Real.sin_sq_add_cos_sq _) rfl).2

theorem norm_cKL_sub (a b : ℝ) :
    ‖cKL a - cKL b‖ =
      |Real.cos (π * b) / Real.sin (π * b) - Real.cos (π * a) / Real.sin (π * a)| / 2 := by
  unfold cKL
  have : (-1 / 2 - Complex.I / 2 * ((Real.cos (π * a) / Real.sin (π * a) : ℝ) : ℂ)) -
      (-1 / 2 - Complex.I / 2 * ((Real.cos (π * b) / Real.sin (π * b) : ℝ) : ℂ)) =
      ((((Real.cos (π * b) / Real.sin (π * b) - Real.cos (π * a) / Real.sin (π * a)) / 2 : ℝ) : ℂ)) *
        Complex.I := by
    push_cast
    ring
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_two]

/-- Abel summation for `zₙ = cₙ (zₙ₊₁ − zₙ)`, `n < L + 1`. -/
theorem abel (z c : ℕ → ℂ) (L : ℕ) (hz : ∀ n, n < L + 1 → z n = c n * (z (n + 1) - z n)) :
    ∑ n ∈ range (L + 2), z n =
      (1 + c L) * z (L + 1) - c 0 * z 0 + ∑ n ∈ range L, (c n - c (n + 1)) * z (n + 1) := by
  have key : ∀ m, m < L + 1 → ∑ n ∈ range (m + 1), z n =
      c m * z (m + 1) - c 0 * z 0 + ∑ n ∈ range m, (c n - c (n + 1)) * z (n + 1) := by
    intro m
    induction m with
    | zero =>
      intro h
      simp only [zero_add, range_one, sum_singleton, range_zero, sum_empty, add_zero]
      have := hz 0 h
      linear_combination this
    | succ m ih =>
      intro h
      rw [sum_range_succ, ih (by omega), sum_range_succ]
      have := hz (m + 1) h
      linear_combination this
  rw [sum_range_succ, key L (by omega)]
  ring

/-- The constant: `(1 + cos πλ)/sin πλ = cot(πλ/2)`. -/
theorem cot_half (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1 / 2) :
    Real.cot (π * lam / 2) = (1 + Real.cos (π * lam)) / Real.sin (π * lam) := by
  have hu : π * lam = 2 * (π * lam / 2) := by ring
  have hs : 0 < Real.sin (π * lam / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc : 0 < Real.cos (π * lam / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  rw [Real.cot_eq_cos_div_sin, hu, Real.cos_two_mul, Real.sin_two_mul]
  field_simp
  ring

/-- **Kusmin–Landau, discrete form.** Nondecreasing differences in `[k + λ, k + 1 − λ]` give
`‖∑_{n<N} e(xₙ)‖ ≤ cot(πλ/2)`. -/
theorem kusmin_landau_discrete (x : ℕ → ℝ) (N : ℕ) (k : ℤ) (lam : ℝ) (hlam : 0 < lam)
    (hlam' : lam ≤ 1 / 2)
    (hδ : ∀ n, n + 1 < N → (k : ℝ) + lam ≤ x (n + 1) - x n ∧ x (n + 1) - x n ≤ k + 1 - lam)
    (hmono : ∀ n, n + 2 < N → x (n + 1) - x n ≤ x (n + 2) - x (n + 1)) :
    ‖∑ n ∈ range N, e (x n)‖ ≤ Real.cot (π * lam / 2) := by
  rw [cot_half lam hlam hlam']
  have hsl : 0 < Real.sin (π * lam) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hcl : 0 ≤ Real.cos (π * lam) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  -- shift by `k n`
  set y : ℕ → ℝ := fun n => x n - k * n with hy
  have hey : ∀ n, e (x n) = e (y n) := by
    intro n
    have : x n = y n + k * n := by simp [hy]
    rw [this, e_add, e_intCast_mul, mul_one]
  simp_rw [hey]
  set d : ℕ → ℝ := fun n => y (n + 1) - y n with hd
  have hd' : ∀ n, d n = x (n + 1) - x n - k := by
    intro n; simp only [hd, hy]; push_cast; ring
  match N with
  | 0 => simp; positivity
  | 1 =>
    simp only [range_one, sum_singleton, norm_e]
    rw [le_div_iff₀ hsl]
    nlinarith [Real.sin_le_one (π * lam)]
  | L + 2 =>
    have hdI : ∀ n, n < L + 1 → lam ≤ d n ∧ d n ≤ 1 - lam := by
      intro n hn
      obtain ⟨h1, h2⟩ := hδ n (by omega)
      rw [hd' n]; constructor <;> linarith
    have hsin : ∀ n, n < L + 1 → Real.sin (π * lam) ≤ Real.sin (π * d n) := by
      intro n hn
      exact sin_ge (hdI n hn).1 (hdI n hn).2 hlam
    set g : ℕ → ℝ := fun n => Real.cos (π * d n) / Real.sin (π * d n) with hg
    have hgG : ∀ n, n < L + 1 → g n ≤ Real.cos (π * lam) / Real.sin (π * lam) ∧
        -(Real.cos (π * lam) / Real.sin (π * lam)) ≤ g n := by
      intro n hn
      obtain ⟨h1, h2⟩ := hdI n hn
      constructor
      · exact cot_anti hlam h1 (by linarith)
      · have := cot_anti (a := d n) (b := 1 - lam) (by linarith) h2 (by linarith)
        have e1 : Real.cos (π * (1 - lam)) = -Real.cos (π * lam) := by
          rw [show π * (1 - lam) = π - π * lam by ring, Real.cos_pi_sub]
        have e2 : Real.sin (π * (1 - lam)) = Real.sin (π * lam) := by
          rw [show π * (1 - lam) = π - π * lam by ring, Real.sin_pi_sub]
        rw [e1, e2, neg_div] at this
        exact this
    have hganti : ∀ n, n < L → g (n + 1) ≤ g n := by
      intro n hn
      have hm := hmono n (by omega)
      have h1 := hdI n (by omega)
      have h2 := hdI (n + 1) (by omega)
      have : d n ≤ d (n + 1) := by
        rw [hd' n, hd' (n + 1)]; linarith
      exact cot_anti (by linarith [h1.1]) this (by linarith [h2.2])
    set c : ℕ → ℂ := fun n => cKL (d n) with hc
    have hz : ∀ n, n < L + 1 → e (y n) = c n * (e (y (n + 1)) - e (y n)) := by
      intro n hn
      have hyn : y (n + 1) = y n + d n := by simp only [hd]; ring
      rw [hyn, e_add]
      have := cKL_mul (d n) (ne_of_gt (lt_of_lt_of_le hsl (hsin n hn)))
      simp only [hc]
      linear_combination (-(e (y n))) * this
    rw [abel (fun n => e (y n)) c L hz]
    have hc0 : ‖c 0‖ ≤ 1 / (2 * Real.sin (π * lam)) := by
      simp only [hc]
      rw [norm_cKL _ (lt_of_lt_of_le hsl (hsin 0 (by omega)))]
      gcongr
      exact hsin 0 (by omega)
    have hcL : ‖1 + c L‖ ≤ 1 / (2 * Real.sin (π * lam)) := by
      simp only [hc]
      rw [norm_one_add_cKL _ (lt_of_lt_of_le hsl (hsin L (by omega)))]
      gcongr
      exact hsin L (by omega)
    have hmid : ∑ n ∈ range L, ‖(c n - c (n + 1)) * e (y (n + 1))‖ = (g 0 - g L) / 2 := by
      have : ∀ n ∈ range L, ‖(c n - c (n + 1)) * e (y (n + 1))‖ = (g n - g (n + 1)) / 2 := by
        intro n hn
        rw [mem_range] at hn
        rw [norm_mul, norm_e, mul_one]
        simp only [hc]
        rw [norm_cKL_sub]
        have := hganti n hn
        simp only [hg] at this
        rw [abs_of_nonpos (by linarith)]
        simp only [hg]
        ring
      rw [sum_congr rfl this, ← sum_div, sum_range_sub' g L]
    have hg0 := (hgG 0 (by omega)).1
    have hgL := (hgG L (by omega)).2
    calc ‖(1 + c L) * e (y (L + 1)) - c 0 * e (y 0) +
          ∑ n ∈ range L, (c n - c (n + 1)) * e (y (n + 1))‖
        ≤ ‖(1 + c L) * e (y (L + 1))‖ + ‖c 0 * e (y 0)‖ +
          ∑ n ∈ range L, ‖(c n - c (n + 1)) * e (y (n + 1))‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          · exact norm_sub_le _ _
          · exact norm_sum_le _ _
      _ = ‖1 + c L‖ + ‖c 0‖ + (g 0 - g L) / 2 := by
          rw [hmid, norm_mul, norm_mul, norm_e, norm_e, mul_one, mul_one]
      _ ≤ 1 / (2 * Real.sin (π * lam)) + 1 / (2 * Real.sin (π * lam)) +
          Real.cos (π * lam) / Real.sin (π * lam) := by
          linarith
      _ = (1 + Real.cos (π * lam)) / Real.sin (π * lam) := by
          field_simp
          ring

/-- **Kusmin–Landau, nondecreasing `f'`.** -/
theorem kusmin_landau_mono (f f' : ℝ → ℝ) (m : ℤ) (N : ℕ) (k : ℤ) (lam : ℝ) (hlam : 0 < lam)
    (hlam' : lam ≤ 1 / 2)
    (hf : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t)
    (hmono : MonotoneOn f' (Set.Icc (m : ℝ) (m + N - 1)))
    (hk : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), (k : ℝ) + lam ≤ f' t ∧ f' t ≤ k + 1 - lam) :
    ‖∑ n ∈ range N, e (f (m + n))‖ ≤ Real.cot (π * lam / 2) := by
  -- the mean value theorem on `[m + n, m + n + 1]`
  have mvt : ∀ n : ℕ, n + 1 < N → ∃ ξ ∈ Set.Icc ((m : ℝ) + n) (m + n + 1),
      ξ ∈ Set.Icc (m : ℝ) (m + N - 1) ∧ f (m + (n + 1 : ℕ)) - f (m + n) = f' ξ := by
    intro n hn
    have hN : ((n : ℝ) + 1 + 1) ≤ N := by exact_mod_cast hn
    have hsub : Set.Icc ((m : ℝ) + n) (m + n + 1) ⊆ Set.Icc (m : ℝ) (m + N - 1) := by
      intro t ht
      exact ⟨by linarith [ht.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)], by linarith [ht.2]⟩
    obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope f f' (show (m : ℝ) + n < m + n + 1 by linarith)
      (fun t ht => (hf t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => hf t (hsub (Set.Ioo_subset_Icc_self ht)))
    refine ⟨ξ, Set.Ioo_subset_Icc_self hξ, hsub (Set.Ioo_subset_Icc_self hξ), ?_⟩
    rw [hξe]
    push_cast
    ring_nf
  apply kusmin_landau_discrete (fun n => f (m + n)) N k lam hlam hlam'
  · intro n hn
    obtain ⟨ξ, -, hξ, he⟩ := mvt n hn
    rw [he]
    exact hk ξ hξ
  · intro n hn
    obtain ⟨ξ₁, hξ₁, hξ₁', he₁⟩ := mvt n (by omega)
    obtain ⟨ξ₂, hξ₂, hξ₂', he₂⟩ := mvt (n + 1) hn
    rw [he₁, show n + 2 = (n + 1) + 1 by ring, he₂]
    apply hmono hξ₁' hξ₂'
    have := hξ₁.2
    have := hξ₂.1
    push_cast at *
    linarith

/-- **Kusmin–Landau** (Graham–Kolesnik Theorem 2.1, with the constant `cot(πλ/2)`). If `f' = f′` on
`[m, m + N − 1]`, `f'` is monotone there and `k + λ ≤ f' ≤ k + 1 − λ` there (`k ∈ ℤ`, `0 < λ ≤ 1/2`), then
`‖∑_{n<N} e(f(m + n))‖ ≤ cot(πλ/2)`. -/
theorem kusmin_landau (f f' : ℝ → ℝ) (m : ℤ) (N : ℕ) (k : ℤ) (lam : ℝ) (hlam : 0 < lam)
    (hlam' : lam ≤ 1 / 2)
    (hf : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t)
    (hmono : MonotoneOn f' (Set.Icc (m : ℝ) (m + N - 1)) ∨
      AntitoneOn f' (Set.Icc (m : ℝ) (m + N - 1)))
    (hk : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), (k : ℝ) + lam ≤ f' t ∧ f' t ≤ k + 1 - lam) :
    ‖∑ n ∈ range N, e (f (m + n))‖ ≤ Real.cot (π * lam / 2) := by
  rcases hmono with hmono | hanti
  · exact kusmin_landau_mono f f' m N k lam hlam hlam' hf hmono hk
  · have h := kusmin_landau_mono (fun t => -f t) (fun t => -f' t) m N (-k - 1) lam hlam hlam'
      (fun t ht => (hf t ht).neg) (fun a ha b hb hab => neg_le_neg (hanti ha hb hab))
      (fun t ht => by
        obtain ⟨h1, h2⟩ := hk t ht
        push_cast
        constructor <;> linarith)
    simp_rw [e_neg, ← map_sum, Complex.norm_conj] at h
    exact h

/-- **Kusmin–Landau, `≪ 1/λ` form**: under the hypotheses of `kusmin_landau`,
`‖∑_{n<N} e(f(m + n))‖ ≤ 1/λ`. -/
theorem kusmin_landau_inv (f f' : ℝ → ℝ) (m : ℤ) (N : ℕ) (k : ℤ) (lam : ℝ) (hlam : 0 < lam)
    (hlam' : lam ≤ 1 / 2)
    (hf : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t)
    (hmono : MonotoneOn f' (Set.Icc (m : ℝ) (m + N - 1)) ∨
      AntitoneOn f' (Set.Icc (m : ℝ) (m + N - 1)))
    (hk : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), (k : ℝ) + lam ≤ f' t ∧ f' t ≤ k + 1 - lam) :
    ‖∑ n ∈ range N, e (f (m + n))‖ ≤ 1 / lam := by
  refine (kusmin_landau f f' m N k lam hlam hlam' hf hmono hk).trans ?_
  rw [cot_half lam hlam hlam']
  have hsl : 2 * lam ≤ Real.sin (π * lam) := by
    have := Real.mul_le_sin (x := π * lam) (by positivity) (by nlinarith [Real.pi_pos])
    rw [show 2 / π * (π * lam) = 2 * lam by field_simp] at this
    exact this
  have hc : Real.cos (π * lam) ≤ 1 := Real.cos_le_one _
  rw [div_le_div_iff₀ (by linarith) hlam]
  nlinarith

end LeanClassics.VanDerCorput
end

-- ===== LeanClassics.VanDerCorputSecond =====
section
/-
# Van der Corput estimates, rung V2: the second-derivative test

`van_der_corput_second`: let `f` have derivative `f'` and `f'` have derivative `f''` on `[m, m + N − 1]`
(`m : ℤ`), with `λ ≤ f'' ≤ αλ` there and `λ > 0`. Then
`‖∑_{n<N} e(f(m + n))‖ ≤ 4 α N √λ + 7/√λ`.

`van_der_corput_second_delta` is the form with a free cut-off `0 < δ ≤ 1/2`: for `N ≥ 1`,
`‖∑_{n<N} e(f(m + n))‖ ≤ (αλ(N − 1) + 2) · (2δ/λ + 1 + 1/δ)`.

This is Graham–Kolesnik, *Van der Corput's method of exponential sums*, Theorem 2.2
(`∑ e(f(n)) ≪ α (b − a) λ^{1/2} + λ^{−1/2}`), with explicit constants.

Proof. Put `w = f' + δ` and cut `[m, m + N − 1]` into maximal blocks of integers on which `⌊w⌋` is a
constant `j`; there are at most `⌊w(end)⌋ − ⌊w(m)⌋ + 1 ≤ αλ(N − 1) + 2` of them. Inside a block `f'` rises
through `[j − δ, j + 1 − δ)`. Its first part, where `f' < j + δ`, has fewer than `2δ/λ + 1` points (`f'` grows
by at least `λ` per step and the part spans less than `2δ`), and is bounded trivially. On the rest
`j + δ ≤ f' ≤ j + 1 − δ` on the whole real interval (since `f'` is monotone), so Kusmin–Landau
(`kusmin_landau_inv`) bounds it by `1/δ`. Taking `δ = √λ` (when `λ ≤ 1/4`; otherwise the trivial bound `N`
already suffices, as `α ≥ 1`) gives the stated form.
-/

namespace LeanClassics.VanDerCorput

open Real Finset

/-- The trivial bound `‖∑_{n<N} e(xₙ)‖ ≤ N`. -/
theorem norm_sum_e_le (x : ℕ → ℝ) (N : ℕ) : ‖∑ n ∈ range N, e (x n)‖ ≤ N := by
  refine (norm_sum_le _ _).trans ?_
  simp [norm_e]

/-- Splitting `∑_{n<N} g(m + n)` at `r ≤ N`. -/
theorem sum_split (g : ℝ → ℂ) (m : ℤ) (N r : ℕ) (hr : r ≤ N) :
    ∑ n ∈ range N, g (m + n) =
      ∑ n ∈ range r, g (m + n) + ∑ n ∈ range (N - r), g (((m + r : ℤ) : ℝ) + n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [Nat.add_sub_cancel_left, sum_range_add]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  congr 1
  push_cast
  ring

/-- A sub-block `[m + s, m + s + q − 1]` of `[m, m + N − 1]` when `s + q ≤ N`. -/
theorem Icc_sub (m : ℤ) (N s q : ℕ) (h : s + q ≤ N) :
    Set.Icc ((m + s : ℤ) : ℝ) ((m + s : ℤ) + (q : ℝ) - 1) ⊆ Set.Icc (m : ℝ) (m + N - 1) := by
  intro t ⟨h1, h2⟩
  have hsq : (s : ℝ) + q ≤ N := by exact_mod_cast h
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  push_cast at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- The mean value theorem for `f'`: `a ≤ f'' ≤ b` on `I = [m, m + N − 1]` gives
`a (t − s) ≤ f' t − f' s ≤ b (t − s)` for `s ≤ t` in `I`. -/
theorem mvt_bounds (f' f'' : ℝ → ℝ) (lo hi : ℝ) (a b : ℝ)
    (hf' : ∀ t ∈ Set.Icc lo hi, HasDerivAt f' (f'' t) t)
    (ha : ∀ t ∈ Set.Icc lo hi, a ≤ f'' t) (hb : ∀ t ∈ Set.Icc lo hi, f'' t ≤ b)
    (s t : ℝ) (hs : s ∈ Set.Icc lo hi) (ht : t ∈ Set.Icc lo hi) (hst : s ≤ t) :
    a * (t - s) ≤ f' t - f' s ∧ f' t - f' s ≤ b * (t - s) := by
  rcases hst.eq_or_lt with h | h
  · subst h; simp
  have hsub : Set.Icc s t ⊆ Set.Icc lo hi := Set.Icc_subset_Icc hs.1 ht.2
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope f' f'' h
    (fun x hx => (hf' x (hsub hx)).continuousAt.continuousWithinAt)
    (fun x hx => hf' x (hsub (Set.Ioo_subset_Icc_self hx)))
  have hξI := hsub (Set.Ioo_subset_Icc_self hξ)
  have hpos : 0 < t - s := by linarith
  have key : f' t - f' s = f'' ξ * (t - s) := by
    rw [hξe]; field_simp
  rw [key]
  exact ⟨mul_le_mul_of_nonneg_right (ha ξ hξI) hpos.le,
    mul_le_mul_of_nonneg_right (hb ξ hξI) hpos.le⟩

/-- One block. With `j = ⌊f'(m) + δ⌋` there is `1 ≤ r ≤ N` such that the first `r` terms have
`‖∑_{n<r} e(f(m + n))‖ ≤ 2δ/λ + 1 + 1/δ`, and if `r < N` then `f'(m + r) + δ ≥ j + 1`. -/
theorem block (f f' : ℝ → ℝ) (lam δ : ℝ) (hlam : 0 < lam) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (m : ℤ) (N : ℕ) (hN : 1 ≤ N)
    (hf : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t)
    (hg : ∀ s ∈ Set.Icc (m : ℝ) (m + N - 1), ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), s ≤ t →
      lam * (t - s) ≤ f' t - f' s) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ N ∧
      (r < N → (⌊f' m + δ⌋ : ℝ) + 1 ≤ f' (m + r) + δ) ∧
      ‖∑ n ∈ range r, e (f (m + n))‖ ≤ 2 * δ / lam + 1 + 1 / δ := by
  classical
  set j : ℤ := ⌊f' m + δ⌋ with hj
  have hj1 : (j : ℝ) ≤ f' m + δ := Int.floor_le _
  have hj2 : f' m + δ < j + 1 := Int.lt_floor_add_one _
  have hmem : ∀ n : ℕ, n < N → ((m : ℝ) + n) ∈ Set.Icc (m : ℝ) (m + N - 1) := by
    intro n hn
    have : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
    exact ⟨by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)], by linarith⟩
  have hmono : ∀ s ∈ Set.Icc (m : ℝ) (m + N - 1), ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), s ≤ t →
      f' s ≤ f' t := by
    intro s hs t ht hst
    have := hg s hs t ht hst
    nlinarith
  -- the block end `r`
  obtain ⟨r, hrN, hrspec, hrmin⟩ : ∃ r : ℕ, r ≤ N ∧ (r = N ∨ (j : ℝ) + 1 ≤ f' (m + r) + δ) ∧
      ∀ n < r, f' (m + n) + δ < j + 1 := by
    have hex : ∃ n : ℕ, n = N ∨ (j : ℝ) + 1 ≤ f' (m + n) + δ := ⟨N, Or.inl rfl⟩
    refine ⟨Nat.find hex, Nat.find_min' hex (Or.inl rfl), Nat.find_spec hex, fun n hn => ?_⟩
    have := Nat.find_min hex hn
    push Not at this
    exact this.2
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      rcases hrspec with h | h
      · omega
      · simp at h; linarith
    · exact h
  -- the end `s` of the near-integer part
  obtain ⟨s, hsr, hsspec, hsmin⟩ : ∃ s : ℕ, s ≤ r ∧ (s = r ∨ (j : ℝ) + δ ≤ f' (m + s)) ∧
      ∀ n < s, f' (m + n) < j + δ := by
    have hex : ∃ n : ℕ, n = r ∨ (j : ℝ) + δ ≤ f' (m + n) := ⟨r, Or.inl rfl⟩
    refine ⟨Nat.find hex, Nat.find_min' hex (Or.inl rfl), Nat.find_spec hex, fun n hn => ?_⟩
    have := Nat.find_min hex hn
    push Not at this
    exact this.2
  refine ⟨r, hr1, hrN, fun h => (hrspec.resolve_left (by omega)), ?_⟩
  rw [sum_split (fun x => e (f x)) m r s hsr]
  refine (norm_add_le _ _).trans ?_
  have hpart1 : ‖∑ n ∈ range s, e (f (m + n))‖ ≤ 2 * δ / lam + 1 := by
    refine (norm_sum_e_le (fun n => f (m + n)) s).trans ?_
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp; positivity
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have h1 := hsmin s' (by omega)
    have h2 := hg m (by simpa using hmem 0 (by omega)) (m + s') (hmem s' (by omega))
      (by linarith [(Nat.cast_nonneg s' : (0 : ℝ) ≤ s')])
    have hlt : lam * s' < 2 * δ := by
      have : (m : ℝ) + s' - m = s' := by ring
      rw [this] at h2
      linarith
    have : (s' : ℝ) ≤ 2 * δ / lam := by
      rw [le_div_iff₀ hlam]; linarith
    push_cast
    linarith
  have hpart2 : ‖∑ n ∈ range (r - s), e (f (((m + s : ℤ) : ℝ) + n))‖ ≤ 1 / δ := by
    rcases hsr.eq_or_lt with h | h
    · rw [h, Nat.sub_self]; simp; positivity
    have hsub := Icc_sub m N s (r - s) (by omega)
    have hcast : ((m + s : ℤ) : ℝ) + ((r - s : ℕ) : ℝ) - 1 = m + ((r - 1 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hsr, Nat.cast_sub hr1]
      ring
    have hlast := hrmin (r - 1) (by omega)
    have hfirst : (j : ℝ) + δ ≤ f' (m + s) := hsspec.resolve_left (by omega)
    refine kusmin_landau_inv f f' (m + s) (r - s) j δ hδ hδ' (fun t ht => hf t (hsub ht))
      (Or.inl fun a ha b hb hab => hmono a (hsub ha) b (hsub hb) hab) ?_
    intro t ht
    have htI := hsub ht
    constructor
    · have hsI := hmem s (by omega)
      have := hmono (m + s) hsI t htI (by have := ht.1; push_cast at this; linarith)
      linarith
    · have hlI := hmem (r - 1) (by omega)
      have := hmono t htI (m + ((r - 1 : ℕ) : ℝ)) hlI (by rw [← hcast]; exact ht.2)
      linarith
  linarith

/-- The block decomposition, by induction on the number `K` of integers crossed by `f' + δ`. -/
theorem blocks (f f' : ℝ → ℝ) (lam δ : ℝ) (hlam : 0 < lam) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (K : ℕ) :
    ∀ (m : ℤ) (N : ℕ), 1 ≤ N →
      (∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t) →
      (∀ s ∈ Set.Icc (m : ℝ) (m + N - 1), ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), s ≤ t →
        lam * (t - s) ≤ f' t - f' s) →
      ⌊f' (m + N - 1) + δ⌋ ≤ ⌊f' m + δ⌋ + K →
      ‖∑ n ∈ range N, e (f (m + n))‖ ≤ (K + 1) * (2 * δ / lam + 1 + 1 / δ) := by
  have hC : 0 ≤ 2 * δ / lam + 1 + 1 / δ := by positivity
  induction K with
  | zero =>
    intro m N hN hf hg hK
    obtain ⟨r, hr1, hrN, hrnext, hr⟩ := block f f' lam δ hlam hδ hδ' m N hN hf hg
    rcases hrN.eq_or_lt with h | h
    · subst h; simpa using hr
    · exfalso
      have h1 := hrnext h
      have hrI : ((m : ℝ) + r) ∈ Set.Icc (m : ℝ) (m + N - 1) := by
        have : (r : ℝ) + 1 ≤ N := by exact_mod_cast h
        exact ⟨by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)], by linarith⟩
      have hNI : ((m : ℝ) + N - 1) ∈ Set.Icc (m : ℝ) (m + N - 1) := ⟨hrI.1.trans hrI.2, le_rfl⟩
      have h2 := hg _ hrI _ hNI hrI.2
      have h2' : 0 ≤ lam * ((m : ℝ) + N - 1 - (m + r)) := mul_nonneg hlam.le (by linarith [hrI.2])
      have h3 : (⌊f' m + δ⌋ : ℝ) + 1 ≤ f' (m + N - 1) + δ := by linarith
      have h4 : ⌊f' m + δ⌋ + 1 ≤ ⌊f' (m + N - 1) + δ⌋ := by
        rw [Int.le_floor]; push_cast; exact h3
      push_cast at hK
      omega
  | succ K ih =>
    intro m N hN hf hg hK
    obtain ⟨r, hr1, hrN, hrnext, hr⟩ := block f f' lam δ hlam hδ hδ' m N hN hf hg
    rcases hrN.eq_or_lt with h | h
    · subst h
      refine hr.trans ?_
      have : (1 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
      nlinarith
    rw [sum_split (fun x => e (f x)) m N r hrN]
    refine (norm_add_le _ _).trans ?_
    have hsub := Icc_sub m N r (N - r) (by omega)
    have hend : ((m + r : ℤ) : ℝ) + ((N - r : ℕ) : ℝ) - 1 = m + N - 1 := by
      push_cast [Nat.cast_sub hrN]
      ring
    have hstart : ((m + r : ℤ) : ℝ) = m + r := by push_cast; ring
    have h1 := hrnext h
    have hfl : ⌊f' m + δ⌋ + 1 ≤ ⌊f' ((m + r : ℤ) : ℝ) + δ⌋ := by
      rw [Int.le_floor, hstart]; push_cast; exact h1
    have hrest := ih (m + r) (N - r) (by omega) (fun t ht => hf t (hsub ht))
      (fun s hs t ht hst => hg s (hsub hs) t (hsub ht) hst)
      (by rw [hend]; push_cast at hK; omega)
    have hrest' : ‖∑ n ∈ range (N - r), e (f (((m + r : ℤ) : ℝ) + n))‖ ≤
        (K + 1) * (2 * δ / lam + 1 + 1 / δ) := hrest
    have hc : ((K + 1 : ℕ) : ℝ) + 1 = (K + 1) + 1 := by push_cast; ring
    rw [hc]
    linarith

/-- **Van der Corput's second-derivative test, with a free cut-off `δ`.** If `f' = f′` and `f'' = f′′` on
`[m, m + N − 1]`, `N ≥ 1`, and `λ ≤ f'' ≤ αλ` there (`λ > 0`), then for every `0 < δ ≤ 1/2`,
`‖∑_{n<N} e(f(m + n))‖ ≤ (αλ(N − 1) + 2)(2δ/λ + 1 + 1/δ)`. -/
theorem van_der_corput_second_delta (f f' f'' : ℝ → ℝ) (m : ℤ) (N : ℕ) (hN : 1 ≤ N)
    (lam alpha δ : ℝ) (hlam : 0 < lam) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hf : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f' (f'' t) t)
    (hlo : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), lam ≤ f'' t)
    (hhi : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), f'' t ≤ alpha * lam) :
    ‖∑ n ∈ range N, e (f (m + n))‖ ≤ (alpha * lam * (N - 1) + 2) * (2 * δ / lam + 1 + 1 / δ) := by
  have hg : ∀ s ∈ Set.Icc (m : ℝ) (m + N - 1), ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), s ≤ t →
      lam * (t - s) ≤ f' t - f' s :=
    fun s hs t ht hst => (mvt_bounds f' f'' _ _ lam (alpha * lam) hf' hlo hhi s t hs ht hst).1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmI : (m : ℝ) ∈ Set.Icc (m : ℝ) (m + N - 1) := ⟨le_rfl, by linarith⟩
  have heI : ((m : ℝ) + N - 1) ∈ Set.Icc (m : ℝ) (m + N - 1) := ⟨by linarith, le_rfl⟩
  have hS := (mvt_bounds f' f'' _ _ lam (alpha * lam) hf' hlo hhi _ _ hmI heI (by linarith)).2
  have hS0 := hg _ hmI _ heI (by linarith)
  set D : ℤ := ⌊f' (m + N - 1) + δ⌋ - ⌊f' m + δ⌋ with hD
  have hD0 : 0 ≤ D := by
    rw [hD, sub_nonneg]
    exact Int.floor_mono (by nlinarith)
  have hDr : (D : ℝ) ≤ f' (m + N - 1) - f' m + 1 := by
    rw [hD]; push_cast
    have := Int.floor_le (f' (m + N - 1) + δ)
    have := Int.sub_one_lt_floor (f' m + δ)
    linarith
  have hK := blocks f f' lam δ hlam hδ hδ' D.toNat m N hN hf hg
    (by have := Int.self_le_toNat D; omega)
  have hKr : ((D.toNat : ℕ) : ℝ) = D := by
    have := Int.toNat_of_nonneg hD0
    exact_mod_cast this
  rw [hKr] at hK
  refine hK.trans ?_
  have hC : 0 ≤ 2 * δ / lam + 1 + 1 / δ := by positivity
  apply mul_le_mul_of_nonneg_right _ hC
  have : (m : ℝ) + N - 1 - m = N - 1 := by ring
  rw [this] at hS
  linarith

/-- **Van der Corput's second-derivative test** (Graham–Kolesnik Theorem 2.2, explicit). If `f' = f′` and
`f'' = f′′` on `[m, m + N − 1]` and `λ ≤ f'' ≤ αλ` there (`λ > 0`), then
`‖∑_{n<N} e(f(m + n))‖ ≤ 4 α N √λ + 7/√λ`. -/
theorem van_der_corput_second (f f' f'' : ℝ → ℝ) (m : ℤ) (N : ℕ) (lam alpha : ℝ) (hlam : 0 < lam)
    (hf : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f' (f'' t) t)
    (hlo : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), lam ≤ f'' t)
    (hhi : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), f'' t ≤ alpha * lam) :
    ‖∑ n ∈ range N, e (f (m + n))‖ ≤ 4 * alpha * N * √lam + 7 / √lam := by
  have hsq : 0 < √lam := Real.sqrt_pos.mpr hlam
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0; simp; positivity
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmI : (m : ℝ) ∈ Set.Icc (m : ℝ) (m + N - 1) := ⟨le_rfl, by linarith⟩
  have halpha : 1 ≤ alpha := by
    have := (hlo m hmI).trans (hhi m hmI)
    nlinarith
  rcases le_or_gt lam (1 / 4) with hl | hl
  · set δ := √lam with hδdef
    have hδsq : δ ^ 2 = lam := Real.sq_sqrt hlam.le
    have hδ' : δ ≤ 1 / 2 := by nlinarith
    have h := van_der_corput_second_delta f f' f'' m N hN lam alpha δ hlam hsq hδ' hf hf' hlo hhi
    refine h.trans ?_
    rw [← hδsq]
    have hP : 0 ≤ alpha * δ ^ 2 * (N - 1) := by
      have : (0 : ℝ) ≤ N - 1 := by linarith
      positivity
    have e1 : (alpha * δ ^ 2 * (N - 1) + 2) * (2 * δ / δ ^ 2 + 1 + 1 / δ) =
        (alpha * δ ^ 2 * (N - 1) + 2) * (3 + δ) / δ := by
      field_simp
      ring
    have e2 : 4 * alpha * N * δ + 7 / δ = (4 * alpha * N * δ ^ 2 + 7) / δ := by
      field_simp
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ hsq.le
    have hPd : alpha * δ ^ 2 * (N - 1) * δ ≤ alpha * δ ^ 2 * (N - 1) * (1 / 2) :=
      mul_le_mul_of_nonneg_left hδ' hP
    have hN' : alpha * δ ^ 2 * (N - 1) ≤ alpha * δ ^ 2 * N := by
      have : 0 ≤ alpha * δ ^ 2 := by positivity
      nlinarith
    nlinarith
  · refine (norm_sum_e_le (fun n => f (m + n)) N).trans ?_
    have hs : 1 / 2 < √lam := by
      rw [show (1 : ℝ) / 2 = √((1 / 2) ^ 2) by rw [Real.sqrt_sq]; norm_num]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    have h7 : 0 ≤ 7 / √lam := by positivity
    have : (N : ℝ) ≤ 4 * alpha * N * √lam := by
      have : 2 ≤ 4 * alpha * √lam := by nlinarith
      nlinarith
    linarith

end LeanClassics.VanDerCorput
end

-- ===== PowerfulFC.PsiSum =====
section
/-
# Rung BG2: the second-derivative bound for sums of the sawtooth `ψ`

`ψ t = {t} − 1/2` (BG1). Main results, all unconditional:

* `abs_sum_psi_le_delta`: if `λ ≤ f'' ≤ αλ` on `[m, m + N − 1]` (`λ > 0`), then for every `0 < Δ ≤ 1/2`,
  `|∑_{n<N} ψ(f(m + n))| ≤ NΔ/2 + 4αN√(λ/Δ) + 7/√λ`.
* `abs_sum_psi_le`: the same with `Δ = λ^{1/3}`:
  `|∑_{n<N} ψ(f(m + n))| ≤ (1/2 + 4α) N λ^{1/3} + 7 λ^{−1/2}`.

This is the classical van der Corput bound `∑ ψ(f(n)) ≪ N λ^{1/3} + λ^{−1/2}` (e.g. Graham–Kolesnik,
*Van der Corput's method of exponential sums*, Ch. 1 + Thm 2.2; Krätzel, *Lattice points*, Thm 1.9 type), with explicit
constants.

Proof (no truncated Fourier series of `ψ` is needed).
1. `P x = B₂({x}) = {x}² − {x} + 1/6` has the absolutely convergent expansion
   `π² P x = ∑_{h ≥ 1} cos(2πhx)/h²` (Mathlib `hasSum_one_div_nat_pow_mul_cos`, `k = 1`).
2. Sandwich (`P_add_sub_le`, `le_P_sub_sub`): for `0 ≤ Δ ≤ 1`,
   `(P(x + Δ) − P x)/(2Δ) − Δ/2 ≤ ψ x ≤ (P x − P(x − Δ))/(2Δ) + Δ/2` (exact algebra on `{x}`; `P' = 2ψ`).
3. Summing over `n` and expanding `P` (step 1): the shifted differences are `Re((e(h(c+Δ)) − e(hc)) S_h)/(π² h²)`
   with `S_h = ∑_n e(h f(m+n))`, and `|e(hΔ) − 1| ≤ min(2, 2πhΔ)`.
4. `‖S_h‖ ≤ 4α N √(hλ) + 7/√(hλ)` (`LeanClassics.VanDerCorput.van_der_corput_second` on `h f`), and the
   `h`-series is split at `H = ⌊1/Δ⌋`.
-/

open Finset Real LeanClassics.VanDerCorput

noncomputable section

namespace PowerfulFC.BG2

open PowerfulFC.BG1 (ψ)
/-- `P x = B₂({x}) = {x}² − {x} + 1/6`, the periodic second Bernoulli function. -/
def P (x : ℝ) : ℝ := Int.fract x ^ 2 - Int.fract x + 1 / 6

/-- **Fourier series of `P`**: `∑_{h ≥ 0} cos(2πhx)/h² = π² P x` (the `h = 0` term is `0` since `1/0 = 0`). -/
theorem hasSum_cos_P (x : ℝ) :
    HasSum (fun h : ℕ => 1 / (h : ℝ) ^ 2 * Real.cos (2 * π * h * x)) (π ^ 2 * P x) := by
  have hI : Int.fract x ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hI
  have hfun : (fun h : ℕ => 1 / (h : ℝ) ^ (2 * 1) * Real.cos (2 * π * h * Int.fract x)) =
      (fun h : ℕ => 1 / (h : ℝ) ^ 2 * Real.cos (2 * π * h * x)) := by
    funext h
    congr 1
    have : 2 * π * h * Int.fract x = 2 * π * h * x - ((h * ⌊x⌋ : ℤ) : ℝ) * (2 * π) := by
      rw [Int.fract]; push_cast; ring
    rw [this, Real.cos_sub_int_mul_two_pi]
  rw [hfun] at h
  convert h using 1
  change _ = _ * bernoulliFun (2 * 1) (Int.fract x)
  rw [show 2 * 1 = 2 from rfl, bernoulliFun_two, P]
  norm_num [Nat.factorial]
  left; ring

/-- `{x + Δ}` for `0 ≤ Δ ≤ 1`: either `{x} + Δ`, or `{x} + Δ − 1` with `{x} + Δ ≥ 1`. -/
lemma fract_add_cases (x Δ : ℝ) (h0 : 0 ≤ Δ) (h1 : Δ ≤ 1) :
    Int.fract (x + Δ) = Int.fract x + Δ ∨
      (Int.fract (x + Δ) = Int.fract x + Δ - 1 ∧ 1 ≤ Int.fract x + Δ) := by
  have hx : x + Δ = (Int.fract x + Δ) + (⌊x⌋ : ℤ) := by rw [Int.fract]; ring
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  rw [hx, Int.fract_add_intCast]
  rcases lt_or_ge (Int.fract x + Δ) 1 with h | h
  · left; exact Int.fract_eq_self.mpr ⟨by linarith, h⟩
  · right
    refine ⟨?_, h⟩
    have h2 := Int.fract_add_one (Int.fract x + Δ - 1)
    rw [sub_add_cancel] at h2
    rw [h2, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]

/-- Upper sandwich step: `P(x + Δ) − P x ≤ 2Δψ(x) + Δ²` for `0 ≤ Δ ≤ 1`. -/
lemma P_add_sub_le (x Δ : ℝ) (h0 : 0 ≤ Δ) (h1 : Δ ≤ 1) :
    P (x + Δ) - P x ≤ 2 * Δ * ψ x + Δ ^ 2 := by
  unfold P ψ
  rcases fract_add_cases x Δ h0 h1 with h | ⟨h, hge⟩ <;> rw [h]
  · nlinarith
  · nlinarith

/-- Lower sandwich step: `2Δψ(x) − Δ² ≤ P x − P(x − Δ)` for `0 ≤ Δ ≤ 1`. -/
lemma le_P_sub_sub (x Δ : ℝ) (h0 : 0 ≤ Δ) (h1 : Δ ≤ 1) :
    2 * Δ * ψ x - Δ ^ 2 ≤ P x - P (x - Δ) := by
  have hc := fract_add_cases (x - Δ) Δ h0 h1
  rw [sub_add_cancel] at hc
  unfold P ψ
  rcases hc with h | ⟨h, hge⟩
  · have : Int.fract (x - Δ) = Int.fract x - Δ := by linarith
    rw [this]; nlinarith
  · have : Int.fract (x - Δ) = Int.fract x - Δ + 1 := by linarith
    have hf1 := Int.fract_lt_one (x - Δ)
    rw [this]; nlinarith

/- ### From `P` to exponential sums -/

lemma re_e (t : ℝ) : (e t).re = Real.cos (2 * π * t) := by
  rw [e_eq]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

/-- `‖e t − 1‖ ≤ min 2 (2π|t|)`. -/
lemma norm_e_sub_one_le (t : ℝ) : ‖e t - 1‖ ≤ min 2 (2 * π * |t|) := by
  refine le_min ?_ ?_
  · calc ‖e t - 1‖ ≤ ‖e t‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_e]; norm_num
  · have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * π * t)
    have he : e t = Complex.exp (Complex.I * ((2 * π * t : ℝ) : ℂ)) := by rw [e, mul_comm]
    rw [he]
    refine h.trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]

/-- The shifted `P`-difference sum `T = ∑_{n<N} (P(uₙ + c + Δ) − P(uₙ + c))`. -/
def T (u : ℕ → ℝ) (N : ℕ) (c Δ : ℝ) : ℝ := ∑ n ∈ range N, (P (u n + c + Δ) - P (u n + c))

/-- The cosine difference sum at frequency `h`. -/
def D (u : ℕ → ℝ) (N : ℕ) (c Δ : ℝ) (h : ℕ) : ℝ :=
  ∑ n ∈ range N, (Real.cos (2 * π * h * (u n + c + Δ)) - Real.cos (2 * π * h * (u n + c)))

lemma hasSum_T (u : ℕ → ℝ) (N : ℕ) (c Δ : ℝ) :
    HasSum (fun h : ℕ => 1 / (h : ℝ) ^ 2 * D u N c Δ h) (π ^ 2 * T u N c Δ) := by
  have hs : ∀ n ∈ range N, HasSum
      (fun h : ℕ => 1 / (h : ℝ) ^ 2 * Real.cos (2 * π * h * (u n + c + Δ)) -
        1 / (h : ℝ) ^ 2 * Real.cos (2 * π * h * (u n + c)))
      (π ^ 2 * P (u n + c + Δ) - π ^ 2 * P (u n + c)) :=
    fun n _ => (hasSum_cos_P _).sub (hasSum_cos_P _)
  have h := hasSum_sum hs
  convert h using 1
  · funext h
    rw [D, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    ring
  · rw [T, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    ring

/-- `|D_h| ≤ min 2 (2πhΔ) · ‖∑_{n<N} e(h uₙ)‖` for `Δ ≥ 0`. -/
lemma abs_D_le (u : ℕ → ℝ) (N : ℕ) (c Δ : ℝ) (hΔ : 0 ≤ Δ) (h : ℕ) :
    |D u N c Δ h| ≤ min 2 (2 * π * h * Δ) * ‖∑ n ∈ range N, e (h * u n)‖ := by
  have hre : D u N c Δ h =
      ((e (h * (c + Δ)) - e (h * c)) * ∑ n ∈ range N, e (h * u n)).re := by
    rw [mul_sum, Complex.re_sum, D]
    refine sum_congr rfl fun n _ => ?_
    rw [sub_mul, ← e_add, ← e_add, Complex.sub_re, re_e, re_e]
    congr 2 <;> ring
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have : e (h * (c + Δ)) - e (h * c) = e (h * c) * (e (h * Δ) - 1) := by
    rw [mul_sub, ← e_add, mul_one]; congr 2; ring
  rw [this, norm_mul, norm_e, one_mul]
  refine (norm_e_sub_one_le _).trans (le_of_eq ?_)
  rw [abs_of_nonneg (by positivity)]
  ring_nf

/-- The weighted exponential-sum series `W = ∑_h h⁻² min(2, 2πhΔ) ‖S_h‖`. -/
def W (u : ℕ → ℝ) (N : ℕ) (Δ : ℝ) : ℝ :=
  ∑' h : ℕ, 1 / (h : ℝ) ^ 2 * min 2 (2 * π * h * Δ) * ‖∑ n ∈ range N, e (h * u n)‖

lemma W_terms_nonneg (u : ℕ → ℝ) (N : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ) (h : ℕ) :
    0 ≤ 1 / (h : ℝ) ^ 2 * min 2 (2 * π * h * Δ) * ‖∑ n ∈ range N, e (h * u n)‖ := by
  have : 0 ≤ min 2 (2 * π * h * Δ) := le_min (by norm_num) (by positivity)
  positivity

lemma summable_W (u : ℕ → ℝ) (N : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    Summable (fun h : ℕ => 1 / (h : ℝ) ^ 2 * min 2 (2 * π * h * Δ) * ‖∑ n ∈ range N, e (h * u n)‖) := by
  have hs : Summable (fun h : ℕ => 1 / (h : ℝ) ^ 2 * (2 * N)) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_right _
  refine Summable.of_nonneg_of_le (W_terms_nonneg u N Δ hΔ) (fun h => ?_) hs
  have h1 : min 2 (2 * π * h * Δ) ≤ 2 := min_le_left _ _
  have h2 : ‖∑ n ∈ range N, e (h * u n)‖ ≤ N := norm_sum_e_le _ N
  have h0 : 0 ≤ min 2 (2 * π * h * Δ) := le_min (by norm_num) (by positivity)
  calc 1 / (h : ℝ) ^ 2 * min 2 (2 * π * h * Δ) * ‖∑ n ∈ range N, e (h * u n)‖
      ≤ 1 / (h : ℝ) ^ 2 * 2 * N := by gcongr
    _ = 1 / (h : ℝ) ^ 2 * (2 * N) := by ring

lemma abs_T_le (u : ℕ → ℝ) (N : ℕ) (c Δ : ℝ) (hΔ : 0 ≤ Δ) :
    π ^ 2 * |T u N c Δ| ≤ W u N Δ := by
  have hF := hasSum_T u N c Δ
  have hG := (summable_W u N Δ hΔ).hasSum
  have hb : ∀ h : ℕ, |1 / (h : ℝ) ^ 2 * D u N c Δ h| ≤
      1 / (h : ℝ) ^ 2 * min 2 (2 * π * h * Δ) * ‖∑ n ∈ range N, e (h * u n)‖ := fun h => by
    rw [abs_mul, abs_of_nonneg (by positivity), mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_D_le u N c Δ hΔ h) (by positivity)
  have hup := hasSum_le (fun h => (le_abs_self _).trans (hb h)) hF hG
  have hlo := hasSum_le (fun h => (neg_le_abs _).trans (hb h)) hF.neg hG
  rw [← abs_of_pos (by positivity : (0 : ℝ) < π ^ 2), ← abs_mul, abs_le]
  exact ⟨by rw [W]; linarith, hup⟩

/-- **ψ-sums by the weighted exponential-sum series.** For any real sequence `u` and `0 < Δ ≤ 1`,
`|∑_{n<N} ψ(uₙ)| ≤ NΔ/2 + W/(2π²Δ)`, `W = ∑_h h⁻² min(2, 2πhΔ) ‖∑_{n<N} e(h uₙ)‖`. -/
theorem abs_sum_psi_le_W (u : ℕ → ℝ) (N : ℕ) (Δ : ℝ) (h0 : 0 < Δ) (h1 : Δ ≤ 1) :
    |∑ n ∈ range N, ψ (u n)| ≤ N * Δ / 2 + W u N Δ / (2 * π ^ 2 * Δ) := by
  have hT0 := abs_T_le u N 0 Δ h0.le
  have hT1 := abs_T_le u N (-Δ) Δ h0.le
  have hlow : T u N 0 Δ - N * Δ ^ 2 ≤ 2 * Δ * ∑ n ∈ range N, ψ (u n) := by
    rw [T, mul_sum]
    have : ∑ n ∈ range N, (P (u n + 0 + Δ) - P (u n + 0)) - N * Δ ^ 2 =
        ∑ n ∈ range N, (P (u n + 0 + Δ) - P (u n + 0) - Δ ^ 2) := by
      rw [sum_sub_distrib]; simp
    rw [this]
    refine sum_le_sum fun n _ => ?_
    have := P_add_sub_le (u n) Δ h0.le h1
    simp only [add_zero]
    linarith
  have hupp : 2 * Δ * ∑ n ∈ range N, ψ (u n) ≤ T u N (-Δ) Δ + N * Δ ^ 2 := by
    rw [T, mul_sum]
    have : ∑ n ∈ range N, (P (u n + -Δ + Δ) - P (u n + -Δ)) + N * Δ ^ 2 =
        ∑ n ∈ range N, (P (u n + -Δ + Δ) - P (u n + -Δ) + Δ ^ 2) := by
      rw [sum_add_distrib]; simp
    rw [this]
    refine sum_le_sum fun n _ => ?_
    have := le_P_sub_sub (u n) Δ h0.le h1
    have e1 : u n + -Δ + Δ = u n := by ring
    have e2 : u n + -Δ = u n - Δ := by ring
    rw [e1, e2]
    linarith
  have hpi : 0 < π ^ 2 := by positivity
  have hW0 : |T u N 0 Δ| ≤ W u N Δ / π ^ 2 := by rw [le_div_iff₀ hpi]; linarith
  have hW1 : |T u N (-Δ) Δ| ≤ W u N Δ / π ^ 2 := by rw [le_div_iff₀ hpi]; linarith
  have key : (N * Δ / 2 + W u N Δ / (2 * π ^ 2 * Δ)) * (2 * Δ) = N * Δ ^ 2 + W u N Δ / π ^ 2 := by
    field_simp
  have a0 := abs_le.mp hW0
  have a1 := abs_le.mp hW1
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/- ### The `h`-series -/

/-- `1/√(k+1) ≤ 2√(k+1) − 2√k`. -/
lemma inv_sqrt_succ_le (k : ℝ) (hk : 0 ≤ k) : 1 / √(k + 1) ≤ 2 * √(k + 1) - 2 * √k := by
  have ha := Real.sqrt_nonneg k
  have hb : 0 < √(k + 1) := Real.sqrt_pos.mpr (by linarith)
  have ha2 := Real.sq_sqrt hk
  have hb2 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ k + 1)
  rw [div_le_iff₀ hb]
  nlinarith [sq_nonneg (√(k + 1) - √k)]

/-- `1/((k+1)√(k+1)) ≤ 2/√k − 2/√(k+1)` for `k ≥ 1`. -/
lemma inv_pow_three_halves_le (k : ℝ) (hk : 1 ≤ k) :
    1 / ((k + 1) * √(k + 1)) ≤ 2 / √k - 2 / √(k + 1) := by
  have ha : 0 < √k := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < √(k + 1) := Real.sqrt_pos.mpr (by linarith)
  have ha2 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ k)
  have hb2 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ k + 1)
  have hab : √k ≤ √(k + 1) := Real.sqrt_le_sqrt (by linarith)
  set a := √k
  set b := √(k + 1)
  have hk1 : k + 1 = b ^ 2 := hb2.symm
  rw [hk1]
  rw [div_sub_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  -- `(2b − 2a) b³ − a b ≥ 0`, i.e. `b (b − a)² (2b + a) ≥ 0` using `b² − a² = 1`
  have h1 : b ^ 2 - a ^ 2 = 1 := by rw [ha2, hb2]; ring
  have h2 : 0 ≤ b * ((b - a) ^ 2 * (2 * b + a)) := by positivity
  nlinarith [h1, h2]

/-- Head sum: `∑_{i<K, i+1 ≤ H} 1/√(i+1) ≤ 2√(min K H)`. -/
lemma sum_head_le (H K : ℕ) :
    ∑ i ∈ range K, (if i + 1 ≤ H then 1 / √((i : ℝ) + 1) else 0) ≤ 2 * √(min K H : ℕ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ]
    split_ifs with h
    · have hm : min (K + 1) H = K + 1 := min_eq_left h
      have hm' : min K H = K := min_eq_left (by omega)
      rw [hm] at *
      rw [hm'] at ih
      have := inv_sqrt_succ_le (K : ℝ) (by positivity)
      push_cast
      linarith
    · have hle : ((min K H : ℕ) : ℝ) ≤ (min (K + 1) H : ℕ) := by exact_mod_cast min_le_min_right H (Nat.le_succ K)
      have := Real.sqrt_le_sqrt hle
      linarith

/-- Tail sum: `∑_{i<K, i+1 > H} 1/((i+1)√(i+1)) ≤ 2/√H − 2/√(max K H)` for `H ≥ 1`. -/
lemma sum_tail_le (H K : ℕ) (hH : 1 ≤ H) :
    ∑ i ∈ range K, (if H < i + 1 then 1 / (((i : ℝ) + 1) * √((i : ℝ) + 1)) else 0) ≤
      2 / √(H : ℝ) - 2 / √(max K H : ℕ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ]
    split_ifs with h
    · have hKH : H ≤ K := by omega
      have hm : max (K + 1) H = K + 1 := max_eq_left (by omega)
      have hm' : max K H = K := max_eq_left hKH
      rw [hm'] at ih
      rw [hm]
      have hK : (1 : ℝ) ≤ K := by exact_mod_cast (le_trans hH hKH)
      have := inv_pow_three_halves_le (K : ℝ) hK
      push_cast
      linarith
    · have hm : max (K + 1) H = H := max_eq_right (by omega)
      have hm' : max K H = H := max_eq_right (by omega)
      rw [hm'] at ih
      rw [hm]
      linarith

/-- `∑_{i<K} 1/((i+1)√(i+1)) ≤ 3`. -/
lemma sum_three_halves_le (K : ℕ) :
    ∑ i ∈ range K, 1 / (((i : ℝ) + 1) * √((i : ℝ) + 1)) ≤ 3 := by
  have h := sum_tail_le 1 K le_rfl
  have hsplit : ∀ i ∈ range K, 1 / (((i : ℝ) + 1) * √((i : ℝ) + 1)) ≤
      (if 1 < i + 1 then 1 / (((i : ℝ) + 1) * √((i : ℝ) + 1)) else 0) + (if i = 0 then 1 else 0) := by
    intro i _
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; simp
    · simp [show 1 < i + 1 by omega, show i ≠ 0 by omega]
  refine (sum_le_sum hsplit).trans ?_
  rw [sum_add_distrib]
  have h3 : ∑ i ∈ range K, (if i = 0 then (1 : ℝ) else 0) ≤ 1 := by
    rw [sum_ite_eq']; split_ifs <;> norm_num
  have h4 : 0 ≤ 2 / √((max K 1 : ℕ) : ℝ) := by positivity
  simp only [Nat.cast_one, Real.sqrt_one, div_one] at h
  linarith

/-- **The `h`-series bound.** If `‖S_h‖ ≤ A√h + B/√h` for every `h ≥ 1` (`A, B ≥ 0`), then for `Δ ≥ 0` and
`H ≥ 1`, `∑_h h⁻² min(2, 2πhΔ) ‖S_h‖ ≤ 4πΔA√H + 4A/√H + 6πΔB`. -/
theorem tsum_le_of_bound (S : ℕ → ℝ) (A B Δ : ℝ) (H : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hΔ : 0 ≤ Δ)
    (hH : 1 ≤ H) (hS0 : ∀ h, 0 ≤ S h) (hS : ∀ h : ℕ, 1 ≤ h → S h ≤ A * √(h : ℝ) + B / √(h : ℝ)) :
    ∑' h : ℕ, 1 / (h : ℝ) ^ 2 * min 2 (2 * π * h * Δ) * S h ≤
      4 * π * Δ * A * √(H : ℝ) + 4 * A / √(H : ℝ) + 6 * π * Δ * B := by
  have hnn : ∀ h : ℕ, 0 ≤ 1 / (h : ℝ) ^ 2 * min 2 (2 * π * h * Δ) * S h := fun h => by
    have : 0 ≤ min 2 (2 * π * h * Δ) := le_min (by norm_num) (by positivity)
    have := hS0 h
    positivity
  refine Real.tsum_le_of_sum_range_le hnn fun K => ?_
  -- per-term bound at `h = i + 1`
  have hterm : ∀ i ∈ range K, 1 / ((i + 1 : ℕ) : ℝ) ^ 2 * min 2 (2 * π * (i + 1 : ℕ) * Δ) * S (i + 1) ≤
      2 * π * Δ * A * (if i + 1 ≤ H then 1 / √((i : ℝ) + 1) else 0) +
      2 * A * (if H < i + 1 then 1 / (((i : ℝ) + 1) * √((i : ℝ) + 1)) else 0) +
      2 * π * Δ * B * (1 / (((i : ℝ) + 1) * √((i : ℝ) + 1))) := by
    intro i _
    push_cast
    set k : ℝ := (i : ℝ) + 1 with hk
    have hk1 : 1 ≤ k := by rw [hk]; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    have hs : 0 < √k := Real.sqrt_pos.mpr (by linarith)
    have hs2 : √k ^ 2 = k := Real.sq_sqrt (by linarith)
    have hSk : S (i + 1) ≤ A * √k + B / √k := by
      have := hS (i + 1) (by omega); push_cast at this; exact this
    set m := min 2 (2 * π * k * Δ) with hm
    have hm0 : 0 ≤ m := le_min (by norm_num) (by positivity)
    have hmA : 1 / k ^ 2 * m * S (i + 1) ≤ m * (A / (k * √k)) + m * (B / (k ^ 2 * √k)) := by
      have e1 : 1 / k ^ 2 * m * (A * √k + B / √k) = m * (A / (k * √k)) + m * (B / (k ^ 2 * √k)) := by
        field_simp
        rw [hs2]
        ring
      rw [← e1]
      exact mul_le_mul_of_nonneg_left hSk (by positivity)
    refine hmA.trans ?_
    have hB' : m * (B / (k ^ 2 * √k)) ≤ 2 * π * Δ * B * (1 / (k * √k)) := by
      have : m * (B / (k ^ 2 * √k)) ≤ 2 * π * k * Δ * (B / (k ^ 2 * √k)) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      refine this.trans (le_of_eq ?_)
      field_simp
    split_ifs with h1 h2 h2
    · omega
    · have hA' : m * (A / (k * √k)) ≤ 2 * π * Δ * A * (1 / √k) := by
        have : m * (A / (k * √k)) ≤ 2 * π * k * Δ * (A / (k * √k)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        refine this.trans (le_of_eq ?_)
        field_simp
      linarith
    · have hA' : m * (A / (k * √k)) ≤ 2 * A * (1 / (k * √k)) := by
        have : m * (A / (k * √k)) ≤ 2 * (A / (k * √k)) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        refine this.trans (le_of_eq ?_)
        ring
      linarith
    · omega
  calc ∑ i ∈ range K, 1 / (i : ℝ) ^ 2 * min 2 (2 * π * i * Δ) * S i
      ≤ ∑ i ∈ range (K + 1), 1 / (i : ℝ) ^ 2 * min 2 (2 * π * i * Δ) * S i := by
        rw [sum_range_succ]; linarith [hnn K]
    _ = ∑ i ∈ range K, 1 / ((i + 1 : ℕ) : ℝ) ^ 2 * min 2 (2 * π * (i + 1 : ℕ) * Δ) * S (i + 1) := by
        rw [sum_range_succ']; simp
    _ ≤ ∑ i ∈ range K, (2 * π * Δ * A * (if i + 1 ≤ H then 1 / √((i : ℝ) + 1) else 0) +
          2 * A * (if H < i + 1 then 1 / (((i : ℝ) + 1) * √((i : ℝ) + 1)) else 0) +
          2 * π * Δ * B * (1 / (((i : ℝ) + 1) * √((i : ℝ) + 1)))) := sum_le_sum hterm
    _ = 2 * π * Δ * A * ∑ i ∈ range K, (if i + 1 ≤ H then 1 / √((i : ℝ) + 1) else 0) +
          2 * A * ∑ i ∈ range K, (if H < i + 1 then 1 / (((i : ℝ) + 1) * √((i : ℝ) + 1)) else 0) +
          2 * π * Δ * B * ∑ i ∈ range K, (1 / (((i : ℝ) + 1) * √((i : ℝ) + 1))) := by
        rw [sum_add_distrib, sum_add_distrib, mul_sum, mul_sum, mul_sum]
    _ ≤ 2 * π * Δ * A * (2 * √(H : ℝ)) + 2 * A * (2 / √(H : ℝ)) + 2 * π * Δ * B * 3 := by
        have h1 := sum_head_le H K
        have h1' : √((min K H : ℕ) : ℝ) ≤ √(H : ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast min_le_right K H)
        have h2 := sum_tail_le H K hH
        have h2' : 0 ≤ 2 / √((max K H : ℕ) : ℝ) := by positivity
        have h3 := sum_three_halves_le K
        have c1 : 0 ≤ 2 * π * Δ * A := by positivity
        have c3 : 0 ≤ 2 * π * Δ * B := by positivity
        gcongr ?_ + ?_ + ?_
        · exact mul_le_mul_of_nonneg_left (h1.trans (by linarith)) c1
        · exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        · exact mul_le_mul_of_nonneg_left h3 c3
    _ = 4 * π * Δ * A * √(H : ℝ) + 4 * A / √(H : ℝ) + 6 * π * Δ * B := by ring

/- ### Van der Corput on each frequency, and the choice of `Δ` -/

/-- `‖∑_{n<N} e(h f(m+n))‖ ≤ 4αN√λ · √h + (7/√λ)/√h` (`van_der_corput_second` applied to `h f`). -/
lemma norm_S_le (f f' f'' : ℝ → ℝ) (m : ℤ) (N : ℕ) (lam alpha : ℝ) (hlam : 0 < lam)
    (hf : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f' (f'' t) t)
    (hlo : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), lam ≤ f'' t)
    (hhi : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), f'' t ≤ alpha * lam) (h : ℕ) (hh : 1 ≤ h) :
    ‖∑ n ∈ range N, e (h * f (m + n))‖ ≤ 4 * alpha * N * √lam * √(h : ℝ) + 7 / √lam / √(h : ℝ) := by
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hv := van_der_corput_second (fun t => h * f t) (fun t => h * f' t) (fun t => h * f'' t) m N
    (h * lam) alpha (by positivity)
    (fun t ht => (hf t ht).const_mul _) (fun t ht => (hf' t ht).const_mul _)
    (fun t ht => mul_le_mul_of_nonneg_left (hlo t ht) hhr.le)
    (fun t ht => by
      have := mul_le_mul_of_nonneg_left (hhi t ht) hhr.le
      calc (h : ℝ) * f'' t ≤ h * (alpha * lam) := this
        _ = alpha * (h * lam) := by ring)
  rw [Real.sqrt_mul hhr.le] at hv
  refine hv.trans (le_of_eq ?_)
  rw [div_div]
  ring

/-- The final real-number step: with `t² ∈ [1/(2Δ), 1/Δ]`,
`(4πΔAt + 4A/t + 6πΔB)/(2π²Δ) ≤ A/√Δ + B`. -/
lemma final_alg (A B Δ t : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hΔ : 0 < Δ) (ht : 0 < t)
    (ht1 : t ^ 2 ≤ 1 / Δ) (ht2 : 1 / (2 * Δ) ≤ t ^ 2) :
    (4 * π * Δ * A * t + 4 * A / t + 6 * π * Δ * B) / (2 * π ^ 2 * Δ) ≤ A / √Δ + B := by
  have hpi := Real.pi_gt_three
  have hs : 0 < √Δ := Real.sqrt_pos.mpr hΔ
  have hs2 : √Δ ^ 2 = Δ := Real.sq_sqrt hΔ.le
  set s := √Δ
  set p := t * s with hp
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 := by
    have : p ^ 2 ≤ 1 := by
      rw [hp, mul_pow, hs2]
      rw [le_div_iff₀ hΔ] at ht1
      linarith
    nlinarith
  have hp2 : 1 / 2 ≤ p := by
    have : 1 / 2 ≤ p ^ 2 := by
      rw [hp, mul_pow, hs2]
      rw [div_le_iff₀ (by positivity)] at ht2
      linarith
    nlinarith
  have e1 : (4 * π * Δ * A * t + 4 * A / t + 6 * π * Δ * B) / (2 * π ^ 2 * Δ) =
      A / s * (2 * p / π + 2 / (π ^ 2 * p)) + 3 * B / π := by
    rw [hp, ← hs2]
    field_simp
    ring
  have k1 : 2 * p / π + 2 / (π ^ 2 * p) ≤ 1 := by
    have a1 : 2 * p / π ≤ 2 * p / 3 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hpi.le
    have a2 : 2 / (π ^ 2 * p) ≤ 2 / (9 * p) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (by have h9 : (9 : ℝ) < π ^ 2 := by nlinarith
            nlinarith)
    have a3 : 2 * p / 3 + 2 / (9 * p) ≤ 1 := by
      rw [div_add_div _ _ (by norm_num) (by positivity), div_le_one (by positivity)]
      nlinarith
    linarith
  have k2 : 3 * B / π ≤ B := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  rw [e1]
  have : A / s * (2 * p / π + 2 / (π ^ 2 * p)) ≤ A / s * 1 :=
    mul_le_mul_of_nonneg_left k1 (by positivity)
  linarith

/-- **ψ-sum second-derivative bound with a free cut-off.** If `f' = f′`, `f'' = f′′` on `[m, m + N − 1]` and
`λ ≤ f'' ≤ αλ` there (`λ > 0`), then for every `0 < Δ ≤ 1/2`,
`|∑_{n<N} ψ(f(m + n))| ≤ NΔ/2 + 4αN√(λ/Δ) + 7/√λ`. -/
theorem abs_sum_psi_le_delta (f f' f'' : ℝ → ℝ) (m : ℤ) (N : ℕ) (lam alpha : ℝ) (hlam : 0 < lam)
    (hf : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f' (f'' t) t)
    (hlo : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), lam ≤ f'' t)
    (hhi : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), f'' t ≤ alpha * lam)
    (Δ : ℝ) (h0 : 0 < Δ) (h1 : Δ ≤ 1 / 2) :
    |∑ n ∈ range N, ψ (f (m + n))| ≤ N * Δ / 2 + 4 * alpha * N * √(lam / Δ) + 7 / √lam := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0; simp; positivity
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmI : (m : ℝ) ∈ Set.Icc (m : ℝ) (m + N - 1) := ⟨le_rfl, by linarith⟩
  have halpha : 1 ≤ alpha := by
    have := (hlo m hmI).trans (hhi m hmI)
    nlinarith
  set u : ℕ → ℝ := fun n => f (m + n) with hu
  have hψ := abs_sum_psi_le_W u N Δ h0 (by linarith)
  set H : ℕ := ⌊1 / Δ⌋₊ with hHdef
  have hinv : 2 ≤ 1 / Δ := by rw [le_div_iff₀ h0]; linarith
  have hH1 : 1 ≤ H := Nat.le_floor (by push_cast; linarith)
  have hHle : (H : ℝ) ≤ 1 / Δ := Nat.floor_le (by positivity)
  have hHge : 1 / (2 * Δ) ≤ (H : ℝ) := by
    have := Nat.lt_floor_add_one (1 / Δ)
    have e : 1 / (2 * Δ) = (1 / Δ) / 2 := by field_simp
    rw [e]; linarith
  set A : ℝ := 4 * alpha * N * √lam
  set B : ℝ := 7 / √lam
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  have hW : W u N Δ ≤ 4 * π * Δ * A * √(H : ℝ) + 4 * A / √(H : ℝ) + 6 * π * Δ * B :=
    tsum_le_of_bound (fun h => ‖∑ n ∈ range N, e (h * u n)‖) A B Δ H hA hB h0.le hH1
      (fun _ => norm_nonneg _) (fun h hh => norm_S_le f f' f'' m N lam alpha hlam hf hf' hlo hhi h hh)
  have ht : 0 < √(H : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hH1)
  have ht2 : √(H : ℝ) ^ 2 = H := Real.sq_sqrt (by positivity)
  have hfin := final_alg A B Δ (√(H : ℝ)) hA hB h0 ht (by rw [ht2]; exact hHle) (by rw [ht2]; exact hHge)
  have hdiv : W u N Δ / (2 * π ^ 2 * Δ) ≤
      (4 * π * Δ * A * √(H : ℝ) + 4 * A / √(H : ℝ) + 6 * π * Δ * B) / (2 * π ^ 2 * Δ) :=
    div_le_div_of_nonneg_right hW (by positivity)
  have hsq : 4 * alpha * N * √(lam / Δ) = A / √Δ := by
    rw [Real.sqrt_div hlam.le]; ring
  rw [hsq]
  linarith

/-- **The ψ-sum second-derivative bound** (van der Corput; explicit constants). If `f' = f′`, `f'' = f′′` on
`[m, m + N − 1]` and `λ ≤ f'' ≤ αλ` there (`λ > 0`), then
`|∑_{n<N} ψ(f(m + n))| ≤ (1/2 + 4α) N λ^{1/3} + 7/√λ`. -/
theorem abs_sum_psi_le (f f' f'' : ℝ → ℝ) (m : ℤ) (N : ℕ) (lam alpha : ℝ) (hlam : 0 < lam)
    (hf : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f' (f'' t) t)
    (hlo : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), lam ≤ f'' t)
    (hhi : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), f'' t ≤ alpha * lam) :
    |∑ n ∈ range N, ψ (f (m + n))| ≤ (1 / 2 + 4 * alpha) * N * lam ^ (1 / 3 : ℝ) + 7 / √lam := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0; simp; positivity
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmI : (m : ℝ) ∈ Set.Icc (m : ℝ) (m + N - 1) := ⟨le_rfl, by linarith⟩
  have halpha : 1 ≤ alpha := by
    have := (hlo m hmI).trans (hhi m hmI)
    nlinarith
  set c := lam ^ (1 / 3 : ℝ) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hlam _
  have hc3 : c ^ 3 = lam := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hlam.le]; norm_num
  have h7 : 0 ≤ 7 / √lam := by positivity
  rcases le_or_gt lam (1 / 8) with hl | hl
  · have hc1 : c ≤ 1 / 2 := by nlinarith [sq_nonneg c, sq_nonneg (c - 1 / 2)]
    have h := abs_sum_psi_le_delta f f' f'' m N lam alpha hlam hf hf' hlo hhi c hc0 hc1
    have hsq : √(lam / c) = c := by
      rw [← hc3, show c ^ 3 / c = c ^ 2 by field_simp, Real.sqrt_sq hc0.le]
    rw [hsq] at h
    linarith
  · have hc1 : 1 / 2 < c := by nlinarith [sq_nonneg c, sq_nonneg (c - 1 / 2)]
    have hab : |∑ n ∈ range N, ψ (f (m + n))| ≤ N * (1 / 2) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have := sum_le_sum (s := range N) (fun n _ => PowerfulFC.BG1.abs_psi_le (f (m + n)))
      simpa using this
    have hk : 1 / 2 ≤ (1 / 2 + 4 * alpha) * c := by nlinarith
    have : (N : ℝ) * (1 / 2) ≤ (1 / 2 + 4 * alpha) * N * c := by
      have := mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ N)
      linarith
    linarith

end PowerfulFC.BG2
end
end

-- ===== PowerfulFC.Dyadic =====
section
/-
# Bateman–Grosswald rung BG3: dyadic bounds for the two ψ-sums

BG1 (`PowerfulFC.BG1.abs_S_sub_main_le_two`) leaves two ψ-sums, with `Z = ⌊y^{1/5}⌋`:

* `Ψ₁(y) = ∑_{b ∈ [1, Z]} ψ(√(y/b³))`,
* `Ψ₂(y) = ∑_{a ∈ [1, Z]} ψ((y/a²)^{1/3})`.

Here we prove, unconditionally, `|Ψ₁(y)| ≤ C₁ y^{1/7}` (`abs_Psi1_le`) and `|Ψ₂(y)| ≤ C₂ y^{2/15}`
(`abs_Psi2_le`) for `y ≥ 1`.

Method. Both summands are `ψ(A t^{-γ})` (`A = √y, γ = 3/2` and `A = y^{1/3}, γ = 2/3`), a convex function of
`t`. Split `[L, Z]` into the doubling blocks `[L 2^k, L 2^{k+1}) ∩ [L, Z]` (`sum_blocks`); on a block starting at
`M`, `f''` lies in `[λ, 2^{γ+2} λ]` with `λ = f''(2M)`, and BG2's van der Corput bound
`PowerfulFC.BG2.abs_sum_psi_le` gives `≤ C₁ A^{1/3} M^{(1-γ)/3} + C₂ A^{-1/2} M^{(γ+2)/2}` (`block_bound`). The block
bounds are geometric in `k` (`geom_neg`, `geom_pos`). For `Ψ₁` the first exponent `-1/6` is negative, so the blocks
start at `L = ⌊y^{1/7}⌋ + 1` and the first `⌊y^{1/7}⌋` terms are bounded trivially by `1/2` each.
-/

open Finset Real

namespace PowerfulFC.BG3

open PowerfulFC.BG1 (ψ)
/-- Telescoping a sum over `[a 0, a K)` into the blocks `[a k, a (k+1))`. -/
lemma sum_blocks (g : ℕ → ℝ) (a : ℕ → ℕ) (ha : Monotone a) (K : ℕ) :
    ∑ k ∈ range K, ∑ n ∈ Ico (a k) (a (k + 1)), g n = ∑ n ∈ Ico (a 0) (a K), g n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih, Finset.sum_Ico_consecutive _ (ha (Nat.zero_le K)) (ha (Nat.le_succ K))]

lemma abs_sum_psi_le_card {ι : Type*} (s : Finset ι) (h : ι → ℝ) :
    |∑ n ∈ s, ψ (h n)| ≤ s.card / 2 := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have := sum_le_sum (s := s) (fun n _ => PowerfulFC.BG1.abs_psi_le (h n))
  simpa [div_eq_mul_inv] using this

lemma mul_two_pow_rpow (L : ℕ) (u : ℝ) (k : ℕ) :
    ((L : ℝ) * 2 ^ k) ^ u = (L : ℝ) ^ u * ((2 : ℝ) ^ u) ^ k := by
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm (k : ℝ) u, mul_comm]

/-- Geometric sum, decreasing ratio. -/
lemma geom_neg (L : ℕ) (u : ℝ) (hu : u < 0) (K : ℕ) :
    ∑ k ∈ range K, ((L : ℝ) * 2 ^ k) ^ u ≤ (L : ℝ) ^ u / (1 - (2 : ℝ) ^ u) := by
  simp_rw [mul_two_pow_rpow, ← mul_sum]
  have hr0 : 0 < (2 : ℝ) ^ u := by positivity
  have hr1 : (2 : ℝ) ^ u < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hu
  rw [geom_sum_eq hr1.ne]
  have h1r : 0 < 1 - (2 : ℝ) ^ u := by linarith
  have hK : 0 ≤ ((2 : ℝ) ^ u) ^ K := by positivity
  have heq : (((2 : ℝ) ^ u) ^ K - 1) / ((2 : ℝ) ^ u - 1) = (1 - ((2 : ℝ) ^ u) ^ K) / (1 - (2 : ℝ) ^ u) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  calc (L : ℝ) ^ u * ((((2 : ℝ) ^ u) ^ K - 1) / ((2 : ℝ) ^ u - 1))
      = (L : ℝ) ^ u * ((1 - ((2 : ℝ) ^ u) ^ K) / (1 - (2 : ℝ) ^ u)) := by rw [heq]
    _ ≤ (L : ℝ) ^ u * (1 / (1 - (2 : ℝ) ^ u)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) h1r.le) (by positivity)
    _ = _ := by ring

/-- Geometric sum, increasing ratio: bounded by a constant times the top term. -/
lemma geom_pos (L : ℕ) (u : ℝ) (hu : 0 < u) (K : ℕ) :
    ∑ k ∈ range (K + 1), ((L : ℝ) * 2 ^ k) ^ u
      ≤ (2 : ℝ) ^ u / ((2 : ℝ) ^ u - 1) * ((L : ℝ) * 2 ^ K) ^ u := by
  simp_rw [mul_two_pow_rpow, ← mul_sum]
  have hr1 : 1 < (2 : ℝ) ^ u := Real.one_lt_rpow (by norm_num) hu
  rw [geom_sum_eq hr1.ne']
  have hL : 0 ≤ (L : ℝ) ^ u := by positivity
  have hK : 0 ≤ ((2 : ℝ) ^ u) ^ K := by positivity
  have hd : 0 < (2 : ℝ) ^ u - 1 := by linarith
  rw [pow_succ]
  have : (((2 : ℝ) ^ u) ^ K * (2 : ℝ) ^ u - 1) / ((2 : ℝ) ^ u - 1)
      ≤ (2 : ℝ) ^ u / ((2 : ℝ) ^ u - 1) * ((2 : ℝ) ^ u) ^ K := by
    rw [div_mul_eq_mul_div, mul_comm ((2 : ℝ) ^ u)]
    exact div_le_div_of_nonneg_right (by linarith) hd.le
  calc (L : ℝ) ^ u * ((((2 : ℝ) ^ u) ^ K * (2 : ℝ) ^ u - 1) / ((2 : ℝ) ^ u - 1))
      ≤ (L : ℝ) ^ u * ((2 : ℝ) ^ u / ((2 : ℝ) ^ u - 1) * ((2 : ℝ) ^ u) ^ K) :=
        mul_le_mul_of_nonneg_left this hL
    _ = _ := by ring

/-- `L 2^{⌊log₂(Z/L)⌋} ≤ Z < L 2^{⌊log₂(Z/L)⌋+1}`. -/
lemma log_facts (L Z : ℕ) (hL : 1 ≤ L) (hLZ : L ≤ Z) :
    L * 2 ^ Nat.log 2 (Z / L) ≤ Z ∧ Z < L * 2 ^ (Nat.log 2 (Z / L) + 1) := by
  have hq : Z / L ≠ 0 := (Nat.div_pos hLZ hL).ne'
  constructor
  · exact (Nat.mul_le_mul_left L (Nat.pow_log_le_self 2 hq)).trans (Nat.mul_div_le Z L)
  · calc Z < L * (Z / L + 1) := Nat.lt_mul_div_succ Z hL
      _ ≤ L * 2 ^ (Nat.log 2 (Z / L) + 1) :=
        Nat.mul_le_mul_left L (Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) _))

/-- **Block lemma.** For `M ≥ 1`, `N ≤ M`: `|∑_{i<N} ψ(A (M+i)^{-γ})| ≤ C₁ A^{1/3} M^{(1-γ)/3} + C₂ A^{-1/2}
M^{(γ+2)/2}`, constants depending on `γ` only. From `PowerfulFC.BG2.abs_sum_psi_le` with `λ = f''(2M)`,
`α = 2^{γ+2}`. -/
theorem block_bound (γ : ℝ) (hγ : 0 < γ) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ A : ℝ, 0 < A → ∀ M N : ℕ, 1 ≤ M → N ≤ M →
      |∑ i ∈ range N, ψ (A * ((M : ℝ) + i) ^ (-γ))|
        ≤ C1 * A ^ (1 / 3 : ℝ) * (M : ℝ) ^ ((1 - γ) / 3) + C2 * A ^ (-1 / 2 : ℝ) * (M : ℝ) ^ ((γ + 2) / 2) := by
  set g := γ * (γ + 1) with hg
  have hg0 : 0 < g := by positivity
  refine ⟨(1 / 2 + 4 * 2 ^ (γ + 2)) * g ^ (1 / 3 : ℝ) * (2 : ℝ) ^ ((-γ - 2) * (1 / 3)),
    7 * g ^ (-1 / 2 : ℝ) * (2 : ℝ) ^ ((-γ - 2) * (-1 / 2)), by positivity, by positivity, ?_⟩
  intro A hA M N hM hN
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNM : (N : ℝ) ≤ M := by exact_mod_cast hN
  set c := A * g with hc
  have hc0 : 0 < c := by positivity
  set lam := c * (2 * (M : ℝ)) ^ (-γ - 2) with hlam_def
  have hlam : 0 < lam := by positivity
  have h2pos : (0 : ℝ) < 2 ^ (γ + 2) := by positivity
  -- the interval
  have hI : ∀ t ∈ Set.Icc ((M : ℤ) : ℝ) ((M : ℤ) + N - 1), 0 < t ∧ (M : ℝ) ≤ t ∧ t ≤ 2 * M := by
    intro t ht
    simp only [Int.cast_natCast] at ht
    exact ⟨by linarith [ht.1], ht.1, by linarith [ht.2]⟩
  have hf'' : ∀ t : ℝ, A * (-γ * ((-γ - 1) * t ^ (-γ - 1 - 1))) = c * t ^ (-γ - 2) := by
    intro t
    rw [show -γ - 1 - 1 = -γ - 2 by ring, hc, hg]; ring
  have key := PowerfulFC.BG2.abs_sum_psi_le (fun t => A * t ^ (-γ)) (fun t => A * (-γ * t ^ (-γ - 1)))
    (fun t => A * (-γ * ((-γ - 1) * t ^ (-γ - 1 - 1)))) (M : ℤ) N lam (2 ^ (γ + 2)) hlam
    (fun t ht => ((Real.hasDerivAt_rpow_const (Or.inl (hI t ht).1.ne')).const_mul A))
    (fun t ht => (((Real.hasDerivAt_rpow_const (Or.inl (hI t ht).1.ne')).const_mul (-γ)).const_mul A))
    (by
      intro t ht
      obtain ⟨h0, -, h2⟩ := hI t ht
      simp only [hf'']
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos h0 h2 (by linarith)) hc0.le)
    (by
      intro t ht
      obtain ⟨h0, h1, -⟩ := hI t ht
      simp only [hf'']
      have hsplit : (2 * (M : ℝ)) ^ (-γ - 2) = (2 : ℝ) ^ (-γ - 2) * (M : ℝ) ^ (-γ - 2) :=
        Real.mul_rpow (by norm_num) hM0.le
      have h22 : (2 : ℝ) ^ (γ + 2) * (2 : ℝ) ^ (-γ - 2) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; norm_num
      have : t ^ (-γ - 2) ≤ (M : ℝ) ^ (-γ - 2) := Real.rpow_le_rpow_of_nonpos hM0 h1 (by linarith)
      rw [hlam_def, hsplit]
      calc c * t ^ (-γ - 2) ≤ c * (M : ℝ) ^ (-γ - 2) := mul_le_mul_of_nonneg_left this hc0.le
        _ = 2 ^ (γ + 2) * (c * ((2 : ℝ) ^ (-γ - 2) * (M : ℝ) ^ (-γ - 2))) := by
          rw [← mul_assoc, ← mul_assoc, mul_comm _ c, mul_assoc c, h22]; ring)
  simp only [Int.cast_natCast] at key
  -- powers of λ
  have hpow : ∀ e : ℝ, lam ^ e
      = A ^ e * g ^ e * (2 : ℝ) ^ ((-γ - 2) * e) * (M : ℝ) ^ ((-γ - 2) * e) := by
    intro e
    have h2M : (2 * (M : ℝ)) ^ (-γ - 2) = (2 : ℝ) ^ (-γ - 2) * (M : ℝ) ^ (-γ - 2) :=
      Real.mul_rpow (by norm_num) hM0.le
    rw [hlam_def, h2M, Real.mul_rpow hc0.le (by positivity),
      Real.mul_rpow (x := (2 : ℝ) ^ (-γ - 2)) (y := (M : ℝ) ^ (-γ - 2)) (by positivity) (by positivity),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul hM0.le, hc, Real.mul_rpow hA.le hg0.le]
    ring
  have hsqrt : 7 / √lam = 7 * lam ^ (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hlam.le, div_eq_mul_inv]
  have hM13 : (M : ℝ) ^ ((1 - γ) / 3) = M * (M : ℝ) ^ ((-γ - 2) * (1 / 3)) := by
    rw [show (1 - γ) / 3 = 1 + (-γ - 2) * (1 / 3) by ring, Real.rpow_add hM0, Real.rpow_one]
  have hM12 : (M : ℝ) ^ ((γ + 2) / 2) = (M : ℝ) ^ ((-γ - 2) * (-1 / 2)) := by
    congr 1; ring
  rw [hsqrt, hpow, hpow] at key
  refine key.trans ?_
  rw [hM13, hM12]
  have hl3 : 0 ≤ A ^ (1 / 3 : ℝ) * g ^ (1 / 3 : ℝ) * (2 : ℝ) ^ ((-γ - 2) * (1 / 3))
      * (M : ℝ) ^ ((-γ - 2) * (1 / 3)) := by positivity
  have h1 : (1 / 2 + 4 * 2 ^ (γ + 2)) * N * (A ^ (1 / 3 : ℝ) * g ^ (1 / 3 : ℝ) * (2 : ℝ) ^ ((-γ - 2) * (1 / 3))
      * (M : ℝ) ^ ((-γ - 2) * (1 / 3)))
      ≤ (1 / 2 + 4 * 2 ^ (γ + 2)) * M * (A ^ (1 / 3 : ℝ) * g ^ (1 / 3 : ℝ) * (2 : ℝ) ^ ((-γ - 2) * (1 / 3))
      * (M : ℝ) ^ ((-γ - 2) * (1 / 3))) := by
    gcongr
  have h2 : (1 / 2 + 4 * 2 ^ (γ + 2)) * M * (A ^ (1 / 3 : ℝ) * g ^ (1 / 3 : ℝ) * (2 : ℝ) ^ ((-γ - 2) * (1 / 3))
      * (M : ℝ) ^ ((-γ - 2) * (1 / 3)))
      + 7 * (A ^ (-1 / 2 : ℝ) * g ^ (-1 / 2 : ℝ) * (2 : ℝ) ^ ((-γ - 2) * (-1 / 2))
      * (M : ℝ) ^ ((-γ - 2) * (-1 / 2)))
      = (1 / 2 + 4 * 2 ^ (γ + 2)) * g ^ (1 / 3 : ℝ) * (2 : ℝ) ^ ((-γ - 2) * (1 / 3)) * A ^ (1 / 3 : ℝ)
          * (M * (M : ℝ) ^ ((-γ - 2) * (1 / 3)))
        + 7 * g ^ (-1 / 2 : ℝ) * (2 : ℝ) ^ ((-γ - 2) * (-1 / 2)) * A ^ (-1 / 2 : ℝ)
          * (M : ℝ) ^ ((-γ - 2) * (-1 / 2)) := by ring
  linarith

/-- **Dyadic assembly.** For `1 ≤ L ≤ Z`, the ψ-sum over `[L, Z]` is at most the sum of the block bounds over the
`⌊log₂(Z/L)⌋ + 1` doubling blocks starting at `L 2^k`. -/
theorem sum_Ico_bound (γ : ℝ) (hγ : 0 < γ) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ A : ℝ, 0 < A → ∀ L Z : ℕ, 1 ≤ L → L ≤ Z →
      |∑ n ∈ Ico L (Z + 1), ψ (A * (n : ℝ) ^ (-γ))|
        ≤ ∑ k ∈ range (Nat.log 2 (Z / L) + 1),
            (C1 * A ^ (1 / 3 : ℝ) * ((L : ℝ) * 2 ^ k) ^ ((1 - γ) / 3)
              + C2 * A ^ (-1 / 2 : ℝ) * ((L : ℝ) * 2 ^ k) ^ ((γ + 2) / 2)) := by
  obtain ⟨C1, C2, hC1, hC2, hB⟩ := block_bound γ hγ
  refine ⟨C1, C2, hC1, hC2, ?_⟩
  intro A hA L Z hL hLZ
  obtain ⟨hlo, hhi⟩ := log_facts L Z hL hLZ
  set K := Nat.log 2 (Z / L) with hK
  set a : ℕ → ℕ := fun k => min (L * 2 ^ k) (Z + 1) with ha
  have hmono : Monotone a := fun i j h =>
    min_le_min_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) h))
  have ha0 : a 0 = L := by simp [ha]; omega
  have haK : a (K + 1) = Z + 1 := by simp only [ha]; omega
  have hsum := sum_blocks (fun n => ψ (A * (n : ℝ) ^ (-γ))) a hmono (K + 1)
  rw [ha0, haK] at hsum
  rw [← hsum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro k hk
  have hkK : k ≤ K := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hMZ : L * 2 ^ k ≤ Z :=
    (Nat.mul_le_mul_left L (Nat.pow_le_pow_right (by norm_num) hkK)).trans hlo
  have hak : a k = L * 2 ^ k := by simp only [ha]; omega
  have hak1 : a (k + 1) ≤ 2 * (L * 2 ^ k) := by
    simp only [ha]; rw [pow_succ]
    exact (min_le_left _ _).trans (by ring_nf; exact le_rfl)
  have hle : a k ≤ a (k + 1) := hmono (Nat.le_succ k)
  rw [hak] at hle ⊢
  rw [Finset.sum_Ico_eq_sum_range]
  have hM1 : 1 ≤ L * 2 ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have := hB A hA (L * 2 ^ k) (a (k + 1) - L * 2 ^ k) hM1 (by omega)
  push_cast at this ⊢
  exact this

/-- `√(y/b³) = √y · b^{-3/2}`. -/
lemma sqrt_div_cube_eq (y : ℝ) (b : ℝ) (hb : 0 < b) :
    √(y / b ^ 3) = √y * b ^ (-(3 / 2 : ℝ)) := by
  rw [Real.sqrt_div' _ (by positivity), Real.rpow_neg hb.le, div_eq_mul_inv]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hb.le]
  norm_num

/-- `(y/a²)^{1/3} = y^{1/3} · a^{-2/3}`. -/
lemma cbrt_div_sq_eq (y : ℝ) (hy : 0 ≤ y) (a : ℝ) (ha : 0 < a) :
    (y / a ^ 2) ^ ((1 : ℝ) / 3) = y ^ ((1 : ℝ) / 3) * a ^ (-(2 / 3 : ℝ)) := by
  rw [Real.div_rpow hy (by positivity), Real.rpow_neg ha.le, div_eq_mul_inv]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
  norm_num

/-- **BG3, first sum.** `|Ψ₁(y)| ≤ C y^{1/7}` for `y ≥ 1`. -/
theorem abs_Psi1_le : ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y →
    |∑ b ∈ Icc 1 ⌊y ^ ((1 : ℝ) / 5)⌋₊, ψ (√(y / (b : ℝ) ^ 3))| ≤ C * y ^ ((1 : ℝ) / 7) := by
  obtain ⟨C1, C2, hC1, hC2, hS⟩ := sum_Ico_bound (3 / 2) (by norm_num)
  set r := (2 : ℝ) ^ (7 / 4 : ℝ)
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hq1 : (2 : ℝ) ^ (-1 / 6 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  set c1 := C1 / (1 - (2 : ℝ) ^ (-1 / 6 : ℝ))
  set c2 := C2 * (r / (r - 1))
  have hc1 : 0 ≤ c1 := div_nonneg hC1 (by linarith)
  have hc2 : 0 ≤ c2 := mul_nonneg hC2 (div_nonneg (by linarith) (by linarith))
  refine ⟨1 / 2 + c1 + c2, ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := by linarith
  set Z := ⌊y ^ ((1 : ℝ) / 5)⌋₊ with hZ
  set T := ⌊y ^ ((1 : ℝ) / 7)⌋₊ with hT
  have hy7 : 1 ≤ y ^ ((1 : ℝ) / 7) := Real.one_le_rpow hy (by norm_num)
  have hTle : (T : ℝ) ≤ y ^ ((1 : ℝ) / 7) := Nat.floor_le (by linarith)
  have hTlt : y ^ ((1 : ℝ) / 7) < T + 1 := Nat.lt_floor_add_one _
  have hZle : (Z : ℝ) ≤ y ^ ((1 : ℝ) / 5) := Nat.floor_le (by positivity)
  have hterm : ∀ b ∈ Icc 1 Z, ψ (√(y / (b : ℝ) ^ 3)) = ψ (√y * (b : ℝ) ^ (-(3 / 2 : ℝ))) := by
    intro b hb
    have : (0 : ℝ) < b := by exact_mod_cast (mem_Icc.mp hb).1
    rw [sqrt_div_cube_eq y b this]
  rw [sum_congr rfl hterm, show Icc 1 Z = Ico 1 (Z + 1) by rfl]
  have hpos : 0 ≤ c1 * y ^ ((1 : ℝ) / 7) + c2 * y ^ ((1 : ℝ) / 7) := by positivity
  rcases lt_or_ge Z (T + 1) with hZT | hZT
  · -- every term trivially
    refine (abs_sum_psi_le_card _ _).trans ?_
    simp only [Nat.card_Ico, Nat.add_sub_cancel]
    have : (Z : ℝ) ≤ T := by exact_mod_cast Nat.lt_succ_iff.mp hZT
    nlinarith
  · rw [← Finset.sum_Ico_consecutive _ (show 1 ≤ T + 1 by omega) (show T + 1 ≤ Z + 1 by omega)]
    refine (abs_add_le _ _).trans ?_
    have hhead := abs_sum_psi_le_card (Ico 1 (T + 1)) (fun n => √y * (n : ℝ) ^ (-(3 / 2 : ℝ)))
    simp only [Nat.card_Ico, Nat.add_sub_cancel] at hhead
    have htail := hS (√y) (by positivity) (T + 1) Z (by omega) hZT
    set K := Nat.log 2 (Z / (T + 1))
    have hK := (log_facts (T + 1) Z (by omega) hZT).1
    rw [show (-(3 / 2 : ℝ)) = -(3 / 2) from rfl] at htail
    rw [sum_add_distrib, ← mul_sum, ← mul_sum] at htail
    norm_num at htail
    -- exponents: (1 - 3/2)/3 = -1/6, (3/2 + 2)/2 = 7/4
    have hA3 : (√y) ^ (1 / 3 : ℝ) = y ^ (1 / 6 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy0]; norm_num
    have hA2 : (√y) ^ (-(1 / 2) : ℝ) = y ^ (-1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy0]; norm_num
    have g1 := geom_neg (T + 1) (-1 / 6) (by norm_num) (K + 1)
    have g2 := geom_pos (T + 1) (7 / 4) (by norm_num) K
    -- L^{-1/6} ≤ y^{-1/42}
    have hL : ((T + 1 : ℕ) : ℝ) ^ (-1 / 6 : ℝ) ≤ y ^ (-1 / 42 : ℝ) := by
      have : y ^ (-1 / 42 : ℝ) = (y ^ ((1 : ℝ) / 7)) ^ (-1 / 6 : ℝ) := by
        rw [← Real.rpow_mul hy0]; norm_num
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by norm_num)
    have hZ74 : (((T + 1 : ℕ) : ℝ) * 2 ^ K) ^ (7 / 4 : ℝ) ≤ y ^ (7 / 20 : ℝ) := by
      have : y ^ (7 / 20 : ℝ) = (y ^ ((1 : ℝ) / 5)) ^ (7 / 4 : ℝ) := by
        rw [← Real.rpow_mul hy0]; norm_num
      rw [this]
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      refine le_trans ?_ hZle
      exact_mod_cast hK
    have e1 : y ^ (1 / 6 : ℝ) * y ^ (-1 / 42 : ℝ) = y ^ ((1 : ℝ) / 7) := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    have e2 : y ^ (-1 / 4 : ℝ) * y ^ (7 / 20 : ℝ) = y ^ (1 / 10 : ℝ) := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    have h10 : y ^ (1 / 10 : ℝ) ≤ y ^ ((1 : ℝ) / 7) := Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
    have hy16 : 0 ≤ y ^ (1 / 6 : ℝ) := by positivity
    have hy14 : 0 ≤ y ^ (-1 / 4 : ℝ) := by positivity
    have t1 : C1 * y ^ (1 / 6 : ℝ) * ∑ k ∈ range (K + 1), (((T + 1 : ℕ) : ℝ) * 2 ^ k) ^ (-1 / 6 : ℝ)
        ≤ c1 * y ^ ((1 : ℝ) / 7) := by
      calc _ ≤ C1 * y ^ (1 / 6 : ℝ) * (y ^ (-1 / 42 : ℝ) / (1 - (2 : ℝ) ^ (-1 / 6 : ℝ))) := by
            gcongr
            exact g1.trans (div_le_div_of_nonneg_right hL (by linarith))
        _ = c1 * y ^ ((1 : ℝ) / 7) := by rw [← e1]; ring
    have t2 : C2 * y ^ (-1 / 4 : ℝ) * ∑ k ∈ range (K + 1), (((T + 1 : ℕ) : ℝ) * 2 ^ k) ^ (7 / 4 : ℝ)
        ≤ c2 * y ^ ((1 : ℝ) / 7) := by
      calc _ ≤ C2 * y ^ (-1 / 4 : ℝ) * (r / (r - 1) * y ^ (7 / 20 : ℝ)) := by
            gcongr
            exact g2.trans (mul_le_mul_of_nonneg_left hZ74 (div_nonneg (by linarith) (by linarith)))
        _ = c2 * (y ^ (-1 / 4 : ℝ) * y ^ (7 / 20 : ℝ)) := by ring
        _ ≤ c2 * y ^ ((1 : ℝ) / 7) := by rw [e2]; exact mul_le_mul_of_nonneg_left h10 hc2
    simp only [hA3, hA2] at htail
    have hT2 : (T : ℝ) / 2 ≤ 1 / 2 * y ^ ((1 : ℝ) / 7) := by linarith
    push_cast at htail t1 t2
    norm_num at htail t1 t2
    linarith

/-- **BG3, second sum.** `|Ψ₂(y)| ≤ C y^{2/15}` for `y ≥ 1`. -/
theorem abs_Psi2_le : ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y →
    |∑ a ∈ Icc 1 ⌊y ^ ((1 : ℝ) / 5)⌋₊, ψ ((y / (a : ℝ) ^ 2) ^ ((1 : ℝ) / 3))| ≤ C * y ^ ((2 : ℝ) / 15) := by
  obtain ⟨C1, C2, hC1, hC2, hS⟩ := sum_Ico_bound (2 / 3) (by norm_num)
  set r1 := (2 : ℝ) ^ (1 / 9 : ℝ)
  set r2 := (2 : ℝ) ^ (4 / 3 : ℝ)
  have hr1 : 1 < r1 := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hr2 : 1 < r2 := Real.one_lt_rpow (by norm_num) (by norm_num)
  set c1 := C1 * (r1 / (r1 - 1))
  set c2 := C2 * (r2 / (r2 - 1))
  have hc1 : 0 ≤ c1 := mul_nonneg hC1 (div_nonneg (by linarith) (by linarith))
  have hc2 : 0 ≤ c2 := mul_nonneg hC2 (div_nonneg (by linarith) (by linarith))
  refine ⟨c1 + c2, ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := by linarith
  set Z := ⌊y ^ ((1 : ℝ) / 5)⌋₊ with hZ
  have hy5 : 1 ≤ y ^ ((1 : ℝ) / 5) := Real.one_le_rpow hy (by norm_num)
  have hZ1 : 1 ≤ Z := Nat.le_floor (by exact_mod_cast hy5)
  have hZle : (Z : ℝ) ≤ y ^ ((1 : ℝ) / 5) := Nat.floor_le (by positivity)
  have hterm : ∀ a ∈ Icc 1 Z, ψ ((y / (a : ℝ) ^ 2) ^ ((1 : ℝ) / 3))
      = ψ (y ^ ((1 : ℝ) / 3) * (a : ℝ) ^ (-(2 / 3 : ℝ))) := by
    intro a ha
    have : (0 : ℝ) < a := by exact_mod_cast (mem_Icc.mp ha).1
    rw [cbrt_div_sq_eq y hy0 a this]
  rw [sum_congr rfl hterm, show Icc 1 Z = Ico 1 (Z + 1) by rfl]
  have htail := hS (y ^ ((1 : ℝ) / 3)) (by positivity) 1 Z le_rfl hZ1
  set K := Nat.log 2 (Z / 1)
  have hK := (log_facts 1 Z le_rfl hZ1).1
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at htail
  norm_num at htail
  have hA3 : (y ^ ((1 : ℝ) / 3)) ^ (1 / 3 : ℝ) = y ^ (1 / 9 : ℝ) := by
    rw [← Real.rpow_mul hy0]; norm_num
  have hA2 : (y ^ ((1 : ℝ) / 3)) ^ (-(1 / 2) : ℝ) = y ^ (-1 / 6 : ℝ) := by
    rw [← Real.rpow_mul hy0]; norm_num
  have g1 := geom_pos 1 (1 / 9) (by norm_num) K
  have g2 := geom_pos 1 (4 / 3) (by norm_num) K
  have hZu : ∀ u : ℝ, 0 < u → (((1 : ℕ) : ℝ) * 2 ^ K) ^ u ≤ y ^ (u / 5) := by
    intro u hu
    have : y ^ (u / 5) = (y ^ ((1 : ℝ) / 5)) ^ u := by
      rw [← Real.rpow_mul hy0]; ring_nf
    rw [this]
    refine Real.rpow_le_rpow (by positivity) ?_ hu.le
    refine le_trans ?_ hZle
    exact_mod_cast hK
  have e1 : y ^ (1 / 9 : ℝ) * y ^ ((1 / 9 : ℝ) / 5) = y ^ ((2 : ℝ) / 15) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have e2 : y ^ (-1 / 6 : ℝ) * y ^ ((4 / 3 : ℝ) / 5) = y ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have h10 : y ^ (1 / 10 : ℝ) ≤ y ^ ((2 : ℝ) / 15) := Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
  have t1 : C1 * y ^ (1 / 9 : ℝ) * ∑ k ∈ range (K + 1), (((1 : ℕ) : ℝ) * 2 ^ k) ^ (1 / 9 : ℝ)
      ≤ c1 * y ^ ((2 : ℝ) / 15) := by
    calc _ ≤ C1 * y ^ (1 / 9 : ℝ) * (r1 / (r1 - 1) * y ^ ((1 / 9 : ℝ) / 5)) := by
          gcongr
          exact g1.trans (mul_le_mul_of_nonneg_left (hZu _ (by norm_num))
            (div_nonneg (by linarith) (by linarith)))
      _ = c1 * y ^ ((2 : ℝ) / 15) := by rw [← e1]; ring
  have t2 : C2 * y ^ (-1 / 6 : ℝ) * ∑ k ∈ range (K + 1), (((1 : ℕ) : ℝ) * 2 ^ k) ^ (4 / 3 : ℝ)
      ≤ c2 * y ^ ((2 : ℝ) / 15) := by
    calc _ ≤ C2 * y ^ (-1 / 6 : ℝ) * (r2 / (r2 - 1) * y ^ ((4 / 3 : ℝ) / 5)) := by
          gcongr
          exact g2.trans (mul_le_mul_of_nonneg_left (hZu _ (by norm_num))
            (div_nonneg (by linarith) (by linarith)))
      _ = c2 * (y ^ (-1 / 6 : ℝ) * y ^ ((4 / 3 : ℝ) / 5)) := by ring
      _ ≤ c2 * y ^ ((2 : ℝ) / 15) := by rw [e2]; exact mul_le_mul_of_nonneg_left h10 hc2
  simp only [hA3, hA2] at htail
  push_cast at htail t1 t2
  norm_num at htail t1 t2
  linarith

end PowerfulFC.BG3
end

-- ===== PowerfulFC.BatemanGrosswald =====
section
/-
# Bateman–Grosswald: `Q(x) = A x^{1/2} + B x^{1/3} + O(x^{1/6})`, in formal-conjectures' wording (rung BG4)

The statement `asymptotic_bateman_grosswald` is copied token for token from google-deepmind/formal-conjectures
`FormalConjectures/Wikipedia/PowerfulNumbersDensity.lean` (commit `ea8e3e19`), under the same `open` line, with
`Q`, `A`, `B` the abbreviations of `PowerfulFC.Main` (also FC's, token for token).

Proof (assembly of BG1-BG3).

1. `abs_E_le`: with `E(y) = S⌊y⌋ − ζ(3/2)√y − ζ(2/3)y^{1/3}`, BG1 (`abs_S_sub_main_le_two`) and BG3
   (`abs_Psi1_le`, `abs_Psi2_le`) give `|E(y)| ≤ C y^{1/7}` for `y ≥ 1` (`2/15 < 1/7`).
2. `Q x = ∑_{d ≤ x} μ(d) S⌊x/d⁶⌋` (`BG1.Q_eq_sum_moebius_S`); the terms with `d > D = ⌊x^{1/6}⌋` vanish, and for
   `d ≤ D`, `S⌊x/d⁶⌋ = ζ(3/2)√x d^{-3} + ζ(2/3)x^{1/3} d^{-2} + E(x/d⁶)` with `x/d⁶ ≥ 1`.
3. `∑_{d ≤ D} |E(x/d⁶)| ≤ C x^{1/7} ∑_{d ≤ D} d^{-6/7} ≤ 7C x^{1/7} D^{1/7} ≤ 7C x^{1/6}` (`sum_rpow_le`, by
   telescoping `t^{-6/7} ≤ 7(t^{1/7} − (t−1)^{1/7})`, Bernoulli).
4. `1/ζ(k) = ∑ μ(n) n^{-k}` for `k = 2, 3` (`inv_zeta_eq`, from `LeanClassics.SquarefreeLSeries.LSeries_moebius`),
   and the tails past `D` are `≤ 1/(2D²)` and `≤ 1/D` (`tail_bound`), so the main-term defects are
   `≤ |ζ(3/2)| √x/(2D²) ≤ 2|ζ(3/2)| x^{1/6}` and `≤ |ζ(2/3)| x^{1/3}/D ≤ 2|ζ(2/3)| x^{1/6}`.
-/

open Finset Real

noncomputable section

namespace PowerfulFC.BG4

open PowerfulFC.BG1 (S ψ)
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- The error after the two main terms, `E(y) = S⌊y⌋ − ζ(3/2)√y − ζ(2/3) y^{1/3}`. -/
def E (y : ℝ) : ℝ :=
  (S ⌊y⌋₊ : ℝ) - ((riemannZeta (3 / 2)).re * √y + (riemannZeta (2 / 3)).re * y ^ ((1 : ℝ) / 3))

/-- **Step 1.** `|E(y)| ≤ C y^{1/7}` for `y ≥ 1`. -/
theorem abs_E_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → |E y| ≤ C * y ^ ((1 : ℝ) / 7) := by
  obtain ⟨C1, h1⟩ := BG3.abs_Psi1_le
  obtain ⟨C2, h2⟩ := BG3.abs_Psi2_le
  refine ⟨2 + |C1| + |C2|, by positivity, fun y hy => ?_⟩
  have hB := BG1.abs_S_sub_main_le_two hy
  have e1 := h1 y hy
  have e2 := h2 y hy
  have p7 : 1 ≤ y ^ ((1 : ℝ) / 7) := Real.one_le_rpow hy (by norm_num)
  have p215 : y ^ ((2 : ℝ) / 15) ≤ y ^ ((1 : ℝ) / 7) :=
    Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
  have q1 : C1 * y ^ ((1 : ℝ) / 7) ≤ |C1| * y ^ ((1 : ℝ) / 7) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have q2 : C2 * y ^ ((2 : ℝ) / 15) ≤ |C2| * y ^ ((1 : ℝ) / 7) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left p215 (abs_nonneg _))
  unfold E
  rw [abs_le] at hB e1 e2 ⊢
  constructor <;> nlinarith

/-- `t^{-6/7} ≤ 7 (t^{1/7} − (t − 1)^{1/7})` for `t ≥ 1` (Bernoulli). -/
lemma rpow_step {t : ℝ} (ht : 1 ≤ t) :
    t ^ (-(6 / 7 : ℝ)) ≤ 7 * (t ^ ((1 : ℝ) / 7) - (t - 1) ^ ((1 : ℝ) / 7)) := by
  have ht0 : 0 < t := by linarith
  have hti : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  have hB := rpow_one_add_le_one_add_mul_self (s := -t⁻¹) (p := 1 / 7) (by linarith)
    (by norm_num) (by norm_num)
  have e : t - 1 = t * (1 + -t⁻¹) := by field_simp; ring
  have hnn : 0 ≤ 1 + -t⁻¹ := by linarith
  rw [e, Real.mul_rpow ht0.le hnn]
  have e2 : t ^ (-(6 / 7 : ℝ)) = t ^ ((1 : ℝ) / 7) * t⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht0]; norm_num
  have hp : 0 ≤ t ^ ((1 : ℝ) / 7) := by positivity
  rw [e2]
  nlinarith [mul_le_mul_of_nonneg_left hB hp]

/-- **Step 3, the sum.** `∑_{i < D} (i+1)^{-6/7} ≤ 7 D^{1/7}`. -/
lemma sum_rpow_le (D : ℕ) :
    ∑ i ∈ range D, ((i + 1 : ℕ) : ℝ) ^ (-(6 / 7 : ℝ)) ≤ 7 * (D : ℝ) ^ ((1 : ℝ) / 7) := by
  induction D with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h := rpow_step (t := ((n + 1 : ℕ) : ℝ)) (by exact_mod_cast Nat.succ_pos n)
    push_cast at h ih ⊢
    rw [show (n : ℝ) + 1 - 1 = n by ring] at h
    linarith

/-- Telescoping tail bound: if `|f (i + D + 1)| ≤ u i − u (i+1)` and `u ≥ 0`, then
`|∑' f − ∑_{n < D+1} f| ≤ u 0`. -/
lemma tail_bound {f : ℕ → ℝ} (u : ℕ → ℝ) (D : ℕ) (hf : Summable f)
    (hstep : ∀ i, |f (i + (D + 1))| ≤ u i - u (i + 1)) (hu : ∀ i, 0 ≤ u i) :
    |∑' n, f n - ∑ n ∈ range (D + 1), f n| ≤ u 0 := by
  rw [← hf.sum_add_tsum_nat_add (D + 1), add_sub_cancel_left]
  have hs : Summable fun i => f (i + (D + 1)) := (summable_nat_add_iff (D + 1)).2 hf
  have hsa : Summable fun i => ‖f (i + (D + 1))‖ := by
    simpa [Real.norm_eq_abs] using (summable_abs_iff.2 hs)
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hsa).trans ?_
  refine Real.tsum_le_of_sum_range_le (fun i => norm_nonneg _) fun n => ?_
  calc ∑ i ∈ range n, ‖f (i + (D + 1))‖ ≤ ∑ i ∈ range n, (u i - u (i + 1)) :=
        sum_le_sum fun i _ => by rw [Real.norm_eq_abs]; exact hstep i
    _ = u 0 - u n := sum_range_sub' _ _
    _ ≤ u 0 := by linarith [hu n]

/-- `μ(n) / n^k`. -/
def f (k : ℕ) (n : ℕ) : ℝ := (μ n : ℝ) / (n : ℝ) ^ k

lemma abs_f_le (k n : ℕ) : |f k n| ≤ 1 / (n : ℝ) ^ k := by
  unfold f
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ k)]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact_mod_cast abs_moebius_le_one

lemma summable_f {k : ℕ} (hk : 1 < k) : Summable (f k) := by
  refine Summable.of_norm_bounded (Real.summable_one_div_nat_pow.2 hk) fun n => ?_
  rw [Real.norm_eq_abs]; exact abs_f_le k n

/-- **Step 4, constants.** `1/ζ(k) = ∑ μ(n) n^{-k}` for `k ≥ 2`. -/
theorem inv_zeta_eq {k : ℕ} (hk : 1 < k) : ((riemannZeta k).re)⁻¹ = ∑' n : ℕ, f k n := by
  have hre : 1 < ((k : ℂ)).re := by simp; exact_mod_cast hk
  have hL := LeanClassics.SquarefreeLSeries.LSeries_moebius hre
  have hterm : ∀ n : ℕ, LSeries.term (fun n => (μ n : ℂ)) k n = ((f k n : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, f]
    · rw [LSeries.term_of_ne_zero hn.ne', Complex.cpow_natCast]
      simp [f]
  have hLS : LSeries (fun n => (μ n : ℂ)) k = ((∑' n : ℕ, f k n : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have hz : riemannZeta (k : ℂ) = (((riemannZeta k).re : ℝ) : ℂ) := by
    have := PowerfulFC.ZetaPartial.riemannZeta_ofReal_eq (k : ℝ)
    simpa using this
  rw [hLS, hz, ← Complex.ofReal_inv] at hL
  exact (Complex.ofReal_injective hL).symm

/-- Tail of `μ(n)/n²` past `D`: at most `1/D`. -/
lemma tail_two {D : ℕ} (hD : 1 ≤ D) :
    |∑' n, f 2 n - ∑ n ∈ range (D + 1), f 2 n| ≤ 1 / (D : ℝ) := by
  have h := tail_bound (f := f 2) (fun i => 1 / ((i : ℝ) + D)) D (summable_f (by norm_num)) ?_ ?_
  · simpa using h
  · intro i
    refine (abs_f_le 2 _).trans ?_
    have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have hm : (1 : ℝ) ≤ (i : ℝ) + D := by have := i.cast_nonneg (α := ℝ); linarith
    push_cast
    rw [show (i : ℝ) + (D + 1) = (i : ℝ) + D + 1 by ring,
      show (i : ℝ) + 1 + D = (i : ℝ) + D + 1 by ring]
    set m := (i : ℝ) + D
    rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · intro i; positivity

/-- Tail of `μ(n)/n³` past `D`: at most `1/(2D²)`. -/
lemma tail_three {D : ℕ} (hD : 1 ≤ D) :
    |∑' n, f 3 n - ∑ n ∈ range (D + 1), f 3 n| ≤ 1 / (2 * (D : ℝ) ^ 2) := by
  have h := tail_bound (f := f 3) (fun i => 1 / (2 * ((i : ℝ) + D) ^ 2)) D (summable_f (by norm_num)) ?_ ?_
  · simpa using h
  · intro i
    refine (abs_f_le 3 _).trans ?_
    have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have hm : (1 : ℝ) ≤ (i : ℝ) + D := by have := i.cast_nonneg (α := ℝ); linarith
    push_cast
    rw [show (i : ℝ) + (D + 1) = (i : ℝ) + D + 1 by ring,
      show (i : ℝ) + 1 + D = (i : ℝ) + D + 1 by ring]
    set m := (i : ℝ) + D
    rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < m) (by linarith : (0 : ℝ) < m)]
  · intro i; positivity

lemma S_zero : S 0 = 0 := by simp [S]

/-- `√(x/d⁶) = √x / d³`. -/
lemma sqrt_div_six (x : ℝ) (d : ℝ) (hd : 0 ≤ d) : √(x / d ^ 6) = √x / d ^ 3 := by
  rw [Real.sqrt_div' x (by positivity), show d ^ 6 = (d ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]

/-- `(x/d⁶)^{1/3} = x^{1/3} / d²`. -/
lemma cbrt_div_six {x : ℝ} (hx : 0 ≤ x) (d : ℝ) (hd : 0 ≤ d) :
    (x / d ^ 6) ^ ((1 : ℝ) / 3) = x ^ ((1 : ℝ) / 3) / d ^ 2 := by
  rw [Real.div_rpow hx (by positivity), ← Real.rpow_natCast d 6, ← Real.rpow_mul hd,
    ← Real.rpow_natCast d 2]
  norm_num

/-- `(x/d⁶)^{1/7} = x^{1/7} d^{-6/7}`. -/
lemma rpow_seven_div_six {x : ℝ} (hx : 0 ≤ x) {d : ℝ} (hd : 0 < d) :
    (x / d ^ 6) ^ ((1 : ℝ) / 7) = x ^ ((1 : ℝ) / 7) * d ^ (-(6 / 7 : ℝ)) := by
  rw [Real.div_rpow hx (by positivity), ← Real.rpow_natCast d 6, ← Real.rpow_mul hd.le,
    Real.rpow_neg hd.le, div_eq_mul_inv]
  norm_num

end PowerfulFC.BG4
end
end

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius
namespace LeanClassics.SquarefreeRH
def mert (n : ℕ) : ℝ := ∑ k ∈ Ioc 0 n, (μ k : ℝ)
end LeanClassics.SquarefreeRH

noncomputable section

namespace PowerfulFC.ETI

open LeanClassics.SquarefreeRH (mert)
open PowerfulFC.BG4 (f summable_f inv_zeta_eq)

lemma mert_succ (n : ℕ) : mert (n + 1) = mert n + (μ (n + 1) : ℝ) := by
  simp only [mert]
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]

/-- **Abel summation** from `D + 1` to `D + m`. -/
lemma abel (g : ℕ → ℝ) (D m : ℕ) :
    ∑ i ∈ range m, (μ (D + 1 + i) : ℝ) * g (D + 1 + i) =
      ∑ i ∈ range m, mert (D + 1 + i) * (g (D + 1 + i) - g (D + 1 + i + 1)) +
        mert (D + m) * g (D + m + 1) - mert D * g (D + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    have e1 : D + 1 + m = D + m + 1 := by ring
    have e2 : D + (m + 1) = D + m + 1 := by ring
    rw [e1, e2, mert_succ (D + m)]
    ring

/-- `y^{k+1} − x^{k+1} ≤ (k+1)(y − x) y^k` for `0 ≤ x ≤ y`. -/
lemma pow_succ_sub_pow_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (k : ℕ) :
    y ^ (k + 1) - x ^ (k + 1) ≤ (k + 1) * (y - x) * y ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hy : 0 ≤ y := hx.trans hxy
    have hxk : x ^ (k + 1) ≤ y ^ (k + 1) := pow_le_pow_left₀ hx hxy _
    have e : y ^ (k + 1 + 1) - x ^ (k + 1 + 1) =
        y * (y ^ (k + 1) - x ^ (k + 1)) + x ^ (k + 1) * (y - x) := by ring
    rw [e]
    have h1 : y * (y ^ (k + 1) - x ^ (k + 1)) ≤ y * ((k + 1) * (y - x) * y ^ k) :=
      mul_le_mul_of_nonneg_left ih hy
    have h2 : x ^ (k + 1) * (y - x) ≤ y ^ (k + 1) * (y - x) :=
      mul_le_mul_of_nonneg_right hxk (by linarith)
    push_cast
    have : y * ((k + 1) * (y - x) * y ^ k) = (k + 1) * (y - x) * y ^ (k + 1) := by ring
    nlinarith

/-- `1/n^k − 1/(n+1)^k ≤ k / n^{k+1}` for `n ≥ 1`. -/
lemma inv_pow_sub_le {n : ℝ} (hn : 1 ≤ n) (k : ℕ) :
    1 / n ^ k - 1 / (n + 1) ^ k ≤ k / n ^ (k + 1) := by
  have hn0 : 0 < n := by linarith
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := pow_succ_sub_pow_le hn0.le (by linarith : n ≤ n + 1) j
  rw [show n + 1 - n = 1 by ring, mul_one] at h
  have hA : 0 < n ^ (j + 1) := by positivity
  have hB : 0 < (n + 1) ^ (j + 1) := by positivity
  rw [div_sub_div _ _ hA.ne' hB.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  -- `((n+1)^{j+1} − n^{j+1}) n^{j+2} ≤ (j+1) n^{j+1} (n+1)^{j+1}`
  have e : (1 * (n + 1) ^ (j + 1) - n ^ (j + 1) * 1) * n ^ (j + 1 + 1) =
      ((n + 1) ^ (j + 1) - n ^ (j + 1)) * n * n ^ (j + 1) := by ring
  rw [e]
  push_cast
  have hpow : (n + 1) ^ j * n ≤ (n + 1) ^ (j + 1) := by
    rw [pow_succ]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : ((n + 1) ^ (j + 1) - n ^ (j + 1)) * n ≤ (j + 1) * (n + 1) ^ (j + 1) := by
    calc ((n + 1) ^ (j + 1) - n ^ (j + 1)) * n ≤ ((j + 1) * (n + 1) ^ j) * n :=
          mul_le_mul_of_nonneg_right h hn0.le
      _ = (j + 1) * ((n + 1) ^ j * n) := by ring
      _ ≤ (j + 1) * (n + 1) ^ (j + 1) := mul_le_mul_of_nonneg_left hpow (by positivity)
  calc ((n + 1) ^ (j + 1) - n ^ (j + 1)) * n * n ^ (j + 1)
      ≤ (j + 1) * (n + 1) ^ (j + 1) * n ^ (j + 1) := mul_le_mul_of_nonneg_right h3 hA.le
    _ = ((j : ℝ) + 1) * (n ^ (j + 1) * (n + 1) ^ (j + 1)) := by ring

/-- `b n^{-(b+1)} ≤ (n−1)^{-b} − n^{-b}` for `n ≥ 2`, `b ≥ 1` (Bernoulli). -/
lemma rpow_neg_step {n b : ℝ} (hn : 2 ≤ n) (hb : 1 ≤ b) :
    b * n ^ (-(b + 1)) ≤ (n - 1) ^ (-b) - n ^ (-b) := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  set s := 1 / (n - 1) with hs
  have hs0 : 0 ≤ s := by positivity
  have hB := one_add_mul_self_le_rpow_one_add (s := s) (by linarith) hb
  -- `(n−1)^{-b} = n^{-b} (1 + s)^b`
  have e1 : 1 + s = n / (n - 1) := by rw [hs]; field_simp; ring
  have e2 : (n - 1) ^ (-b) = n ^ (-b) * (1 + s) ^ b := by
    rw [e1, Real.div_rpow hn0.le hn1.le, Real.rpow_neg hn1.le, Real.rpow_neg hn0.le]
    have : 0 < n ^ b := by positivity
    have : 0 < (n - 1) ^ b := by positivity
    field_simp
  have e3 : n ^ (-(b + 1)) = n ^ (-b) * (1 / n) := by
    rw [neg_add, Real.rpow_add hn0, Real.rpow_neg_one, one_div]
  rw [e2, e3]
  have hp : 0 < n ^ (-b) := by positivity
  have hsn : 1 / n ≤ s := by
    rw [hs]; exact one_div_le_one_div_of_le hn1 (by linarith)
  have : b * (1 / n) ≤ (1 + s) ^ b - 1 := by
    have : b * (1 / n) ≤ b * s := mul_le_mul_of_nonneg_left hsn (by linarith)
    linarith
  have := mul_le_mul_of_nonneg_left this hp.le
  nlinarith

/-- `∑_{i<m} (D+1+i)^{-(b+1)} ≤ D^{-b}/b` for `D ≥ 1`, `b ≥ 1`. -/
lemma sum_rpow_tail_le {b : ℝ} (hb : 1 ≤ b) {D : ℕ} (hD : 1 ≤ D) (m : ℕ) :
    ∑ i ∈ range m, ((D + 1 + i : ℕ) : ℝ) ^ (-(b + 1)) ≤ (D : ℝ) ^ (-b) / b := by
  have hb0 : 0 < b := by linarith
  have key : ∀ m : ℕ, b * ∑ i ∈ range m, ((D + 1 + i : ℕ) : ℝ) ^ (-(b + 1)) ≤
      (D : ℝ) ^ (-b) - ((D + m : ℕ) : ℝ) ^ (-b) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, mul_add]
      have h := rpow_neg_step (n := ((D + 1 + m : ℕ) : ℝ)) (b := b)
        (by have : (1 : ℝ) ≤ D := by exact_mod_cast hD
            push_cast; have := m.cast_nonneg (α := ℝ); linarith) hb
      have e : ((D + 1 + m : ℕ) : ℝ) - 1 = ((D + m : ℕ) : ℝ) := by push_cast; ring
      have e' : D + 1 + m = D + (m + 1) := by ring
      rw [e] at h
      rw [e'] at h ⊢
      linarith
  have h := key m
  have hpos : 0 ≤ ((D + m : ℕ) : ℝ) ^ (-b) := by positivity
  rw [le_div_iff₀ hb0]
  linarith

/-- **R2.** If `|M(n)| ≤ C n^a` for all `n` (`a ≤ k − 1`, `k ≥ 2`), then for `D ≥ 1`,
`|∑' μ(n)/n^k − ∑_{n ≤ D} μ(n)/n^k| ≤ C (k/(k−a) + 2) D^{a−k}`. -/
theorem abs_tail_le {C a : ℝ} {k : ℕ} (hk : 2 ≤ k) (hC : 0 ≤ C)
    (hak : a ≤ k - 1) (hM : ∀ n : ℕ, |mert n| ≤ C * (n : ℝ) ^ a) {D : ℕ} (hD : 1 ≤ D) :
    |∑' n, f k n - ∑ n ∈ range (D + 1), f k n| ≤
      C * (k / (k - a) + 2) * (D : ℝ) ^ (a - k) := by
  set b : ℝ := k - a with hbdef
  have hb : 1 ≤ b := by rw [hbdef]; linarith
  have hb0 : 0 < b := by linarith
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hsum := summable_f (k := k) (by omega)
  set g : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ k with hg
  have hfg : ∀ n, f k n = (μ n : ℝ) * g n := fun n => by simp [f, g, div_eq_mul_inv]
  rw [← hsum.sum_add_tsum_nat_add (D + 1), add_sub_cancel_left]
  have hs : Summable fun i => f k (i + (D + 1)) := (summable_nat_add_iff (D + 1)).2 hsum
  set B := C * (k / (k - a) + 2) * (D : ℝ) ^ (a - k)
  -- every partial sum is bounded by `B`
  have hpart : ∀ m : ℕ, |∑ i ∈ range m, f k (i + (D + 1))| ≤ B := by
    intro m
    have e : ∑ i ∈ range m, f k (i + (D + 1)) = ∑ i ∈ range m, (μ (D + 1 + i) : ℝ) * g (D + 1 + i) :=
      sum_congr rfl fun i _ => by rw [hfg, show i + (D + 1) = D + 1 + i by ring]
    rw [e, abel]
    -- `n^a g n ≤ n^{a-k}`-type facts
    have hrp : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ a * (1 / (n : ℝ) ^ (k + 1)) = (n : ℝ) ^ (-(b + 1)) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]
      congr 1; rw [hbdef]; push_cast; ring
    -- boundary term bound: for `n ≥ D`, `|M(n)| g(n+1) ≤ C D^{a−k}`
    have hbdry : ∀ n : ℕ, D ≤ n → |mert n * g (n + 1)| ≤ C * (D : ℝ) ^ (a - k) := by
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := hD1.trans (by exact_mod_cast hn)
      have hn0 : (0 : ℝ) < n := by linarith
      have hg0 : 0 ≤ g (n + 1) := by simp only [g]; positivity
      rw [abs_mul, abs_of_nonneg hg0]
      have hgle : g (n + 1) ≤ (n : ℝ) ^ (-(k : ℝ)) := by
        simp only [g]
        rw [Real.rpow_neg hn0.le, Real.rpow_natCast, ← one_div]
        push_cast
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hn0.le (by linarith) k)
      calc |mert n| * g (n + 1) ≤ C * (n : ℝ) ^ a * (n : ℝ) ^ (-(k : ℝ)) :=
            mul_le_mul (hM n) hgle hg0 (by positivity)
        _ = C * (n : ℝ) ^ (a - k) := by
            rw [mul_assoc, ← Real.rpow_add hn0]; ring_nf
        _ ≤ C * (D : ℝ) ^ (a - k) := by
            refine mul_le_mul_of_nonneg_left ?_ hC
            exact Real.rpow_le_rpow_of_nonpos hD0 (by exact_mod_cast hn) (by linarith)
    -- interior terms
    have hint : ∀ i ∈ range m, |mert (D + 1 + i) * (g (D + 1 + i) - g (D + 1 + i + 1))| ≤
        C * k * ((D + 1 + i : ℕ) : ℝ) ^ (-(b + 1)) := by
      intro i _
      set n := D + 1 + i
      have hn : 1 ≤ n := by omega
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hdiff0 : 0 ≤ g n - g (n + 1) := by
        simp only [g]; push_cast
        exact sub_nonneg.2 (one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_left₀ (by linarith) (by linarith) k))
      have hdiff : g n - g (n + 1) ≤ k * (1 / (n : ℝ) ^ (k + 1)) := by
        simp only [g]; push_cast
        have := inv_pow_sub_le hn1 k
        rw [mul_one_div]; exact this
      rw [abs_mul, abs_of_nonneg hdiff0]
      calc |mert n| * (g n - g (n + 1)) ≤ C * (n : ℝ) ^ a * (k * (1 / (n : ℝ) ^ (k + 1))) :=
            mul_le_mul (hM n) hdiff hdiff0 (by positivity)
        _ = C * k * ((n : ℝ) ^ a * (1 / (n : ℝ) ^ (k + 1))) := by ring
        _ = C * k * (n : ℝ) ^ (-(b + 1)) := by rw [hrp n hn]
    have hT := sum_rpow_tail_le hb hD m
    have hDb : (D : ℝ) ^ (-b) = (D : ℝ) ^ (a - k) := by rw [hbdef]; congr 1; ring
    have hI : |∑ i ∈ range m, mert (D + 1 + i) * (g (D + 1 + i) - g (D + 1 + i + 1))| ≤
        C * (k / (k - a)) * (D : ℝ) ^ (a - k) := by
      refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hint).trans ?_)
      rw [← mul_sum]
      calc C * k * ∑ i ∈ range m, ((D + 1 + i : ℕ) : ℝ) ^ (-(b + 1)) ≤ C * k * ((D : ℝ) ^ (-b) / b) :=
            mul_le_mul_of_nonneg_left hT (by positivity)
        _ = C * (k / (k - a)) * (D : ℝ) ^ (a - k) := by rw [hDb, ← hbdef]; ring
    have h1 := hbdry (D + m) (by omega)
    have h2 := hbdry D le_rfl
    calc |∑ i ∈ range m, mert (D + 1 + i) * (g (D + 1 + i) - g (D + 1 + i + 1)) +
          mert (D + m) * g (D + m + 1) - mert D * g (D + 1)|
        ≤ |∑ i ∈ range m, mert (D + 1 + i) * (g (D + 1 + i) - g (D + 1 + i + 1))| +
          |mert (D + m) * g (D + m + 1)| + |mert D * g (D + 1)| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ B := by simp only [B]; nlinarith
  have ht := hs.hasSum.tendsto_sum_nat
  exact le_of_tendsto' ((continuous_abs.tendsto _).comp ht) hpart

/-- **R2, as `1/ζ(k)`.** Under the same hypotheses,
`|1/ζ(k) − ∑_{n ≤ D} μ(n)/n^k| ≤ C (k/(k−a) + 2) D^{a−k}`. -/
theorem abs_inv_zeta_sub_le {C a : ℝ} {k : ℕ} (hk : 2 ≤ k) (hC : 0 ≤ C)
    (hak : a ≤ k - 1) (hM : ∀ n : ℕ, |mert n| ≤ C * (n : ℝ) ^ a) {D : ℕ} (hD : 1 ≤ D) :
    |((riemannZeta k).re)⁻¹ - ∑ n ∈ range (D + 1), f k n| ≤
      C * (k / (k - a) + 2) * (D : ℝ) ^ (a - k) := by
  rw [inv_zeta_eq (by omega)]
  exact abs_tail_le hk hC hak hM hD

/-- `k = 2`: `|1/ζ(2) − ∑_{n ≤ D} μ(n)/n²| ≤ C (2/(2−a) + 2) D^{a−2}` for `a ≤ 1`. -/
theorem abs_tail_two_le {C a : ℝ} (hC : 0 ≤ C) (ha1 : a ≤ 1)
    (hM : ∀ n : ℕ, |mert n| ≤ C * (n : ℝ) ^ a) {D : ℕ} (hD : 1 ≤ D) :
    |((riemannZeta 2).re)⁻¹ - ∑ n ∈ range (D + 1), f 2 n| ≤
      C * (2 / (2 - a) + 2) * (D : ℝ) ^ (a - 2) := by
  have := abs_inv_zeta_sub_le (k := 2) le_rfl hC (by norm_num; linarith) hM hD
  simpa using this

/-- `k = 3`: `|1/ζ(3) − ∑_{n ≤ D} μ(n)/n³| ≤ C (3/(3−a) + 2) D^{a−3}` for `a ≤ 2`. -/
theorem abs_tail_three_le {C a : ℝ} (hC : 0 ≤ C) (ha2 : a ≤ 2)
    (hM : ∀ n : ℕ, |mert n| ≤ C * (n : ℝ) ^ a) {D : ℕ} (hD : 1 ≤ D) :
    |((riemannZeta 3).re)⁻¹ - ∑ n ∈ range (D + 1), f 3 n| ≤
      C * (3 / (3 - a) + 2) * (D : ℝ) ^ (a - 3) := by
  have := abs_inv_zeta_sub_le (k := 3) (by norm_num) hC (by norm_num; linarith) hM hD
  simpa using this

end PowerfulFC.ETI

end

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open PowerfulFC.BG1 (S)
open PowerfulFC.BG4 (E f)
open PowerfulFC.ETI

/-- `E^{z} ≤ 2^{-z} s^{z}` for `z ≤ 0`, `s/2 ≤ E`, `0 < s`. -/
lemma powerful_floor_rpow_le {s z : ℝ} (hs : 0 < s) {D : ℕ} (hD : s / 2 ≤ D) (hz : z ≤ 0) :
    (D : ℝ) ^ z ≤ s ^ z / (2 : ℝ) ^ z := by
  have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < s / 2) hD hz
  rwa [Real.div_rpow hs.le (by norm_num)] at h

theorem OMA.solution : OMA.R_PowerfulNumbersDensity_error_term_improvement_R1.H3 := by
  intro a C t ha0 ha hC ht ht6 hM
  obtain ⟨C', hC'0, hC'⟩ := PowerfulFC.BG4.abs_E_le
  set a3 := (riemannZeta (3 / 2)).re
  set b2 := (riemannZeta (2 / 3)).re
  set K3 := |a3| * (C * (3 / (3 - a) + 2)) / (2 : ℝ) ^ (a - 3)
  set K2 := |b2| * (C * (2 / (2 - a) + 2)) / (2 : ℝ) ^ (a - 2)
  have hK3 : 0 ≤ K3 := div_nonneg (mul_nonneg (abs_nonneg _)
    (mul_nonneg hC (by have : 0 < 3 - a := (by linarith); positivity))) (by positivity)
  have hK2 : 0 ≤ K2 := div_nonneg (mul_nonneg (abs_nonneg _)
    (mul_nonneg hC (by have : 0 < 2 - a := (by linarith); positivity))) (by positivity)
  refine ⟨7 * C' + K3 + K2, by positivity, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  set s := x ^ t with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow hx ht.le
  have hs0 : 0 < s := by linarith
  have hs6 : s ^ 6 ≤ x := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    exact Real.rpow_le_self_of_one_le hx (by norm_num; linarith)
  have hspow : ∀ z : ℝ, s ^ z = x ^ (z * t) := by
    intro z
    rw [hs, ← Real.rpow_mul hx0, mul_comm t z]
  set D := ⌊s⌋₊ with hD
  have hD1 : 1 ≤ D := Nat.le_floor (by exact_mod_cast hs1)
  have hDs : (D : ℝ) ≤ s := Nat.floor_le hs0.le
  have hsD : s < D + 1 := Nat.lt_floor_add_one s
  have hD1R : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hD0 : (0 : ℝ) < D := by linarith
  have hD2 : s / 2 ≤ D := by linarith
  set N := ⌊x⌋₊ with hN
  set L := ∑ d ∈ Icc 1 D, (μ d : ℝ) * S (N / d ^ 6)
  -- Step 2: the small-`d` sum, termwise
  set F : ℕ → ℝ := fun d => (μ d : ℝ) * (S ⌊x / (d : ℝ) ^ 6⌋₊ : ℝ) with hF
  have hF0 : F 0 = 0 := by simp [hF]
  have hLF : L = ∑ d ∈ range (D + 1), F d := by
    have h1 : L = ∑ d ∈ Icc 1 D, F d := by
      refine sum_congr rfl fun d _ => ?_
      simp only [hF, hN]
      congr 3
      rw [← Nat.floor_div_natCast]; push_cast; rfl
    have h2 : ∑ d ∈ range (D + 1), F d = ∑ d ∈ Icc 1 D, F d := by
      refine (sum_subset (fun d hd => ?_) fun d hd hd' => ?_).symm
      · simp only [mem_Icc] at hd; simp only [mem_range]; omega
      · simp only [mem_range] at hd; simp only [mem_Icc, not_and, not_le] at hd'
        have : d = 0 := by by_contra h; exact absurd (hd' (by omega)) (by omega)
        rw [this, hF0]
    rw [h1, h2]
  have hterm : ∀ d ∈ range (D + 1), F d =
      a3 * √x * f 3 d + b2 * x ^ ((1 : ℝ) / 3) * f 2 d + (μ d : ℝ) * E (x / (d : ℝ) ^ 6) := by
    intro d _
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [hF0]; simp [f]
    have hdR : (0 : ℝ) ≤ d := d.cast_nonneg
    simp only [hF, E, f]
    rw [PowerfulFC.BG4.sqrt_div_six x d hdR, PowerfulFC.BG4.cbrt_div_six hx0 d hdR]
    ring
  set P3 := ∑ n ∈ range (D + 1), f 3 n
  set P2 := ∑ n ∈ range (D + 1), f 2 n
  set I3 := ((riemannZeta 3).re)⁻¹
  set I2 := ((riemannZeta 2).re)⁻¹
  set ER := ∑ d ∈ range (D + 1), (μ d : ℝ) * E (x / (d : ℝ) ^ 6)
  have hA : PowerfulNumbersDensity.A = a3 * I3 := by rw [PowerfulNumbersDensity.A, div_eq_mul_inv]
  have hB : PowerfulNumbersDensity.B = b2 * I2 := by rw [PowerfulNumbersDensity.B, div_eq_mul_inv]
  have hdec : L - PowerfulNumbersDensity.A * x ^ ((1 : ℝ) / 2)
      - PowerfulNumbersDensity.B * x ^ ((1 : ℝ) / 3)
      = ER - a3 * √x * (I3 - P3)
        - b2 * x ^ ((1 : ℝ) / 3) * (I2 - P2) := by
    have hL' : L = a3 * √x * P3 + b2 * x ^ ((1 : ℝ) / 3) * P2 + ER := by
      rw [hLF, sum_congr rfl hterm, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]
    rw [hL', hA, hB, ← Real.sqrt_eq_rpow]
    ring
  have hER : |ER| ≤ 7 * C' * x ^ ((1 + t) / 7) := by
    have hER' : ER = ∑ i ∈ range D, (μ (i + 1) : ℝ) * E (x / ((i + 1 : ℕ) : ℝ) ^ 6) := by
      simp only [ER]; rw [sum_range_succ']; simp
    rw [hER']
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ i ∈ range D, |(μ (i + 1) : ℝ) * E (x / ((i + 1 : ℕ) : ℝ) ^ 6)|
        ≤ C' * x ^ ((1 : ℝ) / 7) * ((i + 1 : ℕ) : ℝ) ^ (-(6 / 7 : ℝ)) := by
      intro i hi
      have hdD : i + 1 ≤ D := by simp only [mem_range] at hi; omega
      have hdR : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i
      have hy : 1 ≤ x / ((i + 1 : ℕ) : ℝ) ^ 6 := by
        rw [le_div_iff₀ (by positivity), one_mul]
        have : ((i + 1 : ℕ) : ℝ) ≤ s := le_trans (by exact_mod_cast hdD) hDs
        exact (pow_le_pow_left₀ hdR.le this 6).trans hs6
      rw [abs_mul]
      have hmu : |(μ (i + 1) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      have hE := hC' _ hy
      rw [PowerfulFC.BG4.rpow_seven_div_six hx0 hdR] at hE
      calc |(μ (i + 1) : ℝ)| * |E (x / ((i + 1 : ℕ) : ℝ) ^ 6)|
          ≤ 1 * |E (x / ((i + 1 : ℕ) : ℝ) ^ 6)| := mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
        _ ≤ C' * (x ^ ((1 : ℝ) / 7) * ((i + 1 : ℕ) : ℝ) ^ (-(6 / 7 : ℝ))) := by rw [one_mul]; exact hE
        _ = _ := by ring
    refine (sum_le_sum hb).trans ?_
    rw [← mul_sum]
    have hS := PowerfulFC.BG4.sum_rpow_le D
    have hDs7 : (D : ℝ) ^ ((1 : ℝ) / 7) ≤ s ^ ((1 : ℝ) / 7) :=
      Real.rpow_le_rpow hD0.le hDs (by norm_num)
    have hss : x ^ ((1 : ℝ) / 7) * s ^ ((1 : ℝ) / 7) = x ^ ((1 + t) / 7) := by
      rw [hspow, ← Real.rpow_add hxpos]; congr 1; ring
    have hx7 : 0 ≤ x ^ ((1 : ℝ) / 7) := by positivity
    calc C' * x ^ ((1 : ℝ) / 7) * ∑ i ∈ range D, ((i + 1 : ℕ) : ℝ) ^ (-(6 / 7 : ℝ))
        ≤ C' * x ^ ((1 : ℝ) / 7) * (7 * s ^ ((1 : ℝ) / 7)) :=
          mul_le_mul_of_nonneg_left (hS.trans (by linarith)) (by positivity)
      _ = 7 * C' * (x ^ ((1 : ℝ) / 7) * s ^ ((1 : ℝ) / 7)) := by ring
      _ = 7 * C' * x ^ ((1 + t) / 7) := by rw [hss]
  -- Step 3: the two tails (R2)
  have h3 := abs_tail_three_le hC (by linarith) hM hD1
  have h2 := abs_tail_two_le hC (by linarith) hM hD1
  have hT3 : |a3 * √x * (I3 - P3)| ≤ K3 * x ^ ((1 : ℝ) / 2 + (a - 3) * t) := by
    have hE3 := powerful_floor_rpow_le hs0 hD2 (by linarith : a - 3 ≤ 0)
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg x), Real.rpow_add hxpos,
      ← hspow, ← Real.sqrt_eq_rpow]
    calc |a3| * √x * |I3 - P3| ≤ |a3| * √x * (C * (3 / (3 - a) + 2) * (D : ℝ) ^ (a - 3)) := by gcongr
      _ ≤ |a3| * √x * (C * (3 / (3 - a) + 2) * (s ^ (a - 3) / (2 : ℝ) ^ (a - 3))) := by
          gcongr
          exact mul_nonneg hC (by have : 0 < 3 - a := (by linarith); positivity)
      _ = K3 * (√x * s ^ (a - 3)) := by simp only [K3]; ring
  have hT2 : |b2 * x ^ ((1 : ℝ) / 3) * (I2 - P2)| ≤ K2 * x ^ ((1 : ℝ) / 3 + (a - 2) * t) := by
    have hE2 := powerful_floor_rpow_le hs0 hD2 (by linarith : a - 2 ≤ 0)
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ ((1 : ℝ) / 3)),
      Real.rpow_add hxpos, ← hspow]
    calc |b2| * x ^ ((1 : ℝ) / 3) * |I2 - P2|
        ≤ |b2| * x ^ ((1 : ℝ) / 3) * (C * (2 / (2 - a) + 2) * (D : ℝ) ^ (a - 2)) := by gcongr
      _ ≤ |b2| * x ^ ((1 : ℝ) / 3) * (C * (2 / (2 - a) + 2) * (s ^ (a - 2) / (2 : ℝ) ^ (a - 2))) := by
          gcongr
          exact mul_nonneg hC (by have : 0 < 2 - a := (by linarith); positivity)
      _ = K2 * (x ^ ((1 : ℝ) / 3) * s ^ (a - 2)) := by simp only [K2]; ring
  change |L - PowerfulNumbersDensity.A * x ^ ((1 : ℝ) / 2) -
    PowerfulNumbersDensity.B * x ^ ((1 : ℝ) / 3)| ≤ _
  rw [hdec]
  refine (abs_sub _ _).trans ?_
  refine (add_le_add (abs_sub ER (a3 * √x * (I3 - P3))) (le_refl |b2 * x ^ ((1 : ℝ) / 3) * (I2 - P2)|)).trans ?_
  have bound := add_le_add (add_le_add hER hT3) hT2
  apply bound.trans
  have e0 : 0 ≤ x ^ ((1 + t) / 7) := Real.rpow_nonneg hx0 _
  have e3 : 0 ≤ x ^ ((1 : ℝ) / 2 + (a - 3) * t) := Real.rpow_nonneg hx0 _
  have e2 : 0 ≤ x ^ ((1 : ℝ) / 3 + (a - 2) * t) := Real.rpow_nonneg hx0 _
  nlinarith only [mul_nonneg hK2 e0, mul_nonneg hK3 e0, mul_nonneg hK2 e3,
    mul_nonneg hK3 e2, mul_nonneg hC'0 e3, mul_nonneg hC'0 e2]
