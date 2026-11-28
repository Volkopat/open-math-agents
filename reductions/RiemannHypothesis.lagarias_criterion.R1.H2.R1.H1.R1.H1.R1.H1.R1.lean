import OMAReductions.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H1_R1
import Mathlib

/-!
Landau's positivity principle and the logarithmic singularity at a rightmost
zeta zero give incompatible continuations of the Mellin transform of Nicolas's
tail J. The identity theorem on the positive real ray makes the contradiction
independent of the formulas used to construct either continuation.
Portions adapted from Jonas Whidden, Robin1984 (Apache-2.0),
e3697139babfe0f6cc7a76a08bf41a92aa7a2978, NicolasLandau and
NicolasLandauRightmostRay. The compact maximum uses Mathlib's closed zero set.
-/
namespace OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H1_R1_H1_R1
open Real Filter MeasureTheory Set
open scoped Topology

/-- Positivity of the shifted tail gives holomorphic continuation across every
point of the half-plane to the left of b. The integral fixes its initial germ. -/
def H1 : Prop :=
  let J : ℝ → ℝ := fun x : ℝ => ∫ t in Ioi x,
    (Chebyshev.psi t - t) * ((1 / log t + 1 / (log t)^2) / t^2)
  let M : ℂ → ℂ := fun z : ℂ => ∫ x in Ioi (3 : ℝ), (x : ℂ) ^ (z - 1) * (J x : ℂ)
  ∀ b : ℝ, 0 < b → b < 1 / 2 → (∀ᶠ x : ℝ in atTop, 0 ≤ J x + x ^ (-b)) →
    ∃ F : ℂ → ℂ, (∀ z : ℂ, z.re < b → AnalyticAt ℂ F z) ∧
      (∀ z : ℂ, z.re < 0 → F z = M z)

/-- A rightmost zero produces a continuation along the horizontal ray whose
norm diverges at the reflected zero. This is independent of any tail sign. -/
def H2 : Prop :=
  let J : ℝ → ℝ := fun x : ℝ => ∫ t in Ioi x,
    (Chebyshev.psi t - t) * ((1 / log t + 1 / (log t)^2) / t^2)
  let M : ℂ → ℂ := fun z : ℂ => ∫ x in Ioi (3 : ℝ), (x : ℂ) ^ (z - 1) * (J x : ℂ)
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re < 1 →
    (∀ v : ℝ, 0 < v → riemannZeta (ρ + (v : ℂ)) ≠ 0) →
    ∃ G : ℝ → ℂ, AnalyticOnNhd ℝ G (Ioi 0) ∧
      (∀ e : ℝ, 1 < e → G e = M (1 - ρ - (e : ℂ))) ∧
      Tendsto (fun e => ‖G e‖) (𝓝[>] 0) atTop

theorem riemannZeta_one_sub_eq_zero_of_nontrivial_zero
    {s : Complex} (hz : riemannZeta s = 0)
    (hNontrivial : Not (Exists fun n : Nat => s = -2 * (n + 1)))
    (hOne : Not (s = 1)) :
    riemannZeta (1 - s) = 0 := by
  have hsZero : Not (s = 0) := by
    intro hs
    subst s
    norm_num [riemannZeta_zero] at hz
  have hCompleted : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hsZero] at hz
    rcases div_eq_zero_iff.mp hz with hCompleted | hGammaFactor
    . exact hCompleted
    . change
        (Real.pi : Complex) ^ (-s / 2) * Complex.Gamma (s / 2) = 0 at hGammaFactor
      rcases mul_eq_zero.mp hGammaFactor with hPiPower | hGamma
      . have hPi : Not ((Real.pi : Complex) = 0) :=
          Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        exact (Complex.cpow_ne_zero_iff.mpr (Or.inl hPi) hPiPower).elim
      . choose m hm using (Complex.Gamma_eq_zero_iff (s / 2)).mp hGamma
        have hsEq : s = -2 * (m : Complex) := by
          calc
            s = 2 * (s / 2) := by ring
            _ = 2 * (-(m : Complex)) := by rw [hm]
            _ = -2 * (m : Complex) := by ring
        cases m with
        | zero => exact (hsZero (by simpa using hsEq)).elim
        | succ n =>
            exact (hNontrivial (Exists.intro n (by
              simpa [Nat.cast_add, Nat.cast_one] using hsEq))).elim
  have hMirrorCompleted : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact hCompleted
  have hMirrorNeZero : Not (1 - s = 0) :=
    sub_ne_zero.mpr (Ne.symm hOne)
  rw [riemannZeta_def_of_ne_zero hMirrorNeZero, hMirrorCompleted, zero_div]

/-- Failure of RH supplies a zeta zero strictly to the right of the critical
line and strictly inside the critical strip. -/
theorem exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis
    (hNotRH : Not RiemannHypothesis) :
    Exists fun rho : Complex =>
      And (riemannZeta rho = 0)
        (And ((1 / 2 : Real) < rho.re) (rho.re < 1)) := by
  unfold RiemannHypothesis at hNotRH
  push Not at hNotRH
  choose z hz hNontrivial hzOne hzOff using hNotRH
  have hNontrivialExists :
      Not (Exists fun n : Nat => z = -2 * (n + 1)) := by
    intro hExists
    choose n hn using hExists
    exact hNontrivial n hn
  have hzLt : z.re < 1 := by
    by_contra hNotLt
    exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hNotLt) hz
  have hMirrorZero : riemannZeta (1 - z) = 0 :=
    riemannZeta_one_sub_eq_zero_of_nontrivial_zero hz hNontrivialExists hzOne
  have hzPos : 0 < z.re := by
    by_contra hNotPos
    have hMirrorRe : 1 <= (1 - z).re := by
      change 1 <= 1 - z.re
      linarith
    exact riemannZeta_ne_zero_of_one_le_re hMirrorRe hMirrorZero
  by_cases hRight : (1 / 2 : Real) < z.re
  . exact Exists.intro z (And.intro hz (And.intro hRight hzLt))
  . have hzLeft : z.re < (1 / 2 : Real) :=
      lt_of_le_of_ne (le_of_not_gt hRight) hzOff
    refine Exists.intro (1 - z) (And.intro hMirrorZero (And.intro ?_ ?_))
    . change (1 / 2 : Real) < 1 - z.re
      linarith
    . change 1 - z.re < (1 : Real)
      linarith

/-- On a horizontal segment ending at real part one, the zero set is closed.
Its rightmost point has an entire zero-free ray to the right. -/
theorem rightmost_zero {z : ℂ} (hz : riemannZeta z = 0)
    (hh : 1 / 2 < z.re) (h1 : z.re < 1) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1 ∧
      ∀ v : ℝ, 0 < v → riemannZeta (ρ + (v : ℂ)) ≠ 0 := by
  let ray := fun t : ℝ => z + (t : ℂ)
  let S := Icc (0 : ℝ) (1 - z.re) ∩ ray ⁻¹' riemannZetaZeros
  have hc : Continuous ray := by dsimp [ray]; fun_prop
  have hs : IsCompact S := isCompact_Icc.inter_right (isClosed_riemannZetaZeros.preimage hc)
  have hmem : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_rfl, by linarith⟩, ?_⟩
    simpa [ray, mem_riemannZetaZeros] using hz
  obtain ⟨t, ht⟩ := hs.exists_isGreatest ⟨0, hmem⟩
  obtain ⟨⟨ht0, ht1⟩, hzt⟩ := ht.1
  have hzero : riemannZeta (ray t) = 0 := hzt
  have hr : (ray t).re = z.re + t := by simp [ray]
  have hlt : (ray t).re < 1 := by
    by_contra! hn
    exact riemannZeta_ne_zero_of_one_le_re hn hzero
  refine ⟨ray t, hzero, by linarith, hlt, ?_⟩
  intro v hv hshift
  have heq : ray (t + v) = ray t + (v : ℂ) := by simp [ray, add_assoc]
  have hupper : (ray t + (v : ℂ)).re < 1 := by
    by_contra! hn
    exact riemannZeta_ne_zero_of_one_le_re hn hshift
  rw [Complex.add_re, Complex.ofReal_re, hr] at hupper
  have hm : t + v ∈ S := by
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    change riemannZeta (ray (t + v)) = 0
    rwa [heq]
  have := ht.2 hm
  linarith

theorem main : H1 → H2 → OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H1_R1.H1 := by
  intro hLandau hPole hRH
  obtain ⟨z, hz, hh, hlt⟩ := exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hRH
  obtain ⟨ρ, hρ, hhalf, hone, hray⟩ := rightmost_zero hz hh hlt
  let b := ((1 - ρ.re) + 1 / 2) / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hbHalf : b < 1 / 2 := by dsimp [b]; linarith
  have hbρ : 1 - ρ.re < b := by dsimp [b]; linarith
  refine ⟨b, 1, hb, hbHalf, zero_lt_one, ?_⟩
  by_contra h
  have he := not_frequently.mp h
  have hp : ∀ᶠ x : ℝ in atTop, 0 ≤ (∫ t in Ioi x, (Chebyshev.psi t - t) *
        ((1 / log t + 1 / (log t)^2) / t^2)) + x ^ (-b) := by
    filter_upwards [he] with x hx
    rw [one_mul, not_le] at hx
    linarith
  obtain ⟨F, hF, hFM⟩ := hLandau b hb hbHalf hp
  obtain ⟨G, hG, hGM, hInf⟩ := hPole ρ hρ hhalf hone hray
  let s := fun e : ℝ => 1 - ρ - (e : ℂ)
  have hs : ∀ e : ℝ, AnalyticAt ℝ s e :=
    fun e => analyticAt_const.sub (Complex.ofRealCLM.analyticAt e)
  have hA (e : ℝ) (he : 0 ≤ e) : AnalyticAt ℝ (F ∘ s) e := by
    have hsre : (s e).re < b := by
      simp only [s, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
      linarith
    exact (hF _ hsre).restrictScalars.comp_of_eq (hs e) rfl
  have hAon : AnalyticOnNhd ℝ (F ∘ s) (Ioi 0) := fun e he => hA e (mem_Ioi.mp he).le
  have hstart : F ∘ s =ᶠ[𝓝 (2 : ℝ)] G := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2)] with e he
    have he' := mem_Ioi.mp he
    have hleft : (s e).re < 0 := by
      simp only [s, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
      linarith
    exact (hFM _ hleft).trans (hGM _ he').symm
  have hagree : EqOn (F ∘ s) G (Ioi 0) :=
    hAon.eqOn_of_preconnected_of_eventuallyEq hG
      (convex_Ioi (0 : ℝ)).isPreconnected (by norm_num) hstart
  have hfin : Tendsto (fun e => ‖G e‖) (𝓝[>] 0) (𝓝 ‖(F ∘ s) 0‖) := by
    apply ((hA 0 le_rfl).continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with e he
    exact congrArg norm (hagree he)
  exact not_tendsto_nhds_of_tendsto_atTop hInf _ hfin

end OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H1_R1_H1_R1
