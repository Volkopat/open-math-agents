import FormalConjectures.Millennium.RiemannHypothesis
import Mathlib.Analysis.Complex.JensenFormula

/-! A logarithmic circle-mean criterion for Dedekind zeta zeros.

Use circles of radius one half centered at one plus a rational imaginary part.
A zero strictly to the right of the critical line contributes a positive Jensen weight
throughout an open interval of heights. A rational window inside that interval rules out
arbitrarily small excess. Symmetry of the completed function treats the left half.

The first input also requires nonvanishing on the full line of centers, including the
regularized pole. The second input is the remaining analytic estimate. -/

-- Credit: @deepqntm


/- A zero inside a disk contributes a definite positive amount to the logarithmic circle mean. -/

namespace OMA.DedekindJensen
open Complex Set Metric MeromorphicOn Filter Real
open scoped Topology

/-- Each zero in the open disk contributes at least one copy of its Jensen weight.
Zeros on the boundary have weight zero. -/
theorem zero_weight_le_excess {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {c w : ℂ} {R : ℝ} (hR : 0 < R) (hc : F c ≠ 0) (hw : F w = 0) (hd : dist c w < R) :
    Real.log (R / dist c w) ≤ circleAverage (fun z => Real.log ‖F z‖) c R - Real.log ‖F c‖ := by
  classical
  have hA : AnalyticOnNhd ℂ F Set.univ := hF.differentiableOn.analyticOnNhd isOpen_univ
  have hball : AnalyticOnNhd ℂ F (closedBall c |R|) := hA.mono (Set.subset_univ _)
  have hcw : c ≠ w := fun he => hc (he ▸ hw)
  have hdist : 0 < dist c w := dist_pos.mpr hcw
  have hwball : w ∈ closedBall c |R| := by simpa [mem_closedBall, dist_comm, abs_of_pos hR] using hd.le
  let D := divisor F (closedBall c |R|)
  let W (z : ℂ) : ℝ := (D z : ℝ) * Real.log (R * ‖c - z‖⁻¹)
  have hfinite : (Function.support W).Finite :=
    (D.finiteSupport (isCompact_closedBall c |R|)).subset (by intro z hz h; exact hz (by simp [W, h]))
  have hnonneg (z : ℂ) : 0 ≤ W z := by
    by_cases hz : z ∈ closedBall c |R|
    · by_cases he : c = z
      · simp [W, he]
      · have hpos : 0 < ‖c - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
        have hle : ‖c - z‖ ≤ R := by simpa [mem_closedBall, abs_of_pos hR, dist_eq_norm'] using hz
        exact mul_nonneg (by exact_mod_cast hball.divisor_nonneg z)
          (Real.log_nonneg (by simpa only [← div_eq_mul_inv, one_le_div hpos] using hle))
    · simp [W, D, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]
  have horder : analyticOrderAt F w ≠ ⊤ := by
    apply hA.analyticOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ c) (Set.mem_univ w)
    simp [(hA c (Set.mem_univ c)).analyticOrderAt_eq_zero.mpr hc]
  have hm : 1 ≤ D w := by
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp horder
    have hn' : n ≠ 0 := by
      intro h
      apply ((hA w (Set.mem_univ w)).analyticOrderAt_ne_zero.mpr hw)
      rw [← hn, h]
      rfl
    have hn₁ : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn'
    change 1 ≤ divisor F (closedBall c |R|) w
    rw [hball.divisor_apply hwball, ← hn]
    change (1 : ℤ) ≤ (n : ℤ)
    exact_mod_cast hn₁
  rw [hball.circleAverage_log_norm hR.ne' hc, add_sub_cancel_right]
  calc
    Real.log (R / dist c w) ≤ W w := by
      dsimp only [W]
      rw [← dist_eq_norm, ← div_eq_mul_inv]
      exact le_mul_of_one_le_left (Real.log_nonneg ((one_le_div hdist).mpr hd.le)) (by exact_mod_cast hm)
    _ ≤ ∑ᶠ z, W z := single_le_finsum w hfinite hnonneg

end OMA.DedekindJensen

/- A right-half-strip zero gives a whole rational interval of centers where the Jensen
excess stays bounded below by a positive constant. -/

namespace OMA.DedekindJensen
open Complex Set Metric Filter
open scoped Topology

theorem zero_forces_window {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hc : ∀ t : ℝ, F (1 + I * t) ≠ 0) {w : ℂ}
    (hright : 1 / 2 < w.re) (hstrip : w.re < 1) (hw : F w = 0) :
    ∃ a b : ℚ, a < b ∧ ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, (a : ℝ) < t → t < (b : ℝ) →
      Real.log ‖F (1 + I * t)‖ + η ≤ Real.circleAverage (fun z => Real.log ‖F z‖) (1 + I * t) (1 / 2) := by
  let v (t : ℝ) : ℂ := 1 + I * t
  have he : v w.im - w = ((1 - w.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [v]
  have hd : dist (v w.im) w < 1 / 2 := by
    rw [dist_eq_norm, he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hstrip)]
    linarith
  obtain ⟨r, hdr, hr⟩ := exists_between hd
  have hr₀ : 0 < r := dist_nonneg.trans_lt hdr
  have hopen : IsOpen {t : ℝ | dist (v t) w < r} := isOpen_lt (by dsimp [v]; fun_prop) continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen w.im hdr
  obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (sub_lt_self w.im hε)
  obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn (lt_add_of_pos_right w.im hε)
  refine ⟨a, b, by exact_mod_cast ha₂.trans hb₁,
    Real.log ((1 / 2) / r), Real.log_pos ((one_lt_div hr₀).mpr hr), ?_⟩
  intro t ht₁ ht₂
  have hnear : dist (v t) w < r := hball (by
    change |t - w.im| < ε
    exact abs_lt.mpr ⟨by linarith, by linarith⟩)
  have hpos : 0 < dist (v t) w := dist_pos.mpr (fun e => hc t ((congrArg F e).trans hw))
  have hle : Real.log ((1 / 2) / r) ≤ Real.log ((1 / 2) / dist (v t) w) := by
    apply Real.log_le_log (div_pos (by norm_num) hr₀)
    exact div_le_div_of_nonneg_left (by norm_num) hpos hnear.le
  have hbound := zero_weight_le_excess hF (by norm_num : (0 : ℝ) < 1 / 2) (hc t) hw
    (lt_trans hnear hr)
  dsimp only [v] at hle
  linarith

end OMA.DedekindJensen

namespace OMA.R_ERH_extended_riemann_hypothesis_R3

open Complex Set Filter NumberField NumberField.InfinitePlace
open scoped Topology NumberField

/-- The pole-cleared completion is entire, symmetric and nonzero along the line
of absolute convergence. Its normalization relates it to the supplied continuation. -/
def H1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (Z : ℂ → ℂ), ERH.IsDedekindZeta K Z →
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ s, F (1 - s) = F s) ∧
      (∀ t : ℝ, F (1 + I * t) ≠ 0) ∧ ∀ s : ℂ, 0 < s.re → s ≠ 1 →
        F s = s * (s - 1) * (Complex.exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) *
          Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K) * Z s

/-- In each rational height window there are rational samples with arbitrarily small
Jensen excess for the Taylor series computed from the ideal-norm Dirichlet series at two. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    let G : ℂ → ℂ := fun s => s * (s - 1) * (Complex.exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) *
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K) * dedekindZeta K s
    let F : ℂ → ℂ := fun z => ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * iteratedDeriv n G 2 * (z - 2) ^ n
    ∀ a b : ℚ, a < b → ∀ ε : ℝ, 0 < ε →
      ∃ q : ℚ, a < q ∧ q < b ∧
        Real.circleAverage (fun z => Real.log ‖F z‖) (1 + I * (q : ℝ)) (1 / 2) <
          Real.log ‖F (1 + I * (q : ℝ))‖ + ε

/-- A number-field isomorphism preserves the count of integral ideals of each norm. -/
theorem dedekindZeta_eq_of_ringEquiv {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] (e : K ≃+* L) : dedekindZeta K = dedekindZeta L := by
  let r : 𝓞 K ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv e
  let i : Ideal (𝓞 K) ≃ Ideal (𝓞 L) := (Ideal.relIsoOfBijective r.toRingHom r.bijective).symm.toEquiv
  have hnorm (I : Ideal (𝓞 K)) : Ideal.absNorm I = Ideal.absNorm (i I) :=
    Nat.card_congr (Ideal.quotientEquiv I (i I) r rfl).toEquiv
  have hcard (n : ℕ) : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} =
      Nat.card {J : Ideal (𝓞 L) // Ideal.absNorm J = n} :=
    Nat.card_congr (i.subtypeEquiv fun I => by rw [hnorm I])
  funext z
  simp only [dedekindZeta, hcard]

theorem main : H1 → H2 → type_of% @ERH.extended_riemann_hypothesis := by
  intro hcompletion hmean K _ _ Z hZ s hp hs hz
  let f : K →ₐ[ℚ] ℂ := IsAlgClosed.lift (R := ℚ)
  let L := f.fieldRange
  let e : K ≃+* L := f.equivFieldRange.toRingEquiv
  let _ : NumberField L := NumberField.of_ringEquiv K L e
  have hL : ERH.IsDedekindZeta L Z :=
    ⟨hZ.1, fun z h => (hZ.2 z h).trans (congrFun (dedekindZeta_eq_of_ringEquiv e) z)⟩
  obtain ⟨F, hF, hreflect, hcenters, hvalues⟩ := hcompletion L Z hL
  let G (z : ℂ) := z * (z - 1) * (Complex.exp (z * (Real.log (discr L).natAbs / 2 : ℝ)) *
    Gammaℝ z ^ nrRealPlaces L * Gammaℂ z ^ nrComplexPlaces L) * dedekindZeta L z
  have hgerm : F =ᶠ[𝓝 (2 : ℂ)] G := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 1 < (2 : ℂ).re by norm_num)] with z hr
    dsimp only [G]
    rw [← hL.2 z hr]
    exact hvalues z (zero_lt_one.trans hr) (fun he => by simp [he] at hr)
  have hTaylor : (fun z : ℂ => ∑' n : ℕ, (n.factorial : ℂ)⁻¹ *
      iteratedDeriv n G 2 * (z - 2) ^ n) = F := by
    funext z
    simpa only [← fun n => hgerm.iteratedDeriv_eq n] using Complex.taylorSeries_eq_of_entire' (c := 2) (z := z) hF
  have hright (z : ℂ) (h₁ : 1 / 2 < z.re) (h₂ : z.re < 1) : F z ≠ 0 := by
    intro hzero
    obtain ⟨a, b, hab, η, hη, hgap⟩ := OMA.DedekindJensen.zero_forces_window hF hcenters h₁ h₂ hzero
    obtain ⟨q, haq, hqb, hsmall⟩ := hmean L a b hab η hη
    rw [show (fun z : ℂ => ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * iteratedDeriv n G 2 * (z - 2) ^ n) = F
      from hTaylor] at hsmall
    exact (hgap q (by exact_mod_cast haq) (by exact_mod_cast hqb)).not_gt hsmall
  have hzero : F s = 0 := by rw [hvalues s hp (fun he => by simp [he] at hs), hz, mul_zero]
  rcases lt_trichotomy s.re (1 / 2) with hl | he | hr
  · exact (hright (1 - s) (by simp; linarith) (by simpa using hp) ((hreflect s).trans hzero)).elim
  · exact he
  · exact (hright s hr hs hzero).elim

end OMA.R_ERH_extended_riemann_hypothesis_R3
