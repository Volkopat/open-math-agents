import OMAReductions.R_RiemannHypothesis_beurling_nyman_criterion_R1
import Mathlib

/-!
# Module 1: Reduction of Beurling-Nyman forward direction to weighted L2(0, ∞) estimates

Inlines the verified reduction chain from `OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1.H1`
to unconstrained half-line `L²(0, ∞)` approximation by reciprocal-integer dilations, together with
the `(0, 1]` / `(1, ∞)` norm split and Cesaro-weighted Mobius tail convergence.
-/

namespace BN1
open MeasureTheory Set Filter RiemannHypothesis ArithmeticFunction
open scoped RealInnerProductSpace Topology ENNReal

lemma dense_Iic {μ : Measure ℝ} [IsFiniteMeasure μ] (V : Submodule ℝ (Lp ℝ 2 μ))
    (one : indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℝ) ∈
      V.topologicalClosure)
    (rays : ∀ t : ℝ, indicatorConstLp 2 measurableSet_Iic (measure_ne_top μ (Iic t)) (1 : ℝ) ∈
      V.topologicalClosure) :
    Dense (V : Set (Lp ℝ 2 μ)) := by
  have zero : Vᗮ = ⊥ := by
    apply bot_unique
    intro f fin
    have orth : f ∈ V.topologicalClosureᗮ := by rwa [Submodule.orthogonal_closure]
    have int : Integrable f μ := (Lp.memLp f).integrable (by norm_num)
    have whole := orth _ one
    rw [L2.inner_indicatorConstLp_one, Measure.restrict_univ] at whole
    have ray (t : ℝ) : ∫ x in Iic t, f x ∂μ = 0 := by
      rw [← L2.inner_indicatorConstLp_one measurableSet_Iic (measure_ne_top μ _) f]
      exact orth _ (rays t)
    have all (s : Set ℝ) (ms : MeasurableSet s) : ∫ x in s, f x ∂μ = 0 := by
      induction s, ms using
          MeasurableSpace.induction_on_inter (borel_eq_generateFrom_Iic (α := ℝ)) isPiSystem_Iic with
      | empty => simp
      | basic s h => obtain ⟨t, rfl⟩ := h; exact ray t
      | compl s ms ih =>
        have e := integral_add_compl ms int
        rw [ih, whole] at e
        simpa using e
      | iUnion f d m ih => rw [integral_iUnion m d int.integrableOn]; simp [ih]
    have he := int.ae_eq_zero_of_forall_setIntegral_eq_zero (fun s hs _ => all s hs)
    apply Lp.ext
    exact he.trans (Lp.coeFn_zero ℝ 2 μ).symm
  have htop : V.topologicalClosure = ⊤ := by
    rw [← V.orthogonal_orthogonal_eq_closure, zero, Submodule.bot_orthogonal_eq_top]
  exact dense_iff_closure_eq.mpr (by rw [← Submodule.topologicalClosure_coe, htop]; rfl)

lemma sums_subspace :
    ∃ V : Submodule ℝ (Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) 1))),
      (V : Set _) = { RiemannHypothesis.fractScalarInvSumL2 n c θ | (n) (c) (θ)
        (_hθ : ∀ ν, θ ν ∈ Set.Ioc 0 1) (_h : ∑ ν, c ν * θ ν = 0) } := by
  refine ⟨{ carrier := _
            zero_mem' := ?_
            add_mem' := ?_
            smul_mem' := ?_ }, rfl⟩
  · rintro f g ⟨n, c, t, ht, hc, rfl⟩ ⟨m, d, u, hu, hd, rfl⟩
    refine ⟨n + m, Fin.append c d, Fin.append t u, ?_, ?_, ?_⟩
    · intro i
      exact Fin.addCases (fun j => by simpa using ht j) (fun j => by simpa using hu j) i
    · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, hc, hd, add_zero]
    · simp [fractScalarInvSumL2, Fin.sum_univ_add]
  · refine ⟨0, Fin.elim0, Fin.elim0, (fun i => Fin.elim0 i), by simp, ?_⟩
    simp [fractScalarInvSumL2]
  · rintro k f ⟨n, c, t, ht, hc, rfl⟩
    refine ⟨n, fun i => k * c i, t, ht, ?_, ?_⟩
    · simp only [mul_assoc, ← Finset.mul_sum, hc, mul_zero]
    · simp [fractScalarInvSumL2, Finset.smul_sum, mul_smul]

lemma coe_fractSum (n : ℕ) (c θ : Fin n → ℝ) :
    (RiemannHypothesis.fractScalarInvSumL2 n c θ : ℝ → ℝ) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun x => ∑ ν, c ν * Int.fract (θ ν / x) := by
  unfold RiemannHypothesis.fractScalarInvSumL2
  have key : ∀ s : Finset (Fin n),
      ((∑ ν ∈ s, c ν • (RiemannHypothesis.fractScalarInv_memLp2 (θ ν)).toLp _ :
        Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) 1))) : ℝ → ℝ)
        =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fun x => ∑ ν ∈ s, c ν * Int.fract (θ ν / x) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Ioc (0 : ℝ) 1))] with x hx
      rw [hx]
      simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine (Lp.coeFn_add _ _).trans ?_
      have h1 := Lp.coeFn_smul (c a) ((RiemannHypothesis.fractScalarInv_memLp2 (θ a)).toLp _)
      have h2 := (RiemannHypothesis.fractScalarInv_memLp2 (θ a)).coeFn_toLp
      filter_upwards [h1, h2, ih] with x hx1 hx2 hx3
      rw [Pi.add_apply, hx1, Pi.smul_apply, hx2, hx3, Finset.sum_insert ha, smul_eq_mul,
        RiemannHypothesis.fractScalarInv]
  exact key Finset.univ

lemma ind_coe (s : Set ℝ) (hs : MeasurableSet s) :
    (indicatorConstLp 2 hs (measure_ne_top (volume.restrict (Ioc (0 : ℝ) 1)) s) (1 : ℝ) : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] s.indicator (fun _ => (1 : ℝ)) :=
  indicatorConstLp_coeFn

lemma norm_sq_eq_integral (F : Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) 1))) (φ : ℝ → ℝ)
    (h : (F : ℝ → ℝ) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] φ) :
    ‖F‖ ^ 2 = ∫ x in Ioc (0 : ℝ) 1, φ x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hx]

lemma dilation_sq (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) (c θ : Fin n → ℝ)
    (hθ : ∀ ν, θ ν ∈ Ioc (0 : ℝ) 1) (hsum : ∑ ν, c ν * θ ν = 0) :
    ‖RiemannHypothesis.fractScalarInvSumL2 n c (fun ν => a * θ ν) -
        indicatorConstLp 2 measurableSet_Iic
          (measure_ne_top (volume.restrict (Ioc (0 : ℝ) 1)) (Iic a)) (1 : ℝ)‖ ^ 2 =
      a * ‖RiemannHypothesis.fractScalarInvSumL2 n c θ -
        indicatorConstLp 2 MeasurableSet.univ
          (measure_ne_top (volume.restrict (Ioc (0 : ℝ) 1)) univ) (1 : ℝ)‖ ^ 2 := by
  let ψ : ℝ → ℝ := fun y => ∑ ν, c ν * Int.fract (θ ν / y) - 1
  let φ : ℝ → ℝ := fun x =>
    ∑ ν, c ν * Int.fract (a * θ ν / x) - (Iic a).indicator (fun _ => (1 : ℝ)) x
  have hL := norm_sq_eq_integral
    (RiemannHypothesis.fractScalarInvSumL2 n c (fun ν => a * θ ν) -
        indicatorConstLp 2 measurableSet_Iic
          (measure_ne_top (volume.restrict (Ioc (0 : ℝ) 1)) (Iic a)) (1 : ℝ)) φ (by
    filter_upwards [Lp.coeFn_sub (RiemannHypothesis.fractScalarInvSumL2 n c (fun ν => a * θ ν))
        (indicatorConstLp 2 measurableSet_Iic
          (measure_ne_top (volume.restrict (Ioc (0 : ℝ) 1)) (Iic a)) (1 : ℝ)),
      coe_fractSum n c (fun ν => a * θ ν), ind_coe (Iic a) measurableSet_Iic] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3])
  have hR := norm_sq_eq_integral
    (RiemannHypothesis.fractScalarInvSumL2 n c θ -
        indicatorConstLp 2 MeasurableSet.univ
          (measure_ne_top (volume.restrict (Ioc (0 : ℝ) 1)) univ) (1 : ℝ)) ψ (by
    filter_upwards [Lp.coeFn_sub (RiemannHypothesis.fractScalarInvSumL2 n c θ)
        (indicatorConstLp 2 MeasurableSet.univ
          (measure_ne_top (volume.restrict (Ioc (0 : ℝ) 1)) univ) (1 : ℝ)),
      coe_fractSum n c θ, ind_coe univ MeasurableSet.univ] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, Set.indicator_univ])
  rw [hL, hR]
  have hzero : ∀ x ∈ Ioc (0 : ℝ) 1 \ Ioc 0 a, φ x ^ 2 = 0 := by
    intro x hx
    obtain ⟨⟨hx0, _⟩, hxa⟩ := hx
    have hxa' : a < x := by
      by_contra h
      exact hxa ⟨hx0, not_lt.mp h⟩
    have hind : (Iic a).indicator (fun _ => (1 : ℝ)) x = 0 :=
      Set.indicator_of_notMem (fun h => absurd (Set.mem_Iic.mp h) (not_le.mpr hxa')) _
    have hfr : ∀ ν, Int.fract (a * θ ν / x) = a * θ ν / x := by
      intro ν
      rw [Int.fract_eq_self]
      have h := hθ ν
      have hpos : 0 < a * θ ν := mul_pos ha0 h.1
      constructor
      · positivity
      · rw [div_lt_one hx0]
        nlinarith [h.1, h.2]
    have hsum' : ∑ ν, c ν * (a * θ ν / x) = (a / x) * ∑ ν, c ν * θ ν := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      ring
    show (∑ ν, c ν * Int.fract (a * θ ν / x) - (Iic a).indicator (fun _ => (1 : ℝ)) x) ^ 2 = 0
    rw [hind, sub_zero]
    simp only [hfr]
    rw [hsum', hsum]
    ring
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
    (Ioc_subset_Ioc_right ha1.le) hzero]
  have hcongr : EqOn (fun x => φ x ^ 2) (fun x => ψ (x / a) ^ 2) (Ioc (0 : ℝ) a) := by
    intro x hx
    have hind : (Iic a).indicator (fun _ => (1 : ℝ)) x = 1 :=
      Set.indicator_of_mem (Set.mem_Iic.mpr hx.2) _
    have hfr : ∀ ν, Int.fract (a * θ ν / x) = Int.fract (θ ν / (x / a)) := by
      intro ν
      rw [div_div_eq_mul_div]
      ring_nf
    show (∑ ν, c ν * Int.fract (a * θ ν / x) - (Iic a).indicator (fun _ => (1 : ℝ)) x) ^ 2 =
      (∑ ν, c ν * Int.fract (θ ν / (x / a)) - 1) ^ 2
    rw [hind]
    simp only [hfr]
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr]
  rw [← intervalIntegral.integral_of_le ha0.le, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_div (fun y => ψ y ^ 2) ha0.ne', zero_div, div_self ha0.ne',
    smul_eq_mul]

lemma dilate_one_to_rays :
    let μ := volume.restrict (Ioc (0 : ℝ) 1)
    let S := { RiemannHypothesis.fractScalarInvSumL2 n c θ | (n) (c) (θ)
      (_hθ : ∀ ν, θ ν ∈ Set.Ioc 0 1) (_h : ∑ ν, c ν * θ ν = 0) }
    indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℝ) ∈ closure S →
    ∀ a : ℝ, indicatorConstLp 2 measurableSet_Iic (measure_ne_top μ (Iic a)) (1 : ℝ) ∈ closure S := by
  dsimp only
  intro hone a
  have hae : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), x ∈ Ioc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  rcases le_or_gt a 0 with ha0 | ha0
  · have hz : indicatorConstLp 2 measurableSet_Iic
        (measure_ne_top (volume.restrict (Ioc (0 : ℝ) 1)) (Iic a)) (1 : ℝ) = 0 := by
      apply Lp.ext
      filter_upwards [ind_coe (Iic a) measurableSet_Iic,
        Lp.coeFn_zero ℝ 2 (volume.restrict (Ioc (0 : ℝ) 1)), hae] with x h1 h2 hx
      rw [h1, h2, Set.indicator_of_notMem]
      · rfl
      · intro hxa
        exact absurd (lt_of_le_of_lt (Set.mem_Iic.mp hxa) (lt_of_le_of_lt ha0 hx.1)) (lt_irrefl x)
    rw [hz]
    apply subset_closure
    refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp, ?_⟩
    simp [RiemannHypothesis.fractScalarInvSumL2]
  rcases le_or_gt 1 a with ha1 | ha1
  · have he : indicatorConstLp 2 measurableSet_Iic
        (measure_ne_top (volume.restrict (Ioc (0 : ℝ) 1)) (Iic a)) (1 : ℝ) =
        indicatorConstLp 2 MeasurableSet.univ
          (measure_ne_top (volume.restrict (Ioc (0 : ℝ) 1)) univ) (1 : ℝ) := by
      apply Lp.ext
      filter_upwards [ind_coe (Iic a) measurableSet_Iic,
        ind_coe univ MeasurableSet.univ, hae] with x h1 h2 hx
      rw [h1, h2, Set.indicator_of_mem (Set.mem_Iic.mpr (le_trans hx.2 ha1)),
        Set.indicator_of_mem (Set.mem_univ x)]
    rw [he]
    exact hone
  rw [Metric.mem_closure_iff] at hone ⊢
  intro ε hε
  obtain ⟨b, ⟨n, c, θ, hθ, hsum, rfl⟩, hb⟩ := hone ε hε
  refine ⟨RiemannHypothesis.fractScalarInvSumL2 n c (fun ν => a * θ ν),
    ⟨n, c, fun ν => a * θ ν, ?_, ?_, rfl⟩, ?_⟩
  · intro ν
    have h := hθ ν
    refine ⟨mul_pos ha0 h.1, ?_⟩
    nlinarith [h.1, h.2]
  · have : ∑ ν, c ν * (a * θ ν) = a * ∑ ν, c ν * θ ν := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      ring
    rw [this, hsum, mul_zero]
  · have key := dilation_sq a ha0 ha1 n c θ hθ hsum
    rw [dist_eq_norm, norm_sub_rev] at hb ⊢
    set X := ‖RiemannHypothesis.fractScalarInvSumL2 n c (fun ν => a * θ ν) -
        indicatorConstLp 2 measurableSet_Iic
          (measure_ne_top (volume.restrict (Ioc (0 : ℝ) 1)) (Iic a)) (1 : ℝ)‖
    set Y := ‖RiemannHypothesis.fractScalarInvSumL2 n c θ -
        indicatorConstLp 2 MeasurableSet.univ
          (measure_ne_top (volume.restrict (Ioc (0 : ℝ) 1)) univ) (1 : ℝ)‖
    have hX0 : 0 ≤ X := norm_nonneg _
    have hY0 : 0 ≤ Y := norm_nonneg _
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [mul_le_mul hcon hcon hε.le hX0, mul_lt_mul'' hb hb hY0 hY0]

lemma halfline_controls (n : ℕ) (c : Fin n → ℝ) :
    let θ := fun i : Fin n => 1 / ((i.val : ℝ) + 1)
    let μ := volume.restrict (Ioc (0 : ℝ) 1)
    let one := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℝ)
    let E := eLpNorm (fun x : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x -
      ∑ i, c i * fractScalarInv (θ i) x) 2 (volume.restrict (Ioi 0))
    E ≠ ⊤ → dist one (fractScalarInvSumL2 n c θ) + |∑ i, c i * θ i| ≤ 3 * E.toReal := by
  dsimp only
  let θ (i : Fin n) : ℝ := 1 / ((i.val : ℝ) + 1)
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let ν := volume.restrict (Ioc (1 : ℝ) 2)
  let ρ := volume.restrict (Ioi (0 : ℝ))
  let one := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℝ)
  let f (x : ℝ) := ∑ i, c i * fractScalarInv (θ i) x
  let g (x : ℝ) := (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x - f x
  let y := fractScalarInvSumL2 n c θ
  let m := ∑ i, c i * θ i
  let E := eLpNorm g 2 ρ
  change E ≠ ⊤ → dist one y + |m| ≤ 3 * E.toReal
  intro hE
  have μle : μ ≤ ρ := Measure.restrict_mono_set volume (fun _ hx => hx.1)
  have νle : ν ≤ ρ := Measure.restrict_mono_set volume (fun _ hx => zero_lt_one.trans hx.1)
  have hparts : ∀ᵐ x ∂μ, ∀ i : Fin n,
      (c i • (fractScalarInv_memLp2 (θ i)).toLp (fractScalarInv (θ i))) x =
        c i * fractScalarInv (θ i) x := by
    apply ae_all_iff.2
    intro i
    filter_upwards [Lp.coeFn_smul (c i) ((fractScalarInv_memLp2 (θ i)).toLp (fractScalarInv (θ i))),
      (fractScalarInv_memLp2 (θ i)).coeFn_toLp] with x hsmul ht
    rw [hsmul]
    change c i * (fractScalarInv_memLp2 (θ i)).toLp (fractScalarInv (θ i)) x =
      c i * fractScalarInv (θ i) x
    rw [ht]
  have hy : (y : ℝ → ℝ) =ᵐ[μ] f := by
    unfold y fractScalarInvSumL2
    apply (Lp.coeFn_fun_finsetSum Finset.univ _).trans
    filter_upwards [hparts] with x hx
    exact Finset.sum_congr rfl (fun i _ => hx i)
  have hone : (one : ℝ → ℝ) =ᵐ[μ] (Ioc (0 : ℝ) 1).indicator (fun _ => 1) := by
    have h := indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := measure_ne_top μ univ) (c := (1 : ℝ))
    filter_upwards [h, ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx hx'
    simpa [one, indicator_of_mem hx'] using hx
  have hlocal : dist one y ≤ E.toReal := by
    rw [Lp.dist_edist, Lp.edist_def, eLpNorm_congr_ae (hone.sub hy)]
    exact ENNReal.toReal_mono hE (eLpNorm_mono_measure g μle)
  have htail : ∀ x ∈ Ioc (1 : ℝ) 2, g x = -(m / x) := by
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans hx.1
    have hf (i : Fin n) : fractScalarInv (θ i) x = θ i / x := by
      apply Int.fract_eq_self.mpr
      have ht0 : 0 ≤ θ i := by dsimp [θ]; positivity
      have ht1 : θ i ≤ 1 := by
        apply (div_le_one (by positivity : 0 < (i.val : ℝ) + 1)).2
        linarith [Nat.cast_nonneg (α := ℝ) i.val]
      exact ⟨div_nonneg ht0 hx0.le, (div_lt_one hx0).2 (ht1.trans_lt hx.1)⟩
    have hout : x ∉ Ioc (0 : ℝ) 1 := fun h => hx.1.not_ge h.2
    simp [g, f, m, indicator_of_notMem hout, hf, ← mul_div_assoc, ← Finset.sum_div]
  have hab : eLpNorm (fun _ : ℝ => |m| / 2) 2 ν ≤ E := by
    refine (eLpNorm_mono_ae (f := fun _ : ℝ => |m| / 2) (g := g) ?_).trans
      (eLpNorm_mono_measure g νle)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx.1
    have hmnonneg : 0 ≤ |m| / 2 := by positivity
    rw [Real.norm_of_nonneg hmnonneg, htail x hx, norm_neg,
      Real.norm_eq_abs, abs_div, abs_of_pos hx0]
    exact div_le_div_of_nonneg_left (abs_nonneg m) hx0 hx.2
  have hv : ν univ = 1 := by norm_num [ν, Measure.restrict_apply_univ, Real.volume_Ioc]
  rw [eLpNorm_const' _ (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by simp : (2 : ℝ≥0∞) ≠ ⊤), hv, ENNReal.one_rpow, mul_one,
    Real.enorm_eq_ofReal (show 0 ≤ |m| / 2 by positivity)] at hab
  have hreal := ENNReal.toReal_mono hE hab
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ |m| / 2)] at hreal
  linarith

theorem reduce_to_halfline
    (approx : RiemannHypothesis → ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ c : Fin n → ℝ,
      eLpNorm (fun x : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x +
        ∑ i, c i * fractScalarInv (1 / ((i.val : ℝ) + 1)) x) 2 (volume.restrict (Ioi 0)) <
          ENNReal.ofReal ε) :
    OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1.H1 := by
  intro rh
  have one_mem :
      indicatorConstLp 2 MeasurableSet.univ
        (measure_ne_top (volume.restrict (Ioc (0 : ℝ) 1)) univ) (1 : ℝ) ∈
      closure { RiemannHypothesis.fractScalarInvSumL2 n c θ | (n) (c) (θ)
        (_hθ : ∀ ν, θ ν ∈ Set.Ioc 0 1) (_h : ∑ ν, c ν * θ ν = 0) } := by
    apply Metric.mem_closure_iff.mpr
    intro ε epos
    let μ := volume.restrict (Ioc (0 : ℝ) 1)
    let one := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℝ)
    let g := (fractScalarInv_memLp2 1).toLp _
    let δ := ε / (4 * (1 + ‖g‖))
    have dp : 0 < δ := div_pos epos (by positivity)
    obtain ⟨n, c', hc'⟩ := approx rh δ dp
    let c : Fin n → ℝ := fun i => -c' i
    have hc : eLpNorm (fun x : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x -
        ∑ i, c i * fractScalarInv (1 / ((i.val : ℝ) + 1)) x) 2 (volume.restrict (Ioi 0)) <
        ENNReal.ofReal δ := by
      convert hc' using 2
      ext x
      simp [c, Finset.sum_neg_distrib, sub_neg_eq_add]
    let θ := fun i : Fin n => 1 / ((i.val : ℝ) + 1)
    let y := fractScalarInvSumL2 n c θ
    let m := ∑ i, c i * θ i
    let E := eLpNorm (fun x : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x -
      ∑ i, c i * fractScalarInv (θ i) x) 2 (volume.restrict (Ioi 0))
    change E < ENNReal.ofReal δ at hc
    have fin : E ≠ ⊤ := (hc.trans_le le_top).ne
    have hδ : E.toReal < δ := by
      simpa [ENNReal.toReal_ofReal dp.le] using
        (ENNReal.toReal_lt_toReal fin ENNReal.ofReal_ne_top).mpr hc
    have bound : dist one y + |m| ≤ 3 * E.toReal := halfline_controls n c fin
    let cs : Fin (n + 1) → ℝ := Fin.cons (-m) c
    let ts : Fin (n + 1) → ℝ := Fin.cons 1 θ
    refine ⟨fractScalarInvSumL2 (n + 1) cs ts, ⟨n + 1, cs, ts, ?_, ?_, rfl⟩, ?_⟩
    · intro i
      refine Fin.cases (by simp [ts]) (fun j => ?_) i
      change 0 < 1 / ((j.val : ℝ) + 1) ∧ 1 / ((j.val : ℝ) + 1) ≤ 1
      constructor
      · positivity
      · apply (div_le_one (by positivity)).mpr
        linarith [Nat.cast_nonneg (α := ℝ) j.val]
    · simp [cs, ts, Fin.sum_univ_succ, m]
    · have ident : fractScalarInvSumL2 (n + 1) cs ts = y + (-m) • g := by
        simp [fractScalarInvSumL2, cs, ts, Fin.sum_univ_succ, y, g]; abel
      change dist one (fractScalarInvSumL2 (n + 1) cs ts) < ε
      rw [ident]
      have tri := dist_triangle one y (y + (-m) • g)
      have dd : dist y (y + (-m) • g) = |m| * ‖g‖ := by simp [dist_eq_norm, norm_smul]
      rw [dd] at tri
      have hb : dist one y + |m| < 3 * δ := by linarith
      have hp := mul_lt_mul_of_pos_right hb (show 0 < 1 + ‖g‖ by positivity)
      have de : δ * (4 * (1 + ‖g‖)) = ε := by
        dsimp [δ]; exact div_mul_cancel₀ _ (by positivity)
      nlinarith [mul_nonneg (dist_nonneg : 0 ≤ dist one y) (norm_nonneg g), abs_nonneg m,
        mul_pos dp (show 0 < 1 + ‖g‖ by positivity)]
  have rays := dilate_one_to_rays one_mem
  obtain ⟨V, eq⟩ := sums_subspace
  rw [← eq] at one_mem rays ⊢
  exact dense_Iic V one_mem rays

/-- Split the `L²(Ioi 0)` norm into `Ioc 0 1` and `Ioi 1`. -/
lemma splitNorm_one (f : ℝ → ℝ) :
    eLpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) ≤
      eLpNorm f 2 (volume.restrict (Ioc (0 : ℝ) 1)) +
      eLpNorm f 2 (volume.restrict (Ioi (1 : ℝ))) := by
  have hdis : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
    Set.disjoint_left.mpr fun _ h k => (not_lt_of_ge h.2) k
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, Measure.restrict_union hdis measurableSet_Ioi]
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), lintegral_add_measure]
  apply ENNReal.rpow_add_le_add_rpow <;> norm_num

/-- On `(0, 1]`, `1 ≤ x ^ (-ε)` for `ε > 0`, so the weighted `L²(0, ∞)` norm controls `L²(0, 1]`. -/
lemma weight_Ioc_le (ε : ℝ) (hε : 0 < ε) (g : ℝ → ℝ) :
    eLpNorm g 2 (volume.restrict (Ioc (0 : ℝ) 1)) ≤
      eLpNorm (fun x => x ^ (-ε) * g x) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  refine (eLpNorm_mono_ae ?_).trans
    (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume (fun _ hx => hx.1)))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have h1 : (1 : ℝ) ≤ x ^ (-ε) := by
    rw [Real.rpow_neg hx.1.le]
    exact one_le_inv₀ (Real.rpow_pos_of_pos hx.1 ε) |>.mpr
      (Real.rpow_le_one hx.1.le hx.2 hε.le)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
  exact le_mul_of_one_le_left (abs_nonneg _) h1

/-- Exact `L²(1, ∞)` norm of `χ + ∑ c_i ρ_{1/(i+1)}`. -/
lemma tail_L2_le (n : ℕ) (c : Fin n → ℝ) :
    eLpNorm (fun x : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x +
      ∑ i, c i * fractScalarInv (1 / ((i.val : ℝ) + 1)) x) 2 (volume.restrict (Ioi (1 : ℝ))) ≤
      ENNReal.ofReal |∑ i, c i / ((i.val : ℝ) + 1)| := by
  set m : ℝ := ∑ i, c i / ((i.val : ℝ) + 1)
  have hcongr : (fun x : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x +
      ∑ i, c i * fractScalarInv (1 / ((i.val : ℝ) + 1)) x)
      =ᵐ[volume.restrict (Ioi (1 : ℝ))] fun x : ℝ => m * x⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx1
    have hout : x ∉ Ioc (0 : ℝ) 1 := fun h => hx1.not_ge h.2
    rw [Set.indicator_of_notMem hout, zero_add]
    have hfr : ∀ i : Fin n, fractScalarInv (1 / ((i.val : ℝ) + 1)) x =
        (1 / ((i.val : ℝ) + 1)) / x := fun i => by
      apply Int.fract_eq_self.mpr
      have hpos : (0 : ℝ) < (i.val : ℝ) + 1 := by positivity
      have hle : 1 / ((i.val : ℝ) + 1) ≤ 1 := (div_le_one hpos).mpr (by linarith [Nat.cast_nonneg (α := ℝ) i.val])
      exact ⟨by positivity, (div_lt_one hx0).mpr (hle.trans_lt hx1)⟩
    simp_rw [hfr]
    rw [show m * x⁻¹ = ∑ i, c i * (1 / ((i.val : ℝ) + 1) / x) by
      dsimp [m]; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; ring]
  rw [eLpNorm_congr_ae hcongr]
  change eLpNorm (m • fun x : ℝ => x⁻¹) 2 (volume.restrict (Ioi (1 : ℝ))) ≤ ENNReal.ofReal |m|
  rw [eLpNorm_const_smul]
  have hinv_norm : eLpNorm (fun x : ℝ => x⁻¹) 2 (volume.restrict (Ioi (1 : ℝ))) = 1 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp)]
    have hsq : ∫⁻ x in Ioi (1 : ℝ), ‖x⁻¹‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ)) := by
      rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) zero_lt_one)]
      · refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        have hx0 : 0 < x := zero_lt_one.trans hx
        rw [Real.enorm_eq_ofReal (inv_nonneg.mpr hx0.le), ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hx0)]
        congr 1
        rw [Real.rpow_neg hx0.le, Real.inv_rpow hx0.le]
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact Real.rpow_nonneg (zero_lt_one.trans hx).le _
    have hint : ∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) = 1 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
      norm_num
    have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
    rw [h2, hsq, hint]
    simp
  rw [hinv_norm, mul_one, Real.enorm_eq_ofReal_abs]

/-- `1 / ζ(1 + d) → 0` as `d ↓ 0`. -/
lemma reciprocal_zeta_tendsto_zero :
    Tendsto (fun d : ℝ => (riemannZeta (1 + (d : ℂ)))⁻¹.re) (𝓝[>] 0) (𝓝 0) := by
  have hd : Tendsto (fun d : ℝ => (d : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
  have hs : Tendsto (fun d : ℝ => 1 + (d : ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using (tendsto_const_nhds (x := (1 : ℂ))).add hd
    · filter_upwards [self_mem_nhdsWithin] with d (hd : 0 < d)
      simpa using hd.ne'
  have hr := riemannZeta_residue_one.comp hs
  have hr' : Tendsto (fun d : ℝ => (d : ℂ) * riemannZeta (1 + (d : ℂ))) (𝓝[>] 0) (𝓝 1) := by
    simpa [Function.comp_def] using hr
  have hquot := hd.div hr' one_ne_zero
  have hi : Tendsto (fun d : ℝ => (riemannZeta (1 + (d : ℂ)))⁻¹) (𝓝[>] 0) (𝓝 0) := by
    apply (show Tendsto _ _ (𝓝 (0 : ℂ)) from (by simpa using hquot)).congr'
    filter_upwards [self_mem_nhdsWithin] with d (hd : 0 < d)
    simp [div_mul_eq_div_div, div_self (by exact_mod_cast hd.ne' : (d : ℂ) ≠ 0)]
  simpa [Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp hi

/-- Cesaro/Riesz-weighted partial sums of an absolutely summable series converge to the total sum. -/
lemma tendsto_riesz_partial_sum {a : ℕ → ℝ} (ha : Summable (fun n => |a n|)) :
    Tendsto (fun N : ℕ => ∑ i : Fin N, a i.val * (1 - ((i.val : ℝ) + 1) / (N : ℝ)))
      atTop (𝓝 (∑' n, a n)) := by
  have ha_sum : Summable a := ha.of_abs
  have hpartial : Tendsto (fun N : ℕ => ∑ i : Fin N, a i.val) atTop (𝓝 (∑' n, a n)) := by
    simpa [Fin.sum_univ_eq_sum_range] using ha_sum.hasSum.tendsto_sum_nat
  have hdiff : Tendsto (fun N : ℕ =>
      (∑ i : Fin N, a i.val * (1 - ((i.val : ℝ) + 1) / (N : ℝ))) - ∑ i : Fin N, a i.val)
      atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have htail : Tendsto (fun M : ℕ => ∑' n : ℕ, |a (n + M)|) atTop (𝓝 0) := by
      have h1 := ha.hasSum.tendsto_sum_nat
      have h2 : (fun M : ℕ => ∑' n : ℕ, |a (n + M)|) =
          fun M : ℕ => (∑' n, |a n|) - ∑ n ∈ Finset.range M, |a n| := by
        ext M
        rw [← Summable.sum_add_tsum_nat_add M ha]
        ring
      rw [h2]
      simpa using (tendsto_const_nhds (x := ∑' n, |a n|)).sub h1
    obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp htail (ε / 2) (half_pos hε))
    have hMbound : ∑' n : ℕ, |a (n + M)| < ε / 2 := by
      have := hM M le_rfl
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun _ => abs_nonneg _)] at this
      exact this
    let S_head : ℝ := ∑ n ∈ Finset.range M, ((n : ℝ) + 1) * |a n|
    have hS_nn : 0 ≤ S_head := Finset.sum_nonneg fun n _ => by positivity
    obtain ⟨N0, hN0⟩ := exists_nat_gt (2 * S_head / ε)
    refine ⟨max (M + 1) (N0 + 1), fun N hN => ?_⟩
    have hMN : M < N := lt_of_lt_of_le (Nat.lt_succ_self M) (le_trans (le_max_left _ _) hN)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hMN)
    have hN_gt : 2 * S_head / ε < (N : ℝ) :=
      lt_of_lt_of_le hN0 (by exact_mod_cast (le_trans (Nat.le_succ N0) (le_trans (le_max_right _ _) hN)))
    rw [Real.dist_eq, sub_zero]
    have hrew : (∑ i : Fin N, a i.val * (1 - ((i.val : ℝ) + 1) / (N : ℝ))) - ∑ i : Fin N, a i.val =
        -(∑ n ∈ Finset.range N, a n * (((n : ℝ) + 1) / (N : ℝ))) := by
      rw [Fin.sum_univ_eq_sum_range (fun k => a k * (1 - ((k : ℝ) + 1) / (N : ℝ))),
        Fin.sum_univ_eq_sum_range (fun k => a k),
        ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_; ring
    rw [hrew, abs_neg]
    have hsplit : ∑ n ∈ Finset.range N, a n * (((n : ℝ) + 1) / (N : ℝ)) =
        (∑ n ∈ Finset.range M, a n * (((n : ℝ) + 1) / (N : ℝ))) +
        (∑ n ∈ Finset.Ico M N, a n * (((n : ℝ) + 1) / (N : ℝ))) := by
      rw [← Finset.sum_range_add_sum_Ico _ hMN.le]
    rw [hsplit]
    have h1 : |∑ n ∈ Finset.range M, a n * (((n : ℝ) + 1) / (N : ℝ))| ≤ S_head / N := by
      calc |∑ n ∈ Finset.range M, a n * (((n : ℝ) + 1) / (N : ℝ))|
          ≤ ∑ n ∈ Finset.range M, |a n * (((n : ℝ) + 1) / (N : ℝ))| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ n ∈ Finset.range M, (((n : ℝ) + 1) * |a n|) / (N : ℝ) := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((n : ℝ) + 1) / (N : ℝ))]; ring
        _ = S_head / (N : ℝ) := by rw [← Finset.sum_div]
    have h2 : |∑ n ∈ Finset.Ico M N, a n * (((n : ℝ) + 1) / (N : ℝ))| ≤ ∑' n : ℕ, |a (n + M)| := by
      calc |∑ n ∈ Finset.Ico M N, a n * (((n : ℝ) + 1) / (N : ℝ))|
          ≤ ∑ n ∈ Finset.Ico M N, |a n * (((n : ℝ) + 1) / (N : ℝ))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Finset.Ico M N, |a n| := by
            refine Finset.sum_le_sum fun n hn => ?_
            rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((n : ℝ) + 1) / (N : ℝ))]
            have hle1 : ((n : ℝ) + 1) / (N : ℝ) ≤ 1 := by
              rw [div_le_one hNpos]
              exact_mod_cast (Finset.mem_Ico.mp hn).2
            exact mul_le_of_le_one_right (abs_nonneg _) hle1
        _ = ∑ k ∈ Finset.range (N - M), |a (k + M)| := by
            rw [Finset.sum_Ico_eq_sum_range]
            refine Finset.sum_congr rfl fun k _ => by ring_nf
        _ ≤ ∑' k : ℕ, |a (k + M)| := by
            exact (ha.comp_injective (add_left_injective M)).sum_le_tsum _ (fun _ _ => abs_nonneg _)
    have h1' : S_head / (N : ℝ) < ε / 2 := by
      rw [div_lt_iff₀ hNpos]
      have := (div_lt_iff₀ hε).mp hN_gt
      linarith
    calc |(∑ n ∈ Finset.range M, a n * (((n : ℝ) + 1) / (N : ℝ))) +
          (∑ n ∈ Finset.Ico M N, a n * (((n : ℝ) + 1) / (N : ℝ)))|
        ≤ |∑ n ∈ Finset.range M, a n * (((n : ℝ) + 1) / (N : ℝ))| +
          |∑ n ∈ Finset.Ico M N, a n * (((n : ℝ) + 1) / (N : ℝ))| := abs_add_le _ _
      _ ≤ S_head / (N : ℝ) + ∑' n : ℕ, |a (n + M)| := add_le_add h1 h2
      _ < ε / 2 + ε / 2 := add_lt_add h1' hMbound
      _ = ε := add_halves ε
  have := hdiff.add hpartial
  simpa using this

/-- For `Re(s) > 1`, `∑' n : ℕ, (μ (n+1) : ℂ) / (n+1)^s = (riemannZeta s)⁻¹`. -/
lemma tsum_moebius_div_cpow_eq_inv_zeta {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (moebius (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ s) = (riemannZeta s)⁻¹ := by
  have hmul := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  have hzeta : LSeries (fun n => (ArithmeticFunction.zeta n : ℂ)) s = riemannZeta s := by
    rw [← LSeries_one_eq_riemannZeta hs]
    unfold LSeries LSeries.term
    congr 1 with n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, ArithmeticFunction.zeta_apply]
  change LSeries (fun n => (ArithmeticFunction.zeta n : ℂ)) s *
      LSeries (fun n => (moebius n : ℂ)) s = 1 at hmul
  rw [hzeta] at hmul
  have hL : LSeries (fun n => (moebius n : ℂ)) s = (riemannZeta s)⁻¹ :=
    eq_inv_of_mul_eq_one_right hmul
  rw [← hL]
  unfold LSeries LSeries.term
  have hsum : Summable (fun n : ℕ => if n = 0 then (0 : ℂ) else (moebius n : ℂ) / (n : ℂ) ^ s) := by
    have h0 := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
    exact h0
  rw [Summable.tsum_eq_zero_add hsum]
  simp

/-- For real `d > 0`, the Riesz-weighted Mobius sum at exponent `1 + d` tends to `(ζ(1+d))⁻¹.re`. -/
lemma tendsto_riesz_moebius_tail {d : ℝ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => ∑ i : Fin N,
      ((moebius (i.val + 1) : ℝ) / ((i.val : ℝ) + 1) ^ (1 + d)) *
        (1 - ((i.val : ℝ) + 1) / (N : ℝ)))
      atTop (𝓝 (riemannZeta (1 + (d : ℂ)))⁻¹.re) := by
  let a : ℕ → ℝ := fun n => (moebius (n + 1) : ℝ) / ((n : ℝ) + 1) ^ (1 + d)
  have ha_abs : Summable (fun n => |a n|) := by
    have hp : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(1 + d))) := by
      have := (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 1 + d)).comp_injective Nat.succ_injective
      refine this.congr fun n => ?_
      change (((n + 1 : ℕ) : ℝ) ^ (1 + d))⁻¹ = ((n : ℝ) + 1) ^ (-(1 + d))
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
      push_cast
      rfl
    refine hp.of_nonneg_of_le (fun _ => abs_nonneg _) fun n => ?_
    dsimp [a]
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _),
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1), div_eq_mul_inv]
    have hμ : |(moebius (n + 1) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n + 1)
    exact mul_le_of_le_one_left (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _)) hμ
  have htsum : (∑' n : ℕ, a n) = (riemannZeta (1 + (d : ℂ)))⁻¹.re := by
    have hs : 1 < (1 + (d : ℂ)).re := by simp [hd]
    have hc := congrArg Complex.re (tsum_moebius_div_cpow_eq_inv_zeta hs)
    rw [← hc]
    have hsum_c : Summable (fun n : ℕ => (moebius (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (1 + (d : ℂ))) := by
      have h1 : Summable (fun n : ℕ => (a n : ℂ)) := Complex.ofRealCLM.summable ha_abs.of_abs
      refine h1.congr fun n => ?_
      dsimp [a]
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hcp : (((n + 1 : ℕ) : ℂ) ^ (1 + (d : ℂ))) = ((((n : ℝ) + 1) ^ (1 + d) : ℝ) : ℂ) := by
        rw [show ((n + 1 : ℕ) : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
          show (1 + (d : ℂ)) = ((1 + d : ℝ) : ℂ) by push_cast; ring,
          Complex.ofReal_cpow hpos.le]
      rw [hcp]
      push_cast
      rfl
    have hre := Complex.reCLM.map_tsum hsum_c
    change (∑' n : ℕ, a n) = Complex.reCLM (∑' n : ℕ, (moebius (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (1 + (d : ℂ)))
    rw [hre]
    congr 1 with n
    dsimp [a]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hcp : (((n + 1 : ℕ) : ℂ) ^ (1 + (d : ℂ))) = ((((n : ℝ) + 1) ^ (1 + d) : ℝ) : ℂ) := by
      rw [show ((n + 1 : ℕ) : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
        show (1 + (d : ℂ)) = ((1 + d : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_cpow hpos.le]
    rw [hcp]
    change (((moebius (n + 1) : ℝ) / ((n : ℝ) + 1) ^ (1 + d) : ℝ) : ℂ).re = _
    push_cast
    rfl
  rw [← htsum]
  exact tendsto_riesz_partial_sum ha_abs

end BN1

/-
# Module 2: Mellin-Plancherel isometry, Titchmarsh (2.1.5), and polynomial zeta bound

Establishes:
1. Titchmarsh (2.1.5) for `{1 / (k * x)}` on `Ioi 0` (`0 < Re(s) < 1`), adapted from `R1.H2`.
2. Polynomial upper bound `‖riemannZeta s‖ ≤ 6 * ‖s‖` for `1/4 ≤ s.re` and `1/2 ≤ ‖s - 1‖`.
3. Mellin-Plancherel isometry on `L²(0, ∞)` via `x = exp u` and `MeasureTheory.Lp.norm_fourier_eq`.
4. Exact Mellin transform and `L²(0, ∞)` identity for `x^(-ε) * (χ + ∑ c_i ρ_{1/(i+1)})`.
-/

namespace BN2
open MeasureTheory Set Filter RiemannHypothesis FourierTransform
open scoped ComplexInnerProductSpace ENNReal

/-- The reciprocal fractional-part function `x ↦ {1 / x}`. -/
noncomputable def recipFract (x : ℝ) : ℝ := Int.fract (1 / x)

/-- The `k`-th dilated reciprocal fractional-part function `x ↦ {1 / (k * x)}`. -/
noncomputable def recipFractScaled (k : ℝ) (x : ℝ) : ℝ := Int.fract (1 / (k * x))

/-- The `n`-th harmonic sub-interval summand for Titchmarsh (2.1.5). -/
noncomputable def harmonicUnitSummand (s : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) ^ (1 - s) - ((n + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1) -
    ((n : ℂ) / s) * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s))

lemma recipFractScaled_eq_fractScalarInv (k : ℝ) (x : ℝ) :
    recipFractScaled k x = fractScalarInv (1 / k) x := by
  unfold recipFractScaled fractScalarInv
  congr 1
  rw [div_div]

lemma recipFractScaled_eq_of_gt_one {k : ℝ} (hk : 1 ≤ k) {x : ℝ} (hx : 1 < x) :
    recipFractScaled k x = 1 / (k * x) := by
  unfold recipFractScaled
  have hkx : 1 < k * x := by nlinarith
  rw [Int.fract_eq_self]
  exact ⟨by positivity, (div_lt_one (by linarith)).mpr hkx⟩

lemma norm_recipFractScaled_le_one (k : ℝ) (x : ℝ) :
    ‖(recipFractScaled k x : ℂ)‖ ≤ 1 := by
  unfold recipFractScaled
  rw [Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

lemma norm_recipFract_le_one (x : ℝ) : ‖(recipFract x : ℂ)‖ ≤ 1 := by
  simpa [recipFract, recipFractScaled] using norm_recipFractScaled_le_one 1 x

lemma measurable_recipFractScaled (k : ℝ) : Measurable (recipFractScaled k) :=
  measurable_fract.comp (measurable_const.div (measurable_const.mul measurable_id))

lemma measurable_recipFract : Measurable recipFract :=
  measurable_fract.comp (measurable_const.div measurable_id)

lemma integrableOn_Ioc_cpow (s : ℂ) (hs_pos : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) := by
  have hrpow : IntegrableOn (fun x : ℝ => x ^ (s.re - 1)) (Ioc (0 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < s.re - 1)
  refine hrpow.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht.1.ne')).continuousWithinAt
  · refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
    simp

lemma integrableOn_Ioc_recipFract_cpow (s : ℂ) (hs_pos : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) := by
  have hrpow : IntegrableOn (fun x : ℝ => x ^ (s.re - 1)) (Ioc (0 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < s.re - 1)
  refine hrpow.mono' ?_ ?_
  · refine measurable_recipFract.complex_ofReal.aestronglyMeasurable.restrict.mul ?_
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht.1.ne')).continuousWithinAt
  · refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, Complex.one_re]
    exact (mul_le_mul_of_nonneg_right (norm_recipFract_le_one x)
      (Real.rpow_nonneg hx.1.le _)).trans (one_mul _).le

lemma integrableOn_Ioi_recipFract_cpow (s : ℂ) (hs_lt_one : s.re < 1) :
    IntegrableOn (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) (Ioi (1 : ℝ)) := by
  have ha_lt : (s - 2).re < -1 := by
    simp only [Complex.sub_re, Complex.re_ofNat]
    linarith
  refine (integrableOn_Ioi_cpow_of_lt ha_lt zero_lt_one).congr_fun (fun x hx => ?_)
    measurableSet_Ioi
  have hx_pos : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hrf : recipFract x = 1 / x := by
    simpa [recipFract, recipFractScaled] using recipFractScaled_eq_of_gt_one le_rfl hx
  rw [hrf]
  push_cast
  have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
  rw [one_div, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hx_ne]
  congr 1
  ring

lemma integrableOn_Ioi_recipFractScaled_cpow (k : ℝ) (hk : 1 ≤ k) (s : ℂ)
    (hs_pos : 0 < s.re) (hs_lt_one : s.re < 1) :
    IntegrableOn (fun x : ℝ => (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)) (Ioi (0 : ℝ)) := by
  have hk_pos : (0 : ℝ) < k := by linarith
  have hk_ne : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk_pos.ne'
  have hpow_ne : (k : ℂ) ^ (s - 1) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hk_ne)
  have hunion : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hint_unscaled :
      IntegrableOn (fun u : ℝ => (recipFract u : ℂ) * (u : ℂ) ^ (s - 1)) (Ioi (0 : ℝ)) := by
    rw [hunion]
    exact (integrableOn_Ioc_recipFract_cpow s hs_pos).union
      (integrableOn_Ioi_recipFract_cpow s hs_lt_one)
  rw [← integrable_indicator_iff measurableSet_Ioi] at hint_unscaled ⊢
  have hscale : Integrable (fun x : ℝ => ((k : ℂ) ^ (s - 1))⁻¹ *
      ((Ioi (0 : ℝ)).indicator (fun u : ℝ => (recipFract u : ℂ) * (u : ℂ) ^ (s - 1))
        (k * x))) :=
    (hint_unscaled.comp_mul_left' hk_pos.ne').const_mul ((k : ℂ) ^ (s - 1))⁻¹
  refine hscale.congr (ae_of_all _ fun x => ?_)
  dsimp only
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · have hkx : k * x ∈ Ioi (0 : ℝ) := mul_pos hk_pos hx
    rw [indicator_of_mem hx, indicator_of_mem hkx]
    have hcp : ((k * x : ℝ) : ℂ) ^ (s - 1) = (k : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1) := by
      push_cast
      exact Complex.mul_cpow_ofReal_nonneg hk_pos.le (mem_Ioi.mp hx).le (s - 1)
    rw [hcp]
    change ((k : ℂ) ^ (s - 1))⁻¹ *
        ((recipFract (k * x) : ℂ) * ((k : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1))) =
      (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)
    unfold recipFractScaled recipFract
    field_simp [hpow_ne]
  · have hkx : k * x ∉ Ioi (0 : ℝ) := fun hm => hx ((mul_pos_iff_of_pos_left hk_pos).mp hm)
    rw [indicator_of_notMem hx, indicator_of_notMem hkx, mul_zero]

private lemma mellin_recipFract_split (s : ℂ) (hs_pos : 0 < s.re) (hs_lt_one : s.re < 1) :
    ∫ x in Ioi (0 : ℝ), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      (∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) +
      (∫ x in Ioi (1 : ℝ), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) := by
  rw [(Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  exact setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    (integrableOn_Ioc_recipFract_cpow s hs_pos) (integrableOn_Ioi_recipFract_cpow s hs_lt_one)

private lemma integral_Ioi_cpow_of_lt_one {a : ℂ} (ha : a.re < -1) :
    ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ a = -(1 / (a + 1)) := by
  have ha1_ne : a + 1 ≠ 0 := by
    intro h
    have := congr_arg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    linarith
  have hd : ∀ x ∈ Ici (1 : ℝ),
      HasDerivAt (fun t : ℝ => (t : ℂ) ^ (a + 1) / (a + 1)) ((x : ℂ) ^ a) x := fun x hx => by
    have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    exact hasDerivAt_ofReal_cpow_const' hx_pos.ne' (fun h => ha1_ne (by rw [h]; ring))
  have ht : Tendsto (fun t : ℝ => (t : ℂ) ^ (a + 1) / (a + 1)) atTop (nhds (0 / (a + 1))) := by
    apply Tendsto.div_const
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hre : (a + 1).re < 0 := by simp only [Complex.add_re, Complex.one_re]; linarith
    have hnorm : (fun t : ℝ => ‖(t : ℂ) ^ (a + 1)‖) =ᶠ[atTop] fun t : ℝ => t ^ (a + 1).re := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht_pos
      exact Complex.norm_cpow_eq_rpow_re_of_pos ht_pos (a + 1)
    rw [tendsto_congr' hnorm]
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (by linarith : 0 < -(a + 1).re)
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    (integrableOn_Ioi_cpow_of_lt ha zero_lt_one) ht
  simpa [zero_div, Complex.ofReal_one, Complex.one_cpow, neg_div] using hres

private lemma mellin_recipFract_tail (s : ℂ) (hs_lt_one : s.re < 1) :
    ∫ x in Ioi (1 : ℝ), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) = -(1 / (s - 1)) := by
  have hcongr : ∫ x in Ioi (1 : ℝ), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s - 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx_pos : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hrf : recipFract x = 1 / x := by
      simpa [recipFract, recipFractScaled] using recipFractScaled_eq_of_gt_one le_rfl hx
    rw [hrf]
    push_cast
    have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
    rw [one_div, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hx_ne]
    congr 1
    ring
  rw [hcongr]
  have ha_lt : (s - 2).re < -1 := by simp only [Complex.sub_re, Complex.re_ofNat]; linarith
  have htail := integral_Ioi_cpow_of_lt_one ha_lt
  have hs21 : s - 2 + 1 = s - 1 := by ring
  rwa [hs21] at htail

private lemma floor_one_div_eq_of_mem_Ioo {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Ioo (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) : ⌊1 / x⌋ = (n : ℤ) := by
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hx_pos : 0 < x := lt_trans (one_div_pos.mpr hn1_pos) hx.1
  rw [Int.floor_eq_iff]
  refine ⟨?_, ?_⟩
  · have h1 : (n : ℝ) = 1 / (1 / (n : ℝ)) := by rw [one_div_one_div]
    rw [Int.cast_natCast, h1]
    exact one_div_le_one_div_of_le hx_pos hx.2.le
  · have h2 : (n : ℝ) + 1 = 1 / (1 / ((n : ℝ) + 1)) := by rw [one_div_one_div]
    rw [Int.cast_natCast, h2]
    exact one_div_lt_one_div_of_lt (one_div_pos.mpr hn1_pos) hx.1

private lemma abel_harmonic_telescope (s : ℂ) (M : ℕ) :
    ∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)) =
      (∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s)) - (M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1),
      Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1), ih]
    push_cast
    ring

private lemma sum_harmonic_floor_integral_eq (s : ℂ) (M : ℕ) :
    ∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) / s * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)) =
      (1 / s) * ((∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s)) -
        (M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s)) := by
  have hterm : (∑ n ∈ Finset.Ico 1 (M + 1),
      (n : ℂ) / s * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s))) =
      (1 / s) * ∑ n ∈ Finset.Ico 1 (M + 1),
        (n : ℂ) * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hterm, abel_harmonic_telescope]

private lemma inv_cpow_nat (m : ℕ) (w : ℂ) : ((1 / (m : ℝ) : ℝ) : ℂ) ^ w = (m : ℂ) ^ (-w) := by
  push_cast
  have harg : (m : ℂ).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg m)]
    exact Real.pi_ne_zero.symm
  rw [one_div, Complex.inv_cpow_eq_ite, ite_eq_right_iff.mpr (fun h => absurd h harg),
    Complex.cpow_neg]

private lemma integral_Ioc_harmonic_cpow (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs_pos : 0 < s.re) :
    ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), (x : ℂ) ^ (s - 1) =
      ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)) / s := by
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le (Nat.cast_pos.mpr hn) (by linarith)
  rw [← intervalIntegral.integral_of_le hle,
    integral_cpow (Or.inl (by simp [Complex.sub_re]; linarith))]
  have hs1 : s - 1 + 1 = s := by ring
  rw [hs1, inv_cpow_nat n s, show ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) ^ s = ((n + 1 : ℕ) : ℂ) ^ (-s)
    from by simpa [Nat.cast_add, Nat.cast_one] using inv_cpow_nat (n + 1) s]

private lemma floor_cpow_ae_const (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    ∀ᵐ x : ℝ ∂(volume.restrict (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)))),
      ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) = (n : ℂ) * (x : ℂ) ^ (s - 1) := by
  have hdiff : ∀ᵐ x ∂volume, x ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) →
      x ∈ Ioo (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) := by
    have hne : ∀ᵐ x ∂volume, x ≠ (1 / (n : ℝ)) := ae_iff.mpr (by simp [measure_singleton])
    filter_upwards [hne] with x hne hx
    exact ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hdiff] with x hx_imp hx_ioc
  rw [floor_one_div_eq_of_mem_Ioo hn (hx_imp hx_ioc)]
  simp

private lemma integral_Ioc_harmonic_floor_cpow (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs_pos : 0 < s.re) :
    ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) =
      (n : ℂ) / s * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)) := by
  rw [integral_congr_ae (floor_cpow_ae_const n hn s), integral_const_mul,
    integral_Ioc_harmonic_cpow n hn s hs_pos]
  ring

private lemma integrableOn_Ioc_harmonic_floor_cpow (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    IntegrableOn (fun x : ℝ => ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcont : ContinuousOn (fun x : ℝ => (n : ℂ) * (x : ℂ) ^ (s - 1))
      (Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
    refine ContinuousOn.mul continuousOn_const fun x hx => ?_
    have hx_pos : 0 < x := lt_of_lt_of_le (one_div_pos.mpr hn1_pos) hx.1
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx_pos.ne')).continuousWithinAt
  exact (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr
    ((floor_cpow_ae_const n hn s).mono fun _ h => h.symm)

private lemma truncated_floor_partition_aux (M : ℕ) (s : ℂ) :
    IntegrableOn (fun x : ℝ => ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc (1 / ((M : ℝ) + 1)) 1) ∧
    ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) =
      ∑ n ∈ Finset.Ico 1 (M + 1),
        ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) := by
  induction M with
  | zero =>
    have hIoc : Ioc (1 / (((0 : ℕ) : ℝ) + 1)) 1 = ∅ := by norm_num
    rw [hIoc]
    simp
  | succ M ih =>
    rcases ih with ⟨ih_int, ih_eq⟩
    have ha : 1 / (((M + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
    have hb : 1 / ((M : ℝ) + 1) ≤ (1 : ℝ) := div_le_one_of_le₀ (by linarith) (by positivity)
    have hunion : Ioc (1 / (((M + 1 : ℕ) : ℝ) + 1)) 1 =
        Ioc (1 / (((M + 1 : ℕ) : ℝ) + 1)) (1 / ((M : ℝ) + 1)) ∪ Ioc (1 / ((M : ℝ) + 1)) 1 :=
      (Ioc_union_Ioc_eq_Ioc ha hb).symm
    have hdisj : Disjoint (Ioc (1 / (((M + 1 : ℕ) : ℝ) + 1)) (1 / ((M : ℝ) + 1)))
        (Ioc (1 / ((M : ℝ) + 1)) 1) := by
      rw [disjoint_left]
      intro x hx1 hx2
      linarith [hx1.2, hx2.1]
    have hleft_int : IntegrableOn (fun x : ℝ => ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1))
        (Ioc (1 / (((M + 1 : ℕ) : ℝ) + 1)) (1 / ((M : ℝ) + 1))) := by
      simpa [Nat.cast_add, Nat.cast_one] using
        integrableOn_Ioc_harmonic_floor_cpow (M + 1) (by omega) s
    refine ⟨by rw [hunion]; exact hleft_int.union ih_int, ?_⟩
    rw [hunion, setIntegral_union hdisj measurableSet_Ioc hleft_int ih_int, ih_eq,
      Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1), add_comm]
    congr 1
    simp [Nat.cast_add, Nat.cast_one]

private lemma integrableOn_Ioc_truncated_inv_mul_cpow (a : ℝ) (ha : 0 < a) (b : ℝ) (_hab : a ≤ b)
    (s : ℂ) :
    IntegrableOn (fun x : ℝ => ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) (Ioc a b) := by
  have hcont : ContinuousOn (fun x : ℝ => ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) (Icc a b) := by
    refine ContinuousOn.mul (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.div continuousOn_id fun x hx => (lt_of_lt_of_le ha hx.1).ne')) ?_
    intro x hx
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (lt_of_lt_of_le ha hx.1).ne')).continuousWithinAt
  exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self

private lemma integral_Ioc_inv_mul_cpow (a : ℝ) (ha : 0 < a) (b : ℝ) (hab : a ≤ b)
    (s : ℂ) (hs_ne_one : s ≠ 1) :
    ∫ x in Ioc a b, ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
      ((b : ℂ) ^ (s - 1) - (a : ℂ) ^ (s - 1)) / (s - 1) := by
  have hcongr : ∫ x in Ioc a b, ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
      ∫ x in Ioc a b, (x : ℂ) ^ (s - 2) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le ha hx.1.le).ne'
    push_cast
    rw [one_div, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hx_ne]
    congr 1
    ring
  have hs2_ne : s - 2 ≠ -1 := fun h => hs_ne_one (by linear_combination h)
  have h0_not_mem : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab, mem_Icc]
    intro h0
    linarith [h0.1]
  rw [hcongr, ← intervalIntegral.integral_of_le hab, integral_cpow (Or.inr ⟨hs2_ne, h0_not_mem⟩)]
  have hs21 : s - 2 + 1 = s - 1 := by ring
  rw [hs21]

private noncomputable def truncatedTitchmarshRHS (s : ℂ) (M : ℕ) : ℂ :=
  (1 - ((M + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1) -
    (1 / s) * ((∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s)) -
      (M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s))

private lemma integral_Ioc_truncated_recipFract_cpow (M : ℕ) (s : ℂ)
    (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      truncatedTitchmarshRHS s M := by
  have ha : 0 < 1 / ((M : ℝ) + 1) := by positivity
  have hab : 1 / ((M : ℝ) + 1) ≤ (1 : ℝ) := div_le_one_of_le₀ (by linarith) (by positivity)
  have hdecomp : (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) =
      fun x : ℝ => ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) -
        ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) := by
    ext x
    unfold recipFract Int.fract
    push_cast
    ring
  rw [hdecomp, integral_sub (integrableOn_Ioc_truncated_inv_mul_cpow _ ha 1 hab s)
      (truncated_floor_partition_aux M s).1,
    integral_Ioc_inv_mul_cpow _ ha 1 hab s hs_ne_one, (truncated_floor_partition_aux M s).2]
  have hsum :
      (∑ n ∈ Finset.Ico 1 (M + 1),
        ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)),
          ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1)) =
        ∑ n ∈ Finset.Ico 1 (M + 1),
          (n : ℂ) / s * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)) :=
    Finset.sum_congr rfl fun n hn =>
      integral_Ioc_harmonic_floor_cpow n (Finset.mem_Ico.mp hn).1 s hs_pos
  rw [hsum, sum_harmonic_floor_integral_eq, Complex.ofReal_one, Complex.one_cpow]
  have hinv : (((1 / ((M : ℝ) + 1) : ℝ) : ℂ)) ^ (s - 1) = ((M + 1 : ℕ) : ℂ) ^ (1 - s) := by
    have heq : (1 / ((M : ℝ) + 1) : ℝ) = 1 / ((M + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [heq, inv_cpow_nat (M + 1) (s - 1)]
    congr 1
    ring
  rw [hinv]
  rfl

private lemma tendsto_truncatedTitchmarshRHS_eq_unit (s : ℂ)
    (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    Tendsto (truncatedTitchmarshRHS s) atTop
      (nhds (∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1))) := by
  have heq : truncatedTitchmarshRHS s = fun M : ℕ =>
      ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) := by
    ext M
    exact (integral_Ioc_truncated_recipFract_cpow M s hs_pos hs_ne_one).symm
  rw [heq]
  have hsub : (fun M : ℕ => ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1,
      (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) = fun M : ℕ =>
      (∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) -
      (∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) := by
    ext M
    have h0 : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
    have h1 : 1 / ((M : ℝ) + 1) ≤ (1 : ℝ) := div_le_one_of_le₀ (by linarith) (by positivity)
    have hint := integrableOn_Ioc_recipFract_cpow s hs_pos
    have hsplit : ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
        (∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) +
        (∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) := by
      rw [(Ioc_union_Ioc_eq_Ioc h0 h1).symm]
      exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (hint.mono_set (Ioc_subset_Ioc_right h1)) (hint.mono_set (Ioc_subset_Ioc_left h0))
    linear_combination -hsplit
  have hnorm_le : ∀ M : ℕ,
      ‖∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
        ((M : ℝ) + 1) ^ (-s.re) / s.re := fun M => by
    have h0 : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
    have h1 : 1 / ((M : ℝ) + 1) ≤ (1 : ℝ) := div_le_one_of_le₀ (by linarith) (by positivity)
    have hint_fn := (integrableOn_Ioc_recipFract_cpow s hs_pos).mono_set (Ioc_subset_Ioc_right h1)
    have hint_rpow : IntegrableOn (fun x : ℝ => x ^ (s.re - 1))
        (Ioc (0 : ℝ) (1 / ((M : ℝ) + 1))) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le h0]
      exact intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < s.re - 1)
    have hle_int : ∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)),
        ‖(recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
        ∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), x ^ (s.re - 1) := by
      refine setIntegral_mono_on hint_fn.norm hint_rpow measurableSet_Ioc fun x hx => ?_
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, Complex.one_re]
      exact (mul_le_mul_of_nonneg_right (norm_recipFract_le_one x)
        (Real.rpow_nonneg hx.1.le _)).trans (one_mul _).le
    have hval : ∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), x ^ (s.re - 1) =
        ((M : ℝ) + 1) ^ (-s.re) / s.re := by
      rw [← intervalIntegral.integral_of_le h0,
        integral_rpow (Or.inl (by linarith : (-1 : ℝ) < s.re - 1))]
      have hs1 : s.re - 1 + 1 = s.re := by ring
      rw [hs1, Real.zero_rpow hs_pos.ne', sub_zero, one_div,
        Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
    exact (norm_integral_le_integral_norm _).trans (hle_int.trans hval.le)
  have ht_zero : Tendsto (fun M : ℕ =>
      ∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1))
      atTop (nhds 0) := by
    have hm : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have ht : Tendsto (fun M : ℕ => ((M : ℝ) + 1) ^ (-s.re) / s.re) atTop (nhds (0 / s.re)) :=
      ((tendsto_rpow_neg_atTop hs_pos).comp hm).div_const s.re
    rw [zero_div] at ht
    exact squeeze_zero_norm hnorm_le ht
  rw [hsub]
  simpa using tendsto_const_nhds.sub ht_zero

private lemma sum_harmonicUnitSummand_eq_truncatedTitchmarshRHS (s : ℂ)
    (_hs_ne_zero : s ≠ 0) (hs_ne_one : s ≠ 1) (M : ℕ) :
    ∑ n ∈ Finset.Ico 1 (M + 1), harmonicUnitSummand s n = truncatedTitchmarshRHS s M := by
  have htelesc : ∑ n ∈ Finset.Ico 1 (M + 1),
      ((n : ℂ) ^ (1 - s) - ((n + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1) =
      (1 - ((M + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1) := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1), ih]
      have hcast : ((M + 1 : ℕ) : ℂ) + 1 = ((M + 1 + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [← hcast]
      field_simp [sub_ne_zero.mpr hs_ne_one]
      ring
  unfold harmonicUnitSummand
  rw [Finset.sum_sub_distrib, htelesc, sum_harmonic_floor_integral_eq s M]
  rfl

private lemma mellin_recipFract_unit_interval_of_one_lt_re (s : ℂ) (hs_gt_one : 1 < s.re) :
    ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      1 / (s - 1) - riemannZeta s / s := by
  have hs_pos : 0 < s.re := by linarith
  have hs_ne : s ≠ 0 := fun h => by rw [h] at hs_gt_one; simp at hs_gt_one; linarith
  have hs_ne_one : s ≠ 1 := fun h => by rw [h] at hs_gt_one; simp at hs_gt_one
  have hm : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hpow0 : Tendsto (fun t : ℝ => t ^ (1 - s.re)) atTop (nhds 0) := by
    simpa [neg_sub] using tendsto_rpow_neg_atTop (by linarith : 0 < s.re - 1)
  have hpow : Tendsto (fun M : ℕ => ((M : ℝ) + 1) ^ (1 - s.re)) atTop (nhds 0) := hpow0.comp hm
  have h_succ : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℂ) ^ (1 - s)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine hpow.congr fun M => ?_
    have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hcast : ((M + 1 : ℕ) : ℂ) = (((M : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.sub_re, Complex.one_re]
  have h_mul : Tendsto (fun M : ℕ => (M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s)) atTop (nhds 0) := by
    refine squeeze_zero_norm (fun M => ?_) hpow
    have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hcast : ((M + 1 : ℕ) : ℂ) = (((M : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.norm_natCast,
      Complex.neg_re]
    calc (M : ℝ) * ((M : ℝ) + 1) ^ (-s.re)
        ≤ ((M : ℝ) + 1) * ((M : ℝ) + 1) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hpos.le _)
      _ = ((M : ℝ) + 1) ^ (1 : ℝ) * ((M : ℝ) + 1) ^ (-s.re) := by rw [Real.rpow_one]
      _ = ((M : ℝ) + 1) ^ (1 - s.re) := by rw [← Real.rpow_add hpos, sub_eq_add_neg]
  have h_zeta : Tendsto (fun M : ℕ => ∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s))
      atTop (nhds (riemannZeta s)) := by
    have hsum := Complex.summable_one_div_nat_cpow.mpr hs_gt_one
    have hhas : HasSum (fun n : ℕ => 1 / (n : ℂ) ^ s) (riemannZeta s) := by
      rw [zeta_eq_tsum_one_div_nat_cpow hs_gt_one]
      exact hsum.hasSum
    have ht : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (M + 1), 1 / (n : ℂ) ^ s)
        atTop (nhds (riemannZeta s)) := hhas.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have heq : (fun M : ℕ => ∑ n ∈ Finset.range (M + 1), 1 / (n : ℂ) ^ s) =
        fun M : ℕ => ∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s) := by
      ext M
      induction M with
      | zero => simp [Complex.zero_cpow hs_ne]
      | succ M ih =>
        rw [Finset.sum_range_succ, Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1), ih,
          one_div, Complex.cpow_neg]
    rwa [heq] at ht
  have h1 := ((tendsto_const_nhds (x := (1 : ℂ))).sub h_succ).div_const (s - 1)
  have h2 := (tendsto_const_nhds (x := 1 / s)).mul (h_zeta.sub h_mul)
  have h12 : Tendsto (truncatedTitchmarshRHS s) atTop (nhds (1 / (s - 1) - riemannZeta s / s)) := by
    convert h1.sub h2 using 1
    · ext M; unfold truncatedTitchmarshRHS; push_cast; ring
    · simp [sub_zero, one_mul, div_eq_mul_inv, mul_comm]
  exact tendsto_nhds_unique (tendsto_truncatedTitchmarshRHS_eq_unit s hs_pos hs_ne_one) h12

private lemma integral_Ioc_harmonic_recipFract_cpow (n : ℕ) (hn : 1 ≤ n) (s : ℂ)
    (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      harmonicUnitSummand s n := by
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le (Nat.cast_pos.mpr hn) (by linarith)
  have hdecomp : (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) =
      fun x : ℝ => ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) -
        ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) := by
    ext x
    unfold recipFract Int.fract
    push_cast
    ring
  rw [hdecomp, integral_sub (integrableOn_Ioc_truncated_inv_mul_cpow _ (one_div_pos.mpr hn1_pos)
      (1 / (n : ℝ)) hle s) (integrableOn_Ioc_harmonic_floor_cpow n hn s),
    integral_Ioc_inv_mul_cpow _ (one_div_pos.mpr hn1_pos) (1 / (n : ℝ)) hle s hs_ne_one,
    integral_Ioc_harmonic_floor_cpow n hn s hs_pos]
  rw [inv_cpow_nat n (s - 1),
    show ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) ^ (s - 1) = ((n + 1 : ℕ) : ℂ) ^ (1 - s) from by
      simpa [Nat.cast_add, Nat.cast_one, neg_sub] using inv_cpow_nat (n + 1) (s - 1)]
  simp only [neg_sub]
  rfl

private lemma norm_harmonicUnitSummand_le_of_le_re (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ)
    (s : ℂ) (hs_ge : δ ≤ s.re) (hs_ne_one : s ≠ 1) :
    ‖harmonicUnitSummand s n‖ ≤ ((n : ℝ) ^ (-δ) - ((n + 1 : ℕ) : ℝ) ^ (-δ)) / δ := by
  have hs_pos : 0 < s.re := lt_of_lt_of_le hδ hs_ge
  rw [← integral_Ioc_harmonic_recipFract_cpow n hn s hs_pos hs_ne_one]
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le (Nat.cast_pos.mpr hn) (by linarith)
  have hsub : Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) ⊆ Ioc (0 : ℝ) 1 :=
    Ioc_subset_Ioc (by positivity) (div_le_one_of_le₀ (by exact_mod_cast hn) (by positivity))
  have hint_fn := (integrableOn_Ioc_recipFract_cpow s hs_pos).mono_set hsub
  have hint_rpow : IntegrableOn (fun x : ℝ => x ^ (δ - 1))
      (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
    have hcont : ContinuousOn (fun x : ℝ => x ^ (δ - 1))
        (Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := fun x hx =>
      (Real.continuousAt_rpow_const _ _
        (Or.inl (lt_of_lt_of_le (one_div_pos.mpr hn1_pos) hx.1).ne')).continuousWithinAt
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hle_int : ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)),
      ‖(recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
      ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), x ^ (δ - 1) := by
    refine setIntegral_mono_on hint_fn.norm hint_rpow measurableSet_Ioc fun x hx => ?_
    have hx_mem := hsub hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx_mem.1, Complex.sub_re, Complex.one_re]
    calc ‖(recipFract x : ℂ)‖ * x ^ (s.re - 1)
        ≤ 1 * x ^ (s.re - 1) :=
          mul_le_mul_of_nonneg_right (norm_recipFract_le_one x) (Real.rpow_nonneg hx_mem.1.le _)
      _ = x ^ (s.re - 1) := one_mul _
      _ ≤ x ^ (δ - 1) := Real.rpow_le_rpow_of_exponent_ge hx_mem.1 hx_mem.2 (by linarith)
  have hval : ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), x ^ (δ - 1) =
      ((n : ℝ) ^ (-δ) - ((n + 1 : ℕ) : ℝ) ^ (-δ)) / δ := by
    rw [← intervalIntegral.integral_of_le hle,
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < δ - 1))]
    have hδ1 : δ - 1 + 1 = δ := by ring
    have inv_rpow : ∀ m : ℕ, (1 / (m : ℝ)) ^ δ = (m : ℝ) ^ (-δ) := fun m => by
      rw [one_div, Real.inv_rpow (Nat.cast_nonneg m), Real.rpow_neg (Nat.cast_nonneg m)]
    rw [hδ1, inv_rpow n, show (1 / ((n : ℝ) + 1)) ^ δ = ((n + 1 : ℕ) : ℝ) ^ (-δ) from by
      simpa [Nat.cast_add, Nat.cast_one] using inv_rpow (n + 1)]
  exact (norm_integral_le_integral_norm _).trans (hle_int.trans hval.le)

private lemma summable_rpow_diff_div (δ : ℝ) (hδ : 0 < δ) :
    Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-δ) - ((n + 1 + 1 : ℕ) : ℝ) ^ (-δ)) / δ) := by
  let g : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) ^ (-δ) / δ
  have hg_nn : ∀ n : ℕ, 0 ≤ g n - g (n + 1) := fun n => by
    have hle : (((n + 1 + 1 : ℕ) : ℝ) ^ (-δ)) ≤ ((n + 1 : ℕ) : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity)
        (by exact_mod_cast Nat.le_succ (n + 1)) (by linarith)
    simpa [g, sub_div, Nat.cast_add, Nat.cast_one] using div_nonneg (sub_nonneg.mpr hle) hδ.le
  have hg_tz : Tendsto g atTop (nhds 0) := by
    have hm : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have hpow : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ) ^ (-δ)) atTop (nhds 0) := by
      convert (tendsto_rpow_neg_atTop hδ).comp hm using 1
      ext M
      simp [Nat.cast_add, Nat.cast_one]
    simpa [g, zero_div] using hpow.div_const δ
  have hg_t : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, (g n - g (n + 1))) atTop
      (nhds (g 0)) := by
    simp_rw [Finset.sum_range_sub' g]
    simpa [sub_zero] using tendsto_const_nhds.sub hg_tz
  simpa [g, sub_div, Nat.cast_add, Nat.cast_one] using
    ((hasSum_iff_tendsto_nat_of_nonneg hg_nn (g 0)).mpr hg_t).summable

private lemma summable_harmonicUnitSummand (s : ℂ) (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    Summable (fun n : ℕ => harmonicUnitSummand s (n + 1)) := by
  refine (summable_rpow_diff_div s.re hs_pos).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => norm_harmonicUnitSummand_le_of_le_re (n + 1) (by omega)
      s.re hs_pos s le_rfl hs_ne_one) |>.of_norm

private lemma tsum_harmonicUnitSummand_eq_unit_integral (s : ℂ)
    (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    (∑' n : ℕ, harmonicUnitSummand s (n + 1)) =
      ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) := by
  have hs_ne : s ≠ 0 := fun h => by rw [h] at hs_pos; simp at hs_pos
  have ht1 := (summable_harmonicUnitSummand s hs_pos hs_ne_one).hasSum.tendsto_sum_nat
  have heq : (fun M : ℕ => ∑ n ∈ Finset.range M, harmonicUnitSummand s (n + 1)) =
      truncatedTitchmarshRHS s := by
    ext M
    rw [← sum_harmonicUnitSummand_eq_truncatedTitchmarshRHS s hs_ne hs_ne_one M]
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1), ih]
  rw [heq] at ht1
  exact tendsto_nhds_unique ht1 (tendsto_truncatedTitchmarshRHS_eq_unit s hs_pos hs_ne_one)

private lemma analyticOnNhd_tsum_harmonicUnitSummand :
    AnalyticOnNhd ℂ (fun s : ℂ => ∑' n : ℕ, harmonicUnitSummand s (n + 1))
      {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  have hS_open : IsOpen {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hS_open
  let δ : ℝ := s.re / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith [hs.1]
  let Uδ : Set ℂ := {w : ℂ | δ < w.re ∧ w ≠ 1}
  have hUδ_open : IsOpen Uδ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have h_diff_term : ∀ n : ℕ,
      DifferentiableOn ℂ (fun w : ℂ => harmonicUnitSummand w (n + 1)) Uδ := by
    intro n w hw
    have hw_ne_zero : w ≠ 0 := fun h0 => by
      rw [h0] at hw
      simp only [Uδ, Set.mem_ofPred_eq, Complex.zero_re] at hw
      linarith [hw.1, hδ]
    have hn1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hn2 : ((n + 1 + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1 : DifferentiableAt ℂ (fun z : ℂ => ((n + 1 : ℕ) : ℂ) ^ (1 - z)) w :=
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow (Or.inl hn1)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => ((n + 1 + 1 : ℕ) : ℂ) ^ (1 - z)) w :=
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow (Or.inl hn2)
    have h3 : DifferentiableAt ℂ (fun z : ℂ => ((n + 1 : ℕ) : ℂ) ^ (-z)) w :=
      differentiableAt_id.neg.const_cpow (Or.inl hn1)
    have h4 : DifferentiableAt ℂ (fun z : ℂ => ((n + 1 + 1 : ℕ) : ℂ) ^ (-z)) w :=
      differentiableAt_id.neg.const_cpow (Or.inl hn2)
    have h_all : DifferentiableAt ℂ (fun z : ℂ => harmonicUnitSummand z (n + 1)) w := by
      unfold harmonicUnitSummand
      exact ((h1.sub h2).div (differentiableAt_id.sub (differentiableAt_const 1))
        (sub_ne_zero.mpr hw.2)).sub
          (((differentiableAt_const _).div differentiableAt_id hw_ne_zero).mul (h3.sub h4))
    exact h_all.differentiableWithinAt
  have h_diff_Uδ := Complex.differentiableOn_tsum_of_summable_norm (summable_rpow_diff_div δ hδ)
    h_diff_term hUδ_open fun n w hw =>
      norm_harmonicUnitSummand_le_of_le_re (n + 1) (by omega) δ hδ w hw.1.le hw.2
  exact (h_diff_Uδ.differentiableAt
    (hUδ_open.mem_nhds ⟨by dsimp [δ]; linarith [hs.1], hs.2⟩)).differentiableWithinAt

private lemma convex_linear_gt (f : ℂ →ₗ[ℝ] ℝ) (r : ℝ) : Convex ℝ {s : ℂ | r < f s} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at hx hy ⊢
  by_cases ha0 : 0 < a
  · calc r = a * r + b * r := by rw [← add_mul, hab, one_mul]
      _ < a * f x + b * f y := add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hx ha0) (mul_le_mul_of_nonneg_left hy.le hb)
  · have ha0' : a = 0 := le_antisymm (not_lt.mp ha0) ha
    have hb1 : b = 1 := by linarith
    rw [ha0', hb1]
    linarith

private lemma convex_linear_lt (f : ℂ →ₗ[ℝ] ℝ) (r : ℝ) : Convex ℝ {s : ℂ | f s < r} := by
  simpa [neg_lt_neg_iff] using convex_linear_gt (-f) (-r)

theorem riemannZeta_eq_tsum_harmonicUnitSummand (s : ℂ) (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s * ∑' n : ℕ, harmonicUnitSummand s (n + 1) := by
  let S : Set ℂ := {z : ℂ | 0 < z.re ∧ z ≠ 1}
  let F : ℂ → ℂ := fun z =>
    riemannZeta z - z * (1 / (z - 1) - ∑' n : ℕ, harmonicUnitSummand z (n + 1))
  have hS_open : IsOpen S := (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have hF_ana : AnalyticOnNhd ℂ F S := by
    have h_zeta : AnalyticOnNhd ℂ riemannZeta S :=
      DifferentiableOn.analyticOnNhd
        (fun z hz => (differentiableAt_riemannZeta hz.2).differentiableWithinAt) hS_open
    have h_pole : AnalyticOnNhd ℂ (fun z : ℂ => (1 : ℂ) / (z - 1)) S :=
      DifferentiableOn.analyticOnNhd (fun z hz => ((differentiableAt_const (1 : ℂ)).div
        (differentiableAt_id.sub (differentiableAt_const 1))
        (sub_ne_zero.mpr hz.2)).differentiableWithinAt) hS_open
    exact h_zeta.sub (analyticOnNhd_id.mul (h_pole.sub analyticOnNhd_tsum_harmonicUnitSummand))
  have hF_gt_one : ∀ z : ℂ, 1 < z.re → F z = 0 := fun z hz => by
    have hz_ne : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz; linarith
    have hz1 : z ≠ 1 := fun h1 => by rw [h1] at hz; simp at hz
    have htsum : (∑' n : ℕ, harmonicUnitSummand z (n + 1)) = 1 / (z - 1) - riemannZeta z / z := by
      rw [tsum_harmonicUnitSummand_eq_unit_integral z (by linarith) hz1,
        mellin_recipFract_unit_interval_of_one_lt_re z hz]
    dsimp [F]
    rw [htsum]
    field_simp [hz_ne]
    ring
  let U_top : Set ℂ := {z : ℂ | 0 < z.re} ∩ {z : ℂ | 0 < z.im}
  let U_bot : Set ℂ := {z : ℂ | 0 < z.re} ∩ {z : ℂ | z.im < 0}
  let U_left : Set ℂ := {z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1}
  have hre0 : Convex ℝ {z : ℂ | 0 < z.re} := convex_linear_gt Complex.reLm 0
  have hright_open : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have htop_open : IsOpen U_top :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hU_top_sub : U_top ⊆ S := fun z ⟨hz_re, hz_im⟩ =>
    ⟨hz_re, fun h1 => by subst h1; simp at hz_im⟩
  have hU_bot_sub : U_bot ⊆ S := fun z ⟨hz_re, hz_im⟩ =>
    ⟨hz_re, fun h1 => by subst h1; simp at hz_im⟩
  have hU_left_sub : U_left ⊆ S := fun z ⟨hz_re, hz_lt⟩ =>
    ⟨hz_re, fun h1 => by subst h1; simp at hz_lt⟩
  have hzero_top : Set.EqOn F 0 U_top := by
    refine (hF_ana.mono hU_top_sub).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const (hre0.inter (convex_linear_gt Complex.imLm 0)).isPreconnected
      (z₀ := (2 : ℂ) + Complex.I) (by simp [U_top]) ?_
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{z : ℂ | 1 < z.re}, hright_open.mem_nhds (by simp), fun z hz => hF_gt_one z hz⟩
  have hzero_bot : Set.EqOn F 0 U_bot := by
    refine (hF_ana.mono hU_bot_sub).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const (hre0.inter (convex_linear_lt Complex.imLm 0)).isPreconnected
      (z₀ := (2 : ℂ) - Complex.I) (by simp [U_bot]) ?_
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{z : ℂ | 1 < z.re}, hright_open.mem_nhds (by simp), fun z hz => hF_gt_one z hz⟩
  have hzero_left : Set.EqOn F 0 U_left := by
    refine (hF_ana.mono hU_left_sub).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const (hre0.inter (convex_linear_lt Complex.reLm 1)).isPreconnected
      (z₀ := (1 / 2 : ℂ) + Complex.I) (by simp [U_left]; norm_num) ?_
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨U_top, htop_open.mem_nhds (by simp [U_top]), fun z hz => hzero_top hz⟩
  have hFs : F s = 0 := by
    rcases lt_trichotomy s.re 1 with hlt | heq | hgt
    · exact hzero_left ⟨hs_pos, hlt⟩
    · have him : s.im ≠ 0 := fun h0 => hs_ne_one (Complex.ext heq h0)
      rcases lt_or_gt_of_ne him with hneg | hpos
      · exact hzero_bot ⟨hs_pos, hneg⟩
      · exact hzero_top ⟨hs_pos, hpos⟩
    · exact hF_gt_one s hgt
  have h_eq := sub_eq_zero.mp hFs
  rw [h_eq]
  ring

/-- Titchmarsh (1986, Eq. 2.1.5) on `(0, 1]`. -/
theorem mellin_recipFract_unit_interval (s : ℂ) (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    ∫ x in Set.Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      1 / (s - 1) - riemannZeta s / s := by
  have hs_ne : s ≠ 0 := fun h => by rw [h] at hs_pos; simp at hs_pos
  rw [← tsum_harmonicUnitSummand_eq_unit_integral s hs_pos hs_ne_one,
    riemannZeta_eq_tsum_harmonicUnitSummand s hs_pos hs_ne_one]
  field_simp [hs_ne]
  ring

/-- Polynomial bound for `riemannZeta` in the half-plane `Re(s) ≥ 1/4` away from `1`. -/
theorem norm_riemannZeta_le_six_mul_norm {s : ℂ} (hre : (1 / 4 : ℝ) ≤ s.re)
    (h1 : (1 / 2 : ℝ) ≤ ‖s - 1‖) :
    ‖riemannZeta s‖ ≤ 6 * ‖s‖ := by
  have hs_pos : 0 < s.re := by linarith
  have hs_ne_one : s ≠ 1 := fun h => by rw [h, sub_self, norm_zero] at h1; linarith
  have hs_ne_zero : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs_pos; linarith
  have hmt := mellin_recipFract_unit_interval s hs_pos hs_ne_one
  have hzeta_eq : riemannZeta s =
      s / (s - 1) - s * ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) := by
    rw [hmt]
    field_simp [hs_ne_zero, sub_ne_zero.mpr hs_ne_one]
    ring
  have hint_le : ‖∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤ 4 := by
    have hrpow : IntegrableOn (fun x : ℝ => x ^ (s.re - 1)) (Ioc (0 : ℝ) 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < s.re - 1)
    have hle_int : ∫ x in Ioc (0 : ℝ) 1, ‖(recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
        ∫ x in Ioc (0 : ℝ) 1, x ^ (s.re - 1) := by
      refine setIntegral_mono_on (integrableOn_Ioc_recipFract_cpow s hs_pos).norm hrpow
        measurableSet_Ioc fun x hx => ?_
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, Complex.one_re]
      exact (mul_le_mul_of_nonneg_right (norm_recipFract_le_one x)
        (Real.rpow_nonneg hx.1.le _)).trans (one_mul _).le
    have hval : ∫ x in Ioc (0 : ℝ) 1, x ^ (s.re - 1) = 1 / s.re := by
      rw [← intervalIntegral.integral_of_le zero_le_one,
        integral_rpow (Or.inl (by linarith : (-1 : ℝ) < s.re - 1))]
      have hs1 : s.re - 1 + 1 = s.re := by ring
      rw [hs1, Real.zero_rpow hs_pos.ne', Real.one_rpow, sub_zero]
    have h4 : 1 / s.re ≤ 4 := by
      rw [div_le_iff₀ hs_pos]; linarith
    exact (norm_integral_le_integral_norm _).trans (hle_int.trans (hval.le.trans h4))
  rw [hzeta_eq]
  have hterm1 : ‖s / (s - 1)‖ ≤ 2 * ‖s‖ := by
    rw [norm_div]
    calc ‖s‖ / ‖s - 1‖ ≤ ‖s‖ / (1 / 2) := div_le_div_of_nonneg_left (norm_nonneg s) (by norm_num) h1
      _ = 2 * ‖s‖ := by ring
  calc ‖s / (s - 1) - s * ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖
      ≤ ‖s / (s - 1)‖ + ‖s * ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖ :=
        norm_sub_le _ _
    _ = ‖s / (s - 1)‖ + ‖s‖ * ‖∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖ := by
        rw [norm_mul]
    _ ≤ 2 * ‖s‖ + ‖s‖ * 4 := add_le_add hterm1 (mul_le_mul_of_nonneg_left hint_le (norm_nonneg s))
    _ = 6 * ‖s‖ := by ring

/-- Mellin transform of `{1 / (k * x)}` on `(0, ∞)` for `k ≥ 1` and `0 < Re(s) < 1`. -/
theorem mellin_recipFractScaled (k : ℝ) (hk : 1 ≤ k) (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    ∫ x in Ioi (0 : ℝ), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1) =
      -(riemannZeta s / (s * (k : ℂ) ^ s)) := by
  have hk_pos : (0 : ℝ) < k := by linarith
  have hk_ne : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk_pos.ne'
  have hs_ne_one : s ≠ 1 := fun h1 => by rw [h1] at hs; simp at hs
  have hpow_ne : (k : ℂ) ^ (s - 1) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hk_ne)
  have hscale := integral_comp_mul_left_Ioi
    (fun u : ℝ => (recipFract u : ℂ) * (u : ℂ) ^ (s - 1)) 0 hk_pos
  rw [mul_zero] at hscale
  have hcongr : ∫ x in Ioi (0 : ℝ),
      (recipFract (k * x) : ℂ) * ((k * x : ℝ) : ℂ) ^ (s - 1) =
      (k : ℂ) ^ (s - 1) * ∫ x in Ioi (0 : ℝ),
        (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hcp : ((k * x : ℝ) : ℂ) ^ (s - 1) = (k : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1) := by
      push_cast
      exact Complex.mul_cpow_ofReal_nonneg hk_pos.le (mem_Ioi.mp hx).le (s - 1)
    rw [hcp]
    change (recipFract (k * x) : ℂ) * ((k : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1)) =
      (k : ℂ) ^ (s - 1) * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1))
    unfold recipFractScaled recipFract
    ring
  have hmellin : ∫ x in Ioi (0 : ℝ), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      -(riemannZeta s / s) := by
    rw [mellin_recipFract_split s hs.1 hs.2, mellin_recipFract_unit_interval s hs.1 hs_ne_one,
      mellin_recipFract_tail s hs.2]
    ring
  rw [hcongr, hmellin] at hscale
  have hpow_s : (k : ℂ) ^ s = (k : ℂ) * (k : ℂ) ^ (s - 1) := by
    conv_lhs => rw [show s = 1 + (s - 1) from by ring, Complex.cpow_add _ _ hk_ne, Complex.cpow_one]
  have hsmul : (k⁻¹ : ℝ) • -(riemannZeta s / s) = (k : ℂ)⁻¹ * -(riemannZeta s / s) := by
    rw [Complex.real_smul, Complex.ofReal_inv]
  rw [hsmul] at hscale
  calc ∫ x in Ioi (0 : ℝ), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)
      = ((k : ℂ) ^ (s - 1))⁻¹ * ((k : ℂ) ^ (s - 1) *
          ∫ x in Ioi (0 : ℝ), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hpow_ne, one_mul]
    _ = ((k : ℂ) ^ (s - 1))⁻¹ * ((k : ℂ)⁻¹ * -(riemannZeta s / s)) := by rw [hscale]
    _ = -(riemannZeta s / (s * (k : ℂ) ^ s)) := by rw [hpow_s]; field_simp [hk_ne, hpow_ne]

/-- Mellin transform of `1_{(0, 1]}` on `(0, ∞)` for `Re(s) > 0`. -/
theorem mellin_indicator_Ioc (s : ℂ) (hs_pos : 0 < s.re) :
    ∫ x in Ioi (0 : ℝ), ((Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x : ℂ) * (x : ℂ) ^ (s - 1) =
      1 / s := by
  have hcongr : ∫ x in Ioi (0 : ℝ),
      ((Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x : ℂ) * (x : ℂ) ^ (s - 1) =
      ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (s - 1) := by
    rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioi]
    congr 1 with x
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx.1),
        Set.indicator_of_mem hx]
      simp
    · rw [Set.indicator_of_notMem hx]
      by_cases hx0 : x ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hx0, Set.indicator_of_notMem hx]; simp
      · rw [Set.indicator_of_notMem hx0]
  rw [hcongr, ← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl (by simp [Complex.sub_re]; linarith))]
  have hs1 : s - 1 + 1 = s := by ring
  have hs_ne : s ≠ 0 := fun h => by rw [h] at hs_pos; simp at hs_pos
  rw [hs1, Complex.ofReal_one, Complex.ofReal_zero, Complex.one_cpow, Complex.zero_cpow hs_ne,
    sub_zero]

/-- Change of variables `x = exp u` for integrals on `Ioi (0 : ℝ)`. -/
lemma integral_Ioi_eq_integral_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) :
    ∫ x in Ioi (0 : ℝ), F x = ∫ u : ℝ, Real.exp u • F (Real.exp u) := by
  have himg : Real.exp '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
    rw [image_univ]; exact Real.range_exp
  rw [← himg, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn,
    Measure.restrict_univ]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  dsimp only
  rw [abs_of_pos (Real.exp_pos u)]

/-- For `h ∈ L¹(ℝ) ∩ L²(ℝ)` whose pointwise Fourier transform `𝓕 h` is also in `L²(ℝ)`,
the `L²` Fourier transform `𝓕 (hh2.toLp h)` equals `hFh2.toLp (𝓕 h)`. -/
lemma fourier_toLp_eq_toLp_fourier {h : ℝ → ℂ} (hh1 : Integrable h volume)
    (hh2 : MemLp h 2 volume) (hFh2 : MemLp (𝓕 h) 2 volume) :
    𝓕 (hh2.toLp h) = hFh2.toLp (𝓕 h) := by
  apply ext_inner_left ℂ
  have hdense := SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2)
    (μ := volume) ENNReal.ofNat_ne_top
  intro y
  refine hdense.induction_on (p := fun y : Lp ℂ 2 volume =>
      ⟪y, 𝓕 (hh2.toLp h)⟫ = ⟪y, hFh2.toLp (𝓕 h)⟫) y ?_ ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · intro φ
    change ⟪φ.toLp 2 volume, 𝓕 (hh2.toLp h)⟫ = ⟪φ.toLp 2 volume, hFh2.toLp (𝓕 h)⟫
    have hL : ⟪φ.toLp 2 volume, 𝓕 (hh2.toLp h)⟫ = ⟪(𝓕⁻ φ).toLp 2 volume, hh2.toLp h⟫ := by
      symm
      rw [← SchwartzMap.toLp_fourierInv_eq φ, ← Lp.inner_fourier_eq,
        FourierInvPair.fourier_fourierInv_eq]
    rw [hL, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    have hLHS : ∫ u : ℝ, ⟪((𝓕⁻ φ).toLp 2 volume : ℝ → ℂ) u, (hh2.toLp h : ℝ → ℂ) u⟫ =
        ∫ u : ℝ, (starRingEnd ℂ (𝓕⁻ (φ : ℝ → ℂ) u)) * h u := by
      refine integral_congr_ae ?_
      filter_upwards [(𝓕⁻ φ).coeFn_toLp 2 volume, hh2.coeFn_toLp] with u hu1 hu2
      rw [hu1, hu2, RCLike.inner_apply, mul_comm, SchwartzMap.fourierInv_coe]
    have hRHS : ∫ ξ : ℝ, ⟪(φ.toLp 2 volume : ℝ → ℂ) ξ, (hFh2.toLp (𝓕 h) : ℝ → ℂ) ξ⟫ =
        ∫ ξ : ℝ, (starRingEnd ℂ (φ ξ)) * (𝓕 h ξ) := by
      refine integral_congr_ae ?_
      filter_upwards [φ.coeFn_toLp 2 volume, hFh2.coeFn_toLp] with ξ hξ1 hξ2
      rw [hξ1, hξ2, RCLike.inner_apply, mul_comm]
    rw [hLHS, hRHS]
    have hstar : ∀ u : ℝ, starRingEnd ℂ (𝓕⁻ (φ : ℝ → ℂ) u) =
        𝓕 (fun ξ : ℝ => starRingEnd ℂ (φ ξ)) u := by
      intro u
      rw [Real.fourierInv_eq', Real.fourier_eq', ← integral_conj]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_I, Complex.conj_ofReal,
        RCLike.inner_apply, conj_trivial]
      congr 2
      push_cast
      ring
    simp_rw [hstar]
    have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := innerₗ ℝ) (μ := volume) (ν := volume)
      (e := Real.fourierChar) Real.continuous_fourierChar
      (by fun_prop : Continuous fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2)
      (Complex.conjCLE.toContinuousLinearMap.integrable_comp (φ.integrable (μ := volume))) hh1
    simpa [FourierTransform.fourier, smul_eq_mul, mul_comm] using hflip

/-- Mellin-Plancherel isometry: for `g : ℝ → ℝ` whose log-transformed version
`h(u) = e^(u/2) g(e^u)` is in `L¹(ℝ) ∩ L²(ℝ)` and whose Mellin transform
`M(τ) = ∫_0^∞ g(x) x^(-1/2 + iτ) dx` is in `L²(ℝ)`, we have
`∫ x in Ioi 0, (g x)^2 = (2π)⁻¹ ∫ τ, ‖M τ‖^2`. -/
theorem mellin_plancherel (g : ℝ → ℝ)
    (hh1 : Integrable (fun u : ℝ => (Real.exp (u / 2) : ℂ) * (g (Real.exp u) : ℂ)) volume)
    (hh2 : MemLp (fun u : ℝ => (Real.exp (u / 2) : ℂ) * (g (Real.exp u) : ℂ)) 2 volume)
    (hM2 : MemLp (fun τ : ℝ => ∫ x in Ioi (0 : ℝ),
      (g x : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ) + (τ : ℂ) * Complex.I)) 2 volume) :
    ∫ x in Ioi (0 : ℝ), (g x) ^ 2 =
      (2 * Real.pi)⁻¹ * ∫ τ : ℝ,
        ‖∫ x in Ioi (0 : ℝ), (g x : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 := by
  let h : ℝ → ℂ := fun u => (Real.exp (u / 2) : ℂ) * (g (Real.exp u) : ℂ)
  let M : ℝ → ℂ := fun τ =>
    ∫ x in Ioi (0 : ℝ), (g x : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ) + (τ : ℂ) * Complex.I)
  have hFh_eq : ∀ ξ : ℝ, 𝓕 h ξ = M (-(2 * Real.pi) * ξ) := by
    intro ξ
    rw [Real.fourier_eq']
    dsimp [M]
    rw [integral_Ioi_eq_integral_exp]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    dsimp only
    have hexp_pos : 0 < Real.exp u := Real.exp_pos u
    have hcp : ((Real.exp u : ℝ) : ℂ) ^ (-(1 / 2 : ℂ) + ((-(2 * Real.pi) * ξ : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((-(1 / 2 : ℂ) + ((-(2 * Real.pi) * ξ : ℝ) : ℂ) * Complex.I)) * (u : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hexp_pos.ne'),
        ← Complex.ofReal_log hexp_pos.le, Real.log_exp, mul_comm]
    rw [Complex.real_smul, hcp, conj_trivial]
    dsimp [h]
    have hsplit_exp :
        Complex.exp (((-(1 / 2 : ℂ) + ((-(2 * Real.pi) * ξ : ℝ) : ℂ) * Complex.I)) * (u : ℂ)) =
        Complex.exp (-(u : ℂ) / 2) * Complex.exp (((-2 * Real.pi * (ξ * u) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit_exp]
    have hhalf : (Real.exp u : ℂ) * Complex.exp (-(u : ℂ) / 2) = (Real.exp (u / 2) : ℂ) := by
      rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc Complex.exp (((-2 * Real.pi * (ξ * u) : ℝ) : ℂ) * Complex.I) *
          ((Real.exp (u / 2) : ℂ) * (g (Real.exp u) : ℂ))
        = Complex.exp (((-2 * Real.pi * (ξ * u) : ℝ) : ℂ) * Complex.I) *
          (((Real.exp u : ℂ) * Complex.exp (-(u : ℂ) / 2)) * (g (Real.exp u) : ℂ)) := by rw [hhalf]
      _ = (Real.exp u : ℂ) * ((g (Real.exp u) : ℂ) *
          (Complex.exp (-(u : ℂ) / 2) *
            Complex.exp (((-2 * Real.pi * (ξ * u) : ℝ) : ℂ) * Complex.I))) := by ring
  have hFh2 : MemLp (𝓕 h) 2 volume := by
    have hne : (-(2 * Real.pi) : ℝ) ≠ 0 := neg_ne_zero.mpr (by positivity)
    have hM_sq : Integrable (fun τ : ℝ => ‖M τ‖ ^ 2) volume := hM2.norm.integrable_sq
    have hcomp_sq : Integrable (fun ξ : ℝ => ‖𝓕 h ξ‖ ^ 2) volume :=
      (hM_sq.comp_mul_left' hne).congr (ae_of_all _ fun ξ => by dsimp only; rw [hFh_eq])
    have hcont_Fh : Continuous (𝓕 h) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (by fun_prop : Continuous fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2) hh1
    exact (memLp_two_iff_integrable_sq_norm hcont_Fh.aestronglyMeasurable).mpr hcomp_sq
  have hplanch := Lp.norm_fourier_eq (hh2.toLp h)
  rw [fourier_toLp_eq_toLp_fourier hh1 hh2 hFh2] at hplanch
  have hsq : ‖hFh2.toLp (𝓕 h)‖ ^ 2 = ‖hh2.toLp h‖ ^ 2 := by rw [hplanch]
  have hnorm_sq : ∀ {f : ℝ → ℂ} (hf : MemLp f 2 volume),
      ‖hf.toLp f‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := fun {f} hf => by
    have hre := congrArg Complex.re (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (hf.toLp f))
    have hre' : ((‖hf.toLp f‖ : ℂ) ^ 2).re = ‖hf.toLp f‖ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have hnorm_eq : ‖hf.toLp f‖ ^ 2 = (⟪hf.toLp f, hf.toLp f⟫).re := hre'.symm.trans hre.symm
    rw [hnorm_eq, MeasureTheory.L2.inner_def]
    have hint : Integrable (fun x : ℝ => ⟪(hf.toLp f : ℝ → ℂ) x, (hf.toLp f : ℝ → ℂ) x⟫) volume :=
      L2.integrable_inner _ _
    change Complex.reCLM _ = _
    rw [← Complex.reCLM.integral_comp_comm hint]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
    change (⟪f x, f x⟫).re = ‖f x‖ ^ 2
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    have : ((‖f x‖ : ℂ) ^ 2).re = ‖f x‖ ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
    exact this
  rw [hnorm_sq hFh2, hnorm_sq hh2] at hsq
  have hLHS : ∫ x in Ioi (0 : ℝ), (g x) ^ 2 = ∫ u : ℝ, ‖h u‖ ^ 2 := by
    rw [integral_Ioi_eq_integral_exp]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    dsimp [h]
    rw [norm_mul, Complex.norm_real, Complex.norm_real, mul_pow,
      Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul,
      show (2 : ℕ) * (u / 2) = u by push_cast; ring, Real.norm_eq_abs, sq_abs]
  have hRHS : ∫ ξ : ℝ, ‖𝓕 h ξ‖ ^ 2 = (2 * Real.pi)⁻¹ * ∫ τ : ℝ, ‖M τ‖ ^ 2 := by
    have h1 : (fun ξ : ℝ => ‖𝓕 h ξ‖ ^ 2) = fun ξ : ℝ => ‖M (-(2 * Real.pi) * ξ)‖ ^ 2 := by
      ext ξ; rw [hFh_eq]
    rw [h1, Measure.integral_comp_mul_left (fun τ : ℝ => ‖M τ‖ ^ 2) (-(2 * Real.pi))]
    simp [abs_neg, abs_of_pos Real.pi_pos, smul_eq_mul]
  rw [hLHS, ← hsq, hRHS]

end BN2

/-
# Module 3: Unconditional Gamma/Zeta ratio bound (Baez-Duarte Lemma 2.2) and Term A convergence

Establishes:
1. Elementary bound `‖Γ(1/4 + ε/2 + iτ/2)‖ ≤ exp 1 * (1 + |τ|)^ε * ‖Γ(1/4 - ε/2 + iτ/2)‖`
   for `0 < ε ≤ 1/8` and all `τ : ℝ`, proved directly from `Complex.GammaSeq_tendsto_Gamma`.
2. Unconditional zeta ratio bound `‖ζ(1/2 - ε + iτ)‖ ≤ exp 1 * (1 + |τ|)^ε * ‖ζ(1/2 + ε + iτ)‖`
   via `completedRiemannZeta_one_sub` and `riemannZeta_conj`.
3. `∀ᵐ τ : ℝ, riemannZeta (1/2 + τ * I) ≠ 0` from isolated zeros of analytic functions.
4. Dominated convergence of Term A to `0` as `ε ↓ 0`.
-/

namespace BN3
open MeasureTheory Set Filter Complex
open scoped Topology

/-- Telescoping upper bound `∑_{k=M}^n 1 / k^2 ≤ 1 / (M - 1)` for `2 ≤ M`. -/
private lemma sum_inv_sq_Icc_le {M n : ℕ} (hM : 2 ≤ M) :
    ∑ k ∈ Finset.Icc M n, (1 : ℝ) / ((k : ℝ) ^ 2) ≤ 1 / ((M : ℝ) - 1) := by
  rcases lt_or_ge n M with hlt | hle
  · rw [Finset.Icc_eq_empty (not_le.mpr hlt), Finset.sum_empty]
    have : (0 : ℝ) < (M : ℝ) - 1 := by
      have : (2 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    positivity
  · calc ∑ k ∈ Finset.Icc M n, (1 : ℝ) / ((k : ℝ) ^ 2)
        ≤ ∑ k ∈ Finset.Icc M n, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkM : 2 ≤ k := le_trans hM (Finset.mem_Icc.mp hk).1
          have hk_pos : (0 : ℝ) < k := by positivity
          have hk1_pos : (0 : ℝ) < (k : ℝ) - 1 := by
            have : (2 : ℝ) ≤ k := by exact_mod_cast hkM
            linarith
          have hsub : 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) = 1 / (((k : ℝ) - 1) * (k : ℝ)) := by
            field_simp [hk1_pos.ne', hk_pos.ne']
            ring
          rw [hsub]
          exact one_div_le_one_div_of_le (mul_pos hk1_pos hk_pos) (by nlinarith)
      _ = 1 / ((M : ℝ) - 1) - 1 / (n : ℝ) := by
          clear hM
          induction n, hle using Nat.le_induction with
          | base => simp
          | succ n hMn ih =>
            rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hMn), ih]
            push_cast
            ring
      _ ≤ 1 / ((M : ℝ) - 1) := by
          have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
          linarith

/-- Telescoping lower bound `∑_{k=M}^n 1 / (k + 1) ≥ log (n + 2) - log (M + 1)` for `M ≤ n`. -/
private lemma log_sub_log_le_sum_inv_succ {M n : ℕ} (hle : M ≤ n) :
    Real.log ((n : ℝ) + 2) - Real.log ((M : ℝ) + 1) ≤
      ∑ k ∈ Finset.Icc M n, (1 : ℝ) / ((k : ℝ) + 1) := by
  calc Real.log ((n : ℝ) + 2) - Real.log ((M : ℝ) + 1)
      = ∑ k ∈ Finset.Icc M n, (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) := by
        induction n, hle using Nat.le_induction with
        | base => simp
        | succ n hMn ih =>
          rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hMn), ← ih]
          push_cast
          ring
    _ ≤ ∑ k ∈ Finset.Icc M n, (1 : ℝ) / ((k : ℝ) + 1) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have h2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        rw [← Real.log_div h2.ne' h1.ne']
        have hle' := Real.log_le_sub_one_of_pos (div_pos h2 h1)
        have heq : ((k : ℝ) + 2) / ((k : ℝ) + 1) - 1 = 1 / ((k : ℝ) + 1) := by
          field_simp [h1.ne']; ring
        rwa [heq] at hle'

set_option maxHeartbeats 600000 in
/-- Elementary bound on the Gamma ratio on vertical lines near `Re(z) = 1/4`,
proved directly from `Complex.GammaSeq_tendsto_Gamma`. -/
theorem norm_gamma_ratio_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8) (τ : ℝ) :
    ‖Complex.Gamma ((1 / 4 : ℂ) + (ε / 2 : ℂ) + (τ / 2 : ℂ) * I)‖ ≤
      Real.exp 1 * (1 + |τ|) ^ ε *
        ‖Complex.Gamma ((1 / 4 : ℂ) - (ε / 2 : ℂ) + (τ / 2 : ℂ) * I)‖ := by
  set a : ℝ := 1 / 4
  set b : ℝ := ε / 2
  set y : ℝ := τ / 2
  set z₁ : ℂ := ((a + b : ℝ) : ℂ) + (y : ℂ) * I
  set z₂ : ℂ := ((a - b : ℝ) : ℂ) + (y : ℂ) * I
  have hz₁_eq : (1 / 4 : ℂ) + (ε / 2 : ℂ) + (τ / 2 : ℂ) * I = z₁ := by
    dsimp [z₁, a, b, y]; push_cast; ring
  have hz₂_eq : (1 / 4 : ℂ) - (ε / 2 : ℂ) + (τ / 2 : ℂ) * I = z₂ := by
    dsimp [z₂, a, b, y]; push_cast; ring
  rw [hz₁_eq, hz₂_eq]
  have hb0 : 0 < b := by dsimp [b]; linarith
  have hb1 : b ≤ 1 / 16 := by dsimp [b]; linarith
  have hab_lt : a + b < 1 := by dsimp [a, b]; linarith
  have ham_pos : 0 < a - b := by dsimp [a, b]; linarith
  have hG₂_ne : Complex.Gamma z₂ ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp [z₂, ham_pos])
  have hG₂_pos : 0 < ‖Complex.Gamma z₂‖ := norm_pos_iff.mpr hG₂_ne
  suffices hdiv : ‖Complex.Gamma z₁‖ / ‖Complex.Gamma z₂‖ ≤ Real.exp 1 * (1 + |τ|) ^ ε by
    exact (div_le_iff₀ hG₂_pos).mp hdiv
  have htend : Tendsto (fun n : ℕ => ‖Complex.GammaSeq z₁ n‖ / ‖Complex.GammaSeq z₂ n‖)
      atTop (𝓝 (‖Complex.Gamma z₁‖ / ‖Complex.Gamma z₂‖)) :=
    (Complex.GammaSeq_tendsto_Gamma z₁).norm.div (Complex.GammaSeq_tendsto_Gamma z₂).norm hG₂_pos.ne'
  let M : ℕ := Nat.ceil |y| + 2
  have hM2 : 2 ≤ M := by dsimp [M]; omega
  have hM_y : |y| ≤ (M : ℝ) - 1 := by
    have hc : |y| ≤ (Nat.ceil |y| : ℝ) := Nat.le_ceil |y|
    have hMcast : (M : ℝ) = (Nat.ceil |y| : ℝ) + 2 := by dsimp [M]; push_cast; rfl
    linarith
  have hbound_ev : ∀ᶠ n : ℕ in atTop,
      ‖Complex.GammaSeq z₁ n‖ / ‖Complex.GammaSeq z₂ n‖ ≤ Real.exp 1 * (1 + |τ|) ^ ε := by
    filter_upwards [eventually_ge_atTop M] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < M) hn)
    have hfact_pos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hterm_pos₁ : ∀ k : ℕ, 0 < ‖z₁ + (k : ℂ)‖ := fun k =>
      norm_pos_iff.mpr fun h => by
        have := congrArg Complex.re h
        simp [z₁] at this
        linarith [Nat.cast_nonneg (α := ℝ) k]
    have hterm_pos₂ : ∀ k : ℕ, 0 < ‖z₂ + (k : ℂ)‖ := fun k =>
      norm_pos_iff.mpr fun h => by
        have := congrArg Complex.re h
        simp [z₂] at this
        linarith [Nat.cast_nonneg (α := ℝ) k]
    have hprod_pos₁ : 0 < ∏ k ∈ Finset.range (n + 1), ‖z₁ + (k : ℂ)‖ :=
      Finset.prod_pos fun k _ => hterm_pos₁ k
    have hprod_pos₂ : 0 < ∏ k ∈ Finset.range (n + 1), ‖z₂ + (k : ℂ)‖ :=
      Finset.prod_pos fun k _ => hterm_pos₂ k
    have hratio_eq : ‖Complex.GammaSeq z₁ n‖ / ‖Complex.GammaSeq z₂ n‖ =
        (n : ℝ) ^ (2 * b) * ∏ k ∈ Finset.range (n + 1), (‖z₂ + (k : ℂ)‖ / ‖z₁ + (k : ℂ)‖) := by
      unfold Complex.GammaSeq
      rw [norm_div, norm_div, norm_mul, norm_mul, norm_prod, norm_prod, Complex.norm_natCast]
      have hn1 : ‖(n : ℂ) ^ z₁‖ = (n : ℝ) ^ (a + b) := by
        rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]; simp [z₁]
      have hn2 : ‖(n : ℂ) ^ z₂‖ = (n : ℝ) ^ (a - b) := by
        rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]; simp [z₂]
      rw [hn1, hn2, Finset.prod_div_distrib]
      have hrpow : (n : ℝ) ^ (a + b) / (n : ℝ) ^ (a - b) = (n : ℝ) ^ (2 * b) := by
        rw [← Real.rpow_sub hn_pos]
        congr 1; ring
      rw [← hrpow]
      field_simp [hfact_pos.ne', hprod_pos₁.ne', hprod_pos₂.ne',
        (Real.rpow_pos_of_pos hn_pos (a - b)).ne']
    rw [hratio_eq]
    have hLHS_pos : 0 < (n : ℝ) ^ (2 * b) *
        ∏ k ∈ Finset.range (n + 1), (‖z₂ + (k : ℂ)‖ / ‖z₁ + (k : ℂ)‖) :=
      mul_pos (Real.rpow_pos_of_pos hn_pos _)
        (Finset.prod_pos fun k _ => div_pos (hterm_pos₂ k) (hterm_pos₁ k))
    have hRHS_pos : 0 < Real.exp 1 * (1 + |τ|) ^ ε := by positivity
    rw [← Real.log_le_log_iff hLHS_pos hRHS_pos]
    rw [Real.log_mul (Real.rpow_pos_of_pos hn_pos _).ne'
      (Finset.prod_pos fun k _ => div_pos (hterm_pos₂ k) (hterm_pos₁ k)).ne',
      Real.log_rpow hn_pos,
      Real.log_prod fun k _ => (div_pos (hterm_pos₂ k) (hterm_pos₁ k)).ne',
      Real.log_mul (Real.exp_pos 1).ne' (Real.rpow_pos_of_pos (by positivity) ε).ne',
      Real.log_exp, Real.log_rpow (by positivity : (0 : ℝ) < 1 + |τ|)]
    have hterm_le : ∀ k : ℕ,
        Real.log (‖z₂ + (k : ℂ)‖ / ‖z₁ + (k : ℂ)‖) ≤
          -(2 * b * (a + (k : ℝ)) / ((a + b + (k : ℝ)) ^ 2 + y ^ 2)) := by
      intro k
      have hsq₁ : ‖z₁ + (k : ℂ)‖ ^ 2 = (a + b + (k : ℝ)) ^ 2 + y ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [z₁]; ring
      have hsq₂ : ‖z₂ + (k : ℂ)‖ ^ 2 = (a - b + (k : ℝ)) ^ 2 + y ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [z₂]; ring
      have hposA : 0 < (a + b + (k : ℝ)) ^ 2 + y ^ 2 := by rw [← hsq₁]; exact pow_pos (hterm_pos₁ k) 2
      have hposB : 0 < (a - b + (k : ℝ)) ^ 2 + y ^ 2 := by rw [← hsq₂]; exact pow_pos (hterm_pos₂ k) 2
      have hlog_sq : Real.log (‖z₂ + (k : ℂ)‖ / ‖z₁ + (k : ℂ)‖) =
          (1 / 2 : ℝ) * Real.log (((a - b + (k : ℝ)) ^ 2 + y ^ 2) / ((a + b + (k : ℝ)) ^ 2 + y ^ 2)) := by
        rw [← hsq₁, ← hsq₂, ← div_pow, Real.log_pow]
        push_cast; ring
      rw [hlog_sq]
      have hle_log := Real.log_le_sub_one_of_pos (div_pos hposB hposA)
      have hdiff : ((a - b + (k : ℝ)) ^ 2 + y ^ 2) / ((a + b + (k : ℝ)) ^ 2 + y ^ 2) - 1 =
          -(4 * b * (a + (k : ℝ))) / ((a + b + (k : ℝ)) ^ 2 + y ^ 2) := by
        field_simp [hposA.ne']
        ring
      rw [hdiff] at hle_log
      have hhalf : (1 / 2 : ℝ) * (-(4 * b * (a + (k : ℝ))) / ((a + b + (k : ℝ)) ^ 2 + y ^ 2)) =
          -(2 * b * (a + (k : ℝ)) / ((a + b + (k : ℝ)) ^ 2 + y ^ 2)) := by ring
      linarith
    have hterm_nonpos : ∀ k : ℕ, Real.log (‖z₂ + (k : ℂ)‖ / ‖z₁ + (k : ℂ)‖) ≤ 0 := fun k =>
      (hterm_le k).trans (neg_nonpos.mpr (by positivity))
    have hsub_fin : Finset.Icc M n ⊆ Finset.range (n + 1) := by
      intro k hk
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2
    have hsum_drop : ∑ k ∈ Finset.range (n + 1), Real.log (‖z₂ + (k : ℂ)‖ / ‖z₁ + (k : ℂ)‖) ≤
        ∑ k ∈ Finset.Icc M n, Real.log (‖z₂ + (k : ℂ)‖ / ‖z₁ + (k : ℂ)‖) := by
      rw [← Finset.sum_sdiff hsub_fin]
      have hsdiff : ∑ k ∈ Finset.range (n + 1) \ Finset.Icc M n,
          Real.log (‖z₂ + (k : ℂ)‖ / ‖z₁ + (k : ℂ)‖) ≤ 0 :=
        Finset.sum_nonpos fun k _ => hterm_nonpos k
      linarith
    have hsum_bound : ∑ k ∈ Finset.Icc M n, Real.log (‖z₂ + (k : ℂ)‖ / ‖z₁ + (k : ℂ)‖) ≤
        -(2 * b) * ∑ k ∈ Finset.Icc M n, ((a + (k : ℝ)) / ((a + b + (k : ℝ)) ^ 2 + y ^ 2)) := by
      calc ∑ k ∈ Finset.Icc M n, Real.log (‖z₂ + (k : ℂ)‖ / ‖z₁ + (k : ℂ)‖)
          ≤ ∑ k ∈ Finset.Icc M n, -(2 * b * (a + (k : ℝ)) / ((a + b + (k : ℝ)) ^ 2 + y ^ 2)) :=
            Finset.sum_le_sum fun k _ => hterm_le k
        _ = -(2 * b) * ∑ k ∈ Finset.Icc M n, ((a + (k : ℝ)) / ((a + b + (k : ℝ)) ^ 2 + y ^ 2)) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    have htail_diff :
        ∑ k ∈ Finset.Icc M n, (1 / ((k : ℝ) + 1) - (a + (k : ℝ)) / ((a + b + (k : ℝ)) ^ 2 + y ^ 2)) ≤ 2 := by
      have hpt : ∀ k ∈ Finset.Icc M n,
          1 / ((k : ℝ) + 1) - (a + (k : ℝ)) / ((a + b + (k : ℝ)) ^ 2 + y ^ 2) ≤
            (1 + (M : ℝ) - 1) * (1 / ((k : ℝ) ^ 2)) := by
        intro k hk
        have hkM : M ≤ k := (Finset.mem_Icc.mp hk).1
        have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (le_trans hM2 hkM)
        have hk_pos : (0 : ℝ) < k := by linarith
        have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
        have hM1_pos : (0 : ℝ) < (M : ℝ) - 1 := by
          have : (2 : ℝ) ≤ M := by exact_mod_cast hM2
          linarith
        have hM_le_k : (M : ℝ) ≤ k := by exact_mod_cast hkM
        have hden_le : (a + b + (k : ℝ)) ^ 2 + y ^ 2 ≤ ((k : ℝ) + 1) ^ 2 + y ^ 2 := by
          nlinarith
        have hstep1 : (k : ℝ) / (((k : ℝ) + 1) ^ 2 + y ^ 2) ≤
            (a + (k : ℝ)) / ((a + b + (k : ℝ)) ^ 2 + y ^ 2) := by
          calc (k : ℝ) / (((k : ℝ) + 1) ^ 2 + y ^ 2)
              ≤ (a + (k : ℝ)) / (((k : ℝ) + 1) ^ 2 + y ^ 2) :=
                div_le_div_of_nonneg_right (by dsimp [a]; linarith) (by positivity)
            _ ≤ (a + (k : ℝ)) / ((a + b + (k : ℝ)) ^ 2 + y ^ 2) :=
                div_le_div_of_nonneg_left (by dsimp [a]; positivity) (by positivity) hden_le
        have hstep2 : 1 / ((k : ℝ) + 1) - (k : ℝ) / (((k : ℝ) + 1) ^ 2 + y ^ 2) =
            ((k : ℝ) + 1 + y ^ 2) / (((k : ℝ) + 1) * (((k : ℝ) + 1) ^ 2 + y ^ 2)) := by
          field_simp [hk1_pos.ne', (show 0 < ((k : ℝ) + 1) ^ 2 + y ^ 2 by positivity).ne']
          ring
        have hy2 : y ^ 2 ≤ ((M : ℝ) - 1) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg y) hM_y 2
        have hstep3 : ((k : ℝ) + 1 + y ^ 2) / (((k : ℝ) + 1) * (((k : ℝ) + 1) ^ 2 + y ^ 2)) ≤
            1 / ((k : ℝ) ^ 2) + ((M : ℝ) - 1) * (1 / ((k : ℝ) ^ 2)) := by
          have hA : ((k : ℝ) + 1) / (((k : ℝ) + 1) * (((k : ℝ) + 1) ^ 2 + y ^ 2)) ≤
              1 / ((k : ℝ) ^ 2) := by
            rw [div_mul_eq_div_div, div_self hk1_pos.ne']
            exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
          have hB : y ^ 2 / (((k : ℝ) + 1) * (((k : ℝ) + 1) ^ 2 + y ^ 2)) ≤
              ((M : ℝ) - 1) * (1 / ((k : ℝ) ^ 2)) := by
            have hden_ge : (k : ℝ) ^ 3 ≤ ((k : ℝ) + 1) * (((k : ℝ) + 1) ^ 2 + y ^ 2) := by
              nlinarith [sq_nonneg y]
            calc y ^ 2 / (((k : ℝ) + 1) * (((k : ℝ) + 1) ^ 2 + y ^ 2))
                ≤ ((M : ℝ) - 1) ^ 2 / ((k : ℝ) ^ 3) :=
                  div_le_div₀ (by positivity) hy2 (by positivity) hden_ge
              _ ≤ ((M : ℝ) - 1) * (1 / ((k : ℝ) ^ 2)) := by
                  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
                  have h1 : ((M : ℝ) - 1) ^ 2 * (k : ℝ) ^ 2 = ((M : ℝ) - 1) * ((M : ℝ) - 1) * (k : ℝ) ^ 2 := by ring
                  have h2 : ((M : ℝ) - 1) * (k : ℝ) ^ 3 = ((M : ℝ) - 1) * (k : ℝ) * (k : ℝ) ^ 2 := by ring
                  rw [h1, h2]
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left (by linarith : (M : ℝ) - 1 ≤ (k : ℝ)) hM1_pos.le)
                    (sq_nonneg _)
          have hadd : ((k : ℝ) + 1 + y ^ 2) / (((k : ℝ) + 1) * (((k : ℝ) + 1) ^ 2 + y ^ 2)) =
              ((k : ℝ) + 1) / (((k : ℝ) + 1) * (((k : ℝ) + 1) ^ 2 + y ^ 2)) +
              y ^ 2 / (((k : ℝ) + 1) * (((k : ℝ) + 1) ^ 2 + y ^ 2)) := add_div _ _ _
          rw [hadd]
          exact add_le_add hA hB
        linarith
      calc ∑ k ∈ Finset.Icc M n, (1 / ((k : ℝ) + 1) - (a + (k : ℝ)) / ((a + b + (k : ℝ)) ^ 2 + y ^ 2))
          ≤ ∑ k ∈ Finset.Icc M n, ((1 + (M : ℝ) - 1) * (1 / ((k : ℝ) ^ 2))) :=
            Finset.sum_le_sum hpt
        _ = (M : ℝ) * ∑ k ∈ Finset.Icc M n, (1 / ((k : ℝ) ^ 2)) := by
            rw [← Finset.mul_sum]; congr 1; ring
        _ ≤ (M : ℝ) * (1 / ((M : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le hM2) (Nat.cast_nonneg M)
        _ ≤ 2 := by
            have hM1_pos : (0 : ℝ) < (M : ℝ) - 1 := by
              have : (2 : ℝ) ≤ M := by exact_mod_cast hM2
              linarith
            rw [mul_one_div, div_le_iff₀ hM1_pos]
            have : (2 : ℝ) ≤ M := by exact_mod_cast hM2
            linarith
    have hlog_n : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_le_log hn_pos (by linarith)
    have hsum_harm := log_sub_log_le_sum_inv_succ hn
    have hsum_diff :
        Real.log (n : ℝ) - ∑ k ∈ Finset.Icc M n, ((a + (k : ℝ)) / ((a + b + (k : ℝ)) ^ 2 + y ^ 2)) ≤
          Real.log ((M : ℝ) + 1) + 2 := by
      rw [Finset.sum_sub_distrib] at htail_diff
      linarith
    have hM1_le : (M : ℝ) + 1 ≤ 4 * (1 + |τ|) := by
      have hceil : (Nat.ceil |y| : ℝ) < |y| + 1 := Nat.ceil_lt_add_one (abs_nonneg y)
      have hy_abs : |y| = |τ| / 2 := by dsimp [y]; rw [abs_div, abs_two]
      have hMcast : (M : ℝ) = (Nat.ceil |y| : ℝ) + 2 := by dsimp [M]; push_cast; rfl
      linarith [abs_nonneg τ]
    have hlog_M1 : Real.log ((M : ℝ) + 1) ≤ Real.log 4 + Real.log (1 + |τ|) := by
      have h1 : Real.log ((M : ℝ) + 1) ≤ Real.log (4 * (1 + |τ|)) :=
        Real.log_le_log (by positivity) hM1_le
      rwa [Real.log_mul (by norm_num) (by positivity)] at h1
    have hlog4_le : Real.log 4 ≤ 2 := by
      have h4 : (4 : ℝ) ≤ Real.exp 2 := by
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        have he1 := Real.add_one_le_exp (1 : ℝ)
        nlinarith [Real.exp_pos 1]
      calc Real.log 4 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) h4
        _ = 2 := Real.log_exp 2
    have h2b : 2 * b = ε := by dsimp [b]; ring
    have hconst : ε * (Real.log 4 + 2) ≤ 1 := by
      nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
    calc 2 * b * Real.log (n : ℝ) +
          ∑ k ∈ Finset.range (n + 1), Real.log (‖z₂ + (k : ℂ)‖ / ‖z₁ + (k : ℂ)‖)
        ≤ 2 * b * Real.log (n : ℝ) +
          ∑ k ∈ Finset.Icc M n, Real.log (‖z₂ + (k : ℂ)‖ / ‖z₁ + (k : ℂ)‖) := by linarith
      _ ≤ 2 * b * (Real.log (n : ℝ) -
          ∑ k ∈ Finset.Icc M n, ((a + (k : ℝ)) / ((a + b + (k : ℝ)) ^ 2 + y ^ 2))) := by linarith
      _ ≤ ε * (Real.log ((M : ℝ) + 1) + 2) := by
          rw [h2b]; exact mul_le_mul_of_nonneg_left hsum_diff hε0.le
      _ ≤ ε * (Real.log 4 + Real.log (1 + |τ|) + 2) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hε0.le
      _ = ε * (Real.log 4 + 2) + ε * Real.log (1 + |τ|) := by ring
      _ ≤ 1 + ε * Real.log (1 + |τ|) := by linarith
  exact le_of_tendsto htend hbound_ev

/-- Unconditional zeta ratio bound (Baez-Duarte Lemma 2.2):
for `0 < ε ≤ 1/8` and all `τ : ℝ`,
`‖ζ(1/2 - ε + iτ)‖ ≤ exp 1 * (1 + |τ|)^ε * ‖ζ(1/2 + ε + iτ)‖`. -/
theorem norm_zeta_ratio_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8) (τ : ℝ) :
    ‖riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I)‖ ≤
      Real.exp 1 * (1 + |τ|) ^ ε *
        ‖riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ := by
  set s : ℂ := (1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I
  have hs_re : s.re = 1 / 2 + ε := by simp [s]
  have h1s_re : (1 - s).re = 1 / 2 - ε := by simp [s]; ring
  have hs_ne0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs_re; linarith
  have h1s_ne0 : 1 - s ≠ 0 := fun h => by rw [h, Complex.zero_re] at h1s_re; linarith
  have hs_gamma_ne : s.Gammaℝ ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      (Complex.Gamma_ne_zero_of_re_pos (by simp [hs_re]; linarith))
  have h1s_gamma_ne : (1 - s).Gammaℝ ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      (Complex.Gamma_ne_zero_of_re_pos (by simp [h1s_re]; linarith))
  have hfe : riemannZeta (1 - s) * (1 - s).Gammaℝ = riemannZeta s * s.Gammaℝ := by
    rw [riemannZeta_def_of_ne_zero h1s_ne0, riemannZeta_def_of_ne_zero hs_ne0,
      div_mul_cancel₀ _ h1s_gamma_ne, div_mul_cancel₀ _ hs_gamma_ne, completedRiemannZeta_one_sub]
  have hconj_s : 1 - s = starRingEnd ℂ ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) := by
    apply Complex.ext
    · simp [s]; ring
    · simp [s]
  have hnorm_zeta : ‖riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I)‖ = ‖riemannZeta (1 - s)‖ := by
    rw [hconj_s, riemannZeta_conj, Complex.norm_conj]
  have hnorm_eq := congrArg norm hfe
  simp only [norm_mul] at hnorm_eq
  have hGammaR_s : ‖s.Gammaℝ‖ = Real.pi ^ (-(1 / 4 + ε / 2)) *
      ‖Complex.Gamma ((1 / 4 : ℂ) + (ε / 2 : ℂ) + (τ / 2 : ℂ) * I)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    · congr 1; simp [s]; ring
    · congr 1; dsimp [s]; ring
  have hGammaR_1s : ‖(1 - s).Gammaℝ‖ = Real.pi ^ (-(1 / 4 - ε / 2)) *
      ‖Complex.Gamma ((1 / 4 : ℂ) - (ε / 2 : ℂ) + (τ / 2 : ℂ) * I)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hconj_g : (1 - s) / 2 = starRingEnd ℂ ((1 / 4 : ℂ) - (ε / 2 : ℂ) + (τ / 2 : ℂ) * I) := by
      have h1 : (1 - s) / 2 = ((1 / 4 - ε / 2 : ℝ) : ℂ) + ((-(τ / 2) : ℝ) : ℂ) * I := by
        dsimp [s]; push_cast; ring
      have h2 : (1 / 4 : ℂ) - (ε / 2 : ℂ) + (τ / 2 : ℂ) * I =
          ((1 / 4 - ε / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I := by push_cast; ring
      rw [h1, h2, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [hconj_g, Complex.Gamma_conj, Complex.norm_conj]
    congr 1
    congr 1; simp [s]; ring
  rw [hGammaR_s, hGammaR_1s] at hnorm_eq
  have hpi_le : Real.pi ^ (-(1 / 4 + ε / 2)) ≤ Real.pi ^ (-(1 / 4 - ε / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
  have hG_pos : 0 < ‖Complex.Gamma ((1 / 4 : ℂ) - (ε / 2 : ℂ) + (τ / 2 : ℂ) * I)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  have hpi_pos : 0 < Real.pi ^ (-(1 / 4 - ε / 2)) := Real.rpow_pos_of_pos Real.pi_pos _
  have hmul_pos : 0 < Real.pi ^ (-(1 / 4 - ε / 2)) *
      ‖Complex.Gamma ((1 / 4 : ℂ) - (ε / 2 : ℂ) + (τ / 2 : ℂ) * I)‖ := mul_pos hpi_pos hG_pos
  have hgr := norm_gamma_ratio_le hε0 hε1 τ
  rw [hnorm_zeta]
  have hstep : ‖riemannZeta (1 - s)‖ * (Real.pi ^ (-(1 / 4 - ε / 2)) *
      ‖Complex.Gamma ((1 / 4 : ℂ) - (ε / 2 : ℂ) + (τ / 2 : ℂ) * I)‖) ≤
      (Real.exp 1 * (1 + |τ|) ^ ε * ‖riemannZeta s‖) *
      (Real.pi ^ (-(1 / 4 - ε / 2)) *
        ‖Complex.Gamma ((1 / 4 : ℂ) - (ε / 2 : ℂ) + (τ / 2 : ℂ) * I)‖) := by
    rw [hnorm_eq]
    calc ‖riemannZeta s‖ * (Real.pi ^ (-(1 / 4 + ε / 2)) *
            ‖Complex.Gamma ((1 / 4 : ℂ) + (ε / 2 : ℂ) + (τ / 2 : ℂ) * I)‖)
        ≤ ‖riemannZeta s‖ * (Real.pi ^ (-(1 / 4 - ε / 2)) *
            (Real.exp 1 * (1 + |τ|) ^ ε *
              ‖Complex.Gamma ((1 / 4 : ℂ) - (ε / 2 : ℂ) + (τ / 2 : ℂ) * I)‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact mul_le_mul hpi_le hgr (norm_nonneg _) hpi_pos.le
      _ = (Real.exp 1 * (1 + |τ|) ^ ε * ‖riemannZeta s‖) *
          (Real.pi ^ (-(1 / 4 - ε / 2)) *
            ‖Complex.Gamma ((1 / 4 : ℂ) - (ε / 2 : ℂ) + (τ / 2 : ℂ) * I)‖) := by ring
  exact le_of_mul_le_mul_right hstep hmul_pos

/-- Under `RiemannHypothesis`, `riemannZeta s ≠ 0` whenever `1/2 < s.re` and `s ≠ 1`. -/
lemma riemannZeta_ne_zero_of_rh (rh : RiemannHypothesis) {s : ℂ} (hre : (1 / 2 : ℝ) < s.re)
    (h1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hnot : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, rfl⟩
    have := congrArg Complex.re (rfl : (-2 * ((n : ℂ) + 1)) = (-2 * ((n : ℂ) + 1)))
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have heq := rh s hz hnot h1
  linarith

/-- Almost every point on the critical line `Re(s) = 1/2` is not a zero of `riemannZeta`. -/
lemma ae_riemannZeta_half_ne_zero :
    ∀ᵐ τ : ℝ ∂volume, riemannZeta ((1 / 2 : ℂ) + (τ : ℂ) * I) ≠ 0 := by
  let Z : Set ℝ := {τ : ℝ | riemannZeta ((1 / 2 : ℂ) + (τ : ℂ) * I) = 0}
  suffices hcount : Z.Countable by
    rw [ae_iff]
    simpa [Z] using hcount.measure_zero volume
  have hS_open : IsOpen ({z : ℂ | z ≠ 1} : Set ℂ) := isOpen_ne
  have hana : AnalyticOnNhd ℂ riemannZeta {z : ℂ | z ≠ 1} :=
    DifferentiableOn.analyticOnNhd (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
      hS_open
  have hS_preconn : IsPreconnected ({z : ℂ | z ≠ 1} : Set ℂ) := by
    have : ({z : ℂ | z ≠ 1} : Set ℂ) = ({1}ᶜ : Set ℂ) := rfl
    rw [this]
    have hrank : 1 < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      norm_num
    exact (isConnected_compl_singleton_of_one_lt_rank hrank (1 : ℂ)).isPreconnected
  have hisol : ∀ τ ∈ Z, ∃ r > 0, ∀ τ' ∈ Metric.ball τ r, τ' ≠ τ → τ' ∉ Z := by
    intro τ _
    set z₀ : ℂ := (1 / 2 : ℂ) + (τ : ℂ) * I
    have hz₀_ne1 : z₀ ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp [z₀] at this
    have hnot_eq0 : ¬∀ᶠ z in 𝓝 z₀, riemannZeta z = 0 := by
      intro h0
      have heq := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hS_preconn hz₀_ne1 h0
      have h2 : riemannZeta (2 : ℂ) = 0 := heq (by norm_num)
      exact riemannZeta_ne_zero_of_one_lt_re (by norm_num : 1 < (2 : ℂ).re) h2
    have hev := (hana z₀ hz₀_ne1).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnot_eq0
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨r, hr, hball⟩ := hev
    refine ⟨r, hr, fun τ' hτ' hne hmem => ?_⟩
    set z' : ℂ := (1 / 2 : ℂ) + (τ' : ℂ) * I
    have hdist : dist z' z₀ < r := by
      have : z' - z₀ = ((τ' - τ : ℝ) : ℂ) * I := by dsimp [z', z₀]; push_cast; ring
      rw [dist_eq_norm, this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
      simpa [Real.dist_eq] using hτ'
    have hne_z : z' ≠ z₀ := fun h => hne (by
      have := congrArg Complex.im h; simp [z', z₀] at this; exact this)
    exact hball hdist hne_z hmem
  have hrat : ∀ τ : Z, ∃ q : ℚ, τ.1 < (q : ℝ) ∧ ∀ τ' : Z, τ'.1 < (q : ℝ) → τ'.1 ≤ τ.1 := by
    intro ⟨τ, hτ⟩
    obtain ⟨r, hr, hball⟩ := hisol τ hτ
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show τ < τ + r by linarith)
    refine ⟨q, hq1, fun ⟨τ', hτ'⟩ hlt => ?_⟩
    by_contra hnot
    push Not at hnot
    have hdist : τ' ∈ Metric.ball τ r := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hnot)]
      linarith
    exact hball τ' hdist (ne_of_gt hnot) hτ'
  choose f hf1 hf2 using hrat
  have hinj : Function.Injective f := by
    intro a b hab
    have hle1 : a.1 ≤ b.1 := by
      by_contra h
      push Not at h
      have := hf2 b a (by rw [← hab]; exact hf1 a)
      linarith
    have hle2 : b.1 ≤ a.1 := by
      by_contra h
      push Not at h
      have := hf2 a b (by rw [hab]; exact hf1 b)
      linarith
    exact Subtype.ext (le_antisymm hle1 hle2)
  exact Set.countable_coe_iff.mp (Function.Injective.countable hinj)

/-- Integrability of the dominating function `(1 + exp 1 * (1 + |τ|)^(1/8))^2 / (1/16 + τ^2)`. -/
lemma integrable_dom_termA :
    Integrable (fun τ : ℝ => (1 + Real.exp 1 * (1 + |τ|) ^ (1 / 8 : ℝ)) ^ 2 / (1 / 16 + τ ^ 2))
      volume := by
  have hcont : Continuous (fun τ : ℝ =>
      (1 + Real.exp 1 * (1 + |τ|) ^ (1 / 8 : ℝ)) ^ 2 / (1 / 16 + τ ^ 2)) := by
    refine Continuous.div ?_ (by fun_prop) (fun τ => by positivity)
    exact (continuous_const.add (continuous_const.mul
      ((continuous_const.add continuous_abs).rpow_const fun _ => Or.inr (by norm_num)))).pow 2
  have hdom : Integrable (fun τ : ℝ => (32 * (1 + Real.exp 1) ^ 2) * (1 + |τ|) ^ (-3 / 2 : ℝ))
      volume := by
    have h1 : IntegrableOn (fun τ : ℝ => (1 + τ) ^ (-3 / 2 : ℝ)) (Ioi (0 : ℝ)) := by
      have hshift := integrableOn_Ioi_rpow_of_lt (a := (-3 / 2 : ℝ)) (by norm_num) (by norm_num : (0 : ℝ) < 1)
      rw [← integrable_indicator_iff measurableSet_Ioi] at hshift ⊢
      have hcomp := hshift.comp_add_right 1
      refine hcomp.congr (ae_of_all _ fun τ => ?_)
      dsimp only
      by_cases hτ : (0 : ℝ) < τ
      · rw [Set.indicator_of_mem (show τ + 1 ∈ Ioi (1 : ℝ) by simp; linarith),
          Set.indicator_of_mem (show τ ∈ Ioi (0 : ℝ) from hτ), add_comm]
      · rw [Set.indicator_of_notMem (show τ + 1 ∉ Ioi (1 : ℝ) by simp; linarith),
          Set.indicator_of_notMem (show τ ∉ Ioi (0 : ℝ) from hτ)]
    have heven : Integrable (fun τ : ℝ => (1 + |τ|) ^ (-3 / 2 : ℝ)) volume := by
      have hpos : IntegrableOn (fun τ : ℝ => (1 + |τ|) ^ (-3 / 2 : ℝ)) (Ioi (0 : ℝ)) :=
        h1.congr_fun (fun τ (hτ : 0 < τ) => by simp [abs_of_pos hτ]) measurableSet_Ioi
      have hneg : IntegrableOn (fun τ : ℝ => (1 + |τ|) ^ (-3 / 2 : ℝ)) (Iio (0 : ℝ)) := by
        rw [← integrable_indicator_iff measurableSet_Ioi] at hpos
        rw [← integrable_indicator_iff measurableSet_Iio]
        refine hpos.comp_neg.congr (ae_of_all _ fun τ => ?_)
        dsimp only
        by_cases hτ : τ < 0
        · rw [Set.indicator_of_mem (show -τ ∈ Ioi (0 : ℝ) by simp [hτ]),
            Set.indicator_of_mem (show τ ∈ Iio (0 : ℝ) from hτ), abs_neg]
        · rw [Set.indicator_of_notMem (show -τ ∉ Ioi (0 : ℝ) by simp; linarith),
            Set.indicator_of_notMem (show τ ∉ Iio (0 : ℝ) from hτ)]
      have hunion : IntegrableOn (fun τ : ℝ => (1 + |τ|) ^ (-3 / 2 : ℝ))
          (Ioi (0 : ℝ) ∪ Iio (0 : ℝ)) := hpos.union hneg
      rw [← integrableOn_univ]
      refine hunion.congr_set_ae ?_
      rw [ae_eq_set]
      have hdiff1 : (Ioi (0 : ℝ) ∪ Iio (0 : ℝ)) \ univ = ∅ := by simp
      have hdiff2 : univ \ (Ioi (0 : ℝ) ∪ Iio (0 : ℝ)) = {0} := by
        ext x; simp
      rw [hdiff1, hdiff2]
      simp
    exact heven.const_mul _
  refine hdom.mono' hcont.aestronglyMeasurable (ae_of_all _ fun τ => ?_)
  have hpos : 0 ≤ (1 + Real.exp 1 * (1 + |τ|) ^ (1 / 8 : ℝ)) ^ 2 / (1 / 16 + τ ^ 2) := by positivity
  rw [Real.norm_of_nonneg hpos]
  have h1 : (1 : ℝ) ≤ (1 + |τ|) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg τ]) (by norm_num)
  have hnum : (1 + Real.exp 1 * (1 + |τ|) ^ (1 / 8 : ℝ)) ^ 2 ≤
      (1 + Real.exp 1) ^ 2 * (1 + |τ|) ^ (1 / 4 : ℝ) := by
    have hle : 1 + Real.exp 1 * (1 + |τ|) ^ (1 / 8 : ℝ) ≤
        (1 + Real.exp 1) * (1 + |τ|) ^ (1 / 8 : ℝ) := by nlinarith [Real.exp_pos 1]
    have hsq_rpow : ((1 + |τ|) ^ (1 / 8 : ℝ)) ^ (2 : ℕ) = (1 + |τ|) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    calc (1 + Real.exp 1 * (1 + |τ|) ^ (1 / 8 : ℝ)) ^ 2
        ≤ ((1 + Real.exp 1) * (1 + |τ|) ^ (1 / 8 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hle 2
      _ = (1 + Real.exp 1) ^ 2 * ((1 + |τ|) ^ (1 / 8 : ℝ)) ^ 2 := mul_pow _ _ 2
      _ = (1 + Real.exp 1) ^ 2 * (1 + |τ|) ^ (1 / 4 : ℝ) := by rw [hsq_rpow]
  have hden : (1 + |τ|) ^ 2 / 32 ≤ 1 / 16 + τ ^ 2 := by
    have : (1 + |τ|) ^ 2 ≤ 2 + 2 * τ ^ 2 := by
      have : (1 - |τ|) ^ 2 ≥ 0 := sq_nonneg _
      nlinarith [sq_abs τ]
    linarith [sq_nonneg τ]
  have hpow : (1 + |τ|) ^ (1 / 4 : ℝ) / (1 + |τ|) ^ 2 ≤ (1 + |τ|) ^ (-3 / 2 : ℝ) := by
    rw [show (1 + |τ|) ^ 2 = (1 + |τ|) ^ (2 : ℝ) by norm_cast,
      ← Real.rpow_sub (by positivity : 0 < 1 + |τ|)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg τ]) (by norm_num)
  calc (1 + Real.exp 1 * (1 + |τ|) ^ (1 / 8 : ℝ)) ^ 2 / (1 / 16 + τ ^ 2)
      ≤ ((1 + Real.exp 1) ^ 2 * (1 + |τ|) ^ (1 / 4 : ℝ)) / ((1 + |τ|) ^ 2 / 32) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (32 * (1 + Real.exp 1) ^ 2) * ((1 + |τ|) ^ (1 / 4 : ℝ) / (1 + |τ|) ^ 2) := by
        field_simp
    _ ≤ (32 * (1 + Real.exp 1) ^ 2) * (1 + |τ|) ^ (-3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Term A tends to `0` as `ε ↓ 0` under `RiemannHypothesis`. -/
theorem tendsto_termA_zero (rh : RiemannHypothesis) :
    Tendsto (fun ε : ℝ => ∫ τ : ℝ,
      ‖1 - riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) /
        riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ ^ 2 /
        ((1 / 2 - ε) ^ 2 + τ ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let F : ℝ → ℝ → ℝ := fun ε τ =>
    ‖1 - riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) /
      riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ ^ 2 /
      ((1 / 2 - ε) ^ 2 + τ ^ 2)
  let bound : ℝ → ℝ := fun τ =>
    (1 + Real.exp 1 * (1 + |τ|) ^ (1 / 8 : ℝ)) ^ 2 / (1 / 16 + τ ^ 2)
  have hmeas : ∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (F ε) volume := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 8)] with ε hε
    have hcont : Continuous (F ε) := by
      have hc1 : Continuous (fun τ : ℝ => riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I)) := by
        rw [continuous_iff_continuousAt]
        intro τ
        have hne : (1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I ≠ 1 := fun h => by
          have := congrArg Complex.re h; simp at this; linarith [hε.1]
        have harg : Continuous (fun τ : ℝ => (1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) := by fun_prop
        exact ContinuousAt.comp (f := fun τ : ℝ => (1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I)
          (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt harg.continuousAt
      have hc2 : Continuous (fun τ : ℝ => riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)) := by
        rw [continuous_iff_continuousAt]
        intro τ
        have hne : (1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I ≠ 1 := fun h => by
          have := congrArg Complex.re h; simp at this; linarith [hε.2]
        have harg : Continuous (fun τ : ℝ => (1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I) := by fun_prop
        exact ContinuousAt.comp (f := fun τ : ℝ => (1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)
          (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt harg.continuousAt
      have hne2 : ∀ τ : ℝ, riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I) ≠ 0 := fun τ =>
        riemannZeta_ne_zero_of_rh rh (by simp [hε.1]) fun h => by
          have := congrArg Complex.re h; simp at this; linarith [hε.2]
      refine Continuous.div ?_ (by fun_prop) (fun τ => by nlinarith [hε.2])
      exact ((continuous_const.sub (hc1.div hc2 hne2)).norm).pow 2
    exact hcont.aestronglyMeasurable
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ τ ∂volume, ‖F ε τ‖ ≤ bound τ := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 8)] with ε hε
    refine ae_of_all _ fun τ => ?_
    have hden_ge : 1 / 16 + τ ^ 2 ≤ (1 / 2 - ε) ^ 2 + τ ^ 2 := by nlinarith [hε.1, hε.2]
    have hF_nn : 0 ≤ F ε τ := by dsimp [F]; positivity
    rw [Real.norm_of_nonneg hF_nn]
    have hne2 : riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I) ≠ 0 :=
      riemannZeta_ne_zero_of_rh rh (by simp [hε.1]) fun h => by
        have := congrArg Complex.re h; simp at this; linarith [hε.2]
    have hzr := norm_zeta_ratio_le hε.1 hε.2.le τ
    have hdiv_le : ‖riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) /
        riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ ≤
        Real.exp 1 * (1 + |τ|) ^ (1 / 8 : ℝ) := by
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hne2)]
      have hrpow_le : (1 + |τ|) ^ ε ≤ (1 + |τ|) ^ (1 / 8 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg τ]) hε.2.le
      calc ‖riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I)‖
          ≤ Real.exp 1 * (1 + |τ|) ^ ε * ‖riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ := hzr
        _ ≤ Real.exp 1 * (1 + |τ|) ^ (1 / 8 : ℝ) *
            ‖riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ := by gcongr
    have hnum_le : ‖1 - riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) /
        riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤
        (1 + Real.exp 1 * (1 + |τ|) ^ (1 / 8 : ℝ)) ^ 2 := by
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
    exact div_le_div₀ (by positivity) hnum_le (by positivity) hden_ge
  have hlim : ∀ᵐ τ ∂volume, Tendsto (fun ε => F ε τ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    filter_upwards [ae_riemannZeta_half_ne_zero] with τ hτ
    have hne1 : (1 / 2 : ℂ) + (τ : ℂ) * I ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this
    have hc := (differentiableAt_riemannZeta hne1).continuousAt
    have h1 : Tendsto (fun ε : ℝ => (1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I)
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 / 2 : ℂ) + (τ : ℂ) * I)) := by
      have hcont1 : Continuous (fun ε : ℝ => (1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) := by fun_prop
      have ht := (hcont1.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using ht
    have h2 : Tendsto (fun ε : ℝ => (1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 / 2 : ℂ) + (τ : ℂ) * I)) := by
      have hcont2 : Continuous (fun ε : ℝ => (1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I) := by fun_prop
      have ht := (hcont2.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using ht
    have hz1 := hc.tendsto.comp h1
    have hz2 := hc.tendsto.comp h2
    have hq : Tendsto (fun ε : ℝ => 1 - riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) /
        riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have ht := (tendsto_const_nhds (x := (1 : ℂ))).sub (hz1.div hz2 hτ)
      rw [div_self hτ, sub_self] at ht
      exact ht
    have hden : Tendsto (fun ε : ℝ => (1 / 2 - ε) ^ 2 + τ ^ 2) (𝓝[>] (0 : ℝ))
        (𝓝 ((1 / 2 : ℝ) ^ 2 + τ ^ 2)) := by
      have hcontd : Continuous (fun ε : ℝ => (1 / 2 - ε) ^ 2 + τ ^ 2) := by fun_prop
      have ht := (hcontd.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using ht
    have hnum : Tendsto (fun ε : ℝ => ‖1 - riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) /
        riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have ht := (hq.norm).pow 2
      simpa using ht
    have hdiv := hnum.div hden (by positivity : (1 / 2 : ℝ) ^ 2 + τ ^ 2 ≠ 0)
    rw [zero_div] at hdiv
    exact hdiv
  have hdct := tendsto_integral_filter_of_dominated_convergence bound hmeas hbound
    integrable_dom_termA hlim
  simp only [integral_zero] at hdct
  exact hdct

end BN3

/-
# Module 4: Borel-Caratheodory, Hadamard three-circles, and Lindelof / 1/zeta growth under RH

Establishes:
1. Borel-Caratheodory theorem on closed disks via the Maximum Modulus Principle.
2. Hadamard three-circles theorem on closed annuli via integer-power rational approximation.
3. Holomorphic `invZeta` on `{z | 1/2 < z.re}` and holomorphic `logZeta` on `{z | 1/2 < z.re ∧ 0 < z.im}`
   under `RiemannHypothesis`.
4. Titchmarsh Theorem 14.2: under `RiemannHypothesis`, for every `δ ∈ (0, 1/4)` and `η > 0`,
   `‖invZeta z‖ ≤ C * (2 + |z.im|)^η` on `Re(z) ≥ 1/2 + δ`, and `‖ζ(z)‖ ≤ C * (2 + |z.im|)^η`
   on `Re(z) ≥ 1/2 + δ`, `‖z - 1‖ ≥ 1/2`.
-/

namespace BN4
open MeasureTheory Set Filter Complex
open scoped Topology

/-- Removable-singularity inverse of `riemannZeta` (taking value `0` at the pole `s = 1`). -/
noncomputable def invZeta (z : ℂ) : ℂ :=
  if z = 1 then 0 else (riemannZeta z)⁻¹

lemma invZeta_of_ne_one {z : ℂ} (hz : z ≠ 1) : invZeta z = (riemannZeta z)⁻¹ :=
  if_neg hz

lemma invZeta_conj (z : ℂ) : invZeta (starRingEnd ℂ z) = starRingEnd ℂ (invZeta z) := by
  by_cases hz : z = 1
  · subst hz; simp [invZeta]
  · have hzc : starRingEnd ℂ z ≠ 1 := fun h => hz (by
      have := congrArg (starRingEnd ℂ) h; simpa using this)
    rw [invZeta_of_ne_one hzc, invZeta_of_ne_one hz, riemannZeta_conj, map_inv₀]

/-- `invZeta` is continuous at `1` since `riemannZeta` has a simple pole at `1`. -/
lemma continuousAt_invZeta_one : ContinuousAt invZeta 1 := by
  rw [ContinuousAt, show invZeta 1 = 0 by simp [invZeta]]
  have hr := riemannZeta_residue_one
  have hid : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] 1) (𝓝 0) := by
    have hcont : Continuous (fun s : ℂ => s - 1) := by fun_prop
    have ht := (hcont.continuousAt (x := (1 : ℂ))).tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
    simpa using ht
  have hdiv : Tendsto (fun s : ℂ => (s - 1) / ((s - 1) * riemannZeta s)) (𝓝[≠] 1) (𝓝 (0 / 1)) :=
    hid.div hr one_ne_zero
  rw [zero_div] at hdiv
  have hinv_nhds : Tendsto invZeta (𝓝[≠] 1) (𝓝 0) := by
    refine hdiv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ 1)
    rw [invZeta_of_ne_one hs]
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    field_simp [hsub]
  rw [Metric.tendsto_nhds] at hinv_nhds ⊢
  intro ε hε
  have hev := hinv_nhds ε hε
  rw [eventually_nhdsWithin_iff] at hev
  filter_upwards [hev] with s hs
  by_cases h1 : s = 1
  · subst h1; simpa [invZeta] using hε
  · exact hs h1

/-- Under `RiemannHypothesis`, `invZeta` is holomorphic on `{z : ℂ | 1/2 < z.re}`. -/
theorem differentiableOn_invZeta (rh : RiemannHypothesis) :
    DifferentiableOn ℂ invZeta {z : ℂ | (1 / 2 : ℝ) < z.re} := by
  have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  intro z hz
  by_cases h1 : z = 1
  · subst h1
    have hpunct : ∀ᶠ w in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ invZeta w := by
      have hmem : {w : ℂ | (1 / 2 : ℝ) < w.re} ∈ 𝓝 (1 : ℂ) := hopen.mem_nhds (by simp; norm_num)
      filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with w hw (hw1 : w ≠ 1)
      have hne0 : riemannZeta w ≠ 0 := BN3.riemannZeta_ne_zero_of_rh rh hw hw1
      have hdiff_inv : DifferentiableAt ℂ (fun u => (riemannZeta u)⁻¹) w :=
        (differentiableAt_riemannZeta hw1).inv hne0
      refine hdiff_inv.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ne.mem_nhds hw1] with u hu
      exact invZeta_of_ne_one hu
    exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hpunct
      continuousAt_invZeta_one).differentiableAt.differentiableWithinAt
  · have hne0 : riemannZeta z ≠ 0 := BN3.riemannZeta_ne_zero_of_rh rh hz h1
    have hdiff_inv : DifferentiableAt ℂ (fun u => (riemannZeta u)⁻¹) z :=
      (differentiableAt_riemannZeta h1).inv hne0
    have heq : invZeta =ᶠ[𝓝 z] fun u => (riemannZeta u)⁻¹ := by
      filter_upwards [isOpen_ne.mem_nhds h1] with u hu
      exact invZeta_of_ne_one hu
    exact (hdiff_inv.congr_of_eventuallyEq heq).differentiableWithinAt

/-- Borel-Caratheodory theorem on closed disks. -/
theorem borel_caratheodory {f : ℂ → ℂ} {z₀ : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ R))
    (hM : ∀ z ∈ Metric.closedBall z₀ R, (f z).re ≤ M) :
    ∀ z ∈ Metric.closedBall z₀ r, ‖f z - f z₀‖ ≤ 2 * r / (R - r) * (M - (f z₀).re) := by
  have hR : 0 < R := lt_trans hr hrR
  intro z hz
  suffices hδ : ∀ δ : ℝ, 0 < δ → ‖f z - f z₀‖ ≤ 2 * r / (R - r) * (M - (f z₀).re + δ) by
    by_contra hlt
    push Not at hlt
    set gap : ℝ := ‖f z - f z₀‖ - 2 * r / (R - r) * (M - (f z₀).re)
    have hgap : 0 < gap := sub_pos.mpr hlt
    have hfac : 0 < 2 * r / (R - r) := div_pos (by linarith) (sub_pos.mpr hrR)
    set δ : ℝ := gap / (2 * (2 * r / (R - r)))
    have hδpos : 0 < δ := div_pos hgap (by positivity)
    have hle := hδ δ hδpos
    have hmul : 2 * r / (R - r) * δ = gap / 2 := by
      dsimp [δ]; field_simp [hfac.ne', (sub_pos.mpr hrR).ne']
    linarith
  intro δ hδ
  set A : ℝ := M - (f z₀).re + δ
  have hA_pos : 0 < A := by
    have h0 := hM z₀ (Metric.mem_closedBall_self hR.le)
    linarith
  let g : ℂ → ℂ := fun w => (f w - f z₀) / ((2 * A : ℂ) - (f w - f z₀))
  have hden_ne : ∀ w ∈ Metric.closedBall z₀ R, (2 * A : ℂ) - (f w - f z₀) ≠ 0 := by
    intro w hw h0
    have hre := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re,
      Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, Complex.zero_re] at hre
    have hMw := hM w hw
    linarith
  have hg_le1 : ∀ w ∈ Metric.closedBall z₀ R, ‖g w‖ ≤ 1 := by
    intro w hw
    dsimp [g]
    rw [norm_div, div_le_one (norm_pos_iff.mpr (hden_ne w hw))]
    have hsq : ‖f w - f z₀‖ ^ 2 ≤ ‖(2 * A : ℂ) - (f w - f z₀)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      have hMw := hM w hw
      have hre1 : ((2 * A : ℂ) - (f w - f z₀)).re = 2 * A - ((f w).re - (f z₀).re) := by simp
      have him1 : ((2 * A : ℂ) - (f w - f z₀)).im = -((f w).im - (f z₀).im) := by simp
      rw [hre1, him1, Complex.sub_re, Complex.sub_im]
      nlinarith
    exact le_of_sq_le_sq hsq (norm_nonneg _)
  have hg_diff : DifferentiableOn ℂ g (Metric.closedBall z₀ R) := by
    intro w hw
    have hf' := (hf w hw).sub (differentiableWithinAt_const (f z₀))
    have hden' := (differentiableWithinAt_const (2 * A : ℂ)).sub hf'
    exact hf'.div hden' (hden_ne w hw)
  have hg_z0 : g z₀ = 0 := by simp [g]
  have hg_diffAt : DifferentiableAt ℂ g z₀ :=
    hg_diff.differentiableAt (Metric.closedBall_mem_nhds z₀ hR)
  let h : ℂ → ℂ := fun w => if w = z₀ then deriv g z₀ else g w / (w - z₀)
  have hh_cont_z0 : ContinuousAt h z₀ := by
    rw [ContinuousAt, show h z₀ = deriv g z₀ by simp [h]]
    have hd := hg_diffAt.hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope] at hd
    have hd' : Tendsto (fun w => g w / (w - z₀)) (𝓝[≠] z₀) (𝓝 (deriv g z₀)) := by
      refine hd.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w (hw : w ≠ z₀)
      simp [slope, vsub_eq_sub, hg_z0, smul_eq_mul, div_eq_inv_mul]
    rw [Metric.tendsto_nhds] at hd' ⊢
    intro ε hε
    have hev := hd' ε hε
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev] with w hw
    by_cases h0 : w = z₀
    · subst h0; simpa [h] using hε
    · simpa [h, h0] using hw h0
  have hh_diff_ball : DifferentiableOn ℂ h (Metric.ball z₀ R) := by
    intro w hw
    rcases eq_or_ne w z₀ with rfl | h0
    · have hpunct : ∀ᶠ u in 𝓝[≠] w, DifferentiableAt ℂ h u := by
        filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hw),
          self_mem_nhdsWithin] with u hu (hu0 : u ≠ w)
        have hgu : DifferentiableAt ℂ g u :=
          hg_diff.differentiableAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hu)
            Metric.ball_subset_closedBall)
        have hq : DifferentiableAt ℂ (fun v => g v / (v - w)) u :=
          hgu.div (differentiableAt_id.sub (differentiableAt_const w)) (sub_ne_zero.mpr hu0)
        refine hq.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_ne.mem_nhds hu0] with v hv
        exact if_neg hv
      exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hpunct
        hh_cont_z0).differentiableAt.differentiableWithinAt
    · have hgu : DifferentiableAt ℂ g w :=
        hg_diff.differentiableAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hw)
          Metric.ball_subset_closedBall)
      have hq : DifferentiableAt ℂ (fun v => g v / (v - z₀)) w :=
        hgu.div (differentiableAt_id.sub (differentiableAt_const z₀)) (sub_ne_zero.mpr h0)
      have heq : h =ᶠ[𝓝 w] fun v => g v / (v - z₀) := by
        filter_upwards [isOpen_ne.mem_nhds h0] with v hv
        exact if_neg hv
      exact (hq.congr_of_eventuallyEq heq).differentiableWithinAt
  have hh_cont_cl : ContinuousOn h (closure (Metric.ball z₀ R)) := by
    intro w hw
    rw [closure_ball z₀ hR.ne'] at hw
    rcases eq_or_ne w z₀ with rfl | h0
    · exact hh_cont_z0.continuousWithinAt
    · have hcont_g : ContinuousWithinAt g (Metric.closedBall z₀ R) w :=
        (hg_diff w hw).continuousWithinAt
      have hcont_q : ContinuousWithinAt (fun v => g v / (v - z₀)) (Metric.closedBall z₀ R) w :=
        hcont_g.div (continuousWithinAt_id.sub continuousWithinAt_const) (sub_ne_zero.mpr h0)
      rw [closure_ball z₀ hR.ne']
      refine hcont_q.congr_of_eventuallyEq ?_ (if_neg h0)
      filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds h0)] with v hv
      exact if_neg hv
  have hh_front : ∀ w ∈ frontier (Metric.ball z₀ R), ‖h w‖ ≤ 1 / R := by
    intro w hw
    have hcl : dist w z₀ ≤ R := by
      have := hw.1; rwa [closure_ball z₀ hR.ne', Metric.mem_closedBall] at this
    have hnot : ¬ dist w z₀ < R := by
      have := hw.2; rwa [Metric.isOpen_ball.interior_eq, Metric.mem_ball] at this
    have hsp : ‖w - z₀‖ = R := by
      rw [← dist_eq_norm]; exact le_antisymm hcl (not_lt.mp hnot)
    have hne : w ≠ z₀ := fun h0 => by rw [h0, sub_self, norm_zero] at hsp; linarith
    have hw_cl : w ∈ Metric.closedBall z₀ R := by
      rw [Metric.mem_closedBall, dist_eq_norm, hsp]
    dsimp [h]
    rw [if_neg hne, norm_div, hsp]
    exact div_le_div_of_nonneg_right (hg_le1 w hw_cl) hR.le
  have hz_cl : z ∈ closure (Metric.ball z₀ R) := by
    rw [closure_ball z₀ hR.ne']
    exact Metric.closedBall_subset_closedBall hrR.le hz
  have hh_max : ‖h z‖ ≤ 1 / R :=
    Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
      ⟨hh_diff_ball, hh_cont_cl⟩ hh_front hz_cl
  have hgz : ‖g z‖ ≤ r / R := by
    by_cases h0 : z = z₀
    · subst h0; simp [hg_z0]; positivity
    · have hhz := hh_max
      dsimp [h] at hhz
      rw [if_neg h0, norm_div] at hhz
      have hz_dist : ‖z - z₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      have hpos : 0 < ‖z - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h0)
      have := (div_le_iff₀ hpos).mp hhz
      calc ‖g z‖ ≤ 1 / R * ‖z - z₀‖ := this
        _ ≤ 1 / R * r := mul_le_mul_of_nonneg_left hz_dist (by positivity)
        _ = r / R := by ring
  have hden_pos : 0 < ‖(2 * A : ℂ) - (f z - f z₀)‖ :=
    norm_pos_iff.mpr (hden_ne z (Metric.closedBall_subset_closedBall hrR.le hz))
  dsimp [g] at hgz
  rw [norm_div, div_le_iff₀ hden_pos] at hgz
  have htri : ‖(2 * A : ℂ) - (f z - f z₀)‖ ≤ 2 * A + ‖f z - f z₀‖ := by
    calc ‖(2 * A : ℂ) - (f z - f z₀)‖
        ≤ ‖(2 * A : ℂ)‖ + ‖f z - f z₀‖ := norm_sub_le _ _
      _ = 2 * A + ‖f z - f z₀‖ := by
          rw [show (2 * A : ℂ) = ((2 * A : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hkey : ‖f z - f z₀‖ ≤ r / R * (2 * A + ‖f z - f z₀‖) :=
    hgz.trans (mul_le_mul_of_nonneg_left htri (by positivity))
  have hrearr : (R - r) * ‖f z - f z₀‖ ≤ 2 * r * A := by
    have hmul := mul_le_mul_of_nonneg_left hkey hR.le
    have : R * (r / R * (2 * A + ‖f z - f z₀‖)) = r * (2 * A + ‖f z - f z₀‖) := by
      field_simp [hR.ne']
    linarith
  have hRsub : 0 < R - r := sub_pos.mpr hrR
  rw [div_mul_eq_mul_div, le_div_iff₀ hRsub]
  linarith

set_option maxHeartbeats 600000 in
/-- Hadamard three-circles theorem on closed disks. -/
theorem hadamard_three_circles {f : ℂ → ℂ} {z₀ : ℂ} {r₁ r₂ r₃ M₁ M₃ : ℝ}
    (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (h23 : r₂ < r₃)
    (hM₁ : 1 ≤ M₁) (hM₃ : 1 ≤ M₃)
    (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ r₃))
    (h1 : ∀ z, ‖z - z₀‖ = r₁ → ‖f z‖ ≤ M₁)
    (h3 : ∀ z, ‖z - z₀‖ = r₃ → ‖f z‖ ≤ M₃) :
    ∀ z ∈ Metric.closedBall z₀ r₂,
      ‖f z‖ ≤ M₁ ^ (1 - Real.log (r₂ / r₁) / Real.log (r₃ / r₁)) *
              M₃ ^ (Real.log (r₂ / r₁) / Real.log (r₃ / r₁)) := by
  have hr₂ : 0 < r₂ := lt_trans hr₁ h12
  have hr₃ : 0 < r₃ := lt_trans hr₂ h23
  have hM₁_pos : 0 < M₁ := by linarith
  have hM₃_pos : 0 < M₃ := by linarith
  set α : ℝ := Real.log (r₂ / r₁) / Real.log (r₃ / r₁)
  set B : ℝ := M₁ ^ (1 - α) * M₃ ^ α
  have hlog31 : 0 < Real.log (r₃ / r₁) := Real.log_pos ((one_lt_div hr₁).mpr (lt_trans h12 h23))
  -- First prove the bound on the sphere `‖z - z₀‖ = r₂`.
  have hsphere : ∀ z, ‖z - z₀‖ = r₂ → ‖f z‖ ≤ B := by
    intro z hz
    set w₀ : ℂ := z - z₀
    have hw₀ : ‖w₀‖ = r₂ := hz
    let U : Set ℂ := {w : ℂ | r₁ < ‖w‖ ∧ ‖w‖ < r₃}
    have hU_open : IsOpen U :=
      (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    have hU_bdd : Bornology.IsBounded U := by
      refine Metric.isBounded_ball (x := (0 : ℂ)) (r := r₃) |>.subset fun w hw => ?_
      simpa [Metric.mem_ball, dist_zero_right] using hw.2
    have hU_cl_sub : closure U ⊆ {w : ℂ | r₁ ≤ ‖w‖ ∧ ‖w‖ ≤ r₃} := by
      refine closure_minimal (fun w hw => ⟨hw.1.le, hw.2.le⟩) ?_
      exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    have hU_front_sub : frontier U ⊆ {w : ℂ | ‖w‖ = r₁ ∨ ‖w‖ = r₃} := by
      intro w hw
      have hcl := hU_cl_sub hw.1
      have hnot : w ∉ U := by
        have := hw.2; rwa [hU_open.interior_eq] at this
      by_contra hne
      rw [Set.mem_ofPred_eq, not_or] at hne
      exact hnot ⟨lt_of_le_of_ne hcl.1 (Ne.symm hne.1), lt_of_le_of_ne hcl.2 hne.2⟩
    have hrat : ∀ (p : ℤ) (q : ℕ), 0 < q →
        ‖f z‖ ≤ max ((r₁ / r₂) ^ ((p : ℝ) / (q : ℝ)) * M₁)
                    ((r₃ / r₂) ^ ((p : ℝ) / (q : ℝ)) * M₃) := by
      intro p q hq
      have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
      let G : ℂ → ℂ := fun w => w ^ p * (f (z₀ + w)) ^ q
      have hG_diff_cl : DifferentiableOn ℂ G {w : ℂ | r₁ ≤ ‖w‖ ∧ ‖w‖ ≤ r₃} := by
        intro w hw
        have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hr₁ hw.1)
        have h1d : DifferentiableAt ℂ (fun u : ℂ => u ^ p) w :=
          differentiableAt_zpow.mpr (Or.inl hw0)
        have hmem : z₀ + w ∈ Metric.closedBall z₀ r₃ := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hw.2
        have h2d : DifferentiableWithinAt ℂ (fun u : ℂ => f (z₀ + u))
            {u : ℂ | r₁ ≤ ‖u‖ ∧ ‖u‖ ≤ r₃} w := by
          refine (hf (z₀ + w) hmem).comp w
            ((differentiableWithinAt_const z₀).add differentiableWithinAt_id) ?_
          intro u hu
          simpa [Metric.mem_closedBall, dist_eq_norm] using hu.2
        exact h1d.differentiableWithinAt.mul (h2d.pow q)
      have hG_dc : DiffContOnCl ℂ G U :=
        ⟨hG_diff_cl.mono (fun w hw => ⟨hw.1.le, hw.2.le⟩),
         (hG_diff_cl.mono hU_cl_sub).continuousOn⟩
      set Cpq : ℝ := max (r₁ ^ p * M₁ ^ q) (r₃ ^ p * M₃ ^ q)
      have hG_front : ∀ w ∈ frontier U, ‖G w‖ ≤ Cpq := by
        intro w hw
        have hfz_bound : ∀ r M : ℝ, (∀ u, ‖u - z₀‖ = r → ‖f u‖ ≤ M) →
            ‖w‖ = r → ‖G w‖ ≤ r ^ p * M ^ q := by
          intro r M hM_sp hwr
          dsimp [G]
          rw [norm_mul, norm_zpow, norm_pow, hwr]
          have hfu : ‖f (z₀ + w)‖ ≤ M := hM_sp (z₀ + w) (by simpa using hwr)
          have hrp : 0 ≤ r ^ p := zpow_nonneg (by rw [← hwr]; exact norm_nonneg w) p
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hfu q) hrp
        rcases hU_front_sub hw with hr1 | hr3
        · exact (hfz_bound r₁ M₁ h1 hr1).trans (le_max_left _ _)
        · exact (hfz_bound r₃ M₃ h3 hr3).trans (le_max_right _ _)
      have hw₀_cl : w₀ ∈ closure U := subset_closure ⟨by rw [hw₀]; exact h12, by rw [hw₀]; exact h23⟩
      have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le hU_bdd hG_dc hG_front hw₀_cl
      dsimp [G] at hmax
      rw [show z₀ + w₀ = z by dsimp [w₀]; ring, norm_mul, norm_zpow, norm_pow, hw₀] at hmax
      have hr2p_pos : 0 < r₂ ^ p := zpow_pos hr₂ p
      have hpow_le : ‖f z‖ ^ q ≤ max ((r₁ / r₂) ^ p * M₁ ^ q) ((r₃ / r₂) ^ p * M₃ ^ q) := by
        have hdiv : ‖f z‖ ^ q ≤ Cpq / r₂ ^ p := (le_div_iff₀' hr2p_pos).mpr hmax
        have hmax_div : Cpq / r₂ ^ p = max ((r₁ ^ p * M₁ ^ q) / r₂ ^ p) ((r₃ ^ p * M₃ ^ q) / r₂ ^ p) := by
          dsimp [Cpq]
          rcases le_total (r₁ ^ p * M₁ ^ q) (r₃ ^ p * M₃ ^ q) with h | h
          · rw [max_eq_right h, max_eq_right (div_le_div_of_nonneg_right h hr2p_pos.le)]
          · rw [max_eq_left h, max_eq_left (div_le_div_of_nonneg_right h hr2p_pos.le)]
        calc ‖f z‖ ^ q ≤ Cpq / r₂ ^ p := hdiv
          _ = max ((r₁ ^ p * M₁ ^ q) / r₂ ^ p) ((r₃ ^ p * M₃ ^ q) / r₂ ^ p) := hmax_div
          _ = max ((r₁ / r₂) ^ p * M₁ ^ q) ((r₃ / r₂) ^ p * M₃ ^ q) := by
              congr 1 <;> rw [div_zpow] <;> ring
      have hroot : ∀ r M : ℝ, 0 < r → 0 < M →
          ‖f z‖ ^ q ≤ (r / r₂) ^ p * M ^ q → ‖f z‖ ≤ (r / r₂) ^ ((p : ℝ) / (q : ℝ)) * M := by
        intro r M hr hM hle
        have hpos_rhs : 0 < (r / r₂) ^ ((p : ℝ) / (q : ℝ)) * M :=
          mul_pos (Real.rpow_pos_of_pos (div_pos hr hr₂) _) hM
        have hrhs_pow : ((r / r₂) ^ ((p : ℝ) / (q : ℝ)) * M) ^ q = (r / r₂) ^ p * M ^ q := by
          rw [mul_pow, ← Real.rpow_natCast ((r / r₂) ^ _), ← Real.rpow_mul (div_pos hr hr₂).le,
            div_mul_cancel₀ _ hq_pos.ne', Real.rpow_intCast]
        rw [← hrhs_pow] at hle
        exact le_of_pow_le_pow_left₀ hq.ne' hpos_rhs.le hle
      rcases le_total ((r₁ / r₂) ^ p * M₁ ^ q) ((r₃ / r₂) ^ p * M₃ ^ q) with hle | hle
      · rw [max_eq_right hle] at hpow_le
        exact (hroot r₃ M₃ hr₃ hM₃_pos hpow_le).trans (le_max_right _ _)
      · rw [max_eq_left hle] at hpow_le
        exact (hroot r₁ M₁ hr₁ hM₁_pos hpow_le).trans (le_max_left _ _)
    set a : ℝ := -Real.log (M₃ / M₁) / Real.log (r₃ / r₁)
    have hseq : Tendsto (fun n : ℕ => ((⌊a * (n + 1 : ℕ)⌋ : ℤ) : ℝ) / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 a) := by
      have hbound : ∀ n : ℕ,
          |((⌊a * ((n + 1 : ℕ) : ℝ)⌋ : ℤ) : ℝ) / ((n + 1 : ℕ) : ℝ) - a| ≤ 1 / ((n : ℝ) + 1) := by
        intro n
        have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
        have hfl1 : (⌊a * ((n + 1 : ℕ) : ℝ)⌋ : ℝ) ≤ a * ((n + 1 : ℕ) : ℝ) := Int.floor_le _
        have hfl2 : a * ((n + 1 : ℕ) : ℝ) - 1 < (⌊a * ((n + 1 : ℕ) : ℝ)⌋ : ℝ) :=
          Int.sub_one_lt_floor _
        have hrew : ((⌊a * ((n + 1 : ℕ) : ℝ)⌋ : ℤ) : ℝ) / ((n + 1 : ℕ) : ℝ) - a =
            (((⌊a * ((n + 1 : ℕ) : ℝ)⌋ : ℤ) : ℝ) - a * ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) := by
          field_simp [hn.ne']
        rw [hrew, abs_div, abs_of_pos hn]
        push_cast at hfl1 hfl2 ⊢
        exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) (by positivity)
      have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by simpa [Real.norm_eq_abs] using hbound n) h0
    let Φ : ℝ → ℝ := fun t => max ((r₁ / r₂) ^ t * M₁) ((r₃ / r₂) ^ t * M₃)
    have hΦ_cont : Continuous Φ :=
      ((continuous_const.rpow continuous_id (fun _ => Or.inl (div_pos hr₁ hr₂).ne')).mul
        continuous_const).max
      ((continuous_const.rpow continuous_id (fun _ => Or.inl (div_pos hr₃ hr₂).ne')).mul
        continuous_const)
    have hlim : Tendsto (fun n : ℕ => Φ (((⌊a * ((n + 1 : ℕ) : ℝ)⌋ : ℤ) : ℝ) / ((n + 1 : ℕ) : ℝ)))
        atTop (𝓝 (Φ a)) := (hΦ_cont.continuousAt).tendsto.comp hseq
    have hle_a : ‖f z‖ ≤ Φ a :=
      ge_of_tendsto hlim (Eventually.of_forall fun n => hrat ⌊a * ((n + 1 : ℕ) : ℝ)⌋ (n + 1) (Nat.succ_pos n))
    have hB_pos : 0 < B := mul_pos (Real.rpow_pos_of_pos hM₁_pos _) (Real.rpow_pos_of_pos hM₃_pos _)
    have hΦ1 : (r₁ / r₂) ^ a * M₁ = B := by
      rw [← Real.log_injOn_pos.eq_iff (mul_pos (Real.rpow_pos_of_pos (div_pos hr₁ hr₂) _) hM₁_pos) hB_pos,
        Real.log_mul (Real.rpow_pos_of_pos (div_pos hr₁ hr₂) _).ne' hM₁_pos.ne',
        Real.log_rpow (div_pos hr₁ hr₂),
        Real.log_mul (Real.rpow_pos_of_pos hM₁_pos _).ne' (Real.rpow_pos_of_pos hM₃_pos _).ne',
        Real.log_rpow hM₁_pos, Real.log_rpow hM₃_pos,
        Real.log_div hr₁.ne' hr₂.ne']
      dsimp [a, α]
      rw [Real.log_div hr₂.ne' hr₁.ne', Real.log_div hr₃.ne' hr₁.ne', Real.log_div hM₃_pos.ne' hM₁_pos.ne']
      have hne : Real.log r₃ - Real.log r₁ ≠ 0 := by
        rw [← Real.log_div hr₃.ne' hr₁.ne']; exact hlog31.ne'
      field_simp [hne]
      ring
    have hΦ3 : (r₃ / r₂) ^ a * M₃ = B := by
      rw [← Real.log_injOn_pos.eq_iff (mul_pos (Real.rpow_pos_of_pos (div_pos hr₃ hr₂) _) hM₃_pos) hB_pos,
        Real.log_mul (Real.rpow_pos_of_pos (div_pos hr₃ hr₂) _).ne' hM₃_pos.ne',
        Real.log_rpow (div_pos hr₃ hr₂),
        Real.log_mul (Real.rpow_pos_of_pos hM₁_pos _).ne' (Real.rpow_pos_of_pos hM₃_pos _).ne',
        Real.log_rpow hM₁_pos, Real.log_rpow hM₃_pos,
        Real.log_div hr₃.ne' hr₂.ne']
      dsimp [a, α]
      rw [Real.log_div hr₂.ne' hr₁.ne', Real.log_div hr₃.ne' hr₁.ne', Real.log_div hM₃_pos.ne' hM₁_pos.ne']
      have hne : Real.log r₃ - Real.log r₁ ≠ 0 := by
        rw [← Real.log_div hr₃.ne' hr₁.ne']; exact hlog31.ne'
      field_simp [hne]
      ring
    have hΦa : Φ a = B := by dsimp [Φ]; rw [hΦ1, hΦ3, max_self]
    rwa [hΦa] at hle_a
  -- Extend from sphere `r₂` to `closedBall z₀ r₂` by Maximum Modulus Principle.
  have hdc : DiffContOnCl ℂ f (Metric.ball z₀ r₂) := by
    refine ⟨hf.mono (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall h23.le)), ?_⟩
    rw [closure_ball z₀ hr₂.ne']
    exact (hf.mono (Metric.closedBall_subset_closedBall h23.le)).continuousOn
  have hfront : ∀ z ∈ frontier (Metric.ball z₀ r₂), ‖f z‖ ≤ B := fun z hz => by
    have hcl : dist z z₀ ≤ r₂ := by
      have := hz.1; rwa [closure_ball z₀ hr₂.ne', Metric.mem_closedBall] at this
    have hnot : ¬ dist z z₀ < r₂ := by
      have := hz.2; rwa [Metric.isOpen_ball.interior_eq, Metric.mem_ball] at this
    exact hsphere z (by rw [← dist_eq_norm]; exact le_antisymm hcl (not_lt.mp hnot))
  intro z hz
  exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc hfront
    (by rwa [closure_ball z₀ hr₂.ne'])

/-- Elementary tail bound `‖ζ(z) - 1‖ ≤ 3/4` for `2 ≤ z.re`. -/
lemma norm_zeta_sub_one_le_of_two_le_re {z : ℂ} (hz : 2 ≤ z.re) :
    ‖riemannZeta z - 1‖ ≤ 3 / 4 := by
  have hz1 : 1 < z.re := by linarith
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ z) := Complex.summable_one_div_nat_cpow.mpr hz1
  rw [zeta_eq_tsum_one_div_nat_cpow hz1]
  have h01 : ∑' n : ℕ, 1 / (n : ℂ) ^ z =
      1 / (0 : ℂ) ^ z + (1 / (1 : ℂ) ^ z + ∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℂ) ^ z) := by
    rw [Summable.tsum_eq_zero_add hsum]
    have hsum1 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ z) :=
      hsum.comp_injective Nat.succ_injective
    rw [Summable.tsum_eq_zero_add hsum1]
    simp [Nat.add_assoc]
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz; linarith
  rw [h01, Complex.zero_cpow hz0, div_zero, zero_add, Complex.one_cpow, div_one, add_sub_cancel_left]
  have hsum2 : Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℂ) ^ z) :=
    hsum.comp_injective (add_left_injective 2)
  have hreal_sum : Summable (fun n : ℕ => (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2) := by
    have := (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)).comp_injective
      (add_left_injective 2)
    refine this.congr fun n => ?_
    simp [one_div]
  have hnorm_le : ∀ n : ℕ, ‖1 / ((n + 2 : ℕ) : ℂ) ^ z‖ ≤ 1 / ((n + 2 : ℕ) : ℝ) ^ 2 := by
    intro n
    have hn_pos : (0 : ℝ) < (n + 2 : ℕ) := by positivity
    rw [norm_div, norm_one, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]
    have hge : ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) ^ z.re :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n + 2)) hz
    rw [Real.rpow_two] at hge
    exact one_div_le_one_div_of_le (by positivity) hge
  have htsum_le : ∑' n : ℕ, (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2 ≤ 3 / 4 := by
    have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2 ≤ 3 / 4 := by
      intro N
      cases N with
      | zero => simp; norm_num
      | succ N =>
        rw [Finset.sum_range_succ']
        have h0 : (1 : ℝ) / ((0 + 2 : ℕ) : ℝ) ^ 2 = 1 / 4 := by norm_num
        rw [h0]
        have htail : ∑ k ∈ Finset.range N, (1 : ℝ) / ((k + 1 + 2 : ℕ) : ℝ) ^ 2 ≤ 1 / 2 := by
          calc ∑ k ∈ Finset.range N, (1 : ℝ) / ((k + 1 + 2 : ℕ) : ℝ) ^ 2
              ≤ ∑ k ∈ Finset.range N, (1 / ((k + 2 : ℕ) : ℝ) - 1 / ((k + 3 : ℕ) : ℝ)) := by
                refine Finset.sum_le_sum fun k _ => ?_
                have h2 : (0 : ℝ) < (k + 2 : ℕ) := by positivity
                have h3 : (0 : ℝ) < (k + 3 : ℕ) := by positivity
                have heq : 1 / ((k + 2 : ℕ) : ℝ) - 1 / ((k + 3 : ℕ) : ℝ) =
                    1 / (((k + 2 : ℕ) : ℝ) * ((k + 3 : ℕ) : ℝ)) := by
                  field_simp [h2.ne', h3.ne']; push_cast; ring
                rw [heq]
                exact one_div_le_one_div_of_le (mul_pos h2 h3) (by push_cast; nlinarith)
            _ = 1 / ((0 + 2 : ℕ) : ℝ) - 1 / ((N + 2 : ℕ) : ℝ) := by
                induction N with
                | zero => simp
                | succ N ih =>
                  rw [Finset.sum_range_succ, ih]
                  push_cast; ring
            _ ≤ 1 / 2 := by
                have : (0 : ℝ) ≤ 1 / ((N + 2 : ℕ) : ℝ) := by positivity
                norm_num at this ⊢; linarith
        linarith
    exact le_of_tendsto hreal_sum.hasSum.tendsto_sum_nat (Eventually.of_forall hpart)
  calc ‖∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℂ) ^ z‖
      ≤ ∑' n : ℕ, ‖1 / ((n + 2 : ℕ) : ℂ) ^ z‖ := norm_tsum_le_tsum_norm hsum2.norm
    _ ≤ ∑' n : ℕ, (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2 :=
        Summable.tsum_le_tsum hnorm_le hsum2.norm hreal_sum
    _ ≤ 3 / 4 := htsum_le

lemma norm_zeta_ge_quarter_of_two_le_re {z : ℂ} (hz : 2 ≤ z.re) :
    (1 / 4 : ℝ) ≤ ‖riemannZeta z‖ := by
  have h := norm_zeta_sub_one_le_of_two_le_re hz
  have htri : (1 : ℝ) ≤ ‖riemannZeta z‖ + ‖riemannZeta z - 1‖ := by
    simpa [norm_one, norm_sub_rev] using norm_le_norm_add_norm_sub' (1 : ℂ) (riemannZeta z)
  linarith

lemma norm_zeta_le_two_of_two_le_re {z : ℂ} (hz : 2 ≤ z.re) :
    ‖riemannZeta z‖ ≤ 2 := by
  have h := norm_zeta_sub_one_le_of_two_le_re hz
  have htri : ‖riemannZeta z‖ ≤ ‖riemannZeta z - 1‖ + 1 := by
    simpa [norm_one] using norm_add_le (riemannZeta z - 1) 1
  linarith

lemma riemannZeta_mem_slitPlane_of_two_le_re {z : ℂ} (hz : 2 ≤ z.re) :
    riemannZeta z ∈ Complex.slitPlane := by
  left
  have h := norm_zeta_sub_one_le_of_two_le_re hz
  have hre : |(riemannZeta z - 1).re| ≤ ‖riemannZeta z - 1‖ := Complex.abs_re_le_norm _
  rw [Complex.sub_re, Complex.one_re, abs_le] at hre
  linarith

lemma norm_log_zeta_le_six_of_two_le_re {z : ℂ} (hz : 2 ≤ z.re) :
    ‖Complex.log (riemannZeta z)‖ ≤ 6 := by
  have hge := norm_zeta_ge_quarter_of_two_le_re hz
  have hle := norm_zeta_le_two_of_two_le_re hz
  have hpos : 0 < ‖riemannZeta z‖ := by linarith
  have hlog_abs : |Real.log ‖riemannZeta z‖| ≤ 2 := by
    rw [abs_le]
    have h4 : (4 : ℝ) ≤ Real.exp 2 := by
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have he1 := Real.add_one_le_exp (1 : ℝ)
      nlinarith [Real.exp_pos 1]
    have hlog4 : Real.log 4 ≤ 2 := by
      calc Real.log 4 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) h4
        _ = 2 := Real.log_exp 2
    constructor
    · have : Real.log (1 / 4) ≤ Real.log ‖riemannZeta z‖ := Real.log_le_log (by norm_num) hge
      rw [one_div, Real.log_inv] at this
      linarith
    · have : Real.log ‖riemannZeta z‖ ≤ Real.log 2 := Real.log_le_log hpos hle
      have : Real.log 2 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
      linarith
  have hnorm : ‖Complex.log (riemannZeta z)‖ ≤ |Real.log ‖riemannZeta z‖| + |(riemannZeta z).arg| := by
    have := Complex.norm_le_abs_re_add_abs_im (Complex.log (riemannZeta z))
    simpa [Complex.log_re, Complex.log_im] using this
  have harg : |(riemannZeta z).arg| ≤ Real.pi := Complex.abs_arg_le_pi _
  linarith [Real.pi_lt_four]

/-- Holomorphic logarithm of `riemannZeta` on the upper quarter-plane `{z | 1/2 < z.re ∧ 0 < z.im}`,
defined by horizontal integration from `2 + i z.im`. -/
noncomputable def logZeta (z : ℂ) : ℂ :=
  Complex.log (riemannZeta (2 + (z.im : ℂ) * I)) -
    ∫ u in z.re..2, (deriv riemannZeta ((u : ℂ) + (z.im : ℂ) * I) /
      riemannZeta ((u : ℂ) + (z.im : ℂ) * I))

/-- `deriv riemannZeta / riemannZeta` is holomorphic on `{z | 1/2 < z.re ∧ 0 < z.im}` under RH. -/
lemma differentiableOn_logDerivZeta (rh : RiemannHypothesis) :
    DifferentiableOn ℂ (fun z => deriv riemannZeta z / riemannZeta z)
      {z : ℂ | (1 / 2 : ℝ) < z.re ∧ 0 < z.im} := by
  have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re ∧ 0 < z.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hzeta_diff : DifferentiableOn ℂ riemannZeta {z : ℂ | (1 / 2 : ℝ) < z.re ∧ 0 < z.im} := by
    intro z hz
    have h1 : z ≠ 1 := fun h => by subst h; simp at hz
    exact (differentiableAt_riemannZeta h1).differentiableWithinAt
  have hderiv_diff : DifferentiableOn ℂ (deriv riemannZeta) {z : ℂ | (1 / 2 : ℝ) < z.re ∧ 0 < z.im} :=
    hzeta_diff.deriv hopen
  intro z hz
  have h1 : z ≠ 1 := fun h => by subst h; simp at hz
  exact (hderiv_diff z hz).div (hzeta_diff z hz) (BN3.riemannZeta_ne_zero_of_rh rh hz.1 h1)

set_option maxHeartbeats 600000 in
/-- `logZeta` has complex derivative `deriv ζ / ζ` on `{z | 1/2 < z.re ∧ 0 < z.im}` under RH. -/
theorem hasDerivAt_logZeta (rh : RiemannHypothesis) {z : ℂ} (hre : (1 / 2 : ℝ) < z.re)
    (him : 0 < z.im) :
    HasDerivAt logZeta (deriv riemannZeta z / riemannZeta z) z := by
  let φ : ℂ → ℂ := fun w => deriv riemannZeta w / riemannZeta w
  let U : Set ℂ := {w : ℂ | (1 / 2 : ℝ) < w.re ∧ 0 < w.im}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hφ_diff : DifferentiableOn ℂ φ U := differentiableOn_logDerivZeta rh
  have hφ_cont : ContinuousOn φ U := hφ_diff.continuousOn
  set δ : ℝ := min (z.re - 1 / 2) z.im / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdiff_eq : ∀ w ∈ Metric.ball z δ,
      logZeta w - logZeta z =
        (∫ u in z.re..w.re, φ ((u : ℂ) + (z.im : ℂ) * I)) +
        I * (∫ v in z.im..w.im, φ ((w.re : ℂ) + (v : ℂ) * I)) := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hw_re : 1 / 2 < w.re := by
      have h1 : |w.re - z.re| ≤ ‖w - z‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
      rw [abs_le] at h1
      have : δ ≤ (z.re - 1 / 2) / 2 := by dsimp [δ]; linarith [min_le_left (z.re - 1 / 2) z.im]
      linarith
    have hw_im : 0 < w.im := by
      have h1 : |w.im - z.im| ≤ ‖w - z‖ := by
        simpa [Complex.sub_im] using Complex.abs_im_le_norm (w - z)
      rw [abs_le] at h1
      have : δ ≤ z.im / 2 := by dsimp [δ]; linarith [min_le_right (z.re - 1 / 2) z.im]
      linarith
    have hrect_sub : Set.uIcc w.re 2 ×ℂ Set.uIcc z.im w.im ⊆ U := by
      rintro u ⟨hu1, hu2⟩
      constructor
      · have hmin : min w.re 2 ≤ u.re := (Set.mem_uIcc.mp hu1).elim (fun h => le_trans (min_le_left _ _) h.1)
          (fun h => le_trans (min_le_right _ _) h.1)
        exact lt_of_lt_of_le (lt_min hw_re (by norm_num)) hmin
      · have hmin : min z.im w.im ≤ u.im := (Set.mem_uIcc.mp hu2).elim (fun h => le_trans (min_le_left _ _) h.1)
          (fun h => le_trans (min_le_right _ _) h.1)
        exact lt_of_lt_of_le (lt_min him hw_im) hmin
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn φ
      ((w.re : ℂ) + (z.im : ℂ) * I) ((2 : ℂ) + (w.im : ℂ) * I) (by
        refine hφ_diff.mono ?_
        simpa [Complex.re_add_im] using hrect_sub)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, zero_add, Complex.re_ofNat, Complex.im_ofNat, smul_eq_mul] at hrect
    -- Evaluate the right vertical edge `x = 2` by 1D FTC on `Complex.log (riemannZeta (2 + v * I))`.
    have hright : I * ∫ v in z.im..w.im, φ (2 + (v : ℂ) * I) =
        Complex.log (riemannZeta (2 + (w.im : ℂ) * I)) -
        Complex.log (riemannZeta (2 + (z.im : ℂ) * I)) := by
      have hderiv_v : ∀ v ∈ Set.uIcc z.im w.im,
          HasDerivAt (fun t : ℝ => Complex.log (riemannZeta (2 + (t : ℂ) * I)))
            (I * φ (2 + (v : ℂ) * I)) v := by
        intro v _
        have harg : HasDerivAt (fun t : ℝ => (2 : ℂ) + (t : ℂ) * I) I v := by
          have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) (1 * I) v :=
            (Complex.ofRealCLM.hasDerivAt (x := v)).mul_const I
          rw [one_mul] at h1
          exact h1.const_add (2 : ℂ)
        have hne1 : (2 : ℂ) + (v : ℂ) * I ≠ 1 := fun h => by
          have := congrArg Complex.re h; simp at this
        have hz_d : HasDerivAt riemannZeta (deriv riemannZeta (2 + (v : ℂ) * I)) (2 + (v : ℂ) * I) :=
          (differentiableAt_riemannZeta hne1).hasDerivAt
        have hcomp : HasDerivAt (fun t : ℝ => riemannZeta (2 + (t : ℂ) * I))
            (deriv riemannZeta (2 + (v : ℂ) * I) * I) v := hz_d.comp v harg
        have hslit : riemannZeta (2 + (v : ℂ) * I) ∈ Complex.slitPlane :=
          riemannZeta_mem_slitPlane_of_two_le_re (by simp)
        have hlog := (Complex.hasDerivAt_log hslit).comp v hcomp
        have heq : (riemannZeta (2 + (v : ℂ) * I))⁻¹ * (deriv riemannZeta (2 + (v : ℂ) * I) * I) =
            I * φ (2 + (v : ℂ) * I) := by dsimp [φ]; ring
        rw [heq] at hlog
        exact hlog
      have hint_v : IntervalIntegrable (fun v : ℝ => I * φ (2 + (v : ℂ) * I)) volume z.im w.im := by
        refine ContinuousOn.intervalIntegrable ?_
        refine continuousOn_const.mul (hφ_cont.comp (by fun_prop) fun v hv => ?_)
        exact hrect_sub ⟨by simp, by simp [hv]⟩
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_v hint_v
    have hint_bot1 : IntervalIntegrable (fun u : ℝ => φ ((u : ℂ) + (z.im : ℂ) * I)) volume z.re w.re := by
      refine ContinuousOn.intervalIntegrable ?_
      refine hφ_cont.comp (by fun_prop) fun u hu => ?_
      have hu_re : 1 / 2 < u := by
        have hmin : min z.re w.re ≤ u := (Set.mem_uIcc.mp hu).elim (fun h => le_trans (min_le_left _ _) h.1)
          (fun h => le_trans (min_le_right _ _) h.1)
        exact lt_of_lt_of_le (lt_min hre hw_re) hmin
      exact ⟨by simp; linarith, by simp [him]⟩
    have hint_bot2 : IntervalIntegrable (fun u : ℝ => φ ((u : ℂ) + (z.im : ℂ) * I)) volume w.re 2 := by
      refine ContinuousOn.intervalIntegrable ?_
      refine hφ_cont.comp (by fun_prop) fun u hu => ?_
      exact hrect_sub ⟨by simp [hu], by simp⟩
    have hsplit : (∫ u in z.re..w.re, φ ((u : ℂ) + (z.im : ℂ) * I)) +
        (∫ u in w.re..2, φ ((u : ℂ) + (z.im : ℂ) * I)) =
        ∫ u in z.re..2, φ ((u : ℂ) + (z.im : ℂ) * I) :=
      intervalIntegral.integral_add_adjacent_intervals hint_bot1 hint_bot2
    dsimp [logZeta]
    linear_combination hrect - hright - hsplit
  -- Show `(logZeta w - logZeta z - φ z * (w - z)) = o(w - z)` using continuity of `φ` at `z`.
  rw [hasDerivAt_iff_isLittleO]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hφ_contAt : ContinuousAt φ z := hφ_cont.continuousAt (hU_open.mem_nhds ⟨hre, him⟩)
  rw [Metric.continuousAt_iff] at hφ_contAt
  obtain ⟨r, hr, hr_ball⟩ := hφ_contAt (c / 2) (half_pos hc)
  have hmin_pos : 0 < min δ (r / 2) := lt_min hδ (half_pos hr)
  filter_upwards [Metric.ball_mem_nhds z hmin_pos] with w hw
  have hw_δ : w ∈ Metric.ball z δ := Metric.ball_subset_ball (min_le_left _ _) hw
  have hw_r : ‖w - z‖ < r / 2 := by
    have := Metric.mem_ball.mp (Metric.ball_subset_ball (min_le_right _ _) hw)
    rwa [dist_eq_norm] at this
  rw [hdiff_eq w hw_δ]
  have hlin : φ z * (w - z) =
      (∫ _u in z.re..w.re, φ z) + I * (∫ _v in z.im..w.im, φ z) := by
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const,
      Complex.real_smul, Complex.real_smul]
    have hwz : w - z = ((w.re - z.re : ℝ) : ℂ) + I * ((w.im - z.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hwz]; ring
  rw [show ((∫ u in z.re..w.re, φ ((u : ℂ) + (z.im : ℂ) * I)) +
      I * (∫ v in z.im..w.im, φ ((w.re : ℂ) + (v : ℂ) * I))) - (w - z) • φ z =
      ((∫ u in z.re..w.re, (φ ((u : ℂ) + (z.im : ℂ) * I) - φ z)) +
       I * (∫ v in z.im..w.im, (φ ((w.re : ℂ) + (v : ℂ) * I) - φ z))) by
    rw [smul_eq_mul, mul_comm (w - z), hlin,
      intervalIntegral.integral_sub _ intervalIntegrable_const,
      intervalIntegral.integral_sub _ intervalIntegrable_const]
    · ring
    · refine ContinuousOn.intervalIntegrable ?_
      refine hφ_cont.comp (by fun_prop) fun v hv => ?_
      have hdist : ‖((w.re : ℂ) + (v : ℂ) * I) - z‖ < δ := by
        have hv_le : |v - z.im| ≤ |w.im - z.im| := by
          rcases Set.mem_uIcc.mp hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
            rw [abs_le] <;> constructor <;> linarith [le_abs_self (w.im - z.im), neg_abs_le (w.im - z.im)]
        have hre_le : |w.re - z.re| ≤ ‖w - z‖ := by
          simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
        have him_le : |w.im - z.im| ≤ ‖w - z‖ := by
          simpa [Complex.sub_im] using Complex.abs_im_le_norm (w - z)
        have hsq : ‖((w.re : ℂ) + (v : ℂ) * I) - z‖ ^ 2 ≤ ‖w - z‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
          simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero,
            Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add]
          have : (v - z.im) ^ 2 ≤ (w.im - z.im) ^ 2 := by
            rw [← sq_abs (v - z.im), ← sq_abs (w.im - z.im)]
            exact pow_le_pow_left₀ (abs_nonneg _) hv_le 2
          nlinarith
        have hle := le_of_sq_le_sq hsq (norm_nonneg _)
        exact lt_of_le_of_lt hle (by simpa [Metric.mem_ball, dist_eq_norm] using hw_δ)
      have h1 : |(w.re : ℝ) - z.re| ≤ ‖((w.re : ℂ) + (v : ℂ) * I) - z‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (((w.re : ℂ) + (v : ℂ) * I) - z)
      have h2 : |v - z.im| ≤ ‖((w.re : ℂ) + (v : ℂ) * I) - z‖ := by
        simpa [Complex.sub_im] using Complex.abs_im_le_norm (((w.re : ℂ) + (v : ℂ) * I) - z)
      rw [abs_le] at h1 h2
      have hδ1 : δ ≤ (z.re - 1 / 2) / 2 := by dsimp [δ]; linarith [min_le_left (z.re - 1 / 2) z.im]
      have hδ2 : δ ≤ z.im / 2 := by dsimp [δ]; linarith [min_le_right (z.re - 1 / 2) z.im]
      exact ⟨by simp; linarith, by simp; linarith⟩
    · refine ContinuousOn.intervalIntegrable ?_
      refine hφ_cont.comp (by fun_prop) fun u hu => ?_
      have hu_le : |u - z.re| ≤ |w.re - z.re| := by
        rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rw [abs_le] <;> constructor <;> linarith [le_abs_self (w.re - z.re), neg_abs_le (w.re - z.re)]
      have hre_le : |w.re - z.re| ≤ ‖w - z‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
      have hδ1 : δ ≤ (z.re - 1 / 2) / 2 := by dsimp [δ]; linarith [min_le_left (z.re - 1 / 2) z.im]
      have hwd : ‖w - z‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hw_δ
      rw [abs_le] at hu_le
      exact ⟨by simp; linarith, by simp [him]⟩]
  have hb1 : ‖∫ u in z.re..w.re, (φ ((u : ℂ) + (z.im : ℂ) * I) - φ z)‖ ≤ (c / 2) * |w.re - z.re| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
    have hu_le : |u - z.re| ≤ |w.re - z.re| := by
      rcases Set.mem_uIoc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rw [abs_le] <;> constructor <;> linarith [le_abs_self (w.re - z.re), neg_abs_le (w.re - z.re)]
    have hre_le : |w.re - z.re| ≤ ‖w - z‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
    have hdist : dist ((u : ℂ) + (z.im : ℂ) * I) z < r := by
      have heq : ((u : ℂ) + (z.im : ℂ) * I) - z = ((u - z.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [dist_eq_norm, heq, Complex.norm_real, Real.norm_eq_abs]
      linarith
    exact (by simpa [dist_eq_norm] using (hr_ball hdist).le)
  have hb2 : ‖∫ v in z.im..w.im, (φ ((w.re : ℂ) + (v : ℂ) * I) - φ z)‖ ≤ (c / 2) * |w.im - z.im| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun v hv => ?_
    have hv_le : |v - z.im| ≤ |w.im - z.im| := by
      rcases Set.mem_uIoc.mp hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rw [abs_le] <;> constructor <;> linarith [le_abs_self (w.im - z.im), neg_abs_le (w.im - z.im)]
    have hre_le : |w.re - z.re| ≤ ‖w - z‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
    have him_le : |w.im - z.im| ≤ ‖w - z‖ := by
      simpa [Complex.sub_im] using Complex.abs_im_le_norm (w - z)
    have hdist : dist ((w.re : ℂ) + (v : ℂ) * I) z < r := by
      rw [dist_eq_norm]
      have htri : ‖((w.re : ℂ) + (v : ℂ) * I) - z‖ ≤ |w.re - z.re| + |v - z.im| := by
        have := Complex.norm_le_abs_re_add_abs_im (((w.re : ℂ) + (v : ℂ) * I) - z)
        simpa using this
      linarith
    exact (by simpa [dist_eq_norm] using (hr_ball hdist).le)
  have hre_le : |w.re - z.re| ≤ ‖w - z‖ := by
    simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
  have him_le : |w.im - z.im| ≤ ‖w - z‖ := by
    simpa [Complex.sub_im] using Complex.abs_im_le_norm (w - z)
  calc ‖(∫ u in z.re..w.re, (φ ((u : ℂ) + (z.im : ℂ) * I) - φ z)) +
        I * (∫ v in z.im..w.im, (φ ((w.re : ℂ) + (v : ℂ) * I) - φ z))‖
      ≤ ‖∫ u in z.re..w.re, (φ ((u : ℂ) + (z.im : ℂ) * I) - φ z)‖ +
        ‖I * (∫ v in z.im..w.im, (φ ((w.re : ℂ) + (v : ℂ) * I) - φ z))‖ := norm_add_le _ _
    _ = ‖∫ u in z.re..w.re, (φ ((u : ℂ) + (z.im : ℂ) * I) - φ z)‖ +
        ‖∫ v in z.im..w.im, (φ ((w.re : ℂ) + (v : ℂ) * I) - φ z)‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ (c / 2) * |w.re - z.re| + (c / 2) * |w.im - z.im| := add_le_add hb1 hb2
    _ ≤ (c / 2) * ‖w - z‖ + (c / 2) * ‖w - z‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hre_le (by positivity))
          (mul_le_mul_of_nonneg_left him_le (by positivity))
    _ = c * ‖w - z‖ := by ring

/-- `exp (logZeta z) = riemannZeta z` on `{z | 1/2 < z.re ∧ 0 < z.im}` under RH. -/
theorem exp_logZeta_eq (rh : RiemannHypothesis) {z : ℂ} (hre : (1 / 2 : ℝ) < z.re)
    (him : 0 < z.im) : Complex.exp (logZeta z) = riemannZeta z := by
  let G : ℂ → ℂ := fun w => riemannZeta w * Complex.exp (-logZeta w)
  have hG_deriv : ∀ w : ℂ, (1 / 2 : ℝ) < w.re → 0 < w.im → HasDerivAt G 0 w := by
    intro w hw1 hw2
    have h1 : w ≠ 1 := fun h => by subst h; simp at hw2
    have hne : riemannZeta w ≠ 0 := BN3.riemannZeta_ne_zero_of_rh rh hw1 h1
    have hd1 : HasDerivAt riemannZeta (deriv riemannZeta w) w :=
      (differentiableAt_riemannZeta h1).hasDerivAt
    have hd2 : HasDerivAt (fun u => Complex.exp (-logZeta u))
        (Complex.exp (-logZeta w) * -(deriv riemannZeta w / riemannZeta w)) w :=
      (hasDerivAt_logZeta rh hw1 hw2).neg.cexp
    have hmul := hd1.mul hd2
    have hzero : deriv riemannZeta w * Complex.exp (-logZeta w) +
        riemannZeta w * (Complex.exp (-logZeta w) * -(deriv riemannZeta w / riemannZeta w)) = 0 := by
      field_simp [hne]; ring
    rwa [hzero] at hmul
  -- Integrate `0` along the straight line `t ↦ (2 + I) + t * (z - (2 + I))` for `t ∈ [0, 1]`.
  set z₀ : ℂ := 2 + I
  have hline_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => G (z₀ + (u : ℂ) * (z - z₀))) 0 t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hre_t : 1 / 2 < (z₀ + (t : ℂ) * (z - z₀)).re := by
      simp only [z₀, Complex.add_re, Complex.re_ofNat, Complex.I_re, add_zero, Complex.mul_re,
        Complex.ofReal_re, Complex.sub_re, Complex.ofReal_im, zero_mul, sub_zero]
      rcases eq_or_lt_of_le ht.1 with rfl | ht0
      · norm_num
      · nlinarith [ht.2]
    have him_t : 0 < (z₀ + (t : ℂ) * (z - z₀)).im := by
      simp only [z₀, Complex.add_im, Complex.im_ofNat, Complex.I_im, zero_add, Complex.mul_im,
        Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_mul, add_zero]
      rcases eq_or_lt_of_le ht.1 with rfl | ht0
      · norm_num
      · nlinarith [ht.2]
    have harg : HasDerivAt (fun u : ℝ => z₀ + (u : ℂ) * (z - z₀)) (z - z₀) t := by
      have h1 : HasDerivAt (fun u : ℝ => (u : ℂ) * (z - z₀)) (1 * (z - z₀)) t :=
        (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (z - z₀)
      rw [one_mul] at h1
      exact h1.const_add z₀
    have hc := (hG_deriv _ hre_t him_t).comp t harg
    rw [zero_mul] at hc
    exact hc
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hline_deriv intervalIntegrable_const
  simp only [intervalIntegral.integral_zero, Complex.ofReal_one, one_mul, add_sub_cancel,
    Complex.ofReal_zero, zero_mul, add_zero] at hftc
  have hG_const : G z = G z₀ := sub_eq_zero.mp hftc.symm
  have hG2 : G z₀ = 1 := by
    dsimp [G, logZeta, z₀]
    simp only [add_zero, zero_add, Complex.ofReal_one, one_mul,
      intervalIntegral.integral_same, sub_zero, Complex.exp_neg]
    have hne : riemannZeta (2 + I) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by simp)
    rw [Complex.exp_log hne, mul_inv_cancel₀ hne]
  rw [hG2] at hG_const
  dsimp [G] at hG_const
  rw [Complex.exp_neg] at hG_const
  have hexp_ne : Complex.exp (logZeta z) ≠ 0 := Complex.exp_ne_zero _
  calc Complex.exp (logZeta z)
      = 1 * Complex.exp (logZeta z) := (one_mul _).symm
    _ = riemannZeta z * (Complex.exp (logZeta z))⁻¹ * Complex.exp (logZeta z) := by rw [← hG_const]
    _ = riemannZeta z := by rw [mul_assoc, inv_mul_cancel₀ hexp_ne, mul_one]

/-- On `Re(z) ≥ 2, Im(z) > 0`, `logZeta z = Complex.log (riemannZeta z)`, hence `‖logZeta z‖ ≤ 6`. -/
theorem norm_logZeta_le_six_of_two_le_re (rh : RiemannHypothesis) {z : ℂ} (hre : 2 ≤ z.re)
    (him : 0 < z.im) : ‖logZeta z‖ ≤ 6 := by
  have heq : logZeta z = Complex.log (riemannZeta z) := by
    dsimp [logZeta]
    have hderiv_u : ∀ u ∈ Set.uIcc z.re 2,
        HasDerivAt (fun t : ℝ => Complex.log (riemannZeta ((t : ℂ) + (z.im : ℂ) * I)))
          (deriv riemannZeta ((u : ℂ) + (z.im : ℂ) * I) /
            riemannZeta ((u : ℂ) + (z.im : ℂ) * I)) u := by
      intro u hu
      have hu2 : 2 ≤ u := by
        rcases Set.mem_uIcc.mp hu with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
      have harg : HasDerivAt (fun t : ℝ => (t : ℂ) + (z.im : ℂ) * I) 1 u := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).add_const ((z.im : ℂ) * I)
      have hne1 : (u : ℂ) + (z.im : ℂ) * I ≠ 1 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      have hcomp : HasDerivAt (fun t : ℝ => riemannZeta ((t : ℂ) + (z.im : ℂ) * I))
          (deriv riemannZeta ((u : ℂ) + (z.im : ℂ) * I) * 1) u :=
        (differentiableAt_riemannZeta hne1).hasDerivAt.comp u harg
      have hslit : riemannZeta ((u : ℂ) + (z.im : ℂ) * I) ∈ Complex.slitPlane :=
        riemannZeta_mem_slitPlane_of_two_le_re (by simp [hu2])
      have hlog := (Complex.hasDerivAt_log hslit).comp u hcomp
      have heq : (riemannZeta ((u : ℂ) + (z.im : ℂ) * I))⁻¹ *
          (deriv riemannZeta ((u : ℂ) + (z.im : ℂ) * I) * 1) =
          deriv riemannZeta ((u : ℂ) + (z.im : ℂ) * I) /
          riemannZeta ((u : ℂ) + (z.im : ℂ) * I) := by ring
      rw [heq] at hlog
      exact hlog
    have hint : IntervalIntegrable
        (fun u : ℝ => deriv riemannZeta ((u : ℂ) + (z.im : ℂ) * I) /
          riemannZeta ((u : ℂ) + (z.im : ℂ) * I)) volume z.re 2 := by
      refine ContinuousOn.intervalIntegrable ?_
      refine (differentiableOn_logDerivZeta rh).continuousOn.comp (by fun_prop) fun u hu => ?_
      have hu2 : 2 ≤ u := by
        rcases Set.mem_uIcc.mp hu with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
      exact ⟨by simp; linarith, by simp [him]⟩
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_u hint, Complex.re_add_im]
    have h2eq : ((2 : ℝ) : ℂ) + (z.im : ℂ) * I = 2 + (z.im : ℂ) * I := by norm_num
    rw [h2eq]
    ring
  rw [heq]
  exact norm_log_zeta_le_six_of_two_le_re hre

set_option maxHeartbeats 800000 in
/-- Titchmarsh Theorem 14.2: under RH, `‖logZeta z‖ ≤ η * log (2 + z.im) + C`
for `1/2 + δ ≤ z.re ≤ 2` and `4 ≤ z.im`. -/
theorem norm_logZeta_le_of_rh (rh : RiemannHypothesis) {δ η : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (hη : 0 < η) :
    ∃ C > 0, ∀ z : ℂ, 1 / 2 + δ ≤ z.re → z.re ≤ 2 → 4 ≤ z.im →
      ‖logZeta z‖ ≤ η * Real.log (2 + z.im) + C := by
  set r₁ : ℝ := 1
  set r₂ : ℝ := 5 / 2 - δ
  set r₃ : ℝ := 5 / 2 - δ / 2
  set R : ℝ := 5 / 2 - δ / 4
  have hr₁ : 0 < r₁ := by positivity
  have h12 : r₁ < r₂ := by dsimp [r₁, r₂]; linarith
  have h23 : r₂ < r₃ := by dsimp [r₂, r₃]; linarith
  have h3R : r₃ < R := by dsimp [r₃, R]; linarith
  set α : ℝ := Real.log (r₂ / r₁) / Real.log (r₃ / r₁)
  have hα_pos : 0 < α := div_pos (Real.log_pos ((one_lt_div hr₁).mpr h12))
    (Real.log_pos ((one_lt_div hr₁).mpr (lt_trans h12 h23)))
  have hα_lt1 : α < 1 := by
    rw [div_lt_one (Real.log_pos ((one_lt_div hr₁).mpr (lt_trans h12 h23)))]
    exact Real.log_lt_log (div_pos (lt_trans hr₁ h12) hr₁) (div_lt_div_of_pos_right h23 hr₁)
  -- Constants for Borel-Caratheodory on `D(3 + i t, R)`
  set K : ℝ := 2 * r₃ / (R - r₃)
  have hK_pos : 0 < K := div_pos (by linarith) (sub_pos.mpr h3R)
  set A₁ : ℝ := K + 1
  set A₂ : ℝ := K * (Real.log 48 + 6) + 7
  have hA₁_pos : 0 < A₁ := by positivity
  have hA₂_pos : 0 < A₂ := by
    have : 0 ≤ Real.log 48 := Real.log_nonneg (by norm_num)
    positivity
  -- Use Young's inequality / elementary `u^α ≤ ε u + C` for `0 < α < 1`:
  -- For `x ≥ 1`, `(6^(1-α) * (A₁ * x + A₂)^α) ≤ η * x + C`.
  set B₀ : ℝ := (6 : ℝ) ^ (1 - α) * (A₁ + A₂) ^ α
  have hB₀_pos : 0 < B₀ := by positivity
  -- Since `α < 1`, for `u ≥ 1`, `u^α = u * u^(α - 1)`: if `u ≥ (B₀ / η)^(1 / (1 - α))`, then `B₀ * u^α ≤ η * u`.
  set U₀ : ℝ := max 1 ((B₀ / η) ^ (1 / (1 - α)))
  set C : ℝ := max 1 (B₀ * U₀ ^ α)
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun z hre1 hre2 him => ?_⟩
  set t : ℝ := z.im
  set z₀ : ℂ := (3 : ℂ) + (t : ℂ) * I
  have hball_U : ∀ w ∈ Metric.closedBall z₀ R, (1 / 2 : ℝ) < w.re ∧ 0 < w.im := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have hre_w : |w.re - 3| ≤ R := by
      have := Complex.abs_re_le_norm (w - z₀)
      simpa [z₀] using this.trans hw
    have him_w : |w.im - t| ≤ R := by
      have := Complex.abs_im_le_norm (w - z₀)
      simpa [z₀] using this.trans hw
    rw [abs_le] at hre_w him_w
    dsimp [R] at hre_w him_w
    exact ⟨by linarith, by linarith⟩
  have hlog_diff : DifferentiableOn ℂ logZeta (Metric.closedBall z₀ R) := fun w hw =>
    (hasDerivAt_logZeta rh (hball_U w hw).1 (hball_U w hw).2).differentiableAt.differentiableWithinAt
  have hre_bound : ∀ w ∈ Metric.closedBall z₀ R,
      (logZeta w).re ≤ Real.log (48 * (2 + t)) := by
    intro w hw
    have hU := hball_U w hw
    have hexp := exp_logZeta_eq rh hU.1 hU.2
    have hnorm_exp : Real.exp (logZeta w).re = ‖riemannZeta w‖ := by
      rw [← hexp, Complex.norm_exp]
    have hne0 : riemannZeta w ≠ 0 := by
      rw [← hexp]; exact Complex.exp_ne_zero _
    have hlog_eq : (logZeta w).re = Real.log ‖riemannZeta w‖ := by
      rw [← hnorm_exp, Real.log_exp]
    rw [hlog_eq]
    have hw_re14 : (1 / 4 : ℝ) ≤ w.re := by linarith [hU.1]
    have hw_im1 : (1 : ℝ) ≤ w.im := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      have him_w : |w.im - t| ≤ R := by
        have := Complex.abs_im_le_norm (w - z₀)
        simpa [z₀] using this.trans hw
      rw [abs_le] at him_w
      dsimp [R] at him_w
      linarith
    have hw_sub1 : (1 / 2 : ℝ) ≤ ‖w - 1‖ := by
      have := Complex.abs_im_le_norm (w - 1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
      linarith [le_abs_self w.im]
    have hzeta_le := BN2.norm_riemannZeta_le_six_mul_norm hw_re14 hw_sub1
    have hw_norm : ‖w‖ ≤ 8 * (2 + t) := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      have htri : ‖w‖ ≤ ‖w - z₀‖ + ‖z₀‖ := by simpa using norm_add_le (w - z₀) z₀
      have hz0_norm : ‖z₀‖ ≤ 3 + t := by
        have := Complex.norm_le_abs_re_add_abs_im z₀
        simp only [z₀, Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero,
          Complex.add_im, Complex.im_ofNat, Complex.mul_im, zero_add] at this
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos (by linarith : 0 < t)] at this
        exact this
      dsimp [R] at hw
      linarith
    have h6w : ‖riemannZeta w‖ ≤ 48 * (2 + t) := by linarith
    exact Real.log_le_log (norm_pos_iff.mpr hne0) h6w
  have hz0_le6 : ‖logZeta z₀‖ ≤ 6 :=
    norm_logZeta_le_six_of_two_le_re rh (by simp [z₀]; norm_num) (by simp [z₀]; linarith)
  have hM3_bound : ∀ w, ‖w - z₀‖ = r₃ → ‖logZeta w‖ ≤ A₁ * Real.log (2 + t) + A₂ := by
    intro w hw
    have hw_cl : w ∈ Metric.closedBall z₀ r₃ := by rw [Metric.mem_closedBall, dist_eq_norm, hw]
    have hbc := borel_caratheodory (by linarith : 0 < r₃) h3R hlog_diff hre_bound w hw_cl
    have htri : ‖logZeta w‖ ≤ ‖logZeta w - logZeta z₀‖ + ‖logZeta z₀‖ := by
      simpa using norm_add_le (logZeta w - logZeta z₀) (logZeta z₀)
    have hre_z0 : -(logZeta z₀).re ≤ 6 := by
      have := Complex.abs_re_le_norm (logZeta z₀)
      rw [abs_le] at this
      linarith
    have hlog_split : Real.log (48 * (2 + t)) = Real.log 48 + Real.log (2 + t) :=
      Real.log_mul (by norm_num) (by linarith)
    rw [hlog_split] at hbc
    have hlog_pos : 0 ≤ Real.log (2 + t) := Real.log_nonneg (by linarith)
    have hK_eq : 2 * r₃ / (R - r₃) = K := rfl
    rw [hK_eq] at hbc
    dsimp [A₁, A₂]
    nlinarith
  have hM1_bound : ∀ w, ‖w - z₀‖ = r₁ → ‖logZeta w‖ ≤ 6 := by
    intro w hw
    have hre_w : |w.re - 3| ≤ 1 := by
      have := Complex.abs_re_le_norm (w - z₀)
      simpa [z₀, r₁] using this.trans hw.le
    have him_w : |w.im - t| ≤ 1 := by
      have := Complex.abs_im_le_norm (w - z₀)
      simpa [z₀, r₁] using this.trans hw.le
    rw [abs_le] at hre_w him_w
    exact norm_logZeta_le_six_of_two_le_re rh (by linarith) (by linarith)
  set M₃ : ℝ := A₁ * Real.log (2 + t) + A₂
  have hM₃_ge1 : 1 ≤ M₃ := by
    have : 0 ≤ Real.log (2 + t) := Real.log_nonneg (by linarith)
    dsimp [M₃, A₁, A₂]
    have : 0 ≤ Real.log 48 := Real.log_nonneg (by norm_num)
    nlinarith
  have hz_in : z ∈ Metric.closedBall z₀ r₂ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : z - z₀ = ((z.re - 3 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [z₀, t]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    dsimp [r₂]; linarith
  have h3c := hadamard_three_circles hr₁ h12 h23 (by norm_num : (1 : ℝ) ≤ 6) hM₃_ge1
    (hlog_diff.mono (Metric.closedBall_subset_closedBall h3R.le)) hM1_bound hM3_bound z hz_in
  -- Now bound `6^(1-α) * M₃^α ≤ η * log(2 + t) + C`.
  set L : ℝ := Real.log (2 + t)
  have hL_ge1 : 1 ≤ L := by
    have h6 : Real.exp 1 ≤ 2 + t := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (2 + t) := Real.log_le_log (Real.exp_pos 1) h6
  have hM3_le : M₃ ≤ (A₁ + A₂) * L := by
    dsimp [M₃]; nlinarith
  have hprod_le : (6 : ℝ) ^ (1 - α) * M₃ ^ α ≤ B₀ * L ^ α := by
    calc (6 : ℝ) ^ (1 - α) * M₃ ^ α
        ≤ (6 : ℝ) ^ (1 - α) * ((A₁ + A₂) * L) ^ α := by
          gcongr
      _ = (6 : ℝ) ^ (1 - α) * ((A₁ + A₂) ^ α * L ^ α) := by
          rw [Real.mul_rpow (by positivity) (by linarith)]
      _ = B₀ * L ^ α := by dsimp [B₀]; ring
  have hfinal : B₀ * L ^ α ≤ η * L + C := by
    rcases le_or_gt L U₀ with hle | hgt
    · have : B₀ * L ^ α ≤ B₀ * U₀ ^ α := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hle hα_pos.le) hB₀_pos.le
      have hC : B₀ * U₀ ^ α ≤ C := le_max_right _ _
      nlinarith
    · have h1ma : 0 < 1 - α := sub_pos.mpr hα_lt1
      have hL_gt : (B₀ / η) ^ (1 / (1 - α)) ≤ L := le_trans (le_max_right _ _) hgt.le
      have hpow : B₀ / η ≤ L ^ (1 - α) := by
        have := Real.rpow_le_rpow (by positivity) hL_gt h1ma.le
        rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel h1ma.ne', Real.rpow_one] at this
      have hmul : B₀ ≤ η * L ^ (1 - α) := by
        have := (div_le_iff₀ hη).mp hpow
        linarith
      have hstep : B₀ * L ^ α ≤ η * L := by
        calc B₀ * L ^ α ≤ (η * L ^ (1 - α)) * L ^ α :=
              mul_le_mul_of_nonneg_right hmul (by positivity)
          _ = η * (L ^ (1 - α) * L ^ α) := by ring
          _ = η * L := by
              rw [← Real.rpow_add (by linarith), sub_add_cancel, Real.rpow_one]
      have hC_pos : 0 ≤ C := le_trans zero_le_one (le_max_left _ _)
      linarith
  exact h3c.trans (hprod_le.trans hfinal)

/-- Under RH, for every `δ ∈ (0, 1/4)` and `η > 0`, `‖invZeta z‖ ≤ C * (2 + |z.im|)^η`
for all `z` with `1/2 + δ ≤ z.re`. -/
theorem norm_invZeta_le_rpow (rh : RiemannHypothesis) {δ η : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (hη : 0 < η) :
    ∃ C > 0, ∀ z : ℂ, 1 / 2 + δ ≤ z.re → ‖invZeta z‖ ≤ C * (2 + |z.im|) ^ η := by
  obtain ⟨C₁, hC₁, hlog⟩ := norm_logZeta_le_of_rh rh hδ0 hδ1 hη
  -- Compact bound on `[1/2 + δ, 2] × [-4, 4]`.
  let K : Set ℂ := Set.Icc (1 / 2 + δ) 2 ×ℂ Set.Icc (-4 : ℝ) 4
  have hK_comp : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hK_sub : K ⊆ {z : ℂ | (1 / 2 : ℝ) < z.re} := fun z hz => by
    change (1 / 2 : ℝ) < z.re
    have : 1 / 2 + δ ≤ z.re := hz.1.1; linarith
  have hK_cont : ContinuousOn invZeta K := (differentiableOn_invZeta rh).continuousOn.mono hK_sub
  obtain ⟨M, hM⟩ := hK_comp.exists_bound_of_continuousOn hK_cont
  set C : ℝ := max (max 4 (max M 1)) (Real.exp C₁)
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨C, hC_pos, fun z hre => ?_⟩
  have hrpow_ge1 : (1 : ℝ) ≤ (2 + |z.im|) ^ η :=
    Real.one_le_rpow (by linarith [abs_nonneg z.im]) hη.le
  rcases le_or_gt 2 z.re with hre2 | hre2
  · have hne1 : z ≠ 1 := fun h => by subst h; simp at hre2
    rw [invZeta_of_ne_one hne1, norm_inv]
    have h4 : ‖riemannZeta z‖⁻¹ ≤ 4 := by
      have hge := norm_zeta_ge_quarter_of_two_le_re hre2
      rw [inv_le_iff_one_le_mul₀ (by linarith)]; linarith
    have h4C : (4 : ℝ) ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
    nlinarith
  · rcases le_or_gt |z.im| 4 with him4 | him4
    · have hzK : z ∈ K := ⟨⟨hre, hre2.le⟩, abs_le.mp him4⟩
      have hle : ‖invZeta z‖ ≤ M := hM z hzK
      have hMC : M ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
      nlinarith
    · -- Reduce `z.im < -4` to `z.im > 4` via complex conjugation.
      have hpos_case : ∀ w : ℂ, 1 / 2 + δ ≤ w.re → w.re ≤ 2 → 4 ≤ w.im →
          ‖invZeta w‖ ≤ Real.exp C₁ * (2 + w.im) ^ η := by
        intro w hw1 hw2 hw4
        have hw_ne1 : w ≠ 1 := fun h => by subst h; simp at hw4; linarith
        have hexp := exp_logZeta_eq rh (z := w) (by linarith) (by linarith)
        rw [invZeta_of_ne_one hw_ne1, ← hexp, norm_inv, Complex.norm_exp, ← Real.exp_neg]
        have hbl := hlog w hw1 hw2 hw4
        have hneg_re : -(logZeta w).re ≤ ‖logZeta w‖ := by
          have := Complex.abs_re_le_norm (logZeta w)
          rw [abs_le] at this; linarith
        have hexp_le : Real.exp (-(logZeta w).re) ≤ Real.exp (η * Real.log (2 + w.im) + C₁) :=
          Real.exp_le_exp.mpr (hneg_re.trans hbl)
        have heq : Real.exp (η * Real.log (2 + w.im) + C₁) = Real.exp C₁ * (2 + w.im) ^ η := by
          rw [Real.exp_add, mul_comm η, Real.rpow_def_of_pos (by linarith), mul_comm]
        rwa [heq] at hexp_le
      have hC1C : Real.exp C₁ ≤ C := le_max_right _ _
      rcases le_or_gt 0 z.im with him0 | him0
      · rw [abs_of_nonneg him0] at him4 ⊢
        exact (hpos_case z hre hre2.le him4.le).trans
          (mul_le_mul_of_nonneg_right hC1C (by positivity))
      · have habs : |z.im| = -z.im := abs_of_neg him0
        rw [habs] at him4 ⊢
        have hconj := hpos_case (starRingEnd ℂ z) (by simpa using hre) (by simpa using hre2.le)
          (by simpa using him4.le)
        rw [invZeta_conj, Complex.norm_conj] at hconj
        simp only [Complex.conj_im] at hconj
        exact hconj.trans (mul_le_mul_of_nonneg_right hC1C (by positivity))

/-- Under RH, for every `δ ∈ (0, 1/4)` and `η > 0`, `‖riemannZeta z‖ ≤ C * (2 + |z.im|)^η`
for all `z` with `1/2 + δ ≤ z.re` and `1/2 ≤ ‖z - 1‖`. -/
theorem norm_zeta_le_rpow (rh : RiemannHypothesis) {δ η : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (hη : 0 < η) :
    ∃ C > 0, ∀ z : ℂ, 1 / 2 + δ ≤ z.re → (1 / 2 : ℝ) ≤ ‖z - 1‖ →
      ‖riemannZeta z‖ ≤ C * (2 + |z.im|) ^ η := by
  obtain ⟨C₁, _, hlog⟩ := norm_logZeta_le_of_rh rh hδ0 hδ1 hη
  -- For `1/2 + δ ≤ z.re ≤ 2`, `|z.im| ≤ 4`, `1/2 ≤ ‖z - 1‖`, we already have `‖ζ(z)‖ ≤ 6 * ‖z‖ ≤ 36`!
  set C : ℝ := max 36 (Real.exp C₁)
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨C, hC_pos, fun z hre h1 => ?_⟩
  have hrpow_ge1 : (1 : ℝ) ≤ (2 + |z.im|) ^ η :=
    Real.one_le_rpow (by linarith [abs_nonneg z.im]) hη.le
  rcases le_or_gt 2 z.re with hre2 | hre2
  · have h2 := norm_zeta_le_two_of_two_le_re hre2
    have h36 : (36 : ℝ) ≤ C := le_max_left _ _
    nlinarith
  · rcases le_or_gt |z.im| 4 with him4 | him4
    · have hz_norm : ‖z‖ ≤ 6 := by
        have := Complex.norm_le_abs_re_add_abs_im z
        rw [abs_of_pos (by linarith : 0 < z.re)] at this
        linarith
      have h6 := BN2.norm_riemannZeta_le_six_mul_norm (by linarith : (1 / 4 : ℝ) ≤ z.re) h1
      have h36 : (36 : ℝ) ≤ C := le_max_left _ _
      nlinarith
    · have hpos_case : ∀ w : ℂ, 1 / 2 + δ ≤ w.re → w.re ≤ 2 → 4 ≤ w.im →
          ‖riemannZeta w‖ ≤ Real.exp C₁ * (2 + w.im) ^ η := by
        intro w hw1 hw2 hw4
        have hexp := exp_logZeta_eq rh (z := w) (by linarith) (by linarith)
        rw [← hexp, Complex.norm_exp]
        have hbl := hlog w hw1 hw2 hw4
        have hre_le : (logZeta w).re ≤ ‖logZeta w‖ :=
          (le_abs_self _).trans (Complex.abs_re_le_norm _)
        have hexp_le : Real.exp (logZeta w).re ≤ Real.exp (η * Real.log (2 + w.im) + C₁) :=
          Real.exp_le_exp.mpr (hre_le.trans hbl)
        have heq : Real.exp (η * Real.log (2 + w.im) + C₁) = Real.exp C₁ * (2 + w.im) ^ η := by
          rw [Real.exp_add, mul_comm η, Real.rpow_def_of_pos (by linarith), mul_comm]
        rwa [heq] at hexp_le
      have hC1C : Real.exp C₁ ≤ C := le_max_right _ _
      rcases le_or_gt 0 z.im with him0 | him0
      · rw [abs_of_nonneg him0] at him4 ⊢
        exact (hpos_case z hre hre2.le him4.le).trans
          (mul_le_mul_of_nonneg_right hC1C (by positivity))
      · have habs : |z.im| = -z.im := abs_of_neg him0
        rw [habs] at him4 ⊢
        have hconj := hpos_case (starRingEnd ℂ z) (by simpa using hre) (by simpa using hre2.le)
          (by simpa using him4.le)
        rw [riemannZeta_conj, Complex.norm_conj] at hconj
        simp only [Complex.conj_im] at hconj
        exact hconj.trans (mul_le_mul_of_nonneg_right hC1C (by positivity))

end BN4

/-
# Module 5: Riesz-Perron formula, contour shift, and quantitative error bound under RH

Establishes:
1. Riesz-Perron kernel identity via Fourier inversion on `1_{[0, ∞)}(t) (e^{-2t} - e^{-3t})`.
2. Explicit vertical-line integrals of `1 / (w (w + 1))` on `Re(w) = 2` (equals `0`) and
   `Re(w) = -a` for `0 < a < 1` (equals `-2π`).
3. Integral representation of `D_N(s) = ∑_{a=1}^N μ(a) (1 - a/N) a^{-s}` via Fubini (`integral_tsum`).
4. Cauchy rectangle contour shift to `Re(w) = -ε/2` and uniform error bound
   `‖D_N(1/2 + ε + iτ) - invZeta(1/2 + ε + iτ)‖ ≤ C_ε * N^(-ε/2) * (2 + |τ|)^(1/16)`.
-/

namespace BN5
open MeasureTheory Set Filter Complex ArithmeticFunction FourierTransform
open scoped Topology

/-- Riesz-smoothed Mobius Dirichlet polynomial `∑_{a=1}^N μ(a) (1 - a/N) a^{-s}`. -/
noncomputable def rieszMoebiusSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ i : Fin N,
    (moebius (i.val + 1) : ℂ) * (1 - ((((i.val : ℝ) + 1) / (N : ℝ) : ℝ) : ℂ)) /
      ((i.val + 1 : ℕ) : ℂ) ^ s

/-- Exponential Laplace integral `∫_0^∞ exp (-a * t) dt = 1 / a` for `0 < a.re`. -/
lemma integral_Ioi_cexp_neg_mul {a : ℂ} (ha : 0 < a.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-a * (t : ℂ)) = 1 / a := by
  have ha_ne : a ≠ 0 := fun h => by rw [h, Complex.zero_re] at ha; linarith
  have hint_real : IntegrableOn (fun t : ℝ => Real.exp (-a.re * t)) (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hint : IntegrableOn (fun t : ℝ => Complex.exp (-a * (t : ℂ))) (Ioi (0 : ℝ)) := by
    refine hint_real.mono' (by fun_prop : Continuous fun t : ℝ => Complex.exp (-a * (t : ℂ))).aestronglyMeasurable.restrict ?_
    filter_upwards with t
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hd : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun u : ℝ => -Complex.exp (-a * (u : ℂ)) / a)
        (Complex.exp (-a * (t : ℂ))) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ => -a * (u : ℂ)) (-a) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-a)
    have h2 : HasDerivAt (fun u : ℝ => Complex.exp (-a * (u : ℂ)))
        (Complex.exp (-a * (t : ℂ)) * (-a)) t := h1.cexp
    have h3 : HasDerivAt (fun u : ℝ => -Complex.exp (-a * (u : ℂ)) / a)
        (-(Complex.exp (-a * (t : ℂ)) * (-a)) / a) t := (h2.neg).div_const a
    convert h3 using 1
    field_simp [ha_ne]
  have ht : Tendsto (fun u : ℝ => -Complex.exp (-a * (u : ℂ)) / a) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : (fun u : ℝ => ‖-Complex.exp (-a * (u : ℂ)) / a‖) =
        fun u : ℝ => Real.exp (-a.re * u) / ‖a‖ := by
      ext u
      rw [norm_div, norm_neg, Complex.norm_exp]
      simp [Complex.mul_re]
    rw [hnorm]
    have hexp : Tendsto (fun u : ℝ => Real.exp (-a.re * u)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp
        (Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id)
    simpa using hexp.div_const ‖a‖
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint ht
  simpa [neg_div, neg_neg] using hres

/-- Riesz-Perron kernel identity via Fourier inversion on `1_{[0, ∞)}(t) (e^{-2t} - e^{-3t})`. -/
theorem riesz_perron_kernel {y : ℝ} (hy : 0 < y) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ v : ℝ, (y : ℂ) ^ ((2 : ℂ) + (v : ℂ) * I) /
        (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I)) =
      if 1 ≤ y then (1 - (y : ℂ)⁻¹) else 0 := by
  let φ : ℝ → ℂ := fun t =>
    if 0 ≤ t then ((Real.exp (-2 * t) - Real.exp (-3 * t) : ℝ) : ℂ) else 0
  have hφ_cont : Continuous φ := by
    exact Continuous.if_le (by fun_prop) continuous_const
      continuous_const continuous_id fun t ht => by rw [← ht]; simp
  have hφ_int : Integrable φ volume := by
    have hpos : IntegrableOn φ (Ioi (0 : ℝ)) := by
      have hdom : IntegrableOn (fun t : ℝ => 2 * Real.exp (-2 * t)) (Ioi (0 : ℝ)) :=
        (integrableOn_exp_mul_Ioi (by norm_num) 0).const_mul 2
      refine hdom.mono' hφ_cont.aestronglyMeasurable.restrict ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      dsimp [φ]
      rw [if_pos ht.le, Complex.norm_real, Real.norm_eq_abs]
      have h3le2 : Real.exp (-3 * t) ≤ Real.exp (-2 * t) := Real.exp_le_exp.mpr (by linarith)
      rw [abs_of_nonneg (sub_nonneg.mpr h3le2)]
      linarith [Real.exp_pos (-3 * t)]
    have hneg : IntegrableOn φ (Iic (0 : ℝ)) := by
      have hzero : IntegrableOn (fun _ : ℝ => (0 : ℂ)) (Iic (0 : ℝ)) := integrableOn_zero
      refine hzero.congr_fun (fun t (ht : t ≤ 0) => ?_) measurableSet_Iic
      dsimp [φ]
      rcases eq_or_lt_of_le ht with rfl | hlt
      · simp
      · rw [if_neg (not_le.mpr hlt)]
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact hneg.union hpos
  have hFφ : ∀ ξ : ℝ, 𝓕 φ ξ =
      1 / (((2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
           ((3 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) := by
    intro ξ
    rw [Real.fourier_eq']
    have hsplit : ∫ t : ℝ, Complex.exp (((-2 * Real.pi * inner ℝ t ξ : ℝ) : ℂ) * I) • φ t =
        (∫ t in Iic (0 : ℝ), Complex.exp (((-2 * Real.pi * inner ℝ t ξ : ℝ) : ℂ) * I) • φ t) +
        (∫ t in Ioi (0 : ℝ), Complex.exp (((-2 * Real.pi * inner ℝ t ξ : ℝ) : ℂ) * I) • φ t) := by
      have hint_all : Integrable (fun t : ℝ =>
          Complex.exp (((-2 * Real.pi * inner ℝ t ξ : ℝ) : ℂ) * I) • φ t) volume := by
        refine hφ_int.norm.mono' ?_ (ae_of_all _ fun t => ?_)
        · exact ((by fun_prop : Continuous fun t : ℝ =>
            Complex.exp (((-2 * Real.pi * inner ℝ t ξ : ℝ) : ℂ) * I)).mul hφ_cont).aestronglyMeasurable
        · rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
      exact setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hint_all.integrableOn hint_all.integrableOn
    rw [hsplit]
    have hIic0 : ∫ t in Iic (0 : ℝ), Complex.exp (((-2 * Real.pi * inner ℝ t ξ : ℝ) : ℂ) * I) • φ t = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun t (ht : t ≤ 0) => ?_
      dsimp [φ]
      rcases eq_or_lt_of_le ht with rfl | hlt
      · simp
      · rw [if_neg (not_le.mpr hlt)]; simp
    rw [hIic0, zero_add]
    set a₂ : ℂ := (2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I
    set a₃ : ℂ := (3 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I
    have ha₂_re : 0 < a₂.re := by simp [a₂]
    have ha₃_re : 0 < a₃.re := by simp [a₃]
    have ha₂_ne : a₂ ≠ 0 := fun h => by rw [h, Complex.zero_re] at ha₂_re; linarith
    have ha₃_ne : a₃ ≠ 0 := fun h => by rw [h, Complex.zero_re] at ha₃_re; linarith
    have hcongr : ∫ t in Ioi (0 : ℝ), Complex.exp (((-2 * Real.pi * inner ℝ t ξ : ℝ) : ℂ) * I) • φ t =
        ∫ t in Ioi (0 : ℝ), (Complex.exp (-a₂ * (t : ℂ)) - Complex.exp (-a₃ * (t : ℂ))) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
      dsimp [φ]
      rw [if_pos ht.le]
      simp only [Complex.ofReal_sub, Complex.ofReal_exp, mul_sub, ← Complex.exp_add, conj_trivial]
      congr 2 <;> (dsimp [a₂, a₃]; push_cast; ring)
    have hint₂ : IntegrableOn (fun t : ℝ => Complex.exp (-a₂ * (t : ℂ))) (Ioi (0 : ℝ)) := by
      refine (integrableOn_exp_mul_Ioi (by linarith : -a₂.re < 0) 0).mono'
        (by fun_prop : Continuous fun t : ℝ => Complex.exp (-a₂ * (t : ℂ))).aestronglyMeasurable.restrict ?_
      filter_upwards with t; rw [Complex.norm_exp]; simp [Complex.mul_re]
    have hint₃ : IntegrableOn (fun t : ℝ => Complex.exp (-a₃ * (t : ℂ))) (Ioi (0 : ℝ)) := by
      refine (integrableOn_exp_mul_Ioi (by linarith : -a₃.re < 0) 0).mono'
        (by fun_prop : Continuous fun t : ℝ => Complex.exp (-a₃ * (t : ℂ))).aestronglyMeasurable.restrict ?_
      filter_upwards with t; rw [Complex.norm_exp]; simp [Complex.mul_re]
    rw [hcongr, integral_sub hint₂ hint₃, integral_Ioi_cexp_neg_mul ha₂_re,
      integral_Ioi_cexp_neg_mul ha₃_re]
    have hsub : a₃ - a₂ = 1 := by dsimp [a₂, a₃]; ring
    field_simp [ha₂_ne, ha₃_ne]
    rw [hsub]
  have hFφ_int : Integrable (𝓕 φ) volume := by
    have hinv_sq : Integrable (fun ξ : ℝ => (1 + (2 * Real.pi * ξ) ^ 2)⁻¹) volume := by
      have h1 : Integrable (fun u : ℝ => (1 + u ^ 2)⁻¹) volume := integrable_inv_one_add_sq
      exact h1.comp_mul_left' (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    have hcont : Continuous (𝓕 φ) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (by fun_prop : Continuous fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2) hφ_int
    refine hinv_sq.mono' hcont.aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
    rw [hFφ ξ, norm_div, norm_one, norm_mul, one_div]
    have hge1 : 1 + (2 * Real.pi * ξ) ^ 2 ≤
        ‖(2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I‖ *
        ‖(3 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I‖ := by
      have hsq2 : ‖(2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I‖ ^ 2 = 4 + (2 * Real.pi * ξ) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      have hsq3 : ‖(3 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I‖ ^ 2 = 9 + (2 * Real.pi * ξ) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      have hsq : (1 + (2 * Real.pi * ξ) ^ 2) ^ 2 ≤
          (‖(2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I‖ *
           ‖(3 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I‖) ^ 2 := by
        rw [mul_pow ‖(2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I‖, hsq2, hsq3]
        nlinarith [sq_nonneg (2 * Real.pi * ξ)]
      exact le_of_sq_le_sq hsq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    exact inv_anti₀ (by positivity) hge1
  have hinv := hφ_int.fourierInv_fourier_eq hFφ_int (hφ_cont.continuousAt (x := Real.log y))
  rw [Real.fourierInv_eq'] at hinv
  have hchvar : ∫ ξ : ℝ, Complex.exp (((2 * Real.pi * inner ℝ ξ (Real.log y) : ℝ) : ℂ) * I) • 𝓕 φ ξ =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ v : ℝ, Complex.exp (((v * Real.log y : ℝ) : ℂ) * I) /
        (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I)) := by
    have hrew : (fun ξ : ℝ => Complex.exp (((2 * Real.pi * inner ℝ ξ (Real.log y) : ℝ) : ℂ) * I) • 𝓕 φ ξ) =
        fun ξ : ℝ => (fun v : ℝ => Complex.exp (((v * Real.log y : ℝ) : ℂ) * I) /
          (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I))) ((2 * Real.pi) * ξ) := by
      ext ξ
      rw [hFφ ξ, smul_eq_mul, mul_one_div]
      have hinner : inner ℝ ξ (Real.log y) = ξ * Real.log y := by simp [mul_comm]
      rw [hinner]
      congr 2; ring
    rw [hrew, Measure.integral_comp_mul_left
      (fun v : ℝ => Complex.exp (((v * Real.log y : ℝ) : ℂ) * I) /
        (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I))) (2 * Real.pi)]
    rw [abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi)),
      Complex.real_smul, Complex.ofReal_inv]
  rw [hchvar] at hinv
  have hmul_y2 : ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ v : ℝ, (y : ℂ) ^ ((2 : ℂ) + (v : ℂ) * I) /
        (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I)) =
      (y : ℂ) ^ (2 : ℕ) * φ (Real.log y) := by
    rw [← hinv, ← mul_assoc, mul_comm ((y : ℂ) ^ (2 : ℕ)), mul_assoc]
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    have hcp : (y : ℂ) ^ ((2 : ℂ) + (v : ℂ) * I) =
        (y : ℂ) ^ (2 : ℕ) * Complex.exp (((v * Real.log y : ℝ) : ℂ) * I) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
        ← Complex.ofReal_log hy.le, mul_add, Complex.exp_add]
      congr 1
      · rw [show (Real.log y : ℂ) * (2 : ℂ) = ((2 * Real.log y : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_exp, show 2 * Real.log y = Real.log (y ^ 2) by rw [Real.log_pow]; ring,
          Real.exp_log (pow_pos hy 2), Complex.ofReal_pow]
      · congr 1; push_cast; ring
    dsimp only
    rw [hcp]; ring
  rw [hmul_y2]
  dsimp [φ]
  by_cases hy1 : 1 ≤ y
  · rw [if_pos hy1, if_pos (Real.log_nonneg hy1)]
    have h1 : Real.exp (-2 * Real.log y) = y⁻¹ ^ 2 := by
      rw [show -2 * Real.log y = Real.log (y⁻¹ ^ 2) by
        rw [Real.log_pow, Real.log_inv]; ring, Real.exp_log (by positivity)]
    have h2 : Real.exp (-3 * Real.log y) = y⁻¹ ^ 3 := by
      rw [show -3 * Real.log y = Real.log (y⁻¹ ^ 3) by
        rw [Real.log_pow, Real.log_inv]; ring, Real.exp_log (by positivity)]
    rw [h1, h2]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hy.ne']
  · rw [if_neg hy1, if_neg (not_le.mpr (Real.log_neg hy (not_le.mp hy1))), mul_zero]

/-- On `Re(w) = 2`, `∫ v : ℝ, 1 / ((2 + iv)(3 + iv)) = 0`. -/
lemma integral_inv_line_two :
    ∫ v : ℝ, (1 : ℂ) / (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I)) = 0 := by
  have h := riesz_perron_kernel zero_lt_one
  simp only [Complex.ofReal_one, Complex.one_cpow, le_refl, ↓reduceIte, inv_one, sub_self] at h
  have hne : (((2 * Real.pi : ℝ) : ℂ)⁻¹) ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity))
  exact (mul_eq_zero.mp h).resolve_left hne

/-- On `Re(w) = -a` with `0 < a < 1`, `∫ v : ℝ, 1 / ((-a + iv)(1 - a + iv)) = -2π`. -/
lemma integral_inv_line_neg {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∫ v : ℝ, (1 : ℂ) / (((-(a : ℂ)) + (v : ℂ) * I) * (((1 - a : ℝ) : ℂ) + (v : ℂ) * I)) =
      -((2 * Real.pi : ℝ) : ℂ) := by
  have hb0 : 0 < 1 - a := sub_pos.mpr ha1
  have hdecomp : ∀ v : ℝ,
      (1 : ℂ) / (((-(a : ℂ)) + (v : ℂ) * I) * (((1 - a : ℝ) : ℂ) + (v : ℂ) * I)) =
      (((-(a / (a ^ 2 + v ^ 2)) - (1 - a) / ((1 - a) ^ 2 + v ^ 2) : ℝ) : ℂ)) +
      (((-v / (a ^ 2 + v ^ 2) + v / ((1 - a) ^ 2 + v ^ 2) : ℝ) : ℂ)) * I := by
    intro v
    have h1 : (-(a : ℂ)) + (v : ℂ) * I ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have h2 : ((1 - a : ℝ) : ℂ) + (v : ℂ) * I ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hpf : (1 : ℂ) / (((-(a : ℂ)) + (v : ℂ) * I) * (((1 - a : ℝ) : ℂ) + (v : ℂ) * I)) =
        1 / ((-(a : ℂ)) + (v : ℂ) * I) - 1 / (((1 - a : ℝ) : ℂ) + (v : ℂ) * I) := by
      field_simp [h1, h2]; push_cast; ring
    rw [hpf]
    have ha_sq : (a ^ 2 + v ^ 2 : ℝ) ≠ 0 := by positivity
    have hb_sq : ((1 - a) ^ 2 + v ^ 2 : ℝ) ≠ 0 := by positivity
    have ha_sqC : ((a : ℂ) ^ 2 + (v : ℂ) ^ 2) ≠ 0 := by exact_mod_cast ha_sq
    have hb_sqC : (((1 - (a : ℂ)) ^ 2 + (v : ℂ) ^ 2)) ≠ 0 := by exact_mod_cast hb_sq
    have hf1 : (1 : ℂ) / ((-(a : ℂ)) + (v : ℂ) * I) =
        ((-(a / (a ^ 2 + v ^ 2)) : ℝ) : ℂ) + ((-v / (a ^ 2 + v ^ 2) : ℝ) : ℂ) * I := by
      rw [div_eq_iff h1]
      push_cast
      field_simp [ha_sqC]
      ring_nf
      rw [Complex.I_sq]
      ring
    have hf2 : (1 : ℂ) / (((1 - a : ℝ) : ℂ) + (v : ℂ) * I) =
        (((1 - a) / ((1 - a) ^ 2 + v ^ 2) : ℝ) : ℂ) + ((-v / ((1 - a) ^ 2 + v ^ 2) : ℝ) : ℂ) * I := by
      rw [div_eq_iff h2]
      push_cast
      field_simp [hb_sqC]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hf1, hf2]
    push_cast; ring
  have hint_pos : ∀ c : ℝ, 0 < c →
      Integrable (fun v : ℝ => c / (c ^ 2 + v ^ 2)) volume ∧
      ∫ v : ℝ, c / (c ^ 2 + v ^ 2) = Real.pi := by
    intro c hc
    have hrew : (fun v : ℝ => c / (c ^ 2 + v ^ 2)) = fun v : ℝ => c⁻¹ * (1 + (c⁻¹ * v) ^ 2)⁻¹ := by
      ext v
      have hden : c ^ 2 + v ^ 2 ≠ 0 := by positivity
      have hden2 : 1 + (c⁻¹ * v) ^ 2 ≠ 0 := by positivity
      field_simp [hc.ne', hden, hden2]
    rw [hrew]
    refine ⟨(integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hc.ne')).const_mul _, ?_⟩
    rw [integral_const_mul, Measure.integral_comp_mul_left (fun u : ℝ => (1 + u ^ 2)⁻¹) c⁻¹,
      integral_univ_inv_one_add_sq, inv_inv, abs_of_pos hc, smul_eq_mul,
      inv_mul_cancel_left₀ hc.ne']
  have hint_re1 := (hint_pos a ha0).1
  have hint_re2 := (hint_pos (1 - a) hb0).1
  have hint_re : Integrable (fun v : ℝ =>
      (-(a / (a ^ 2 + v ^ 2)) - (1 - a) / ((1 - a) ^ 2 + v ^ 2) : ℝ)) volume :=
    hint_re1.neg.sub hint_re2
  have hint_im : Integrable (fun v : ℝ =>
      (-v / (a ^ 2 + v ^ 2) + v / ((1 - a) ^ 2 + v ^ 2) : ℝ)) volume := by
    have hcont : Continuous (fun v : ℝ =>
        (-v / (a ^ 2 + v ^ 2) + v / ((1 - a) ^ 2 + v ^ 2) : ℝ)) := by
      refine Continuous.add ?_ ?_
      · exact (continuous_id.neg).div (by fun_prop) (fun v => by positivity)
      · exact continuous_id.div (by fun_prop) (fun v => by positivity)
    set m : ℝ := min a (1 - a)
    have hm : 0 < m := lt_min ha0 hb0
    have hdom : Integrable (fun v : ℝ => (|a ^ 2 - (1 - a) ^ 2| / (2 * m ^ 2)) * (m / (m ^ 2 + v ^ 2))) volume :=
      (hint_pos m hm).1.const_mul _
    refine hdom.mono' hcont.aestronglyMeasurable (ae_of_all _ fun v => ?_)
    have halg : -v / (a ^ 2 + v ^ 2) + v / ((1 - a) ^ 2 + v ^ 2) =
        v * (a ^ 2 - (1 - a) ^ 2) / ((a ^ 2 + v ^ 2) * ((1 - a) ^ 2 + v ^ 2)) := by
      field_simp [(show a ^ 2 + v ^ 2 ≠ 0 by positivity),
        (show (1 - a) ^ 2 + v ^ 2 ≠ 0 by positivity)]
      ring
    rw [halg, Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_pos (mul_pos (by positivity : 0 < a ^ 2 + v ^ 2) (by positivity : 0 < (1 - a) ^ 2 + v ^ 2))]
    have hden1 : m ^ 2 + v ^ 2 ≤ a ^ 2 + v ^ 2 := by
      have : m ≤ a := min_le_left _ _
      nlinarith
    have hden2 : m ^ 2 + v ^ 2 ≤ (1 - a) ^ 2 + v ^ 2 := by
      have : m ≤ 1 - a := min_le_right _ _
      nlinarith
    have hv_le : |v| ≤ (m ^ 2 + v ^ 2) / (2 * m) := by
      rw [le_div_iff₀ (by positivity)]
      have : (m - |v|) ^ 2 ≥ 0 := sq_nonneg _
      nlinarith [sq_abs v]
    have hprod_ge : (m ^ 2 + v ^ 2) ^ 2 ≤ (a ^ 2 + v ^ 2) * ((1 - a) ^ 2 + v ^ 2) := by
      nlinarith [sq_nonneg v]
    have hmv : 0 < m ^ 2 + v ^ 2 := by positivity
    calc |v| * |a ^ 2 - (1 - a) ^ 2| / ((a ^ 2 + v ^ 2) * ((1 - a) ^ 2 + v ^ 2))
        ≤ ((m ^ 2 + v ^ 2) / (2 * m)) * |a ^ 2 - (1 - a) ^ 2| / ((m ^ 2 + v ^ 2) ^ 2) := by
          refine div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hv_le (abs_nonneg _))
            (by positivity) hprod_ge
      _ = |a ^ 2 - (1 - a) ^ 2| / (2 * m ^ 2) * (m / (m ^ 2 + v ^ 2)) := by
          field_simp [hm.ne', hmv.ne']
  have him_zero : ∫ v : ℝ, (-v / (a ^ 2 + v ^ 2) + v / ((1 - a) ^ 2 + v ^ 2) : ℝ) = 0 := by
    have hodd := Measure.integral_comp_mul_left
      (fun v : ℝ => (-v / (a ^ 2 + v ^ 2) + v / ((1 - a) ^ 2 + v ^ 2) : ℝ)) (-1)
    simp only [inv_neg, inv_one, abs_neg, abs_one, one_smul, neg_one_mul] at hodd
    have hneg_fn : (fun v : ℝ => -(-v) / (a ^ 2 + (-v) ^ 2) + (-v) / ((1 - a) ^ 2 + (-v) ^ 2)) =
        fun v : ℝ => -(-v / (a ^ 2 + v ^ 2) + v / ((1 - a) ^ 2 + v ^ 2)) := by
      ext v; ring
    rw [hneg_fn, integral_neg] at hodd
    linarith
  have hre_val : ∫ v : ℝ, (-(a / (a ^ 2 + v ^ 2)) - (1 - a) / ((1 - a) ^ 2 + v ^ 2) : ℝ) =
      -(2 * Real.pi) := by
    have hneg1 : Integrable (fun v : ℝ => -(a / (a ^ 2 + v ^ 2))) volume := hint_re1.neg
    rw [integral_sub hneg1 hint_re2, integral_neg, (hint_pos a ha0).2, (hint_pos (1 - a) hb0).2]
    ring
  simp_rw [hdecomp]
  change ∫ v : ℝ, (Complex.ofRealCLM (-(a / (a ^ 2 + v ^ 2)) - (1 - a) / ((1 - a) ^ 2 + v ^ 2)) +
      Complex.ofRealCLM (-v / (a ^ 2 + v ^ 2) + v / ((1 - a) ^ 2 + v ^ 2)) * I) = _
  rw [integral_add (Complex.ofRealCLM.integrable_comp hint_re)
      ((Complex.ofRealCLM.integrable_comp hint_im).mul_const I),
    integral_mul_const,
    Complex.ofRealCLM.integral_comp_comm hint_re,
    Complex.ofRealCLM.integral_comp_comm hint_im]
  change ((∫ v : ℝ, (-(a / (a ^ 2 + v ^ 2)) - (1 - a) / ((1 - a) ^ 2 + v ^ 2) : ℝ) : ℝ) : ℂ) +
    ((∫ v : ℝ, (-v / (a ^ 2 + v ^ 2) + v / ((1 - a) ^ 2 + v ^ 2) : ℝ) : ℝ) : ℂ) * I = _
  rw [hre_val, him_zero]
  push_cast; ring

/-- Integral representation of `rieszMoebiusSum N s` on `Re(w) = 2` via Fubini (`integral_tsum`). -/
theorem rieszMoebiusSum_eq_integral {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) {N : ℕ} (hN : 1 ≤ N) :
    rieszMoebiusSum N s =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ v : ℝ, (N : ℂ) ^ ((2 : ℂ) + (v : ℂ) * I) /
        (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I)) *
        BN4.invZeta (s + 2 + (v : ℂ) * I) := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN_ne : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN_pos.ne'
  let f : ℕ → ℝ → ℂ := fun n v =>
    ((moebius (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ s) *
    (((N : ℝ) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ ((2 : ℂ) + (v : ℂ) * I) /
      (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I))
  have hf_meas : ∀ n : ℕ, AEStronglyMeasurable (f n) volume := fun n => by
    have hcont : Continuous (f n) := by
      refine Continuous.div ?_ ?_ fun v => ?_
      · refine continuous_const.mul ?_
        have hpos : (0 : ℝ) < (N : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
        refine Continuous.comp (g := fun w : ℂ => (((N : ℝ) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ w) ?_ (by fun_prop)
        rw [continuous_iff_continuousAt]
        intro w
        exact (differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hpos.ne'))).continuousAt
      · fun_prop
      · apply mul_ne_zero
        · intro h; have := congrArg Complex.re h; simp at this
        · intro h; have := congrArg Complex.re h; simp at this
    exact hcont.aestronglyMeasurable
  have hf_bound : ∀ (n : ℕ) (v : ℝ),
      ‖f n v‖ ≤ ((N : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ (s.re + 2)) * (1 + v ^ 2)⁻¹ := by
    intro n v
    have hn_pos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hy_pos : (0 : ℝ) < (N : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
    dsimp [f]
    rw [norm_div, norm_mul, norm_div, norm_mul]
    have hμ : ‖(moebius (n + 1) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n + 1)
    have hns : ‖((n + 1 : ℕ) : ℂ) ^ s‖ = ((n + 1 : ℕ) : ℝ) ^ s.re := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]
    have hy2 : ‖(((N : ℝ) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ ((2 : ℂ) + (v : ℂ) * I)‖ =
        ((N : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ (2 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy_pos]
      simp
    have hden : 1 + v ^ 2 ≤ ‖(2 : ℂ) + (v : ℂ) * I‖ * ‖(3 : ℂ) + (v : ℂ) * I‖ := by
      have h2 : ‖(2 : ℂ) + (v : ℂ) * I‖ ^ 2 = 4 + v ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      have h3 : ‖(3 : ℂ) + (v : ℂ) * I‖ ^ 2 = 9 + v ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      have hsq : (1 + v ^ 2) ^ 2 ≤ (‖(2 : ℂ) + (v : ℂ) * I‖ * ‖(3 : ℂ) + (v : ℂ) * I‖) ^ 2 := by
        rw [mul_pow, h2, h3]; nlinarith [sq_nonneg v]
      exact le_of_sq_le_sq hsq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [hns, hy2, Real.rpow_two, div_pow]
    have hpow_add : ((n + 1 : ℕ) : ℝ) ^ s.re * ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) =
        ((n + 1 : ℕ) : ℝ) ^ (s.re + 2) := by
      rw [← Real.rpow_natCast ((n + 1 : ℕ) : ℝ) 2, ← Real.rpow_add hn_pos]; norm_cast
    calc ‖(moebius (n + 1) : ℂ)‖ / ((n + 1 : ℕ) : ℝ) ^ s.re * ((N : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2) /
          (‖(2 : ℂ) + (v : ℂ) * I‖ * ‖(3 : ℂ) + (v : ℂ) * I‖)
        ≤ 1 / ((n + 1 : ℕ) : ℝ) ^ s.re * ((N : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2) / (1 + v ^ 2) := by
          refine div_le_div₀ (by positivity) ?_ (by positivity) hden
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hμ (by positivity)) (by positivity)
      _ = ((N : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ (s.re + 2)) * (1 + v ^ 2)⁻¹ := by
          rw [← hpow_add]; field_simp
  have hlint_bound : ∀ n : ℕ, ∫⁻ v : ℝ, ‖f n v‖ₑ ≤
      ENNReal.ofReal (((N : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ (s.re + 2)) * Real.pi) := by
    intro n
    have hdom_int : Integrable (fun v : ℝ => ((N : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ (s.re + 2)) * (1 + v ^ 2)⁻¹) volume :=
      integrable_inv_one_add_sq.const_mul _
    have hdom_val : ∫ v : ℝ, ((N : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ (s.re + 2)) * (1 + v ^ 2)⁻¹ =
        ((N : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ (s.re + 2)) * Real.pi := by
      rw [integral_const_mul, integral_univ_inv_one_add_sq]
    rw [← hdom_val, ofReal_integral_eq_lintegral_ofReal hdom_int (ae_of_all _ fun _ => by positivity)]
    refine lintegral_mono fun v => ?_
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hf_bound n v)
  have hsum_lint : ∑' n : ℕ, ∫⁻ v : ℝ, ‖f n v‖ₑ ≠ ⊤ := by
    have hreal_sum : Summable (fun n : ℕ => ((N : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ (s.re + 2)) * Real.pi) := by
      have hp : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (s.re + 2))⁻¹) :=
        (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < s.re + 2)).comp_injective Nat.succ_injective
      refine (hp.mul_left ((N : ℝ) ^ 2)).mul_right Real.pi |>.congr fun n => by ring
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hlint_bound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hreal_sum]
    exact ENNReal.ofReal_ne_top
  have hfub := integral_tsum hf_meas hsum_lint
  have hpointwise : ∀ v : ℝ,
      (∑' n : ℕ, f n v) =
      (N : ℂ) ^ ((2 : ℂ) + (v : ℂ) * I) /
        (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I)) *
        BN4.invZeta (s + 2 + (v : ℂ) * I) := by
    intro v
    set w : ℂ := (2 : ℂ) + (v : ℂ) * I
    have hre_sw : 1 < (s + w).re := by simp [w]; linarith
    have hne1 : s + w ≠ 1 := fun h => by rw [h] at hre_sw; simp at hre_sw
    have hrew : ∀ n : ℕ, f n v =
        ((N : ℂ) ^ w / (w * (w + 1))) *
        ((moebius (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (s + w)) := by
      intro n
      have hn_pos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
      have hn_ne : ((n + 1 : ℕ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn_pos.ne'
      have hdiv_cpow : (((N : ℝ) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ w =
          (N : ℂ) ^ w / ((n + 1 : ℕ) : ℂ) ^ w := by
        have hy_pos : (0 : ℝ) < (N : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy_pos.ne'),
          Complex.cpow_def_of_ne_zero hN_ne,
          Complex.cpow_def_of_ne_zero hn_ne,
          ← Complex.exp_sub, ← sub_mul,
          ← Complex.ofReal_log hy_pos.le,
          ← Complex.ofReal_natCast, ← Complex.ofReal_log hN_pos.le,
          ← Complex.ofReal_natCast, ← Complex.ofReal_log hn_pos.le,
          ← Complex.ofReal_sub, Real.log_div hN_pos.ne' hn_pos.ne']
      have hcp_add : ((n + 1 : ℕ) : ℂ) ^ (s + w) = ((n + 1 : ℕ) : ℂ) ^ s * ((n + 1 : ℕ) : ℂ) ^ w :=
        Complex.cpow_add _ _ hn_ne
      dsimp [f]
      rw [show (2 : ℂ) + (v : ℂ) * I = w by rfl, show (3 : ℂ) + (v : ℂ) * I = w + 1 by dsimp [w]; ring,
        hdiv_cpow, hcp_add]
      ring
    simp_rw [hrew]
    rw [tsum_mul_left, BN1.tsum_moebius_div_cpow_eq_inv_zeta hre_sw,
      ← BN4.invZeta_of_ne_one hne1]
    congr 1 <;> dsimp [w] <;> ring
  have hRHS : ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ v : ℝ, (N : ℂ) ^ ((2 : ℂ) + (v : ℂ) * I) /
        (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I)) *
        BN4.invZeta (s + 2 + (v : ℂ) * I) =
      ∑' n : ℕ, ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, f n v := by
    simp_rw [← hpointwise]
    rw [hfub, ← tsum_mul_left]
  rw [hRHS]
  have hterm_eq : ∀ n : ℕ, ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, f n v =
      if n < N then
        (moebius (n + 1) : ℂ) * (1 - ((((n : ℝ) + 1) / (N : ℝ) : ℝ) : ℂ)) /
          ((n + 1 : ℕ) : ℂ) ^ s
      else 0 := by
    intro n
    have hy_pos : (0 : ℝ) < (N : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
    have hpull : ∫ v : ℝ, f n v =
        ((moebius (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ s) *
        ∫ v : ℝ, (((N : ℝ) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ ((2 : ℂ) + (v : ℂ) * I) /
          (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun v => ?_)
      dsimp [f]; ring
    rw [hpull, ← mul_assoc, mul_comm (((2 * Real.pi : ℝ) : ℂ)⁻¹), mul_assoc,
      riesz_perron_kernel hy_pos]
    have hle_iff : (1 : ℝ) ≤ (N : ℝ) / ((n + 1 : ℕ) : ℝ) ↔ n < N := by
      rw [one_le_div (by positivity : (0 : ℝ) < (n + 1 : ℕ))]
      exact_mod_cast Nat.succ_le_iff
    by_cases hn : n < N
    · rw [if_pos (hle_iff.mpr hn), if_pos hn]
      have hinv : ((((N : ℝ) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ))⁻¹ =
          ((((n : ℝ) + 1) / (N : ℝ) : ℝ) : ℂ) := by
        push_cast; field_simp [hN_ne]
      rw [hinv]; ring
    · rw [if_neg (mt hle_iff.mp hn), if_neg hn, mul_zero]
  simp_rw [hterm_eq]
  rw [tsum_eq_sum (s := Finset.range N) (fun n hn => if_neg (by simpa [Finset.mem_range] using hn)),
    rieszMoebiusSum]
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ =>
    (moebius (n + 1) : ℂ) * (1 - ((((n : ℝ) + 1) / (N : ℝ) : ℝ) : ℂ)) / ((n + 1 : ℕ) : ℂ) ^ s)]
  refine Finset.sum_congr rfl fun n hn => (if_pos (Finset.mem_range.mp hn)).symm

set_option maxHeartbeats 800000 in
/-- Contour shift of `rieszMoebiusSum N s` from `Re(w) = 2` to `Re(w) = -ε/2` under RH,
yielding the quantitative error bound `C_ε * N^(-ε/2) * (2 + |τ|)^(1/16)`. -/
theorem riesz_perron_error_bound (rh : RiemannHypothesis) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8) :
    ∃ C > 0, ∀ (N : ℕ), 1 ≤ N → ∀ τ : ℝ,
      ‖rieszMoebiusSum N ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I) -
        BN4.invZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ ≤
        C * (N : ℝ) ^ (-(ε / 2)) * (2 + |τ|) ^ (1 / 16 : ℝ) := by
  -- Get `invZeta` growth bound on `Re(z) ≥ 1/2 + ε/2` with exponent `1/16`.
  obtain ⟨C₀, hC₀, hinv_bound⟩ := BN4.norm_invZeta_le_rpow rh (δ := ε / 2) (η := 1 / 16)
    (by linarith) (by linarith) (by norm_num)
  set a : ℝ := ε / 2
  have ha0 : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  -- Integrability of `(1 + |v|)^(1/16) / (‖-a + iv‖ * ‖1 - a + iv‖)` over `ℝ`.
  have hker_int : Integrable (fun v : ℝ =>
      (1 + |v|) ^ (1 / 16 : ℝ) /
        (‖(-(a : ℂ)) + (v : ℂ) * I‖ * ‖((1 - a : ℝ) : ℂ) + (v : ℂ) * I‖)) volume := by
    have hcont : Continuous (fun v : ℝ =>
        (1 + |v|) ^ (1 / 16 : ℝ) /
          (‖(-(a : ℂ)) + (v : ℂ) * I‖ * ‖((1 - a : ℝ) : ℂ) + (v : ℂ) * I‖)) := by
      refine Continuous.div ?_ (by fun_prop) fun v => mul_ne_zero ?_ ?_
      · exact (continuous_const.add continuous_abs).rpow_const fun _ => Or.inr (by norm_num)
      · exact norm_ne_zero_iff.mpr fun h => by have := congrArg Complex.re h; simp at this; linarith
      · exact norm_ne_zero_iff.mpr fun h => by have := congrArg Complex.re h; simp at this; linarith
    set m : ℝ := min a (1 - a)
    have hm : 0 < m := lt_min ha0 (sub_pos.mpr ha1)
    have hdom : Integrable (fun v : ℝ =>
        (2 / m ^ 2) * (1 + |v|) ^ (-3 / 2 : ℝ)) volume := by
      have h1 : Integrable (fun v : ℝ => (1 + |v|) ^ (-3 / 2 : ℝ)) volume := by
        -- Reuse the same `(-3/2)` integrability as in BN3.
        have hpos : IntegrableOn (fun v : ℝ => (1 + |v|) ^ (-3 / 2 : ℝ)) (Ioi (0 : ℝ)) := by
          have hshift := integrableOn_Ioi_rpow_of_lt (a := (-3 / 2 : ℝ)) (by norm_num) (by norm_num : (0 : ℝ) < 1)
          rw [← integrable_indicator_iff measurableSet_Ioi] at hshift ⊢
          refine (hshift.comp_add_right 1).congr (ae_of_all _ fun v => ?_)
          dsimp only
          by_cases hv : (0 : ℝ) < v
          · rw [Set.indicator_of_mem (show v + 1 ∈ Ioi (1 : ℝ) by simp; linarith),
              Set.indicator_of_mem (show v ∈ Ioi (0 : ℝ) from hv), abs_of_pos hv, add_comm]
          · rw [Set.indicator_of_notMem (show v + 1 ∉ Ioi (1 : ℝ) by simp; linarith),
              Set.indicator_of_notMem (show v ∉ Ioi (0 : ℝ) from hv)]
        have hneg : IntegrableOn (fun v : ℝ => (1 + |v|) ^ (-3 / 2 : ℝ)) (Iio (0 : ℝ)) := by
          rw [← integrable_indicator_iff measurableSet_Ioi] at hpos
          rw [← integrable_indicator_iff measurableSet_Iio]
          refine hpos.comp_neg.congr (ae_of_all _ fun v => ?_)
          dsimp only
          by_cases hv : v < 0
          · rw [Set.indicator_of_mem (show -v ∈ Ioi (0 : ℝ) by simp [hv]),
              Set.indicator_of_mem (show v ∈ Iio (0 : ℝ) from hv), abs_neg]
          · rw [Set.indicator_of_notMem (show -v ∉ Ioi (0 : ℝ) by simp; linarith),
              Set.indicator_of_notMem (show v ∉ Iio (0 : ℝ) from hv)]
        rw [← integrableOn_univ]
        refine (hpos.union hneg).congr_set_ae ?_
        rw [ae_eq_set]
        have h1 : (Ioi (0 : ℝ) ∪ Iio (0 : ℝ)) \ univ = ∅ := by simp
        have h2 : univ \ (Ioi (0 : ℝ) ∪ Iio (0 : ℝ)) = {0} := by ext x; simp
        rw [h1, h2]; simp
      exact h1.const_mul _
    refine hdom.mono' hcont.aestronglyMeasurable (ae_of_all _ fun v => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have hden1 : m ^ 2 + v ^ 2 ≤ ‖(-(a : ℂ)) + (v : ℂ) * I‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp
      have : m ≤ a := min_le_left _ _
      nlinarith
    have hden2 : m ^ 2 + v ^ 2 ≤ ‖((1 - a : ℝ) : ℂ) + (v : ℂ) * I‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp
      have : m ≤ 1 - a := min_le_right _ _
      nlinarith
    have hprod_ge : m ^ 2 + v ^ 2 ≤
        ‖(-(a : ℂ)) + (v : ℂ) * I‖ * ‖((1 - a : ℝ) : ℂ) + (v : ℂ) * I‖ := by
      have hsq : (m ^ 2 + v ^ 2) ^ 2 ≤
          (‖(-(a : ℂ)) + (v : ℂ) * I‖ * ‖((1 - a : ℝ) : ℂ) + (v : ℂ) * I‖) ^ 2 := by
        rw [mul_pow]; nlinarith
      exact le_of_sq_le_sq hsq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hm1 : m ≤ 1 := le_trans (min_le_left _ _) ha1.le
    have hden_ge2 : (m ^ 2 / 2) * (1 + |v|) ^ 2 ≤ m ^ 2 + v ^ 2 := by
      have : (1 + |v|) ^ 2 ≤ 2 + 2 * v ^ 2 := by
        have : (1 - |v|) ^ 2 ≥ 0 := sq_nonneg _
        nlinarith [sq_abs v]
      have : m ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg v]
    have hpow : (1 + |v|) ^ (1 / 16 : ℝ) / (1 + |v|) ^ 2 ≤ (1 + |v|) ^ (-3 / 2 : ℝ) := by
      rw [show (1 + |v|) ^ 2 = (1 + |v|) ^ (2 : ℝ) by norm_cast,
        ← Real.rpow_sub (by positivity : 0 < 1 + |v|)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v]) (by norm_num)
    calc (1 + |v|) ^ (1 / 16 : ℝ) /
          (‖(-(a : ℂ)) + (v : ℂ) * I‖ * ‖((1 - a : ℝ) : ℂ) + (v : ℂ) * I‖)
        ≤ (1 + |v|) ^ (1 / 16 : ℝ) / ((m ^ 2 / 2) * (1 + |v|) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (hden_ge2.trans hprod_ge)
      _ = (2 / m ^ 2) * ((1 + |v|) ^ (1 / 16 : ℝ) / (1 + |v|) ^ 2) := by field_simp
      _ ≤ (2 / m ^ 2) * (1 + |v|) ^ (-3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  set I_ker : ℝ := ∫ v : ℝ, (1 + |v|) ^ (1 / 16 : ℝ) /
      (‖(-(a : ℂ)) + (v : ℂ) * I‖ * ‖((1 - a : ℝ) : ℂ) + (v : ℂ) * I‖)
  have hI_ker_nn : 0 ≤ I_ker := integral_nonneg fun _ => by positivity
  set C : ℝ := (2 * Real.pi)⁻¹ * C₀ * (I_ker + 1)
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, fun N hN τ => ?_⟩
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN_ne : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN_pos.ne'
  set s : ℂ := (1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I
  have hs_re : (1 / 2 : ℝ) < s.re := by simp [s]; linarith
  -- Define `g(w) = N^w * invZeta (s + w)` and removable-singularity `H(w) = (g(w) - g(0)) / (w (w + 1))`.
  let g : ℂ → ℂ := fun w => (N : ℂ) ^ w * BN4.invZeta (s + w)
  have hg_diff : DifferentiableOn ℂ g {w : ℂ | -(a + a / 2) < w.re} := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun u : ℂ => (N : ℂ) ^ u) w :=
      differentiableAt_id.const_cpow (Or.inl hN_ne)
    have hre_sw : (1 / 2 : ℝ) < (s + w).re := by
      simp only [s, Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
        sub_zero, add_zero]
      dsimp [a] at hw
      linarith
    have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have h2 : DifferentiableAt ℂ BN4.invZeta (s + w) :=
      (BN4.differentiableOn_invZeta rh).differentiableAt (hopen.mem_nhds hre_sw)
    exact (h1.mul (h2.comp w (differentiableAt_id.const_add s))).differentiableWithinAt
  have hg0 : g 0 = BN4.invZeta s := by simp [g]
  have hg_diff0 : DifferentiableAt ℂ g 0 :=
    hg_diff.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simp; linarith))
  let H : ℂ → ℂ := fun w =>
    if w = 0 then deriv g 0 else (g w - g 0) / (w * (w + 1))
  have hH_cont0 : ContinuousAt H 0 := by
    rw [ContinuousAt, show H 0 = deriv g 0 by simp [H]]
    have hd := hg_diff0.hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope] at hd
    have h1 : Tendsto (fun w : ℂ => (g w - g 0) / w) (𝓝[≠] 0) (𝓝 (deriv g 0)) := by
      refine hd.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w (hw : w ≠ 0)
      simp [slope, vsub_eq_sub, smul_eq_mul, div_eq_inv_mul]
    have h2 : Tendsto (fun w : ℂ => w + 1) (𝓝[≠] 0) (𝓝 1) := by
      have hc : Continuous (fun w : ℂ => w + 1) := by fun_prop
      simpa using (hc.continuousAt (x := (0 : ℂ))).tendsto.mono_left nhdsWithin_le_nhds
    have hq : Tendsto (fun w : ℂ => (g w - g 0) / (w * (w + 1))) (𝓝[≠] 0) (𝓝 (deriv g 0)) := by
      have hdiv := h1.div h2 one_ne_zero
      rw [div_one] at hdiv
      refine hdiv.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w _
      dsimp only [Pi.div_apply]
      rw [div_div]
    rw [Metric.tendsto_nhds] at hq ⊢
    intro r hr
    have hev := hq r hr
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev] with w hw
    by_cases h0 : w = 0
    · subst h0; simpa [H] using hr
    · simpa [H, h0] using hw h0
  have hH_diff : DifferentiableOn ℂ H {w : ℂ | -(a + a / 2) < w.re} := by
    have hopen : IsOpen {w : ℂ | -(a + a / 2) < w.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    intro w hw
    rcases eq_or_ne w 0 with rfl | h0
    · have hpunct : ∀ᶠ u in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ H u := by
        filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hw), self_mem_nhdsWithin] with u hu (hu0 : u ≠ 0)
        have hgu : DifferentiableAt ℂ g u := hg_diff.differentiableAt (hopen.mem_nhds hu)
        have hu1 : u + 1 ≠ 0 := fun h => by
          have := congrArg Complex.re h; simp at this; dsimp [a] at hu; linarith
        have hq : DifferentiableAt ℂ (fun v => (g v - g 0) / (v * (v + 1))) u :=
          (hgu.sub (differentiableAt_const (g 0))).div
            (differentiableAt_id.mul (differentiableAt_id.add (differentiableAt_const 1)))
            (mul_ne_zero hu0 hu1)
        refine hq.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_ne.mem_nhds hu0] with v hv
        exact if_neg hv
      exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hpunct
        hH_cont0).differentiableAt.differentiableWithinAt
    · have hgw : DifferentiableAt ℂ g w := hg_diff.differentiableAt (hopen.mem_nhds hw)
      have hw1 : w + 1 ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; dsimp [a] at hw; linarith
      have hq : DifferentiableAt ℂ (fun v => (g v - g 0) / (v * (v + 1))) w :=
        (hgw.sub (differentiableAt_const (g 0))).div
          (differentiableAt_id.mul (differentiableAt_id.add (differentiableAt_const 1)))
          (mul_ne_zero h0 hw1)
      have heq : H =ᶠ[𝓝 w] fun v => (g v - g 0) / (v * (v + 1)) := by
        filter_upwards [isOpen_ne.mem_nhds h0] with v hv
        exact if_neg hv
      exact (hq.congr_of_eventuallyEq heq).differentiableWithinAt
  -- Bound `g w` uniformly on the strip `-a ≤ w.re ≤ 2`.
  have hg_strip : ∀ w : ℂ, -a ≤ w.re → w.re ≤ 2 →
      ‖g w‖ ≤ (N : ℝ) ^ w.re * (C₀ * (2 + |τ + w.im|) ^ (1 / 16 : ℝ)) := by
    intro w hw1 hw2
    dsimp [g]
    rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN_pos]
    have hre_sw : 1 / 2 + a ≤ (s + w).re := by
      simp only [s, Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
        sub_zero, add_zero]
      dsimp [a] at hw1 ⊢; linarith
    have him_sw : (s + w).im = τ + w.im := by simp [s]
    have hinv := hinv_bound (s + w) hre_sw
    rw [him_sw] at hinv
    exact mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hN_pos.le _)
  -- Submultiplicativity `(2 + |τ + v|)^(1/16) ≤ (2 + |τ|)^(1/16) * (1 + |v|)^(1/16)`.
  have hsubmul : ∀ v : ℝ,
      (2 + |τ + v|) ^ (1 / 16 : ℝ) ≤ (2 + |τ|) ^ (1 / 16 : ℝ) * (1 + |v|) ^ (1 / 16 : ℝ) := by
    intro v
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    have htri : |τ + v| ≤ |τ| + |v| := abs_add_le τ v
    nlinarith [abs_nonneg τ, abs_nonneg v]
  -- Integrability of `v ↦ g(-a + iv) / ((-a + iv)(1 - a + iv))` and `v ↦ H(-a + iv)` and `v ↦ H(2 + iv)`.
  have hleft_int : Integrable (fun v : ℝ =>
      g ((-(a : ℂ)) + (v : ℂ) * I) /
        (((-(a : ℂ)) + (v : ℂ) * I) * (((1 - a : ℝ) : ℂ) + (v : ℂ) * I))) volume := by
    have hcont : Continuous (fun v : ℝ =>
        g ((-(a : ℂ)) + (v : ℂ) * I) /
          (((-(a : ℂ)) + (v : ℂ) * I) * (((1 - a : ℝ) : ℂ) + (v : ℂ) * I))) := by
      refine Continuous.div ?_ (by fun_prop) fun v => mul_ne_zero ?_ ?_
      · exact hg_diff.continuousOn.comp_continuous (by fun_prop) fun v => by simp; linarith
      · intro h; have := congrArg Complex.re h; simp at this; linarith
      · intro h; have := congrArg Complex.re h; simp at this; linarith
    refine (hker_int.const_mul ((N : ℝ) ^ (-a) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ))).mono'
      hcont.aestronglyMeasurable (ae_of_all _ fun v => ?_)
    rw [norm_div, norm_mul ((-(a : ℂ)) + (v : ℂ) * I)]
    have hgb := hg_strip ((-(a : ℂ)) + (v : ℂ) * I) (by simp) (by simp; linarith)
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
      Complex.neg_im, neg_zero, Complex.mul_im, zero_add] at hgb
    have hsm := hsubmul v
    have hnum : ‖g ((-(a : ℂ)) + (v : ℂ) * I)‖ ≤
        ((N : ℝ) ^ (-a) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ)) * (1 + |v|) ^ (1 / 16 : ℝ) := by
      calc ‖g ((-(a : ℂ)) + (v : ℂ) * I)‖
          ≤ (N : ℝ) ^ (-a) * (C₀ * (2 + |τ + v|) ^ (1 / 16 : ℝ)) := hgb
        _ ≤ (N : ℝ) ^ (-a) * (C₀ * ((2 + |τ|) ^ (1 / 16 : ℝ) * (1 + |v|) ^ (1 / 16 : ℝ))) := by
            gcongr
        _ = ((N : ℝ) ^ (-a) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ)) * (1 + |v|) ^ (1 / 16 : ℝ) := by ring
    calc ‖g ((-(a : ℂ)) + (v : ℂ) * I)‖ /
          (‖(-(a : ℂ)) + (v : ℂ) * I‖ * ‖((1 - a : ℝ) : ℂ) + (v : ℂ) * I‖)
        ≤ (((N : ℝ) ^ (-a) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ)) * (1 + |v|) ^ (1 / 16 : ℝ)) /
          (‖(-(a : ℂ)) + (v : ℂ) * I‖ * ‖((1 - a : ℝ) : ℂ) + (v : ℂ) * I‖) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = ((N : ℝ) ^ (-a) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ)) *
          ((1 + |v|) ^ (1 / 16 : ℝ) /
            (‖(-(a : ℂ)) + (v : ℂ) * I‖ * ‖((1 - a : ℝ) : ℂ) + (v : ℂ) * I‖)) := by ring
  have hinv_left_int : Integrable (fun v : ℝ =>
      (1 : ℂ) / (((-(a : ℂ)) + (v : ℂ) * I) * (((1 - a : ℝ) : ℂ) + (v : ℂ) * I))) volume := by
    have hcont : Continuous (fun v : ℝ =>
        (1 : ℂ) / (((-(a : ℂ)) + (v : ℂ) * I) * (((1 - a : ℝ) : ℂ) + (v : ℂ) * I))) :=
      continuous_const.div (by fun_prop) fun v => mul_ne_zero
        (fun h => by have := congrArg Complex.re h; simp at this; linarith)
        (fun h => by have := congrArg Complex.re h; simp at this; linarith)
    refine hker_int.mono' hcont.aestronglyMeasurable (ae_of_all _ fun v => ?_)
    rw [norm_div, norm_one, norm_mul]
    have h1 : (1 : ℝ) ≤ (1 + |v|) ^ (1 / 16 : ℝ) :=
      Real.one_le_rpow (by linarith [abs_nonneg v]) (by norm_num)
    exact div_le_div_of_nonneg_right h1 (by positivity)
  have hright_int : Integrable (fun v : ℝ =>
      g ((2 : ℂ) + (v : ℂ) * I) / (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I))) volume := by
    have hcont : Continuous (fun v : ℝ =>
        g ((2 : ℂ) + (v : ℂ) * I) / (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I))) := by
      refine Continuous.div ?_ (by fun_prop) fun v => mul_ne_zero ?_ ?_
      · exact hg_diff.continuousOn.comp_continuous (by fun_prop) fun v => by simp; linarith
      · intro h; have := congrArg Complex.re h; simp at this
      · intro h; have := congrArg Complex.re h; simp at this
    refine (integrable_inv_one_add_sq.const_mul ((N : ℝ) ^ (2 : ℝ) * 4)).mono'
      hcont.aestronglyMeasurable (ae_of_all _ fun v => ?_)
    rw [norm_div, norm_mul ((2 : ℂ) + (v : ℂ) * I)]
    have hre2 : (2 : ℝ) ≤ (s + ((2 : ℂ) + (v : ℂ) * I)).re := by simp [s]; linarith
    have hne1 : s + ((2 : ℂ) + (v : ℂ) * I) ≠ 1 := fun h => by rw [h] at hre2; simp at hre2
    have hg_le : ‖g ((2 : ℂ) + (v : ℂ) * I)‖ ≤ (N : ℝ) ^ (2 : ℝ) * 4 := by
      dsimp [g]
      rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN_pos,
        BN4.invZeta_of_ne_one hne1, norm_inv]
      simp only [Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      have hge := BN4.norm_zeta_ge_quarter_of_two_le_re hre2
      have h4 : ‖riemannZeta (s + (2 + (v : ℂ) * I))‖⁻¹ ≤ 4 := by
        rw [inv_le_iff_one_le_mul₀ (by linarith)]; linarith
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    have hden : 1 + v ^ 2 ≤ ‖(2 : ℂ) + (v : ℂ) * I‖ * ‖(3 : ℂ) + (v : ℂ) * I‖ := by
      have h2 : ‖(2 : ℂ) + (v : ℂ) * I‖ ^ 2 = 4 + v ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      have h3 : ‖(3 : ℂ) + (v : ℂ) * I‖ ^ 2 = 9 + v ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      have hsq : (1 + v ^ 2) ^ 2 ≤ (‖(2 : ℂ) + (v : ℂ) * I‖ * ‖(3 : ℂ) + (v : ℂ) * I‖) ^ 2 := by
        rw [mul_pow, h2, h3]; nlinarith [sq_nonneg v]
      exact le_of_sq_le_sq hsq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [div_eq_mul_inv]
    exact mul_le_mul hg_le (inv_anti₀ (by positivity) hden) (by positivity) (by positivity)
  have hinv_right_int : Integrable (fun v : ℝ =>
      (1 : ℂ) / (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I))) volume := by
    have hcont : Continuous (fun v : ℝ =>
        (1 : ℂ) / (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I))) :=
      continuous_const.div (by fun_prop) fun v => mul_ne_zero
        (fun h => by have := congrArg Complex.re h; simp at this)
        (fun h => by have := congrArg Complex.re h; simp at this)
    refine integrable_inv_one_add_sq.mono' hcont.aestronglyMeasurable (ae_of_all _ fun v => ?_)
    rw [norm_div, norm_one, norm_mul, one_div]
    have hden : 1 + v ^ 2 ≤ ‖(2 : ℂ) + (v : ℂ) * I‖ * ‖(3 : ℂ) + (v : ℂ) * I‖ := by
      have h2 : ‖(2 : ℂ) + (v : ℂ) * I‖ ^ 2 = 4 + v ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      have h3 : ‖(3 : ℂ) + (v : ℂ) * I‖ ^ 2 = 9 + v ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      have hsq : (1 + v ^ 2) ^ 2 ≤ (‖(2 : ℂ) + (v : ℂ) * I‖ * ‖(3 : ℂ) + (v : ℂ) * I‖) ^ 2 := by
        rw [mul_pow, h2, h3]; nlinarith [sq_nonneg v]
      exact le_of_sq_le_sq hsq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    exact inv_anti₀ (by positivity) hden
  -- Express `H` on both vertical lines.
  have hH_right_eq : ∀ v : ℝ, H ((2 : ℂ) + (v : ℂ) * I) =
      g ((2 : ℂ) + (v : ℂ) * I) / (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I)) -
      g 0 * ((1 : ℂ) / (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I))) := by
    intro v
    have hne0 : (2 : ℂ) + (v : ℂ) * I ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this
    dsimp [H]
    rw [if_neg hne0, show (2 : ℂ) + (v : ℂ) * I + 1 = (3 : ℂ) + (v : ℂ) * I by ring]
    ring
  have hH_left_eq : ∀ v : ℝ, H ((-(a : ℂ)) + (v : ℂ) * I) =
      g ((-(a : ℂ)) + (v : ℂ) * I) /
        (((-(a : ℂ)) + (v : ℂ) * I) * (((1 - a : ℝ) : ℂ) + (v : ℂ) * I)) -
      g 0 * ((1 : ℂ) / (((-(a : ℂ)) + (v : ℂ) * I) * (((1 - a : ℝ) : ℂ) + (v : ℂ) * I))) := by
    intro v
    have hne0 : (-(a : ℂ)) + (v : ℂ) * I ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    dsimp [H]
    rw [if_neg hne0, show (-(a : ℂ)) + (v : ℂ) * I + 1 = ((1 - a : ℝ) : ℂ) + (v : ℂ) * I by push_cast; ring]
    ring
  have hH_right_int : Integrable (fun v : ℝ => H ((2 : ℂ) + (v : ℂ) * I)) volume := by
    simp_rw [hH_right_eq]
    exact hright_int.sub (hinv_right_int.const_mul (g 0))
  have hH_left_int : Integrable (fun v : ℝ => H ((-(a : ℂ)) + (v : ℂ) * I)) volume := by
    simp_rw [hH_left_eq]
    exact hleft_int.sub (hinv_left_int.const_mul (g 0))
  -- Cauchy's rectangle theorem on `[-a, 2] × [-T, T]` as `T → ∞` gives `∫ H(2 + iv) = ∫ H(-a + iv)`.
  have hrect_eq : ∫ v : ℝ, H ((2 : ℂ) + (v : ℂ) * I) = ∫ v : ℝ, H ((-(a : ℂ)) + (v : ℂ) * I) := by
    have hrect_T : ∀ T : ℝ, 0 < T →
        ((∫ x in (-a)..2, H ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) -
         (∫ x in (-a)..2, H ((x : ℂ) + (T : ℂ) * I))) +
        I * (∫ v in (-T)..T, H ((2 : ℂ) + (v : ℂ) * I)) -
        I * (∫ v in (-T)..T, H ((-(a : ℂ)) + (v : ℂ) * I)) = 0 := by
      intro T _
      have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn H
        ((-(a : ℂ)) + ((-T : ℝ) : ℂ) * I) ((2 : ℂ) + (T : ℂ) * I) (by
          refine hH_diff.mono ?_
          rintro w ⟨hw1, _⟩
          have hle : -a ≤ (2 : ℝ) := by linarith
          simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero,
            Complex.re_ofNat] at hw1
          rw [Set.uIcc_of_le hle] at hw1
          change -(a + a / 2) < w.re
          linarith [hw1.1])
      simpa [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.neg_im, Complex.mul_im,
        Complex.re_ofNat, Complex.im_ofNat, smul_eq_mul] using h
    -- Show the horizontal integrals vanish as `T → ∞`.
    have hhoriz : ∀ (sgn : ℝ), |sgn| = 1 →
        Tendsto (fun T : ℝ => ∫ x in (-a)..2, H ((x : ℂ) + ((sgn * T : ℝ) : ℂ) * I))
          atTop (𝓝 0) := by
      intro sgn hsgn
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hbound_T : ∀ᶠ T : ℝ in atTop,
          ‖∫ x in (-a)..2, H ((x : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖ ≤
            (2 + a) * (((N : ℝ) ^ (2 : ℝ) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ) * (1 + T) ^ (1 / 16 : ℝ) + ‖g 0‖) /
              T ^ 2) := by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
        have hT_pos : 0 < T := by linarith
        have hle_const : ∀ x ∈ Set.uIoc (-a) 2,
            ‖H ((x : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖ ≤
              ((N : ℝ) ^ (2 : ℝ) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ) * (1 + T) ^ (1 / 16 : ℝ) + ‖g 0‖) /
                T ^ 2 := by
          intro x hx
          rw [Set.uIoc_of_le (by linarith : -a ≤ 2)] at hx
          set w : ℂ := (x : ℂ) + ((sgn * T : ℝ) : ℂ) * I
          have hw_im : w.im = sgn * T := by simp [w]
          have hw_abs_im : |w.im| = T := by rw [hw_im, abs_mul, hsgn, one_mul, abs_of_pos hT_pos]
          have hw_ne0 : w ≠ 0 := fun h => by rw [h, Complex.zero_im, abs_zero] at hw_abs_im; linarith
          dsimp [H]
          rw [if_neg hw_ne0, norm_div, norm_mul]
          have hden1 : T ≤ ‖w‖ := by rw [← hw_abs_im]; exact Complex.abs_im_le_norm w
          have hden2 : T ≤ ‖w + 1‖ := by
            have : (w + 1).im = w.im := by simp
            rw [← hw_abs_im, ← this]; exact Complex.abs_im_le_norm (w + 1)
          have hprod : T ^ 2 ≤ ‖w‖ * ‖w + 1‖ := by nlinarith
          have hgb := hg_strip w (by simp [w]; linarith [hx.1]) (by simp [w]; exact hx.2)
          have hN_le : (N : ℝ) ^ w.re ≤ (N : ℝ) ^ (2 : ℝ) := by
            have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
            exact Real.rpow_le_rpow_of_exponent_le hN1 (by simp [w]; exact hx.2)
          have hsm := hsubmul w.im
          rw [hw_abs_im] at hsm
          have hgw_le : ‖g w‖ ≤ (N : ℝ) ^ (2 : ℝ) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ) * (1 + T) ^ (1 / 16 : ℝ) := by
            calc ‖g w‖ ≤ (N : ℝ) ^ w.re * (C₀ * (2 + |τ + w.im|) ^ (1 / 16 : ℝ)) := hgb
              _ ≤ (N : ℝ) ^ (2 : ℝ) * (C₀ * ((2 + |τ|) ^ (1 / 16 : ℝ) * (1 + T) ^ (1 / 16 : ℝ))) := by
                  gcongr
              _ = (N : ℝ) ^ (2 : ℝ) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ) * (1 + T) ^ (1 / 16 : ℝ) := by ring
          have hnum : ‖g w - g 0‖ ≤
              (N : ℝ) ^ (2 : ℝ) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ) * (1 + T) ^ (1 / 16 : ℝ) + ‖g 0‖ :=
            (norm_sub_le _ _).trans (add_le_add hgw_le le_rfl)
          exact div_le_div₀ (by positivity) hnum (by positivity) hprod
        have hint_le := intervalIntegral.norm_integral_le_of_norm_le_const hle_const
        have hlen : |2 - (-a)| = 2 + a := by rw [sub_neg_eq_add, abs_of_pos (by linarith)]
        rw [hlen, mul_comm _ (2 + a)] at hint_le
        exact hint_le
      have hlim_zero : Tendsto (fun T : ℝ =>
          (2 + a) * (((N : ℝ) ^ (2 : ℝ) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ) * (1 + T) ^ (1 / 16 : ℝ) + ‖g 0‖) /
            T ^ 2)) atTop (𝓝 0) := by
        have hterm1 : Tendsto (fun T : ℝ => (1 + T) ^ (1 / 16 : ℝ) / T ^ 2) atTop (𝓝 0) := by
          refine squeeze_zero' (by
            filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
            exact div_nonneg (by positivity) (sq_nonneg T)) ?_
            (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1) |>.const_mul (2 : ℝ) |> fun h => by simpa using h)
          filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
          have h1T : (1 + T) ^ (1 / 16 : ℝ) ≤ (2 * T) ^ (1 / 16 : ℝ) :=
            Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
          have h2T : (2 * T) ^ (1 / 16 : ℝ) ≤ 2 * T := by
            have h1 : (2 * T) ^ (1 / 16 : ℝ) ≤ (2 * T) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
            simpa using h1
          have hTpos : 0 < T := by linarith
          calc (1 + T) ^ (1 / 16 : ℝ) / T ^ 2
              ≤ (2 * T) / T ^ 2 := div_le_div_of_nonneg_right (h1T.trans h2T) (by positivity)
            _ = 2 * T ^ (-1 : ℝ) := by
                rw [Real.rpow_neg hTpos.le, Real.rpow_one]; field_simp [hTpos.ne']
        have hterm2 : Tendsto (fun T : ℝ => ‖g 0‖ / T ^ 2) atTop (𝓝 0) := by
          have hinv2 : Tendsto (fun T : ℝ => T ^ (-2 : ℝ)) atTop (𝓝 0) :=
            tendsto_rpow_neg_atTop (by norm_num)
          have := hinv2.const_mul ‖g 0‖
          rw [mul_zero] at this
          refine this.congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
          rw [Real.rpow_neg hT.le, Real.rpow_two, div_eq_mul_inv]
        have hsum := ((hterm1.const_mul ((N : ℝ) ^ (2 : ℝ) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ))).add hterm2).const_mul (2 + a)
        simp only [mul_zero, add_zero] at hsum
        refine hsum.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with T _
        ring
      exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound_T hlim_zero
    have hbot := hhoriz (-1) (by norm_num)
    have htop := hhoriz 1 (by norm_num)
    have hv_right : Tendsto (fun T : ℝ => ∫ v in (-T)..T, H ((2 : ℂ) + (v : ℂ) * I))
        atTop (𝓝 (∫ v : ℝ, H ((2 : ℂ) + (v : ℂ) * I))) :=
      intervalIntegral_tendsto_integral hH_right_int tendsto_neg_atTop_atBot tendsto_id
    have hv_left : Tendsto (fun T : ℝ => ∫ v in (-T)..T, H ((-(a : ℂ)) + (v : ℂ) * I))
        atTop (𝓝 (∫ v : ℝ, H ((-(a : ℂ)) + (v : ℂ) * I))) :=
      intervalIntegral_tendsto_integral hH_left_int tendsto_neg_atTop_atBot tendsto_id
    have hcomb : Tendsto (fun T : ℝ =>
        ((∫ x in (-a)..2, H ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) -
         (∫ x in (-a)..2, H ((x : ℂ) + (T : ℂ) * I))) +
        I * (∫ v in (-T)..T, H ((2 : ℂ) + (v : ℂ) * I)) -
        I * (∫ v in (-T)..T, H ((-(a : ℂ)) + (v : ℂ) * I)))
        atTop (𝓝 (I * (∫ v : ℝ, H ((2 : ℂ) + (v : ℂ) * I)) -
          I * (∫ v : ℝ, H ((-(a : ℂ)) + (v : ℂ) * I)))) := by
      have hbot' : Tendsto (fun T : ℝ => ∫ x in (-a)..2, H ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
          atTop (𝓝 0) := by simpa using hbot
      have htop' : Tendsto (fun T : ℝ => ∫ x in (-a)..2, H ((x : ℂ) + (T : ℂ) * I))
          atTop (𝓝 0) := by simpa using htop
      have := ((hbot'.sub htop').add (hv_right.const_mul I)).sub (hv_left.const_mul I)
      simpa using this
    have hzero : I * (∫ v : ℝ, H ((2 : ℂ) + (v : ℂ) * I)) -
        I * (∫ v : ℝ, H ((-(a : ℂ)) + (v : ℂ) * I)) = 0 :=
      tendsto_nhds_unique hcomb (tendsto_const_nhds.congr' (by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
        exact (hrect_T T hT).symm))
    have hIeq : I * (∫ v : ℝ, H ((2 : ℂ) + (v : ℂ) * I)) =
        I * (∫ v : ℝ, H ((-(a : ℂ)) + (v : ℂ) * I)) := sub_eq_zero.mp hzero
    exact mul_left_cancel₀ Complex.I_ne_zero hIeq
  -- Expand both sides of `hrect_eq` using `integral_inv_line_two` and `integral_inv_line_neg`.
  have hRHS_expand : ∫ v : ℝ, H ((2 : ℂ) + (v : ℂ) * I) =
      ∫ v : ℝ, g ((2 : ℂ) + (v : ℂ) * I) / (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I)) := by
    simp_rw [hH_right_eq]
    rw [integral_sub hright_int (hinv_right_int.const_mul (g 0)), integral_const_mul,
      integral_inv_line_two, mul_zero, sub_zero]
  have hLHS_expand : ∫ v : ℝ, H ((-(a : ℂ)) + (v : ℂ) * I) =
      (∫ v : ℝ, g ((-(a : ℂ)) + (v : ℂ) * I) /
        (((-(a : ℂ)) + (v : ℂ) * I) * (((1 - a : ℝ) : ℂ) + (v : ℂ) * I))) +
      ((2 * Real.pi : ℝ) : ℂ) * BN4.invZeta s := by
    simp_rw [hH_left_eq]
    rw [integral_sub hleft_int (hinv_left_int.const_mul (g 0)), integral_const_mul,
      integral_inv_line_neg ha0 ha1, hg0]
    ring
  have hdiff_eq : rieszMoebiusSum N s - BN4.invZeta s =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ v : ℝ, g ((-(a : ℂ)) + (v : ℂ) * I) /
        (((-(a : ℂ)) + (v : ℂ) * I) * (((1 - a : ℝ) : ℂ) + (v : ℂ) * I)) := by
    rw [rieszMoebiusSum_eq_integral hs_re hN]
    have hD_eq : ∫ v : ℝ, (N : ℂ) ^ ((2 : ℂ) + (v : ℂ) * I) /
        (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I)) *
        BN4.invZeta (s + 2 + (v : ℂ) * I) =
        ∫ v : ℝ, g ((2 : ℂ) + (v : ℂ) * I) / (((2 : ℂ) + (v : ℂ) * I) * ((3 : ℂ) + (v : ℂ) * I)) := by
      refine integral_congr_ae (ae_of_all _ fun v => ?_)
      dsimp [g]; rw [add_assoc]; ring
    rw [hD_eq, ← hRHS_expand, hrect_eq, hLHS_expand, mul_add]
    have hpi_ne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    rw [← mul_assoc, inv_mul_cancel₀ hpi_ne, one_mul, add_sub_cancel_right]
  -- Bound the shifted integral directly!
  rw [hdiff_eq, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hint_le : ‖∫ v : ℝ, g ((-(a : ℂ)) + (v : ℂ) * I) /
      (((-(a : ℂ)) + (v : ℂ) * I) * (((1 - a : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
      ((N : ℝ) ^ (-a) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ)) * I_ker := by
    calc ‖∫ v : ℝ, g ((-(a : ℂ)) + (v : ℂ) * I) /
          (((-(a : ℂ)) + (v : ℂ) * I) * (((1 - a : ℝ) : ℂ) + (v : ℂ) * I))‖
        ≤ ∫ v : ℝ, ‖g ((-(a : ℂ)) + (v : ℂ) * I) /
          (((-(a : ℂ)) + (v : ℂ) * I) * (((1 - a : ℝ) : ℂ) + (v : ℂ) * I))‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, ((N : ℝ) ^ (-a) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ)) *
          ((1 + |v|) ^ (1 / 16 : ℝ) /
            (‖(-(a : ℂ)) + (v : ℂ) * I‖ * ‖((1 - a : ℝ) : ℂ) + (v : ℂ) * I‖)) := by
          refine integral_mono hleft_int.norm (hker_int.const_mul _) fun v => ?_
          rw [norm_div, norm_mul ((-(a : ℂ)) + (v : ℂ) * I)]
          have hgb := hg_strip ((-(a : ℂ)) + (v : ℂ) * I) (by simp) (by simp; linarith)
          simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero,
            Complex.add_im, Complex.neg_im, neg_zero, Complex.mul_im, zero_add] at hgb
          have hsm := hsubmul v
          have hnum : ‖g ((-(a : ℂ)) + (v : ℂ) * I)‖ ≤
              ((N : ℝ) ^ (-a) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ)) * (1 + |v|) ^ (1 / 16 : ℝ) := by
            calc ‖g ((-(a : ℂ)) + (v : ℂ) * I)‖
                ≤ (N : ℝ) ^ (-a) * (C₀ * (2 + |τ + v|) ^ (1 / 16 : ℝ)) := hgb
              _ ≤ (N : ℝ) ^ (-a) * (C₀ * ((2 + |τ|) ^ (1 / 16 : ℝ) * (1 + |v|) ^ (1 / 16 : ℝ))) := by
                  gcongr
              _ = ((N : ℝ) ^ (-a) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ)) * (1 + |v|) ^ (1 / 16 : ℝ) := by ring
          calc ‖g ((-(a : ℂ)) + (v : ℂ) * I)‖ /
                (‖(-(a : ℂ)) + (v : ℂ) * I‖ * ‖((1 - a : ℝ) : ℂ) + (v : ℂ) * I‖)
              ≤ (((N : ℝ) ^ (-a) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ)) * (1 + |v|) ^ (1 / 16 : ℝ)) /
                (‖(-(a : ℂ)) + (v : ℂ) * I‖ * ‖((1 - a : ℝ) : ℂ) + (v : ℂ) * I‖) :=
                div_le_div_of_nonneg_right hnum (by positivity)
            _ = ((N : ℝ) ^ (-a) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ)) *
                ((1 + |v|) ^ (1 / 16 : ℝ) /
                  (‖(-(a : ℂ)) + (v : ℂ) * I‖ * ‖((1 - a : ℝ) : ℂ) + (v : ℂ) * I‖)) := by ring
      _ = ((N : ℝ) ^ (-a) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ)) * I_ker := integral_const_mul _ _
  calc (2 * Real.pi)⁻¹ *
        ‖∫ v : ℝ, g ((-(a : ℂ)) + (v : ℂ) * I) /
          (((-(a : ℂ)) + (v : ℂ) * I) * (((1 - a : ℝ) : ℂ) + (v : ℂ) * I))‖
      ≤ (2 * Real.pi)⁻¹ * (((N : ℝ) ^ (-a) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ)) * I_ker) :=
        mul_le_mul_of_nonneg_left hint_le (by positivity)
    _ ≤ (2 * Real.pi)⁻¹ * (((N : ℝ) ^ (-a) * C₀ * (2 + |τ|) ^ (1 / 16 : ℝ)) * (I_ker + 1)) := by
        gcongr; linarith
    _ = C * (N : ℝ) ^ (-(ε / 2)) * (2 + |τ|) ^ (1 / 16 : ℝ) := by dsimp [C, a]; ring

end BN5


/-
# Module 6: Final assembly of Beurling-Nyman forward direction (RH -> Density)

Combines Modules 1-5 to prove `OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1.H1`.
-/

namespace BN6
open MeasureTheory Set Filter Complex ArithmeticFunction RiemannHypothesis
open scoped Topology ENNReal

/-- Integrability of `(2 + |τ|)^(1/2) / (1/16 + τ^2)` over `ℝ`. -/
lemma integrable_termB_kernel :
    Integrable (fun τ : ℝ => (2 + |τ|) ^ (1 / 2 : ℝ) / (1 / 16 + τ ^ 2)) volume := by
  have hcont : Continuous (fun τ : ℝ => (2 + |τ|) ^ (1 / 2 : ℝ) / (1 / 16 + τ ^ 2)) := by
    refine Continuous.div ?_ (by fun_prop) (fun τ => by positivity)
    exact (continuous_const.add continuous_abs).rpow_const fun _ => Or.inr (by norm_num)
  have hbase : Integrable (fun τ : ℝ => (1 + |τ|) ^ (-3 / 2 : ℝ)) volume := by
    have hpos : IntegrableOn (fun τ : ℝ => (1 + |τ|) ^ (-3 / 2 : ℝ)) (Ioi (0 : ℝ)) := by
      have hshift := integrableOn_Ioi_rpow_of_lt (a := (-3 / 2 : ℝ)) (by norm_num) (by norm_num : (0 : ℝ) < 1)
      rw [← integrable_indicator_iff measurableSet_Ioi] at hshift ⊢
      refine (hshift.comp_add_right 1).congr (ae_of_all _ fun τ => ?_)
      dsimp only
      by_cases hτ : (0 : ℝ) < τ
      · rw [Set.indicator_of_mem (show τ + 1 ∈ Ioi (1 : ℝ) by simp; linarith),
          Set.indicator_of_mem (show τ ∈ Ioi (0 : ℝ) from hτ), abs_of_pos hτ, add_comm]
      · rw [Set.indicator_of_notMem (show τ + 1 ∉ Ioi (1 : ℝ) by simp; linarith),
          Set.indicator_of_notMem (show τ ∉ Ioi (0 : ℝ) from hτ)]
    have hneg : IntegrableOn (fun τ : ℝ => (1 + |τ|) ^ (-3 / 2 : ℝ)) (Iio (0 : ℝ)) := by
      rw [← integrable_indicator_iff measurableSet_Ioi] at hpos
      rw [← integrable_indicator_iff measurableSet_Iio]
      refine hpos.comp_neg.congr (ae_of_all _ fun τ => ?_)
      dsimp only
      by_cases hτ : τ < 0
      · rw [Set.indicator_of_mem (show -τ ∈ Ioi (0 : ℝ) by simp [hτ]),
          Set.indicator_of_mem (show τ ∈ Iio (0 : ℝ) from hτ), abs_neg]
      · rw [Set.indicator_of_notMem (show -τ ∉ Ioi (0 : ℝ) by simp; linarith),
          Set.indicator_of_notMem (show τ ∉ Iio (0 : ℝ) from hτ)]
    rw [← integrableOn_univ]
    refine (hpos.union hneg).congr_set_ae ?_
    rw [ae_eq_set]
    have h1 : (Ioi (0 : ℝ) ∪ Iio (0 : ℝ)) \ univ = ∅ := by simp
    have h2 : univ \ (Ioi (0 : ℝ) ∪ Iio (0 : ℝ)) = {0} := by ext x; simp
    rw [h1, h2]; simp
  refine (hbase.const_mul 64).mono' hcont.aestronglyMeasurable (ae_of_all _ fun τ => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have hnum : (2 + |τ|) ^ (1 / 2 : ℝ) ≤ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) := by
    have hle : 2 + |τ| ≤ 2 * (1 + |τ|) := by linarith [abs_nonneg τ]
    calc (2 + |τ|) ^ (1 / 2 : ℝ) ≤ (2 * (1 + |τ|)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hle (by norm_num)
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) * (1 + |τ|) ^ (1 / 2 : ℝ) := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) := by
          gcongr
          have h2le : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          simpa using h2le
  have hden : (1 + |τ|) ^ 2 / 32 ≤ 1 / 16 + τ ^ 2 := by
    have : (1 + |τ|) ^ 2 ≤ 2 + 2 * τ ^ 2 := by
      have : (1 - |τ|) ^ 2 ≥ 0 := sq_nonneg _
      nlinarith [sq_abs τ]
    linarith [sq_nonneg τ]
  have hpow : (1 + |τ|) ^ (1 / 2 : ℝ) / (1 + |τ|) ^ 2 = (1 + |τ|) ^ (-3 / 2 : ℝ) := by
    rw [show (1 + |τ|) ^ 2 = (1 + |τ|) ^ (2 : ℝ) by norm_cast,
      ← Real.rpow_sub (by positivity : 0 < 1 + |τ|)]
    norm_num
  calc (2 + |τ|) ^ (1 / 2 : ℝ) / (1 / 16 + τ ^ 2)
      ≤ (2 * (1 + |τ|) ^ (1 / 2 : ℝ)) / ((1 + |τ|) ^ 2 / 32) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 64 * ((1 + |τ|) ^ (1 / 2 : ℝ) / (1 + |τ|) ^ 2) := by field_simp; norm_num
    _ = 64 * (1 + |τ|) ^ (-3 / 2 : ℝ) := by rw [hpow]

/-- Growth bound `‖ζ(1/2 - ε + iτ)‖ ≤ C_ζ * (2 + |τ|)^(3/16)` for fixed `ε ∈ (0, 1/8]` under RH. -/
lemma norm_zeta_minus_bound (rh : RiemannHypothesis) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8) :
    ∃ C > 0, ∀ τ : ℝ,
      ‖riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I)‖ ≤ C * (2 + |τ|) ^ (3 / 16 : ℝ) := by
  obtain ⟨C₁, hC₁, hzeta_plus⟩ := BN4.norm_zeta_le_rpow rh (δ := ε) (η := 1 / 16)
    hε0 (by linarith) (by norm_num)
  have hcont : Continuous (fun τ : ℝ => riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro τ
    have hne : (1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have harg : Continuous (fun τ : ℝ => (1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I) := by fun_prop
    exact ContinuousAt.comp (f := fun τ : ℝ => (1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)
      (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt harg.continuousAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont.continuousOn (s := Set.Icc (-1 : ℝ) 1))
  set C₂ : ℝ := max C₁ (max M 1)
  have hC₂_pos : 0 < C₂ := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (le_max_right _ _))
  have hplus_all : ∀ τ : ℝ,
      ‖riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ ≤ C₂ * (2 + |τ|) ^ (1 / 16 : ℝ) := by
    intro τ
    rcases le_or_gt |τ| 1 with hτ | hτ
    · have hle := hM τ (abs_le.mp hτ)
      have h1 : (1 : ℝ) ≤ (2 + |τ|) ^ (1 / 16 : ℝ) :=
        Real.one_le_rpow (by linarith [abs_nonneg τ]) (by norm_num)
      have hMC : M ≤ C₂ := le_trans (le_max_left _ _) (le_max_right _ _)
      nlinarith
    · have hsub1 : (1 / 2 : ℝ) ≤ ‖((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I) - 1‖ := by
        have := Complex.abs_im_le_norm (((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I) - 1)
        simp at this
        linarith
      have hle := hzeta_plus ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I) (by simp) hsub1
      simp only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, zero_div, Complex.ofReal_im,
        add_zero, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
        zero_add] at hle
      exact hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  refine ⟨Real.exp 1 * C₂, by positivity, fun τ => ?_⟩
  have hzr := BN3.norm_zeta_ratio_le hε0 hε1 τ
  have hp := hplus_all τ
  have hpow1 : (1 + |τ|) ^ ε ≤ (2 + |τ|) ^ (1 / 8 : ℝ) := by
    calc (1 + |τ|) ^ ε ≤ (2 + |τ|) ^ ε :=
          Real.rpow_le_rpow (by positivity) (by linarith) hε0.le
      _ ≤ (2 + |τ|) ^ (1 / 8 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg τ]) hε1
  have hpow_add : (2 + |τ|) ^ (1 / 8 : ℝ) * (2 + |τ|) ^ (1 / 16 : ℝ) = (2 + |τ|) ^ (3 / 16 : ℝ) := by
    rw [← Real.rpow_add (by positivity)]; norm_num
  calc ‖riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I)‖
      ≤ Real.exp 1 * (1 + |τ|) ^ ε * ‖riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ := hzr
    _ ≤ Real.exp 1 * (2 + |τ|) ^ (1 / 8 : ℝ) * (C₂ * (2 + |τ|) ^ (1 / 16 : ℝ)) := by
        gcongr
    _ = (Real.exp 1 * C₂) * ((2 + |τ|) ^ (1 / 8 : ℝ) * (2 + |τ|) ^ (1 / 16 : ℝ)) := by ring
    _ = (Real.exp 1 * C₂) * (2 + |τ|) ^ (3 / 16 : ℝ) := by rw [hpow_add]

set_option maxHeartbeats 1200000 in
/-- Core half-line `L²(0, ∞)` approximation under `RiemannHypothesis`. -/
theorem approx_halfline (rh : RiemannHypothesis) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ n : ℕ, ∃ c : Fin n → ℝ,
      eLpNorm (fun x : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x +
        ∑ i, c i * fractScalarInv (1 / ((i.val : ℝ) + 1)) x) 2 (volume.restrict (Ioi 0)) <
          ENNReal.ofReal ε₀ := by
  set η : ℝ := ε₀ / 3
  have hη : 0 < η := by dsimp [η]; positivity
  -- Step 1: Choose `ε ∈ (0, 1/8]` so small that Term A and `|1/ζ(1 + 2ε)|` are tiny.
  have htermA_ev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∫ τ : ℝ, ‖1 - riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) /
        riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ ^ 2 /
        ((1 / 2 - ε) ^ 2 + τ ^ 2) < (2 * Real.pi) * (η / 2) ^ 2 / 4 :=
    (BN3.tendsto_termA_zero rh).eventually (Iio_mem_nhds (by positivity))
  have htail_ev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      |(riemannZeta (1 + ((2 * ε : ℝ) : ℂ)))⁻¹.re| < η / 2 := by
    have h2 : Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hc : Continuous (fun ε : ℝ => 2 * ε) := by fun_prop
        simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
        show 0 < 2 * ε; linarith
    have hlim := (BN1.reciprocal_zeta_tendsto_zero.comp h2).abs
    rw [abs_zero] at hlim
    exact hlim.eventually (Iio_mem_nhds (half_pos hη))
  have hsmall_ev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) (1 / 8) :=
    Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨ε, hε_ioo, htermA_lt, htail_lt⟩ := (hsmall_ev.and (htermA_ev.and htail_ev)).exists
  have hε0 : 0 < ε := hε_ioo.1
  have hε1 : ε ≤ 1 / 8 := hε_ioo.2.le
  -- Step 2: Obtain the fixed-`ε` bounds for `ζ(1/2 - ε + iτ)` and `D_N - invZeta`.
  obtain ⟨C_ζ, hC_ζ, hzeta_m⟩ := norm_zeta_minus_bound rh hε0 hε1
  obtain ⟨C_err, hC_err, herr⟩ := BN5.riesz_perron_error_bound rh hε0 hε1
  set I_B : ℝ := ∫ τ : ℝ, (2 + |τ|) ^ (1 / 2 : ℝ) / (1 / 16 + τ ^ 2)
  have hI_B_nn : 0 ≤ I_B := integral_nonneg fun _ => by positivity
  set C_B : ℝ := 2 * (C_ζ * C_err) ^ 2 * (I_B + 1)
  have hC_B_pos : 0 < C_B := by positivity
  -- Step 3: Choose `N ≥ 1` large enough that BOTH Term B and the `(1, ∞)` tail are small.
  have hN_termB : ∀ᶠ N : ℕ in atTop,
      C_B * (N : ℝ) ^ (-ε) < (2 * Real.pi) * (η / 2) ^ 2 / 2 := by
    have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (-ε)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hε0).comp tendsto_natCast_atTop_atTop
    have hmul := hpow.const_mul C_B
    rw [mul_zero] at hmul
    exact hmul.eventually (Iio_mem_nhds (by positivity))
  have hN_tail : ∀ᶠ N : ℕ in atTop,
      |∑ i : Fin N, ((moebius (i.val + 1) : ℝ) / ((i.val : ℝ) + 1) ^ (1 + 2 * ε)) *
        (1 - ((i.val : ℝ) + 1) / (N : ℝ))| < η := by
    have ht := (BN1.tendsto_riesz_moebius_tail (d := 2 * ε) (by linarith)).abs
    exact ht.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨N, hN1, hN_B, hN_t⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and (hN_termB.and hN_tail)).exists
  -- Step 4: Define coefficients `c : Fin N → ℝ` and verify the `L²(Ioi 0)` bound!
  let c : Fin N → ℝ := fun i =>
    ((moebius (i.val + 1) : ℝ) / ((i.val : ℝ) + 1) ^ (2 * ε)) *
      (1 - ((i.val : ℝ) + 1) / (N : ℝ))
  let F : ℝ → ℝ := fun x =>
    (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x +
      ∑ i : Fin N, c i * fractScalarInv (1 / ((i.val : ℝ) + 1)) x
  let g : ℝ → ℝ := fun x => x ^ (-ε) * F x
  refine ⟨N, c, ?_⟩
  -- Part A: `(1, ∞)` tail bound.
  have htail_norm : eLpNorm F 2 (volume.restrict (Ioi (1 : ℝ))) < ENNReal.ofReal η := by
    refine (BN1.tail_L2_le N c).trans_lt ?_
    refine ENNReal.ofReal_lt_ofReal_iff hη |>.mpr ?_
    have heq_sum : (∑ i : Fin N, c i / ((i.val : ℝ) + 1)) =
        ∑ i : Fin N, ((moebius (i.val + 1) : ℝ) / ((i.val : ℝ) + 1) ^ (1 + 2 * ε)) *
          (1 - ((i.val : ℝ) + 1) / (N : ℝ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp [c]
      have hpos : (0 : ℝ) < (i.val : ℝ) + 1 := by positivity
      have hpow : ((i.val : ℝ) + 1) ^ (1 + 2 * ε) =
          ((i.val : ℝ) + 1) * ((i.val : ℝ) + 1) ^ (2 * ε) := by
        rw [Real.rpow_add hpos, Real.rpow_one]
      rw [hpow, mul_comm ((i.val : ℝ) + 1) _, ← div_div]; ring
    rw [heq_sum]
    exact hN_t
  -- Part B: `(0, 1]` bound via `X_ε` weight + Mellin-Plancherel!
  have hg_meas : Measurable g := by
    have hF_meas : Measurable F := by
      refine (measurable_const.indicator measurableSet_Ioc).add ?_
      refine Finset.measurable_sum _ fun i _ => ?_
      exact measurable_const.mul (measurable_fract.comp (measurable_const.div measurable_id))
    exact (measurable_id.pow_const (-ε)).mul hF_meas
  let K_N : ℝ := 1 + ∑ i : Fin N, |c i|
  have hK_N_pos : 0 < K_N := by
    have : 0 ≤ ∑ i : Fin N, |c i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    dsimp [K_N]; linarith
  -- Pointwise exponential decay of `h(u) = e^(u/2) g(e^u)`.
  let h : ℝ → ℂ := fun u => (Real.exp (u / 2) : ℂ) * (g (Real.exp u) : ℂ)
  have hh_meas : AEStronglyMeasurable h volume :=
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.div_const 2))).measurable.mul
      (Complex.continuous_ofReal.measurable.comp (hg_meas.comp Real.continuous_exp.measurable))).aestronglyMeasurable
  have hh_decay : ∀ u : ℝ, ‖h u‖ ≤ K_N * Real.exp (-(1 / 4) * |u|) := by
    intro u
    dsimp [h, g]
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Real.exp_pos u).le _),
      ← Real.exp_mul, ← mul_assoc, ← Real.exp_add]
    have hF_le : |F (Real.exp u)| ≤ if u ≤ 0 then K_N else K_N * Real.exp (-u) := by
      by_cases hu : u ≤ 0
      · rw [if_pos hu]
        dsimp [F]
        have hind : |(Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (Real.exp u)| ≤ 1 := by
          by_cases hm : Real.exp u ∈ Ioc (0 : ℝ) 1
          · rw [Set.indicator_of_mem hm]; norm_num
          · rw [Set.indicator_of_notMem hm]; norm_num
        have hsum : |∑ i : Fin N, c i * fractScalarInv (1 / ((i.val : ℝ) + 1)) (Real.exp u)| ≤
            ∑ i : Fin N, |c i| := by
          calc |∑ i : Fin N, c i * fractScalarInv (1 / ((i.val : ℝ) + 1)) (Real.exp u)|
              ≤ ∑ i : Fin N, |c i * fractScalarInv (1 / ((i.val : ℝ) + 1)) (Real.exp u)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i : Fin N, |c i| := by
                refine Finset.sum_le_sum fun i _ => ?_
                have hfr_nn : 0 ≤ fractScalarInv (1 / ((i.val : ℝ) + 1)) (Real.exp u) := Int.fract_nonneg _
                rw [abs_mul, abs_of_nonneg hfr_nn]
                exact mul_le_of_le_one_right (abs_nonneg _) (Int.fract_lt_one _).le
        exact (abs_add_le _ _).trans (by dsimp [K_N]; linarith)
      · rw [if_neg hu]
        have hu_pos : 0 < u := not_le.mp hu
        have hexp_gt1 : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu_pos
        have hout : Real.exp u ∉ Ioc (0 : ℝ) 1 := fun hm => hexp_gt1.not_ge hm.2
        dsimp [F]
        rw [Set.indicator_of_notMem hout, zero_add]
        have hfr : ∀ i : Fin N, fractScalarInv (1 / ((i.val : ℝ) + 1)) (Real.exp u) =
            (1 / ((i.val : ℝ) + 1)) / Real.exp u := fun i => by
          apply Int.fract_eq_self.mpr
          have hpos : (0 : ℝ) < (i.val : ℝ) + 1 := by positivity
          have hle1 : 1 / ((i.val : ℝ) + 1) ≤ 1 := (div_le_one hpos).mpr (by linarith [Nat.cast_nonneg (α := ℝ) i.val])
          exact ⟨by positivity, (div_lt_one (Real.exp_pos u)).mpr (hle1.trans_lt hexp_gt1)⟩
        simp_rw [hfr]
        calc |∑ i : Fin N, c i * (1 / ((i.val : ℝ) + 1) / Real.exp u)|
            ≤ ∑ i : Fin N, |c i * (1 / ((i.val : ℝ) + 1) / Real.exp u)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i : Fin N, |c i| * Real.exp (-u) := by
              refine Finset.sum_le_sum fun i _ => ?_
              have hfr_nn : 0 ≤ 1 / ((i.val : ℝ) + 1) / Real.exp u := by positivity
              rw [abs_mul, abs_of_nonneg hfr_nn, Real.exp_neg, div_eq_mul_inv]
              have hle1 : 1 / ((i.val : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) i.val])
              exact mul_le_mul_of_nonneg_left
                (mul_le_of_le_one_left (inv_nonneg.mpr (Real.exp_pos u).le) hle1) (abs_nonneg _)
          _ = (∑ i : Fin N, |c i|) * Real.exp (-u) := (Finset.sum_mul _ _ _).symm
          _ ≤ K_N * Real.exp (-u) := by dsimp [K_N]; gcongr; linarith
    by_cases hu : u ≤ 0
    · rw [if_pos hu] at hF_le
      rw [abs_of_nonpos hu]
      calc Real.exp (u / 2 + u * -ε) * |F (Real.exp u)|
          ≤ Real.exp (u / 2 + u * -ε) * K_N := mul_le_mul_of_nonneg_left hF_le (Real.exp_pos _).le
        _ = K_N * Real.exp (u * (1 / 2 - ε)) := by ring_nf
        _ ≤ K_N * Real.exp (-(1 / 4) * -u) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hK_N_pos.le
    · rw [if_neg hu] at hF_le
      have hu_pos : 0 < u := not_le.mp hu
      rw [abs_of_pos hu_pos]
      calc Real.exp (u / 2 + u * -ε) * |F (Real.exp u)|
          ≤ Real.exp (u / 2 + u * -ε) * (K_N * Real.exp (-u)) := mul_le_mul_of_nonneg_left hF_le (Real.exp_pos _).le
        _ = K_N * (Real.exp (u / 2 + u * -ε) * Real.exp (-u)) := by ring
        _ = K_N * Real.exp (u / 2 + u * -ε + -u) := by rw [← Real.exp_add]
        _ ≤ K_N * Real.exp (-(1 / 4) * u) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hK_N_pos.le
  have hexp_abs_int : ∀ r : ℝ, 0 < r → Integrable (fun u : ℝ => Real.exp (-r * |u|)) volume := by
    intro r hr
    have hpos : IntegrableOn (fun u : ℝ => Real.exp (-r * |u|)) (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (by linarith : -r < 0) 0).congr_fun
        (fun u (hu : 0 < u) => by simp [abs_of_pos hu]) measurableSet_Ioi
    have hneg : IntegrableOn (fun u : ℝ => Real.exp (-r * |u|)) (Iio (0 : ℝ)) := by
      rw [← integrable_indicator_iff measurableSet_Ioi] at hpos
      rw [← integrable_indicator_iff measurableSet_Iio]
      refine hpos.comp_neg.congr (ae_of_all _ fun u => ?_)
      dsimp only
      by_cases hu : u < 0
      · rw [Set.indicator_of_mem (show -u ∈ Ioi (0 : ℝ) by simp [hu]),
          Set.indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu), abs_neg]
      · rw [Set.indicator_of_notMem (show -u ∉ Ioi (0 : ℝ) by simp; linarith),
          Set.indicator_of_notMem (show u ∉ Iio (0 : ℝ) from hu)]
    rw [← integrableOn_univ]
    refine (hpos.union hneg).congr_set_ae ?_
    rw [ae_eq_set]
    have h1 : (Ioi (0 : ℝ) ∪ Iio (0 : ℝ)) \ univ = ∅ := by simp
    have h2 : univ \ (Ioi (0 : ℝ) ∪ Iio (0 : ℝ)) = {0} := by ext x; simp
    rw [h1, h2]; simp
  have hh1 : Integrable h volume :=
    ((hexp_abs_int (1 / 4) (by norm_num)).const_mul K_N).mono' hh_meas (ae_of_all _ hh_decay)
  have hh2 : MemLp h 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hh_meas).mpr ?_
    refine ((hexp_abs_int (1 / 2) (by norm_num)).const_mul (K_N ^ 2)).mono'
      (hh_meas.norm.pow 2) (ae_of_all _ fun u => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc ‖h u‖ ^ 2 ≤ (K_N * Real.exp (-(1 / 4) * |u|)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hh_decay u) 2
      _ = K_N ^ 2 * Real.exp (-(1 / 2) * |u|) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  -- Evaluate the Mellin transform `M(τ)` explicitly!
  let M : ℝ → ℂ := fun τ =>
    ∫ x in Ioi (0 : ℝ), (g x : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ) + (τ : ℂ) * I)
  have hM_eq : ∀ τ : ℝ, M τ =
      (1 - riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) *
        BN5.rieszMoebiusSum N ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)) /
        ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) := by
    intro τ
    set s_m : ℂ := (1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I
    set s_p : ℂ := (1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I
    have hsm_pos : 0 < s_m.re := by simp [s_m]; linarith
    have hsm_lt1 : s_m.re < 1 := by simp [s_m]; linarith
    have hcongr : ∫ x in Ioi (0 : ℝ), (g x : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ) + (τ : ℂ) * I) =
        ∫ x in Ioi (0 : ℝ),
          (((Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x : ℂ) * (x : ℂ) ^ (s_m - 1) +
           ∑ i : Fin N, (c i : ℂ) *
             ((BN2.recipFractScaled ((i.val : ℝ) + 1) x : ℂ) * (x : ℂ) ^ (s_m - 1))) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_
      have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
      have hpow_comb : ((x ^ (-ε) : ℝ) : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ) + (τ : ℂ) * I) =
          (x : ℂ) ^ (s_m - 1) := by
        rw [Complex.ofReal_cpow hx.le, ← Complex.cpow_add _ _ hx_ne]
        congr 1; dsimp [s_m]; push_cast; ring
      dsimp [g, F]
      rw [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sum,
        mul_comm (((x ^ (-ε) : ℝ) : ℂ)), mul_assoc, hpow_comb, add_mul, Finset.sum_mul]
      congr 1
      · by_cases hmem : x ∈ Ioc (0 : ℝ) 1
        · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]; simp
        · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]; simp
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.ofReal_mul, BN2.recipFractScaled_eq_fractScalarInv, mul_assoc]
    have hint_chi : IntegrableOn (fun x : ℝ =>
        ((Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x : ℂ) * (x : ℂ) ^ (s_m - 1)) (Ioi (0 : ℝ)) := by
      have h1 := BN2.integrableOn_Ioc_cpow s_m hsm_pos
      rw [← integrable_indicator_iff measurableSet_Ioc] at h1
      rw [← integrable_indicator_iff measurableSet_Ioi]
      refine h1.congr (ae_of_all _ fun x => ?_)
      by_cases hx : x ∈ Ioc (0 : ℝ) 1
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx.1),
          Set.indicator_of_mem hx]; simp
      · rw [Set.indicator_of_notMem hx]
        by_cases hx0 : x ∈ Ioi (0 : ℝ)
        · rw [Set.indicator_of_mem hx0, Set.indicator_of_notMem hx]; simp
        · rw [Set.indicator_of_notMem hx0]
    have hint_term : ∀ i : Fin N, IntegrableOn (fun x : ℝ =>
        (c i : ℂ) * ((BN2.recipFractScaled ((i.val : ℝ) + 1) x : ℂ) * (x : ℂ) ^ (s_m - 1))) (Ioi (0 : ℝ)) := by
      intro i
      exact (BN2.integrableOn_Ioi_recipFractScaled_cpow ((i.val : ℝ) + 1)
        (by linarith [Nat.cast_nonneg (α := ℝ) i.val]) s_m hsm_pos hsm_lt1).const_mul (c i : ℂ)
    have hint_sum : IntegrableOn (fun x : ℝ =>
        ∑ i : Fin N, (c i : ℂ) *
          ((BN2.recipFractScaled ((i.val : ℝ) + 1) x : ℂ) * (x : ℂ) ^ (s_m - 1))) (Ioi (0 : ℝ)) :=
      integrable_finsetSum _ fun i _ => hint_term i
    dsimp [M]
    rw [hcongr, integral_add hint_chi hint_sum, BN2.mellin_indicator_Ioc s_m hsm_pos,
      integral_finsetSum _ fun i _ => hint_term i]
    have hsum_eval : (∑ i : Fin N, ∫ x in Ioi (0 : ℝ),
        (c i : ℂ) * ((BN2.recipFractScaled ((i.val : ℝ) + 1) x : ℂ) * (x : ℂ) ^ (s_m - 1))) =
        -(riemannZeta s_m * BN5.rieszMoebiusSum N s_p) / s_m := by
      have hterm_eval : ∀ i : Fin N,
          ∫ x in Ioi (0 : ℝ), (c i : ℂ) *
            ((BN2.recipFractScaled ((i.val : ℝ) + 1) x : ℂ) * (x : ℂ) ^ (s_m - 1)) =
          -(riemannZeta s_m / s_m) *
            ((moebius (i.val + 1) : ℂ) * (1 - ((((i.val : ℝ) + 1) / (N : ℝ) : ℝ) : ℂ)) /
              ((i.val + 1 : ℕ) : ℂ) ^ s_p) := by
        intro i
        have hi_pos : (0 : ℝ) < (i.val : ℝ) + 1 := by positivity
        have hi_ge1 : (1 : ℝ) ≤ (i.val : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) i.val]
        rw [integral_const_mul, BN2.mellin_recipFractScaled ((i.val : ℝ) + 1) hi_ge1 s_m ⟨hsm_pos, hsm_lt1⟩]
        have hi_ne : (((i.val : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hi_pos.ne'
        have hcast_i : ((i.val + 1 : ℕ) : ℂ) = (((i.val : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
        have hpow_comb : ((((i.val : ℝ) + 1) ^ (2 * ε) : ℝ) : ℂ) * (((i.val : ℝ) + 1 : ℝ) : ℂ) ^ s_m =
            ((i.val + 1 : ℕ) : ℂ) ^ s_p := by
          rw [Complex.ofReal_cpow hi_pos.le, ← Complex.cpow_add _ _ hi_ne, hcast_i]
          congr 1; dsimp [s_m, s_p]; push_cast; ring
        dsimp [c]
        push_cast at hpow_comb ⊢
        rw [← hpow_comb]
        ring
      simp_rw [hterm_eval]
      rw [← Finset.mul_sum]
      dsimp [BN5.rieszMoebiusSum]
      ring
    rw [hsum_eval]
    ring
  -- Bound `‖M τ‖^2` using Term A + Term B, proving both `MemLp M 2 volume` and the integral estimate!
  have hM_sq_bound : ∀ τ : ℝ, ‖M τ‖ ^ 2 ≤
      2 * (‖1 - riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) /
            riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ ^ 2 /
            ((1 / 2 - ε) ^ 2 + τ ^ 2)) +
      (2 * (C_ζ * C_err) ^ 2 * (N : ℝ) ^ (-ε)) *
        ((2 + |τ|) ^ (1 / 2 : ℝ) / (1 / 16 + τ ^ 2)) := by
    intro τ
    set s_m : ℂ := (1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I
    set s_p : ℂ := (1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I
    have hsp_ne1 : s_p ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp [s_p] at this; linarith
    have hsp_ne0 : riemannZeta s_p ≠ 0 :=
      BN3.riemannZeta_ne_zero_of_rh rh (by simp [s_p]; linarith) hsp_ne1
    have hsplit : 1 - riemannZeta s_m * BN5.rieszMoebiusSum N s_p =
        (1 - riemannZeta s_m / riemannZeta s_p) +
        riemannZeta s_m * (BN4.invZeta s_p - BN5.rieszMoebiusSum N s_p) := by
      rw [BN4.invZeta_of_ne_one hsp_ne1]
      field_simp [hsp_ne0]
      ring
    have hsm_sq : ‖s_m‖ ^ 2 = (1 / 2 - ε) ^ 2 + τ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp [s_m]; ring
    have hsm_ge : 1 / 16 + τ ^ 2 ≤ (1 / 2 - ε) ^ 2 + τ ^ 2 := by nlinarith
    rw [hM_eq τ, norm_div, div_pow, hsm_sq, hsplit]
    have htri2 : ∀ a b : ℂ, ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := fun a b => by
      have h1 := norm_add_le a b
      have h2 : (‖a‖ - ‖b‖) ^ 2 ≥ 0 := sq_nonneg _
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) h1 2]
    have hnum_le := htri2 (1 - riemannZeta s_m / riemannZeta s_p)
      (riemannZeta s_m * (BN4.invZeta s_p - BN5.rieszMoebiusSum N s_p))
    have htermB_num : ‖riemannZeta s_m * (BN4.invZeta s_p - BN5.rieszMoebiusSum N s_p)‖ ^ 2 ≤
        (C_ζ * C_err) ^ 2 * (N : ℝ) ^ (-ε) * (2 + |τ|) ^ (1 / 2 : ℝ) := by
      rw [norm_mul, norm_sub_rev]
      have h1 := hzeta_m τ
      have h2 := herr N hN1 τ
      have hprod : ‖riemannZeta s_m‖ * ‖BN5.rieszMoebiusSum N s_p - BN4.invZeta s_p‖ ≤
          (C_ζ * C_err) * (N : ℝ) ^ (-(ε / 2)) * (2 + |τ|) ^ (1 / 4 : ℝ) := by
        have hpow_t : (2 + |τ|) ^ (3 / 16 : ℝ) * (2 + |τ|) ^ (1 / 16 : ℝ) = (2 + |τ|) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_add (by positivity)]; norm_num
        calc ‖riemannZeta s_m‖ * ‖BN5.rieszMoebiusSum N s_p - BN4.invZeta s_p‖
            ≤ (C_ζ * (2 + |τ|) ^ (3 / 16 : ℝ)) * (C_err * (N : ℝ) ^ (-(ε / 2)) * (2 + |τ|) ^ (1 / 16 : ℝ)) :=
              mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          _ = (C_ζ * C_err) * (N : ℝ) ^ (-(ε / 2)) * ((2 + |τ|) ^ (3 / 16 : ℝ) * (2 + |τ|) ^ (1 / 16 : ℝ)) := by ring
          _ = (C_ζ * C_err) * (N : ℝ) ^ (-(ε / 2)) * (2 + |τ|) ^ (1 / 4 : ℝ) := by rw [hpow_t]
      have hN_sq : ((N : ℝ) ^ (-(ε / 2))) ^ (2 : ℕ) = (N : ℝ) ^ (-ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]; congr 1; push_cast; ring
      have ht_sq : ((2 + |τ|) ^ (1 / 4 : ℝ)) ^ (2 : ℕ) = (2 + |τ|) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      calc (‖riemannZeta s_m‖ * ‖BN5.rieszMoebiusSum N s_p - BN4.invZeta s_p‖) ^ 2
          ≤ ((C_ζ * C_err) * (N : ℝ) ^ (-(ε / 2)) * (2 + |τ|) ^ (1 / 4 : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hprod 2
        _ = (C_ζ * C_err) ^ 2 * ((N : ℝ) ^ (-(ε / 2))) ^ 2 * ((2 + |τ|) ^ (1 / 4 : ℝ)) ^ 2 := by ring
        _ = (C_ζ * C_err) ^ 2 * (N : ℝ) ^ (-ε) * (2 + |τ|) ^ (1 / 2 : ℝ) := by rw [hN_sq, ht_sq]
    have hden_pos : 0 < (1 / 2 - ε) ^ 2 + τ ^ 2 := by nlinarith
    calc ‖(1 - riemannZeta s_m / riemannZeta s_p) +
            riemannZeta s_m * (BN4.invZeta s_p - BN5.rieszMoebiusSum N s_p)‖ ^ 2 /
            ((1 / 2 - ε) ^ 2 + τ ^ 2)
        ≤ (2 * ‖1 - riemannZeta s_m / riemannZeta s_p‖ ^ 2 +
            2 * ‖riemannZeta s_m * (BN4.invZeta s_p - BN5.rieszMoebiusSum N s_p)‖ ^ 2) /
            ((1 / 2 - ε) ^ 2 + τ ^ 2) :=
          div_le_div_of_nonneg_right hnum_le hden_pos.le
      _ = 2 * (‖1 - riemannZeta s_m / riemannZeta s_p‖ ^ 2 / ((1 / 2 - ε) ^ 2 + τ ^ 2)) +
          2 * (‖riemannZeta s_m * (BN4.invZeta s_p - BN5.rieszMoebiusSum N s_p)‖ ^ 2 /
            ((1 / 2 - ε) ^ 2 + τ ^ 2)) := by ring
      _ ≤ 2 * (‖1 - riemannZeta s_m / riemannZeta s_p‖ ^ 2 / ((1 / 2 - ε) ^ 2 + τ ^ 2)) +
          2 * (((C_ζ * C_err) ^ 2 * (N : ℝ) ^ (-ε) * (2 + |τ|) ^ (1 / 2 : ℝ)) / (1 / 16 + τ ^ 2)) := by
          gcongr
      _ = 2 * (‖1 - riemannZeta s_m / riemannZeta s_p‖ ^ 2 / ((1 / 2 - ε) ^ 2 + τ ^ 2)) +
          (2 * (C_ζ * C_err) ^ 2 * (N : ℝ) ^ (-ε)) *
            ((2 + |τ|) ^ (1 / 2 : ℝ) / (1 / 16 + τ ^ 2)) := by ring
  -- Integrability of Term A at fixed `ε`.
  have htermA_int : Integrable (fun τ : ℝ =>
      ‖1 - riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) /
        riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ ^ 2 /
        ((1 / 2 - ε) ^ 2 + τ ^ 2)) volume := by
    have hcont : Continuous (fun τ : ℝ =>
        ‖1 - riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) /
          riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ ^ 2 /
          ((1 / 2 - ε) ^ 2 + τ ^ 2)) := by
      have hc1 : Continuous (fun τ : ℝ => riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I)) := by
        rw [continuous_iff_continuousAt]; intro τ
        have hne : (1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I ≠ 1 := fun h => by
          have := congrArg Complex.re h; simp at this; linarith
        have harg : Continuous (fun τ : ℝ => (1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) := by fun_prop
        exact ContinuousAt.comp (f := fun τ : ℝ => (1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I)
          (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt harg.continuousAt
      have hc2 : Continuous (fun τ : ℝ => riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)) := by
        rw [continuous_iff_continuousAt]; intro τ
        have hne : (1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I ≠ 1 := fun h => by
          have := congrArg Complex.re h; simp at this; linarith
        have harg : Continuous (fun τ : ℝ => (1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I) := by fun_prop
        exact ContinuousAt.comp (f := fun τ : ℝ => (1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)
          (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt harg.continuousAt
      have hne2 : ∀ τ : ℝ, riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I) ≠ 0 := fun τ =>
        BN3.riemannZeta_ne_zero_of_rh rh (by simp; linarith) fun h => by
          have := congrArg Complex.re h; simp at this; linarith
      refine Continuous.div ?_ (by fun_prop) (fun τ => by nlinarith)
      exact ((continuous_const.sub (hc1.div hc2 hne2)).norm).pow 2
    refine BN3.integrable_dom_termA.mono' hcont.aestronglyMeasurable (ae_of_all _ fun τ => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have hne2 : riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I) ≠ 0 :=
      BN3.riemannZeta_ne_zero_of_rh rh (by simp; linarith) fun h => by
        have := congrArg Complex.re h; simp at this; linarith
    have hzr := BN3.norm_zeta_ratio_le hε0 hε1 τ
    have hdiv_le : ‖riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) /
        riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ ≤
        Real.exp 1 * (1 + |τ|) ^ (1 / 8 : ℝ) := by
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hne2)]
      have hrpow_le : (1 + |τ|) ^ ε ≤ (1 + |τ|) ^ (1 / 8 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg τ]) hε1
      calc ‖riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I)‖
          ≤ Real.exp 1 * (1 + |τ|) ^ ε * ‖riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ := hzr
        _ ≤ Real.exp 1 * (1 + |τ|) ^ (1 / 8 : ℝ) *
            ‖riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ := by gcongr
    have hnum_le : ‖1 - riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) /
        riemannZeta ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤
        (1 + Real.exp 1 * (1 + |τ|) ^ (1 / 8 : ℝ)) ^ 2 := by
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
    exact div_le_div₀ (by positivity) hnum_le (by positivity) (by nlinarith)
  have hM_cont : Continuous M := by
    have heq : M = fun τ : ℝ =>
        (1 - riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) *
          BN5.rieszMoebiusSum N ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)) /
          ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) := funext hM_eq
    rw [heq]
    have hc1 : Continuous (fun τ : ℝ => riemannZeta ((1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I)) := by
      rw [continuous_iff_continuousAt]; intro τ
      have hne : (1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I ≠ 1 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      have harg : Continuous (fun τ : ℝ => (1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I) := by fun_prop
      exact ContinuousAt.comp (f := fun τ : ℝ => (1 / 2 : ℂ) - (ε : ℂ) + (τ : ℂ) * I)
        (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt harg.continuousAt
    have hcD : Continuous (fun τ : ℝ => BN5.rieszMoebiusSum N ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)) := by
      unfold BN5.rieszMoebiusSum
      refine continuous_finsetSum _ fun i _ => Continuous.div continuous_const ?_ fun τ =>
        Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)))
      have hcp_eq : (fun τ : ℝ => ((i.val + 1 : ℕ) : ℂ) ^ ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)) =
          fun τ : ℝ => Complex.exp (Complex.log ((i.val + 1 : ℕ) : ℂ) * ((1 / 2 : ℂ) + (ε : ℂ) + (τ : ℂ) * I)) := by
        ext τ
        exact Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)) _
      rw [hcp_eq]; fun_prop
    refine Continuous.div (continuous_const.sub (hc1.mul hcD)) (by fun_prop) fun τ h => by
      have := congrArg Complex.re h; simp at this; linarith
  have hM_sq_int : Integrable (fun τ : ℝ => ‖M τ‖ ^ 2) volume := by
    refine ((htermA_int.const_mul 2).add
      (integrable_termB_kernel.const_mul (2 * (C_ζ * C_err) ^ 2 * (N : ℝ) ^ (-ε)))).mono'
      (hM_cont.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun τ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hM_sq_bound τ
  have hM2 : MemLp M 2 volume :=
    (memLp_two_iff_integrable_sq_norm hM_cont.aestronglyMeasurable).mpr hM_sq_int
  -- Apply Mellin-Plancherel!
  have hplanch := BN2.mellin_plancherel g hh1 hh2 hM2
  have hM_int_lt : ∫ τ : ℝ, ‖M τ‖ ^ 2 < (2 * Real.pi) * (η / 2) ^ 2 := by
    have hle := integral_mono hM_sq_int
      ((htermA_int.const_mul 2).add
        (integrable_termB_kernel.const_mul (2 * (C_ζ * C_err) ^ 2 * (N : ℝ) ^ (-ε))))
      hM_sq_bound
    dsimp only [Pi.add_apply] at hle
    rw [integral_add (htermA_int.const_mul 2)
      (integrable_termB_kernel.const_mul (2 * (C_ζ * C_err) ^ 2 * (N : ℝ) ^ (-ε))),
      integral_const_mul, integral_const_mul] at hle
    have hB_le : (2 * (C_ζ * C_err) ^ 2 * (N : ℝ) ^ (-ε)) * I_B ≤ C_B * (N : ℝ) ^ (-ε) := by
      dsimp [C_B]
      have : (2 * (C_ζ * C_err) ^ 2 * (N : ℝ) ^ (-ε)) * I_B =
          (2 * (C_ζ * C_err) ^ 2 * I_B) * (N : ℝ) ^ (-ε) := by ring
      rw [this]
      gcongr
      linarith
    linarith
  have hg_sq_lt : ∫ x in Ioi (0 : ℝ), (g x) ^ 2 < (η / 2) ^ 2 := by
    rw [hplanch]
    have hpi : 0 < 2 * Real.pi := by positivity
    calc (2 * Real.pi)⁻¹ * ∫ τ : ℝ, ‖M τ‖ ^ 2
        < (2 * Real.pi)⁻¹ * ((2 * Real.pi) * (η / 2) ^ 2) :=
          mul_lt_mul_of_pos_left hM_int_lt (inv_pos.mpr hpi)
      _ = (η / 2) ^ 2 := inv_mul_cancel_left₀ hpi.ne' _
  -- Convert `∫ x in Ioi 0, (g x)^2 < (η / 2)^2` to `eLpNorm g 2 (volume.restrict (Ioi 0)) < ENNReal.ofReal η`.
  have hg_sq_int : IntegrableOn (fun x : ℝ => (g x) ^ 2) (Ioi (0 : ℝ)) := by
    have hh_sq : Integrable (fun u : ℝ => Real.exp u * (g (Real.exp u)) ^ 2) volume := by
      refine hh2.norm.integrable_sq.congr (ae_of_all _ fun u => ?_)
      dsimp [h]
      rw [norm_mul, Complex.norm_real, Complex.norm_real, mul_pow,
        Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul,
        show (2 : ℕ) * (u / 2) = u by push_cast; ring, Real.norm_eq_abs, sq_abs]
    have himg : Real.exp '' (univ : Set ℝ) = Ioi (0 : ℝ) := by rw [image_univ]; exact Real.range_exp
    rw [← himg]
    exact (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn
      (fun x : ℝ => (g x) ^ 2)).mpr (by
        rw [integrableOn_univ]
        refine hh_sq.congr (ae_of_all _ fun u => ?_)
        simp [abs_of_pos (Real.exp_pos u)])
  have hg_norm_lt : eLpNorm g 2 (volume.restrict (Ioi (0 : ℝ))) < ENNReal.ofReal η := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp)]
    have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
    rw [h2]
    have hlint : ∫⁻ x in Ioi (0 : ℝ), ‖g x‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (∫ x in Ioi (0 : ℝ), (g x) ^ 2) := by
      rw [ofReal_integral_eq_lintegral_ofReal hg_sq_int (ae_of_all _ fun _ => sq_nonneg _)]
      refine setLIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        Real.rpow_two, Real.norm_eq_abs, sq_abs]
    rw [hlint, ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun _ => sq_nonneg _) (by norm_num)]
    refine ENNReal.ofReal_lt_ofReal_iff hη |>.mpr ?_
    have hsq_lt : (∫ x in Ioi (0 : ℝ), (g x) ^ 2) ^ (1 / 2 : ℝ) < η / 2 := by
      have hnonneg : 0 ≤ ∫ x in Ioi (0 : ℝ), (g x) ^ 2 := integral_nonneg fun _ => sq_nonneg _
      have hrpow_lt := Real.rpow_lt_rpow hnonneg hg_sq_lt (by norm_num : (0 : ℝ) < 1 / 2)
      have hη_eq : ((η / 2) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = η / 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      rwa [hη_eq] at hrpow_lt
    linarith
  have hbody_norm : eLpNorm F 2 (volume.restrict (Ioc (0 : ℝ) 1)) < ENNReal.ofReal η :=
    (BN1.weight_Ioc_le ε hε0 F).trans_lt hg_norm_lt
  -- Combine `(0, 1]` and `(1, ∞)`!
  calc eLpNorm F 2 (volume.restrict (Ioi (0 : ℝ)))
      ≤ eLpNorm F 2 (volume.restrict (Ioc (0 : ℝ) 1)) +
        eLpNorm F 2 (volume.restrict (Ioi (1 : ℝ))) := BN1.splitNorm_one F
    _ < ENNReal.ofReal η + ENNReal.ofReal η := ENNReal.add_lt_add hbody_norm htail_norm
    _ = ENNReal.ofReal (η + η) := (ENNReal.ofReal_add hη.le hη.le).symm
    _ < ENNReal.ofReal ε₀ := (ENNReal.ofReal_lt_ofReal_iff hε₀).mpr (by dsimp [η]; linarith)

end BN6

theorem OMA.solution : OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1.H1 :=
  BN1.reduce_to_halfline BN6.approx_halfline
