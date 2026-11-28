import OMAStatements.S_mo_45322
import Mathlib

namespace Mo45322

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

/-! Section 1: Measures, kernel K_s, sigma-finiteness, and null-set equivalence -/

def Iset : Set ℝ := Set.Icc (0 : ℝ) 1

noncomputable def μI : Measure ℝ := volume.restrict Iset

noncomputable def μΩ : Measure (ℝ × ℝ) := μI.prod μI

noncomputable def sVal (α : NNReal) : ℝ := 1 / 2 - (α : ℝ)

noncomputable def Ks (s : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  if p.1 = p.2 then 0 else ENNReal.ofReal (|p.1 - p.2| ^ (-(1 + 2 * s)))

noncomputable def μ₂ (s : ℝ) : Measure (ℝ × ℝ) := μΩ.withDensity (Ks s)

lemma measurableSet_Iset : MeasurableSet Iset := measurableSet_Icc

lemma μI_univ : μI Set.univ = 1 := by
  simp [μI, Iset, Real.volume_Icc]

lemma μI_Iset : μI Iset = 1 := by
  simp [μI, Iset, Real.volume_Icc]

lemma μI_singleton (x : ℝ) : μI {x} = 0 := by
  rw [μI, Measure.restrict_apply (measurableSet_singleton x)]
  exact measure_mono_null Set.inter_subset_left (by simp)

lemma μI_pair (a b : ℝ) : μI ({a, b} : Set ℝ) = 0 := by
  have heq : ({a, b} : Set ℝ) = {a} ∪ {b} := by ext x; simp [or_comm]
  rw [heq]
  exact le_antisymm ((measure_union_le {a} {b}).trans (by simp [μI_singleton])) bot_le

instance instIsFiniteMeasureμI : IsFiniteMeasure μI :=
  ⟨by rw [μI_univ]; exact ENNReal.one_lt_top⟩

instance instIsFiniteMeasureμΩ : IsFiniteMeasure μΩ := by
  unfold μΩ; infer_instance

lemma μΩ_univ : μΩ Set.univ = 1 := by
  rw [μΩ, ← Set.univ_prod_univ, Measure.prod_prod, μI_univ, mul_one]

lemma ae_mem_Iset : ∀ᵐ x ∂μI, x ∈ Iset :=
  ae_restrict_mem measurableSet_Iset

lemma measurable_Ks (s : ℝ) : Measurable (Ks s) := by
  unfold Ks
  refine Measurable.ite ?_ measurable_const ?_
  · exact (isClosed_eq continuous_fst continuous_snd).measurableSet
  · exact ENNReal.measurable_ofReal.comp
      (((continuous_fst.sub continuous_snd).abs.measurable).pow_const _)

lemma Ks_symm (s : ℝ) (p : ℝ × ℝ) : Ks s p.swap = Ks s p := by
  unfold Ks
  simp only [Prod.fst_swap, Prod.snd_swap]
  by_cases h : p.2 = p.1
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h), abs_sub_comm]

lemma μΩ_diag_eq_zero : μΩ {p : ℝ × ℝ | p.1 = p.2} = 0 := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  rw [μΩ, Measure.prod_apply hmeas]
  have hzero : ∀ x : ℝ, μI (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0 := by
    intro x
    have heq : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} := by
      ext y; simp [eq_comm]
    rw [heq]
    exact μI_singleton x
  simp_rw [hzero]
  simp

lemma ae_ne_diag_μΩ : ∀ᵐ p : ℝ × ℝ ∂μΩ, p.1 ≠ p.2 := by
  rw [ae_iff]
  simpa using μΩ_diag_eq_zero

lemma Ks_pos_of_ne {s : ℝ} {p : ℝ × ℝ} (h : p.1 ≠ p.2) : 0 < Ks s p := by
  unfold Ks
  rw [if_neg h]
  exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr h)) _)

lemma ae_Ks_ne_zero (s : ℝ) : ∀ᵐ p ∂μΩ, Ks s p ≠ 0 := by
  filter_upwards [ae_ne_diag_μΩ] with p hp
  exact (Ks_pos_of_ne hp).ne'

lemma sigmaFinite_μ₂ (s : ℝ) (hs : 0 < s) : SigmaFinite (μ₂ s) := by
  refine ⟨⟨{
    set := fun n =>
      if n = 0 then {p : ℝ × ℝ | p.1 = p.2}
      else {p : ℝ × ℝ | (1 : ℝ) / (n : ℝ) ≤ |p.1 - p.2|}
    set_mem := fun _ => trivial
    finite := fun n => by
      by_cases hn : n = 0
      · subst hn
        simp only [if_true]
        rw [μ₂, withDensity_apply _ (isClosed_eq continuous_fst continuous_snd).measurableSet]
        rw [setLIntegral_measure_zero _ _ μΩ_diag_eq_zero]
        exact ENNReal.zero_lt_top
      · simp only [hn, if_false]
        have hmeas : MeasurableSet {p : ℝ × ℝ | (1 : ℝ) / (n : ℝ) ≤ |p.1 - p.2|} :=
          measurableSet_le measurable_const (continuous_fst.sub continuous_snd).abs.measurable
        rw [μ₂, withDensity_apply _ hmeas]
        have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
        have hbound : ∀ p ∈ {p : ℝ × ℝ | (1 : ℝ) / (n : ℝ) ≤ |p.1 - p.2|},
            Ks s p ≤ ENNReal.ofReal ((n : ℝ) ^ (1 + 2 * s)) := by
          intro p hp
          have habs : (1 : ℝ) / (n : ℝ) ≤ |p.1 - p.2| := hp
          have hpos : 0 < |p.1 - p.2| := lt_of_lt_of_le (by positivity) habs
          have hne : p.1 ≠ p.2 := sub_ne_zero.mp (abs_pos.mp hpos)
          unfold Ks
          rw [if_neg hne]
          apply ENNReal.ofReal_le_ofReal
          have hexp : 0 ≤ 1 + 2 * s := by linarith
          calc
            |p.1 - p.2| ^ (-(1 + 2 * s))
                = (|p.1 - p.2|⁻¹) ^ (1 + 2 * s) := by
                  rw [Real.rpow_neg hpos.le, Real.inv_rpow hpos.le]
            _ ≤ (n : ℝ) ^ (1 + 2 * s) := by
                  apply Real.rpow_le_rpow (inv_nonneg.mpr hpos.le) _ hexp
                  rw [inv_le_iff_one_le_mul₀ hpos]
                  have := (div_le_iff₀ hnpos).mp habs
                  linarith
        calc
          ∫⁻ p in {p : ℝ × ℝ | (1 : ℝ) / (n : ℝ) ≤ |p.1 - p.2|}, Ks s p ∂μΩ
              ≤ ∫⁻ _ in {p : ℝ × ℝ | (1 : ℝ) / (n : ℝ) ≤ |p.1 - p.2|},
                  ENNReal.ofReal ((n : ℝ) ^ (1 + 2 * s)) ∂μΩ :=
                setLIntegral_mono' hmeas hbound
          _ ≤ ENNReal.ofReal ((n : ℝ) ^ (1 + 2 * s)) * μΩ Set.univ := by
                rw [setLIntegral_const]
                exact mul_le_mul_of_nonneg_left (measure_mono (Set.subset_univ _)) bot_le
          _ = ENNReal.ofReal ((n : ℝ) ^ (1 + 2 * s)) := by rw [μΩ_univ, mul_one]
          _ < ⊤ := ENNReal.ofReal_lt_top
    spanning := by
      ext p
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      by_cases h : p.1 = p.2
      · exact ⟨0, by simp [h]⟩
      · have hpos : 0 < |p.1 - p.2| := abs_pos.mpr (sub_ne_zero.mpr h)
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
        refine ⟨k + 1, ?_⟩
        simp only [Nat.succ_ne_zero, if_false]
        change (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ |p.1 - p.2|
        rw [Nat.cast_add, Nat.cast_one]
        exact le_of_lt hk
  }⟩⟩

lemma μ₂_absolutelyContinuous_μΩ (s : ℝ) : μ₂ s ≪ μΩ :=
  withDensity_absolutelyContinuous μΩ (Ks s)

lemma μΩ_absolutelyContinuous_μ₂ (s : ℝ) : μΩ ≪ μ₂ s := by
  refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
  rw [μ₂, withDensity_apply _ hA] at hA0
  have hae : ∀ᵐ p ∂(μΩ.restrict A), Ks s p = 0 :=
    (lintegral_eq_zero_iff (measurable_Ks s)).mp hA0
  have hae2 : ∀ᵐ p ∂(μΩ.restrict A), Ks s p ≠ 0 :=
    ae_restrict_of_ae (ae_Ks_ne_zero s)
  have hfalse : ∀ᵐ _ ∂(μΩ.restrict A), False := by
    filter_upwards [hae, hae2] with p h1 h2
    exact h2 h1
  rw [ae_iff] at hfalse
  have : μΩ.restrict A Set.univ = 0 := by simpa using hfalse
  simpa [Measure.restrict_apply_univ] using this

lemma ae_μ₂_iff_ae_μΩ {s : ℝ} {P : ℝ × ℝ → Prop} :
    (∀ᵐ p ∂(μ₂ s), P p) ↔ (∀ᵐ p ∂μΩ, P p) :=
  ⟨fun h => (μΩ_absolutelyContinuous_μ₂ s).ae_le h,
   fun h => (μ₂_absolutelyContinuous_μΩ s).ae_le h⟩

/-! Section 2: L2 norm helpers and 1D power integral bounds -/

lemma lintegral_ofReal_sq_eq_enorm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ) :
    ∫⁻ a, ENNReal.ofReal (f a ^ 2) ∂μ = ∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ := by
  apply lintegral_congr
  intro a
  rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

lemma Lp_norm_sq_eq_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = (∫⁻ a, ENNReal.ofReal ((f : α → ℝ) a ^ 2) ∂μ).toReal := by
  have h1 : ‖f‖ = (eLpNorm (f : α → ℝ) 2 μ).toReal := Lp.norm_def f
  have h2 : eLpNorm (f : α → ℝ) 2 μ =
      (∫⁻ a, ENNReal.ofReal ((f : α → ℝ) a ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, lintegral_ofReal_sq_eq_enorm_sq]
  rw [h1, h2, ← ENNReal.toReal_rpow, ← Real.rpow_two, ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num

lemma Lp_ofReal_norm_sq_eq_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) :
    ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ a, ENNReal.ofReal ((f : α → ℝ) a ^ 2) ∂μ := by
  have hlt : ∫⁻ a, ENNReal.ofReal ((f : α → ℝ) a ^ 2) ∂μ < ⊤ := by
    have hfin := Lp.eLpNorm_lt_top f
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at hfin
    simp only [ENNReal.toReal_ofNat] at hfin
    rw [lintegral_ofReal_sq_eq_enorm_sq]
    by_contra htop
    have heq : ∫⁻ a, ‖(f : α → ℝ) a‖ₑ ^ (2 : ℝ) ∂μ = ⊤ := eq_top_iff.mpr (not_lt.mp htop)
    rw [heq, ENNReal.top_rpow_of_pos (by positivity)] at hfin
    exact lt_irrefl ⊤ hfin
  rw [Lp_norm_sq_eq_lintegral, ENNReal.ofReal_toReal hlt.ne]

lemma memLp_two_of_lintegral_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfin : ∫⁻ a, ENNReal.ofReal (f a ^ 2) ∂μ < ⊤) :
    MemLp f 2 μ := by
  refine ⟨hf, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ← lintegral_ofReal_sq_eq_enorm_sq]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hfin.ne

lemma Lp_coeFn_finset_sum {ι α : Type*} [MeasurableSpace α] {μ : Measure α}
    (S : Finset ι) (f : ι → Lp ℝ 2 μ) :
    ((∑ i ∈ S, f i : Lp ℝ 2 μ) : α → ℝ) =ᵐ[μ] fun x => ∑ i ∈ S, (f i : α → ℝ) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    simpa using hx
  | insert a s ha ih =>
    have h1 := Lp.coeFn_add (f a) (∑ i ∈ s, f i)
    rw [Finset.sum_insert ha]
    filter_upwards [h1, ih] with x hx1 hxih
    simp only [Pi.add_apply] at hx1
    rw [hx1, hxih, Finset.sum_insert ha]

lemma lintegral_Ioo_sub_rpow_le {s a x : ℝ} (hs : 0 < s) (ha0 : 0 ≤ a) (hax : a < x) :
    ∫⁻ y in Set.Ioo 0 a, ENNReal.ofReal ((x - y) ^ (-(1 + 2 * s))) ≤
      ENNReal.ofReal ((x - a) ^ (-2 * s) / (2 * s)) := by
  by_cases ha : a = 0
  · subst ha
    simp only [Set.Ioo_self, setLIntegral_empty]
    exact bot_le
  · let F : ℝ → ℝ := fun y => (x - y) ^ (-2 * s) / (2 * s)
    let g : ℝ → ℝ := fun y => (x - y) ^ (-(1 + 2 * s))
    have hderiv : ∀ y ∈ Set.uIcc 0 a, HasDerivAt F (g y) y := by
      intro y hy
      rw [Set.uIcc_of_le ha0] at hy
      have hpos : 0 < x - y := by linarith [hy.2]
      have h1 : HasDerivAt (fun t => x - t) (-1) y := (hasDerivAt_id y).const_sub x
      have h2 := h1.rpow_const (p := -2 * s) (Or.inl hpos.ne')
      have h3 := h2.div_const (2 * s)
      have heq : -1 * (-2 * s) * (x - y) ^ (-2 * s - 1) / (2 * s) = g y := by
        dsimp only [g]
        have h2s : (2 * s : ℝ) ≠ 0 := by linarith
        have hexp : -2 * s - 1 = -(1 + 2 * s) := by ring
        rw [hexp]
        field_simp [h2s]
      rw [← heq]
      exact h3
    have hcont : ContinuousOn g (Set.uIcc 0 a) := by
      rw [Set.uIcc_of_le ha0]
      intro y hy
      have hpos : 0 < x - y := by linarith [hy.2]
      exact ((continuous_const.sub continuous_id).continuousAt.rpow_const
        (Or.inl hpos.ne')).continuousWithinAt
    have hint : IntervalIntegrable g volume 0 a := hcont.intervalIntegrable
    have hftc : ∫ y in (0 : ℝ)..a, g y = F a - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hnonneg' : ∀ y ∈ Set.Ioc (0 : ℝ) a, 0 ≤ g y := fun y hy =>
      Real.rpow_nonneg (by linarith [hy.2]) _
    have hint_Ioc : IntegrableOn g (Set.Ioc 0 a) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ha0).mp hint
    have hlin : ∫⁻ y in Set.Ioo (0 : ℝ) a, ENNReal.ofReal (g y) =
        ENNReal.ofReal (∫ y in (0 : ℝ)..a, g y) := by
      rw [restrict_Ioo_eq_restrict_Ioc,
        ← ofReal_integral_eq_lintegral_ofReal hint_Ioc
          (ae_restrict_of_forall_mem measurableSet_Ioc hnonneg'),
        ← intervalIntegral.integral_of_le ha0]
    rw [hlin, hftc]
    apply ENNReal.ofReal_le_ofReal
    have hF0 : 0 ≤ F 0 := by
      dsimp only [F]
      have hx0 : 0 ≤ x - 0 := by linarith
      exact div_nonneg (Real.rpow_nonneg hx0 _) (by linarith)
    linarith

lemma lintegral_Ioo_rsub_rpow_le {s b x : ℝ} (hs : 0 < s) (hxb : x < b) (hb1 : b ≤ 1) :
    ∫⁻ y in Set.Ioo b 1, ENNReal.ofReal ((y - x) ^ (-(1 + 2 * s))) ≤
      ENNReal.ofReal ((b - x) ^ (-2 * s) / (2 * s)) := by
  by_cases hb : b = 1
  · subst hb
    simp only [Set.Ioo_self, setLIntegral_empty]
    exact bot_le
  · let F : ℝ → ℝ := fun y => -((y - x) ^ (-2 * s) / (2 * s))
    let g : ℝ → ℝ := fun y => (y - x) ^ (-(1 + 2 * s))
    have hderiv : ∀ y ∈ Set.uIcc b 1, HasDerivAt F (g y) y := by
      intro y hy
      rw [Set.uIcc_of_le hb1] at hy
      have hpos : 0 < y - x := by linarith [hy.1]
      have h1 : HasDerivAt (fun t => t - x) 1 y := (hasDerivAt_id y).sub_const x
      have h2 := h1.rpow_const (p := -2 * s) (Or.inl hpos.ne')
      have h3 : HasDerivAt F (-(1 * (-2 * s) * (y - x) ^ (-2 * s - 1) / (2 * s))) y :=
        (h2.div_const (2 * s)).neg
      have heq : -(1 * (-2 * s) * (y - x) ^ (-2 * s - 1) / (2 * s)) = g y := by
        dsimp only [g]
        have h2s : (2 * s : ℝ) ≠ 0 := by linarith
        have hexp : -2 * s - 1 = -(1 + 2 * s) := by ring
        rw [hexp]
        field_simp [h2s]
      rw [← heq]
      exact h3
    have hcont : ContinuousOn g (Set.uIcc b 1) := by
      rw [Set.uIcc_of_le hb1]
      intro y hy
      have hpos : 0 < y - x := by linarith [hy.1]
      exact ((continuous_id.sub continuous_const).continuousAt.rpow_const
        (Or.inl hpos.ne')).continuousWithinAt
    have hint : IntervalIntegrable g volume b 1 := hcont.intervalIntegrable
    have hftc : ∫ y in b..(1 : ℝ), g y = F 1 - F b :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hnonneg' : ∀ y ∈ Set.Ioc b (1 : ℝ), 0 ≤ g y := fun y hy =>
      Real.rpow_nonneg (by linarith [hy.1]) _
    have hint_Ioc : IntegrableOn g (Set.Ioc b 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb1).mp hint
    have hlin : ∫⁻ y in Set.Ioo b (1 : ℝ), ENNReal.ofReal (g y) =
        ENNReal.ofReal (∫ y in b..(1 : ℝ), g y) := by
      rw [restrict_Ioo_eq_restrict_Ioc,
        ← ofReal_integral_eq_lintegral_ofReal hint_Ioc
          (ae_restrict_of_forall_mem measurableSet_Ioc hnonneg'),
        ← intervalIntegral.integral_of_le hb1]
    rw [hlin, hftc]
    apply ENNReal.ofReal_le_ofReal
    have hF1 : 0 ≤ (1 - x) ^ (-2 * s) / (2 * s) :=
      div_nonneg (Real.rpow_nonneg (by linarith) _) (by linarith)
    dsimp only [F]
    linarith

lemma lintegral_Ioo_left_rpow_eq {s a b : ℝ} (hs : s < 1 / 2) (hab : a ≤ b) :
    ∫⁻ x in Set.Ioo a b, ENNReal.ofReal ((x - a) ^ (-2 * s)) =
      ENNReal.ofReal ((b - a) ^ (1 - 2 * s) / (1 - 2 * s)) := by
  have hr : (-1 : ℝ) < -2 * s := by linarith
  have hint0 : IntervalIntegrable (fun t : ℝ => t ^ (-2 * s)) volume 0 (b - a) :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have hint : IntervalIntegrable (fun x : ℝ => (x - a) ^ (-2 * s)) volume a b := by
    have hcomp := hint0.comp_sub_right a
    simpa [sub_self] using hcomp
  have hval : ∫ x in a..b, (x - a) ^ (-2 * s) = (b - a) ^ (1 - 2 * s) / (1 - 2 * s) := by
    rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => t ^ (-2 * s)) a, sub_self]
    rw [integral_rpow (Or.inl hr)]
    have hexp : -2 * s + 1 = 1 - 2 * s := by ring
    rw [hexp, Real.zero_rpow (by linarith), sub_zero]
  have hint_Ioc : IntegrableOn (fun x : ℝ => (x - a) ^ (-2 * s)) (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint
  have hnonneg : ∀ x ∈ Set.Ioc a b, 0 ≤ (x - a) ^ (-2 * s) := fun x hx =>
    Real.rpow_nonneg (by linarith [hx.1]) _
  rw [restrict_Ioo_eq_restrict_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hint_Ioc
      (ae_restrict_of_forall_mem measurableSet_Ioc hnonneg),
    ← intervalIntegral.integral_of_le hab, hval]

lemma lintegral_Ioo_right_rpow_eq {s a b : ℝ} (hs : s < 1 / 2) (hab : a ≤ b) :
    ∫⁻ x in Set.Ioo a b, ENNReal.ofReal ((b - x) ^ (-2 * s)) =
      ENNReal.ofReal ((b - a) ^ (1 - 2 * s) / (1 - 2 * s)) := by
  have hr : (-1 : ℝ) < -2 * s := by linarith
  have hint0 : IntervalIntegrable (fun t : ℝ => t ^ (-2 * s)) volume 0 (b - a) :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have hint : IntervalIntegrable (fun x : ℝ => (b - x) ^ (-2 * s)) volume a b := by
    have hcomp := hint0.comp_sub_left b
    simpa [sub_self] using hcomp.symm
  have hval : ∫ x in a..b, (b - x) ^ (-2 * s) = (b - a) ^ (1 - 2 * s) / (1 - 2 * s) := by
    rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ (-2 * s)) b, sub_self]
    rw [integral_rpow (Or.inl hr)]
    have hexp : -2 * s + 1 = 1 - 2 * s := by ring
    rw [hexp, Real.zero_rpow (by linarith), sub_zero]
  have hint_Ioc : IntegrableOn (fun x : ℝ => (b - x) ^ (-2 * s)) (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint
  have hnonneg : ∀ x ∈ Set.Ioc a b, 0 ≤ (b - x) ^ (-2 * s) := fun x hx =>
    Real.rpow_nonneg (by linarith [hx.2]) _
  rw [restrict_Ioo_eq_restrict_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hint_Ioc
      (ae_restrict_of_forall_mem measurableSet_Ioc hnonneg),
    ← intervalIntegral.integral_of_le hab, hval]

/-! Section 3: Ambient Hilbert space H and linear isometric equivalence to Hilbert -/

abbrev AmbSpace (s : ℝ) := WithLp 2 (Lp ℝ 2 μI × Lp ℝ 2 (μ₂ s))

def Hsub (s : ℝ) : Submodule ℝ (AmbSpace s) where
  carrier := { x | ∀ᵐ p ∂μΩ, (x.snd : ℝ × ℝ → ℝ) p = (x.fst : ℝ → ℝ) p.1 - (x.fst : ℝ → ℝ) p.2 }
  zero_mem' := by
    have h1 : ((0 : Lp ℝ 2 μI) : ℝ → ℝ) =ᵐ[μI] 0 := Lp.coeFn_zero ℝ 2 μI
    have h2 : ((0 : Lp ℝ 2 (μ₂ s)) : ℝ × ℝ → ℝ) =ᵐ[μ₂ s] 0 := Lp.coeFn_zero ℝ 2 (μ₂ s)
    have h2' : ((0 : Lp ℝ 2 (μ₂ s)) : ℝ × ℝ → ℝ) =ᵐ[μΩ] 0 := ae_μ₂_iff_ae_μΩ.mp h2
    have h1a : ∀ᵐ p : ℝ × ℝ ∂μΩ, ((0 : Lp ℝ 2 μI) : ℝ → ℝ) p.1 = 0 :=
      Measure.quasiMeasurePreserving_fst.ae h1
    have h1b : ∀ᵐ p : ℝ × ℝ ∂μΩ, ((0 : Lp ℝ 2 μI) : ℝ → ℝ) p.2 = 0 :=
      Measure.quasiMeasurePreserving_snd.ae h1
    filter_upwards [h2', h1a, h1b] with p hp hpa hpb
    change ((0 : Lp ℝ 2 (μ₂ s)) : ℝ × ℝ → ℝ) p =
      ((0 : Lp ℝ 2 μI) : ℝ → ℝ) p.1 - ((0 : Lp ℝ 2 μI) : ℝ → ℝ) p.2
    simp only [Pi.zero_apply] at hp
    rw [hp, hpa, hpb, sub_zero]
  add_mem' {x y} hx hy := by
    have hf : ((x + y).fst : ℝ → ℝ) =ᵐ[μI] (x.fst : ℝ → ℝ) + (y.fst : ℝ → ℝ) :=
      Lp.coeFn_add x.fst y.fst
    have hF : ((x + y).snd : ℝ × ℝ → ℝ) =ᵐ[μΩ] (x.snd : ℝ × ℝ → ℝ) + (y.snd : ℝ × ℝ → ℝ) :=
      ae_μ₂_iff_ae_μΩ.mp (Lp.coeFn_add x.snd y.snd)
    have hfa := Measure.quasiMeasurePreserving_fst (μ := μI) (ν := μI) |>.ae hf
    have hfb := Measure.quasiMeasurePreserving_snd (μ := μI) (ν := μI) |>.ae hf
    filter_upwards [hx, hy, hF, hfa, hfb] with p hxp hyp hFp hfap hfbp
    simp only [Pi.add_apply] at hFp hfap hfbp
    rw [hFp, hxp, hyp, hfap, hfbp]
    ring
  smul_mem' c {x} hx := by
    have hf : ((c • x).fst : ℝ → ℝ) =ᵐ[μI] c • (x.fst : ℝ → ℝ) :=
      Lp.coeFn_smul c x.fst
    have hF : ((c • x).snd : ℝ × ℝ → ℝ) =ᵐ[μΩ] c • (x.snd : ℝ × ℝ → ℝ) :=
      ae_μ₂_iff_ae_μΩ.mp (Lp.coeFn_smul c x.snd)
    have hfa := Measure.quasiMeasurePreserving_fst (μ := μI) (ν := μI) |>.ae hf
    have hfb := Measure.quasiMeasurePreserving_snd (μ := μI) (ν := μI) |>.ae hf
    filter_upwards [hx, hF, hfa, hfb] with p hxp hFp hfap hfbp
    simp only [Pi.smul_apply, smul_eq_mul] at hFp hfap hfbp
    rw [hFp, hxp, hfap, hfbp]
    ring

lemma isClosed_Hsub (s : ℝ) : IsClosed (Hsub s : Set (AmbSpace s)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u x hu hlim
  have hlim1 : Tendsto (fun n => (u n).fst) atTop (𝓝 x.fst) :=
    (WithLp.continuous_fst 2 (Lp ℝ 2 μI) (Lp ℝ 2 (μ₂ s))).continuousAt.tendsto.comp hlim
  obtain ⟨φ, hφ_mono, hφ_ae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim1).exists_seq_tendsto_ae
  have hlim2 : Tendsto (fun k => (u (φ k)).snd) atTop (𝓝 x.snd) :=
    ((WithLp.continuous_snd 2 (Lp ℝ 2 μI) (Lp ℝ 2 (μ₂ s))).continuousAt.tendsto.comp hlim).comp
      hφ_mono.tendsto_atTop
  obtain ⟨ψ, hψ_mono, hψ_ae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim2).exists_seq_tendsto_ae
  have hψ_ae' : ∀ᵐ p ∂μΩ, Tendsto (fun m => ((u (φ (ψ m))).snd : ℝ × ℝ → ℝ) p) atTop
      (𝓝 ((x.snd : ℝ × ℝ → ℝ) p)) := ae_μ₂_iff_ae_μΩ.mp hψ_ae
  have h1a : ∀ᵐ p : ℝ × ℝ ∂μΩ, Tendsto (fun k => ((u (φ k)).fst : ℝ → ℝ) p.1) atTop
      (𝓝 ((x.fst : ℝ → ℝ) p.1)) :=
    Measure.quasiMeasurePreserving_fst.ae hφ_ae
  have h1b : ∀ᵐ p : ℝ × ℝ ∂μΩ, Tendsto (fun k => ((u (φ k)).fst : ℝ → ℝ) p.2) atTop
      (𝓝 ((x.fst : ℝ → ℝ) p.2)) :=
    Measure.quasiMeasurePreserving_snd.ae hφ_ae
  have hmem : ∀ᵐ p ∂μΩ, ∀ m, ((u (φ (ψ m))).snd : ℝ × ℝ → ℝ) p =
      ((u (φ (ψ m))).fst : ℝ → ℝ) p.1 - ((u (φ (ψ m))).fst : ℝ → ℝ) p.2 :=
    ae_all_iff.mpr (fun m => hu (φ (ψ m)))
  filter_upwards [hψ_ae', h1a, h1b, hmem] with p h2p h1ap h1bp hmp
  have hdiff : Tendsto (fun m => ((u (φ (ψ m))).fst : ℝ → ℝ) p.1 - ((u (φ (ψ m))).fst : ℝ → ℝ) p.2)
      atTop (𝓝 (((x.fst : ℝ → ℝ) p.1) - ((x.fst : ℝ → ℝ) p.2))) :=
    (h1ap.comp hψ_mono.tendsto_atTop).sub (h1bp.comp hψ_mono.tendsto_atTop)
  have heq : (fun m => ((u (φ (ψ m))).snd : ℝ × ℝ → ℝ) p) =
      (fun m => ((u (φ (ψ m))).fst : ℝ → ℝ) p.1 - ((u (φ (ψ m))).fst : ℝ → ℝ) p.2) :=
    funext hmp
  rw [heq] at h2p
  exact tendsto_nhds_unique h2p hdiff

lemma completeSpace_Hsub (s : ℝ) : CompleteSpace (Hsub s) :=
  (isClosed_Hsub s).completeSpace_coe

lemma secondCountable_Hsub (s : ℝ) (hs : 0 < s) : SecondCountableTopology (Hsub s) := by
  have : SigmaFinite (μ₂ s) := sigmaFinite_μ₂ s hs
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℝ 2 μI) := inferInstance
  have : SecondCountableTopology (Lp ℝ 2 (μ₂ s)) := inferInstance
  have : SecondCountableTopology (Lp ℝ 2 μI × Lp ℝ 2 (μ₂ s)) := inferInstance
  have : SecondCountableTopology (AmbSpace s) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 μI) (Lp ℝ 2 (μ₂ s))).toHomeomorph.secondCountableTopology
  infer_instance

lemma Hsub_fst_finset_sum {ι : Type*} {s : ℝ} (S : Finset ι) (v : ι → Hsub s) :
    ((∑ i ∈ S, v i : Hsub s).1.fst : Lp ℝ 2 μI) = ∑ i ∈ S, (v i).1.fst := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    change (v a).1.fst + (∑ i ∈ t, v i).1.fst = _
    rw [ih]

lemma Hsub_norm_sq_eq {s : ℝ} (g : Hsub s) {f : ℝ → ℝ} (hf : (g.1.fst : ℝ → ℝ) =ᵐ[μI] f) :
    ‖g‖ ^ 2 = (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μI).toReal +
      (∫⁻ p, ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * Ks s p ∂μΩ).toReal := by
  have hnorm : ‖g‖ ^ 2 = ‖g.1.fst‖ ^ 2 + ‖g.1.snd‖ ^ 2 := by
    change ‖g.1‖ ^ 2 = _
    exact WithLp.prod_norm_sq_eq_of_L2 g.1
  rw [hnorm, Lp_norm_sq_eq_lintegral g.1.fst, Lp_norm_sq_eq_lintegral g.1.snd]
  congr 1
  · congr 1
    apply lintegral_congr_ae
    filter_upwards [hf] with x hx
    rw [hx]
  · congr 1
    have hF : (g.1.snd : ℝ × ℝ → ℝ) =ᵐ[μΩ] fun p => f p.1 - f p.2 := by
      have h1 := Measure.quasiMeasurePreserving_fst (μ := μI) (ν := μI) |>.ae hf
      have h2 := Measure.quasiMeasurePreserving_snd (μ := μI) (ν := μI) |>.ae hf
      filter_upwards [g.2, h1, h2] with p hgp h1p h2p
      rw [hgp, h1p, h2p]
    have haesm : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((g.1.snd : ℝ × ℝ → ℝ) p ^ 2)) μΩ :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (((Lp.aestronglyMeasurable g.1.snd).aemeasurable.mono_ac (μΩ_absolutelyContinuous_μ₂ s)).pow_const 2)
    change ∫⁻ p, ENNReal.ofReal ((g.1.snd : ℝ × ℝ → ℝ) p ^ 2) ∂(μΩ.withDensity (Ks s)) = _
    rw [lintegral_withDensity_eq_lintegral_mul₀ (measurable_Ks s).aemeasurable haesm]
    apply lintegral_congr_ae
    filter_upwards [hF] with p hp
    simp only [Pi.mul_apply]
    rw [hp, mul_comm]

noncomputable def mkH {s : ℝ} (f : ℝ → ℝ)
    (hf_meas : Measurable f)
    (hf_fin : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μI < ⊤)
    (hF_fin : ∫⁻ p, ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * Ks s p ∂μΩ < ⊤) :
    Hsub s :=
  let hf_lp : MemLp f 2 μI := memLp_two_of_lintegral_lt_top hf_meas.aestronglyMeasurable hf_fin
  let hF_meas : Measurable (fun p : ℝ × ℝ => f p.1 - f p.2) :=
    (hf_meas.comp measurable_fst).sub (hf_meas.comp measurable_snd)
  let hF_lp : MemLp (fun p : ℝ × ℝ => f p.1 - f p.2) 2 (μ₂ s) := by
    apply memLp_two_of_lintegral_lt_top hF_meas.aestronglyMeasurable
    have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal ((f p.1 - f p.2) ^ 2)) :=
      ENNReal.measurable_ofReal.comp (hF_meas.pow_const 2)
    change ∫⁻ p, ENNReal.ofReal ((f p.1 - f p.2) ^ 2) ∂(μΩ.withDensity (Ks s)) < ⊤
    rw [lintegral_withDensity_eq_lintegral_mul μΩ (measurable_Ks s) hm]
    simpa [mul_comm] using hF_fin
  ⟨WithLp.toLp 2 (hf_lp.toLp f, hF_lp.toLp (fun p => f p.1 - f p.2)), by
    have h1 : ((hf_lp.toLp f : Lp ℝ 2 μI) : ℝ → ℝ) =ᵐ[μI] f := hf_lp.coeFn_toLp
    have h2 : ((hF_lp.toLp (fun p => f p.1 - f p.2) : Lp ℝ 2 (μ₂ s)) : ℝ × ℝ → ℝ) =ᵐ[μΩ]
        (fun p => f p.1 - f p.2) := ae_μ₂_iff_ae_μΩ.mp hF_lp.coeFn_toLp
    have h1a := Measure.quasiMeasurePreserving_fst (μ := μI) (ν := μI) |>.ae h1
    have h1b := Measure.quasiMeasurePreserving_snd (μ := μI) (ν := μI) |>.ae h1
    filter_upwards [h2, h1a, h1b] with p h2p h1ap h1bp
    change ((hF_lp.toLp (fun p => f p.1 - f p.2) : Lp ℝ 2 (μ₂ s)) : ℝ × ℝ → ℝ) p =
      ((hf_lp.toLp f : Lp ℝ 2 μI) : ℝ → ℝ) p.1 - ((hf_lp.toLp f : Lp ℝ 2 μI) : ℝ → ℝ) p.2
    rw [h2p, h1ap, h1bp]⟩

lemma mkH_fst_ae {s : ℝ} (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_fin : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μI < ⊤)
    (hF_fin : ∫⁻ p, ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * Ks s p ∂μΩ < ⊤) :
    ((mkH f hf_meas hf_fin hF_fin).1.fst : ℝ → ℝ) =ᵐ[μI] f :=
  (memLp_two_of_lintegral_lt_top hf_meas.aestronglyMeasurable hf_fin).coeFn_toLp

lemma indicator_Icc_energy_lt_top {s a b : ℝ} (hs0 : 0 < s) (hs : s < 1 / 2)
    (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    ∫⁻ p, ENNReal.ofReal
      (((Set.Icc a b).indicator (1 : ℝ → ℝ) p.1 - (Set.Icc a b).indicator (1 : ℝ → ℝ) p.2) ^ 2) *
        Ks s p ∂μΩ < ⊤ := by
  let χ : ℝ → ℝ := (Set.Icc a b).indicator (1 : ℝ → ℝ)
  let S₁ : Set (ℝ × ℝ) := Set.Icc a b ×ˢ (Iset \ Set.Icc a b)
  let S₂ : Set (ℝ × ℝ) := (Iset \ Set.Icc a b) ×ˢ Set.Icc a b
  have hS₁ : MeasurableSet S₁ := measurableSet_Icc.prod (measurableSet_Iset.diff measurableSet_Icc)
  have hS₂ : MeasurableSet S₂ := (measurableSet_Iset.diff measurableSet_Icc).prod measurableSet_Icc
  have hsplit : ∀ p : ℝ × ℝ,
      ENNReal.ofReal ((χ p.1 - χ p.2) ^ 2) * Ks s p ≤
        S₁.indicator (Ks s) p + S₂.indicator (Ks s) p +
        (Iset ×ˢ Iset)ᶜ.indicator (fun _ => ⊤) p := by
    intro p
    by_cases hpI : p ∈ Iset ×ˢ Iset
    · simp only [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hpI), add_zero]
      by_cases h1 : p.1 ∈ Set.Icc a b <;> by_cases h2 : p.2 ∈ Set.Icc a b
      · simp [χ, h1, h2]
      · have hmem : p ∈ S₁ := ⟨h1, hpI.2, h2⟩
        simp [χ, h1, h2, hmem]
      · have hmem : p ∈ S₂ := ⟨⟨hpI.1, h1⟩, h2⟩
        simp [χ, h1, h2, hmem]
      · simp [χ, h1, h2]
    · simp [hpI]
  have hcompl_zero : ∫⁻ p, (Iset ×ˢ Iset)ᶜ.indicator (fun _ => (⊤ : ℝ≥0∞)) p ∂μΩ = 0 := by
    rw [lintegral_indicator (measurableSet_Iset.prod measurableSet_Iset).compl]
    have hμ0 : μΩ (Iset ×ˢ Iset)ᶜ = 0 := by
      have hprod : μΩ (Iset ×ˢ Iset) = 1 := by rw [μΩ, Measure.prod_prod, μI_Iset, mul_one]
      rw [measure_compl (measurableSet_Iset.prod measurableSet_Iset) (measure_ne_top _ _),
        μΩ_univ, hprod, tsub_self]
    rw [setLIntegral_measure_zero _ _ hμ0]
  have hsymm : ∫⁻ p, S₂.indicator (Ks s) p ∂μΩ = ∫⁻ p, S₁.indicator (Ks s) p ∂μΩ := by
    have hmp : MeasurePreserving Prod.swap μΩ μΩ := Measure.measurePreserving_swap
    rw [← hmp.lintegral_comp ((measurable_Ks s).indicator hS₁)]
    apply lintegral_congr
    intro p
    by_cases h : p.swap ∈ S₁
    · have h' : p ∈ S₂ := ⟨h.2, h.1⟩
      simp [h, h', Ks_symm]
    · have h' : p ∉ S₂ := fun hp => h ⟨hp.2, hp.1⟩
      simp [h, h']
  have hcross : ∫⁻ p, S₁.indicator (Ks s) p ∂μΩ < ⊤ := by
    rw [μΩ, lintegral_prod _ ((measurable_Ks s).indicator hS₁).aemeasurable]
    have houter : ∫⁻ x, (∫⁻ y, S₁.indicator (Ks s) (x, y) ∂μI) ∂μI ≤
        ∫⁻ x in Set.Ioo a b,
          (ENNReal.ofReal ((x - a) ^ (-2 * s) / (2 * s)) +
            ENNReal.ofReal ((b - x) ^ (-2 * s) / (2 * s))) := by
      have hae_ab : ∀ᵐ x ∂μI, x ≠ a ∧ x ≠ b := by
        rw [ae_iff]
        have heq : {x : ℝ | ¬ (x ≠ a ∧ x ≠ b)} = ({a, b} : Set ℝ) := by
          ext x
          simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto
        rw [heq]
        exact μI_pair a b
      have hae_eq : (fun x => ∫⁻ y, S₁.indicator (Ks s) (x, y) ∂μI) =ᵐ[μI]
          (Set.Ioo a b).indicator (fun x => ∫⁻ y, S₁.indicator (Ks s) (x, y) ∂μI) := by
        filter_upwards [hae_ab] with x hx
        by_cases hxoo : x ∈ Set.Ioo a b
        · simp [hxoo]
        · have hxcc : x ∉ Set.Icc a b := by
            intro hcc
            exact hxoo ⟨lt_of_le_of_ne hcc.1 (Ne.symm hx.1), lt_of_le_of_ne hcc.2 hx.2⟩
          simp [hxoo, S₁, hxcc]
      rw [lintegral_congr_ae hae_eq, lintegral_indicator measurableSet_Ioo]
      have hsubI : Set.Ioo a b ⊆ Iset := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hres : μI.restrict (Set.Ioo a b) = volume.restrict (Set.Ioo a b) := by
        rw [μI, Measure.restrict_restrict measurableSet_Ioo, Set.inter_eq_left.mpr hsubI]
      rw [hres]
      apply setLIntegral_mono' measurableSet_Ioo
      intro x hx
      have hsub : Iset \ Set.Icc a b ⊆ Set.Ioo 0 a ∪ Set.Ioo b 1 ∪ {0, 1} := by
        intro y hy
        rcases hy with ⟨⟨hy0, hy1⟩, hyn⟩
        by_cases hya : y < a
        · by_cases hyz : y = 0
          · exact Or.inr (Or.inl hyz)
          · exact Or.inl (Or.inl ⟨lt_of_le_of_ne hy0 (Ne.symm hyz), hya⟩)
        · have hyb : b < y := by
            by_contra hle; exact hyn ⟨not_lt.mp hya, not_lt.mp hle⟩
          by_cases hyo : y = 1
          · exact Or.inr (Or.inr hyo)
          · exact Or.inl (Or.inr ⟨hyb, lt_of_le_of_ne hy1 hyo⟩)
      have hinner_eq : ∫⁻ y, S₁.indicator (Ks s) (x, y) ∂μI =
          ∫⁻ y in Iset \ Set.Icc a b, Ks s (x, y) ∂μI := by
        rw [← lintegral_indicator (measurableSet_Iset.diff measurableSet_Icc)]
        apply lintegral_congr
        intro y
        have hxcc : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
        by_cases hy : y ∈ Iset \ Set.Icc a b <;> simp [S₁, hxcc, hy]
      rw [hinner_eq]
      calc
        ∫⁻ y in Iset \ Set.Icc a b, Ks s (x, y) ∂μI
            ≤ ∫⁻ y in Set.Ioo 0 a ∪ Set.Ioo b 1 ∪ {0, 1}, Ks s (x, y) ∂μI :=
              lintegral_mono_set hsub
        _ ≤ (∫⁻ y in Set.Ioo 0 a, Ks s (x, y) ∂μI) + (∫⁻ y in Set.Ioo b 1, Ks s (x, y) ∂μI) +
              (∫⁻ y in ({0, 1} : Set ℝ), Ks s (x, y) ∂μI) := by
              refine le_trans (lintegral_union_le _ _ _) ?_
              exact add_le_add (lintegral_union_le _ _ _) le_rfl
        _ = (∫⁻ y in Set.Ioo 0 a, ENNReal.ofReal ((x - y) ^ (-(1 + 2 * s)))) +
              (∫⁻ y in Set.Ioo b 1, ENNReal.ofReal ((y - x) ^ (-(1 + 2 * s)))) := by
              rw [setLIntegral_measure_zero _ _ (μI_pair 0 1), add_zero]
              have hsub1 : Set.Ioo 0 a ⊆ Iset := fun y hy => ⟨hy.1.le, by linarith [hy.2]⟩
              have hsub2 : Set.Ioo b 1 ⊆ Iset := fun y hy => ⟨by linarith [hy.1], hy.2.le⟩
              congr 1
              · rw [μI, Measure.restrict_restrict measurableSet_Ioo, Set.inter_eq_left.mpr hsub1]
                apply setLIntegral_congr_fun measurableSet_Ioo
                intro y hy
                have hne : x ≠ y := by linarith [hx.1, hy.2]
                dsimp only [Ks]; rw [if_neg hne, abs_of_pos (by linarith [hx.1, hy.2])]
              · rw [μI, Measure.restrict_restrict measurableSet_Ioo, Set.inter_eq_left.mpr hsub2]
                apply setLIntegral_congr_fun measurableSet_Ioo
                intro y hy
                have hne : x ≠ y := by linarith [hx.2, hy.1]
                dsimp only [Ks]
                rw [if_neg hne, abs_sub_comm, abs_of_pos (by linarith [hx.2, hy.1])]
        _ ≤ ENNReal.ofReal ((x - a) ^ (-2 * s) / (2 * s)) +
              ENNReal.ofReal ((b - x) ^ (-2 * s) / (2 * s)) :=
              add_le_add (lintegral_Ioo_sub_rpow_le hs0 ha0 hx.1)
                (lintegral_Ioo_rsub_rpow_le hs0 hx.2 hb1)
    have hm1 : Measurable (fun x : ℝ => ENNReal.ofReal ((x - a) ^ (-2 * s) / (2 * s))) :=
      ENNReal.measurable_ofReal.comp
        (((measurable_id.sub measurable_const).pow_const _).div_const _)
    calc
      ∫⁻ x, (∫⁻ y, S₁.indicator (Ks s) (x, y) ∂μI) ∂μI
          ≤ ∫⁻ x in Set.Ioo a b,
              (ENNReal.ofReal ((x - a) ^ (-2 * s) / (2 * s)) +
                ENNReal.ofReal ((b - x) ^ (-2 * s) / (2 * s))) := houter
      _ = (∫⁻ x in Set.Ioo a b, ENNReal.ofReal ((x - a) ^ (-2 * s) / (2 * s))) +
            (∫⁻ x in Set.Ioo a b, ENNReal.ofReal ((b - x) ^ (-2 * s) / (2 * s))) :=
            lintegral_add_left hm1 _
      _ < ⊤ := by
            have h1 : ∫⁻ x in Set.Ioo a b, ENNReal.ofReal ((x - a) ^ (-2 * s) / (2 * s)) < ⊤ := by
              have hpull : ∀ x : ℝ, ENNReal.ofReal ((x - a) ^ (-2 * s) / (2 * s)) =
                  ENNReal.ofReal ((2 * s)⁻¹) * ENNReal.ofReal ((x - a) ^ (-2 * s)) := by
                intro x; rw [div_eq_inv_mul, ENNReal.ofReal_mul (by positivity)]
              have hm1' : Measurable (fun x : ℝ => ENNReal.ofReal ((x - a) ^ (-2 * s))) :=
                ENNReal.measurable_ofReal.comp ((measurable_id.sub measurable_const).pow_const _)
              simp_rw [hpull]
              rw [lintegral_const_mul _ hm1', lintegral_Ioo_left_rpow_eq hs hab]
              exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
            have h2 : ∫⁻ x in Set.Ioo a b, ENNReal.ofReal ((b - x) ^ (-2 * s) / (2 * s)) < ⊤ := by
              have hpull : ∀ x : ℝ, ENNReal.ofReal ((b - x) ^ (-2 * s) / (2 * s)) =
                  ENNReal.ofReal ((2 * s)⁻¹) * ENNReal.ofReal ((b - x) ^ (-2 * s)) := by
                intro x; rw [div_eq_inv_mul, ENNReal.ofReal_mul (by positivity)]
              have hm2' : Measurable (fun x : ℝ => ENNReal.ofReal ((b - x) ^ (-2 * s))) :=
                ENNReal.measurable_ofReal.comp ((measurable_const.sub measurable_id).pow_const _)
              simp_rw [hpull]
              rw [lintegral_const_mul _ hm2', lintegral_Ioo_right_rpow_eq hs hab]
              exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
            exact ENNReal.add_lt_top.mpr ⟨h1, h2⟩
  have hmS1 : Measurable (fun p : ℝ × ℝ => S₁.indicator (Ks s) p) := (measurable_Ks s).indicator hS₁
  have hmS2 : Measurable (fun p : ℝ × ℝ => S₂.indicator (Ks s) p) := (measurable_Ks s).indicator hS₂
  have hmS12 : Measurable (fun p : ℝ × ℝ => S₁.indicator (Ks s) p + S₂.indicator (Ks s) p) :=
    hmS1.add hmS2
  have hle : ∫⁻ p, ENNReal.ofReal ((χ p.1 - χ p.2) ^ 2) * Ks s p ∂μΩ ≤
      (∫⁻ p, S₁.indicator (Ks s) p ∂μΩ) + (∫⁻ p, S₂.indicator (Ks s) p ∂μΩ) +
      (∫⁻ p, (Iset ×ˢ Iset)ᶜ.indicator (fun _ => (⊤ : ℝ≥0∞)) p ∂μΩ) := by
    calc
      ∫⁻ p, ENNReal.ofReal ((χ p.1 - χ p.2) ^ 2) * Ks s p ∂μΩ
          ≤ ∫⁻ p, (S₁.indicator (Ks s) p + S₂.indicator (Ks s) p +
              (Iset ×ˢ Iset)ᶜ.indicator (fun _ => ⊤) p) ∂μΩ := lintegral_mono hsplit
      _ = (∫⁻ p, (S₁.indicator (Ks s) p + S₂.indicator (Ks s) p) ∂μΩ) +
            (∫⁻ p, (Iset ×ˢ Iset)ᶜ.indicator (fun _ => (⊤ : ℝ≥0∞)) p ∂μΩ) :=
            lintegral_add_left hmS12 _
      _ = _ := by rw [lintegral_add_left hmS1 _]
  rw [hcompl_zero, add_zero, hsymm] at hle
  exact lt_of_le_of_lt hle (ENNReal.add_lt_top.mpr ⟨hcross, hcross⟩)

noncomputable def indicatorH {s : ℝ} (hs0 : 0 < s) (hs : s < 1 / 2)
    (a b : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) : Hsub s :=
  mkH ((Set.Icc a b).indicator (1 : ℝ → ℝ))
    (measurable_const.indicator measurableSet_Icc)
    (by
      have hle : ∀ x : ℝ, ENNReal.ofReal (((Set.Icc a b).indicator (1 : ℝ → ℝ) x) ^ 2) ≤ 1 := by
        intro x; by_cases hx : x ∈ Set.Icc a b <;> simp [hx]
      calc
        ∫⁻ x, ENNReal.ofReal (((Set.Icc a b).indicator (1 : ℝ → ℝ) x) ^ 2) ∂μI
            ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂μI := lintegral_mono hle
        _ = 1 := by simp [μI_univ]
        _ < ⊤ := ENNReal.one_lt_top)
    (indicator_Icc_energy_lt_top hs0 hs ha0 hab hb1)

lemma indicatorH_fst_ae {s : ℝ} (hs0 : 0 < s) (hs : s < 1 / 2)
    (a b : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    ((indicatorH hs0 hs a b ha0 hab hb1).1.fst : ℝ → ℝ) =ᵐ[μI]
      (Set.Icc a b).indicator (1 : ℝ → ℝ) :=
  mkH_fst_ae _ _ _ _

lemma linearIndependent_indicators {s : ℝ} (hs0 : 0 < s) (hs : s < 1 / 2) :
    LinearIndependent ℝ (fun k : ℕ =>
      indicatorH hs0 hs (1 / ((k : ℝ) + 2)) (1 / ((k : ℝ) + 1))
        (by positivity)
        (by apply one_div_le_one_div_of_le (by positivity); linarith)
        (by rw [div_le_one (by positivity)]; linarith)) := by
  rw [linearIndependent_iff']
  intro S c hsum k hk
  let v : ℕ → Hsub s := fun j =>
    indicatorH hs0 hs (1 / ((j : ℝ) + 2)) (1 / ((j : ℝ) + 1))
      (by positivity) (by apply one_div_le_one_div_of_le (by positivity); linarith)
      (by rw [div_le_one (by positivity)]; linarith)
  have hsum_val : (∑ j ∈ S, c j • (v j).1.fst : Lp ℝ 2 μI) = 0 := by
    have h1 : (∑ j ∈ S, c j • v j).1.fst = (0 : Hsub s).1.fst := congrArg (fun z => z.1.fst) hsum
    rw [Hsub_fst_finset_sum] at h1
    exact h1
  have hae_sum : ∀ᵐ x ∂μI, (∑ j ∈ S, c j * (Set.Icc (1 / ((j : ℝ) + 2)) (1 / ((j : ℝ) + 1))).indicator
      (1 : ℝ → ℝ) x) = 0 := by
    have h0 : ((∑ j ∈ S, c j • (v j).1.fst : Lp ℝ 2 μI) : ℝ → ℝ) =ᵐ[μI] 0 := by
      rw [hsum_val]; exact Lp.coeFn_zero ℝ 2 μI
    have hfin : ((∑ j ∈ S, c j • (v j).1.fst : Lp ℝ 2 μI) : ℝ → ℝ) =ᵐ[μI]
        fun x => ∑ j ∈ S, c j * (Set.Icc (1 / ((j : ℝ) + 2)) (1 / ((j : ℝ) + 1))).indicator
          (1 : ℝ → ℝ) x := by
      have hterm : ∀ j : ℕ, ((c j • (v j).1.fst : Lp ℝ 2 μI) : ℝ → ℝ) =ᵐ[μI]
          fun x => c j * (Set.Icc (1 / ((j : ℝ) + 2)) (1 / ((j : ℝ) + 1))).indicator (1 : ℝ → ℝ) x := by
        intro j
        filter_upwards [Lp.coeFn_smul (c j) (v j).1.fst, indicatorH_fst_ae hs0 hs _ _ _ _ _] with x hx1 hx2
        simp only [Pi.smul_apply, smul_eq_mul] at hx1
        rw [hx1, hx2]
      have hsum_ae := Lp_coeFn_finset_sum S (fun j => c j • (v j).1.fst)
      have hall : ∀ᵐ x ∂μI, ∀ j ∈ S, ((c j • (v j).1.fst : Lp ℝ 2 μI) : ℝ → ℝ) x =
          c j * (Set.Icc (1 / ((j : ℝ) + 2)) (1 / ((j : ℝ) + 1))).indicator (1 : ℝ → ℝ) x :=
        (ae_ball_iff S.countable_toSet).mpr (fun j _ => hterm j)
      filter_upwards [hsum_ae, hall] with x hxs hallx
      rw [hxs]
      exact Finset.sum_congr rfl (fun j hj => hallx j hj)
    filter_upwards [h0, hfin] with x hx0 hxf
    rw [← hxf]; exact hx0
  let Jk : Set ℝ := Set.Ioo (1 / ((k : ℝ) + 2)) (1 / ((k : ℝ) + 1))
  have hJk_pos : 0 < μI Jk := by
    have hsub : Jk ⊆ Iset := fun x hx => ⟨by linarith [hx.1, show (0 : ℝ) < 1 / ((k : ℝ) + 2) by positivity],
      by linarith [hx.2, show (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 by rw [div_le_one (by positivity)]; linarith]⟩
    rw [μI, Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.mpr hsub, Real.volume_Ioo]
    apply ENNReal.ofReal_pos.mpr
    have hlt : (1 : ℝ) / ((k : ℝ) + 2) < 1 / ((k : ℝ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  have hex : ∃ x ∈ Jk, (∑ j ∈ S, c j * (Set.Icc (1 / ((j : ℝ) + 2)) (1 / ((j : ℝ) + 1))).indicator
      (1 : ℝ → ℝ) x) = 0 := by
    by_contra hnot
    push Not at hnot
    have hsub : Jk ⊆ {x | (∑ j ∈ S, c j * (Set.Icc (1 / ((j : ℝ) + 2)) (1 / ((j : ℝ) + 1))).indicator
        (1 : ℝ → ℝ) x) ≠ 0} := hnot
    have h0 : μI Jk = 0 := measure_mono_null hsub (ae_iff.mp hae_sum)
    exact hJk_pos.ne' h0
  obtain ⟨x, hxJk, hxsum⟩ := hex
  have hterm_eq : ∀ j ∈ S, c j * (Set.Icc (1 / ((j : ℝ) + 2)) (1 / ((j : ℝ) + 1))).indicator
      (1 : ℝ → ℝ) x = if j = k then c k else 0 := by
    intro j _
    by_cases hjk : j = k
    · subst hjk
      have hxcc : x ∈ Set.Icc (1 / ((j : ℝ) + 2)) (1 / ((j : ℝ) + 1)) := ⟨hxJk.1.le, hxJk.2.le⟩
      simp only [if_true, Set.indicator_of_mem hxcc, Pi.one_apply, mul_one]
    · simp only [hjk, if_false]
      have hxnot : x ∉ Set.Icc (1 / ((j : ℝ) + 2)) (1 / ((j : ℝ) + 1)) := by
        intro hcc
        rcases lt_or_gt_of_ne hjk with hlt | hgt
        · have hle : (j : ℝ) + 2 ≤ (k : ℝ) + 1 := by exact_mod_cast (by omega : j + 2 ≤ k + 1)
          have h1 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((j : ℝ) + 2) :=
            one_div_le_one_div_of_le (by positivity) hle
          linarith [hxJk.2, hcc.1]
        · have hle : (k : ℝ) + 2 ≤ (j : ℝ) + 1 := by exact_mod_cast (by omega : k + 2 ≤ j + 1)
          have h1 : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((k : ℝ) + 2) :=
            one_div_le_one_div_of_le (by positivity) hle
          linarith [hxJk.1, hcc.2]
      simp only [Set.indicator_of_notMem hxnot, mul_zero]
  rw [Finset.sum_congr rfl hterm_eq, Finset.sum_ite_eq' S k, if_pos hk] at hxsum
  exact hxsum

noncomputable def lpReindex {ι₁ ι₂ : Type*} (π : ι₁ ≃ ι₂) :
    lp (fun _ : ι₁ => ℝ) 2 ≃ₗᵢ[ℝ] lp (fun _ : ι₂ => ℝ) 2 where
  toFun x :=
    ⟨fun n => (x : ι₁ → ℝ) (π.symm n), by
      have h2pos : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
      change Memℓp (fun n : ι₂ => (x : ι₁ → ℝ) (π.symm n)) 2
      rw [memℓp_gen_iff h2pos]
      have hx : Memℓp (fun i : ι₁ => (x : ι₁ → ℝ) i) 2 := x.2
      rw [memℓp_gen_iff h2pos] at hx
      exact (Equiv.summable_iff π.symm).mpr hx⟩
  invFun y :=
    ⟨fun i => (y : ι₂ → ℝ) (π i), by
      have h2pos : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
      change Memℓp (fun i : ι₁ => (y : ι₂ → ℝ) (π i)) 2
      rw [memℓp_gen_iff h2pos]
      have hy : Memℓp (fun n : ι₂ => (y : ι₂ → ℝ) n) 2 := y.2
      rw [memℓp_gen_iff h2pos] at hy
      exact (Equiv.summable_iff π).mpr hy⟩
  left_inv x := by ext i; exact congrArg (fun j => (x : ι₁ → ℝ) j) (π.symm_apply_apply i)
  right_inv y := by ext n; exact congrArg (fun m => (y : ι₂ → ℝ) m) (π.apply_symm_apply n)
  map_add' _ _ := by ext n; rfl
  map_smul' _ _ := by ext n; rfl
  norm_map' x := by
    have h2pos : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
    rw [lp.norm_eq_tsum_rpow h2pos, lp.norm_eq_tsum_rpow h2pos]
    congr 1
    exact Equiv.tsum_eq π.symm (fun i => ‖(x : ι₁ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal)

lemma exists_equiv_hilbert {s : ℝ} (hs0 : 0 < s) (hs : s < 1 / 2) :
    Nonempty (Hsub s ≃ₗᵢ[ℝ] OMA.S_mo_45322.Hilbert) := by
  have : CompleteSpace (Hsub s) := completeSpace_Hsub s
  have : SecondCountableTopology (Hsub s) := secondCountable_Hsub s hs0
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℝ (Hsub s)
  have hw_count : Countable w := by
    obtain ⟨D, hD_count, hD_dense⟩ := TopologicalSpace.exists_countable_dense (Hsub s)
    have hball : ∀ i : w, ∃ d : D, dist (b i) (d : Hsub s) < 1 / 2 := by
      intro i
      obtain ⟨d, hd_ball, hdD⟩ := Metric.dense_iff.mp hD_dense (b i) (1 / 2) (by norm_num)
      exact ⟨⟨d, hdD⟩, by rw [dist_comm]; exact hd_ball⟩
    choose f hf using hball
    have hfinj : Function.Injective f := by
      intro i j hij
      by_contra hne
      have hsq : dist (b i) (b j) ^ 2 = 2 := by
        rw [dist_eq_norm, norm_sub_sq_real, b.orthonormal.1 i, b.orthonormal.1 j,
          b.orthonormal.2 hne]
        ring
      have htri : dist (b i) (b j) ≤ dist (b i) (f i : Hsub s) + dist (f j : Hsub s) (b j) := by
        rw [hij]; exact dist_triangle _ _ _
      have h1 : dist (b i) (b j) < 1 := by
        have hfi := hf i
        have hfj := hf j
        rw [dist_comm] at hfj
        linarith
      nlinarith [dist_nonneg (x := b i) (y := b j)]
    have : Countable D := hD_count.to_subtype
    exact hfinj.countable
  have hw_inf : Infinite w := by
    by_contra hnot
    rw [not_infinite_iff_finite] at hnot
    have : Fintype w := Fintype.ofFinite w
    let efin : Hsub s ≃ₗ[ℝ] (w → ℝ) :=
      b.repr.toLinearEquiv.trans
        { toFun := fun x i => x i
          invFun := fun f => ⟨f, (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mpr
            (hasSum_fintype _).summable⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
    have : FiniteDimensional ℝ (Hsub s) := Module.Finite.equiv efin.symm
    have hli := linearIndependent_indicators hs0 hs
    have hcard := hli.cardinal_lift_le_rank
    have hfin : Module.rank ℝ (Hsub s) < Cardinal.aleph0 := Module.rank_lt_aleph0 ℝ (Hsub s)
    have hnat : Cardinal.aleph0 ≤ Cardinal.lift.{0, 0} (Cardinal.mk ℕ) := by simp
    have hcard' : Cardinal.aleph0 ≤ Module.rank ℝ (Hsub s) := by
      simpa using hnat.trans hcard
    exact not_lt.mpr hcard' hfin
  have : Countable w := hw_count
  have : Encodable w := Encodable.ofCountable w
  have : Infinite w := hw_inf
  obtain ⟨π⟩ : Nonempty (w ≃ ℕ) := ⟨(Denumerable.ofEncodableOfInfinite w).eqv w⟩
  exact ⟨b.repr.trans (lpReindex π)⟩

/-! Section 4: Integer-valued subgroup Gsub, transfer, and impossibility for β > α -/

def Gsub (s : ℝ) : AddSubgroup (Hsub s) where
  carrier := { g | ∀ᵐ x ∂μI, (g.1.fst : ℝ → ℝ) x ∈ Set.range ((↑) : ℤ → ℝ) }
  zero_mem' := by
    have h0 : ((0 : Lp ℝ 2 μI) : ℝ → ℝ) =ᵐ[μI] 0 := Lp.coeFn_zero ℝ 2 μI
    filter_upwards [h0] with x hx
    change ((0 : Lp ℝ 2 μI) : ℝ → ℝ) x ∈ Set.range ((↑) : ℤ → ℝ)
    simp only [Pi.zero_apply] at hx
    exact ⟨0, by rw [Int.cast_zero, hx]⟩
  add_mem' {g₁ g₂} h₁ h₂ := by
    have hadd : ((g₁.1.fst + g₂.1.fst : Lp ℝ 2 μI) : ℝ → ℝ) =ᵐ[μI]
        (g₁.1.fst : ℝ → ℝ) + (g₂.1.fst : ℝ → ℝ) := Lp.coeFn_add g₁.1.fst g₂.1.fst
    filter_upwards [h₁, h₂, hadd] with x ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩ hax
    change ((g₁.1.fst + g₂.1.fst : Lp ℝ 2 μI) : ℝ → ℝ) x ∈ Set.range ((↑) : ℤ → ℝ)
    simp only [Pi.add_apply] at hax
    exact ⟨n₁ + n₂, by rw [Int.cast_add, hax, hn₁, hn₂]⟩
  neg_mem' {g} hg := by
    have hneg : ((-g.1.fst : Lp ℝ 2 μI) : ℝ → ℝ) =ᵐ[μI] -(g.1.fst : ℝ → ℝ) := Lp.coeFn_neg g.1.fst
    filter_upwards [hg, hneg] with x ⟨n, hn⟩ hnx
    change ((-g.1.fst : Lp ℝ 2 μI) : ℝ → ℝ) x ∈ Set.range ((↑) : ℤ → ℝ)
    simp only [Pi.neg_apply] at hnx
    exact ⟨-n, by rw [Int.cast_neg, hnx, hn]⟩

lemma isClosed_Gsub (s : ℝ) : IsClosed (Gsub s : Set (Hsub s)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u g hu hlim
  have hlim1 : Tendsto (fun n => (u n).1.fst) atTop (𝓝 g.1.fst) :=
    ((WithLp.continuous_fst 2 (Lp ℝ 2 μI) (Lp ℝ 2 (μ₂ s))).comp continuous_subtype_val).continuousAt.tendsto.comp hlim
  obtain ⟨φ, _, hφ_ae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim1).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μI, ∀ k, ((u (φ k)).1.fst : ℝ → ℝ) x ∈ Set.range ((↑) : ℤ → ℝ) :=
    ae_all_iff.mpr (fun k => hu (φ k))
  filter_upwards [hφ_ae, hall] with x hxp hmem
  exact Real.isClosed_range_intCast.mem_of_tendsto hxp (Eventually.of_forall hmem)

def holderConnectedH {s : ℝ} (exponent : NNReal) (K : AddSubgroup (Hsub s)) : Prop :=
  ∀ a ∈ K, ∀ b ∈ K,
    ∃ path : Path a b, (∀ t, path t ∈ K) ∧
      ∃ constant : NNReal, HolderWith constant exponent path

lemma transfer_holderConnected {s : ℝ} (e : Hsub s ≃ₗᵢ[ℝ] OMA.S_mo_45322.Hilbert)
    (exponent : NNReal) :
    OMA.S_mo_45322.holderConnected exponent (Gsub s |>.map e.toAddEquiv.toAddMonoidHom) ↔
      holderConnectedH exponent (Gsub s) := by
  constructor
  · intro hG a ha b hb
    obtain ⟨p, hpG, C, hC⟩ := hG (e a) ⟨a, ha, rfl⟩ (e b) ⟨b, hb, rfl⟩
    let q : Path a b :=
      { toFun := fun t => e.symm (p t)
        continuous_toFun := e.symm.continuous.comp p.continuous
        source' := by simp [p.source]
        target' := by simp [p.target] }
    refine ⟨q, fun t => ?_, C, ?_⟩
    · obtain ⟨y, hyG, hy⟩ := hpG t
      have : e.symm (p t) = y := by rw [← hy]; exact e.symm_apply_apply y
      simpa [q, this] using hyG
    · intro t₁ t₂
      have heq : edist (q t₁) (q t₂) = edist (p t₁) (p t₂) := e.symm.isometry.edist_eq (p t₁) (p t₂)
      rw [heq]
      exact hC t₁ t₂
  · intro hH a ha b hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    obtain ⟨p, hpH, C, hC⟩ := hH a' ha' b' hb'
    let q : Path (e.toAddEquiv.toAddMonoidHom a') (e.toAddEquiv.toAddMonoidHom b') :=
      { toFun := fun t => e (p t)
        continuous_toFun := e.continuous.comp p.continuous
        source' := by change e (p 0) = e a'; rw [p.source]
        target' := by change e (p 1) = e b'; rw [p.target] }
    refine ⟨q, fun t => ⟨p t, hpH t, rfl⟩, C, ?_⟩
    intro t₁ t₂
    have heq : edist (q t₁) (q t₂) = edist (p t₁) (p t₂) := e.isometry.edist_eq (p t₁) (p t₂)
    rw [heq]
    exact hC t₁ t₂

noncomputable def intRep {s : ℝ} (g : Hsub s) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ Iset then (⌊(Lp.aestronglyMeasurable g.1.fst).mk g.1.fst x + 1 / 2⌋ : ℝ) else 0

lemma measurable_intRep {s : ℝ} (g : Hsub s) : Measurable (intRep g) := by
  classical
  unfold intRep
  refine Measurable.ite measurableSet_Iset ?_ measurable_const
  exact measurable_from_top.comp
    (Int.measurable_floor.comp
      ((Lp.aestronglyMeasurable g.1.fst).stronglyMeasurable_mk.measurable.add measurable_const))

lemma intRep_int {s : ℝ} (g : Hsub s) (x : ℝ) :
    ∃ n : ℤ, intRep g x = (n : ℝ) := by
  classical
  unfold intRep
  by_cases hx : x ∈ Iset
  · exact ⟨⌊(Lp.aestronglyMeasurable g.1.fst).mk g.1.fst x + 1 / 2⌋, by simp [hx]⟩
  · exact ⟨0, by simp [hx]⟩

lemma intRep_ae_eq {s : ℝ} {g : Hsub s} (hg : g ∈ Gsub s) :
    (g.1.fst : ℝ → ℝ) =ᵐ[μI] intRep g := by
  classical
  filter_upwards [ae_mem_Iset, hg, (Lp.aestronglyMeasurable g.1.fst).ae_eq_mk] with x hx ⟨n, hn⟩ hmk
  unfold intRep
  rw [if_pos hx, ← hmk, ← hn]
  have hfl : ⌊(n : ℝ) + 1 / 2⌋ = n := by
    rw [Int.floor_eq_iff]
    constructor <;> linarith
  rw [hfl]

lemma isoperimetric_1d {s : ℝ} (hs0 : 0 < s) {A : Set ℝ} (hA_meas : MeasurableSet A)
    (hδ_pos : 0 < (μI A).toReal) (hδ_le : (μI A).toReal ≤ 1 / 4)
    {x : ℝ} (hx : x ∈ Iset) :
    ENNReal.ofReal ((2 : ℝ) ^ (-(1 + 2 * s)) * (μI A).toReal ^ (-2 * s)) ≤
      ∫⁻ y in Iset \ A, Ks s (x, y) ∂μI := by
  set δ := (μI A).toReal
  have hδ_fin : μI A ≠ ⊤ := measure_ne_top μI A
  have hδ_eq : ENNReal.ofReal δ = μI A := ENNReal.ofReal_toReal hδ_fin
  let J : Set ℝ := Set.Icc (x - 2 * δ) (x + 2 * δ) ∩ Iset
  have hJ_meas : MeasurableSet J := measurableSet_Icc.inter measurableSet_Iset
  have hJ_ge : ENNReal.ofReal (2 * δ) ≤ μI J := by
    by_cases hxmid : x ≤ 1 / 2
    · have hsub : Set.Icc x (x + 2 * δ) ⊆ J := fun y hy =>
        ⟨⟨by linarith [hy.1], hy.2⟩, ⟨by linarith [hx.1, hy.1], by linarith [hy.2, hxmid, hδ_le]⟩⟩
      calc
        ENNReal.ofReal (2 * δ) = volume (Set.Icc x (x + 2 * δ)) := by
          rw [Real.volume_Icc]; congr 1; ring
        _ = μI (Set.Icc x (x + 2 * δ)) := by
          rw [μI, Measure.restrict_apply measurableSet_Icc,
            Set.inter_eq_left.mpr (hsub.trans Set.inter_subset_right)]
        _ ≤ μI J := measure_mono hsub
    · have hsub : Set.Icc (x - 2 * δ) x ⊆ J := fun y hy =>
        ⟨⟨hy.1, by linarith [hy.2]⟩, ⟨by linarith [hy.1, hxmid, hδ_le], by linarith [hy.2, hx.2]⟩⟩
      calc
        ENNReal.ofReal (2 * δ) = volume (Set.Icc (x - 2 * δ) x) := by
          rw [Real.volume_Icc]; congr 1; ring
        _ = μI (Set.Icc (x - 2 * δ) x) := by
          rw [μI, Measure.restrict_apply measurableSet_Icc,
            Set.inter_eq_left.mpr (hsub.trans Set.inter_subset_right)]
        _ ≤ μI J := measure_mono hsub
  have hdiff_ge : ENNReal.ofReal δ ≤ μI (J \ A) := by
    have hcov : μI J ≤ μI (J \ A) + μI A := by
      calc
        μI J ≤ μI ((J \ A) ∪ A) := measure_mono (fun y hy => by by_cases h : y ∈ A <;> simp [hy, h])
        _ ≤ μI (J \ A) + μI A := measure_union_le _ _
    have h1 : ENNReal.ofReal δ + ENNReal.ofReal δ ≤ μI (J \ A) + ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add hδ_pos.le hδ_pos.le, show δ + δ = 2 * δ by ring, hδ_eq]
      exact hJ_ge.trans hcov
    exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top h1
  have hsub_IA : (J \ A) \ {x} ⊆ Iset \ A := fun y hy => ⟨hy.1.1.2, hy.1.2⟩
  have hmeas_s : MeasurableSet ((J \ A) \ {x}) := (hJ_meas.diff hA_meas).diff (measurableSet_singleton x)
  have hdiff_x : μI ((J \ A) \ {x}) = μI (J \ A) := measure_sdiff_null (μI_singleton x)
  have hpt : ∀ y ∈ (J \ A) \ {x}, ENNReal.ofReal ((2 * δ) ^ (-(1 + 2 * s))) ≤ Ks s (x, y) := by
    intro y hy
    have hne : x ≠ y := Ne.symm hy.2
    have habs_le : |x - y| ≤ 2 * δ := by
      rw [abs_le]
      constructor <;> linarith [hy.1.1.1.1, hy.1.1.1.2]
    have habs_pos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
    unfold Ks
    rw [if_neg hne]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_neg (by positivity), Real.rpow_neg habs_pos.le]
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow habs_pos.le habs_le (by linarith))
  calc
    ENNReal.ofReal ((2 : ℝ) ^ (-(1 + 2 * s)) * δ ^ (-2 * s))
        = ENNReal.ofReal ((2 * δ) ^ (-(1 + 2 * s))) * ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [Real.mul_rpow (by norm_num) hδ_pos.le, mul_assoc,
            ← Real.rpow_add_one hδ_pos.ne']
          congr 2; ring
    _ ≤ ENNReal.ofReal ((2 * δ) ^ (-(1 + 2 * s))) * μI ((J \ A) \ {x}) := by
          rw [hdiff_x]; gcongr
    _ = ∫⁻ _ in (J \ A) \ {x}, ENNReal.ofReal ((2 * δ) ^ (-(1 + 2 * s))) ∂μI := by
          rw [setLIntegral_const]
    _ ≤ ∫⁻ y in (J \ A) \ {x}, Ks s (x, y) ∂μI := setLIntegral_mono' hmeas_s hpt
    _ ≤ ∫⁻ y in Iset \ A, Ks s (x, y) ∂μI := lintegral_mono_set hsub_IA

lemma l1_le_of_small_norm {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    {g : Hsub (sVal α)} (hg : g ∈ Gsub (sVal α)) (hnorm : ‖g‖ ≤ 1 / 4) :
    (∫⁻ x, ENNReal.ofReal (|intRep g x|) ∂μI).toReal ≤
      (2 : ℝ) ^ (sVal α / (α : ℝ)) * ‖g‖ ^ (1 / (α : ℝ)) := by
  let s := sVal α
  have hα_pos : (0 : ℝ) < (α : ℝ) := NNReal.coe_pos.mpr hα0
  have hα_lt : (α : ℝ) < 1 / 2 := by exact_mod_cast hαhalf
  have hs0 : 0 < s := by dsimp [s, sVal]; linarith
  have h2αs : 1 - 2 * s = 2 * (α : ℝ) := by dsimp [s, sVal]; ring
  let f := intRep g
  have hf_meas : Measurable f := measurable_intRep g
  let A : Set ℝ := {x ∈ Iset | f x ≠ 0}
  have hA_meas : MeasurableSet A :=
    measurableSet_Iset.inter (hf_meas (measurableSet_singleton 0).compl)
  have hge1 : ∀ x ∈ A, (1 : ℝ) ≤ |f x| := by
    intro x hx
    obtain ⟨n, hn⟩ := intRep_int g x
    have hn0 : n ≠ 0 := by intro h0; subst h0; exact hx.2 (by simpa using hn)
    have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    rw [show f x = (n : ℝ) from hn, ← Int.cast_abs]
    exact_mod_cast h1
  set δ := (μI A).toReal
  by_cases hδ0 : δ = 0
  · have hμA0 : μI A = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).mp hδ0).resolve_right (measure_ne_top μI A)
    have hf0 : ∀ᵐ x ∂μI, ENNReal.ofReal (|f x|) = 0 := by
      have haeA : ∀ᵐ x ∂μI, x ∉ A := ae_iff.mpr (by simpa using hμA0)
      filter_upwards [ae_mem_Iset, haeA] with x hxI hxA
      have : f x = 0 := by by_contra hne; exact hxA ⟨hxI, hne⟩
      simp [this]
    change (∫⁻ x, ENNReal.ofReal (|f x|) ∂μI).toReal ≤ _
    rw [lintegral_congr_ae hf0, lintegral_zero, ENNReal.toReal_zero]
    positivity
  · have hδ_pos : 0 < δ := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hδ0)
    have hf_sq_fin : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μI = ENNReal.ofReal (‖g.1.fst‖ ^ 2) := by
      rw [Lp_ofReal_norm_sq_eq_lintegral g.1.fst]
      apply lintegral_congr_ae
      filter_upwards [intRep_ae_eq hg] with x hx
      rw [hx]
    have hL1_le_L2 : ∫⁻ x, ENNReal.ofReal (|f x|) ∂μI ≤ ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μI := by
      apply lintegral_mono_ae
      filter_upwards [ae_mem_Iset] with x hxI
      apply ENNReal.ofReal_le_ofReal
      by_cases hfx : f x = 0
      · simp [hfx]
      · have h1 := hge1 x ⟨hxI, hfx⟩
        nlinarith [sq_abs (f x)]
    have hL1_fin : ∫⁻ x, ENNReal.ofReal (|f x|) ∂μI ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [hf_sq_fin]; exact ENNReal.ofReal_ne_top) hL1_le_L2
    set L1 := (∫⁻ x, ENNReal.ofReal (|f x|) ∂μI).toReal
    have hL1_eq_ofReal : ENNReal.ofReal L1 = ∫⁻ x, ENNReal.ofReal (|f x|) ∂μI :=
      ENNReal.ofReal_toReal hL1_fin
    have hδ_le_L1 : δ ≤ L1 := by
      have h1 : μI A ≤ ∫⁻ x, ENNReal.ofReal (|f x|) ∂μI := by
        calc
          μI A = ∫⁻ _ in A, (1 : ℝ≥0∞) ∂μI := by rw [setLIntegral_one]
          _ ≤ ∫⁻ x in A, ENNReal.ofReal (|f x|) ∂μI := by
                apply setLIntegral_mono' hA_meas
                intro x hx; exact ENNReal.one_le_ofReal.mpr (hge1 x hx)
          _ ≤ ∫⁻ x, ENNReal.ofReal (|f x|) ∂μI := setLIntegral_le_lintegral _ _
      exact ENNReal.toReal_mono hL1_fin h1
    have hL1_pos : 0 < L1 := lt_of_lt_of_le hδ_pos hδ_le_L1
    have hfst_le_g : ‖g.1.fst‖ ≤ ‖g‖ := by
      have hsq : ‖g.1.fst‖ ^ 2 ≤ ‖g‖ ^ 2 := by
        have h1 : ‖g‖ ^ 2 = ‖g.1.fst‖ ^ 2 + ‖g.1.snd‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 g.1
        nlinarith [sq_nonneg ‖g.1.snd‖]
      nlinarith [norm_nonneg g.1.fst, norm_nonneg g]
    have hL1_le_fst : L1 ≤ ‖g.1.fst‖ := by
      have hcs : ∫⁻ x, ENNReal.ofReal (|f x|) ∂μI ≤
          (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μI) ^ (1 / 2 : ℝ) * (∫⁻ _, (1 : ℝ≥0∞) ∂μI) ^ (1 / 2 : ℝ) := by
        have hmul := ENNReal.lintegral_mul_le_Lp_mul_Lq μI
          (Real.HolderConjugate.conjExponent (by norm_num : (1 : ℝ) < 2))
          (f := fun x => ENNReal.ofReal (|f x|)) (g := fun _ => (1 : ℝ≥0∞))
          (ENNReal.measurable_ofReal.comp hf_meas.abs).aemeasurable measurable_const.aemeasurable
        have hconj : Real.conjExponent 2 = 2 := by norm_num [Real.conjExponent]
        rw [hconj] at hmul
        refine le_trans ?_ (hmul.trans (le_of_eq ?_))
        · apply lintegral_mono
          intro x; simp
        · congr 2
          · apply lintegral_congr
            intro x
            rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
              Real.rpow_two, sq_abs]
          · simp
      rw [hf_sq_fin, lintegral_const, μI_univ, mul_one, ENNReal.one_rpow, mul_one,
        ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _),
        show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at hcs
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcs
      simpa [L1, ENNReal.toReal_ofReal (norm_nonneg _)] using this
    have hδ_le_quarter : δ ≤ 1 / 4 := hδ_le_L1.trans (hL1_le_fst.trans (hfst_le_g.trans hnorm))
    have hnorm_ge : 2 ^ (-2 * s) * L1 ^ (2 * (α : ℝ)) ≤ ‖g‖ ^ 2 := by
      have hsnd_le : ‖g.1.snd‖ ^ 2 ≤ ‖g‖ ^ 2 := by
        have h1 : ‖g‖ ^ 2 = ‖g.1.fst‖ ^ 2 + ‖g.1.snd‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 g.1
        nlinarith [sq_nonneg ‖g.1.fst‖]
      have hsem_eq : ENNReal.ofReal (‖g.1.snd‖ ^ 2) =
          ∫⁻ p, ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * Ks s p ∂μΩ := by
        rw [Lp_ofReal_norm_sq_eq_lintegral g.1.snd]
        have haesm : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((g.1.snd : ℝ × ℝ → ℝ) p ^ 2)) μΩ :=
          ENNReal.measurable_ofReal.comp_aemeasurable
            (((Lp.aestronglyMeasurable g.1.snd).aemeasurable.mono_ac (μΩ_absolutelyContinuous_μ₂ s)).pow_const 2)
        change ∫⁻ p, ENNReal.ofReal ((g.1.snd : ℝ × ℝ → ℝ) p ^ 2) ∂(μΩ.withDensity (Ks s)) = _
        rw [lintegral_withDensity_eq_lintegral_mul₀ (measurable_Ks s).aemeasurable haesm]
        have hF : (g.1.snd : ℝ × ℝ → ℝ) =ᵐ[μΩ] fun p => f p.1 - f p.2 := by
          have h1 := Measure.quasiMeasurePreserving_fst (μ := μI) (ν := μI) |>.ae (intRep_ae_eq hg)
          have h2 := Measure.quasiMeasurePreserving_snd (μ := μI) (ν := μI) |>.ae (intRep_ae_eq hg)
          filter_upwards [g.2, h1, h2] with p hgp h1p h2p
          rw [hgp, h1p, h2p]
        apply lintegral_congr_ae
        filter_upwards [hF] with p hp
        simp only [Pi.mul_apply]
        rw [hp, mul_comm]
      have hdisj : Disjoint (A ×ˢ (Iset \ A)) ((Iset \ A) ×ˢ A) := by
        rw [Set.disjoint_left]
        intro p hp1 hp2
        exact hp1.2.2 hp2.2
      have hmeas_fun : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * Ks s p) :=
        (ENNReal.measurable_ofReal.comp
          (((hf_meas.comp measurable_fst).sub (hf_meas.comp measurable_snd)).pow_const 2)).mul
          (measurable_Ks s)
      have h1_term : ENNReal.ofReal (2 ^ (-(1 + 2 * s)) * δ ^ (-2 * s)) * ∫⁻ x, ENNReal.ofReal (|f x|) ∂μI ≤
          ∫⁻ p in A ×ˢ (Iset \ A), ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * Ks s p ∂μΩ := by
        have hton : ∫⁻ p in A ×ˢ (Iset \ A), ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * Ks s p ∂μΩ =
            ∫⁻ x in A, ENNReal.ofReal (f x ^ 2) * (∫⁻ y in Iset \ A, Ks s (x, y) ∂μI) ∂μI := by
          rw [← lintegral_indicator (hA_meas.prod (measurableSet_Iset.diff hA_meas)),
            μΩ, lintegral_prod _ (hmeas_fun.indicator (hA_meas.prod (measurableSet_Iset.diff hA_meas))).aemeasurable,
            ← lintegral_indicator hA_meas]
          apply lintegral_congr
          intro x
          by_cases hx : x ∈ A
          · simp only [Set.indicator_of_mem hx]
            have hm_y : Measurable (fun y : ℝ => (Iset \ A).indicator (fun y => Ks s (x, y)) y) :=
              ((measurable_Ks s).comp (measurable_const.prodMk measurable_id)).indicator
                (measurableSet_Iset.diff hA_meas)
            rw [← lintegral_indicator (measurableSet_Iset.diff hA_meas),
              ← lintegral_const_mul _ hm_y]
            apply lintegral_congr
            intro y
            by_cases hy : y ∈ Iset \ A
            · have hfy : f y = 0 := by by_contra hne; exact hy.2 ⟨hy.1, hne⟩
              simp [hx, hy, hfy]
            · simp [hx, hy]
          · simp [hx]
        rw [hton]
        have hL1_A : ∫⁻ x, ENNReal.ofReal (|f x|) ∂μI = ∫⁻ x in A, ENNReal.ofReal (|f x|) ∂μI := by
          rw [← lintegral_indicator hA_meas]
          apply lintegral_congr_ae
          filter_upwards [ae_mem_Iset] with x hxI
          by_cases hx : x ∈ A
          · simp [hx]
          · have hfx : f x = 0 := by by_contra hne; exact hx ⟨hxI, hne⟩
            simp [hx, hfx]
        have hm_abs : Measurable (fun x : ℝ => ENNReal.ofReal (|f x|)) :=
          ENNReal.measurable_ofReal.comp hf_meas.abs
        rw [hL1_A, ← lintegral_const_mul _ hm_abs]
        apply setLIntegral_mono' hA_meas
        intro x hx
        have h1x : ENNReal.ofReal (|f x|) ≤ ENNReal.ofReal (f x ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          have := hge1 x hx
          nlinarith [sq_abs (f x)]
        calc
          ENNReal.ofReal (2 ^ (-(1 + 2 * s)) * δ ^ (-2 * s)) * ENNReal.ofReal (|f x|)
              = ENNReal.ofReal (|f x|) * ENNReal.ofReal (2 ^ (-(1 + 2 * s)) * δ ^ (-2 * s)) := mul_comm _ _
          _ ≤ ENNReal.ofReal (f x ^ 2) * (∫⁻ y in Iset \ A, Ks s (x, y) ∂μI) :=
              mul_le_mul' h1x (isoperimetric_1d hs0 hA_meas hδ_pos hδ_le_quarter hx.1)
      have h2_term : ∫⁻ p in (Iset \ A) ×ˢ A, ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * Ks s p ∂μΩ =
          ∫⁻ p in A ×ˢ (Iset \ A), ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * Ks s p ∂μΩ := by
        have hmp : MeasurePreserving Prod.swap μΩ μΩ := Measure.measurePreserving_swap
        rw [← lintegral_indicator ((measurableSet_Iset.diff hA_meas).prod hA_meas),
          ← lintegral_indicator (hA_meas.prod (measurableSet_Iset.diff hA_meas))]
        rw [← hmp.lintegral_comp (hmeas_fun.indicator (hA_meas.prod (measurableSet_Iset.diff hA_meas)))]
        apply lintegral_congr
        intro p
        by_cases h : p.swap ∈ A ×ˢ (Iset \ A)
        · have h' : p ∈ (Iset \ A) ×ˢ A := ⟨h.2, h.1⟩
          simp only [Set.indicator_of_mem h, Set.indicator_of_mem h',
            Prod.fst_swap, Prod.snd_swap, Ks_symm]
          congr 2; ring
        · have h' : p ∉ (Iset \ A) ×ˢ A := fun hp => h ⟨hp.2, hp.1⟩
          simp [h, h']
      have hsum_le : ∫⁻ p in A ×ˢ (Iset \ A), ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * Ks s p ∂μΩ +
          ∫⁻ p in (Iset \ A) ×ˢ A, ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * Ks s p ∂μΩ ≤
          ENNReal.ofReal (‖g.1.snd‖ ^ 2) := by
        rw [hsem_eq, ← lintegral_union ((measurableSet_Iset.diff hA_meas).prod hA_meas) hdisj]
        exact setLIntegral_le_lintegral _ _
      rw [h2_term] at hsum_le
      have hcomb : ENNReal.ofReal (2 ^ (-2 * s) * δ ^ (-2 * s) * L1) ≤ ENNReal.ofReal (‖g.1.snd‖ ^ 2) := by
        have hmul2 : ENNReal.ofReal (2 ^ (-2 * s) * δ ^ (-2 * s) * L1) =
            ENNReal.ofReal (2 ^ (-(1 + 2 * s)) * δ ^ (-2 * s)) * ENNReal.ofReal L1 +
            ENNReal.ofReal (2 ^ (-(1 + 2 * s)) * δ ^ (-2 * s)) * ENNReal.ofReal L1 := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          have hpow : (2 : ℝ) * 2 ^ (-(1 + 2 * s)) = 2 ^ (-2 * s) := by
            rw [mul_comm, ← Real.rpow_add_one (by norm_num)]
            congr 1; ring
          rw [← two_mul, ← mul_assoc, ← mul_assoc, hpow]
        rw [hmul2, hL1_eq_ofReal]
        exact (add_le_add h1_term h1_term).trans hsum_le
      have hreal : 2 ^ (-2 * s) * δ ^ (-2 * s) * L1 ≤ ‖g.1.snd‖ ^ 2 :=
        (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp hcomb
      have hδ_pow : L1 ^ (-2 * s) ≤ δ ^ (-2 * s) := by
        rw [show (-2 * s : ℝ) = -(2 * s) by ring, Real.rpow_neg hL1_pos.le, Real.rpow_neg hδ_pos.le]
        exact inv_anti₀ (by positivity) (Real.rpow_le_rpow hδ_pos.le hδ_le_L1 (by linarith))
      have hL1_pow : 2 ^ (-2 * s) * L1 ^ (2 * (α : ℝ)) ≤ 2 ^ (-2 * s) * δ ^ (-2 * s) * L1 := by
        rw [← h2αs, show 1 - 2 * s = -2 * s + 1 by ring, Real.rpow_add_one hL1_pos.ne', ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ_pow (by positivity)) hL1_pos.le
      exact hL1_pow.trans (hreal.trans hsnd_le)
    have hmul_pow : L1 ^ (2 * (α : ℝ)) ≤ 2 ^ (2 * s) * ‖g‖ ^ 2 := by
      have h1 : 2 ^ (2 * s) * (2 ^ (-2 * s) * L1 ^ (2 * (α : ℝ))) ≤ 2 ^ (2 * s) * ‖g‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hnorm_ge (by positivity)
      rw [← mul_assoc, ← Real.rpow_add (by norm_num),
        show 2 * s + -2 * s = 0 by ring, Real.rpow_zero, one_mul] at h1
      exact h1
    have hrpow := Real.rpow_le_rpow (by positivity) hmul_pow (show (0 : ℝ) ≤ 1 / (2 * (α : ℝ)) by positivity)
    rw [← Real.rpow_mul hL1_pos.le, mul_one_div_cancel (by positivity), Real.rpow_one,
      Real.mul_rpow (by positivity) (sq_nonneg _),
      ← Real.rpow_mul (by norm_num), ← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)] at hrpow
    have he1 : 2 * s * (1 / (2 * (α : ℝ))) = s / (α : ℝ) := by field_simp
    have he2 : (2 : ℝ) * (1 / (2 * (α : ℝ))) = 1 / (α : ℝ) := by field_simp
    rw [he1, he2] at hrpow
    exact hrpow

private lemma fin_sum_sub {M : Type*} [AddCommGroup M] (m : ℕ) (f : Fin (m + 1) → M) :
    ∑ i : Fin m, (f i.succ - f i.castSucc) = f (Fin.last m) - f 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    have hih := ih (fun i => f i.castSucc)
    simp only [Fin.succ_castSucc, Fin.castSucc_zero] at hih ⊢
    rw [hih]
    have hsucc : (Fin.last m).succ = Fin.last (m + 1) := rfl
    rw [hsucc]
    abel

lemma not_holderConnectedH_of_gt {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    {β : NNReal} (hαβ : α < β) : ¬ holderConnectedH β (Gsub (sVal α)) := by
  let s := sVal α
  have hα_pos : (0 : ℝ) < (α : ℝ) := NNReal.coe_pos.mpr hα0
  have hα_lt : (α : ℝ) < 1 / 2 := by exact_mod_cast hαhalf
  have hβ_gt : (α : ℝ) < (β : ℝ) := by exact_mod_cast hαβ
  have hβ_pos : (0 : ℝ) < (β : ℝ) := hα_pos.trans hβ_gt
  have hs0 : 0 < s := by dsimp [s, sVal]; linarith
  have hs_half : s < 1 / 2 := by dsimp [s, sVal]; linarith
  intro hconn
  let u : Hsub s := indicatorH hs0 hs_half 0 1 le_rfl zero_le_one le_rfl
  have hu_mem : u ∈ Gsub s := by
    filter_upwards [ae_mem_Iset, indicatorH_fst_ae hs0 hs_half 0 1 le_rfl zero_le_one le_rfl] with x hxI hxf
    rw [hxf]
    exact ⟨1, by simp [Iset] at hxI; simp [hxI]⟩
  obtain ⟨γ, hγG, C, hC⟩ := hconn 0 (Gsub s).zero_mem u hu_mem
  have htend1 : Tendsto (fun m : ℕ => (C : ℝ) * (m : ℝ) ^ (-(β : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ((m : ℝ) ^ (β : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop hβ_pos).comp tendsto_natCast_atTop_atTop)
    have h2 : Tendsto (fun m : ℕ => (C : ℝ) * ((m : ℝ) ^ (β : ℝ))⁻¹) atTop (𝓝 ((C : ℝ) * 0)) :=
      h1.const_mul (C : ℝ)
    rw [mul_zero] at h2
    refine h2.congr (fun m => ?_)
    rw [Real.rpow_neg (Nat.cast_nonneg m)]
  have hexp_neg : 1 - (β : ℝ) / (α : ℝ) < 0 := by
    rw [sub_lt_zero, one_lt_div hα_pos]; exact hβ_gt
  have htend2 : Tendsto (fun m : ℕ => (2 : ℝ) ^ (s / (α : ℝ)) * (C : ℝ) ^ (1 / (α : ℝ)) *
      (m : ℝ) ^ (1 - (β : ℝ) / (α : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ((m : ℝ) ^ ((β : ℝ) / (α : ℝ) - 1))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        ((tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop)
    have h2 := h1.const_mul ((2 : ℝ) ^ (s / (α : ℝ)) * (C : ℝ) ^ (1 / (α : ℝ)))
    rw [mul_zero] at h2
    refine h2.congr (fun m => ?_)
    rw [show (1 : ℝ) - (β : ℝ) / (α : ℝ) = -((β : ℝ) / (α : ℝ) - 1) by ring,
      Real.rpow_neg (Nat.cast_nonneg m)]
  have hev1 : ∀ᶠ m : ℕ in atTop, (C : ℝ) * (m : ℝ) ^ (-(β : ℝ)) ≤ 1 / 4 :=
    (htend1.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono (fun _ h => le_of_lt h)
  have hev2 : ∀ᶠ m : ℕ in atTop,
      (2 : ℝ) ^ (s / (α : ℝ)) * (C : ℝ) ^ (1 / (α : ℝ)) * (m : ℝ) ^ (1 - (β : ℝ) / (α : ℝ)) < 1 :=
    htend2.eventually (Iio_mem_nhds zero_lt_one)
  have hev3 : ∀ᶠ m : ℕ in atTop, 1 ≤ m := eventually_ge_atTop 1
  obtain ⟨m, hm1, hm2, hm_ge⟩ := (hev1.and (hev2.and hev3)).exists
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  let pt : Fin (m + 1) → Set.Icc (0 : ℝ) 1 := fun i =>
    ⟨(i : ℝ) / (m : ℝ), div_nonneg (Nat.cast_nonneg _) hm_pos.le,
      (div_le_one hm_pos).mpr (by exact_mod_cast Nat.le_of_lt_succ i.isLt)⟩
  let d : Fin m → Hsub s := fun i => γ (pt i.succ) - γ (pt i.castSucc)
  have hd_mem : ∀ i : Fin m, d i ∈ Gsub s := fun i =>
    (Gsub s).sub_mem (hγG (pt i.succ)) (hγG (pt i.castSucc))
  have hd_norm : ∀ i : Fin m, ‖d i‖ ≤ (C : ℝ) * (m : ℝ) ^ (-(β : ℝ)) := by
    intro i
    have hdist : dist (γ (pt i.succ)) (γ (pt i.castSucc)) ≤
        (C : ℝ) * dist (pt i.succ) (pt i.castSucc) ^ (β : ℝ) :=
      hC.dist_le (pt i.succ) (pt i.castSucc)
    have hstep : dist (pt i.succ) (pt i.castSucc) = (m : ℝ)⁻¹ := by
      rw [Subtype.dist_eq, Real.dist_eq]
      dsimp only [pt, Fin.val_succ, Fin.val_castSucc]
      rw [Nat.cast_add, Nat.cast_one, add_div, add_sub_cancel_left, abs_of_pos (by positivity),
        one_div]
    rw [dist_eq_norm, hstep, Real.inv_rpow hm_pos.le, ← Real.rpow_neg hm_pos.le] at hdist
    exact hdist
  have hd_l1 : ∀ i : Fin m, (∫⁻ x, ENNReal.ofReal (|intRep (d i) x|) ∂μI).toReal ≤
      (2 : ℝ) ^ (s / (α : ℝ)) * (C : ℝ) ^ (1 / (α : ℝ)) * (m : ℝ) ^ (-((β : ℝ) / (α : ℝ))) := by
    intro i
    have hle := l1_le_of_small_norm hα0 hαhalf (hd_mem i) ((hd_norm i).trans hm1)
    refine hle.trans ?_
    have hrp : ‖d i‖ ^ (1 / (α : ℝ)) ≤ ((C : ℝ) * (m : ℝ) ^ (-(β : ℝ))) ^ (1 / (α : ℝ)) :=
      Real.rpow_le_rpow (norm_nonneg _) (hd_norm i) (by positivity)
    rw [Real.mul_rpow (NNReal.coe_nonneg C) (by positivity),
      ← Real.rpow_mul hm_pos.le,
      show -(β : ℝ) * (1 / (α : ℝ)) = -((β : ℝ) / (α : ℝ)) by ring] at hrp
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hrp (by positivity)
  have hsum_d : ∑ i : Fin m, d i = u := by
    have htel := fin_sum_sub m (fun j => γ (pt j))
    rw [show (∑ i : Fin m, d i) = ∑ i : Fin m, (γ (pt i.succ) - γ (pt i.castSucc)) from rfl, htel]
    have hlast : pt (Fin.last m) = 1 := by
      apply Subtype.ext; dsimp [pt]; exact div_self hm_pos.ne'
    have hzero : pt 0 = 0 := by
      apply Subtype.ext; dsimp [pt]; simp
    rw [hlast, hzero, γ.target, γ.source, sub_zero]
  have hae_sum : ∀ᵐ x ∂μI, (1 : ℝ) = ∑ i : Fin m, intRep (d i) x := by
    have h1 : (u.1.fst : ℝ → ℝ) =ᵐ[μI] fun _ => (1 : ℝ) := by
      filter_upwards [ae_mem_Iset, indicatorH_fst_ae hs0 hs_half 0 1 le_rfl zero_le_one le_rfl] with x hxI hxf
      rw [hxf]; simp [Iset] at hxI; simp [hxI]
    have h2 : ((∑ i : Fin m, (d i).1.fst : Lp ℝ 2 μI) : ℝ → ℝ) =ᵐ[μI]
        fun x => ∑ i : Fin m, intRep (d i) x := by
      have hsum_ae := Lp_coeFn_finset_sum (Finset.univ : Finset (Fin m)) (fun i => (d i).1.fst)
      have hall : ∀ᵐ x ∂μI, ∀ i : Fin m, ((d i).1.fst : ℝ → ℝ) x = intRep (d i) x :=
        ae_all_iff.mpr (fun i => intRep_ae_eq (hd_mem i))
      filter_upwards [hsum_ae, hall] with x hxs hallx
      rw [hxs]
      exact Finset.sum_congr rfl (fun i _ => hallx i)
    have hfst_eq : (∑ i : Fin m, (d i).1.fst : Lp ℝ 2 μI) = u.1.fst := by
      have h := congrArg (fun z : Hsub s => z.1.fst) hsum_d
      rw [Hsub_fst_finset_sum] at h
      exact h
    rw [hfst_eq] at h2
    filter_upwards [h1, h2] with x hx1 hx2
    rw [← hx1, hx2]
  have h1_le : (1 : ℝ≥0∞) ≤ ∑ i : Fin m, ∫⁻ x, ENNReal.ofReal (|intRep (d i) x|) ∂μI := by
    calc
      (1 : ℝ≥0∞) = ∫⁻ _, (1 : ℝ≥0∞) ∂μI := by simp [μI_univ]
      _ ≤ ∫⁻ x, ∑ i : Fin m, ENNReal.ofReal (|intRep (d i) x|) ∂μI := by
            apply lintegral_mono_ae
            filter_upwards [hae_sum] with x hx
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
            apply ENNReal.ofReal_le_ofReal
            have habs : (1 : ℝ) = |∑ i : Fin m, intRep (d i) x| := by rw [← hx]; norm_num
            rw [habs]
            exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin m, ∫⁻ x, ENNReal.ofReal (|intRep (d i) x|) ∂μI :=
            lintegral_finsetSum _ (fun i _ => ENNReal.measurable_ofReal.comp (measurable_intRep (d i)).abs)
  have hfin_i : ∀ i : Fin m, ∫⁻ x, ENNReal.ofReal (|intRep (d i) x|) ∂μI ≠ ⊤ := by
    intro i
    have hsq : ∫⁻ x, ENNReal.ofReal (intRep (d i) x ^ 2) ∂μI = ENNReal.ofReal (‖(d i).1.fst‖ ^ 2) := by
      rw [Lp_ofReal_norm_sq_eq_lintegral]
      apply lintegral_congr_ae
      filter_upwards [intRep_ae_eq (hd_mem i)] with x hx; rw [hx]
    have hle : ∫⁻ x, ENNReal.ofReal (|intRep (d i) x|) ∂μI ≤
        ∫⁻ x, ENNReal.ofReal (intRep (d i) x ^ 2) ∂μI + μI Set.univ := by
      have hμ_one : μI Set.univ = ∫⁻ _, (1 : ℝ≥0∞) ∂μI := by simp
      rw [hμ_one, ← lintegral_add_right _ measurable_const]
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (sq_nonneg _) zero_le_one]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [sq_abs (intRep (d i) x), sq_nonneg (|intRep (d i) x| - 1)]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨by rw [hsq]; exact ENNReal.ofReal_ne_top, by rw [μI_univ]; exact ENNReal.one_ne_top⟩) hle
  have h1_real : (1 : ℝ) ≤ ∑ i : Fin m, (∫⁻ x, ENNReal.ofReal (|intRep (d i) x|) ∂μI).toReal := by
    have hto := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _ => hfin_i i)) h1_le
    rw [ENNReal.toReal_one, ENNReal.toReal_sum (fun i _ => hfin_i i)] at hto
    exact hto
  have hsum_bound : ∑ i : Fin m, (∫⁻ x, ENNReal.ofReal (|intRep (d i) x|) ∂μI).toReal ≤
      (2 : ℝ) ^ (s / (α : ℝ)) * (C : ℝ) ^ (1 / (α : ℝ)) * (m : ℝ) ^ (1 - (β : ℝ) / (α : ℝ)) := by
    calc
      ∑ i : Fin m, (∫⁻ x, ENNReal.ofReal (|intRep (d i) x|) ∂μI).toReal
          ≤ ∑ _ : Fin m, ((2 : ℝ) ^ (s / (α : ℝ)) * (C : ℝ) ^ (1 / (α : ℝ)) *
              (m : ℝ) ^ (-((β : ℝ) / (α : ℝ)))) := Finset.sum_le_sum (fun i _ => hd_l1 i)
      _ = (m : ℝ) * ((2 : ℝ) ^ (s / (α : ℝ)) * (C : ℝ) ^ (1 / (α : ℝ)) *
              (m : ℝ) ^ (-((β : ℝ) / (α : ℝ)))) := by simp
      _ = (2 : ℝ) ^ (s / (α : ℝ)) * (C : ℝ) ^ (1 / (α : ℝ)) *
              ((m : ℝ) * (m : ℝ) ^ (-((β : ℝ) / (α : ℝ)))) := by ring
      _ = (2 : ℝ) ^ (s / (α : ℝ)) * (C : ℝ) ^ (1 / (α : ℝ)) *
              (m : ℝ) ^ (1 - (β : ℝ) / (α : ℝ)) := by
            have hm_pow : (m : ℝ) * (m : ℝ) ^ (-((β : ℝ) / (α : ℝ))) =
                (m : ℝ) ^ (1 - (β : ℝ) / (α : ℝ)) := by
              rw [show (1 : ℝ) - (β : ℝ) / (α : ℝ) = 1 + (-((β : ℝ) / (α : ℝ))) by ring,
                Real.rpow_add hm_pos, Real.rpow_one]
            rw [hm_pow]
  linarith

/-! Section 5: Dyadic layer decomposition and weighted level-set summability -/

lemma Hsub_eq_of_fst_ae {s : ℝ} {x y : Hsub s}
    (h : (x.1.fst : ℝ → ℝ) =ᵐ[μI] (y.1.fst : ℝ → ℝ)) : x = y := by
  have hsub : ((x - y).1.fst : ℝ → ℝ) =ᵐ[μI] fun _ => (0 : ℝ) := by
    filter_upwards [Lp.coeFn_sub x.1.fst y.1.fst, h] with t ht1 ht2
    change ((x.1.fst - y.1.fst : Lp ℝ 2 μI) : ℝ → ℝ) t = 0
    simp only [Pi.sub_apply] at ht1
    rw [ht1, ht2, sub_self]
  have hnorm := Hsub_norm_sq_eq (x - y) hsub
  simp only [zero_pow (by norm_num : 2 ≠ 0), sub_self, ENNReal.ofReal_zero, zero_mul,
    lintegral_zero, ENNReal.toReal_zero, add_zero] at hnorm
  have hn0 : ‖x - y‖ = 0 := sq_eq_zero_iff.mp hnorm
  exact sub_eq_zero.mp (norm_eq_zero.mp hn0)

lemma tsum_ofReal_le {v : ℕ → ℝ} (hv0 : ∀ n, 0 ≤ v n) (hv : Summable v) :
    ∑' n, ENNReal.ofReal (v n) ≤ ENNReal.ofReal (∑' n, v n) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => hv0 n)]
  exact ENNReal.ofReal_le_ofReal (hv.sum_le_tsum (Finset.range N) (fun n _ => hv0 n))

lemma summable_and_tsum_toReal_le {u : ℕ → ℝ≥0∞} {C : ℝ} (hC : 0 ≤ C)
    (hle : ∑' n, u n ≤ ENNReal.ofReal C) :
    Summable (fun n => (u n).toReal) ∧ ∑' n, (u n).toReal ≤ C := by
  have hfin : ∀ n, u n ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((ENNReal.le_tsum n).trans hle)
  have hbound : ∀ N : ℕ, ∑ n ∈ Finset.range N, (u n).toReal ≤ C := by
    intro N
    rw [← ENNReal.toReal_sum (fun n _ => hfin n)]
    have hsum_le : ∑ n ∈ Finset.range N, u n ≤ ENNReal.ofReal C :=
      (ENNReal.sum_le_tsum (Finset.range N)).trans hle
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum_le
    rwa [ENNReal.toReal_ofReal hC] at this
  have hsumm : Summable (fun n => (u n).toReal) :=
    summable_of_sum_range_le (fun _ => ENNReal.toReal_nonneg) hbound
  refine ⟨hsumm, le_of_tendsto hsumm.hasSum.tendsto_sum_nat (Eventually.of_forall hbound)⟩

def Mthresh : ℕ → ℝ
  | 0 => 0
  | r + 1 => (2 : ℝ) ^ r

def wLayer : ℕ → ℝ
  | 0 => 1
  | r + 1 => (2 : ℝ) ^ r

lemma Mthresh_nonneg (r : ℕ) : 0 ≤ Mthresh r := by
  cases r <;> simp [Mthresh]

lemma wLayer_nonneg (r : ℕ) : 0 ≤ wLayer r := by
  cases r <;> simp [wLayer]

lemma Mthresh_succ_sub (r : ℕ) : Mthresh (r + 1) - Mthresh r = wLayer r := by
  cases r with
  | zero => simp [Mthresh, wLayer]
  | succ k => simp [Mthresh, wLayer, pow_succ]; ring

lemma Mthresh_le_succ (r : ℕ) : Mthresh r ≤ Mthresh (r + 1) := by
  have := Mthresh_succ_sub r
  have := wLayer_nonneg r
  linarith

lemma Mthresh_mono : Monotone Mthresh :=
  monotone_nat_of_le_succ Mthresh_le_succ

lemma wLayer_le_two_pow (r : ℕ) : wLayer r ≤ (2 : ℝ) ^ r := by
  cases r with
  | zero => simp [wLayer]
  | succ k =>
    simp only [wLayer, pow_succ]
    have : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
    linarith

lemma Mthresh_le_two_wLayer {m : ℕ} (hm : 1 ≤ m) : Mthresh m ≤ 2 * wLayer (m - 1) := by
  rcases m with _ | m
  · omega
  · cases m with
    | zero => simp [Mthresh, wLayer]
    | succ k =>
      simp only [Nat.add_sub_cancel, Mthresh, wLayer, pow_succ]
      linarith [show (0 : ℝ) ≤ (2 : ℝ) ^ k by positivity]

lemma sum_wLayer_range (m : ℕ) : ∑ r ∈ Finset.range m, wLayer r = Mthresh m := by
  induction m with
  | zero => simp [Mthresh]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, ← Mthresh_succ_sub k]
    ring

lemma Mthresh_int (r : ℕ) : ∃ n : ℤ, Mthresh r = (n : ℝ) := by
  cases r with
  | zero => exact ⟨0, by simp [Mthresh]⟩
  | succ k => exact ⟨(2 : ℤ) ^ k, by simp [Mthresh]⟩

lemma exists_Mthresh_ge (C : ℝ) : ∃ N : ℕ, C ≤ Mthresh N := by
  obtain ⟨k, hk⟩ := exists_nat_gt C
  refine ⟨k + 1, ?_⟩
  simp only [Mthresh]
  have h2 : (k : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self (n := k))
  linarith

def clamp (M y : ℝ) : ℝ := max (-M) (min M y)

lemma clamp_zero (y : ℝ) : clamp 0 y = 0 := by
  unfold clamp
  rcases le_total 0 y with h | h
  · rw [min_eq_left h, neg_zero, max_self]
  · rw [min_eq_right h, neg_zero, max_eq_left h]

lemma clamp_neg {M : ℝ} (hM : 0 ≤ M) (y : ℝ) : clamp M (-y) = -clamp M y := by
  unfold clamp
  rcases le_total y (-M) with h1 | h1
  · rw [min_eq_left (by linarith), max_eq_right (by linarith),
      min_eq_right (by linarith), max_eq_left h1, neg_neg]
  · rcases le_total y M with h2 | h2
    · rw [min_eq_right (by linarith), max_eq_right (by linarith),
        min_eq_right h2, max_eq_right h1]
    · rw [min_eq_right (by linarith), max_eq_left (by linarith),
        min_eq_left h2, max_eq_right (by linarith)]

lemma clamp_eq_self_of_abs_le {M y : ℝ} (h : |y| ≤ M) : clamp M y = y := by
  rw [abs_le] at h
  unfold clamp
  rw [min_eq_right h.2, max_eq_right h.1]

lemma clamp_int {M y : ℝ} (hM : ∃ m : ℤ, M = (m : ℝ)) (hy : ∃ n : ℤ, y = (n : ℝ)) :
    ∃ k : ℤ, clamp M y = (k : ℝ) := by
  rcases hM with ⟨m, rfl⟩
  rcases hy with ⟨n, rfl⟩
  refine ⟨max (-m) (min m n), ?_⟩
  unfold clamp
  push_cast
  rfl

lemma clamp_sub_eq_sum_max_min {A B y : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    clamp B y - clamp A y =
      max (-(B - A)) (min 0 (y + A)) + max 0 (min (B - A) (y - A)) := by
  unfold clamp
  by_cases h1 : y ≤ -B
  · rw [min_eq_right (by linarith), max_eq_left h1,
      min_eq_right (by linarith), max_eq_left (by linarith),
      min_eq_right (by linarith), max_eq_left (by linarith),
      min_eq_right (by linarith), max_eq_left (by linarith)]
    ring
  · push Not at h1
    by_cases h2 : y ≤ -A
    · rw [min_eq_right (by linarith), max_eq_right h1.le,
        min_eq_right (by linarith), max_eq_left h2,
        min_eq_right (by linarith), max_eq_right (by linarith),
        min_eq_right (by linarith), max_eq_left (by linarith)]
      ring
    · push Not at h2
      by_cases h3 : y ≤ A
      · rw [min_eq_right (by linarith), max_eq_right h1.le,
          min_eq_right h3, max_eq_right h2.le,
          min_eq_left (by linarith), max_eq_right (by linarith),
          min_eq_right (by linarith), max_eq_left (by linarith)]
        ring
      · push Not at h3
        by_cases h4 : y ≤ B
        · rw [min_eq_right h4, max_eq_right h1.le,
            min_eq_left h3.le, max_eq_right (by linarith),
            min_eq_left (by linarith), max_eq_right (by linarith),
            min_eq_right (by linarith), max_eq_right (by linarith)]
          ring
        · push Not at h4
          rw [min_eq_left h4.le, max_eq_right (by linarith),
            min_eq_left (by linarith), max_eq_right (by linarith),
            min_eq_left (by linarith), max_eq_right (by linarith),
            min_eq_left (by linarith), max_eq_right (by linarith)]
          ring

def phi (r : ℕ) (y : ℝ) : ℝ := clamp (Mthresh (r + 1)) y - clamp (Mthresh r) y

lemma continuous_phi (r : ℕ) : Continuous (phi r) := by
  unfold phi clamp
  fun_prop

lemma measurable_phi (r : ℕ) : Measurable (phi r) :=
  (continuous_phi r).measurable

lemma phi_odd (r : ℕ) (y : ℝ) : phi r (-y) = -phi r y := by
  unfold phi
  rw [clamp_neg (Mthresh_nonneg (r + 1)), clamp_neg (Mthresh_nonneg r)]
  ring

lemma phi_zero (r : ℕ) : phi r 0 = 0 := by
  unfold phi
  rw [clamp_eq_self_of_abs_le (by simp [Mthresh_nonneg]),
    clamp_eq_self_of_abs_le (by simp [Mthresh_nonneg]), sub_self]

lemma phi_mono (r : ℕ) : Monotone (phi r) := by
  intro y₁ y₂ hy
  unfold phi
  rw [clamp_sub_eq_sum_max_min (Mthresh_nonneg r) (Mthresh_le_succ r),
    clamp_sub_eq_sum_max_min (Mthresh_nonneg r) (Mthresh_le_succ r)]
  apply add_le_add
  · exact max_le_max le_rfl (min_le_min le_rfl (by linarith))
  · exact max_le_max le_rfl (min_le_min le_rfl (by linarith))

lemma phi_nonneg_of_nonneg (r : ℕ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ phi r y := by
  rw [← phi_zero r]
  exact phi_mono r hy

lemma phi_int (r : ℕ) {y : ℝ} (hy : ∃ n : ℤ, y = (n : ℝ)) : ∃ m : ℤ, phi r y = (m : ℝ) := by
  obtain ⟨k₁, hk₁⟩ := clamp_int (Mthresh_int (r + 1)) hy
  obtain ⟨k₂, hk₂⟩ := clamp_int (Mthresh_int r) hy
  exact ⟨k₁ - k₂, by unfold phi; push_cast; rw [hk₁, hk₂]⟩

lemma phi_eq_zero_of_abs_le (r : ℕ) {y : ℝ} (h : |y| ≤ Mthresh r) : phi r y = 0 := by
  unfold phi
  rw [clamp_eq_self_of_abs_le (h.trans (Mthresh_le_succ r)),
    clamp_eq_self_of_abs_le h, sub_self]

lemma phi_eq_wLayer_of_ge (r : ℕ) {y : ℝ} (h : Mthresh (r + 1) ≤ y) : phi r y = wLayer r := by
  unfold phi
  rw [clamp_sub_eq_sum_max_min (Mthresh_nonneg r) (Mthresh_le_succ r)]
  have hA := Mthresh_nonneg r
  have hAB := Mthresh_le_succ r
  rw [min_eq_left (by linarith), max_eq_right (by linarith),
    min_eq_left (by linarith), max_eq_right (by linarith), zero_add, Mthresh_succ_sub]

lemma abs_phi_le_wLayer (r : ℕ) (y : ℝ) : |phi r y| ≤ wLayer r := by
  rw [abs_le]
  have hA := Mthresh_nonneg r
  have hAB := Mthresh_le_succ r
  have hw := Mthresh_succ_sub r
  unfold phi
  rw [clamp_sub_eq_sum_max_min hA hAB]
  have h1 : -(Mthresh (r + 1) - Mthresh r) ≤ max (-(Mthresh (r + 1) - Mthresh r)) (min 0 (y + Mthresh r)) :=
    le_max_left _ _
  have h2 : max (-(Mthresh (r + 1) - Mthresh r)) (min 0 (y + Mthresh r)) ≤ 0 :=
    max_le (by linarith) (min_le_left _ _)
  have h3 : 0 ≤ max 0 (min (Mthresh (r + 1) - Mthresh r) (y - Mthresh r)) := le_max_left _ _
  have h4 : max 0 (min (Mthresh (r + 1) - Mthresh r) (y - Mthresh r)) ≤ Mthresh (r + 1) - Mthresh r :=
    max_le (by linarith) (min_le_left _ _)
  constructor <;> linarith

lemma abs_phi_le_two_pow (r : ℕ) (y : ℝ) : |phi r y| ≤ (2 : ℝ) ^ r :=
  (abs_phi_le_wLayer r y).trans (wLayer_le_two_pow r)

lemma abs_phi_eq_wLayer_of_gt (r : ℕ) {y : ℝ} (h : Mthresh (r + 1) < |y|) :
    |phi r y| = wLayer r := by
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy] at h
    rw [phi_eq_wLayer_of_ge r h.le, abs_of_nonneg (wLayer_nonneg r)]
  · rw [abs_of_nonpos hy] at h
    have h1 := phi_eq_wLayer_of_ge r h.le
    rw [phi_odd] at h1
    have h2 : phi r y = -wLayer r := by linarith
    rw [h2, abs_neg, abs_of_nonneg (wLayer_nonneg r)]

lemma abs_phi_le_abs (r : ℕ) (y : ℝ) : |phi r y| ≤ |y| := by
  have hpos : ∀ z : ℝ, 0 ≤ z → |phi r z| ≤ z := by
    intro z hz
    rw [abs_of_nonneg (phi_nonneg_of_nonneg r hz)]
    unfold phi
    rw [clamp_sub_eq_sum_max_min (Mthresh_nonneg r) (Mthresh_le_succ r)]
    have hA := Mthresh_nonneg r
    have hAB := Mthresh_le_succ r
    rw [min_eq_left (by linarith), max_eq_right (by linarith), zero_add]
    exact max_le hz ((min_le_right _ _).trans (by linarith))
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]; exact hpos y hy
  · rw [abs_of_nonpos hy]
    have h1 := hpos (-y) (by linarith)
    rwa [phi_odd, abs_neg] at h1

lemma sum_phi_range (N : ℕ) (y : ℝ) : ∑ r ∈ Finset.range N, phi r y = clamp (Mthresh N) y := by
  induction N with
  | zero => simp [Mthresh, clamp_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    unfold phi
    ring

lemma sum_phi_eq_self {N : ℕ} {y : ℝ} (h : |y| ≤ Mthresh N) :
    ∑ r ∈ Finset.range N, phi r y = y := by
  rw [sum_phi_range, clamp_eq_self_of_abs_le h]

lemma sum_abs_phi_diff_eq {N : ℕ} {y₁ y₂ : ℝ} (h₁ : |y₁| ≤ Mthresh N) (h₂ : |y₂| ≤ Mthresh N) :
    ∑ r ∈ Finset.range N, |phi r y₂ - phi r y₁| = |y₂ - y₁| := by
  rcases le_total y₁ y₂ with hle | hle
  · have hterm : ∀ r ∈ Finset.range N, |phi r y₂ - phi r y₁| = phi r y₂ - phi r y₁ := fun r _ =>
      abs_of_nonneg (sub_nonneg.mpr (phi_mono r hle))
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, sum_phi_eq_self h₂, sum_phi_eq_self h₁,
      abs_of_nonneg (sub_nonneg.mpr hle)]
  · have hterm : ∀ r ∈ Finset.range N, |phi r y₂ - phi r y₁| = phi r y₁ - phi r y₂ := fun r _ => by
      rw [abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr (phi_mono r hle))
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, sum_phi_eq_self h₁, sum_phi_eq_self h₂,
      abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]

lemma finset_sum_sq_le_sq_sum {ι : Type*} (S : Finset ι) {d : ι → ℝ} (hd : ∀ i ∈ S, 0 ≤ d i) :
    ∑ i ∈ S, d i ^ 2 ≤ (∑ i ∈ S, d i) ^ 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have ha0 : 0 ≤ d a := hd a (Finset.mem_insert_self a s)
    have hs0 : 0 ≤ ∑ i ∈ s, d i := Finset.sum_nonneg (fun i hi => hd i (Finset.mem_insert_of_mem hi))
    have hih := ih (fun i hi => hd i (Finset.mem_insert_of_mem hi))
    nlinarith [mul_nonneg ha0 hs0]

lemma tsum_ofReal_phi_diff_sq_le (y₁ y₂ : ℝ) :
    ∑' r : ℕ, ENNReal.ofReal ((phi r y₂ - phi r y₁) ^ 2) ≤ ENNReal.ofReal ((y₂ - y₁) ^ 2) := by
  obtain ⟨N, hN⟩ := exists_Mthresh_ge (max |y₁| |y₂|)
  have h₁ : |y₁| ≤ Mthresh N := (le_max_left _ _).trans hN
  have h₂ : |y₂| ≤ Mthresh N := (le_max_right _ _).trans hN
  have hsupp : ∀ r ∉ Finset.range N, ENNReal.ofReal ((phi r y₂ - phi r y₁) ^ 2) = 0 := by
    intro r hr
    rw [Finset.mem_range, not_lt] at hr
    have hM := Mthresh_mono hr
    rw [phi_eq_zero_of_abs_le r (h₁.trans hM), phi_eq_zero_of_abs_le r (h₂.trans hM)]
    simp
  rw [tsum_eq_sum hsupp, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hsq : ∑ r ∈ Finset.range N, (phi r y₂ - phi r y₁) ^ 2 =
      ∑ r ∈ Finset.range N, |phi r y₂ - phi r y₁| ^ 2 := by
    refine Finset.sum_congr rfl fun r _ => (sq_abs _).symm
  rw [hsq]
  calc
    ∑ r ∈ Finset.range N, |phi r y₂ - phi r y₁| ^ 2
        ≤ (∑ r ∈ Finset.range N, |phi r y₂ - phi r y₁|) ^ 2 :=
          finset_sum_sq_le_sq_sum _ (fun _ _ => abs_nonneg _)
    _ = |y₂ - y₁| ^ 2 := by rw [sum_abs_phi_diff_eq h₁ h₂]
    _ = (y₂ - y₁) ^ 2 := sq_abs _

lemma phi_reverse_quad_nonneg {a b : ℕ} {y₁ y₂ : ℝ} (hy₁ : 0 ≤ y₁) (hy₁₂ : y₁ ≤ y₂) :
    (∑ r ∈ Finset.Ico a b, |phi r y₂ - phi r y₁|) ^ 2 ≤
      5 * ∑ r ∈ Finset.Ico a b, (phi r y₂ - phi r y₁) ^ 2 := by
  classical
  let d : ℕ → ℝ := fun r => |phi r y₂ - phi r y₁|
  have hd_eq : ∀ r, d r = phi r y₂ - phi r y₁ := fun r =>
    abs_of_nonneg (sub_nonneg.mpr (phi_mono r hy₁₂))
  have hd_sq : ∀ r, d r ^ 2 = (phi r y₂ - phi r y₁) ^ 2 := fun r => sq_abs _
  have hd_nonneg : ∀ r, 0 ≤ d r := fun r => abs_nonneg _
  change (∑ r ∈ Finset.Ico a b, d r) ^ 2 ≤ 5 * ∑ r ∈ Finset.Ico a b, (phi r y₂ - phi r y₁) ^ 2
  rw [Finset.sum_congr rfl (fun r _ => (hd_sq r).symm)]
  let S := (Finset.Ico a b).filter (fun r => 0 < d r)
  by_cases hS : S.Nonempty
  · let m := S.max' hS
    have hmS : m ∈ S := Finset.max'_mem S hS
    have hm_mem : m ∈ Finset.Ico a b := (Finset.mem_filter.mp hmS).1
    have hm_pos : 0 < d m := (Finset.mem_filter.mp hmS).2
    have hzero_gt : ∀ r ∈ Finset.Ico a b, m < r → d r = 0 := by
      intro r hr hmr
      by_contra hne
      have hrS : r ∈ S := Finset.mem_filter.mpr ⟨hr, lt_of_le_of_ne (hd_nonneg r) (Ne.symm hne)⟩
      exact not_lt.mpr (Finset.le_max' S r hrS) hmr
    have ham : a ≤ m := (Finset.mem_Ico.mp hm_mem).1
    have hmb : m < b := (Finset.mem_Ico.mp hm_mem).2
    by_cases hma : m = a
    · have hsum_eq : ∑ r ∈ Finset.Ico a b, d r = d m := by
        rw [Finset.sum_eq_single m]
        · intro r hr hrm
          have hgt : m < r := lt_of_le_of_ne (by rw [hma]; exact (Finset.mem_Ico.mp hr).1) (Ne.symm hrm)
          exact hzero_gt r hr hgt
        · intro hm'; exact absurd hm_mem hm'
      have hsq_le : d m ^ 2 ≤ ∑ r ∈ Finset.Ico a b, d r ^ 2 :=
        Finset.single_le_sum (fun r _ => sq_nonneg (d r)) hm_mem
      rw [hsum_eq]
      nlinarith [sq_nonneg (d m)]
    · have ha_lt_m : a < m := lt_of_le_of_ne ham (Ne.symm hma)
      have hm1_mem : m - 1 ∈ Finset.Ico a b := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      have hm1_ne : m - 1 ≠ m := by omega
      have hpair_le : d (m - 1) ^ 2 + d m ^ 2 ≤ ∑ r ∈ Finset.Ico a b, d r ^ 2 := by
        have hsub : ({m - 1, m} : Finset ℕ) ⊆ Finset.Ico a b := by
          intro r hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at hr
          rcases hr with rfl | rfl <;> assumption
        have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => sq_nonneg (d r))
        rwa [Finset.sum_pair hm1_ne] at h1
      by_cases hy1_ge : Mthresh (m - 1) ≤ y₁
      · have hzero_lt : ∀ r ∈ Finset.Ico a b, r < m - 1 → d r = 0 := by
          intro r hr hrl
          have hM : Mthresh (r + 1) ≤ Mthresh (m - 1) := Mthresh_mono (by omega)
          rw [hd_eq, phi_eq_wLayer_of_ge r (hM.trans hy1_ge),
            phi_eq_wLayer_of_ge r (hM.trans (hy1_ge.trans hy₁₂)), sub_self]
        have hsum_eq : ∑ r ∈ Finset.Ico a b, d r = d (m - 1) + d m := by
          have hsub : ({m - 1, m} : Finset ℕ) ⊆ Finset.Ico a b := by
            intro r hr
            simp only [Finset.mem_insert, Finset.mem_singleton] at hr
            rcases hr with rfl | rfl <;> assumption
          rw [← Finset.sum_subset hsub]
          · exact Finset.sum_pair hm1_ne
          · intro r hr hnot
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
            rcases lt_or_gt_of_ne hnot.2 with hlt | hgt
            · exact hzero_lt r hr (by omega)
            · exact hzero_gt r hr hgt
        rw [hsum_eq]
        nlinarith [sq_nonneg (d (m - 1) - d m), sq_nonneg (d (m - 1)), sq_nonneg (d m)]
      · push Not at hy1_ge
        have hy2_gt : Mthresh m < y₂ := by
          by_contra hle
          push Not at hle
          have hy1_le : |y₁| ≤ Mthresh m := by
            rw [abs_of_nonneg hy₁]; exact hy₁₂.trans hle
          have hy2_le : |y₂| ≤ Mthresh m := by
            rw [abs_of_nonneg (hy₁.trans hy₁₂)]; exact hle
          have hm0 : d m = 0 := by
            rw [hd_eq, phi_eq_zero_of_abs_le m hy1_le, phi_eq_zero_of_abs_le m hy2_le, sub_self]
          linarith
        have hdm1 : d (m - 1) = wLayer (m - 1) := by
          have h1 : phi (m - 1) y₁ = 0 :=
            phi_eq_zero_of_abs_le (m - 1) (by rw [abs_of_nonneg hy₁]; exact hy1_ge.le)
          have hm_eq : m - 1 + 1 = m := by omega
          have h2 : phi (m - 1) y₂ = wLayer (m - 1) :=
            phi_eq_wLayer_of_ge (m - 1) (by rw [hm_eq]; exact hy2_gt.le)
          rw [hd_eq, h1, h2, sub_zero]
        have hsum_le : ∑ r ∈ Finset.Ico a b, d r ≤ d m + 2 * d (m - 1) := by
          have hsplit : ∑ r ∈ Finset.Ico a b, d r = (∑ r ∈ Finset.Ico a m, d r) + d m := by
            have hsub : Finset.Ico a (m + 1) ⊆ Finset.Ico a b :=
              Finset.Ico_subset_Ico_right (by omega)
            rw [← Finset.sum_subset hsub]
            · rw [Finset.sum_Ico_succ_top ham]
            · intro r hr hnot
              rw [Finset.mem_Ico] at hr hnot
              have : m < r := by omega
              exact hzero_gt r (Finset.mem_Ico.mpr hr) this
          rw [hsplit]
          have hle_m : ∑ r ∈ Finset.Ico a m, d r ≤ 2 * d (m - 1) := by
            have hdr_le : ∀ r, d r ≤ wLayer r := by
              intro r
              rw [hd_eq]
              have h2 := abs_phi_le_wLayer r y₂
              have h1 := phi_nonneg_of_nonneg r hy₁
              have h2' := phi_nonneg_of_nonneg r (hy₁.trans hy₁₂)
              rw [abs_of_nonneg h2'] at h2
              linarith
            calc
              ∑ r ∈ Finset.Ico a m, d r
                  ≤ ∑ r ∈ Finset.Ico a m, wLayer r := Finset.sum_le_sum (fun r _ => hdr_le r)
              _ ≤ ∑ r ∈ Finset.range m, wLayer r :=
                  Finset.sum_le_sum_of_subset_of_nonneg
                    (fun r hr => Finset.mem_range.mpr (Finset.mem_Ico.mp hr).2)
                    (fun r _ _ => wLayer_nonneg r)
              _ = Mthresh m := sum_wLayer_range m
              _ ≤ 2 * wLayer (m - 1) := Mthresh_le_two_wLayer (by omega)
              _ = 2 * d (m - 1) := by rw [hdm1]
          linarith
        have hsum_nn : 0 ≤ ∑ r ∈ Finset.Ico a b, d r := Finset.sum_nonneg (fun r _ => hd_nonneg r)
        nlinarith [sq_nonneg (2 * d m - d (m - 1)), hpair_le]
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    have hall0 : ∀ r ∈ Finset.Ico a b, d r = 0 := by
      intro r hr
      by_contra hne
      have : r ∈ S := Finset.mem_filter.mpr ⟨hr, lt_of_le_of_ne (hd_nonneg r) (Ne.symm hne)⟩
      rw [hS] at this
      exact Finset.notMem_empty r this
    have hzero : ∑ r ∈ Finset.Ico a b, d r = 0 := Finset.sum_eq_zero hall0
    rw [hzero, zero_pow (by norm_num)]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun r _ => sq_nonneg _))

lemma phi_reverse_quad {a b : ℕ} (y₁ y₂ : ℝ) :
    (∑ r ∈ Finset.Ico a b, |phi r y₂ - phi r y₁|) ^ 2 ≤
      10 * ∑ r ∈ Finset.Ico a b, (phi r y₂ - phi r y₁) ^ 2 := by
  suffices h : ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ →
      (∑ r ∈ Finset.Ico a b, |phi r x₂ - phi r x₁|) ^ 2 ≤
        10 * ∑ r ∈ Finset.Ico a b, (phi r x₂ - phi r x₁) ^ 2 by
    rcases le_total y₁ y₂ with hle | hle
    · exact h y₁ y₂ hle
    · have h1 := h y₂ y₁ hle
      have heq1 : ∑ r ∈ Finset.Ico a b, |phi r y₂ - phi r y₁| =
          ∑ r ∈ Finset.Ico a b, |phi r y₁ - phi r y₂| :=
        Finset.sum_congr rfl (fun r _ => abs_sub_comm _ _)
      have heq2 : ∑ r ∈ Finset.Ico a b, (phi r y₂ - phi r y₁) ^ 2 =
          ∑ r ∈ Finset.Ico a b, (phi r y₁ - phi r y₂) ^ 2 :=
        Finset.sum_congr rfl (fun r _ => by ring)
      rw [heq1, heq2]; exact h1
  intro x₁ x₂ hx₁₂
  by_cases hx1 : 0 ≤ x₁
  · have h5 := phi_reverse_quad_nonneg (a := a) (b := b) hx1 hx₁₂
    have hnn : 0 ≤ ∑ r ∈ Finset.Ico a b, (phi r x₂ - phi r x₁) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    linarith
  · push Not at hx1
    by_cases hx2 : x₂ ≤ 0
    · have h5 := phi_reverse_quad_nonneg (a := a) (b := b) (y₁ := -x₂) (y₂ := -x₁)
        (by linarith) (by linarith)
      have heq1 : ∑ r ∈ Finset.Ico a b, |phi r (-x₁) - phi r (-x₂)| =
          ∑ r ∈ Finset.Ico a b, |phi r x₂ - phi r x₁| := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [phi_odd, phi_odd]
        congr 1; ring
      have heq2 : ∑ r ∈ Finset.Ico a b, (phi r (-x₁) - phi r (-x₂)) ^ 2 =
          ∑ r ∈ Finset.Ico a b, (phi r x₂ - phi r x₁) ^ 2 := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [phi_odd, phi_odd]; ring
      rw [heq1, heq2] at h5
      have hnn : 0 ≤ ∑ r ∈ Finset.Ico a b, (phi r x₂ - phi r x₁) ^ 2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      linarith
    · push Not at hx2
      let u : ℕ → ℝ := fun r => phi r x₂
      let v : ℕ → ℝ := fun r => phi r (-x₁)
      have hu0 : ∀ r, 0 ≤ u r := fun r => phi_nonneg_of_nonneg r hx2.le
      have hv0 : ∀ r, 0 ≤ v r := fun r => phi_nonneg_of_nonneg r (by linarith)
      have hd_eq : ∀ r, |phi r x₂ - phi r x₁| = u r + v r := by
        intro r
        have hodd : phi r x₁ = -v r := by
          have := phi_odd r (-x₁); rw [neg_neg] at this; linarith
        rw [hodd, sub_neg_eq_add, abs_of_nonneg (add_nonneg (hu0 r) (hv0 r))]
      have hsq_eq : ∀ r, (phi r x₂ - phi r x₁) ^ 2 = (u r + v r) ^ 2 := by
        intro r
        have hodd : phi r x₁ = -v r := by
          have := phi_odd r (-x₁); rw [neg_neg] at this; linarith
        rw [hodd, sub_neg_eq_add]
      have h5u := phi_reverse_quad_nonneg (a := a) (b := b) (y₁ := 0) (y₂ := x₂) le_rfl hx2.le
      have h5v := phi_reverse_quad_nonneg (a := a) (b := b) (y₁ := 0) (y₂ := -x₁) le_rfl (by linarith)
      simp only [phi_zero, sub_zero] at h5u h5v
      have h5u' : (∑ r ∈ Finset.Ico a b, u r) ^ 2 ≤ 5 * ∑ r ∈ Finset.Ico a b, u r ^ 2 := by
        have heq : ∑ r ∈ Finset.Ico a b, |u r| = ∑ r ∈ Finset.Ico a b, u r :=
          Finset.sum_congr rfl (fun r _ => abs_of_nonneg (hu0 r))
        rwa [heq] at h5u
      have h5v' : (∑ r ∈ Finset.Ico a b, v r) ^ 2 ≤ 5 * ∑ r ∈ Finset.Ico a b, v r ^ 2 := by
        have heq : ∑ r ∈ Finset.Ico a b, |v r| = ∑ r ∈ Finset.Ico a b, v r :=
          Finset.sum_congr rfl (fun r _ => abs_of_nonneg (hv0 r))
        rwa [heq] at h5v
      have hsum_uv : ∑ r ∈ Finset.Ico a b, (u r ^ 2 + v r ^ 2) ≤
          ∑ r ∈ Finset.Ico a b, (u r + v r) ^ 2 :=
        Finset.sum_le_sum (fun r _ => by nlinarith [mul_nonneg (hu0 r) (hv0 r)])
      rw [Finset.sum_congr rfl (fun r _ => hd_eq r), Finset.sum_congr rfl (fun r _ => hsq_eq r),
        Finset.sum_add_distrib]
      rw [Finset.sum_add_distrib] at hsum_uv
      nlinarith [sq_nonneg ((∑ r ∈ Finset.Ico a b, u r) - (∑ r ∈ Finset.Ico a b, v r))]

lemma phi_block_diff_sq_le {a b : ℕ} (y₁ y₂ : ℝ) :
    ((∑ r ∈ Finset.Ico a b, phi r y₂) - (∑ r ∈ Finset.Ico a b, phi r y₁)) ^ 2 ≤
      10 * ∑ r ∈ Finset.Ico a b, (phi r y₂ - phi r y₁) ^ 2 := by
  have habs : |(∑ r ∈ Finset.Ico a b, phi r y₂) - (∑ r ∈ Finset.Ico a b, phi r y₁)| ≤
      ∑ r ∈ Finset.Ico a b, |phi r y₂ - phi r y₁| := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hsq : ((∑ r ∈ Finset.Ico a b, phi r y₂) - (∑ r ∈ Finset.Ico a b, phi r y₁)) ^ 2 ≤
      (∑ r ∈ Finset.Ico a b, |phi r y₂ - phi r y₁|) ^ 2 := by
    rw [← sq_abs ((∑ r ∈ Finset.Ico a b, phi r y₂) - (∑ r ∈ Finset.Ico a b, phi r y₁))]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  exact hsq.trans (phi_reverse_quad y₁ y₂)

lemma phi_tail_diff_sq_le (a : ℕ) (y₁ y₂ : ℝ) :
    ENNReal.ofReal
      (((y₂ - ∑ r ∈ Finset.range a, phi r y₂) - (y₁ - ∑ r ∈ Finset.range a, phi r y₁)) ^ 2) ≤
      10 * ∑' r : ℕ, ENNReal.ofReal ((phi (a + r) y₂ - phi (a + r) y₁) ^ 2) := by
  obtain ⟨N, hN⟩ := exists_Mthresh_ge (max |y₁| |y₂|)
  let b := max a N
  have hab : a ≤ b := le_max_left a N
  have h₁ : |y₁| ≤ Mthresh b := ((le_max_left _ _).trans hN).trans (Mthresh_mono (le_max_right a N))
  have h₂ : |y₂| ≤ Mthresh b := ((le_max_right _ _).trans hN).trans (Mthresh_mono (le_max_right a N))
  have htail : ∀ y : ℝ, |y| ≤ Mthresh b →
      y - ∑ r ∈ Finset.range a, phi r y = ∑ r ∈ Finset.Ico a b, phi r y := by
    intro y hy
    have h1 : y = ∑ r ∈ Finset.range b, phi r y := (sum_phi_eq_self hy).symm
    rw [← Finset.sum_range_add_sum_Ico _ hab] at h1
    linarith
  rw [htail y₁ h₁, htail y₂ h₂]
  calc
    ENNReal.ofReal (((∑ r ∈ Finset.Ico a b, phi r y₂) - (∑ r ∈ Finset.Ico a b, phi r y₁)) ^ 2)
        ≤ ENNReal.ofReal (10 * ∑ r ∈ Finset.Ico a b, (phi r y₂ - phi r y₁) ^ 2) :=
          ENNReal.ofReal_le_ofReal (phi_block_diff_sq_le y₁ y₂)
    _ = 10 * ∑ r ∈ Finset.Ico a b, ENNReal.ofReal ((phi r y₂ - phi r y₁) ^ 2) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
            ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    _ = 10 * ∑ r ∈ Finset.range (b - a), ENNReal.ofReal ((phi (a + r) y₂ - phi (a + r) y₁) ^ 2) := by
          congr 1
          rw [Finset.sum_Ico_eq_sum_range]
    _ ≤ 10 * ∑' r : ℕ, ENNReal.ofReal ((phi (a + r) y₂ - phi (a + r) y₁) ^ 2) :=
          mul_le_mul_of_nonneg_left (ENNReal.sum_le_tsum _) bot_le

noncomputable def hLayer {s : ℝ} (g : Hsub s) (r : ℕ) (x : ℝ) : ℝ :=
  phi r (intRep g x)

noncomputable def Eset {s : ℝ} (g : Hsub s) (r : ℕ) : Set ℝ :=
  {x ∈ Iset | Mthresh r < |intRep g x|}

noncomputable def σvalE (s : ℝ) (g : Hsub s) (r : ℕ) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal ((hLayer g r p.1 - hLayer g r p.2) ^ 2) * Ks s p ∂μΩ

noncomputable def σval (s : ℝ) (g : Hsub s) (r : ℕ) : ℝ :=
  (σvalE s g r).toReal

lemma measurable_hLayer {s : ℝ} (g : Hsub s) (r : ℕ) : Measurable (hLayer g r) :=
  (measurable_phi r).comp (measurable_intRep g)

lemma measurableSet_Eset {s : ℝ} (g : Hsub s) (r : ℕ) : MeasurableSet (Eset g r) :=
  measurableSet_Iset.inter (measurableSet_lt measurable_const (measurable_intRep g).abs)

lemma hLayer_int {s : ℝ} (g : Hsub s) (r : ℕ) (x : ℝ) :
    ∃ n : ℤ, hLayer g r x = (n : ℝ) :=
  phi_int r (intRep_int g x)

lemma Eset_antitone {s : ℝ} (g : Hsub s) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    Eset g r₂ ⊆ Eset g r₁ := fun _ hx =>
  ⟨hx.1, lt_of_le_of_lt (Mthresh_mono h) hx.2⟩

lemma hLayer_eq_zero_of_not_mem_Eset {s : ℝ} (g : Hsub s) (r : ℕ) {x : ℝ}
    (hxI : x ∈ Iset) (hxE : x ∉ Eset g r) : hLayer g r x = 0 := by
  have hle : |intRep g x| ≤ Mthresh r := by
    by_contra hgt
    push Not at hgt
    exact hxE ⟨hxI, hgt⟩
  exact phi_eq_zero_of_abs_le r hle

lemma hLayer_L2_lt_top {s : ℝ} {g : Hsub s} (hg : g ∈ Gsub s) (r : ℕ) :
    ∫⁻ x, ENNReal.ofReal (hLayer g r x ^ 2) ∂μI < ⊤ := by
  have hle : ∫⁻ x, ENNReal.ofReal (hLayer g r x ^ 2) ∂μI ≤
      ∫⁻ x, ENNReal.ofReal (intRep g x ^ 2) ∂μI := by
    apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    rw [← sq_abs (hLayer g r x), ← sq_abs (intRep g x)]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_phi_le_abs r _) 2
  have hfin : ∫⁻ x, ENNReal.ofReal (intRep g x ^ 2) ∂μI = ENNReal.ofReal (‖g.1.fst‖ ^ 2) := by
    rw [Lp_ofReal_norm_sq_eq_lintegral g.1.fst]
    apply lintegral_congr_ae
    filter_upwards [intRep_ae_eq hg] with x hx; rw [hx]
  exact lt_of_le_of_lt hle (by rw [hfin]; exact ENNReal.ofReal_lt_top)

lemma tsum_σvalE_le {s : ℝ} {g : Hsub s} (hg : g ∈ Gsub s) :
    ∑' r : ℕ, σvalE s g r ≤ ENNReal.ofReal (‖g.1.snd‖ ^ 2) := by
  have hm : ∀ r : ℕ, AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal ((hLayer g r p.1 - hLayer g r p.2) ^ 2) * Ks s p) μΩ :=
    fun r => ((ENNReal.measurable_ofReal.comp
      (((measurable_hLayer g r).comp measurable_fst).sub
        ((measurable_hLayer g r).comp measurable_snd) |>.pow_const 2)).mul
      (measurable_Ks s)).aemeasurable
  have hsem : ∫⁻ p, ENNReal.ofReal ((intRep g p.1 - intRep g p.2) ^ 2) * Ks s p ∂μΩ =
      ENNReal.ofReal (‖g.1.snd‖ ^ 2) := by
    rw [Lp_ofReal_norm_sq_eq_lintegral g.1.snd]
    have haesm : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((g.1.snd : ℝ × ℝ → ℝ) p ^ 2)) μΩ :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (((Lp.aestronglyMeasurable g.1.snd).aemeasurable.mono_ac (μΩ_absolutelyContinuous_μ₂ s)).pow_const 2)
    change _ = ∫⁻ p, ENNReal.ofReal ((g.1.snd : ℝ × ℝ → ℝ) p ^ 2) ∂(μΩ.withDensity (Ks s))
    rw [lintegral_withDensity_eq_lintegral_mul₀ (measurable_Ks s).aemeasurable haesm]
    have hF : (g.1.snd : ℝ × ℝ → ℝ) =ᵐ[μΩ] fun p => intRep g p.1 - intRep g p.2 := by
      have h1 := Measure.quasiMeasurePreserving_fst (μ := μI) (ν := μI) |>.ae (intRep_ae_eq hg)
      have h2 := Measure.quasiMeasurePreserving_snd (μ := μI) (ν := μI) |>.ae (intRep_ae_eq hg)
      filter_upwards [g.2, h1, h2] with p hgp h1p h2p
      rw [hgp, h1p, h2p]
    apply lintegral_congr_ae
    filter_upwards [hF] with p hp
    simp only [Pi.mul_apply]
    rw [hp, mul_comm]
  rw [← hsem]
  unfold σvalE
  rw [← lintegral_tsum hm]
  apply lintegral_mono
  intro p
  dsimp only
  rw [ENNReal.tsum_mul_right]
  exact mul_le_mul_of_nonneg_right (tsum_ofReal_phi_diff_sq_le (intRep g p.2) (intRep g p.1)) bot_le

lemma σvalE_lt_top {s : ℝ} {g : Hsub s} (hg : g ∈ Gsub s) (r : ℕ) : σvalE s g r < ⊤ :=
  lt_of_le_of_lt ((ENNReal.le_tsum r).trans (tsum_σvalE_le hg)) ENNReal.ofReal_lt_top

lemma summable_σval_and_tsum_le {s : ℝ} {g : Hsub s} (hg : g ∈ Gsub s) :
    Summable (σval s g) ∧ ∑' r, σval s g r ≤ ‖g.1.snd‖ ^ 2 :=
  summable_and_tsum_toReal_le (sq_nonneg _) (tsum_σvalE_le hg)

noncomputable def hLayerH {s : ℝ} (g : Hsub s) (hg : g ∈ Gsub s) (r : ℕ) : Hsub s :=
  mkH (hLayer g r) (measurable_hLayer g r) (hLayer_L2_lt_top hg r) (σvalE_lt_top hg r)

lemma hLayerH_fst_ae {s : ℝ} (g : Hsub s) (hg : g ∈ Gsub s) (r : ℕ) :
    ((hLayerH g hg r).1.fst : ℝ → ℝ) =ᵐ[μI] hLayer g r :=
  mkH_fst_ae _ _ _ _

lemma hLayerH_mem_Gsub {s : ℝ} (g : Hsub s) (hg : g ∈ Gsub s) (r : ℕ) :
    hLayerH g hg r ∈ Gsub s := by
  filter_upwards [hLayerH_fst_ae g hg r] with x hx
  rw [hx]
  obtain ⟨n, hn⟩ := hLayer_int g r x
  exact ⟨n, hn.symm⟩

lemma hLayerH_norm_sq_eq {s : ℝ} (g : Hsub s) (hg : g ∈ Gsub s) (r : ℕ) :
    ‖hLayerH g hg r‖ ^ 2 = (∫⁻ x, ENNReal.ofReal (hLayer g r x ^ 2) ∂μI).toReal + σval s g r :=
  Hsub_norm_sq_eq (hLayerH g hg r) (hLayerH_fst_ae g hg r)

lemma hBlock_norm_sq_le {s : ℝ} (g : Hsub s) (hg : g ∈ Gsub s) (a b : ℕ) :
    ‖∑ r ∈ Finset.Ico a b, hLayerH g hg r‖ ^ 2 ≤
      10 * ∑ r ∈ Finset.Ico a b, ‖hLayerH g hg r‖ ^ 2 := by
  have hae : ((∑ r ∈ Finset.Ico a b, hLayerH g hg r : Hsub s).1.fst : ℝ → ℝ) =ᵐ[μI]
      fun x => ∑ r ∈ Finset.Ico a b, hLayer g r x := by
    rw [Hsub_fst_finset_sum]
    have hsum := Lp_coeFn_finset_sum (Finset.Ico a b) (fun r => (hLayerH g hg r).1.fst)
    have hall : ∀ᵐ x ∂μI, ∀ r ∈ Finset.Ico a b, ((hLayerH g hg r).1.fst : ℝ → ℝ) x = hLayer g r x :=
      (ae_ball_iff (Finset.Ico a b).countable_toSet).mpr (fun r _ => hLayerH_fst_ae g hg r)
    filter_upwards [hsum, hall] with x hxs hallx
    rw [hxs]
    exact Finset.sum_congr rfl (fun r hr => hallx r hr)
  rw [Hsub_norm_sq_eq _ hae]
  have hL2 : (∫⁻ x, ENNReal.ofReal ((∑ r ∈ Finset.Ico a b, hLayer g r x) ^ 2) ∂μI).toReal ≤
      10 * ∑ r ∈ Finset.Ico a b, (∫⁻ x, ENNReal.ofReal (hLayer g r x ^ 2) ∂μI).toReal := by
    have hle : ∫⁻ x, ENNReal.ofReal ((∑ r ∈ Finset.Ico a b, hLayer g r x) ^ 2) ∂μI ≤
        10 * ∑ r ∈ Finset.Ico a b, ∫⁻ x, ENNReal.ofReal (hLayer g r x ^ 2) ∂μI := by
      have hm1 : ∀ r ∈ Finset.Ico a b, Measurable (fun x : ℝ => ENNReal.ofReal (hLayer g r x ^ 2)) :=
        fun r _ => ENNReal.measurable_ofReal.comp ((measurable_hLayer g r).pow_const 2)
      rw [← lintegral_finsetSum (Finset.Ico a b) hm1,
        ← lintegral_const_mul (10 : ℝ≥0∞) (Finset.measurable_sum _ hm1)]
      apply lintegral_mono
      intro x
      have h0 := phi_block_diff_sq_le (a := a) (b := b) 0 (intRep g x)
      simp only [phi_zero, Finset.sum_const_zero, sub_zero] at h0
      calc
        ENNReal.ofReal ((∑ r ∈ Finset.Ico a b, hLayer g r x) ^ 2)
            ≤ ENNReal.ofReal (10 * ∑ r ∈ Finset.Ico a b, hLayer g r x ^ 2) :=
              ENNReal.ofReal_le_ofReal h0
        _ = 10 * ∑ r ∈ Finset.Ico a b, ENNReal.ofReal (hLayer g r x ^ 2) := by
              rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
                ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    have hfin : (10 : ℝ≥0∞) * ∑ r ∈ Finset.Ico a b, ∫⁻ x, ENNReal.ofReal (hLayer g r x ^ 2) ∂μI ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.sum_ne_top.mpr (fun r _ => (hLayer_L2_lt_top hg r).ne))
    have hto := ENNReal.toReal_mono hfin hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_sum (fun r _ => (hLayer_L2_lt_top hg r).ne)] at hto
    exact hto
  have hsem : (∫⁻ p, ENNReal.ofReal
        (((∑ r ∈ Finset.Ico a b, hLayer g r p.1) - (∑ r ∈ Finset.Ico a b, hLayer g r p.2)) ^ 2) *
          Ks s p ∂μΩ).toReal ≤
      10 * ∑ r ∈ Finset.Ico a b, σval s g r := by
    have hle : ∫⁻ p, ENNReal.ofReal
          (((∑ r ∈ Finset.Ico a b, hLayer g r p.1) - (∑ r ∈ Finset.Ico a b, hLayer g r p.2)) ^ 2) *
            Ks s p ∂μΩ ≤
        10 * ∑ r ∈ Finset.Ico a b, σvalE s g r := by
      have hm1 : ∀ r ∈ Finset.Ico a b, Measurable
          (fun p : ℝ × ℝ => ENNReal.ofReal ((hLayer g r p.1 - hLayer g r p.2) ^ 2) * Ks s p) :=
        fun r _ => (ENNReal.measurable_ofReal.comp
          (((measurable_hLayer g r).comp measurable_fst).sub
            ((measurable_hLayer g r).comp measurable_snd) |>.pow_const 2)).mul (measurable_Ks s)
      unfold σvalE
      rw [← lintegral_finsetSum (Finset.Ico a b) hm1,
        ← lintegral_const_mul (10 : ℝ≥0∞) (Finset.measurable_sum _ hm1)]
      apply lintegral_mono
      intro p
      have h0 := phi_block_diff_sq_le (a := a) (b := b) (intRep g p.2) (intRep g p.1)
      calc
        ENNReal.ofReal
            (((∑ r ∈ Finset.Ico a b, hLayer g r p.1) - (∑ r ∈ Finset.Ico a b, hLayer g r p.2)) ^ 2) *
              Ks s p
            ≤ ENNReal.ofReal (10 * ∑ r ∈ Finset.Ico a b, (hLayer g r p.1 - hLayer g r p.2) ^ 2) *
                Ks s p :=
              mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h0) bot_le
        _ = 10 * ∑ r ∈ Finset.Ico a b, ENNReal.ofReal ((hLayer g r p.1 - hLayer g r p.2) ^ 2) *
              Ks s p := by
              rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
                ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _), mul_assoc, Finset.sum_mul]
    have hfin : (10 : ℝ≥0∞) * ∑ r ∈ Finset.Ico a b, σvalE s g r ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.sum_ne_top.mpr (fun r _ => (σvalE_lt_top hg r).ne))
    have hto := ENNReal.toReal_mono hfin hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_sum (fun r _ => (σvalE_lt_top hg r).ne)] at hto
    exact hto
  have hsum_eq : ∑ r ∈ Finset.Ico a b, ‖hLayerH g hg r‖ ^ 2 =
      (∑ r ∈ Finset.Ico a b, (∫⁻ x, ENNReal.ofReal (hLayer g r x ^ 2) ∂μI).toReal) +
      (∑ r ∈ Finset.Ico a b, σval s g r) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r _ => hLayerH_norm_sq_eq g hg r)
  rw [hsum_eq]
  linarith

lemma hTail_norm_sq_le {s : ℝ} (g : Hsub s) (hg : g ∈ Gsub s)
    (hsumm : Summable (fun r => ‖hLayerH g hg r‖ ^ 2)) (a : ℕ) :
    ‖g - ∑ r ∈ Finset.range a, hLayerH g hg r‖ ^ 2 ≤
      10 * ∑' r : ℕ, ‖hLayerH g hg (a + r)‖ ^ 2 := by
  have hae : ((g - ∑ r ∈ Finset.range a, hLayerH g hg r : Hsub s).1.fst : ℝ → ℝ) =ᵐ[μI]
      fun x => intRep g x - ∑ r ∈ Finset.range a, hLayer g r x := by
    have hsub_ae := Lp.coeFn_sub g.1.fst (∑ r ∈ Finset.range a, hLayerH g hg r).1.fst
    rw [Hsub_fst_finset_sum] at hsub_ae
    have hsum := Lp_coeFn_finset_sum (Finset.range a) (fun r => (hLayerH g hg r).1.fst)
    have hall : ∀ᵐ x ∂μI, ∀ r ∈ Finset.range a, ((hLayerH g hg r).1.fst : ℝ → ℝ) x = hLayer g r x :=
      (ae_ball_iff (Finset.range a).countable_toSet).mpr (fun r _ => hLayerH_fst_ae g hg r)
    filter_upwards [hsub_ae, intRep_ae_eq hg, hsum, hall] with x hxs hxg hxs2 hallx
    change ((g.1.fst - (∑ r ∈ Finset.range a, hLayerH g hg r).1.fst : Lp ℝ 2 μI) : ℝ → ℝ) x = _
    rw [Hsub_fst_finset_sum]
    simp only [Pi.sub_apply] at hxs
    rw [hxs, hxg, hxs2]
    congr 1
    exact Finset.sum_congr rfl (fun r hr => hallx r hr)
  have hnorm_eq := Hsub_norm_sq_eq (g - ∑ r ∈ Finset.range a, hLayerH g hg r) hae
  have htail_summ : Summable (fun r => ‖hLayerH g hg (a + r)‖ ^ 2) := by
    have h1 := (summable_nat_add_iff a).mpr hsumm
    simpa [add_comm] using h1
  have hL2E : ∫⁻ x, ENNReal.ofReal ((intRep g x - ∑ r ∈ Finset.range a, hLayer g r x) ^ 2) ∂μI ≤
      10 * ∑' r : ℕ, ∫⁻ x, ENNReal.ofReal (hLayer g (a + r) x ^ 2) ∂μI := by
    have hm : ∀ r : ℕ, AEMeasurable (fun x : ℝ => ENNReal.ofReal (hLayer g (a + r) x ^ 2)) μI :=
      fun r => (ENNReal.measurable_ofReal.comp ((measurable_hLayer g (a + r)).pow_const 2)).aemeasurable
    rw [← lintegral_tsum hm, ← lintegral_const_mul'' (10 : ℝ≥0∞) (AEMeasurable.tsum hm)]
    apply lintegral_mono
    intro x
    have h0 := phi_tail_diff_sq_le a 0 (intRep g x)
    simp only [phi_zero, Finset.sum_const_zero, sub_zero] at h0
    exact h0
  have hsemE : ∫⁻ p, ENNReal.ofReal
        (((intRep g p.1 - ∑ r ∈ Finset.range a, hLayer g r p.1) -
          (intRep g p.2 - ∑ r ∈ Finset.range a, hLayer g r p.2)) ^ 2) * Ks s p ∂μΩ ≤
      10 * ∑' r : ℕ, σvalE s g (a + r) := by
    have hm : ∀ r : ℕ, AEMeasurable
        (fun p : ℝ × ℝ => ENNReal.ofReal ((hLayer g (a + r) p.1 - hLayer g (a + r) p.2) ^ 2) *
          Ks s p) μΩ :=
      fun r => ((ENNReal.measurable_ofReal.comp
        (((measurable_hLayer g (a + r)).comp measurable_fst).sub
          ((measurable_hLayer g (a + r)).comp measurable_snd) |>.pow_const 2)).mul
        (measurable_Ks s)).aemeasurable
    unfold σvalE
    rw [← lintegral_tsum hm, ← lintegral_const_mul'' (10 : ℝ≥0∞) (AEMeasurable.tsum hm)]
    apply lintegral_mono
    intro p
    dsimp only
    rw [ENNReal.tsum_mul_right, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (phi_tail_diff_sq_le a (intRep g p.2) (intRep g p.1)) bot_le
  have hcomb : (∫⁻ x, ENNReal.ofReal ((intRep g x - ∑ r ∈ Finset.range a, hLayer g r x) ^ 2) ∂μI) +
      (∫⁻ p, ENNReal.ofReal
        (((intRep g p.1 - ∑ r ∈ Finset.range a, hLayer g r p.1) -
          (intRep g p.2 - ∑ r ∈ Finset.range a, hLayer g r p.2)) ^ 2) * Ks s p ∂μΩ) ≤
      ENNReal.ofReal (10 * ∑' r : ℕ, ‖hLayerH g hg (a + r)‖ ^ 2) := by
    calc
      _ ≤ 10 * (∑' r : ℕ, ∫⁻ x, ENNReal.ofReal (hLayer g (a + r) x ^ 2) ∂μI) +
            10 * (∑' r : ℕ, σvalE s g (a + r)) := add_le_add hL2E hsemE
      _ = 10 * ∑' r : ℕ, ((∫⁻ x, ENNReal.ofReal (hLayer g (a + r) x ^ 2) ∂μI) +
            σvalE s g (a + r)) := by
            rw [← mul_add, ← ENNReal.tsum_add]
      _ = 10 * ∑' r : ℕ, ENNReal.ofReal (‖hLayerH g hg (a + r)‖ ^ 2) := by
            congr 1; refine tsum_congr fun r => ?_
            rw [hLayerH_norm_sq_eq g hg (a + r)]
            dsimp only [σval]
            rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
              ENNReal.ofReal_toReal (hLayer_L2_lt_top hg (a + r)).ne,
              ENNReal.ofReal_toReal (σvalE_lt_top hg (a + r)).ne]
      _ ≤ 10 * ENNReal.ofReal (∑' r : ℕ, ‖hLayerH g hg (a + r)‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (tsum_ofReal_le (fun _ => sq_nonneg _) htail_summ) bot_le
      _ = ENNReal.ofReal (10 * ∑' r : ℕ, ‖hLayerH g hg (a + r)‖ ^ 2) := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have h1fin : ∫⁻ x, ENNReal.ofReal ((intRep g x - ∑ r ∈ Finset.range a, hLayer g r x) ^ 2) ∂μI ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hcomb)
  have h2fin : ∫⁻ p, ENNReal.ofReal
      (((intRep g p.1 - ∑ r ∈ Finset.range a, hLayer g r p.1) -
        (intRep g p.2 - ∑ r ∈ Finset.range a, hLayer g r p.2)) ^ 2) * Ks s p ∂μΩ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_add_self.trans hcomb)
  have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcomb
  rw [ENNReal.toReal_add h1fin h2fin,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (tsum_nonneg (fun _ => sq_nonneg _)))] at hto
  rw [hnorm_eq]
  exact hto

noncomputable def aSeq (α : NNReal) (g : Hsub (sVal α)) (r : ℕ) : ℝ :=
  (2 : ℝ) ^ ((r : ℝ) / (α : ℝ)) * (μI (Eset g r)).toReal

lemma aSeq_nonneg (α : NNReal) (g : Hsub (sVal α)) (r : ℕ) : 0 ≤ aSeq α g r :=
  mul_nonneg (by positivity) ENNReal.toReal_nonneg

lemma sum_rpow_le_rpow_sum {ι : Type*} (S : Finset ι) {u : ι → ℝ} (hu : ∀ i ∈ S, 0 ≤ u i)
    {p : ℝ} (hp : 1 ≤ p) :
    ∑ i ∈ S, u i ^ p ≤ (∑ i ∈ S, u i) ^ p := by
  set T := ∑ i ∈ S, u i
  have hT : 0 ≤ T := Finset.sum_nonneg hu
  by_cases hT0 : T = 0
  · have hall : ∀ i ∈ S, u i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hu).mp hT0
    have hsum0 : ∑ i ∈ S, u i ^ p = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hall i hi, Real.zero_rpow (by linarith)])
    rw [hsum0, hT0, Real.zero_rpow (by linarith)]
  · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
    have hdiv : ∀ i ∈ S, u i ^ p / T ^ p ≤ u i / T := by
      intro i hi
      rw [← Real.div_rpow (hu i hi) hTpos.le]
      have hle1 : u i / T ≤ 1 := (div_le_one hTpos).mpr (Finset.single_le_sum hu hi)
      have hnn : 0 ≤ u i / T := div_nonneg (hu i hi) hTpos.le
      exact Real.rpow_le_self_of_le_one hnn hle1 hp
    have hsum_div : (∑ i ∈ S, u i ^ p) / T ^ p ≤ 1 := by
      rw [Finset.sum_div]
      calc
        ∑ i ∈ S, u i ^ p / T ^ p ≤ ∑ i ∈ S, u i / T := Finset.sum_le_sum hdiv
        _ = (∑ i ∈ S, u i) / T := by rw [Finset.sum_div]
        _ = 1 := div_self hTpos.ne'
    exact (div_le_one (Real.rpow_pos_of_pos hTpos p)).mp hsum_div

lemma summable_aSeq {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    {g : Hsub (sVal α)} (hg : g ∈ Gsub (sVal α)) :
    Summable (aSeq α g) := by
  let s := sVal α
  have hα_pos : (0 : ℝ) < (α : ℝ) := NNReal.coe_pos.mpr hα0
  have hα_lt : (α : ℝ) < 1 / 2 := by exact_mod_cast hαhalf
  have hs0 : 0 < s := by dsimp [s, sVal]; linarith
  have h2αs : 2 * (α : ℝ) + 2 * s = 1 := by dsimp [s, sVal]; ring
  have hmarkov : ∀ r : ℕ, 1 ≤ r →
      (μI (Eset g r)).toReal ≤ ‖g.1.fst‖ ^ 2 / (Mthresh r) ^ 2 := by
    intro r hr
    have hMpos : 0 < Mthresh r := by
      rcases r with _ | k
      · omega
      · simp [Mthresh]
    have h1 : ENNReal.ofReal (Mthresh r ^ 2) * μI (Eset g r) ≤
        ENNReal.ofReal (‖g.1.fst‖ ^ 2) := by
      have hsq : ∫⁻ x, ENNReal.ofReal (intRep g x ^ 2) ∂μI = ENNReal.ofReal (‖g.1.fst‖ ^ 2) := by
        rw [Lp_ofReal_norm_sq_eq_lintegral g.1.fst]
        apply lintegral_congr_ae
        filter_upwards [intRep_ae_eq hg] with x hx; rw [hx]
      rw [← hsq, ← setLIntegral_const]
      refine (setLIntegral_mono' (measurableSet_Eset g r) ?_).trans (setLIntegral_le_lintegral _ _)
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      rw [← sq_abs (intRep g x)]
      exact pow_le_pow_left₀ hMpos.le hx.2.le 2
    have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_ofReal (sq_nonneg _)] at hto
    exact (le_div_iff₀' (sq_pos_of_pos hMpos)).mpr hto
  have hex_r0 : ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r ≥ r₀, (μI (Eset g r)).toReal ≤ 1 / 4 := by
    obtain ⟨k, hk⟩ := exists_nat_gt (4 * ‖g.1.fst‖ ^ 2)
    refine ⟨k + 1, by omega, fun r hr => ?_⟩
    have hmr := hmarkov r (by omega)
    have hMge : (k : ℝ) ≤ Mthresh r ^ 2 := by
      rcases r with _ | m
      · omega
      · simp only [Mthresh]
        have h1 : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : k ≤ m)
        have h2 : (m : ℝ) ≤ (2 : ℝ) ^ m := by
          exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self (n := m))
        have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
        nlinarith
    have hMpos : 0 < Mthresh r ^ 2 := by
      rcases r with _ | m
      · omega
      · simp [Mthresh]
    refine hmr.trans ?_
    rw [div_le_div_iff₀ hMpos (by norm_num : (0 : ℝ) < 4)]
    linarith
  obtain ⟨r₀, hr₀_ge, hr₀_le⟩ := hex_r0
  let Kα : ℝ := 2 * (α : ℝ) * (2 : ℝ) ^ ((1 / (α : ℝ) + 2 + 4 * s) / (2 * (α : ℝ)))
  have hKα_nn : 0 ≤ Kα := by positivity
  have hrec : ∀ r : ℕ, r₀ ≤ r →
      aSeq α g (r + 1) ≤ Kα * (σval s g r) ^ (1 / (2 * (α : ℝ))) + (1 / 2) * aSeq α g r := by
    intro r hr
    have hr1 : 1 ≤ r := le_trans hr₀_ge hr
    set δ := (μI (Eset g r)).toReal
    by_cases hδ0 : δ = 0
    · have hμ0 : μI (Eset g r) = 0 :=
        ((ENNReal.toReal_eq_zero_iff _).mp hδ0).resolve_right (measure_ne_top _ _)
      have hμ1 : μI (Eset g (r + 1)) = 0 :=
        measure_mono_null (Eset_antitone g (Nat.le_succ r)) hμ0
      have ha1 : aSeq α g (r + 1) = 0 := by simp [aSeq, hμ1]
      rw [ha1]
      have hσ_nn : 0 ≤ σval s g r := ENNReal.toReal_nonneg
      have ha_nn : 0 ≤ aSeq α g r := aSeq_nonneg α g r
      positivity
    · have hδ_pos : 0 < δ := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hδ0)
      have hδ_le : δ ≤ 1 / 4 := hr₀_le r hr
      have hσ_ge : (2 : ℝ) ^ (-(2 + 2 * s)) * (2 : ℝ) ^ (2 * r) * (μI (Eset g (r + 1))).toReal *
          δ ^ (-2 * s) ≤ σval s g r := by
        let A₁ := Eset g (r + 1)
        let A₂ := Iset \ Eset g r
        have hA₁ : MeasurableSet A₁ := measurableSet_Eset g (r + 1)
        have hA₂ : MeasurableSet A₂ := measurableSet_Iset.diff (measurableSet_Eset g r)
        have hdisj : Disjoint (A₁ ×ˢ A₂) (A₂ ×ˢ A₁) := by
          rw [Set.disjoint_left]
          intro p hp1 hp2
          exact hp1.2.2 (Eset_antitone g (Nat.le_succ r) hp2.2)
        have hmeas_fun : Measurable
            (fun p : ℝ × ℝ => ENNReal.ofReal ((hLayer g r p.1 - hLayer g r p.2) ^ 2) * Ks s p) :=
          (ENNReal.measurable_ofReal.comp
            (((measurable_hLayer g r).comp measurable_fst).sub
              ((measurable_hLayer g r).comp measurable_snd) |>.pow_const 2)).mul (measurable_Ks s)
        have hw_eq : wLayer r = (2 : ℝ) ^ (r - 1) := by
          rcases r with _ | k
          · omega
          · simp [wLayer]
        have h1_term : ENNReal.ofReal (((2 : ℝ) ^ (r - 1)) ^ 2 *
              ((2 : ℝ) ^ (-(1 + 2 * s)) * δ ^ (-2 * s))) * μI A₁ ≤
            ∫⁻ p in A₁ ×ˢ A₂,
              ENNReal.ofReal ((hLayer g r p.1 - hLayer g r p.2) ^ 2) * Ks s p ∂μΩ := by
          have hton : ∫⁻ p in A₁ ×ˢ A₂,
                ENNReal.ofReal ((hLayer g r p.1 - hLayer g r p.2) ^ 2) * Ks s p ∂μΩ =
              ∫⁻ x in A₁, ENNReal.ofReal (((2 : ℝ) ^ (r - 1)) ^ 2) *
                (∫⁻ y in A₂, Ks s (x, y) ∂μI) ∂μI := by
            rw [← lintegral_indicator (hA₁.prod hA₂),
              μΩ, lintegral_prod _ (hmeas_fun.indicator (hA₁.prod hA₂)).aemeasurable,
              ← lintegral_indicator hA₁]
            apply lintegral_congr
            intro x
            by_cases hx : x ∈ A₁
            · simp only [Set.indicator_of_mem hx]
              have hm_y : Measurable (fun y : ℝ => A₂.indicator (fun y => Ks s (x, y)) y) :=
                ((measurable_Ks s).comp (measurable_const.prodMk measurable_id)).indicator hA₂
              rw [← lintegral_indicator hA₂, ← lintegral_const_mul _ hm_y]
              apply lintegral_congr
              intro y
              by_cases hy : y ∈ A₂
              · have hfx : |hLayer g r x| = (2 : ℝ) ^ (r - 1) := by
                  rw [← hw_eq]; exact abs_phi_eq_wLayer_of_gt r hx.2
                have hfy : hLayer g r y = 0 := hLayer_eq_zero_of_not_mem_Eset g r hy.1 hy.2
                have hdiff : (hLayer g r x - hLayer g r y) ^ 2 = ((2 : ℝ) ^ (r - 1)) ^ 2 := by
                  rw [hfy, sub_zero, ← sq_abs, hfx]
                simp [hx, hy, hdiff]
              · simp [hx, hy]
            · simp [hx]
          rw [hton, ← setLIntegral_const]
          apply setLIntegral_mono' hA₁
          intro x hx
          rw [ENNReal.ofReal_mul (sq_nonneg _)]
          exact mul_le_mul_of_nonneg_left
            (isoperimetric_1d hs0 (measurableSet_Eset g r) hδ_pos hδ_le hx.1) bot_le
        have h2_term : ∫⁻ p in A₂ ×ˢ A₁,
              ENNReal.ofReal ((hLayer g r p.1 - hLayer g r p.2) ^ 2) * Ks s p ∂μΩ =
            ∫⁻ p in A₁ ×ˢ A₂,
              ENNReal.ofReal ((hLayer g r p.1 - hLayer g r p.2) ^ 2) * Ks s p ∂μΩ := by
          have hmp : MeasurePreserving Prod.swap μΩ μΩ := Measure.measurePreserving_swap
          rw [← lintegral_indicator (hA₂.prod hA₁), ← lintegral_indicator (hA₁.prod hA₂),
            ← hmp.lintegral_comp (hmeas_fun.indicator (hA₁.prod hA₂))]
          apply lintegral_congr
          intro p
          by_cases h : p.swap ∈ A₁ ×ˢ A₂
          · have h' : p ∈ A₂ ×ˢ A₁ := ⟨h.2, h.1⟩
            simp only [Set.indicator_of_mem h, Set.indicator_of_mem h',
              Prod.fst_swap, Prod.snd_swap, Ks_symm]
            congr 2; ring
          · have h' : p ∉ A₂ ×ˢ A₁ := fun hp => h ⟨hp.2, hp.1⟩
            simp [h, h']
        have hsumE : ∫⁻ p in A₁ ×ˢ A₂,
              ENNReal.ofReal ((hLayer g r p.1 - hLayer g r p.2) ^ 2) * Ks s p ∂μΩ +
            ∫⁻ p in A₂ ×ˢ A₁,
              ENNReal.ofReal ((hLayer g r p.1 - hLayer g r p.2) ^ 2) * Ks s p ∂μΩ ≤
            σvalE s g r := by
          unfold σvalE
          rw [← lintegral_union (hA₂.prod hA₁) hdisj]
          exact setLIntegral_le_lintegral _ _
        rw [h2_term] at hsumE
        have hcombE := (add_le_add h1_term h1_term).trans hsumE
        have hto := ENNReal.toReal_mono (σvalE_lt_top hg r).ne hcombE
        rw [ENNReal.toReal_add
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hto
        have hpow_alg : 2 * (((2 : ℝ) ^ (r - 1)) ^ 2 * ((2 : ℝ) ^ (-(1 + 2 * s)) * δ ^ (-2 * s))) =
            (2 : ℝ) ^ (-(2 + 2 * s)) * (2 : ℝ) ^ (2 * r) * δ ^ (-2 * s) := by
          have hr_pow : (2 : ℝ) * (2 : ℝ) ^ (r - 1) = (2 : ℝ) ^ r := by
            rcases r with _ | k
            · omega
            · simp [pow_succ]; ring
          have hsq_pow : ((2 : ℝ) ^ (r - 1)) ^ 2 = (2 : ℝ) ^ (2 * r) / 4 := by
            have h1 : (4 : ℝ) * ((2 : ℝ) ^ (r - 1)) ^ 2 = ((2 : ℝ) ^ r) ^ 2 := by
              rw [← hr_pow]; ring
            have h2 : ((2 : ℝ) ^ r) ^ 2 = (2 : ℝ) ^ (2 * r) := by
              rw [← pow_mul, mul_comm r 2]
            linarith
          have h2exp : (2 : ℝ) ^ (-(1 + 2 * s)) / 2 = (2 : ℝ) ^ (-(2 + 2 * s)) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add (by norm_num)]
            congr 1; ring
          rw [hsq_pow]
          calc
            2 * ((2 : ℝ) ^ (2 * r) / 4 * ((2 : ℝ) ^ (-(1 + 2 * s)) * δ ^ (-2 * s)))
                = ((2 : ℝ) ^ (-(1 + 2 * s)) / 2) * (2 : ℝ) ^ (2 * r) * δ ^ (-2 * s) := by ring
            _ = (2 : ℝ) ^ (-(2 + 2 * s)) * (2 : ℝ) ^ (2 * r) * δ ^ (-2 * s) := by rw [h2exp]
        have hlin : (2 : ℝ) ^ (-(2 + 2 * s)) * (2 : ℝ) ^ (2 * r) * (μI A₁).toReal * δ ^ (-2 * s) =
            (((2 : ℝ) ^ (r - 1)) ^ 2 * ((2 : ℝ) ^ (-(1 + 2 * s)) * δ ^ (-2 * s)) * (μI A₁).toReal) +
            (((2 : ℝ) ^ (r - 1)) ^ 2 * ((2 : ℝ) ^ (-(1 + 2 * s)) * δ ^ (-2 * s)) * (μI A₁).toReal) := by
          have := congrArg (fun z => z * (μI A₁).toReal) hpow_alg
          linarith
        rw [hlin]
        exact hto
      have hfactor : (2 : ℝ) ^ (2 * r) * (μI (Eset g (r + 1))).toReal * δ ^ (-2 * s) ≤
          (2 : ℝ) ^ (2 + 2 * s) * σval s g r := by
        have hmul := mul_le_mul_of_nonneg_left hσ_ge (show (0 : ℝ) ≤ (2 : ℝ) ^ (2 + 2 * s) by positivity)
        have hcancel : (2 : ℝ) ^ (2 + 2 * s) *
            ((2 : ℝ) ^ (-(2 + 2 * s)) * (2 : ℝ) ^ (2 * r) * (μI (Eset g (r + 1))).toReal *
              δ ^ (-2 * s)) =
            (2 : ℝ) ^ (2 * r) * (μI (Eset g (r + 1))).toReal * δ ^ (-2 * s) := by
          rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← Real.rpow_add (by norm_num),
            add_neg_cancel, Real.rpow_zero, one_mul]
        rwa [hcancel] at hmul
      have ha_id : aSeq α g (r + 1) =
          (2 : ℝ) ^ (1 / (α : ℝ)) *
            ((2 : ℝ) ^ (2 * r) * (μI (Eset g (r + 1))).toReal * δ ^ (-2 * s)) *
            (aSeq α g r) ^ (2 * s) := by
        unfold aSeq
        rw [Real.mul_rpow (by positivity) ENNReal.toReal_nonneg,
          ← Real.rpow_mul (by norm_num)]
        have hpow_nat : ((2 : ℝ) ^ (2 * r)) = (2 : ℝ) ^ ((2 * r : ℕ) : ℝ) :=
          (Real.rpow_natCast 2 (2 * r)).symm
        have hδ_cancel : δ ^ (-2 * s) * δ ^ (2 * s) = 1 := by
          rw [← Real.rpow_add hδ_pos, show (-2 * s : ℝ) + 2 * s = 0 by ring, Real.rpow_zero]
        have h2_comb : (2 : ℝ) ^ (1 / (α : ℝ)) * (2 : ℝ) ^ (2 * r) *
            (2 : ℝ) ^ ((r : ℝ) / (α : ℝ) * (2 * s)) =
            (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) / (α : ℝ)) := by
          rw [hpow_nat, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
          congr 1
          push_cast
          have h2s : 2 * s = 1 - 2 * (α : ℝ) := by linarith
          rw [h2s]
          field_simp [hα_pos.ne']
          ring
        calc
          (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) / (α : ℝ)) * (μI (Eset g (r + 1))).toReal
              = ((2 : ℝ) ^ (1 / (α : ℝ)) * (2 : ℝ) ^ (2 * r) *
                  (2 : ℝ) ^ ((r : ℝ) / (α : ℝ) * (2 * s))) *
                  (μI (Eset g (r + 1))).toReal * (δ ^ (-2 * s) * δ ^ (2 * s)) := by
                rw [h2_comb, hδ_cancel, mul_one]
          _ = _ := by ring
      have ha_le_prod : aSeq α g (r + 1) ≤
          ((2 : ℝ) ^ (1 / (α : ℝ) + 2 + 4 * s) * σval s g r) *
            (((1 / 2 : ℝ) * aSeq α g r) ^ (2 * s)) := by
        rw [ha_id]
        have h1 : (2 : ℝ) ^ (1 / (α : ℝ)) *
              ((2 : ℝ) ^ (2 * r) * (μI (Eset g (r + 1))).toReal * δ ^ (-2 * s)) *
              (aSeq α g r) ^ (2 * s) ≤
            (2 : ℝ) ^ (1 / (α : ℝ)) * ((2 : ℝ) ^ (2 + 2 * s) * σval s g r) *
              (aSeq α g r) ^ (2 * s) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfactor (by positivity))
            (Real.rpow_nonneg (aSeq_nonneg α g r) _)
        refine h1.trans (le_of_eq ?_)
        rw [Real.mul_rpow (by norm_num) (aSeq_nonneg α g r)]
        have h2half : ((1 / 2 : ℝ) ^ (2 * s)) = (2 : ℝ) ^ (-(2 * s)) := by
          rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
        rw [h2half]
        have h2eq : (2 : ℝ) ^ (1 / (α : ℝ)) * (2 : ℝ) ^ (2 + 2 * s) =
            (2 : ℝ) ^ (1 / (α : ℝ) + 2 + 4 * s) * (2 : ℝ) ^ (-(2 * s)) := by
          rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
          congr 1; ring
        calc
          (2 : ℝ) ^ (1 / (α : ℝ)) * ((2 : ℝ) ^ (2 + 2 * s) * σval s g r) * (aSeq α g r) ^ (2 * s)
              = ((2 : ℝ) ^ (1 / (α : ℝ)) * (2 : ℝ) ^ (2 + 2 * s)) * σval s g r *
                  (aSeq α g r) ^ (2 * s) := by ring
          _ = ((2 : ℝ) ^ (1 / (α : ℝ) + 2 + 4 * s) * (2 : ℝ) ^ (-(2 * s))) * σval s g r *
                  (aSeq α g r) ^ (2 * s) := by rw [h2eq]
          _ = _ := by ring
      let p : ℝ := 1 / (2 * (α : ℝ))
      let q : ℝ := 1 / (2 * s)
      have hpq : p.HolderConjugate q := by
        rw [Real.holderConjugate_iff]
        refine ⟨?_, ?_⟩
        · dsimp [p]; rw [one_lt_div (by positivity)]; linarith
        · dsimp [p, q]; rw [one_div, inv_inv, one_div, inv_inv]; exact h2αs
      have hX_nn : 0 ≤ (2 : ℝ) ^ (1 / (α : ℝ) + 2 + 4 * s) * σval s g r :=
        mul_nonneg (by positivity) ENNReal.toReal_nonneg
      have hY_nn : 0 ≤ ((1 / 2 : ℝ) * aSeq α g r) ^ (2 * s) :=
        Real.rpow_nonneg (mul_nonneg (by norm_num) (aSeq_nonneg α g r)) _
      have hyoung := Real.young_inequality_of_nonneg hX_nn hY_nn hpq
      have hσ_nn : 0 ≤ σval s g r := ENNReal.toReal_nonneg
      have hterm1 : ((2 : ℝ) ^ (1 / (α : ℝ) + 2 + 4 * s) * σval s g r) ^ p / p =
          Kα * (σval s g r) ^ (1 / (2 * (α : ℝ))) := by
        dsimp only [Kα, p]
        rw [Real.mul_rpow (by positivity) hσ_nn,
          ← Real.rpow_mul (by norm_num), div_eq_mul_inv, one_div (2 * (α : ℝ)), inv_inv,
          show (1 / (α : ℝ) + 2 + 4 * s) * (2 * (α : ℝ))⁻¹ =
            (1 / (α : ℝ) + 2 + 4 * s) / (2 * (α : ℝ)) by ring]
        ring
      have hterm2 : (((1 / 2 : ℝ) * aSeq α g r) ^ (2 * s)) ^ q / q =
          (2 * s) * ((1 / 2 : ℝ) * aSeq α g r) := by
        dsimp only [q]
        rw [← Real.rpow_mul (mul_nonneg (by norm_num) (aSeq_nonneg α g r)),
          mul_one_div_cancel (by positivity), Real.rpow_one, div_eq_mul_inv,
          one_div (2 * s), inv_inv]
        ring
      have h2s_lt1 : 2 * s ≤ 1 := by linarith
      have hterm2_le : (2 * s) * ((1 / 2 : ℝ) * aSeq α g r) ≤ (1 / 2 : ℝ) * aSeq α g r :=
        mul_le_of_le_one_left (mul_nonneg (by norm_num) (aSeq_nonneg α g r)) h2s_lt1
      rw [hterm1, hterm2] at hyoung
      exact ha_le_prod.trans (hyoung.trans (by linarith))
  have hσ_summ := summable_σval_and_tsum_le hg
  let B : ℝ := (∑ r ∈ Finset.range (r₀ + 1), aSeq α g r) + aSeq α g r₀ +
      2 * Kα * (‖g.1.snd‖ ^ 2) ^ (1 / (2 * (α : ℝ)))
  refine summable_of_sum_range_le (c := B) (aSeq_nonneg α g) (fun N => ?_)
  by_cases hN : N ≤ r₀ + 1
  · calc
      ∑ r ∈ Finset.range N, aSeq α g r
          ≤ ∑ r ∈ Finset.range (r₀ + 1), aSeq α g r :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN) (fun _ _ _ => aSeq_nonneg α g _)
      _ ≤ B := by
            dsimp only [B]
            have h1 : 0 ≤ aSeq α g r₀ := aSeq_nonneg α g r₀
            have h2 : 0 ≤ 2 * Kα * (‖g.1.snd‖ ^ 2) ^ (1 / (2 * (α : ℝ))) := by positivity
            linarith
  · push Not at hN
    let R := N - 1
    have hR : r₀ < R := by omega
    have hN_eq : R + 1 = N := by omega
    have hsum_rec : ∑ r ∈ Finset.Ico r₀ R, aSeq α g (r + 1) ≤
        Kα * (∑ r ∈ Finset.Ico r₀ R, (σval s g r) ^ (1 / (2 * (α : ℝ)))) +
        (1 / 2) * ∑ r ∈ Finset.Ico r₀ R, aSeq α g r := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun r hr => hrec r (Finset.mem_Ico.mp hr).1)
    have hshift : ∑ r ∈ Finset.Ico r₀ R, aSeq α g (r + 1) =
        ∑ r ∈ Finset.Ico (r₀ + 1) (R + 1), aSeq α g r := by
      have h := Finset.sum_Ico_add (f := aSeq α g) r₀ R 1
      simpa [add_comm] using h
    have hle_rhs : ∑ r ∈ Finset.Ico r₀ R, aSeq α g r ≤
        aSeq α g r₀ + ∑ r ∈ Finset.Ico (r₀ + 1) (R + 1), aSeq α g r := by
      rw [Finset.sum_eq_sum_Ico_succ_bot hR]
      have hsub : Finset.Ico (r₀ + 1) R ⊆ Finset.Ico (r₀ + 1) (R + 1) :=
        Finset.Ico_subset_Ico_right (Nat.le_succ R)
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := aSeq α g) hsub
        (fun r _ _ => aSeq_nonneg α g r)
      linarith
    have hσ_p : ∑ r ∈ Finset.Ico r₀ R, (σval s g r) ^ (1 / (2 * (α : ℝ))) ≤
        (‖g.1.snd‖ ^ 2) ^ (1 / (2 * (α : ℝ))) := by
      have hp1 : (1 : ℝ) ≤ 1 / (2 * (α : ℝ)) := by
        rw [one_le_div (by positivity)]; linarith
      calc
        ∑ r ∈ Finset.Ico r₀ R, (σval s g r) ^ (1 / (2 * (α : ℝ)))
            ≤ (∑ r ∈ Finset.Ico r₀ R, σval s g r) ^ (1 / (2 * (α : ℝ))) :=
              sum_rpow_le_rpow_sum _ (fun _ _ => ENNReal.toReal_nonneg) hp1
        _ ≤ (∑' r, σval s g r) ^ (1 / (2 * (α : ℝ))) :=
              Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
                (hσ_summ.1.sum_le_tsum _ (fun _ _ => ENNReal.toReal_nonneg)) (by positivity)
        _ ≤ (‖g.1.snd‖ ^ 2) ^ (1 / (2 * (α : ℝ))) :=
              Real.rpow_le_rpow (tsum_nonneg (fun _ => ENNReal.toReal_nonneg))
                hσ_summ.2 (by positivity)
    have htail_bound : ∑ r ∈ Finset.Ico (r₀ + 1) N, aSeq α g r ≤
        aSeq α g r₀ + 2 * Kα * (‖g.1.snd‖ ^ 2) ^ (1 / (2 * (α : ℝ))) := by
      rw [← hN_eq]
      rw [hshift] at hsum_rec
      have hK := mul_le_mul_of_nonneg_left hσ_p hKα_nn
      linarith
    rw [← Finset.sum_range_add_sum_Ico (aSeq α g) (by omega : r₀ + 1 ≤ N)]
    dsimp only [B]
    linarith

/-! Section 6: Rearrangement, interval restriction, reparameterization, and alpha-Holder path -/

lemma rearrangement_left {s a b : ℝ} (hs0 : 0 < s) (hs : s < 1 / 2)
    (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
    {A : Set ℝ} (hA_meas : MeasurableSet A) (hA_sub : A ⊆ Set.Icc a b) :
    ∫⁻ x in A, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI ≤
      ENNReal.ofReal ((μI A).toReal ^ (1 - 2 * s) / (1 - 2 * s)) := by
  set m := (μI A).toReal
  by_cases hm0 : m = 0
  · have hμ0 : μI A = 0 := ((ENNReal.toReal_eq_zero_iff _).mp hm0).resolve_right (measure_ne_top _ _)
    rw [setLIntegral_measure_zero _ _ hμ0]
    exact bot_le
  · have hm_pos : 0 < m := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hm0)
    have hIcc_sub : Set.Icc a b ⊆ Iset := fun x hx => ⟨ha0.trans hx.1, hx.2.trans hb1⟩
    have hm_le : m ≤ b - a := by
      have h1 : μI A ≤ μI (Set.Icc a b) := measure_mono hA_sub
      have h2 : μI (Set.Icc a b) = ENNReal.ofReal (b - a) := by
        rw [μI, Measure.restrict_apply measurableSet_Icc, Set.inter_eq_left.mpr hIcc_sub,
          Real.volume_Icc]
      rw [h2] at h1
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [ENNReal.toReal_ofReal (by linarith)] at this
    let B : Set ℝ := Set.Icc a (a + m)
    have hB_meas : MeasurableSet B := measurableSet_Icc
    have hB_sub : B ⊆ Set.Icc a b := fun x hx => ⟨hx.1, by linarith [hx.2]⟩
    have hB_sub_I : B ⊆ Iset := hB_sub.trans hIcc_sub
    have hμB : μI B = μI A := by
      have h1 : μI B = ENNReal.ofReal m := by
        rw [μI, Measure.restrict_apply hB_meas, Set.inter_eq_left.mpr hB_sub_I,
          Real.volume_Icc, add_sub_cancel_left]
      rw [h1, ENNReal.ofReal_toReal (measure_ne_top μI A)]
    have hdisj1 : Disjoint (A \ B) (A ∩ B) :=
      Set.disjoint_left.mpr (fun _ h1 h2 => h1.2 h2.2)
    have hdisj2 : Disjoint (B \ A) (A ∩ B) :=
      Set.disjoint_left.mpr (fun _ h1 h2 => h1.2 h2.1)
    have hdiff_eq : μI (A \ B) = μI (B \ A) := by
      have hA_split : μI (A \ B) + μI (A ∩ B) = μI A := by
        rw [← measure_union hdisj1 (hA_meas.inter hB_meas), Set.sdiff_union_inter]
      have hB_split : μI (B \ A) + μI (A ∩ B) = μI B := by
        rw [← measure_union hdisj2 (hA_meas.inter hB_meas), Set.inter_comm A B,
          Set.sdiff_union_inter]
      have hsum : μI (A \ B) + μI (A ∩ B) = μI (B \ A) + μI (A ∩ B) := by
        rw [hA_split, hB_split, hμB]
      exact (ENNReal.add_left_inj (measure_ne_top μI (A ∩ B))).mp hsum
    have hAB_le_BA : ∫⁻ x in A \ B, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI ≤
        ∫⁻ x in B \ A, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI := by
      have h1 : ∫⁻ x in A \ B, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI ≤
          ENNReal.ofReal (m ^ (-2 * s)) * μI (A \ B) := by
        rw [← setLIntegral_const]
        apply setLIntegral_mono' (hA_meas.diff hB_meas)
        intro x hx
        have hxa : m < x - a := by
          have hge := (hA_sub hx.1).1
          have hnot : ¬ (a ≤ x ∧ x ≤ a + m) := hx.2
          have : a + m < x := by by_contra hle; exact hnot ⟨hge, not_lt.mp hle⟩
          linarith
        apply ENNReal.ofReal_le_ofReal
        rw [show (-2 * s : ℝ) = -(2 * s) by ring,
          Real.rpow_neg (by linarith), Real.rpow_neg hm_pos.le]
        exact inv_anti₀ (by positivity) (Real.rpow_le_rpow hm_pos.le hxa.le (by linarith))
      have h2 : ENNReal.ofReal (m ^ (-2 * s)) * μI ((B \ A) \ {a}) ≤
          ∫⁻ x in (B \ A) \ {a}, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI := by
        rw [← setLIntegral_const]
        apply setLIntegral_mono' ((hB_meas.diff hA_meas).diff (measurableSet_singleton a))
        intro x hx
        have hxpos : 0 < x - a := by
          have hge : a ≤ x := hx.1.1.1
          have hne : x ≠ a := hx.2
          exact sub_pos.mpr (lt_of_le_of_ne hge (Ne.symm hne))
        have hxle : x - a ≤ m := by linarith [hx.1.1.2]
        apply ENNReal.ofReal_le_ofReal
        rw [show (-2 * s : ℝ) = -(2 * s) by ring,
          Real.rpow_neg hxpos.le, Real.rpow_neg hm_pos.le]
        exact inv_anti₀ (by positivity) (Real.rpow_le_rpow hxpos.le hxle (by linarith))
      calc
        ∫⁻ x in A \ B, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI
            ≤ ENNReal.ofReal (m ^ (-2 * s)) * μI (A \ B) := h1
        _ = ENNReal.ofReal (m ^ (-2 * s)) * μI ((B \ A) \ {a}) := by
            rw [hdiff_eq, measure_sdiff_null (μI_singleton a)]
        _ ≤ ∫⁻ x in (B \ A) \ {a}, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI := h2
        _ ≤ ∫⁻ x in B \ A, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI :=
            lintegral_mono_set Set.sdiff_subset
    have hA_le_B : ∫⁻ x in A, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI ≤
        ∫⁻ x in B, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI := by
      have hA_eq : A = (A \ B) ∪ (A ∩ B) := (Set.sdiff_union_inter A B).symm
      have hB_eq : B = (B \ A) ∪ (A ∩ B) := by
        rw [Set.inter_comm A B]; exact (Set.sdiff_union_inter B A).symm
      have hL : ∫⁻ x in A, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI =
          (∫⁻ x in A \ B, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI) +
            (∫⁻ x in A ∩ B, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI) := by
        conv_lhs => rw [hA_eq]
        exact lintegral_union (hA_meas.inter hB_meas) hdisj1
      have hR : ∫⁻ x in B, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI =
          (∫⁻ x in B \ A, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI) +
            (∫⁻ x in A ∩ B, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI) := by
        conv_lhs => rw [hB_eq]
        exact lintegral_union (hA_meas.inter hB_meas) hdisj2
      rw [hL, hR]
      exact add_le_add hAB_le_BA le_rfl
    have hB_val : ∫⁻ x in B, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI =
        ENNReal.ofReal (m ^ (1 - 2 * s) / (1 - 2 * s)) := by
      have hres : μI.restrict B = volume.restrict (Set.Ioo a (a + m)) := by
        rw [μI, Measure.restrict_restrict hB_meas, Set.inter_eq_left.mpr hB_sub_I]
        exact (Measure.restrict_congr_set Ioo_ae_eq_Icc).symm
      rw [hres, lintegral_Ioo_left_rpow_eq hs (by linarith), add_sub_cancel_left]
    exact hA_le_B.trans_eq hB_val

lemma rearrangement_right {s a b : ℝ} (hs0 : 0 < s) (hs : s < 1 / 2)
    (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
    {A : Set ℝ} (hA_meas : MeasurableSet A) (hA_sub : A ⊆ Set.Icc a b) :
    ∫⁻ x in A, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI ≤
      ENNReal.ofReal ((μI A).toReal ^ (1 - 2 * s) / (1 - 2 * s)) := by
  set m := (μI A).toReal
  by_cases hm0 : m = 0
  · have hμ0 : μI A = 0 := ((ENNReal.toReal_eq_zero_iff _).mp hm0).resolve_right (measure_ne_top _ _)
    rw [setLIntegral_measure_zero _ _ hμ0]
    exact bot_le
  · have hm_pos : 0 < m := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hm0)
    have hIcc_sub : Set.Icc a b ⊆ Iset := fun x hx => ⟨ha0.trans hx.1, hx.2.trans hb1⟩
    have hm_le : m ≤ b - a := by
      have h1 : μI A ≤ μI (Set.Icc a b) := measure_mono hA_sub
      have h2 : μI (Set.Icc a b) = ENNReal.ofReal (b - a) := by
        rw [μI, Measure.restrict_apply measurableSet_Icc, Set.inter_eq_left.mpr hIcc_sub,
          Real.volume_Icc]
      rw [h2] at h1
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [ENNReal.toReal_ofReal (by linarith)] at this
    let B : Set ℝ := Set.Icc (b - m) b
    have hB_meas : MeasurableSet B := measurableSet_Icc
    have hB_sub : B ⊆ Set.Icc a b := fun x hx => ⟨by linarith [hx.1], hx.2⟩
    have hB_sub_I : B ⊆ Iset := hB_sub.trans hIcc_sub
    have hμB : μI B = μI A := by
      have h1 : μI B = ENNReal.ofReal m := by
        rw [μI, Measure.restrict_apply hB_meas, Set.inter_eq_left.mpr hB_sub_I,
          Real.volume_Icc, sub_sub_cancel]
      rw [h1, ENNReal.ofReal_toReal (measure_ne_top μI A)]
    have hdisj1 : Disjoint (A \ B) (A ∩ B) :=
      Set.disjoint_left.mpr (fun _ h1 h2 => h1.2 h2.2)
    have hdisj2 : Disjoint (B \ A) (A ∩ B) :=
      Set.disjoint_left.mpr (fun _ h1 h2 => h1.2 h2.1)
    have hdiff_eq : μI (A \ B) = μI (B \ A) := by
      have hA_split : μI (A \ B) + μI (A ∩ B) = μI A := by
        rw [← measure_union hdisj1 (hA_meas.inter hB_meas), Set.sdiff_union_inter]
      have hB_split : μI (B \ A) + μI (A ∩ B) = μI B := by
        rw [← measure_union hdisj2 (hA_meas.inter hB_meas), Set.inter_comm A B,
          Set.sdiff_union_inter]
      have hsum : μI (A \ B) + μI (A ∩ B) = μI (B \ A) + μI (A ∩ B) := by
        rw [hA_split, hB_split, hμB]
      exact (ENNReal.add_left_inj (measure_ne_top μI (A ∩ B))).mp hsum
    have hAB_le_BA : ∫⁻ x in A \ B, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI ≤
        ∫⁻ x in B \ A, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI := by
      have h1 : ∫⁻ x in A \ B, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI ≤
          ENNReal.ofReal (m ^ (-2 * s)) * μI (A \ B) := by
        rw [← setLIntegral_const]
        apply setLIntegral_mono' (hA_meas.diff hB_meas)
        intro x hx
        have hbx : m < b - x := by
          have hle := (hA_sub hx.1).2
          have hnot : ¬ (b - m ≤ x ∧ x ≤ b) := hx.2
          have : x < b - m := by by_contra hge; exact hnot ⟨not_lt.mp hge, hle⟩
          linarith
        apply ENNReal.ofReal_le_ofReal
        rw [show (-2 * s : ℝ) = -(2 * s) by ring,
          Real.rpow_neg (by linarith), Real.rpow_neg hm_pos.le]
        exact inv_anti₀ (by positivity) (Real.rpow_le_rpow hm_pos.le hbx.le (by linarith))
      have h2 : ENNReal.ofReal (m ^ (-2 * s)) * μI ((B \ A) \ {b}) ≤
          ∫⁻ x in (B \ A) \ {b}, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI := by
        rw [← setLIntegral_const]
        apply setLIntegral_mono' ((hB_meas.diff hA_meas).diff (measurableSet_singleton b))
        intro x hx
        have hxpos : 0 < b - x := by
          have hle : x ≤ b := hx.1.1.2
          have hne : x ≠ b := hx.2
          exact sub_pos.mpr (lt_of_le_of_ne hle hne)
        have hxle : b - x ≤ m := by linarith [hx.1.1.1]
        apply ENNReal.ofReal_le_ofReal
        rw [show (-2 * s : ℝ) = -(2 * s) by ring,
          Real.rpow_neg hxpos.le, Real.rpow_neg hm_pos.le]
        exact inv_anti₀ (by positivity) (Real.rpow_le_rpow hxpos.le hxle (by linarith))
      calc
        ∫⁻ x in A \ B, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI
            ≤ ENNReal.ofReal (m ^ (-2 * s)) * μI (A \ B) := h1
        _ = ENNReal.ofReal (m ^ (-2 * s)) * μI ((B \ A) \ {b}) := by
            rw [hdiff_eq, measure_sdiff_null (μI_singleton b)]
        _ ≤ ∫⁻ x in (B \ A) \ {b}, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI := h2
        _ ≤ ∫⁻ x in B \ A, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI :=
            lintegral_mono_set Set.sdiff_subset
    have hA_le_B : ∫⁻ x in A, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI ≤
        ∫⁻ x in B, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI := by
      have hA_eq : A = (A \ B) ∪ (A ∩ B) := (Set.sdiff_union_inter A B).symm
      have hB_eq : B = (B \ A) ∪ (A ∩ B) := by
        rw [Set.inter_comm A B]; exact (Set.sdiff_union_inter B A).symm
      have hL : ∫⁻ x in A, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI =
          (∫⁻ x in A \ B, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI) +
            (∫⁻ x in A ∩ B, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI) := by
        conv_lhs => rw [hA_eq]
        exact lintegral_union (hA_meas.inter hB_meas) hdisj1
      have hR : ∫⁻ x in B, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI =
          (∫⁻ x in B \ A, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI) +
            (∫⁻ x in A ∩ B, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI) := by
        conv_lhs => rw [hB_eq]
        exact lintegral_union (hA_meas.inter hB_meas) hdisj2
      rw [hL, hR]
      exact add_le_add hAB_le_BA le_rfl
    have hB_val : ∫⁻ x in B, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI =
        ENNReal.ofReal (m ^ (1 - 2 * s) / (1 - 2 * s)) := by
      have hres : μI.restrict B = volume.restrict (Set.Ioo (b - m) b) := by
        rw [μI, Measure.restrict_restrict hB_meas, Set.inter_eq_left.mpr hB_sub_I]
        exact (Measure.restrict_congr_set Ioo_ae_eq_Icc).symm
      rw [hres, lintegral_Ioo_right_rpow_eq hs (by linarith), sub_sub_cancel]
    exact hA_le_B.trans_eq hB_val

lemma lintegral_Iset_diff_Icc_Ks_le {s a b x : ℝ} (hs0 : 0 < s)
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hx : x ∈ Set.Ioo a b) :
    ∫⁻ y in Iset \ Set.Icc a b, Ks s (x, y) ∂μI ≤
      ENNReal.ofReal ((x - a) ^ (-2 * s) / (2 * s)) +
        ENNReal.ofReal ((b - x) ^ (-2 * s) / (2 * s)) := by
  have hsub : Iset \ Set.Icc a b ⊆ Set.Ioo 0 a ∪ Set.Ioo b 1 ∪ {0, 1} := by
    intro y hy
    rcases hy with ⟨⟨hy0, hy1⟩, hyn⟩
    by_cases hya : y < a
    · by_cases hyz : y = 0
      · exact Or.inr (Or.inl hyz)
      · exact Or.inl (Or.inl ⟨lt_of_le_of_ne hy0 (Ne.symm hyz), hya⟩)
    · have hyb : b < y := by
        by_contra hle; exact hyn ⟨not_lt.mp hya, not_lt.mp hle⟩
      by_cases hyo : y = 1
      · exact Or.inr (Or.inr hyo)
      · exact Or.inl (Or.inr ⟨hyb, lt_of_le_of_ne hy1 hyo⟩)
  calc
    ∫⁻ y in Iset \ Set.Icc a b, Ks s (x, y) ∂μI
        ≤ ∫⁻ y in Set.Ioo 0 a ∪ Set.Ioo b 1 ∪ {0, 1}, Ks s (x, y) ∂μI := lintegral_mono_set hsub
    _ ≤ (∫⁻ y in Set.Ioo 0 a, Ks s (x, y) ∂μI) + (∫⁻ y in Set.Ioo b 1, Ks s (x, y) ∂μI) +
          (∫⁻ y in ({0, 1} : Set ℝ), Ks s (x, y) ∂μI) := by
          refine le_trans (lintegral_union_le _ _ _) ?_
          exact add_le_add (lintegral_union_le _ _ _) le_rfl
    _ = (∫⁻ y in Set.Ioo 0 a, ENNReal.ofReal ((x - y) ^ (-(1 + 2 * s)))) +
          (∫⁻ y in Set.Ioo b 1, ENNReal.ofReal ((y - x) ^ (-(1 + 2 * s)))) := by
          rw [setLIntegral_measure_zero _ _ (μI_pair 0 1), add_zero]
          have hsub1 : Set.Ioo 0 a ⊆ Iset := fun y hy => ⟨hy.1.le, by linarith [hy.2, hx.1, hx.2]⟩
          have hsub2 : Set.Ioo b 1 ⊆ Iset := fun y hy => ⟨by linarith [hy.1, hx.1, hx.2], hy.2.le⟩
          congr 1
          · rw [μI, Measure.restrict_restrict measurableSet_Ioo, Set.inter_eq_left.mpr hsub1]
            apply setLIntegral_congr_fun measurableSet_Ioo
            intro y hy
            have hne : x ≠ y := by linarith [hx.1, hy.2]
            dsimp only [Ks]; rw [if_neg hne, abs_of_pos (by linarith [hx.1, hy.2])]
          · rw [μI, Measure.restrict_restrict measurableSet_Ioo, Set.inter_eq_left.mpr hsub2]
            apply setLIntegral_congr_fun measurableSet_Ioo
            intro y hy
            have hne : x ≠ y := by linarith [hx.2, hy.1]
            dsimp only [Ks]; rw [if_neg hne, abs_sub_comm, abs_of_pos (by linarith [hx.2, hy.1])]
    _ ≤ ENNReal.ofReal ((x - a) ^ (-2 * s) / (2 * s)) +
          ENNReal.ofReal ((b - x) ^ (-2 * s) / (2 * s)) :=
          add_le_add (lintegral_Ioo_sub_rpow_le hs0 ha0 hx.1)
            (lintegral_Ioo_rsub_rpow_le hs0 hx.2 hb1)

noncomputable def ρE (s : ℝ) (g : Hsub s) (r : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal ((hLayer g r x - hLayer g r y) ^ 2) * Ks s (x, y) ∂μI

lemma measurable_ρE (s : ℝ) (g : Hsub s) (r : ℕ) : Measurable (ρE s g r) := by
  unfold ρE
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((hLayer g r p.1 - hLayer g r p.2) ^ 2) * Ks s p) :=
    (ENNReal.measurable_ofReal.comp
      (((measurable_hLayer g r).comp measurable_fst).sub
        ((measurable_hLayer g r).comp measurable_snd) |>.pow_const 2)).mul (measurable_Ks s)
  exact hm.lintegral_prod_right'

lemma lintegral_ρE_eq (s : ℝ) (g : Hsub s) (r : ℕ) :
    ∫⁻ x, ρE s g r x ∂μI = σvalE s g r := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((hLayer g r p.1 - hLayer g r p.2) ^ 2) * Ks s p) :=
    (ENNReal.measurable_ofReal.comp
      (((measurable_hLayer g r).comp measurable_fst).sub
        ((measurable_hLayer g r).comp measurable_snd) |>.pow_const 2)).mul (measurable_Ks s)
  unfold σvalE ρE μΩ
  exact (lintegral_prod _ hm.aemeasurable).symm

noncomputable def hLayerTruncFun {s : ℝ} (g : Hsub s) (r : ℕ) (a b : ℝ) : ℝ → ℝ :=
  (Set.Icc a b).indicator (hLayer g r)

lemma measurable_hLayerTruncFun {s : ℝ} (g : Hsub s) (r : ℕ) (a b : ℝ) :
    Measurable (hLayerTruncFun g r a b) :=
  (measurable_hLayer g r).indicator measurableSet_Icc

lemma hLayerTruncFun_int {s : ℝ} (g : Hsub s) (r : ℕ) (a b x : ℝ) :
    ∃ n : ℤ, hLayerTruncFun g r a b x = (n : ℝ) := by
  unfold hLayerTruncFun
  by_cases hx : x ∈ Set.Icc a b
  · rw [Set.indicator_of_mem hx]; exact hLayer_int g r x
  · rw [Set.indicator_of_notMem hx]; exact ⟨0, by simp⟩

lemma hLayerTrunc_L2_le {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (g : Hsub (sVal α)) (r : ℕ) {a b : ℝ} :
    ∫⁻ x, ENNReal.ofReal (hLayerTruncFun g r a b x ^ 2) ∂μI ≤
      ENNReal.ofReal ((2 : ℝ) ^ (2 * r) * (μI (Eset g r ∩ Set.Icc a b)).toReal ^ (2 * (α : ℝ))) := by
  let A := Eset g r ∩ Set.Icc a b
  have hA_meas : MeasurableSet A := (measurableSet_Eset g r).inter measurableSet_Icc
  have hα_pos : (0 : ℝ) < (α : ℝ) := NNReal.coe_pos.mpr hα0
  have hα_lt : (α : ℝ) < 1 / 2 := by exact_mod_cast hαhalf
  set m := (μI A).toReal
  have hm_le1 : m ≤ 1 := by
    have h1 : μI A ≤ 1 := by rw [← μI_univ]; exact measure_mono (Set.subset_univ _)
    have := ENNReal.toReal_mono ENNReal.one_ne_top h1
    simpa using this
  have hm_pow : m ≤ m ^ (2 * (α : ℝ)) := by
    by_cases hm0 : m = 0
    · rw [hm0, Real.zero_rpow (by positivity)]
    · have hmp : 0 < m := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hm0)
      simpa using Real.rpow_le_rpow_of_exponent_ge hmp hm_le1 (by linarith : 2 * (α : ℝ) ≤ 1)
  have h1 : ∫⁻ x, ENNReal.ofReal (hLayerTruncFun g r a b x ^ 2) ∂μI ≤
      ENNReal.ofReal ((2 : ℝ) ^ (2 * r)) * μI A := by
    rw [← setLIntegral_const, ← lintegral_indicator hA_meas]
    apply lintegral_mono_ae
    filter_upwards [ae_mem_Iset] with x hxI
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA]
      apply ENNReal.ofReal_le_ofReal
      unfold hLayerTruncFun
      rw [Set.indicator_of_mem hxA.2, ← sq_abs]
      have h2 := abs_phi_le_two_pow r (intRep g x)
      have hsq : |hLayer g r x| ^ 2 ≤ ((2 : ℝ) ^ r) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h2 2
      rwa [← pow_mul, mul_comm r 2] at hsq
    · rw [Set.indicator_of_notMem hxA]
      have h0 : hLayerTruncFun g r a b x = 0 := by
        unfold hLayerTruncFun
        by_cases hxJ : x ∈ Set.Icc a b
        · rw [Set.indicator_of_mem hxJ]
          exact hLayer_eq_zero_of_not_mem_Eset g r hxI (fun hxE => hxA ⟨hxE, hxJ⟩)
        · exact Set.indicator_of_notMem hxJ _
      simp [h0]
  refine h1.trans ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top μI A), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hm_pow (by positivity))

lemma hLayerTrunc_sem_le {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (g : Hsub (sVal α)) (r : ℕ) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    ∫⁻ p, ENNReal.ofReal ((hLayerTruncFun g r a b p.1 - hLayerTruncFun g r a b p.2) ^ 2) *
        Ks (sVal α) p ∂μΩ ≤
      (∫⁻ x in Set.Icc a b, ρE (sVal α) g r x ∂μI) +
        ENNReal.ofReal
          ((1 / ((α : ℝ) * sVal α)) * (2 : ℝ) ^ (2 * r) *
            (μI (Eset g r ∩ Set.Icc a b)).toReal ^ (2 * (α : ℝ))) := by
  let s := sVal α
  have hα_pos : (0 : ℝ) < (α : ℝ) := NNReal.coe_pos.mpr hα0
  have hα_lt : (α : ℝ) < 1 / 2 := by exact_mod_cast hαhalf
  have hs0 : 0 < s := by dsimp [s, sVal]; linarith
  have hs_half : s < 1 / 2 := by dsimp [s, sVal]; linarith
  have h12s : 1 - 2 * s = 2 * (α : ℝ) := by dsimp [s, sVal]; ring
  let q := hLayerTruncFun g r a b
  let J := Set.Icc a b
  let A := Eset g r ∩ J
  have hJ_meas : MeasurableSet J := measurableSet_Icc
  have hA_meas : MeasurableSet A := (measurableSet_Eset g r).inter hJ_meas
  let F : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal ((q p.1 - q p.2) ^ 2) * Ks s p
  have hF_meas : Measurable F :=
    (ENNReal.measurable_ofReal.comp
      (((measurable_hLayerTruncFun g r a b).comp measurable_fst).sub
        ((measurable_hLayerTruncFun g r a b).comp measurable_snd) |>.pow_const 2)).mul
      (measurable_Ks s)
  let S₀ : Set (ℝ × ℝ) := J ×ˢ J
  let S₁ : Set (ℝ × ℝ) := J ×ˢ (Iset \ J)
  let S₂ : Set (ℝ × ℝ) := (Iset \ J) ×ˢ J
  have hS₀ : MeasurableSet S₀ := hJ_meas.prod hJ_meas
  have hS₁ : MeasurableSet S₁ := hJ_meas.prod (measurableSet_Iset.diff hJ_meas)
  have hS₂ : MeasurableSet S₂ := (measurableSet_Iset.diff hJ_meas).prod hJ_meas
  have hsplit : ∀ p : ℝ × ℝ, F p ≤
      S₀.indicator F p + S₁.indicator F p + S₂.indicator F p +
        (Iset ×ˢ Iset)ᶜ.indicator (fun _ => ⊤) p := by
    intro p
    by_cases hpI : p ∈ Iset ×ˢ Iset
    · simp only [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hpI), add_zero]
      by_cases h1 : p.1 ∈ J <;> by_cases h2 : p.2 ∈ J
      · have hm0 : p ∈ S₀ := ⟨h1, h2⟩
        rw [Set.indicator_of_mem hm0]
        exact le_self_add.trans le_self_add
      · have hm1 : p ∈ S₁ := ⟨h1, hpI.2, h2⟩
        rw [Set.indicator_of_mem hm1]
        exact le_add_self.trans le_self_add
      · have hm2 : p ∈ S₂ := ⟨⟨hpI.1, h1⟩, h2⟩
        rw [Set.indicator_of_mem hm2]
        exact le_add_self
      · have hq1 : q p.1 = 0 := Set.indicator_of_notMem h1 _
        have hq2 : q p.2 = 0 := Set.indicator_of_notMem h2 _
        simp [F, hq1, hq2]
    · simp [hpI]
  have hcompl_zero : ∫⁻ p, (Iset ×ˢ Iset)ᶜ.indicator (fun _ => (⊤ : ℝ≥0∞)) p ∂μΩ = 0 := by
    rw [lintegral_indicator (measurableSet_Iset.prod measurableSet_Iset).compl]
    have hμ0 : μΩ (Iset ×ˢ Iset)ᶜ = 0 := by
      have hprod : μΩ (Iset ×ˢ Iset) = 1 := by rw [μΩ, Measure.prod_prod, μI_Iset, mul_one]
      rw [measure_compl (measurableSet_Iset.prod measurableSet_Iset) (measure_ne_top _ _),
        μΩ_univ, hprod, tsub_self]
    rw [setLIntegral_measure_zero _ _ hμ0]
  have hsymm : ∫⁻ p, S₂.indicator F p ∂μΩ = ∫⁻ p, S₁.indicator F p ∂μΩ := by
    have hmp : MeasurePreserving Prod.swap μΩ μΩ := Measure.measurePreserving_swap
    rw [← hmp.lintegral_comp (hF_meas.indicator hS₁)]
    apply lintegral_congr
    intro p
    by_cases h : p.swap ∈ S₁
    · have h' : p ∈ S₂ := ⟨h.2, h.1⟩
      simp only [Set.indicator_of_mem h, Set.indicator_of_mem h', F,
        Prod.fst_swap, Prod.snd_swap, Ks_symm]
      congr 2; ring
    · have h' : p ∉ S₂ := fun hp => h ⟨hp.2, hp.1⟩
      simp [h, h']
  have hdiag : ∫⁻ p, S₀.indicator F p ∂μΩ ≤ ∫⁻ x in J, ρE s g r x ∂μI := by
    rw [μΩ, lintegral_prod _ (hF_meas.indicator hS₀).aemeasurable, ← lintegral_indicator hJ_meas]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ J
    · rw [Set.indicator_of_mem hx]
      unfold ρE
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ J
      · have hp : (x, y) ∈ S₀ := ⟨hx, hy⟩
        have hxJ : x ∈ Set.Icc a b := hx
        have hyJ : y ∈ Set.Icc a b := hy
        simp [hp, F, q, hLayerTruncFun, hxJ, hyJ]
      · have hp : (x, y) ∉ S₀ := fun h => hy h.2
        simp [hp]
    · rw [Set.indicator_of_notMem hx]
      have h0 : ∀ y, S₀.indicator F (x, y) = 0 := fun y =>
        Set.indicator_of_notMem (fun h => hx h.1) _
      simp [h0]
  have hcross : ∫⁻ p, S₁.indicator F p ∂μΩ ≤
      ENNReal.ofReal ((2 : ℝ) ^ (2 * r) / (2 * s) *
        ((μI A).toReal ^ (2 * (α : ℝ)) / (2 * (α : ℝ)) +
         (μI A).toReal ^ (2 * (α : ℝ)) / (2 * (α : ℝ)))) := by
    rw [μΩ, lintegral_prod _ (hF_meas.indicator hS₁).aemeasurable]
    have hae_ab : ∀ᵐ x ∂μI, x ≠ a ∧ x ≠ b := by
      rw [ae_iff]
      have heq : {x : ℝ | ¬ (x ≠ a ∧ x ≠ b)} = ({a, b} : Set ℝ) := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [heq]; exact μI_pair a b
    have hpt : (fun x => ∫⁻ y, S₁.indicator F (x, y) ∂μI) ≤ᵐ[μI]
        A.indicator (fun x => ENNReal.ofReal ((2 : ℝ) ^ (2 * r) / (2 * s)) *
          (ENNReal.ofReal ((x - a) ^ (-2 * s)) + ENNReal.ofReal ((b - x) ^ (-2 * s)))) := by
      filter_upwards [ae_mem_Iset, hae_ab] with x hxI habx
      by_cases hxA : x ∈ A
      · rw [Set.indicator_of_mem hxA]
        have hxoo : x ∈ Set.Ioo a b :=
          ⟨lt_of_le_of_ne hxA.2.1 (Ne.symm habx.1), lt_of_le_of_ne hxA.2.2 habx.2⟩
        have hq2 : ENNReal.ofReal (q x ^ 2) ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * r)) := by
          apply ENNReal.ofReal_le_ofReal
          unfold q hLayerTruncFun
          rw [Set.indicator_of_mem hxA.2, ← sq_abs]
          have h2 := abs_phi_le_two_pow r (intRep g x)
          have hsq : |hLayer g r x| ^ 2 ≤ ((2 : ℝ) ^ r) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h2 2
          rwa [← pow_mul, mul_comm r 2] at hsq
        have hinner : ∫⁻ y, S₁.indicator F (x, y) ∂μI ≤
            ENNReal.ofReal ((2 : ℝ) ^ (2 * r)) * ∫⁻ y in Iset \ J, Ks s (x, y) ∂μI := by
          have hm_y : Measurable (fun y : ℝ => (Iset \ J).indicator (fun y => Ks s (x, y)) y) :=
            ((measurable_Ks s).comp (measurable_const.prodMk measurable_id)).indicator
              (measurableSet_Iset.diff hJ_meas)
          rw [← lintegral_indicator (measurableSet_Iset.diff hJ_meas),
            ← lintegral_const_mul _ hm_y]
          apply lintegral_mono
          intro y
          by_cases hy : y ∈ Iset \ J
          · have hp : (x, y) ∈ S₁ := ⟨hxA.2, hy⟩
            have hqy : q y = 0 := Set.indicator_of_notMem hy.2 _
            simp only [Set.indicator_of_mem hp, Set.indicator_of_mem hy, F, hqy, sub_zero]
            exact mul_le_mul_of_nonneg_right hq2 bot_le
          · have hp : (x, y) ∉ S₁ := fun h => hy h.2
            simp [hp, hy]
        refine hinner.trans ?_
        have hK := lintegral_Iset_diff_Icc_Ks_le hs0 ha0 hb1 hxoo
        calc
          ENNReal.ofReal ((2 : ℝ) ^ (2 * r)) * ∫⁻ y in Iset \ J, Ks s (x, y) ∂μI
              ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * r)) *
                  (ENNReal.ofReal ((x - a) ^ (-2 * s) / (2 * s)) +
                    ENNReal.ofReal ((b - x) ^ (-2 * s) / (2 * s))) :=
                mul_le_mul_of_nonneg_left hK bot_le
          _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * r) / (2 * s)) *
                (ENNReal.ofReal ((x - a) ^ (-2 * s)) + ENNReal.ofReal ((b - x) ^ (-2 * s))) := by
                have hdiv1 : ENNReal.ofReal ((x - a) ^ (-2 * s) / (2 * s)) =
                    ENNReal.ofReal ((2 * s)⁻¹) * ENNReal.ofReal ((x - a) ^ (-2 * s)) := by
                  rw [div_eq_inv_mul, ENNReal.ofReal_mul (by positivity)]
                have hdiv2 : ENNReal.ofReal ((b - x) ^ (-2 * s) / (2 * s)) =
                    ENNReal.ofReal ((2 * s)⁻¹) * ENNReal.ofReal ((b - x) ^ (-2 * s)) := by
                  rw [div_eq_inv_mul, ENNReal.ofReal_mul (by positivity)]
                rw [hdiv1, hdiv2, ← mul_add, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
                  ← div_eq_mul_inv]
      · rw [Set.indicator_of_notMem hxA]
        have h0 : ∀ y, S₁.indicator F (x, y) = 0 := by
          intro y
          by_cases hp : (x, y) ∈ S₁
          · rw [Set.indicator_of_mem hp]
            have hxE : x ∉ Eset g r := fun h => hxA ⟨h, hp.1⟩
            have hqx : q x = 0 := by
              unfold q hLayerTruncFun
              rw [Set.indicator_of_mem hp.1]
              exact hLayer_eq_zero_of_not_mem_Eset g r hxI hxE
            have hqy : q y = 0 := Set.indicator_of_notMem hp.2.2 _
            simp [F, hqx, hqy]
          · exact Set.indicator_of_notMem hp _
        simp [h0]
    have hm1 : Measurable (fun x : ℝ => ENNReal.ofReal ((x - a) ^ (-2 * s))) :=
      ENNReal.measurable_ofReal.comp ((measurable_id.sub measurable_const).pow_const _)
    have hm2 : Measurable (fun x : ℝ => ENNReal.ofReal ((b - x) ^ (-2 * s))) :=
      ENNReal.measurable_ofReal.comp ((measurable_const.sub measurable_id).pow_const _)
    have hm12 : Measurable (fun x : ℝ =>
        ENNReal.ofReal ((x - a) ^ (-2 * s)) + ENNReal.ofReal ((b - x) ^ (-2 * s))) :=
      hm1.add hm2
    calc
      ∫⁻ x, (∫⁻ y, S₁.indicator F (x, y) ∂μI) ∂μI
          ≤ ∫⁻ x, A.indicator (fun x => ENNReal.ofReal ((2 : ℝ) ^ (2 * r) / (2 * s)) *
              (ENNReal.ofReal ((x - a) ^ (-2 * s)) + ENNReal.ofReal ((b - x) ^ (-2 * s)))) x ∂μI :=
            lintegral_mono_ae hpt
      _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * r) / (2 * s)) *
            ((∫⁻ x in A, ENNReal.ofReal ((x - a) ^ (-2 * s)) ∂μI) +
             (∫⁻ x in A, ENNReal.ofReal ((b - x) ^ (-2 * s)) ∂μI)) := by
            rw [lintegral_indicator hA_meas, lintegral_const_mul _ hm12,
              lintegral_add_left hm1 _]
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * r) / (2 * s)) *
            (ENNReal.ofReal ((μI A).toReal ^ (1 - 2 * s) / (1 - 2 * s)) +
             ENNReal.ofReal ((μI A).toReal ^ (1 - 2 * s) / (1 - 2 * s))) := by
            apply mul_le_mul_of_nonneg_left _ bot_le
            exact add_le_add
              (rearrangement_left hs0 hs_half ha0 hab hb1 hA_meas Set.inter_subset_right)
              (rearrangement_right hs0 hs_half ha0 hab hb1 hA_meas Set.inter_subset_right)
      _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * r) / (2 * s) *
            ((μI A).toReal ^ (2 * (α : ℝ)) / (2 * (α : ℝ)) +
             (μI A).toReal ^ (2 * (α : ℝ)) / (2 * (α : ℝ)))) := by
            rw [h12s, ← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
  have hmS0 : Measurable (fun p => S₀.indicator F p) := hF_meas.indicator hS₀
  have hmS1 : Measurable (fun p => S₁.indicator F p) := hF_meas.indicator hS₁
  have hmS2 : Measurable (fun p => S₂.indicator F p) := hF_meas.indicator hS₂
  have hmS01 : Measurable (fun p => S₀.indicator F p + S₁.indicator F p) := hmS0.add hmS1
  have hmS012 : Measurable (fun p => S₀.indicator F p + S₁.indicator F p + S₂.indicator F p) :=
    hmS01.add hmS2
  have hle : ∫⁻ p, F p ∂μΩ ≤
      (∫⁻ p, S₀.indicator F p ∂μΩ) + (∫⁻ p, S₁.indicator F p ∂μΩ) +
        (∫⁻ p, S₂.indicator F p ∂μΩ) +
        (∫⁻ p, (Iset ×ˢ Iset)ᶜ.indicator (fun _ => (⊤ : ℝ≥0∞)) p ∂μΩ) := by
    calc
      ∫⁻ p, F p ∂μΩ
          ≤ ∫⁻ p, (S₀.indicator F p + S₁.indicator F p + S₂.indicator F p +
              (Iset ×ˢ Iset)ᶜ.indicator (fun _ => ⊤) p) ∂μΩ := lintegral_mono hsplit
      _ = (∫⁻ p, (S₀.indicator F p + S₁.indicator F p + S₂.indicator F p) ∂μΩ) +
            (∫⁻ p, (Iset ×ˢ Iset)ᶜ.indicator (fun _ => (⊤ : ℝ≥0∞)) p ∂μΩ) :=
            lintegral_add_left hmS012 _
      _ = _ := by rw [lintegral_add_left hmS01 _, lintegral_add_left hmS0 _]
  rw [hcompl_zero, add_zero, hsymm, add_assoc] at hle
  refine hle.trans (add_le_add hdiag ?_)
  refine (add_le_add hcross hcross).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  dsimp only [s, A, J]
  have hs0' : sVal α ≠ 0 := hs0.ne'
  field_simp [hα_pos.ne', hs0']
  ring

noncomputable def hLayerTrunc {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ)
    (a b : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) : Hsub (sVal α) :=
  mkH (hLayerTruncFun g r a b) (measurable_hLayerTruncFun g r a b)
    (lt_of_le_of_lt (hLayerTrunc_L2_le hα0 hαhalf g r) ENNReal.ofReal_lt_top)
    (by
      have hρ_fin : ∫⁻ x in Set.Icc a b, ρE (sVal α) g r x ∂μI < ⊤ :=
        lt_of_le_of_lt (setLIntegral_le_lintegral _ _)
          (by rw [lintegral_ρE_eq]; exact σvalE_lt_top hg r)
      exact lt_of_le_of_lt (hLayerTrunc_sem_le hα0 hαhalf g r ha0 hab hb1)
        (ENNReal.add_lt_top.mpr ⟨hρ_fin, ENNReal.ofReal_lt_top⟩))

lemma hLayerTrunc_fst_ae {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ)
    (a b : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    ((hLayerTrunc hα0 hαhalf g hg r a b ha0 hab hb1).1.fst : ℝ → ℝ) =ᵐ[μI]
      hLayerTruncFun g r a b :=
  mkH_fst_ae _ _ _ _

lemma hLayerTrunc_mem_Gsub {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ)
    (a b : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    hLayerTrunc hα0 hαhalf g hg r a b ha0 hab hb1 ∈ Gsub (sVal α) := by
  filter_upwards [hLayerTrunc_fst_ae hα0 hαhalf g hg r a b ha0 hab hb1] with x hx
  rw [hx]
  obtain ⟨n, hn⟩ := hLayerTruncFun_int g r a b x
  exact ⟨n, hn.symm⟩

lemma hLayerTrunc_norm_sq_le {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ)
    (a b : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    ‖hLayerTrunc hα0 hαhalf g hg r a b ha0 hab hb1‖ ^ 2 ≤
      (∫⁻ x in Set.Icc a b, ρE (sVal α) g r x ∂μI).toReal +
        (1 + 1 / ((α : ℝ) * sVal α)) * (2 : ℝ) ^ (2 * r) *
          (μI (Eset g r ∩ Set.Icc a b)).toReal ^ (2 * (α : ℝ)) := by
  have hα_pos : (0 : ℝ) < (α : ℝ) := NNReal.coe_pos.mpr hα0
  have hα_lt : (α : ℝ) < 1 / 2 := by exact_mod_cast hαhalf
  have hs0 : 0 < sVal α := by dsimp [sVal]; linarith
  rw [Hsub_norm_sq_eq _ (hLayerTrunc_fst_ae hα0 hαhalf g hg r a b ha0 hab hb1)]
  have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hLayerTrunc_L2_le hα0 hαhalf g r (a := a) (b := b))
  rw [ENNReal.toReal_ofReal (by positivity)] at h1
  have hρ_fin : ∫⁻ x in Set.Icc a b, ρE (sVal α) g r x ∂μI ≠ ⊤ :=
    (lt_of_le_of_lt (setLIntegral_le_lintegral _ _)
      (by rw [lintegral_ρE_eq]; exact σvalE_lt_top hg r)).ne
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hρ_fin, ENNReal.ofReal_ne_top⟩)
    (hLayerTrunc_sem_le hα0 hαhalf g r ha0 hab hb1)
  rw [ENNReal.toReal_add hρ_fin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity)] at h2
  linarith

noncomputable def wDens (α : NNReal) (g : Hsub (sVal α)) (r : ℕ) (x : ℝ) : ℝ :=
  Iset.indicator
    (fun t => (ρE (sVal α) g r t).toReal +
      (Eset g r).indicator (fun _ => (2 : ℝ) ^ ((r : ℝ) / (α : ℝ))) t) x

lemma wDens_nonneg (α : NNReal) (g : Hsub (sVal α)) (r : ℕ) (x : ℝ) : 0 ≤ wDens α g r x := by
  unfold wDens
  by_cases hx : x ∈ Iset
  · rw [Set.indicator_of_mem hx]
    apply add_nonneg ENNReal.toReal_nonneg
    by_cases hxE : x ∈ Eset g r
    · rw [Set.indicator_of_mem hxE]; positivity
    · rw [Set.indicator_of_notMem hxE]
  · rw [Set.indicator_of_notMem hx]

lemma measurable_wDens (α : NNReal) (g : Hsub (sVal α)) (r : ℕ) : Measurable (wDens α g r) := by
  unfold wDens
  refine Measurable.indicator ?_ measurableSet_Iset
  exact (measurable_ρE (sVal α) g r).ennreal_toReal.add
    (measurable_const.indicator (measurableSet_Eset g r))

lemma setLIntegral_wDens_eq {α : NNReal} (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ)
    {A : Set ℝ} (hA_meas : MeasurableSet A) (hA_sub : A ⊆ Iset) :
    ∫⁻ x in A, ENNReal.ofReal (wDens α g r x) ∂volume =
      (∫⁻ x in A, ρE (sVal α) g r x ∂μI) +
        ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) / (α : ℝ))) * μI (Eset g r ∩ A) := by
  have hres : volume.restrict A = μI.restrict A := by
    rw [μI, Measure.restrict_restrict hA_meas, Set.inter_eq_left.mpr hA_sub]
  rw [hres]
  have hae_fin : ∀ᵐ x ∂μI, ρE (sVal α) g r x < ⊤ :=
    ae_lt_top (measurable_ρE (sVal α) g r) (by rw [lintegral_ρE_eq]; exact (σvalE_lt_top hg r).ne)
  have hae_eq : (fun x => ENNReal.ofReal (wDens α g r x)) =ᵐ[μI.restrict A]
      fun x => ρE (sVal α) g r x +
        (Eset g r).indicator (fun _ => ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) / (α : ℝ)))) x := by
    filter_upwards [ae_restrict_mem hA_meas, ae_restrict_of_ae hae_fin] with x hxA hxfin
    have hxI : x ∈ Iset := hA_sub hxA
    unfold wDens
    rw [Set.indicator_of_mem hxI]
    by_cases hxE : x ∈ Eset g r
    · rw [Set.indicator_of_mem hxE, Set.indicator_of_mem hxE,
        ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
        ENNReal.ofReal_toReal hxfin.ne]
    · rw [Set.indicator_of_notMem hxE, Set.indicator_of_notMem hxE, add_zero, add_zero,
        ENNReal.ofReal_toReal hxfin.ne]
  rw [lintegral_congr_ae hae_eq, lintegral_add_left (measurable_ρE (sVal α) g r)]
  congr 1
  rw [lintegral_indicator (measurableSet_Eset g r), setLIntegral_const,
    Measure.restrict_apply (measurableSet_Eset g r)]

lemma integrable_wDens {α : NNReal} (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ) :
    Integrable (wDens α g r) volume := by
  refine ⟨(measurable_wDens α g r).aestronglyMeasurable, ?_⟩
  change ∫⁻ x, ‖wDens α g r x‖ₑ ∂volume < ⊤
  have heq : ∫⁻ x, ‖wDens α g r x‖ₑ ∂volume = ∫⁻ x in Iset, ENNReal.ofReal (wDens α g r x) ∂volume := by
    rw [← lintegral_indicator measurableSet_Iset]
    apply lintegral_congr
    intro x
    rw [Real.enorm_eq_ofReal (wDens_nonneg α g r x)]
    by_cases hx : x ∈ Iset
    · simp [hx]
    · simp [hx, wDens]
  rw [heq, setLIntegral_wDens_eq g hg r measurableSet_Iset Set.Subset.rfl]
  have h1 : ∫⁻ x in Iset, ρE (sVal α) g r x ∂μI < ⊤ :=
    lt_of_le_of_lt (setLIntegral_le_lintegral _ _) (by rw [lintegral_ρE_eq]; exact σvalE_lt_top hg r)
  have h2 : ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) / (α : ℝ))) * μI (Eset g r ∩ Iset) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  exact ENNReal.add_lt_top.mpr ⟨h1, h2⟩

noncomputable def Llen (α : NNReal) (g : Hsub (sVal α)) (r : ℕ) : ℝ :=
  σval (sVal α) g r + aSeq α g r

lemma Llen_nonneg (α : NNReal) (g : Hsub (sVal α)) (r : ℕ) : 0 ≤ Llen α g r :=
  add_nonneg ENNReal.toReal_nonneg (aSeq_nonneg α g r)

lemma summable_Llen {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    {g : Hsub (sVal α)} (hg : g ∈ Gsub (sVal α)) :
    Summable (Llen α g) :=
  (summable_σval_and_tsum_le hg).1.add (summable_aSeq hα0 hαhalf hg)

lemma hLayerH_norm_sq_le_Llen {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ) :
    ‖hLayerH g hg r‖ ^ 2 ≤ Llen α g r := by
  have hα_pos : (0 : ℝ) < (α : ℝ) := NNReal.coe_pos.mpr hα0
  have hα_lt : (α : ℝ) < 1 / 2 := by exact_mod_cast hαhalf
  rw [hLayerH_norm_sq_eq g hg r]
  unfold Llen aSeq
  have hL2 : (∫⁻ x, ENNReal.ofReal (hLayer g r x ^ 2) ∂μI).toReal ≤
      (2 : ℝ) ^ ((r : ℝ) / (α : ℝ)) * (μI (Eset g r)).toReal := by
    have h1 : ∫⁻ x, ENNReal.ofReal (hLayer g r x ^ 2) ∂μI ≤
        ENNReal.ofReal ((2 : ℝ) ^ (2 * r)) * μI (Eset g r) := by
      rw [← setLIntegral_const, ← lintegral_indicator (measurableSet_Eset g r)]
      apply lintegral_mono_ae
      filter_upwards [ae_mem_Iset] with x hxI
      by_cases hxE : x ∈ Eset g r
      · rw [Set.indicator_of_mem hxE]
        apply ENNReal.ofReal_le_ofReal
        rw [← sq_abs]
        have h2 := abs_phi_le_two_pow r (intRep g x)
        have hsq : |hLayer g r x| ^ 2 ≤ ((2 : ℝ) ^ r) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h2 2
        rwa [← pow_mul, mul_comm r 2] at hsq
      · rw [Set.indicator_of_notMem hxE, hLayer_eq_zero_of_not_mem_Eset g r hxI hxE]
        simp
    have hto := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hto
    refine hto.trans (mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg)
    have h2nat : (2 : ℝ) ^ (2 * r) = (2 : ℝ) ^ ((2 * r : ℕ) : ℝ) := (Real.rpow_natCast 2 (2 * r)).symm
    rw [h2nat]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    have h2le : (2 : ℝ) ≤ 1 / (α : ℝ) := by
      rw [le_div_iff₀ hα_pos]; linarith
    have : 2 * (r : ℝ) ≤ (1 / (α : ℝ)) * (r : ℝ) :=
      mul_le_mul_of_nonneg_right h2le (Nat.cast_nonneg r)
    linarith [show (1 / (α : ℝ)) * (r : ℝ) = (r : ℝ) / (α : ℝ) by ring]
  linarith

lemma summable_hLayerH_norm_sq {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) :
    Summable (fun r => ‖hLayerH g hg r‖ ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (hLayerH_norm_sq_le_Llen hα0 hαhalf g hg)
    (summable_Llen hα0 hαhalf hg)

noncomputable def Fcum (α : NNReal) (g : Hsub (sVal α)) (r : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, wDens α g r t

lemma continuous_Fcum {α : NNReal} (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ) :
    Continuous (Fcum α g r) :=
  intervalIntegral.continuous_primitive (fun _ _ => (integrable_wDens g hg r).intervalIntegrable) 0

lemma Fcum_zero (α : NNReal) (g : Hsub (sVal α)) (r : ℕ) : Fcum α g r 0 = 0 :=
  intervalIntegral.integral_same

lemma Fcum_sub_eq {α : NNReal} (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    Fcum α g r b - Fcum α g r a =
      (∫⁻ x in Set.Icc a b, ρE (sVal α) g r x ∂μI).toReal +
        (2 : ℝ) ^ ((r : ℝ) / (α : ℝ)) * (μI (Eset g r ∩ Set.Icc a b)).toReal := by
  have hint := integrable_wDens g hg r
  have hadj : (∫ t in (0 : ℝ)..a, wDens α g r t) + (∫ t in a..b, wDens α g r t) =
      ∫ t in (0 : ℝ)..b, wDens α g r t :=
    intervalIntegral.integral_add_adjacent_intervals hint.intervalIntegrable hint.intervalIntegrable
  have hsub : Fcum α g r b - Fcum α g r a = ∫ t in a..b, wDens α g r t := by
    unfold Fcum; linarith
  rw [hsub, intervalIntegral.integral_of_le hab]
  have hnn : 0 ≤ ∫ t in Set.Ioc a b, wDens α g r t :=
    integral_nonneg (wDens_nonneg α g r)
  have hof : ENNReal.ofReal (∫ t in Set.Ioc a b, wDens α g r t) =
      ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (wDens α g r t) ∂volume :=
    ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (ae_of_all _ (wDens_nonneg α g r))
  have hIoc_eq : ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (wDens α g r t) ∂volume =
      ∫⁻ t in Set.Icc a b, ENNReal.ofReal (wDens α g r t) ∂volume := by
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have hIcc_sub : Set.Icc a b ⊆ Iset := fun x hx => ⟨ha0.trans hx.1, hx.2.trans hb1⟩
  have hlin := setLIntegral_wDens_eq g hg r measurableSet_Icc hIcc_sub
  rw [hIoc_eq, hlin] at hof
  have h1fin : ∫⁻ x in Set.Icc a b, ρE (sVal α) g r x ∂μI ≠ ⊤ :=
    (lt_of_le_of_lt (setLIntegral_le_lintegral _ _)
      (by rw [lintegral_ρE_eq]; exact σvalE_lt_top hg r)).ne
  have h2fin : ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) / (α : ℝ))) * μI (Eset g r ∩ Set.Icc a b) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hto := congrArg ENNReal.toReal hof
  rw [ENNReal.toReal_ofReal hnn, ENNReal.toReal_add h1fin h2fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hto
  exact hto

lemma Fcum_mono {α : NNReal} (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ) :
    Monotone (Fcum α g r) := by
  intro a b hab
  have hint := integrable_wDens g hg r
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := a) (c := b) hint.intervalIntegrable hint.intervalIntegrable
  have hnn : 0 ≤ ∫ t in a..b, wDens α g r t := by
    rw [intervalIntegral.integral_of_le hab]
    exact integral_nonneg (wDens_nonneg α g r)
  unfold Fcum
  linarith

lemma Fcum_one {α : NNReal} (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ) :
    Fcum α g r 1 = Llen α g r := by
  have h := Fcum_sub_eq g hg r le_rfl zero_le_one le_rfl
  rw [Fcum_zero, sub_zero] at h
  have h1 : ∫⁻ x in Set.Icc (0 : ℝ) 1, ρE (sVal α) g r x ∂μI = σvalE (sVal α) g r := by
    rw [← lintegral_ρE_eq (sVal α) g r]
    change ∫⁻ x in Iset, ρE (sVal α) g r x ∂μI = _
    rw [μI, Measure.restrict_restrict measurableSet_Iset, Set.inter_self]
  have h2 : Eset g r ∩ Set.Icc (0 : ℝ) 1 = Eset g r :=
    Set.inter_eq_left.mpr (fun _ hx => hx.1)
  rw [h, h1, h2]
  rfl

noncomputable def tau (α : NNReal) (g : Hsub (sVal α)) (r : ℕ) (u : ℝ) : ℝ :=
  sInf {x ∈ Iset | max 0 (min (Llen α g r) u) ≤ Fcum α g r x}

lemma tau_mem_Iset {α : NNReal} (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ) (u : ℝ) :
    tau α g r u ∈ Iset := by
  let u' := max 0 (min (Llen α g r) u)
  let S := {x ∈ Iset | u' ≤ Fcum α g r x}
  have hu'_le : u' ≤ Llen α g r := max_le (Llen_nonneg α g r) (min_le_left _ _)
  have hclosed : IsClosed S :=
    isClosed_Icc.inter (isClosed_le continuous_const (continuous_Fcum g hg r))
  have hne : S.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [Fcum_one g hg r]; exact hu'_le⟩
  have hbdd : BddBelow S := ⟨0, fun _ hx => hx.1.1⟩
  exact (hclosed.csInf_mem hne hbdd).1

lemma Fcum_tau_eq {α : NNReal} (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ)
    {u : ℝ} (hu0 : 0 ≤ u) (huL : u ≤ Llen α g r) :
    Fcum α g r (tau α g r u) = u := by
  have hu' : max 0 (min (Llen α g r) u) = u := by
    rw [min_eq_right huL, max_eq_right hu0]
  let S := {x ∈ Iset | max 0 (min (Llen α g r) u) ≤ Fcum α g r x}
  have hclosed : IsClosed S :=
    isClosed_Icc.inter (isClosed_le continuous_const (continuous_Fcum g hg r))
  have hne : S.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [hu', Fcum_one g hg r]; exact huL⟩
  have hbdd : BddBelow S := ⟨0, fun _ hx => hx.1.1⟩
  have hmem : tau α g r u ∈ S := hclosed.csInf_mem hne hbdd
  have hge : u ≤ Fcum α g r (tau α g r u) := by
    have := hmem.2; rwa [hu'] at this
  have hivt : u ∈ Set.Icc (Fcum α g r 0) (Fcum α g r 1) := by
    rw [Fcum_zero, Fcum_one g hg r]; exact ⟨hu0, huL⟩
  obtain ⟨x₀, hx₀I, hx₀eq⟩ :=
    intermediate_value_Icc zero_le_one (continuous_Fcum g hg r).continuousOn hivt
  have hx₀S : x₀ ∈ S := ⟨hx₀I, by rw [hu', hx₀eq]⟩
  have hle_x0 : tau α g r u ≤ x₀ := csInf_le hbdd hx₀S
  have hle : Fcum α g r (tau α g r u) ≤ u :=
    (Fcum_mono g hg r hle_x0).trans_eq hx₀eq
  exact le_antisymm hle hge

lemma tau_zero {α : NNReal} (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ) :
    tau α g r 0 = 0 := by
  have hu' : max 0 (min (Llen α g r) 0) = 0 := by
    rw [min_eq_right (Llen_nonneg α g r), max_self]
  let S := {x ∈ Iset | max 0 (min (Llen α g r) 0) ≤ Fcum α g r x}
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, zero_le_one⟩, by rw [hu', Fcum_zero]⟩
  have hbdd : BddBelow S := ⟨0, fun _ hx => hx.1.1⟩
  exact le_antisymm (csInf_le hbdd h0S) (tau_mem_Iset g hg r 0).1

lemma tau_mono {α : NNReal} (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ) :
    Monotone (tau α g r) := by
  intro u₁ u₂ hu
  have hu' : max 0 (min (Llen α g r) u₁) ≤ max 0 (min (Llen α g r) u₂) :=
    max_le_max le_rfl (min_le_min le_rfl hu)
  let S₁ := {x ∈ Iset | max 0 (min (Llen α g r) u₁) ≤ Fcum α g r x}
  let S₂ := {x ∈ Iset | max 0 (min (Llen α g r) u₂) ≤ Fcum α g r x}
  have hne₂ : S₂.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, by
    rw [Fcum_one g hg r]; exact max_le (Llen_nonneg α g r) (min_le_left _ _)⟩
  have hbdd₁ : BddBelow S₁ := ⟨0, fun _ hx => hx.1.1⟩
  have hsub : S₂ ⊆ S₁ := fun x hx => ⟨hx.1, hu'.trans hx.2⟩
  exact csInf_le_csInf hbdd₁ hne₂ hsub

noncomputable def gammaLayer {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ) (u : ℝ) : Hsub (sVal α) :=
  hLayerTrunc hα0 hαhalf g hg r 0 (tau α g r u) le_rfl
    (tau_mem_Iset g hg r u).1 (tau_mem_Iset g hg r u).2

lemma gammaLayer_mem_Gsub {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ) (u : ℝ) :
    gammaLayer hα0 hαhalf g hg r u ∈ Gsub (sVal α) :=
  hLayerTrunc_mem_Gsub hα0 hαhalf g hg r 0 (tau α g r u) le_rfl _ _

lemma gammaLayer_zero {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ) :
    gammaLayer hα0 hαhalf g hg r 0 = 0 := by
  apply Hsub_eq_of_fst_ae
  have hne0 : ∀ᵐ x ∂μI, x ≠ 0 := ae_iff.mpr (by simpa using μI_singleton 0)
  filter_upwards [hLayerTrunc_fst_ae hα0 hαhalf g hg r 0 (tau α g r 0) le_rfl
      (tau_mem_Iset g hg r 0).1 (tau_mem_Iset g hg r 0).2,
    Lp.coeFn_zero ℝ 2 μI, hne0] with x hx1 hx0 hxne
  dsimp only [gammaLayer]
  rw [hx1]
  simp only [Pi.zero_apply] at hx0
  change hLayerTruncFun g r 0 (tau α g r 0) x = ((0 : Lp ℝ 2 μI) : ℝ → ℝ) x
  rw [hx0]
  unfold hLayerTruncFun
  rw [tau_zero g hg r]
  have hnot : x ∉ Set.Icc (0 : ℝ) 0 := fun h => hxne (le_antisymm h.2 h.1)
  exact Set.indicator_of_notMem hnot _

lemma gammaLayer_end {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ) :
    gammaLayer hα0 hαhalf g hg r (Llen α g r) = hLayerH g hg r := by
  apply Hsub_eq_of_fst_ae
  set τ := tau α g r (Llen α g r)
  have hτI : τ ∈ Iset := tau_mem_Iset g hg r (Llen α g r)
  have hF_sub := Fcum_sub_eq g hg r hτI.1 hτI.2 le_rfl
  rw [Fcum_one g hg r, Fcum_tau_eq g hg r (Llen_nonneg α g r) le_rfl, sub_self] at hF_sub
  have hμ0_real : (μI (Eset g r ∩ Set.Icc τ 1)).toReal = 0 := by
    have h1 : 0 ≤ (∫⁻ x in Set.Icc τ 1, ρE (sVal α) g r x ∂μI).toReal := ENNReal.toReal_nonneg
    have h2 : 0 < (2 : ℝ) ^ ((r : ℝ) / (α : ℝ)) := by positivity
    have h3 : 0 ≤ (μI (Eset g r ∩ Set.Icc τ 1)).toReal := ENNReal.toReal_nonneg
    nlinarith
  have hμ0 : μI (Eset g r ∩ Set.Icc τ 1) = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp hμ0_real).resolve_right (measure_ne_top _ _)
  have hae_not : ∀ᵐ x ∂μI, x ∉ Eset g r ∩ Set.Icc τ 1 := by
    rw [ae_iff]
    have heq : {x : ℝ | ¬ (x ∉ Eset g r ∩ Set.Icc τ 1)} = Eset g r ∩ Set.Icc τ 1 := by
      ext x; simp only [Set.mem_ofPred_eq, not_not]
    rw [heq]; exact hμ0
  filter_upwards [ae_mem_Iset, hae_not,
    hLayerTrunc_fst_ae hα0 hαhalf g hg r 0 τ le_rfl hτI.1 hτI.2,
    hLayerH_fst_ae g hg r] with x hxI hxnot hx1 hx2
  dsimp only [gammaLayer]
  rw [hx1, hx2]
  unfold hLayerTruncFun
  by_cases hxle : x ≤ τ
  · rw [Set.indicator_of_mem (show x ∈ Set.Icc 0 τ from ⟨hxI.1, hxle⟩)]
  · push Not at hxle
    rw [Set.indicator_of_notMem (fun h => not_lt.mpr h.2 hxle)]
    have hxE : x ∉ Eset g r := fun h => hxnot ⟨h, hxle.le, hxI.2⟩
    exact (hLayer_eq_zero_of_not_mem_Eset g r hxI hxE).symm

lemma gammaLayer_sub_eq {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ)
    {u₁ u₂ : ℝ} (hu : u₁ ≤ u₂) :
    gammaLayer hα0 hαhalf g hg r u₂ - gammaLayer hα0 hαhalf g hg r u₁ =
      hLayerTrunc hα0 hαhalf g hg r (tau α g r u₁) (tau α g r u₂)
        (tau_mem_Iset g hg r u₁).1 (tau_mono g hg r hu) (tau_mem_Iset g hg r u₂).2 := by
  apply Hsub_eq_of_fst_ae
  set a := tau α g r u₁
  set b := tau α g r u₂
  have hab : a ≤ b := tau_mono g hg r hu
  have haI : a ∈ Iset := tau_mem_Iset g hg r u₁
  have hbI : b ∈ Iset := tau_mem_Iset g hg r u₂
  have hnea : ∀ᵐ x ∂μI, x ≠ a := ae_iff.mpr (by simpa using μI_singleton a)
  filter_upwards [ae_mem_Iset, hnea,
    Lp.coeFn_sub (gammaLayer hα0 hαhalf g hg r u₂).1.fst (gammaLayer hα0 hαhalf g hg r u₁).1.fst,
    hLayerTrunc_fst_ae hα0 hαhalf g hg r 0 b le_rfl hbI.1 hbI.2,
    hLayerTrunc_fst_ae hα0 hαhalf g hg r 0 a le_rfl haI.1 haI.2,
    hLayerTrunc_fst_ae hα0 hαhalf g hg r a b haI.1 hab hbI.2] with x hxI hxa hsub hx2 hx1 hxab
  change (((gammaLayer hα0 hαhalf g hg r u₂).1.fst -
    (gammaLayer hα0 hαhalf g hg r u₁).1.fst : Lp ℝ 2 μI) : ℝ → ℝ) x = _
  simp only [Pi.sub_apply] at hsub
  rw [hsub]
  dsimp only [gammaLayer]
  rw [hx2, hx1, hxab]
  unfold hLayerTruncFun
  by_cases h1 : x ≤ a
  · have hlt : x < a := lt_of_le_of_ne h1 hxa
    rw [Set.indicator_of_mem (show x ∈ Set.Icc 0 b from ⟨hxI.1, h1.trans hab⟩),
      Set.indicator_of_mem (show x ∈ Set.Icc 0 a from ⟨hxI.1, h1⟩),
      Set.indicator_of_notMem (fun h => not_lt.mpr h.1 hlt), sub_self]
  · push Not at h1
    by_cases h2 : x ≤ b
    · rw [Set.indicator_of_mem (show x ∈ Set.Icc 0 b from ⟨hxI.1, h2⟩),
        Set.indicator_of_notMem (fun h => not_lt.mpr h.2 h1),
        Set.indicator_of_mem (show x ∈ Set.Icc a b from ⟨h1.le, h2⟩), sub_zero]
    · push Not at h2
      rw [Set.indicator_of_notMem (fun h => not_lt.mpr h.2 h2),
        Set.indicator_of_notMem (fun h => not_lt.mpr h.2 h1),
        Set.indicator_of_notMem (fun h => not_lt.mpr h.2 h2), sub_self]

lemma gammaLayer_holder {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (r : ℕ)
    {L : ℝ} (hL_ge : Llen α g r ≤ L)
    (u₁ u₂ : ℝ) (hu₁ : 0 ≤ u₁) (hu₁₂ : u₁ ≤ u₂) (hu₂ : u₂ ≤ Llen α g r) :
    ‖gammaLayer hα0 hαhalf g hg r u₂ - gammaLayer hα0 hαhalf g hg r u₁‖ ≤
      Real.sqrt (L ^ (1 - 2 * (α : ℝ)) + 1 + 1 / ((α : ℝ) * sVal α)) *
        (u₂ - u₁) ^ (α : ℝ) := by
  have hα_pos : (0 : ℝ) < (α : ℝ) := NNReal.coe_pos.mpr hα0
  have hα_lt : (α : ℝ) < 1 / 2 := by exact_mod_cast hαhalf
  have hs0 : 0 < sVal α := by dsimp [sVal]; linarith
  have hL_nn : 0 ≤ L := (Llen_nonneg α g r).trans hL_ge
  have hdu_nn : 0 ≤ u₂ - u₁ := sub_nonneg.mpr hu₁₂
  have hdu_le_L : u₂ - u₁ ≤ L := by linarith
  set a := tau α g r u₁
  set b := tau α g r u₂
  have haI := tau_mem_Iset g hg r u₁
  have hbI := tau_mem_Iset g hg r u₂
  have hab : a ≤ b := tau_mono g hg r hu₁₂
  rw [gammaLayer_sub_eq hα0 hαhalf g hg r hu₁₂]
  have hnorm_sq := hLayerTrunc_norm_sq_le hα0 hαhalf g hg r a b haI.1 hab hbI.2
  have hF_sub := Fcum_sub_eq g hg r haI.1 hab hbI.2
  rw [Fcum_tau_eq g hg r (hu₁.trans hu₁₂) hu₂,
    Fcum_tau_eq g hg r hu₁ (hu₁₂.trans hu₂)] at hF_sub
  have hterm1 : (∫⁻ x in Set.Icc a b, ρE (sVal α) g r x ∂μI).toReal ≤
      L ^ (1 - 2 * (α : ℝ)) * (u₂ - u₁) ^ (2 * (α : ℝ)) := by
    have hle_du : (∫⁻ x in Set.Icc a b, ρE (sVal α) g r x ∂μI).toReal ≤ u₂ - u₁ := by
      have : 0 ≤ (2 : ℝ) ^ ((r : ℝ) / (α : ℝ)) * (μI (Eset g r ∩ Set.Icc a b)).toReal :=
        mul_nonneg (by positivity) ENNReal.toReal_nonneg
      linarith
    have hsplit : u₂ - u₁ = (u₂ - u₁) ^ (1 - 2 * (α : ℝ)) * (u₂ - u₁) ^ (2 * (α : ℝ)) := by
      by_cases h0 : u₂ - u₁ = 0
      · rw [h0, Real.zero_rpow (by linarith), zero_mul]
      · rw [← Real.rpow_add (lt_of_le_of_ne hdu_nn (Ne.symm h0)),
          show 1 - 2 * (α : ℝ) + 2 * (α : ℝ) = 1 by ring, Real.rpow_one]
    calc
      (∫⁻ x in Set.Icc a b, ρE (sVal α) g r x ∂μI).toReal
          ≤ u₂ - u₁ := hle_du
      _ = (u₂ - u₁) ^ (1 - 2 * (α : ℝ)) * (u₂ - u₁) ^ (2 * (α : ℝ)) := hsplit
      _ ≤ L ^ (1 - 2 * (α : ℝ)) * (u₂ - u₁) ^ (2 * (α : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hdu_nn hdu_le_L (by linarith : 0 ≤ 1 - 2 * (α : ℝ)))
            (Real.rpow_nonneg hdu_nn _)
  have hterm2 : (2 : ℝ) ^ (2 * r) * (μI (Eset g r ∩ Set.Icc a b)).toReal ^ (2 * (α : ℝ)) ≤
      (u₂ - u₁) ^ (2 * (α : ℝ)) := by
    have hle_du : (2 : ℝ) ^ ((r : ℝ) / (α : ℝ)) * (μI (Eset g r ∩ Set.Icc a b)).toReal ≤ u₂ - u₁ := by
      have : 0 ≤ (∫⁻ x in Set.Icc a b, ρE (sVal α) g r x ∂μI).toReal := ENNReal.toReal_nonneg
      linarith
    have hrew : (2 : ℝ) ^ (2 * r) * (μI (Eset g r ∩ Set.Icc a b)).toReal ^ (2 * (α : ℝ)) =
        ((2 : ℝ) ^ ((r : ℝ) / (α : ℝ)) * (μI (Eset g r ∩ Set.Icc a b)).toReal) ^ (2 * (α : ℝ)) := by
      rw [Real.mul_rpow (by positivity) ENNReal.toReal_nonneg, ← Real.rpow_mul (by norm_num)]
      congr 1
      have hexp : (r : ℝ) / (α : ℝ) * (2 * (α : ℝ)) = ((2 * r : ℕ) : ℝ) := by
        push_cast; field_simp [hα_pos.ne']
      rw [hexp, Real.rpow_natCast]
    rw [hrew]
    exact Real.rpow_le_rpow (mul_nonneg (by positivity) ENNReal.toReal_nonneg) hle_du (by positivity)
  have hsq_bound : ‖hLayerTrunc hα0 hαhalf g hg r a b haI.1 hab hbI.2‖ ^ 2 ≤
      (L ^ (1 - 2 * (α : ℝ)) + 1 + 1 / ((α : ℝ) * sVal α)) * (u₂ - u₁) ^ (2 * (α : ℝ)) := by
    have hc_pos : 0 ≤ 1 + 1 / ((α : ℝ) * sVal α) := by positivity
    have h2' := mul_le_mul_of_nonneg_left hterm2 hc_pos
    linarith
  have hC_nn : 0 ≤ L ^ (1 - 2 * (α : ℝ)) + 1 + 1 / ((α : ℝ) * sVal α) := by positivity
  have hrhs_sq : (Real.sqrt (L ^ (1 - 2 * (α : ℝ)) + 1 + 1 / ((α : ℝ) * sVal α)) *
      (u₂ - u₁) ^ (α : ℝ)) ^ 2 =
      (L ^ (1 - 2 * (α : ℝ)) + 1 + 1 / ((α : ℝ) * sVal α)) * (u₂ - u₁) ^ (2 * (α : ℝ)) := by
    rw [mul_pow, Real.sq_sqrt hC_nn, ← Real.rpow_natCast ((u₂ - u₁) ^ (α : ℝ)) 2,
      ← Real.rpow_mul hdu_nn]
    congr 2; push_cast; ring
  have hle_sq : ‖hLayerTrunc hα0 hαhalf g hg r a b haI.1 hab hbI.2‖ ^ 2 ≤
      (Real.sqrt (L ^ (1 - 2 * (α : ℝ)) + 1 + 1 / ((α : ℝ) * sVal α)) *
        (u₂ - u₁) ^ (α : ℝ)) ^ 2 := by
    rwa [hrhs_sq]
  have hnn1 : 0 ≤ ‖hLayerTrunc hα0 hαhalf g hg r a b haI.1 hab hbI.2‖ := norm_nonneg _
  have hnn2 : 0 ≤ Real.sqrt (L ^ (1 - 2 * (α : ℝ)) + 1 + 1 / ((α : ℝ) * sVal α)) *
      (u₂ - u₁) ^ (α : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hdu_nn (α : ℝ))
  change ‖hLayerTrunc hα0 hαhalf g hg r a b haI.1 hab hbI.2‖ ≤ _
  nlinarith

lemma exists_holder_curve_from_zero {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (g : Hsub (sVal α)) (hg : g ∈ Gsub (sVal α)) (hg0 : g ≠ 0) :
    ∃ (L C₀ : ℝ) (Γ : ℝ → Hsub (sVal α)),
      0 < L ∧ 0 ≤ C₀ ∧ Γ 0 = 0 ∧ Γ L = g ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, Γ t ∈ Gsub (sVal α)) ∧
      (∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ L → ‖Γ t₂ - Γ t₁‖ ≤ C₀ * (t₂ - t₁) ^ (α : ℝ)) := by
  classical
  have hα_pos : (0 : ℝ) < (α : ℝ) := NNReal.coe_pos.mpr hα0
  have hα_lt : (α : ℝ) < 1 / 2 := by exact_mod_cast hαhalf
  have hs0 : 0 < sVal α := by dsimp [sVal]; linarith
  have hL_summ : Summable (Llen α g) := summable_Llen hα0 hαhalf hg
  have hH_summ : Summable (fun r => ‖hLayerH g hg r‖ ^ 2) :=
    summable_hLayerH_norm_sq hα0 hαhalf g hg
  let L : ℝ := ∑' r, Llen α g r
  have hL0_pos : 0 < Llen α g 0 := by
    have hge0 : 0 ≤ Llen α g 0 := Llen_nonneg α g 0
    refine lt_of_le_of_ne hge0 (Ne.symm ?_)
    intro h0
    have ha0_eq : aSeq α g 0 = 0 := by
      unfold Llen at h0
      linarith [show 0 ≤ σval (sVal α) g 0 from ENNReal.toReal_nonneg, aSeq_nonneg α g 0]
    have hμE0 : (μI (Eset g 0)).toReal = 0 := by
      unfold aSeq at ha0_eq
      simpa using ha0_eq
    have hμ0 : μI (Eset g 0) = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).mp hμE0).resolve_right (measure_ne_top _ _)
    have hae0 : (g.1.fst : ℝ → ℝ) =ᵐ[μI] ((0 : Hsub (sVal α)).1.fst : ℝ → ℝ) := by
      have hnotE : ∀ᵐ x ∂μI, x ∉ Eset g 0 := ae_iff.mpr (by simpa using hμ0)
      filter_upwards [ae_mem_Iset, hnotE, intRep_ae_eq hg, Lp.coeFn_zero ℝ 2 μI] with x hxI hxE hxg hx0
      simp only [Pi.zero_apply] at hx0
      have hle0 : |intRep g x| ≤ 0 := by
        by_contra hgt
        push Not at hgt
        exact hxE ⟨hxI, by simpa [Mthresh] using hgt⟩
      have hfx : intRep g x = 0 := abs_nonpos_iff.mp hle0
      rw [hxg, hfx]; exact hx0.symm
    exact hg0 (Hsub_eq_of_fst_ae hae0)
  have hL_pos : 0 < L := lt_of_lt_of_le hL0_pos
    (hL_summ.le_tsum 0 (fun r _ => Llen_nonneg α g r))
  let S : ℕ → ℝ := fun k => ∑ r ∈ Finset.range k, Llen α g r
  have hS_zero : S 0 = 0 := by simp [S]
  have hS_succ : ∀ k, S (k + 1) = S k + Llen α g k := fun k => Finset.sum_range_succ _ k
  have hS_mono : Monotone S :=
    monotone_nat_of_le_succ (fun k => by rw [hS_succ]; linarith [Llen_nonneg α g k])
  have hS_tendsto : Tendsto S atTop (𝓝 L) := hL_summ.hasSum.tendsto_sum_nat
  have hS_le_L : ∀ k, S k ≤ L := fun k =>
    hL_summ.sum_le_tsum (Finset.range k) (fun r _ => Llen_nonneg α g r)
  have hex_k : ∀ t : ℝ, t < L → ∃ k : ℕ, t < S (k + 1) := by
    intro t ht
    have hev := hS_tendsto.eventually (Ioi_mem_nhds ht)
    obtain ⟨n, hn⟩ := hev.exists
    exact ⟨n, lt_of_lt_of_le hn (hS_mono (Nat.le_succ n))⟩
  let kIdx : ∀ t : ℝ, t < L → ℕ := fun t ht => Nat.find (hex_k t ht)
  have hk_upper : ∀ t (ht : t < L), t < S (kIdx t ht + 1) :=
    fun t ht => Nat.find_spec (hex_k t ht)
  have hk_lower : ∀ t (ht0 : 0 ≤ t) (ht : t < L), S (kIdx t ht) ≤ t := by
    intro t ht0 ht
    cases hk : kIdx t ht with
    | zero => rw [hS_zero]; exact ht0
    | succ m =>
      have hmin := Nat.find_min (hex_k t ht) (show m < kIdx t ht by rw [hk]; exact Nat.lt_succ_self m)
      exact not_lt.mp hmin
  let Γ : ℝ → Hsub (sVal α) := fun t =>
    if h : 0 ≤ t ∧ t < L then
      (∑ r ∈ Finset.range (kIdx t h.2), hLayerH g hg r) +
        gammaLayer hα0 hαhalf g hg (kIdx t h.2) (t - S (kIdx t h.2))
    else if t = L then g else 0
  let C₁ : ℝ := Real.sqrt (L ^ (1 - 2 * (α : ℝ)) + 1 + 1 / ((α : ℝ) * sVal α))
  let C₂ : ℝ := Real.sqrt (10 * L ^ (1 - 2 * (α : ℝ)))
  let C₀ : ℝ := 2 * C₁ + C₂
  have hC₁_nn : 0 ≤ C₁ := Real.sqrt_nonneg _
  have hC₂_nn : 0 ≤ C₂ := Real.sqrt_nonneg _
  have hC₀_nn : 0 ≤ C₀ := by linarith
  have hLlen_le_L : ∀ r : ℕ, Llen α g r ≤ L := fun r =>
    hL_summ.le_tsum r (fun k _ => Llen_nonneg α g k)
  have hΓ_end : Γ L = g := by
    dsimp only [Γ]
    rw [dif_neg (fun h => lt_irrefl L h.2), if_pos rfl]
  refine ⟨L, C₀, Γ, hL_pos, hC₀_nn, ?_, hΓ_end, ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) < L := ⟨le_rfl, hL_pos⟩
    dsimp only [Γ]
    rw [dif_pos h0]
    have hk0 : kIdx 0 hL_pos = 0 := by
      refine Nat.eq_zero_of_le_zero ?_
      have hspec : (0 : ℝ) < S (0 + 1) := by rw [hS_succ, hS_zero, zero_add]; exact hL0_pos
      exact Nat.find_min' (hex_k 0 hL_pos) hspec
    rw [hk0, Finset.range_zero, Finset.sum_empty, hS_zero, sub_zero, zero_add]
    exact gammaLayer_zero hα0 hαhalf g hg 0
  · intro t ht
    dsimp only [Γ]
    by_cases hlt : t < L
    · rw [dif_pos ⟨ht.1, hlt⟩]
      refine (Gsub (sVal α)).add_mem ?_ (gammaLayer_mem_Gsub hα0 hαhalf g hg _ _)
      exact (Gsub (sVal α)).sum_mem (fun r _ => hLayerH_mem_Gsub g hg r)
    · have heq : t = L := le_antisymm ht.2 (not_lt.mp hlt)
      rw [dif_neg (fun h => hlt h.2), if_pos heq]
      exact hg
  · intro t₁ t₂ ht₁ ht₁₂ ht₂
    by_cases heq : t₁ = t₂
    · subst heq; simp [mul_nonneg hC₀_nn (Real.rpow_nonneg le_rfl _)]
    · have ht₁_lt_t₂ : t₁ < t₂ := lt_of_le_of_ne ht₁₂ heq
      have ht₁_lt_L : t₁ < L := lt_of_lt_of_le ht₁_lt_t₂ ht₂
      let j := kIdx t₁ ht₁_lt_L
      have hj_lo : S j ≤ t₁ := hk_lower t₁ ht₁ ht₁_lt_L
      have hj_hi : t₁ < S (j + 1) := hk_upper t₁ ht₁_lt_L
      have hΓt₁ : Γ t₁ = (∑ r ∈ Finset.range j, hLayerH g hg r) +
          gammaLayer hα0 hαhalf g hg j (t₁ - S j) := by
        dsimp only [Γ]; rw [dif_pos ⟨ht₁, ht₁_lt_L⟩]
      have hdt_nn : 0 ≤ t₂ - t₁ := sub_nonneg.mpr ht₁₂
      have hdt_le_L : t₂ - t₁ ≤ L := by linarith
      have hdt_pow : t₂ - t₁ ≤ L ^ (1 - 2 * (α : ℝ)) * (t₂ - t₁) ^ (2 * (α : ℝ)) := by
        have hsplit : t₂ - t₁ = (t₂ - t₁) ^ (1 - 2 * (α : ℝ)) * (t₂ - t₁) ^ (2 * (α : ℝ)) := by
          rw [← Real.rpow_add (sub_pos.mpr ht₁_lt_t₂),
            show 1 - 2 * (α : ℝ) + 2 * (α : ℝ) = 1 by ring, Real.rpow_one]
        conv_lhs => rw [hsplit]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hdt_nn hdt_le_L (by linarith : 0 ≤ 1 - 2 * (α : ℝ)))
          (Real.rpow_nonneg hdt_nn _)
      by_cases ht₂_lt : t₂ < L
      · let k := kIdx t₂ ht₂_lt
        have hk_lo : S k ≤ t₂ := hk_lower t₂ (ht₁.trans ht₁₂) ht₂_lt
        have hk_hi : t₂ < S (k + 1) := hk_upper t₂ ht₂_lt
        have hΓt₂ : Γ t₂ = (∑ r ∈ Finset.range k, hLayerH g hg r) +
            gammaLayer hα0 hαhalf g hg k (t₂ - S k) := by
          dsimp only [Γ]; rw [dif_pos ⟨ht₁.trans ht₁₂, ht₂_lt⟩]
        have hjk : j ≤ k := by
          by_contra hgt
          push Not at hgt
          have h1 : S (k + 1) ≤ S j := hS_mono (by omega)
          linarith
        by_cases hjeqk : j = k
        · have hdiff : Γ t₂ - Γ t₁ =
              gammaLayer hα0 hαhalf g hg j (t₂ - S j) -
              gammaLayer hα0 hαhalf g hg j (t₁ - S j) := by
            rw [hΓt₂, hΓt₁, ← hjeqk]; abel
          rw [hdiff]
          have hu2_le : t₂ - S j ≤ Llen α g j := by
            have hk_hi' : t₂ < S (j + 1) := by rwa [← hjeqk] at hk_hi
            rw [hS_succ] at hk_hi'; linarith
          have hbound := gammaLayer_holder hα0 hαhalf g hg j (hLlen_le_L j)
            (t₁ - S j) (t₂ - S j) (by linarith) (by linarith) hu2_le
          have hsub_eq : (t₂ - S j) - (t₁ - S j) = t₂ - t₁ := by ring
          rw [hsub_eq] at hbound
          exact hbound.trans (mul_le_mul_of_nonneg_right (by dsimp only [C₀, C₁]; linarith)
            (Real.rpow_nonneg hdt_nn _))
        · have hjk_lt : j < k := lt_of_le_of_ne hjk hjeqk
          have hsum_split : ∑ r ∈ Finset.range k, hLayerH g hg r =
              (∑ r ∈ Finset.range j, hLayerH g hg r) + hLayerH g hg j +
              ∑ r ∈ Finset.Ico (j + 1) k, hLayerH g hg r := by
            rw [← Finset.sum_range_succ, Finset.sum_range_add_sum_Ico _ (by omega : j + 1 ≤ k)]
          have hdiff : Γ t₂ - Γ t₁ =
              (gammaLayer hα0 hαhalf g hg j (Llen α g j) -
                gammaLayer hα0 hαhalf g hg j (t₁ - S j)) +
              (∑ r ∈ Finset.Ico (j + 1) k, hLayerH g hg r) +
              (gammaLayer hα0 hαhalf g hg k (t₂ - S k) -
                gammaLayer hα0 hαhalf g hg k 0) := by
            rw [hΓt₂, hΓt₁, hsum_split, gammaLayer_end hα0 hαhalf g hg j,
              gammaLayer_zero hα0 hαhalf g hg k]
            abel
          have hterm1 : ‖gammaLayer hα0 hαhalf g hg j (Llen α g j) -
              gammaLayer hα0 hαhalf g hg j (t₁ - S j)‖ ≤ C₁ * (t₂ - t₁) ^ (α : ℝ) := by
            have hu1_le : t₁ - S j ≤ Llen α g j := by rw [hS_succ] at hj_hi; linarith
            have h1 := gammaLayer_holder hα0 hαhalf g hg j (hLlen_le_L j)
              (t₁ - S j) (Llen α g j) (by linarith) hu1_le le_rfl
            have hsub_eq : Llen α g j - (t₁ - S j) = S (j + 1) - t₁ := by rw [hS_succ]; ring
            rw [hsub_eq] at h1
            have hSj1_le_t2 : S (j + 1) ≤ t₂ := (hS_mono (by omega : j + 1 ≤ k)).trans hk_lo
            exact h1.trans (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (by linarith) (by linarith) hα_pos.le) hC₁_nn)
          have hterm2 : ‖∑ r ∈ Finset.Ico (j + 1) k, hLayerH g hg r‖ ≤ C₂ * (t₂ - t₁) ^ (α : ℝ) := by
            have hblk := hBlock_norm_sq_le g hg (j + 1) k
            have hsum_L : ∑ r ∈ Finset.Ico (j + 1) k, ‖hLayerH g hg r‖ ^ 2 ≤ t₂ - t₁ := by
              calc
                ∑ r ∈ Finset.Ico (j + 1) k, ‖hLayerH g hg r‖ ^ 2
                    ≤ ∑ r ∈ Finset.Ico (j + 1) k, Llen α g r :=
                      Finset.sum_le_sum (fun r _ => hLayerH_norm_sq_le_Llen hα0 hαhalf g hg r)
                _ = S k - S (j + 1) := by
                      have := Finset.sum_range_add_sum_Ico (Llen α g) (by omega : j + 1 ≤ k)
                      dsimp only [S]; linarith
                _ ≤ t₂ - t₁ := by linarith
            have hsq : ‖∑ r ∈ Finset.Ico (j + 1) k, hLayerH g hg r‖ ^ 2 ≤
                (C₂ * (t₂ - t₁) ^ (α : ℝ)) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (by positivity),
                ← Real.rpow_natCast ((t₂ - t₁) ^ (α : ℝ)) 2, ← Real.rpow_mul hdt_nn,
                show (α : ℝ) * ((2 : ℕ) : ℝ) = 2 * (α : ℝ) by push_cast; ring]
              linarith
            nlinarith [norm_nonneg (∑ r ∈ Finset.Ico (j + 1) k, hLayerH g hg r),
              mul_nonneg hC₂_nn (Real.rpow_nonneg hdt_nn (α : ℝ))]
          have hterm3 : ‖gammaLayer hα0 hαhalf g hg k (t₂ - S k) -
              gammaLayer hα0 hαhalf g hg k 0‖ ≤ C₁ * (t₂ - t₁) ^ (α : ℝ) := by
            have hu2_le : t₂ - S k ≤ Llen α g k := by rw [hS_succ] at hk_hi; linarith
            have h3 := gammaLayer_holder hα0 hαhalf g hg k (hLlen_le_L k)
              0 (t₂ - S k) le_rfl (by linarith) hu2_le
            rw [sub_zero] at h3
            have hSk_ge_t1 : t₁ ≤ S k := hj_hi.le.trans (hS_mono (by omega : j + 1 ≤ k))
            exact h3.trans (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (by linarith) (by linarith) hα_pos.le) hC₁_nn)
          rw [hdiff]
          calc
            ‖(gammaLayer hα0 hαhalf g hg j (Llen α g j) -
                gammaLayer hα0 hαhalf g hg j (t₁ - S j)) +
              (∑ r ∈ Finset.Ico (j + 1) k, hLayerH g hg r) +
              (gammaLayer hα0 hαhalf g hg k (t₂ - S k) -
                gammaLayer hα0 hαhalf g hg k 0)‖
                ≤ ‖(gammaLayer hα0 hαhalf g hg j (Llen α g j) -
                      gammaLayer hα0 hαhalf g hg j (t₁ - S j)) +
                    (∑ r ∈ Finset.Ico (j + 1) k, hLayerH g hg r)‖ +
                  ‖gammaLayer hα0 hαhalf g hg k (t₂ - S k) -
                    gammaLayer hα0 hαhalf g hg k 0‖ := norm_add_le _ _
            _ ≤ ‖gammaLayer hα0 hαhalf g hg j (Llen α g j) -
                    gammaLayer hα0 hαhalf g hg j (t₁ - S j)‖ +
                  ‖∑ r ∈ Finset.Ico (j + 1) k, hLayerH g hg r‖ +
                  ‖gammaLayer hα0 hαhalf g hg k (t₂ - S k) -
                    gammaLayer hα0 hαhalf g hg k 0‖ := add_le_add (norm_add_le _ _) le_rfl
            _ ≤ C₁ * (t₂ - t₁) ^ (α : ℝ) + C₂ * (t₂ - t₁) ^ (α : ℝ) +
                  C₁ * (t₂ - t₁) ^ (α : ℝ) := add_le_add (add_le_add hterm1 hterm2) hterm3
            _ = C₀ * (t₂ - t₁) ^ (α : ℝ) := by dsimp only [C₀]; ring
      · have ht₂_eq : t₂ = L := le_antisymm ht₂ (not_lt.mp ht₂_lt)
        subst ht₂_eq
        have hdiff : Γ L - Γ t₁ =
            (g - ∑ r ∈ Finset.range (j + 1), hLayerH g hg r) +
            (gammaLayer hα0 hαhalf g hg j (Llen α g j) -
              gammaLayer hα0 hαhalf g hg j (t₁ - S j)) := by
          rw [hΓ_end, hΓt₁, Finset.sum_range_succ, gammaLayer_end hα0 hαhalf g hg j]
          abel
        have hterm1 : ‖g - ∑ r ∈ Finset.range (j + 1), hLayerH g hg r‖ ≤
            C₂ * (L - t₁) ^ (α : ℝ) := by
          have htail := hTail_norm_sq_le g hg hH_summ (j + 1)
          have htsum_L : ∑' r : ℕ, ‖hLayerH g hg (j + 1 + r)‖ ^ 2 ≤ L - t₁ := by
            have hts1 : Summable (fun r => ‖hLayerH g hg (j + 1 + r)‖ ^ 2) := by
              simpa [add_comm] using (summable_nat_add_iff (j + 1)).mpr hH_summ
            have hts2 : Summable (fun r => Llen α g (j + 1 + r)) := by
              simpa [add_comm] using (summable_nat_add_iff (j + 1)).mpr hL_summ
            have hadd_eq : S (j + 1) + ∑' r : ℕ, Llen α g (j + 1 + r) = L := by
              have h := hL_summ.sum_add_tsum_nat_add (j + 1)
              simpa [S, add_comm] using h
            calc
              ∑' r : ℕ, ‖hLayerH g hg (j + 1 + r)‖ ^ 2
                  ≤ ∑' r : ℕ, Llen α g (j + 1 + r) :=
                    hts1.tsum_le_tsum (fun r => hLayerH_norm_sq_le_Llen hα0 hαhalf g hg _) hts2
              _ = L - S (j + 1) := by linarith
              _ ≤ L - t₁ := by linarith
          have hsq : ‖g - ∑ r ∈ Finset.range (j + 1), hLayerH g hg r‖ ^ 2 ≤
              (C₂ * (L - t₁) ^ (α : ℝ)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by positivity),
              ← Real.rpow_natCast ((L - t₁) ^ (α : ℝ)) 2, ← Real.rpow_mul hdt_nn,
              show (α : ℝ) * ((2 : ℕ) : ℝ) = 2 * (α : ℝ) by push_cast; ring]
            linarith
          nlinarith [norm_nonneg (g - ∑ r ∈ Finset.range (j + 1), hLayerH g hg r),
            mul_nonneg hC₂_nn (Real.rpow_nonneg hdt_nn (α : ℝ))]
        have hterm2 : ‖gammaLayer hα0 hαhalf g hg j (Llen α g j) -
            gammaLayer hα0 hαhalf g hg j (t₁ - S j)‖ ≤ C₁ * (L - t₁) ^ (α : ℝ) := by
          have hu1_le : t₁ - S j ≤ Llen α g j := by rw [hS_succ] at hj_hi; linarith
          have h2 := gammaLayer_holder hα0 hαhalf g hg j (hLlen_le_L j)
            (t₁ - S j) (Llen α g j) (by linarith) hu1_le le_rfl
          have hsub_eq : Llen α g j - (t₁ - S j) = S (j + 1) - t₁ := by rw [hS_succ]; ring
          rw [hsub_eq] at h2
          exact h2.trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by linarith) (by linarith [hS_le_L (j + 1)]) hα_pos.le) hC₁_nn)
        rw [hdiff]
        calc
          ‖(g - ∑ r ∈ Finset.range (j + 1), hLayerH g hg r) +
            (gammaLayer hα0 hαhalf g hg j (Llen α g j) -
              gammaLayer hα0 hαhalf g hg j (t₁ - S j))‖
              ≤ ‖g - ∑ r ∈ Finset.range (j + 1), hLayerH g hg r‖ +
                ‖gammaLayer hα0 hαhalf g hg j (Llen α g j) -
                  gammaLayer hα0 hαhalf g hg j (t₁ - S j)‖ := norm_add_le _ _
          _ ≤ C₂ * (L - t₁) ^ (α : ℝ) + C₁ * (L - t₁) ^ (α : ℝ) := add_le_add hterm1 hterm2
          _ ≤ C₀ * (L - t₁) ^ (α : ℝ) := by
                have : 0 ≤ C₁ * (L - t₁) ^ (α : ℝ) :=
                  mul_nonneg hC₁_nn (Real.rpow_nonneg hdt_nn _)
                dsimp only [C₀]; linarith

lemma holderConnectedH_Gsub {α : NNReal} (hα0 : 0 < α) (hαhalf : α < 1 / 2) :
    holderConnectedH α (Gsub (sVal α)) := by
  have hα_pos : (0 : ℝ) < (α : ℝ) := NNReal.coe_pos.mpr hα0
  intro a ha b hb
  let g : Hsub (sVal α) := b - a
  have hg : g ∈ Gsub (sVal α) := (Gsub (sVal α)).sub_mem hb ha
  by_cases hg0 : g = 0
  · have hab_eq : a = b := (sub_eq_zero.mp hg0).symm
    subst hab_eq
    refine ⟨Path.refl a, fun _ => ha, 0, ?_⟩
    intro t₁ t₂
    change edist a a ≤ _
    simp
  · obtain ⟨L, C₀, Γ, hL_pos, hC₀_nn, hΓ_zero, hΓ_end, hΓ_mem, hΓ_holder⟩ :=
      exists_holder_curve_from_zero hα0 hαhalf g hg hg0
    let pFun : unitInterval → Hsub (sVal α) := fun u => a + Γ (L * (u : ℝ))
    let Cfin : NNReal := ⟨C₀ * L ^ (α : ℝ), mul_nonneg hC₀_nn (Real.rpow_nonneg hL_pos.le _)⟩
    have hp_holder : HolderWith Cfin α pFun := by
      intro u₁ u₂
      rw [edist_dist, edist_dist, ENNReal.coe_nnreal_eq,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα_pos.le,
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg Cfin)]
      apply ENNReal.ofReal_le_ofReal
      have hdist_eq : dist (pFun u₁) (pFun u₂) = ‖Γ (L * (u₁ : ℝ)) - Γ (L * (u₂ : ℝ))‖ := by
        rw [dist_eq_norm]; dsimp only [pFun]; abel_nf
      have hdu_eq : dist u₁ u₂ = |(u₁ : ℝ) - (u₂ : ℝ)| := by
        rw [Subtype.dist_eq, Real.dist_eq]
      rw [hdist_eq, hdu_eq]
      rcases le_total (u₁ : ℝ) (u₂ : ℝ) with hle | hle
      · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
        have h1 := hΓ_holder (L * (u₁ : ℝ)) (L * (u₂ : ℝ))
          (mul_nonneg hL_pos.le u₁.2.1)
          (mul_le_mul_of_nonneg_left hle hL_pos.le)
          (by nlinarith [u₂.2.2])
        rw [← mul_sub, Real.mul_rpow hL_pos.le (sub_nonneg.mpr hle), ← mul_assoc] at h1
        exact h1
      · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        have h1 := hΓ_holder (L * (u₂ : ℝ)) (L * (u₁ : ℝ))
          (mul_nonneg hL_pos.le u₂.2.1)
          (mul_le_mul_of_nonneg_left hle hL_pos.le)
          (by nlinarith [u₁.2.2])
        rw [← mul_sub, Real.mul_rpow hL_pos.le (sub_nonneg.mpr hle), ← mul_assoc] at h1
        exact h1
    let p : Path a b :=
      { toFun := pFun
        continuous_toFun := hp_holder.continuous hα0
        source' := by dsimp [pFun]; simp [hΓ_zero]
        target' := by dsimp [pFun]; simp [hΓ_end, g] }
    refine ⟨p, fun u => ?_, Cfin, hp_holder⟩
    exact (Gsub (sVal α)).add_mem ha (hΓ_mem (L * (u : ℝ))
      ⟨mul_nonneg hL_pos.le u.2.1, by nlinarith [u.2.2]⟩)

/-! Section 7: Main theorem -/

theorem main_proof :
    ∀ α : NNReal, 0 < α → α < 1 / 2 →
      ∃ G : AddSubgroup OMA.S_mo_45322.Hilbert,
        IsClosed (G : Set OMA.S_mo_45322.Hilbert) ∧
        OMA.S_mo_45322.holderConnected α G ∧
        ∀ β : NNReal, α < β → ¬ OMA.S_mo_45322.holderConnected β G := by
  intro α hα0 hαhalf
  have hα_pos : (0 : ℝ) < (α : ℝ) := NNReal.coe_pos.mpr hα0
  have hα_lt : (α : ℝ) < 1 / 2 := by exact_mod_cast hαhalf
  have hs0 : 0 < sVal α := by dsimp [sVal]; linarith
  have hs_half : sVal α < 1 / 2 := by dsimp [sVal]; linarith
  obtain ⟨e⟩ := exists_equiv_hilbert hs0 hs_half
  refine ⟨(Gsub (sVal α)).map e.toAddEquiv.toAddMonoidHom, ?_, ?_, ?_⟩
  · have heq : (((Gsub (sVal α)).map e.toAddEquiv.toAddMonoidHom :
        AddSubgroup OMA.S_mo_45322.Hilbert) : Set OMA.S_mo_45322.Hilbert) =
        e '' (Gsub (sVal α) : Set (Hsub (sVal α))) := rfl
    rw [heq]
    exact e.toHomeomorph.isClosed_image.mpr (isClosed_Gsub (sVal α))
  · rw [transfer_holderConnected e α]
    exact holderConnectedH_Gsub hα0 hαhalf
  · intro β hαβ
    rw [transfer_holderConnected e β]
    exact not_holderConnectedH_of_gt hα0 hαhalf hαβ

end Mo45322

theorem OMA.solution : type_of% @OMA.S_mo_45322.main := Mo45322.main_proof
