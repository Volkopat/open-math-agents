import OMAStatements.S_mo_182409

/-!
Adapted from @connoranderson’s earlier complete proof, pin
 ef8173d60323165be133d7d8be852e4e8bbd813a, linked by statement #27443.
The direct finite-coordinate product-integral bridge follows the corresponding
argument in @Solfanbtc’s merged proof #31141. All transform construction and
zero-free-strip arguments are retained from Connor’s proof. The dyadic-weight
normalization uses the standard geometric-series identity.
Source: Chee, MathOverflow 182409 (CC BY-SA 3.0).
-/

namespace OMA.S_mo_182409
open MeasureTheory Set

private lemma exp_bound (z : ℂ) {x R : ℝ} (hx : |x| ≤ 1) (hz : |z.re| ≤ R) :
    ‖Complex.exp (z*x)‖ ≤ Real.exp R := by
  rw [Complex.norm_exp, Real.exp_le_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero,sub_zero]
  calc z.re*x ≤ |z.re*x| := le_abs_self _
       _ = |z.re| * |x| := abs_mul _ _
       _ ≤ |z.re| * 1 := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
       _ ≤ R := by simpa using hz

private lemma integrable_transform (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hh : ∀ᵐ x ∂μ, |x|≤1) (z : ℂ) : Integrable (fun x : ℝ => Complex.exp (z*x)) μ := by
  apply Integrable.of_bound (C := Real.exp |z.re|) (by fun_prop)
  filter_upwards [hh] with x hx
  exact exp_bound z hx le_rfl

private lemma entire (μ : Measure ℝ) [IsProbabilityMeasure μ] (hh : ∀ᵐ x ∂μ, |x|≤1) :
    Differentiable ℂ (transform μ) ∧ ∀ z : ℂ, ‖transform μ z‖ ≤ Real.exp |z.re| := by
  have hall : ProbabilityTheory.integrableExpSet id μ = univ := by
    ext t
    simp only [mem_univ, iff_true]
    change Integrable (fun x : ℝ => Real.exp (t*x)) μ
    simpa [Complex.norm_exp, Complex.mul_re] using (integrable_transform μ hh (t:ℂ)).norm
  constructor
  · have h := ProbabilityTheory.differentiableOn_complexMGF (X := id) (μ := μ)
    change Differentiable ℂ (ProbabilityTheory.complexMGF id μ)
    apply differentiableOn_univ.mp
    simpa [hall] using h
  · intro z
    have hb : ∀ᵐ (x : ℝ) ∂μ, ‖Complex.exp (z*(x:ℂ))‖ ≤ Real.exp |z.re| := hh.mono fun x hx => exp_bound z hx le_rfl
    simpa [transform] using norm_integral_le_of_norm_le_const hb

private lemma dominates (μ : Measure ℝ) [IsProbabilityMeasure μ] (hh : ∀ᵐ x ∂μ, |x|≤1)
    (R : ℝ) (hd : Real.exp R*(1-μ.real {0})<μ.real {0}) (z : ℂ) (hz : |z.re|≤R) :
    transform μ z ≠ 0 := by
  let g (x : ℝ) := Complex.exp (z*x)
  have hsum := integral_add_compl (μ := μ) (s := ({0}:Set ℝ)) (by measurability) (integrable_transform μ hh z)
  have hb : ∀ᵐ x ∂μ.restrict ({0}:Set ℝ)ᶜ, ‖g x‖ ≤ Real.exp R := by
    filter_upwards [ae_restrict_of_ae hh] with x hx
    exact exp_bound z hx hz
  have hnorm := norm_setIntegral_le_of_norm_le_const_ae (measure_lt_top μ ({0}:Set ℝ)ᶜ) hb
  intro h
  change (∫ x, g x ∂μ) = 0 at h
  change (∫ x in ({0}:Set ℝ), g x ∂μ) + (∫ x in ({0}:Set ℝ)ᶜ, g x ∂μ) = ∫ x, g x ∂μ at hsum
  rw [h,integral_singleton] at hsum
  have hr : ∫ x in ({0}:Set ℝ)ᶜ, g x ∂μ = -(μ.real {0}:ℂ) := by
    simpa [g, Complex.real_smul] using (eq_neg_of_add_eq_zero_right hsum)
  rw [hr,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg,
    measureReal_compl (by measurability)] at hnorm
  exact not_le_of_gt hd (by simpa using hnorm)

end OMA.S_mo_182409

namespace OMA.S_mo_182409
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
private abbrev Ω := ℕ → Bool
private noncomputable def w (i : ℕ) : ℝ := (1/2:ℝ)^i/2
private noncomputable def jump (i : ℕ) (b : Bool) : ℝ := if b then w i else 0
private noncomputable def total (ω : Ω) : ℝ := ∑' i, jump i (ω i)
private lemma w_pos (i : ℕ) : 0 < w i := by unfold w; positivity
private lemma jump_range (i : ℕ) (b : Bool) : 0 ≤ jump i b ∧ jump i b ≤ w i := by
  cases b <;> simp [jump,(w_pos i).le]
private lemma jump_m (i : ℕ) : Measurable (fun ω : Ω => jump i (ω i)) :=
  (measurable_of_countable (jump i)).comp (measurable_pi_apply i)

private lemma w_sum : HasSum w 1 := by
  change HasSum (fun i : ℕ => (1/2:ℝ)^i/2) 1
  simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0)] using hasSum_geometric_two.div_const (2 : ℝ)
private lemma jump_sum (ω : Ω) : Summable (fun i => jump i (ω i)) :=
  w_sum.summable.of_nonneg_of_le (fun i => (jump_range i _).1) (fun i => (jump_range i _).2)
private lemma total_m : Measurable total := Measurable.tsum jump_m
private lemma total_range (ω : Ω) : total ω ∈ Icc (0:ℝ) 1 :=
  ⟨tsum_nonneg fun i => (jump_range i _).1,
    ((jump_sum ω).tsum_le_tsum (fun i => (jump_range i _).2) w_sum.summable).trans_eq w_sum.tsum_eq⟩

private noncomputable def prob (r : ℕ → ℝ) (i : ℕ) : unitInterval :=
  ⟨1/(1+Real.exp (r i * w i)), by
    constructor
    · positivity
    · have h := Real.exp_pos (r i*w i)
      exact (div_le_one (by positivity)).mpr (by linarith)⟩

private noncomputable def bitLaw (r : ℕ → ℝ) (i : ℕ) : Measure Bool :=
  bernoulliMeasure true false (prob r i)
private instance (r : ℕ → ℝ) (i : ℕ) : IsProbabilityMeasure (bitLaw r i) :=
  inferInstanceAs (IsProbabilityMeasure (bernoulliMeasure true false (prob r i)))

private noncomputable def point (r : ℕ → ℝ) (i : ℕ) : ℂ := ⟨r i,Real.pi/w i⟩

private lemma cancellation (r : ℕ → ℝ) (i : ℕ) :
    ∫ b, Complex.exp (point r i * (jump i b:ℂ)) ∂bitLaw r i = 0 := by
  have hz : point r i * (w i:ℂ) = (r i*w i:ℝ) + Real.pi*Complex.I := by
    apply Complex.ext <;> simp [point,Complex.mul_re,Complex.mul_im,(w_pos i).ne']
  rw [bitLaw, integral_bernoulliMeasure]
  simp only [jump, ↓reduceIte, Bool.false_eq_true, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, hz, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg, mul_one,
    ← Complex.ofReal_exp, ← Complex.ofReal_neg, Complex.real_smul, ← Complex.ofReal_mul]
  rw [← Complex.ofReal_add, ← Complex.ofReal_zero]
  congr 1
  dsimp [prob]
  field_simp
  ring

end OMA.S_mo_182409

namespace OMA.S_mo_182409
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

private lemma allzeros (r : ℕ → ℝ) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ (∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) ∧
      ∀ i, transform μ (point r i) = 0 := by
  let P := Measure.infinitePi (bitLaw r)
  have : IsProbabilityMeasure P := inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (bitLaw r)))
  let μ := P.map total
  refine ⟨μ, Measure.isProbabilityMeasure_map total_m.aemeasurable, ?_, ?_⟩
  · exact (ae_map_iff total_m.aemeasurable measurableSet_Icc).mpr (.of_forall total_range)
  intro i
  let z := point r i
  let partialSum (n : ℕ) (ω : Ω) : ℝ := ∑ j ∈ Finset.range n, jump j (ω j)
  let integ (n : ℕ) (ω : Ω) : ℂ := Complex.exp (z * (partialSum n ω:ℂ))
  have hpartialSum (n : ℕ) : Measurable (partialSum n) :=
    Finset.measurable_fun_sum _ fun j _ => jump_m j
  have hbound (n : ℕ) (ω : Ω) : |partialSum n ω| ≤ 1 := by
    rw [abs_of_nonneg (Finset.sum_nonneg fun j _ => (jump_range j _).1)]
    exact ((jump_sum ω).sum_le_tsum _ (fun j _ => (jump_range j _).1)).trans (total_range ω).2
  have hconv : Tendsto (fun n => ∫ ω, integ n ω ∂P) atTop (𝓝 (transform μ z)) := by
    rw [transform,show μ=P.map total from rfl,integral_map total_m.aemeasurable (by fun_prop)]
    apply tendsto_integral_of_dominated_convergence (fun _ => Real.exp |z.re|)
    · intro n
      exact (Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp (hpartialSum n)))).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact .of_forall fun ω => exp_bound z (hbound n ω) le_rfl
    · apply Filter.Eventually.of_forall
      intro ω
      have ht : Tendsto (fun n => partialSum n ω) atTop (𝓝 (total ω)) := (jump_sum ω).hasSum.tendsto_sum_nat
      exact (Complex.continuous_exp.continuousAt.tendsto.comp
        (tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp ht)))
  apply tendsto_nhds_unique hconv
  apply Filter.EventuallyEq.tendsto
  filter_upwards [eventually_gt_atTop i] with n hn
  let s := Finset.range n
  let v (j : s) (b : Bool) := Complex.exp (z * (jump j.val b:ℂ))
  have fac (ω : Ω) : integ n ω = ∏ j : s, v j (s.restrict ω j) := by
    dsimp only [integ, partialSum]
    push_cast
    rw [Finset.mul_sum, Complex.exp_sum]
    rw [← Finset.prod_coe_sort s (fun j => Complex.exp (z * (jump j (ω j):ℂ)))]
    rfl
  simp_rw [fac]
  have hm : AEStronglyMeasurable (fun y : (j : s) → Bool => ∏ j : s, v j (y j))
      (Measure.pi fun j : s => bitLaw r j.val) :=
    (measurable_of_countable _).aestronglyMeasurable
  rw [show P = Measure.infinitePi (bitLaw r) from rfl,
    integral_restrict_infinitePi (μ := bitLaw r) (s := s) hm,
    integral_fintype_prod_eq_prod v]
  exact Finset.prod_eq_zero (i := ⟨i, Finset.mem_range.mpr hn⟩)
    (Finset.mem_univ _) (cancellation r i)

end OMA.S_mo_182409

theorem OMA.solution : type_of% @OMA.S_mo_182409.main := by
  constructor
  · let q (n : ℕ) : ℚ := (Encodable.decode n).getD 0
    have hq : Function.Surjective q := Encodable.surjective_decode_getD ℚ 0
    let r (n : ℕ) : ℝ := q n
    obtain ⟨μ,hμ,hh,h⟩ := OMA.S_mo_182409.allzeros r
    have := hμ
    have hr (s : ℚ) : ∃ z : ℂ, z.re=s ∧ OMA.S_mo_182409.transform μ z = 0 := by
      obtain ⟨n,hn⟩ := hq s
      exact ⟨OMA.S_mo_182409.point r n,congrArg (fun x : ℚ => (x:ℝ)) hn,h n⟩
    have hb : ∀ᵐ x ∂μ, |x|≤1 := hh.mono fun x hx => (abs_of_nonneg hx.1).le.trans hx.2
    obtain ⟨hent,hbd⟩ := OMA.S_mo_182409.entire μ hb
    refine ⟨μ,hμ,hh,OMA.S_mo_182409.integrable_transform μ hb,hent,hbd,hr,?_⟩
    · intro a b hab
      obtain ⟨s,has,hsb⟩ := exists_rat_btwn hab
      obtain ⟨z,hz,hv⟩ := hr s
      exact ⟨z,hz.symm ▸ has,hz.symm ▸ hsb,hv⟩
  · intro μ _ hh R _ hd z hz
    exact OMA.S_mo_182409.dominates μ hh R hd z hz
