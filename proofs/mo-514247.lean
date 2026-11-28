import OMAStatements.S_mo_514247

namespace OMA.S_mo_514247
open ProbabilityTheory MeasureTheory Set Finset
private noncomputable abbrev γ := gaussianReal 0 1
private instance law_prob (n : ℕ) : IsProbabilityMeasure (law n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin (n+1) => γ)))

private lemma total_le {n} {C : ℝ} {Y : Coeff n} (hY : bounded C Y) (x : Sample n) :
    |total Y x| ≤ C*radius x := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold radius
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro i _
  rw [abs_mul,mul_comm C]
  exact mul_le_mul_of_nonneg_left ((hY i).2 x) (abs_nonneg _)

private lemma tail_le {n} {C : ℝ} (hC : 0≤C) {Y : Coeff n} (hY : bounded C Y) (t : ℝ) :
    tail (total Y) t ≤ tail (fun x : Sample n => C*radius x) t := by
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  have hr : 0≤radius x := sum_nonneg (fun _ _ => abs_nonneg _)
  exact (show t≤|total Y x| from hx).trans ((total_le hY x).trans_eq (abs_of_nonneg (mul_nonneg hC hr)).symm)

private lemma exp_moment (s : ℝ) : Integrable (fun x : ℝ => Real.exp (s*|x|)) γ ∧
    (∫ x : ℝ,Real.exp (s*|x|) ∂γ) ≤ 2*Real.exp (s^2/2) := by
  let f (x : ℝ) := Real.exp (s*x) + Real.exp (-s*x)
  have hfi : Integrable f γ := (integrable_exp_mul_gaussianReal s).add (integrable_exp_mul_gaussianReal (-s))
  have hle (x : ℝ) : Real.exp (s*|x|) ≤ f x := by
    rcases le_total 0 x with h|h
    · rw [abs_of_nonneg h]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos h,mul_neg,←neg_mul]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have hi : Integrable (fun x : ℝ => Real.exp (s*|x|)) γ :=
    hfi.mono' (by fun_prop) (.of_forall fun x => by
      simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hle x)
  refine ⟨hi,(integral_mono hi hfi hle).trans_eq ?_⟩
  have hm (a : ℝ) : (∫ x : ℝ,Real.exp (a*x) ∂γ) = Real.exp (a^2/2) := by
    simpa only [mgf,zero_mul,NNReal.coe_one,one_mul,zero_add] using congrFun (mgf_fun_id_gaussianReal (μ:=0) (v:=1)) a
  rw [show f=(fun x => Real.exp (s*x)+Real.exp (-s*x)) from rfl,
    integral_add (integrable_exp_mul_gaussianReal s) (integrable_exp_mul_gaussianReal (-s)),hm,hm]
  simp [two_mul]

private lemma exponential_tail {n} {C t : ℝ} (hC : 0<C) (ht : 0<t) :
    tail (fun x : Sample n => C*radius x) t ≤
    (2:ℝ)^(n+1)*Real.exp (-(t^2)/(2*(n+1:ℝ)*C^2)) := by
  let d : ℝ := n+1
  have hd : 0<d := by dsimp [d];positivity
  let s := t/(d*C)
  have hs : 0<s := div_pos ht (mul_pos hd hC)
  let F (x : Sample n) := ∏ i,Real.exp (s*|x i|)
  have he (x : Sample n) : F x=Real.exp (s*radius x) := by
    simp [F,radius,Finset.mul_sum,Real.exp_sum]
  have hent : Integrable F (law n) := Integrable.fintype_prod_dep (fun _ => (exp_moment s).1)
  have hm : (∫ x,F x ∂law n) ≤ (2*Real.exp (s^2/2))^(n+1) := by
    change (∫ x,∏ i,Real.exp (s*|x i|) ∂Measure.pi (fun _ : Fin (n+1) => γ)) ≤ _
    rw [integral_fintype_prod_eq_prod (fun _ : Fin (n+1) => fun x : ℝ => Real.exp (s*|x|))]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    exact pow_le_pow_left₀ (integral_nonneg (fun _ => (Real.exp_pos _).le)) (exp_moment _).2 _
  let b := Real.exp (s*(t/C))
  have hm' := mul_meas_ge_le_integral_of_nonneg (μ:=law n) (f:=F)
    (.of_forall fun x => (he x).symm ▸ (Real.exp_pos _).le) hent b
  have hset : {x : Sample n | t≤|C*radius x|} = {x | b≤F x} := by
    ext x
    have hr : 0≤radius x := sum_nonneg (fun _ _ => abs_nonneg _)
    change (t≤|C*radius x|) ↔ (Real.exp _ ≤ F x)
    rw [he,abs_of_nonneg (mul_nonneg hC.le hr),Real.exp_le_exp,mul_le_mul_iff_right₀ hs,
      div_le_iff₀ hC,mul_comm C]
  unfold tail
  rw [hset]
  have hb : 0<b := Real.exp_pos _
  apply le_of_mul_le_mul_left (a:=b) _ hb
  refine (hm'.trans hm).trans_eq ?_
  rw [mul_pow,← Real.exp_nat_mul]
  dsimp [b]
  rw [mul_left_comm,←Real.exp_add]
  congr 2
  dsimp [s,d]
  push_cast
  field_simp
  ring
end OMA.S_mo_514247
namespace OMA.S_mo_514247
open ProbabilityTheory MeasureTheory Set Finset Filter
private noncomputable def direction (s : ℝ) : ℝ := if s=0 then 0 else if 0<s then 1 else -1
private lemma meas_dir : Measurable direction := by
  unfold direction
  exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const)
private lemma dir_abs (s : ℝ) : |direction s|≤1 := by unfold direction; split_ifs <;> norm_num
private lemma dir_mul (s : ℝ) : s*direction s=|s| := by
  unfold direction
  split_ifs with h h
  · simp [h]
  · simp [abs_of_pos h]
  · simp [abs_of_nonpos (le_of_not_gt h)]
private lemma dir_neg (s : ℝ) : direction (-s)= -direction s := by
  rcases lt_trichotomy s 0 with hs|rfl|hs
  · simp [direction,hs.ne,hs.not_gt,neg_pos.mpr hs]
  · simp [direction]
  · simp [direction,hs.ne',hs,not_lt.mpr (neg_nonpos.mpr hs.le)]

private noncomputable def witness (n : ℕ) (C : ℝ) : Coeff n := fun i x =>
  C*direction (x 0)*direction (x i)
private lemma witness_value {n C} (x : Sample n) :
    total (witness n C) x = C*direction (x 0)*radius x := by
  simp only [total,witness,radius,Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  rw [← dir_mul]
  ring
private lemma witness_admissible (n : ℕ) (C : ℝ) (hC : 0≤C) :
    bounded C (witness n C) ∧ ∀ i,witness n C i 0=0 := by
  constructor
  · intro i
    refine ⟨(measurable_const.mul (meas_dir.comp (measurable_pi_apply 0))).mul
      (meas_dir.comp (measurable_pi_apply i)),?_⟩
    intro x
    simp only [witness,abs_mul,abs_of_nonneg hC]
    have h := mul_le_mul (dir_abs (x 0)) (dir_abs (x i)) (abs_nonneg _) zero_le_one
    calc C*|direction (x 0)| * |direction (x i)| = C*(|direction (x 0)| * |direction (x i)|) := by ring
         _ ≤ C := by nlinarith [mul_nonneg hC (sub_nonneg.mpr (show |direction (x 0)| * |direction (x i)|≤1 by simpa using h))]
  · intro i; simp [witness,direction]

private lemma integ_radius (n : ℕ) : Integrable (radius (n:=n)) (law n) := by
  apply integrable_finsetSum
  intro i _
  exact (measurePreserving_eval (fun _ : Fin (n+1) => γ) i).integrable_comp_of_integrable
    (IsGaussian.integrable_id (μ:=γ)).abs

private lemma witness_mean (n : ℕ) (C : ℝ) (hC : 0≤C) :
    Integrable (total (witness n C)) (law n) ∧ (∫ x,total (witness n C) x ∂law n)=0 := by
  let f := total (witness n C)
  have hmeas : Measurable f := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_pi_apply i).mul ((witness_admissible n C hC).1 i).1
  have hfi : Integrable f (law n) :=
    ((integ_radius n).const_mul C).mono' hmeas.aestronglyMeasurable
      (.of_forall fun x => by simpa [Real.norm_eq_abs] using total_le (witness_admissible n C hC).1 x)
  have hs : MeasurePreserving (fun x : Sample n => -x) (law n) (law n) :=
    measurePreserving_pi (fun _ => γ) (fun _ => γ) (f:=fun (_ : Fin (n+1)) (r : ℝ) => -r)
      (fun _ => ⟨measurable_neg,by simpa only [neg_zero] using (gaussianReal_map_neg (μ:=0) (v:=1))⟩)
  have odd (x : Sample n) : f (-x) = -f x := by
    simp only [f,witness_value,Pi.neg_apply,dir_neg,mul_neg,neg_mul]
    simp [radius]
  have hh : ∫ x,f (-x) ∂law n = ∫ x,f x ∂law n := by
    rw [← integral_map hs.measurable.aemeasurable hmeas.aestronglyMeasurable,hs.map_eq]
  simp only [odd,integral_neg] at hh
  exact ⟨hfi,by linarith only [hh]⟩

private lemma witness_tail (n : ℕ) (C t : ℝ) :
    tail (total (witness n C)) t = tail (fun x : Sample n => C*radius x) t := by
  have hn : ∀ᵐ x ∂law n, x 0 ≠ 0 := by
    apply ae_iff.mpr
    simp only [not_ne_iff] 
    change Measure.pi (fun _ : Fin (n+1) => γ) ((Function.eval 0) ⁻¹' ({0}:Set ℝ))=0
    exact Measure.pi_eval_preimage_null _ ((gaussianReal_absolutelyContinuous 0 one_ne_zero) (measure_singleton _))
  apply measureReal_congr
  filter_upwards [hn] with x hx
  apply propext
  change (t≤|total (witness n C) x|) ↔ (t≤|C*radius x|)
  rw [witness_value]
  by_cases hp : 0<x 0 <;> simp [direction,hx,hp]
end OMA.S_mo_514247
namespace OMA.S_mo_514247
open ProbabilityTheory MeasureTheory Set Finset Filter
open scoped NNReal
private noncomputable def above (x : ℝ) : ℝ := (Ioi (1:ℝ)).indicator (fun _ => (1:ℝ)) x
private noncomputable def tailCount {n} (x : Sample n) := ∑ i,above (x i)
private lemma one_tail_pos : 0<γ.real (Ioi 1) := by
  apply ENNReal.toReal_pos _ (measure_ne_top _ _)
  intro hz
  have hh := gaussianReal_absolutelyContinuous' 0 (by norm_num : (1:ℝ≥0)≠0) hz
  simp at hh
private lemma meas_above : Measurable above :=
  measurable_const.indicator measurableSet_Ioi
private lemma above_bounds (t : ℝ) : 0≤above t ∧ above t≤1 ∧ above t≤|t| := by
  by_cases ht : 1<t
  · simp [above,ht,abs_of_pos (by linarith : 0<t),le_of_lt ht]
  · simp [above,ht,abs_nonneg]
private lemma count_mean (n : ℕ) : Integrable (tailCount (n:=n)) (law n) ∧
    (∫ x : Sample n,tailCount x ∂law n)=(n+1:ℝ)*γ.real (Ioi 1) := by
  have hi : Integrable above γ := (integrable_const (1:ℝ)).indicator measurableSet_Ioi
  have hc (i : Fin (n+1)) : Integrable (fun x : Sample n => above (x i)) (law n) :=
    (measurePreserving_eval (fun _ : Fin (n+1) => γ) i).integrable_comp_of_integrable hi
  refine ⟨integrable_finsetSum _ (fun i _ => hc i),?_⟩
  have he (i : Fin (n+1)) : (∫ x : Sample n,above (x i) ∂law n)=γ.real (Ioi 1) := by
    have hp : MeasurePreserving (Function.eval i) (law n) γ := measurePreserving_eval _ _
    change (∫ x : Sample n,above (Function.eval i x) ∂law n)=_
    rw [←integral_map hp.measurable.aemeasurable meas_above.aestronglyMeasurable,
      hp.map_eq]
    exact integral_indicator_one measurableSet_Ioi
  simp only [tailCount,integral_finsetSum _ (fun i _ => hc i),he,sum_const,card_univ,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]

private lemma count_tail (n : ℕ) (C : ℝ) (hC : 0<C) :
    γ.real (Ioi 1)/2 ≤ tail (fun x : Sample n => C*radius x) (γ.real (Ioi 1)/2*C*(n+1:ℝ)) := by
  let c := γ.real (Ioi 1)/2
  let d : ℝ := n+1
  have hd : 0<d := by dsimp [d];positivity
  have hc : 0<c := half_pos one_tail_pos
  let E : Set (Sample n) := {x | c*d≤tailCount x}
  have hmeas : Measurable (tailCount (n:=n)) := Finset.measurable_sum _ (fun i _ => meas_above.comp (measurable_pi_apply i))
  have hE : MeasurableSet E := measurableSet_le measurable_const hmeas
  let Z := E.indicator (fun _ => (1:ℝ))
  have hZi : Integrable Z (law n) := (integrable_const _).indicator hE
  have hle (x : Sample n) : tailCount x≤c*d+d*Z x := by
    by_cases hx : x∈E
    · have hf : tailCount x≤d := calc
        _ ≤ ∑ _ : Fin (n+1),(1:ℝ) := sum_le_sum (fun i _ => (above_bounds _).2.1)
        _ = d := by simp [d]
      simpa [Z,hx] using (show tailCount x≤c*d+d by nlinarith [mul_nonneg hc.le hd.le])
    · have hn : ¬c*d≤tailCount x := hx
      simpa [Z,hx] using (le_of_not_ge hn)
  have hh := integral_mono (count_mean n).1 ((integrable_const _).add (hZi.const_mul d)) hle
  have he : (∫ x,Z x ∂law n)=(law n).real E := integral_indicator_one hE
  change (∫ x,tailCount x ∂law n) ≤ ∫ x,c*d+d*Z x ∂law n at hh
  rw [(count_mean n).2,integral_add (integrable_const _) (hZi.const_mul _),integral_const,
    integral_const_mul,he] at hh
  simp only [probReal_univ,one_smul] at hh
  have hp : γ.real (Ioi 1)=2*c := by dsimp [c];ring
  rw [hp] at hh
  change d*(2*c)≤c*d+d*(law n).real E at hh
  have hprob : c≤(law n).real E := by
    by_contra! hn
    nlinarith [mul_pos hd (sub_pos.mpr hn)]
  refine hprob.trans (measureReal_mono ?_ (measure_ne_top _ _))
  intro x hx
  have hr : tailCount x ≤ radius x := sum_le_sum fun i _ => (above_bounds _).2.2
  have hr' := (show c*d≤tailCount x from hx).trans hr
  change c*C*d≤|C*radius x|
  have hrad : 0≤radius x := sum_nonneg fun _ _ => abs_nonneg _
  rw [abs_of_nonneg (mul_nonneg hC.le hrad)]
  nlinarith [mul_le_mul_of_nonneg_left hr' hC.le]
end OMA.S_mo_514247

open OMA.S_mo_514247 in
theorem OMA.solution : type_of% @OMA.S_mo_514247.main := by
  refine ⟨fun n C hC Y hY t ht => ?_,?_⟩
  · have he := OMA.S_mo_514247.tail_le hC.le hY t
    exact ⟨he,he.trans (OMA.S_mo_514247.exponential_tail hC ht)⟩
  · refine ⟨γ.real (Set.Ioi 1)/2,half_pos one_tail_pos,fun n C hC => ?_⟩
    obtain ⟨ha,hz⟩ := witness_admissible n C hC.le
    obtain ⟨hi,hm⟩ := witness_mean n C hC.le
    refine ⟨witness n C,ha,hz,hi,hm,witness_tail n C,?_⟩
    rw [witness_tail]
    exact count_tail n C hC
