import OMAStatements.S_mo_422632
namespace OMA.S_mo_422632
open MeasureTheory Filter
private lemma positive {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (X : Ω → E) (z : E) (f : E → WithTop ℝ) (g : Ω → ℝ)
    (hf : EpigraphCone f) (hz : PettisValue μ X z) (hg : Integrable g μ)
    (hdom : ∀ᵐ ω ∂μ, f (X ω) ≤ (g ω : WithTop ℝ)) :
    f z ≤ ((∫ ω, g ω ∂μ : ℝ) : WithTop ℝ) := by
  obtain ⟨C,hC⟩ := hf
  apply (hC _ _).mp
  by_contra h
  obtain ⟨L,hL,hneg⟩ := C.hyperplane_separation_point h
  let A := L.comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hsplit (x : E) (t : ℝ) : L (x,t) = A x + t*L (0,1) := by
    have he : (x,t) = ((x,0) : E×ℝ) + t • (0,1) := by ext <;> simp
    rw [he,map_add,map_smul]
    rfl
  obtain ⟨hAi,hAv⟩ := hz A
  have hn : 0 ≤ ∫ ω, L (X ω,g ω) ∂μ := integral_nonneg_of_ae
    (hdom.mono fun ω hω => hL _ ((hC _ _).mpr hω))
  rw [hsplit] at hneg
  have hcomp : (fun ω => L (X ω,g ω)) = (fun ω => A (X ω) + g ω * L (0,1)) :=
    funext fun ω => hsplit _ _
  rw [hcomp] at hn
  rw [integral_add hAi (hg.mul_const _),integral_mul_const,←hAv] at hn
  linarith

private lemma bochner {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (μ : Measure Ω) (X : Ω→E) (hX : Integrable X μ) :
    PettisValue μ X (∫ ω, X ω ∂μ) :=
  fun L => ⟨L.integrable_comp hX,(L.integral_comp_comm hX).symm⟩
end OMA.S_mo_422632
namespace OMA.S_mo_422632
open MeasureTheory Filter
open scoped ENNReal
private noncomputable def vector (n : ℕ) : H :=
  if n=0 then 0 else lp.single 2 n ((1/2:ℝ)^n)

private def finiteTail : Submodule ℝ H where
  carrier := {x | ∀ᶠ j in atTop, x j = 0}
  zero_mem' := .of_forall fun _ => rfl
  add_mem' := by
    intro a b ha hb
    filter_upwards [ha,hb] with j hj hk
    change a j+b j=0
    rw [hj,hk,add_zero]
  smul_mem' := by
    intro c a ha
    filter_upwards [ha] with j hj
    change c*a j=0
    rw [hj,mul_zero]

private lemma vector_mem (n : ℕ) : vector n ∈ finiteTail := by
  filter_upwards [eventually_gt_atTop n] with j hj
  by_cases hn : n=0
  · simp [vector,hn]
  · rw [vector,if_neg hn]; exact lp.single_apply_ne _ _ _ hj.ne'

private lemma negative : ∃ (μ : Measure ℕ) (X : ℕ → H) (F : H →ₗ[ℝ] ℝ),
    ¬SigmaFinite μ ∧ Integrable X μ ∧ (∀ n, F (X n)=0) ∧
    F (∫ n, X n ∂μ)=1 ∧ (∫ n, F (X n) ∂μ) < F (∫ n, X n ∂μ) := by
  classical
  let ν : Measure ℕ := (∞ : ℝ≥0∞) • Measure.dirac 0
  let μ := (Measure.count : Measure ℕ)+ν
  have hν : vector =ᵐ[ν] 0 := by
    change ∀ᵐ n ∂((∞ : ℝ≥0∞) • Measure.dirac (0:ℕ)), vector n=0
    apply Measure.ae_smul_measure
    rw [ae_dirac_iff .of_discrete]
    simp [vector]
  have hνi : Integrable vector ν := (integrable_congr hν).mpr (integrable_zero _ _ _)
  have hci : Integrable vector Measure.count := by
    apply integrable_count_iff.mpr
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (summable_geometric_of_lt_one
      (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num))
    intro n
    by_cases hn : n=0
    · simp [vector,hn]
    · rw [vector,if_neg hn,lp.norm_single (by norm_num : (0:ℝ≥0∞)<2),Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
  have hx := hci.add_measure hνi
  have hev (j : ℕ) (hj : j≠0) : (∫ n, vector n ∂μ) j=(1/2:ℝ)^j := by
    rw [show μ=Measure.count+ν from rfl,integral_add_measure hci hνi,integral_congr_ae hν]
    simp only [Pi.zero_apply,integral_zero,add_zero]
    let e := lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 j
    change e (∫ n, vector n ∂Measure.count) = _
    rw [←e.integral_comp_comm hci, integral_countable (e.integrable_comp hci)]
    rw [tsum_eq_single j]
    · change Measure.count.real {j} • (vector j) j = _
      simp [MeasureTheory.measureReal_def,vector,hj]
    · intro n hn
      change Measure.count.real {n} • (vector n) j = 0
      by_cases h0 : n=0
      · simp [vector,h0]
      · rw [vector,if_neg h0,lp.single_apply_ne _ _ _ (Ne.symm hn),smul_zero]
  have hnot : finiteTail.mkQ (∫ n, vector n ∂μ) ≠ 0 := by
    rw [Submodule.mkQ_apply,ne_eq, Submodule.Quotient.mk_eq_zero]
    intro hm
    have he : ∀ᶠ j : ℕ in atTop, (∫ n,vector n ∂μ) j=0 := hm
    obtain ⟨j,hj,hpos⟩ := (he.and (eventually_gt_atTop 0)).exists
    rw [hev j hpos.ne'] at hj
    exact (ne_of_gt (by positivity : (0:ℝ)<(1/2:ℝ)^j)) hj
  obtain ⟨L,hL⟩ := Module.Projective.exists_dual_eq_one ℝ hnot
  let F := L.comp finiteTail.mkQ
  have hf (n : ℕ) : F (vector n)=0 := by
    change L (Submodule.Quotient.mk (vector n))=0
    rw [(Submodule.Quotient.mk_eq_zero _).mpr (vector_mem n),map_zero]
  refine ⟨μ,vector,F,?_,hx,hf,hL,?_⟩
  · intro hs
    let _ := hs
    have he : μ {0}=∞ := by simp [μ,ν]
    exact (measure_singleton_lt_top (μ:=μ) (a:=0)).ne he
  · simp only [hf,integral_zero]
    change 0 < L (finiteTail.mkQ _)
    rw [hL]
    norm_num
end OMA.S_mo_422632
theorem OMA.solution : type_of% @OMA.S_mo_422632.main := ⟨fun _ _ _ _ _ => OMA.S_mo_422632.positive, fun _ _ _ _ _ _ => OMA.S_mo_422632.bochner, OMA.S_mo_422632.negative⟩
