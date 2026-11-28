import OMAStatements.S_mo_246858

namespace OMA.S_mo_246858
open Matrix Set MeasureTheory NormedSpace
open scoped Matrix.Norms.Operator
variable {I : Type} [Fintype I] [DecidableEq I]

private lemma flow_left (A : Mat I) (t : ℝ) : HasDerivAt (flow A) (A * flow A t) t :=
  hasDerivAt_exp_smul_const' A t
private lemma flow_right (A : Mat I) (t : ℝ) : HasDerivAt (flow A) (flow A t * A) t :=
  hasDerivAt_exp_smul_const A t
private lemma dIntegral (A B : Mat I) (t : ℝ) :
    HasDerivAt (integrated A B) (flow A t * flow B t) t := by
  have h (A : Mat I) : Continuous (flow A) := continuous_iff_continuousAt.mpr fun t =>
    (flow_left A t).continuousAt
  let : TopologicalSpace.PseudoMetrizableSpace (Mat I) := inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (I → I → ℝ))
  have hc := (h A).mul (h B)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

private lemma flow_cancel (A : Mat I) (t : ℝ) : flow (-A) t * flow A t = 1 := by
  unfold flow
  rw [smul_neg,← Matrix.exp_add_of_commute _ _ (Commute.refl (t • A)).neg_left,neg_add_cancel,
    NormedSpace.exp_zero]
private lemma flow0 (A : Mat I) : flow A 0 = 1 := by simp [flow]
private lemma integral0 (A B : Mat I) : integrated A B 0 = 0 := by simp [integrated]

lemma sylvester (A B : Mat I) (t : ℝ) :
    A * integrated A B t + integrated A B t * B = flow A t * flow B t - 1 := by
  let Z (t : ℝ) := A * integrated A B t + integrated A B t * B - flow A t * flow B t
  have h (s : ℝ) : HasDerivAt Z 0 s := by
    have hi := dIntegral A B s
    have hh := ((hi.const_mul A).add (hi.mul_const B)).sub ((flow_left A s).mul (flow_right B s))
    simp only [Pi.mul_def,Pi.add_def,Pi.sub_def,mul_assoc,sub_self] at hh
    exact hh
  have he := is_const_of_deriv_eq_zero (fun s => (h s).differentiableAt) (fun s => (h s).deriv) t 0
  simp only [Z,integral0,flow0,mul_zero,zero_mul,zero_add,one_mul,zero_sub] at he
  exact sub_eq_iff_eq_add.mp he |>.trans (by abel)

private noncomputable def pack :
    (Mat I × Mat I × Mat I) →ₗ[ℝ] Mat (I ⊕ I) where
  toFun x := fromBlocks x.1 x.2.1 0 x.2.2
  map_add' _ _ := by simp [fromBlocks_add]
  map_smul' _ _ := by simp [fromBlocks_smul]

omit [DecidableEq I] in
private lemma block_deriv {f g h : ℝ → Mat I} {df dg dh : Mat I} {t : ℝ}
    (hf : HasDerivAt f df t) (hg : HasDerivAt g dg t) (hh : HasDerivAt h dh t) :
    HasDerivAt (fun s => fromBlocks (f s) (g s) (0 : Mat I) (h s))
      (fromBlocks df dg 0 dh) t :=
  (pack (I:=I)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hf.prodMk (hg.prodMk hh))

lemma block_formula (A B : Mat I) (t : ℝ) :
    integrated A B t = flow A t * (flow (generator A B) t).toBlocks₁₂ := by
  let K := generator A B
  let G (s : ℝ) := fromBlocks (flow (-A) s) (flow (-A) s * integrated A B s) (0:Mat I) (flow B s)
  have hG (s : ℝ) : HasDerivAt G (K * G s) s := by
    have h1 := flow_left (-A) s
    have h2 := h1.mul (dIntegral A B s)
    have hv : flow (-A) s * (flow A s * flow B s) = flow B s := by
      rw [← mul_assoc, flow_cancel,one_mul]
    have hh := block_deriv h1 h2 (flow_left B s)
    simpa [K,generator,G,Pi.mul_def,fromBlocks_multiply,mul_assoc,hv] using hh
  have h (s : ℝ) : HasDerivAt (fun r => flow (-K) r * G r) 0 s := by
    have hh := (flow_right (-K) s).mul (hG s)
    simp [Pi.mul_def,mul_assoc] at hh
    exact hh
  have he := is_const_of_deriv_eq_zero (fun s => (h s).differentiableAt) (fun s => (h s).deriv) t 0
  change flow (-K) t * G t = flow (-K) 0 * G 0 at he
  have h0 : G 0 = 1 := by simp [G,flow0,integral0,fromBlocks_one]
  rw [h0,flow0,one_mul] at he
  have hc (J : Mat I) : flow J t * flow (-J) t = 1 := by simpa using flow_cancel (-J) t
  have hk : flow K t * flow (-K) t = 1 := by simpa using flow_cancel (-K) t
  have eq := congrArg (flow K t * ·) he
  simp only [← mul_assoc,hk,one_mul,mul_one] at eq
  have h12 := congrArg Matrix.toBlocks₁₂ eq
  change flow (-A) t * integrated A B t = (flow K t).toBlocks₁₂ at h12
  rw [← h12,← mul_assoc,hc,one_mul]
end OMA.S_mo_246858

namespace OMA.S_mo_246858
open Matrix Set MeasureTheory Filter
open scoped Matrix.Norms.Operator Topology
variable {I : Type} [Fintype I] [DecidableEq I]

lemma first_root (A B : Mat I) :
    (∃ ε : ℝ, 0<ε ∧ ∀ t : ℝ, 0<t → t<ε → (integrated A B t).det ≠ 0) ∧
    ((∃ t : ℝ, 0<t ∧ (integrated A B t).det=0) →
      ∃ t : ℝ, IsLeast {s : ℝ | 0<s ∧ (integrated A B s).det=0} t) := by
  have hsl := (dIntegral A B 0).tendsto_slope
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • integrated A B t) (𝓝[≠] (0:ℝ)) (𝓝 (1:Mat I)) := by
    have hg (t : ℝ) : slope (integrated A B) 0 t = t⁻¹ • integrated A B t := by
      rw [slope_def_module,sub_zero,integral0,sub_zero]
    simp only [funext hg,flow0,mul_one] at hsl
    exact hsl
  have hdet : Tendsto (fun t : ℝ => (t⁻¹ • integrated A B t).det) (𝓝[≠] (0:ℝ)) (𝓝 1) := by
    have hD : Continuous (fun M : Mat I => M.det) := continuous_id.matrix_det
    simpa only [Function.comp_def,Matrix.det_one] using hD.continuousAt.tendsto.comp hlim
  have he : ∀ᶠ t in 𝓝[≠] (0:ℝ), (integrated A B t).det ≠ 0 := by
    filter_upwards [hdet.eventually_ne (by norm_num : (1:ℝ)≠0)] with t ht
    intro hz
    exact ht (by simp [hz])
  obtain ⟨ε,hε,hh⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp he)
  have hnear (t : ℝ) (ht : 0<t) (hl : t<ε) : (integrated A B t).det ≠ 0 :=
    hh (by simpa [Real.dist_eq,abs_of_pos ht] using hl) ht.ne'
  refine ⟨⟨ε,hε,hnear⟩,?_⟩
  rintro ⟨t,ht,hz⟩
  have hc : Continuous (integrated A B) := continuous_iff_continuousAt.mpr fun s =>
    (dIntegral A B s).continuousAt
  let S := {s : ℝ | ε ≤ s ∧ (integrated A B s).det = 0}
  have hclosed : IsClosed S := isClosed_Ici.inter (isClosed_eq hc.matrix_det continuous_const)
  have hn : S.Nonempty := ⟨t,le_of_not_gt fun h => hnear t ht h hz,hz⟩
  have hb : BddBelow S := ⟨ε,fun _ hh => hh.1⟩
  have hm := hclosed.isLeast_csInf hn hb
  refine ⟨sInf S,⟨hε.trans_le hm.1.1,hm.1.2⟩,?_⟩
  rintro s ⟨hs,hzs⟩
  exact hm.2 ⟨le_of_not_gt fun h => hnear s hs h hzs,hzs⟩
end OMA.S_mo_246858

namespace OMA.S_mo_246858
open Matrix Set MeasureTheory
open scoped Matrix.Norms.Operator
private lemma nilFlow {I : Type} [Fintype I] [DecidableEq I] (A : Mat I) (h : A^2=0) (t : ℝ) :
    flow A t = 1+t • A := by
  rw [flow,NormedSpace.exp_eq_tsum ℝ]
  change (∑' j : ℕ, (j.factorial:ℝ)⁻¹ • (t • A)^j) = _
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ]
  · intro j hj
    have hs : (t • A)^2 = 0 := by rw [smul_pow,h,smul_zero]
    have hle : 2≤j := Nat.le_of_not_lt (fun hl => hj (Finset.mem_range.mpr hl))
    rw [pow_eq_zero_of_le hle hs,smul_zero]

private lemma nilIntegral {I : Type} [Fintype I] [DecidableEq I] (A B : Mat I)
    (hA : A^2=0) (hB : B^2=0) (T : ℝ) :
    integrated A B T = T • 1 + (T^2/2) • (A+B)+(T^3/3) • (A*B) := by
  have he (t : ℝ) : flow A t*flow B t = (1:Mat I)+t • (A+B)+t^2 • (A*B) := by
    rw [nilFlow A hA,nilFlow B hB]
    simp [add_mul,mul_add,smul_add,smul_smul,pow_two]
    abel
  unfold integrated
  simp_rw [he]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const, intervalIntegral.integral_smul_const _ (A+B),
        intervalIntegral.integral_smul_const _ (A*B),integral_id,integral_pow]
    norm_num
  all_goals apply Continuous.intervalIntegrable; fun_prop

lemma example_data (k : ℝ) : exampleA.trace=0 ∧ (exampleB k).trace=0 ∧
    exampleA^2=0 ∧ (exampleB k)^2=0 ∧ exampleA.charpoly=Polynomial.X^6 ∧
    (exampleB k).charpoly=Polynomial.X^6 := by
  have triv (a b : ℝ) (hab : a*b=0) : (!![0,a;b,0]:Mat (Fin 2))^2=0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two,Matrix.mul_apply,Fin.sum_univ_succ,hab,mul_comm b a]
  have sq (a b : ℝ) (hab : a*b=0) : (fromBlocks (!![0,a;b,0]:Mat (Fin 2)) 0 0 (0:Mat (Fin 4)))^2=0 := by
    have ht := triv a b hab
    simp only [pow_two] at ht ⊢
    simp [fromBlocks_multiply,ht]
  have char (a b : ℝ) (hab : a*b=0) : (fromBlocks (!![0,a;b,0]:Mat (Fin 2)) 0 0 (0:Mat (Fin 4))).charpoly=Polynomial.X^6 := by
    rw [Matrix.charpoly_fromBlocks_zero₂₁,Matrix.charpoly_fin_two]
    simp [Matrix.trace, Matrix.det_fin_two,hab,Fin.sum_univ_succ]; ring
  refine ⟨?_,?_,sq _ _ (by simp),sq _ _ (by simp),char _ _ (by simp),char _ _ (by simp)⟩ <;>
    simp [exampleA,exampleB,Matrix.trace,Fintype.sum_sum_type,Fin.sum_univ_succ,Matrix.diag]

lemma example_noncomm (k : ℝ) (hk : k≠0) : ¬ Commute exampleA (exampleB k) := by
  intro h
  have hh := congrArg (fun M : Mat Six => M (Sum.inl 0) (Sum.inl 0)) h.eq
  simp [exampleA,exampleB,Matrix.mul_apply,Fin.sum_univ_succ] at hh
  exact hk (by linarith)

lemma example_det (k T : ℝ) : (integrated exampleA (exampleB k) T).det=T^6*(1+k*T^2) := by
  rcases example_data k with ⟨_,_,ha,hb,_,_⟩
  rw [nilIntegral _ _ ha hb]
  have hon : (1:Mat Six)=fromBlocks (1:Mat (Fin 2)) 0 0 (1:Mat (Fin 4)) := fromBlocks_one.symm
  rw [hon]
  simp only [exampleA,exampleB,fromBlocks_multiply,fromBlocks_smul,fromBlocks_add,Matrix.zero_mul,
    Matrix.mul_zero,smul_zero,add_zero,Matrix.det_fromBlocks_zero₂₁,Matrix.det_smul,
    Matrix.det_one,Fintype.card_fin,mul_one]
  simp [Matrix.det_fin_two,smul_eq_mul]
  ring
end OMA.S_mo_246858

open OMA.S_mo_246858 Matrix
theorem OMA.solution : type_of% @OMA.S_mo_246858.main := by
  refine ⟨?_,fun _ _ _ => first_root,example_data,example_noncomm,example_det,?_,?_⟩
  · intro I _ _ A B T
    refine ⟨block_formula A B T,?_,sylvester A B T⟩
    rw [block_formula,Matrix.det_mul,mul_eq_zero]
    have hn : (flow A T).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp (T • A))).ne_zero
    simp [hn]
  · refine ⟨⟨by norm_num,by norm_num [example_det]⟩,?_⟩
    rintro t ⟨ht,hz⟩
    rw [example_det,mul_eq_zero] at hz
    rcases hz with h | h
    · exact absurd h (pow_ne_zero _ ht.ne')
    · nlinarith [sq_nonneg (t-1)]
  · intro t ht
    rw [example_det]
    positivity
