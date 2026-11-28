import OMAStatements.S_mo_262608
namespace OMA.S_mo_262608
open MeasureTheory Matrix Finset
open scoped MatrixOrder ComplexOrder
private lemma support_poly {n : ℕ} (A : Mat n) (hA : A.PosSemidef) (t : ℝ) (ht : 0≤ t) (i : Fin n) :
    3*t^2*(A i i).re ≤ ((A*A) i i).re + 2*t^3*((CFC.sqrt A) i i).re := by
  let B := CFC.sqrt A
  let E := B - t • (1 : Mat n)
  have hb : B.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hb2 : B*B=A := CFC.sqrt_mul_sqrt_self _ hA.nonneg
  have he : Eᴴ=E := hb.1.sub (isHermitian_one.smul (IsSelfAdjoint.all t))
  have hp := (hA.add (hb.smul (show 0≤ 2*t by positivity))).mul_mul_conjTranspose_same E
  have eq : E*(A+(2*t) • B)*Eᴴ = A*A - (3*t^2) • A + (2*t^3) • B := by
    rw [he,←hb2]
    dsimp only [E]
    simp only [sub_mul, mul_sub,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
      one_mul,mul_one,mul_assoc]
    module
  rw [eq] at hp
  have hdi := hp.diag_nonneg (i := i)
  change 0 ≤ ((A*A) i i - (3*t^2) • A i i + (2*t^3) • B i i) at hdi
  have hre := (Complex.nonneg_iff.mp hdi).1
  simp only [Complex.add_re,Complex.sub_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] at hre
  linarith

end OMA.S_mo_262608
namespace OMA.S_mo_262608
open MeasureTheory Matrix Finset ComplexConjugate ProbabilityTheory
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
private lemma square_diag {n : ℕ} (A : Mat n) (h : A.IsHermitian) (i : Fin n) :
    ((A*A) i i).re = ∑ j, ‖A i j‖^2 := by
  rw [Matrix.mul_apply, Complex.re_sum]
  apply sum_congr rfl
  intro j _
  rw [← h.apply j i]
  change (A i j * conj (A i j)).re = _
  rw [Complex.mul_conj,Complex.ofReal_re,Complex.sq_norm]
private lemma mean_herm {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) (U : Ω → Mat n) :
    (meanRoot μ U).IsHermitian := by
  ext i j
  change conj (∫ ω, CFC.sqrt (U ω) j i ∂μ) = _
  rw [←integral_conj]
  apply integral_congr_ae
  exact .of_forall (fun ω => ((CFC.sqrt_nonneg (U ω)).posSemidef.1.apply i j))
private lemma quantity_sum {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) (U : Ω → Mat n) :
    quantity μ U = ∑ i,∑ j,‖meanRoot μ U i j‖^2 := by
  unfold quantity Matrix.trace
  rw [Complex.re_sum]
  exact sum_congr rfl fun i _ => square_diag _ (mean_herm μ U) i
private lemma scalar_lower {m s b : ℝ} (hm : 0≤ m) (hs : 0≤ s) (_hb : 0≤ b)
    (h : ∀ t : ℝ, 0≤ t → 3*t^2*m ≤ s + 2*t^3*b) : m^3/s ≤ b^2 := by
  rcases hs.eq_or_lt with hs|hs
  · rw [←hs,div_zero]; positivity
  rcases hm.eq_or_lt with hm|hm
  · rw [←hm]; simpa using sq_nonneg b
  let t := Real.sqrt (s/m)
  have ht : 0< t := Real.sqrt_pos.mpr (div_pos hs hm)
  have hq : t^2 = s/m := Real.sq_sqrt (by positivity)
  have he : t^2*m = s := (eq_div_iff hm.ne').mp hq
  have hh := h t ht.le
  have ht3 : t^3 = t^2*t := by ring
  rw [ht3] at hh
  have hm' : m ≤ t*b := by
    by_contra! ha
    nlinarith [mul_lt_mul_of_pos_left ha (show 0< t^2 by positivity)]
  rw [div_le_iff₀ hs,← he]
  nlinarith [mul_le_mul_of_nonneg_right (sq_le_sq' (by nlinarith) hm') hm.le]
end OMA.S_mo_262608
namespace OMA.S_mo_262608
open MeasureTheory Matrix Finset ComplexConjugate ProbabilityTheory
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
private lemma establish {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → Mat n) (hpos : ∀ᵐ ω ∂μ, (U ω).PosSemidef)
    (h2 : ∀ i j, MemLp (fun ω => U ω i j) 2 μ) :
    (∑ i, (first μ U i)^3 / second μ U i) ≤ quantity μ U ∧ quantity μ U ≤ ∑ i,first μ U i := by
  classical
  let : MeasurableSpace (Mat n) := inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℂ))
  let : BorelSpace (Mat n) := inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))
  let R (ω : Ω) := CFC.sqrt (U ω)
  have hm : AEMeasurable U μ := aemeasurable_pi_iff.mpr fun i => aemeasurable_pi_iff.mpr fun j => (h2 i j).aemeasurable
  have hr : AEMeasurable R μ := by
    have hcont : Continuous (fun A : Mat n => CFC.sqrt (CFC.abs A)) :=
      CFC.continuousOn_sqrt.comp_continuous CFC.continuous_abs (fun A => CFC.abs_nonneg A)
    apply (hcont.measurable.comp_aemeasurable hm).congr
    filter_upwards [hpos] with ω hω
    simp [R,CFC.abs_of_nonneg _ hω.nonneg]
  have hentry (i j : Fin n) : AEMeasurable (fun ω => R ω i j) μ :=
    aemeasurable_pi_iff.mp (aemeasurable_pi_iff.mp hr i) j
  have hsum (i : Fin n) : ∀ᵐ ω ∂μ, (U ω i i).re = ∑ j, ‖R ω i j‖^2 := by
    filter_upwards [hpos] with ω hω
    convert square_diag (R ω) ((CFC.sqrt_nonneg (U ω)).posSemidef.1) i using 1
    rw [show R ω * R ω = U ω from CFC.sqrt_mul_sqrt_self _ hω.nonneg]
  have hL (i j : Fin n) : MemLp (fun ω => R ω i j) 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm (hentry i j).aestronglyMeasurable).mpr
    have hi := ((h2 i i).integrable (by norm_num)).re
    apply hi.mono' (((hentry i j).norm.pow_const 2).aestronglyMeasurable)
    filter_upwards [hsum i] with ω hω
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (single_le_sum (f := fun j => ‖R ω i j‖^2) (fun j _ => sq_nonneg _) (mem_univ j)).trans hω.ge
  have hS (i : Fin n) : Integrable (fun ω => ((U ω * U ω) i i).re) μ := by
    have hi : Integrable (fun ω => (U ω * U ω) i i) μ := by
      simp only [Matrix.mul_apply]
      exact integrable_finsetSum Finset.univ (fun j _ => (h2 i j).integrable_mul (h2 j i))
    exact hi.re
  have hF (i : Fin n) : 0 ≤ first μ U i := integral_nonneg_of_ae <| hpos.mono (fun ω hw => (Complex.nonneg_iff.mp (hw.diag_nonneg (i:=i))).1)
  have hB (i : Fin n) : 0 ≤ (meanRoot μ U i i).re := by
    change 0 ≤ (∫ ω, R ω i i ∂μ).re
    rw [← (show (∫ ω, (R ω i i).re ∂μ) = (∫ ω, R ω i i ∂μ).re from integral_re ((hL i i).integrable (by norm_num)))]
    exact integral_nonneg (fun ω => (Complex.nonneg_iff.mp ((CFC.sqrt_nonneg (U ω)).posSemidef.diag_nonneg (i:=i))).1)
  have hRint (i j : Fin n) : (∫ ω, (R ω i j).re ∂μ) = (meanRoot μ U i j).re :=
    integral_re ((hL i j).integrable (by norm_num))
  have hdiag (i : Fin n) : (first μ U i)^3 / second μ U i ≤ (meanRoot μ U i i).re^2 := by
    apply scalar_lower (hF i) (integral_nonneg_of_ae (hpos.mono (fun ω hw => by
      change 0 ≤ ((U ω * U ω) i i).re
      rw [square_diag _ hw.1]; positivity))) (hB i)
    intro t ht
    have hu : Integrable (fun ω => (U ω i i).re) μ := ((h2 i i).integrable (by norm_num)).re
    have hv : Integrable (fun ω => (R ω i i).re) μ := ((hL i i).integrable (by norm_num)).re
    have hp : (∫ ω, 3*t^2*(U ω i i).re ∂μ) ≤ ∫ ω, ((U ω*U ω) i i).re + 2*t^3*(R ω i i).re ∂μ :=
      integral_mono_ae (hu.const_mul _) ((hS i).add (hv.const_mul _)) (hpos.mono (fun ω hw => support_poly _ hw t ht i))
    rw [integral_const_mul,integral_add (hS i) (hv.const_mul _),integral_const_mul,hRint] at hp
    exact hp
  rw [quantity_sum]
  constructor
  · apply sum_le_sum
    intro i _
    apply (hdiag i).trans
    apply le_trans _ (single_le_sum (f := fun j => ‖meanRoot μ U i j‖^2) (fun j _ => sq_nonneg _) (mem_univ i))
    rw [Complex.sq_norm,Complex.normSq_apply]
    nlinarith [sq_nonneg (meanRoot μ U i i).im]
  · apply sum_le_sum
    intro i _
    unfold first
    rw [integral_congr_ae (hsum i),integral_finsetSum _ (fun j _ => (memLp_two_iff_integrable_sq_norm (hL i j).1).mp (hL i j))]
    apply sum_le_sum
    intro j _
    have hvar := variance_nonneg (fun ω => ‖R ω i j‖) μ
    rw [variance_eq_sub (hL i j).norm] at hvar
    have hn := norm_integral_le_integral_norm (fun ω => R ω i j) (μ := μ)
    change ‖∫ ω, R ω i j ∂μ‖^2 ≤ _
    change 0 ≤ (∫ ω, ‖R ω i j‖^2 ∂μ) - (∫ ω, ‖R ω i j‖ ∂μ)^2 at hvar
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (sub_nonneg.mp hvar)
end
end OMA.S_mo_262608
namespace OMA.S_mo_262608
open MeasureTheory Matrix Finset Set
open scoped MatrixOrder ComplexOrder
private instance unit_probability : IsProbabilityMeasure unitLaw := ⟨by simp [unitLaw,Real.volume_Ioc]⟩
private lemma mean_two (p a b : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (∫ x, (if x ≤ p then b else a) ∂unitLaw) = p*b+(1-p)*a := by
  have he : (Iic p ∩ Ioc 0 1) = Ioc 0 p := by ext x; simp; constructor <;> rintro ⟨h,h'⟩ <;> grind
  have ht : unitLaw.real (Iic p) = p := by
    rw [unitLaw,measureReal_restrict_apply measurableSet_Iic,he,Real.volume_real_Ioc_of_le h0, sub_zero]
  change (∫ x, (Iic p).piecewise (fun _ => b) (fun _ => a) x ∂unitLaw) = _
  rw [integral_piecewise measurableSet_Iic (integrable_const _).integrableOn (integrable_const _).integrableOn,
    setIntegral_const,setIntegral_const,measureReal_compl measurableSet_Iic,probReal_univ,ht]
  rfl
private noncomputable def mix {n : ℕ} (p a b : Fin n → ℝ) (x : ℝ) (i : Fin n) := if x ≤ p i then b i else a i
private noncomputable def diagonalLaw {n : ℕ} (p a b : Fin n → ℝ) (x : ℝ) : Mat n :=
  diagonal (fun i => (mix p a b x i : ℂ))
private lemma mix_finite {n : ℕ} (p a b : Fin n → ℝ) : finiteDiagonal (diagonalLaw p a b) := by
  classical
  let G (u : Fin n → Bool) : Mat n := diagonal (fun i => if u i then (b i:ℂ) else (a i:ℂ))
  refine ⟨(Set.finite_range G).subset ?_,fun x i j h => diagonal_apply_ne _ h⟩
  rintro _ ⟨x,rfl⟩
  refine ⟨fun i => decide (x ≤ p i),?_⟩
  unfold G diagonalLaw
  congr 1
  funext i
  by_cases h : x ≤ p i <;> simp [h,mix]
private lemma sqrt_diagonal_real {n : ℕ} (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) :
    CFC.sqrt (diagonal (fun i => (v i:ℂ))) = diagonal (fun i => (Real.sqrt (v i):ℂ)) := by
  let D : Mat n := diagonal (fun i => (Real.sqrt (v i):ℂ))
  have hD : D.PosSemidef := posSemidef_diagonal_iff.mpr (fun i => by exact_mod_cast Real.sqrt_nonneg (v i))
  apply Eq.trans _ (CFC.sqrt_mul_self D hD.nonneg)
  congr 1
  dsimp only [D]
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  change (v i:ℂ) = ↑(Real.sqrt (v i)) * ↑(Real.sqrt (v i))
  exact_mod_cast (Real.mul_self_sqrt (hv i)).symm
private lemma mix_info {n : ℕ} (p a b : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∀ x, (diagonalLaw p a b x).PosSemidef) ∧
    (∀ i j, MemLp (fun x => diagonalLaw p a b x i j) 2 unitLaw) ∧
    (∀ i, first unitLaw (diagonalLaw p a b) i = p i*b i+(1-p i)*a i) ∧
    (∀ i, second unitLaw (diagonalLaw p a b) i = p i*(b i)^2+(1-p i)*(a i)^2) ∧
    quantity unitLaw (diagonalLaw p a b) = ∑ i,(p i*Real.sqrt (b i)+(1-p i)*Real.sqrt (a i))^2 := by
  classical
  have hnon (x i) : 0 ≤ mix p a b x i := by unfold mix; split_ifs <;> grind
  have hm (x) : CFC.sqrt (diagonalLaw p a b x) = diagonal (fun i => (Real.sqrt (mix p a b x i):ℂ)) :=
    sqrt_diagonal_real _ (hnon x)
  have hroot : meanRoot unitLaw (diagonalLaw p a b) = diagonal (fun i => ((p i*Real.sqrt (b i)+(1-p i)*Real.sqrt (a i):ℝ):ℂ)) := by
    ext i j
    change (∫ x, CFC.sqrt (diagonalLaw p a b x) i j ∂unitLaw) = _
    simp_rw [hm]
    by_cases h : i=j
    · subst j; simp only [diagonal_apply_eq]
      rw [show (∫ x, (Real.sqrt (mix p a b x i):ℂ) ∂unitLaw) = ↑(∫ x, Real.sqrt (mix p a b x i) ∂unitLaw) from integral_ofReal]
      congr 1
      simpa only [mix,apply_ite Real.sqrt] using mean_two (p i) (Real.sqrt (a i)) (Real.sqrt (b i)) (hp0 i) (hp1 i)
    · simp [diagonal_apply_ne _ h]
  refine ⟨fun x => posSemidef_diagonal_iff.mpr (fun i => by exact_mod_cast hnon x i),?_,?_,?_,?_⟩
  · intro i j
    by_cases h : i=j
    · subst j; simp only [diagonalLaw,diagonal_apply_eq,mix,apply_ite Complex.ofReal]
      exact MemLp.piecewise (s:=Iic (p i)) measurableSet_Iic (memLp_const _) (memLp_const _)
    · simp [diagonalLaw,diagonal_apply_ne _ h]
  · intro i
    simpa only [first,diagonalLaw,diagonal_apply_eq,Complex.ofReal_re,mix] using mean_two (p i) (a i) (b i) (hp0 i) (hp1 i)
  · intro i
    unfold second diagonalLaw
    simp only [diagonal_mul_diagonal,diagonal_apply_eq,←Complex.ofReal_mul,Complex.ofReal_re]
    convert mean_two (p i) (a i^2) (b i^2) (hp0 i) (hp1 i) using 1
    apply integral_congr_ae
    exact .of_forall (fun x => by by_cases hx : x ≤ p i <;> simp [mix,hx,sq])
  · simp only [quantity,hroot,diagonal_mul_diagonal,Matrix.trace,Matrix.diag_diagonal,Complex.re_sum,
      ←Complex.ofReal_mul,Complex.ofReal_re,sq]
end OMA.S_mo_262608
namespace OMA.S_mo_262608
open Real Filter Set
open scoped Topology
private noncomputable def topAtom (m s t : ℝ) := m + (s-m^2)/((1-t)*m)
private noncomputable def topMass (m s t : ℝ) := ((1-t)*m)^2 / (s-m^2+((1-t)*m)^2)
private noncomputable def average (m s t : ℝ) :=
  topMass m s t * √(topAtom m s t) + (1-topMass m s t)*√(t*m)
private lemma parameter_data (m s : ℝ) (hm : 0 < m) (hs : m^2 ≤ s)
    (t : ℝ) (ht : t < 1) :
    0 < topMass m s t ∧ topMass m s t ≤ 1 ∧ m ≤ topAtom m s t ∧
    topMass m s t * topAtom m s t + (1-topMass m s t)*(t*m) = m ∧
    topMass m s t * (topAtom m s t)^2 + (1-topMass m s t)*(t*m)^2 = s := by
  let v := s-m^2
  let d := (1-t)*m
  have hv : 0 ≤ v := sub_nonneg.mpr hs
  have hd : 0 < d := mul_pos (sub_pos.mpr ht) hm
  have hD : 0 < v+d^2 := by positivity
  have ht' : t*m=m-d := by dsimp [d]; ring
  change 0 < d^2/(v+d^2) ∧ d^2/(v+d^2) ≤ 1 ∧ m ≤ m+v/d ∧ _
  refine ⟨by positivity,(div_le_one hD).mpr (by linarith),(le_add_of_nonneg_right (div_nonneg hv hd.le)),?_⟩
  change d^2/(v+d^2)*(m+v/d)+(1-d^2/(v+d^2))*(t*m)=m ∧
    d^2/(v+d^2)*(m+v/d)^2+(1-d^2/(v+d^2))*(t*m)^2=s
  rw [ht']
  constructor
  · field_simp; ring
  · field_simp
    dsimp [v]
    ring
private lemma average_cont (m s : ℝ) (hm : 0 < m) (hs : m^2≤ s) (t : ℝ) (ht : t< 1) :
    ContinuousAt (average m s) t := by
  have hd : 0 < (1-t)*m := mul_pos (sub_pos.mpr ht) hm
  have hD : 0 < s-m^2+((1-t)*m)^2 := add_pos_of_nonneg_of_pos (sub_nonneg.mpr hs) (sq_pos_of_pos hd)
  unfold average topMass topAtom
  fun_prop (disch := positivity)
private lemma average_zero (m s : ℝ) (hm : 0 < m) (hs : m^2≤ s) : average m s 0 ^ 2=m^3/s := by
  have hs' : 0 < s := (sq_pos_of_pos hm).trans_le hs
  have hh : m+(s-m^2)/m=s/m := by field_simp; ring
  simp only [average,topMass,topAtom,sub_zero,one_mul,zero_mul,Real.sqrt_zero,mul_zero,add_zero,
    sub_add_cancel,hh,mul_pow,Real.sq_sqrt (div_nonneg hs'.le hm.le)]
  field_simp
private lemma average_bound (m s : ℝ) (hm : 0 < m) (hs : m^2 ≤ s)
    (t : ℝ) (ht : 0≤ t) (ht1 : t< 1) : t*m ≤ (average m s t)^2 := by
  obtain ⟨hp,_,hb,_,_⟩ := parameter_data m s hm hs t ht1
  have ha : t*m ≤ topAtom m s t := (mul_le_of_le_one_left hm.le ht1.le).trans hb
  have hq := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ha) hp.le
  have he : √(t*m) ≤ average m s t := by unfold average; linarith
  simpa [Real.sq_sqrt (mul_nonneg ht hm.le)] using pow_le_pow_left₀ (Real.sqrt_nonneg _) he 2
end OMA.S_mo_262608
namespace OMA.S_mo_262608
open MeasureTheory Matrix Finset Filter Set
open scoped MatrixOrder ComplexOrder Topology
private lemma sharp_range {n : ℕ} (m s : Fin n → ℝ) (hm : ∀ i, 0 < m i) (hs : ∀ i, (m i)^2 ≤ s i) :
    (∃ U : ℝ → Mat n, (∀ x, (U x).PosSemidef) ∧ finiteDiagonal U ∧ fits m s U ∧ quantity unitLaw U = ∑ i,(m i)^3/s i) ∧
    IsGLB (diagonalValues m s) (∑ i,(m i)^3/s i) ∧ IsLUB (diagonalValues m s) (∑ i,m i) ∧
    Set.Ioo (∑ i,(m i)^3/s i) (∑ i,m i) ⊆ diagonalValues m s := by
  classical
  let F (t : ℝ) := ∑ i,(average (m i) (s i) t)^2
  have hc (t : ℝ) (ht : t < 1) : ContinuousAt F t := by
    have hterm (i : Fin n) := average_cont _ _ (hm i) (hs i) t ht
    unfold F
    fun_prop
  have h0 : F 0 = ∑ i,(m i)^3/s i := sum_congr rfl fun i _ => average_zero _ _ (hm i) (hs i)
  have hbig (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) : t*(∑ i, m i) ≤ F t := by
    rw [mul_sum]; exact sum_le_sum (fun i _ => average_bound _ _ (hm i) (hs i) _ ht ht1)
  have make (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) : ∃ U : ℝ → Mat n, (∀ x, (U x).PosSemidef) ∧
      finiteDiagonal U ∧ fits m s U ∧ quantity unitLaw U = F t ∧ (0 < t → ∀ x, (U x).PosDef) := by
    let p i := topMass (m i) (s i) t
    let a i := t*m i
    let b i := topAtom (m i) (s i) t
    have hi i := parameter_data (m i) (s i) (hm i) (hs i) t ht1
    obtain ⟨hn,hl,hf,hg,hq⟩ := mix_info p a b (fun i => (hi i).1.le) (fun i => (hi i).2.1)
      (fun i => mul_nonneg ht (hm i).le) (fun i => (hm i).le.trans (hi i).2.2.1)
    refine ⟨_,hn,mix_finite p a b,⟨hl,funext (fun i => (hf i).trans (hi i).2.2.2.1),funext (fun i => (hg i).trans (hi i).2.2.2.2)⟩,hq,?_⟩
    intro ht' x
    apply posDef_diagonal_iff.mpr
    intro i
    change (0:ℂ) < ↑(mix p a b x i)
    apply Complex.zero_lt_real.mpr
    dsimp [mix]
    split_ifs
    · exact (hm i).trans_le (hi i).2.2.1
    · exact mul_pos ht' (hm i)
  have hval (t : ℝ) (ht : 0 < t) (ht1 : t < 1) : F t ∈ diagonalValues m s := by
    obtain ⟨U,_,hfin,hfit,hq,hpd⟩ := make t ht.le ht1
    exact ⟨U,hpd ht,hfin,hfit,hq⟩
  have bounds {z : ℝ} (hz : z ∈ diagonalValues m s) : (∑ i, m i^3/s i) ≤ z ∧ z ≤ ∑ i,m i := by
    obtain ⟨U,hpd,_,⟨hl,hfirst,hsec⟩,rfl⟩ := hz
    simpa only [hfirst,hsec] using establish unitLaw U (.of_forall (fun x => (hpd x).posSemidef)) hl
  have near_zero (z : ℝ) (hz : F 0 < z) : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ F t < z := by
    have he : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), F t < z := (((hc 0 zero_lt_one).tendsto.mono_left nhdsWithin_le_nhds).eventually_lt_const hz)
    have ha : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), 0 < t := self_mem_nhdsWithin
    exact (ha.and (((eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds).and he)).exists
  have near_one (z : ℝ) (hz : z < ∑ i,m i) : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ z < F t := by
    have hg : ContinuousAt (fun t : ℝ => t*∑ i,m i) 1 := by fun_prop
    have he : ∀ᶠ t : ℝ in 𝓝[<] (1:ℝ), z < t*∑ i,m i := (hg.tendsto.mono_left nhdsWithin_le_nhds).eventually_const_lt (show z < 1*∑ i,m i by simpa using hz)
    have ha : ∀ᶠ t : ℝ in 𝓝[<] (1:ℝ), t < 1 := self_mem_nhdsWithin
    obtain ⟨t,ht0,ht1,ht⟩ := (((eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds).and (ha.and he)).exists
    exact ⟨t,ht0,ht1,ht.trans_le (hbig t ht0.le ht1)⟩
  obtain ⟨U,hU,hfin,hfit,hq,_⟩ := make 0 le_rfl zero_lt_one
  refine ⟨⟨U,hU,hfin,hfit,hq.trans h0⟩,⟨fun _ hz => (bounds hz).1,?_⟩,⟨fun _ hz => (bounds hz).2,?_⟩,?_⟩
  · intro z hz
    by_contra! hn
    obtain ⟨t,ha,hb,hh⟩ := near_zero z (h0.trans_lt hn)
    exact (not_lt_of_ge (hz (hval t ha hb))) hh
  · intro z hz
    by_contra! hn
    obtain ⟨t,ha,hb,hh⟩ := near_one z hn
    exact (not_lt_of_ge (hz (hval t ha hb))) hh
  · intro z hz
    obtain ⟨t,ha,hb,hh⟩ := near_one z hz.2
    obtain ⟨u,hu,hu'⟩ := intermediate_value_Icc ha.le
      (fun x hx => (hc x (hx.2.trans_lt hb)).continuousWithinAt) (show z ∈ Icc (F 0) (F t) from ⟨(h0.trans_lt hz.1).le,hh.le⟩)
    have hu0 : u ≠ 0 := by rintro rfl; linarith [h0.trans_lt hz.1]
    exact hu' ▸ hval u (lt_of_le_of_ne hu.1 hu0.symm) (hu.2.trans_lt hb)
end OMA.S_mo_262608
theorem OMA.solution : type_of% @OMA.S_mo_262608.main := by
  exact ⟨fun _ _ μ _ _ U => OMA.S_mo_262608.establish μ U, fun _ m s => OMA.S_mo_262608.sharp_range m s⟩
