import OMAStatements.S_mo_299643

namespace OMA.S_mo_299643
open MeasureTheory ProbabilityTheory Matrix Finset Set
open scoped NNReal
private lemma lognormal_ac : lognormal ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs h0
  rw [lognormal,Measure.map_apply Real.measurable_exp hs]
  apply gaussianReal_absolutelyContinuous 0 (by norm_num : (4:ℝ≥0)≠0)
  let t := Real.exp ⁻¹' s
  have ht : MeasurableSet t := Real.measurable_exp hs
  have hi := lintegral_deriv_eq_volume_image_of_monotoneOn ht
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) (Real.exp_monotone.monotoneOn t)
  have him : volume (Real.exp '' t)=0 := measure_mono_null (image_preimage_subset _ _) h0
  rw [him] at hi
  have hpos : Function.support (fun x : ℝ => ENNReal.ofReal (Real.exp x))=Set.univ := by
    ext x
    simp [Function.mem_support,Real.exp_pos]
  by_contra! hn
  have h := (setLIntegral_pos_iff (f:=fun x : ℝ => ENNReal.ofReal (Real.exp x))
    (by fun_prop) (s:=t) (μ:=volume)).mpr (by simpa [hpos] using pos_iff_ne_zero.mpr hn)
  exact (ne_of_gt h) hi

private lemma lognormal_integrable (k : ℕ) : Integrable (fun x : ℝ => x^k) lognormal := by
  rw [lognormal,integrable_map_measure (by fun_prop) Real.measurable_exp.aemeasurable]
  simpa [Function.comp_def,← Real.exp_nat_mul] using
    (integrable_exp_mul_gaussianReal (μ:=0) (v:=4) (k:ℝ))

private lemma lognormal_moment (k : ℕ) : moment lognormal k=Real.exp (2*(k:ℝ)^2) := by
  rw [moment,lognormal,integral_map Real.measurable_exp.aemeasurable (by fun_prop)]
  have h := congrFun (mgf_id_gaussianReal (μ:=0) (v:=4)) (k:ℝ)
  simp only [mgf,id_eq,zero_mul,zero_add,NNReal.coe_ofNat] at h
  simp only [← Real.exp_nat_mul]
  rw [h]
  congr 1
  ring

private lemma lognormal_gram (n : ℕ) (i j : Fin n) :
    gram lognormal n i j=Real.exp (-2*((i.val:ℝ)-j.val)^2) := by
  have hroot (x : ℝ) : Real.sqrt (Real.exp x)=Real.exp (x/2) := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [gram,lognormal_moment,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
    hroot,← Real.exp_add,← Real.exp_sub]
  congr 1
  ring

private lemma gram_herm (μ : Measure ℝ) (n : ℕ) : (gram μ n).IsHermitian := by
  ext i j
  simp [gram,Matrix.conjTranspose_apply,add_comm,mul_comm]

private lemma gaussian_decay (i j : ℕ) (hij : i < j) :
    Real.exp (-2*((i:ℝ)-j)^2)≤(1/4:ℝ)^(j-i) := by
  let d := j-i
  have hd : 1≤d := by omega
  have hreal : (d:ℝ)=j-i := by exact_mod_cast Nat.cast_sub hij.le
  have h1 : (1:ℝ)≤d := by exact_mod_cast hd
  have h2 : 4≤Real.exp 2 := by
    have he := Real.add_one_le_exp 1
    rw [show (2:ℝ)=1+1 by norm_num,Real.exp_add]
    nlinarith [Real.exp_pos 1]
  have hq : Real.exp (-2)≤(1/4:ℝ) := by
    rw [Real.exp_neg,one_div]
    exact inv_anti₀ (by norm_num) h2
  calc Real.exp (-2*((i:ℝ)-j)^2) ≤ Real.exp ((d:ℝ)*(-2)) := by
         apply Real.exp_le_exp.mpr
         rw [← sub_sq_comm,← hreal]
         nlinarith
       _ = Real.exp (-2)^d := Real.exp_nat_mul _ _
       _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hq d

private lemma half_row {n : ℕ} (s : Finset (Fin n)) (f : Fin n → ℕ) (b : Fin n → ℝ)
    (hinj : Set.InjOn f s) (hmem : ∀ j ∈ s, f j<n)
    (hbound : ∀ j ∈ s, b j≤(1/4:ℝ)^(f j+1)) : ∑ j ∈ s,b j≤1/3 := by
  classical
  calc ∑ j ∈ s,b j ≤ ∑ j ∈ s,(1/4:ℝ)^(f j+1) := sum_le_sum hbound
       _ = ∑ a ∈ s.image f,(1/4:ℝ)^(a+1) := by rw [sum_image hinj]
       _ ≤ ∑ a ∈ range n,(1/4:ℝ)^(a+1) := by
         apply sum_le_sum_of_subset_of_nonneg
         · intro a ha
           obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
           exact mem_range.mpr (hmem j hj)
         · intros; positivity
       _ ≤ 1/3 := by
         simp_rw [pow_succ]
         rw [← sum_mul,geom_sum_eq (by norm_num : (1/4:ℝ)≠1)]
         have hgeo (x : ℝ) (hx : 0≤x) : (x-1)/(1/4-1)*(1/4) ≤ 1/3 := by
           rw [show (1/4-1:ℝ)=-3/4 by norm_num]
           linarith
         exact hgeo _ (pow_nonneg (by norm_num) n)

private lemma radius {n : ℕ} (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i,‖gram lognormal n i j‖≤2/3 := by
  classical
  let s := Finset.univ.erase i
  let g := fun j : Fin n => ‖gram lognormal n i j‖
  have hlo : ∑ j ∈ s.filter (fun j => j < i),g j≤1/3 := by
    apply half_row _ (fun j => i.val-j.val-1)
    · intro a ha b hb he
      have ha' := (mem_filter.mp ha).2
      have hb' := (mem_filter.mp hb).2
      exact Fin.ext (by dsimp at he; omega)
    · intro j hj
      omega
    · intro j hj
      have hji := (mem_filter.mp hj).2
      have hh : i.val-j.val-1+1=i.val-j.val := by omega
      simp only [g,lognormal_gram,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),hh]
      rw [sub_sq_comm]
      exact gaussian_decay _ _ hji
  have hhi : ∑ j ∈ s.filter (fun j => ¬ j < i),g j≤1/3 := by
    have hlt (j : Fin n) (h : j ∈ s.filter (fun j => ¬ j < i)) : i < j := by
      obtain ⟨h1,h2⟩ := mem_filter.mp h
      exact lt_of_le_of_ne (not_lt.mp h2) (ne_of_mem_erase h1).symm
    apply half_row _ (fun j => j.val-i.val-1)
    · intro a ha b hb he
      have := hlt a ha; have := hlt b hb
      exact Fin.ext (by dsimp at he; omega)
    · intro j hj
      omega
    · intro j hj
      have hij := hlt j hj
      have hh : j.val-i.val-1+1=j.val-i.val := by omega
      simp only [g,lognormal_gram,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),hh]
      exact gaussian_decay _ _ hij
  change ∑ j ∈ s,g j≤2/3
  have h := sum_filter_add_sum_filter_not s (fun j => j < i) g
  linarith

private lemma lognormal_gap (n : ℕ) (i : Fin n) :
    1/3≤(gram_herm lognormal n).eigenvalues i := by
  let A := gram lognormal n
  let hA := gram_herm lognormal n
  have hm := hA.mulVec_eigenvectorBasis i
  have he : Module.End.HasEigenvalue (Matrix.toLin' A) (hA.eigenvalues i) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector (x:=⇑(hA.eigenvectorBasis i))
    refine ⟨Module.End.mem_eigenspace_iff.mpr hm,?_⟩
    intro hz
    have hh : hA.eigenvectorBasis i=0 := by ext j; exact congrFun hz j
    have hnorm := hA.eigenvectorBasis.norm_eq_one i
    simp [hh] at hnorm
  obtain ⟨j,hj⟩ := eigenvalue_mem_ball he
  rw [Metric.mem_closedBall,Real.dist_eq] at hj
  have hdiag : A j j=1 := by simp [A,lognormal_gram]
  rw [hdiag,abs_le] at hj
  have hr := radius j
  change ∑ k ∈ Finset.univ.erase j, ‖A j k‖≤2/3 at hr
  linarith [hj.1]

open Filter Unitary
private lemma trace_estimates {n : ℕ} (hn : 0<n) (A : Mat n) (hA : A.PosDef)
    (hd : ∀ i,A i i=1) :
    (∀ k : ℕ, 0<k → ∀ i,traceBound A k≤hA.1.eigenvalues i) ∧
      ∃ k : ℕ, 0<k ∧ 0<traceBound A k := by
  classical
  let e := hA.1.eigenvalues
  let x := fun i => 1-(n:ℝ)⁻¹*e i
  let F := conjStarAlgAut ℝ _ hA.1.eigenvectorUnitary
  have hN : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hsum : ∑ i,e i=(n:ℝ) := by
    calc ∑ i,e i = A.trace := by simpa [e] using hA.1.trace_eq_sum_eigenvalues.symm
         _ = _ := by simp [Matrix.trace,Matrix.diag,hd]
  have hEi i : e i≤(n:ℝ) := hsum ▸ single_le_sum (fun j _ => (hA.eigenvalues_pos j).le)
    (mem_univ i)
  have hx i : 0≤x i := by
    change 0≤1-(n:ℝ)⁻¹*e i
    rw [← div_eq_inv_mul]
    exact sub_nonneg.mpr ((div_le_one hN).mpr (hEi i))
  have hx1 i : x i<1 := by
    change 1-(n:ℝ)⁻¹ * e i<1
    have := mul_pos (inv_pos.mpr hN) (hA.eigenvalues_pos i)
    linarith
  have hspec : A = F (diagonal e) := by simpa [F,e] using hA.1.spectral_theorem
  have hR : 1-(n:ℝ)⁻¹ • A = F (diagonal x) := by
    have hdiag : diagonal x=1-(n:ℝ)⁻¹ • diagonal e := by
      ext i j
      by_cases h : i=j <;> simp [x,h]
    rw [hdiag,map_sub,map_one,map_smul,← hspec]
  have htr (k : ℕ) : ((1-(n:ℝ)⁻¹ • A)^k).trace=∑ i,x i^k := by
    rw [hR,← map_pow,diagonal_pow]
    dsimp only [F]
    rw [conjStarAlgAut_apply,trace_mul_cycle,coe_star_mul_self,Matrix.one_mul,trace_diagonal]
    rfl
  constructor
  · intro k hk i
    have hK : (0:ℝ)<k := Nat.cast_pos.mpr hk
    have ht := single_le_sum (s:=Finset.univ) (f:=fun j => x j^k)
      (fun j _ => pow_nonneg (hx j) k) (mem_univ i)
    have hp := one_add_mul_le_pow (a:=-(n:ℝ)⁻¹*e i) (by
      have h := hx i
      dsimp [x] at h
      linarith) k
    have hp' : 1-(k:ℝ)*((n:ℝ)⁻¹*e i) ≤ x i^k := by
      simpa only [x,neg_mul,mul_neg,sub_eq_add_neg] using hp
    rw [traceBound,htr,div_le_iff₀ hK]
    have h := mul_le_mul_of_nonneg_left (hp'.trans ht) hN.le
    calc (n:ℝ)*(1-∑ j,x j^k) ≤ (n:ℝ)*((k:ℝ)*((n:ℝ)⁻¹*e i)) := by linarith
         _ = e i*k := by field_simp
  · have ht : Tendsto (fun k : ℕ => ∑ i,x i^k) atTop (nhds 0) := by
      simpa using tendsto_finsetSum Finset.univ
        (fun i _ => tendsto_pow_atTop_nhds_zero_of_lt_one (hx i) (hx1 i))
    obtain ⟨k,hk,hsmall⟩ := ((eventually_gt_atTop 0).and
      (ht.eventually_lt_const (by norm_num : (0:ℝ)<1))).exists
    refine ⟨k,hk,?_⟩
    rw [traceBound,htr]
    exact div_pos (mul_pos hN (sub_pos.mpr hsmall)) (Nat.cast_pos.mpr hk)

open Polynomial
private lemma rayleigh_min {n : ℕ} (H : Mat (n+1)) (hh : H.IsHermitian)
    (z : Fin (n+1) → ℝ) :
    ∃ i, hh.eigenvalues i*(∑ j,z j^2)≤z ⬝ᵥ (H *ᵥ z) := by
  classical
  let e := hh.eigenvalues
  obtain ⟨i,_,hi⟩ := exists_min_image Finset.univ e Finset.univ_nonempty
  let F := Unitary.conjStarAlgAut ℝ _ hh.eigenvectorUnitary
  have hs : H=F (diagonal e) := by simpa [F,e] using hh.spectral_theorem
  have hId : diagonal (fun j => e j-e i) = diagonal e - e i • (1 : Mat (n+1)) := by
    ext u v
    by_cases h : u=v <;> simp [h]
  have hps : (H-e i • (1 : Mat (n+1))).PosSemidef := by
    have hp := Matrix.PosSemidef.diagonal (fun j =>
      sub_nonneg.mpr (hi j (mem_univ j)))
    have h := hp.mul_mul_conjTranspose_same (hh.eigenvectorUnitary : Mat (n+1))
    change (F (diagonal (fun j => e j-e i))).PosSemidef at h
    rwa [hId,map_sub,map_smul,map_one,← hs] at h
  have h := hps.dotProduct_mulVec_nonneg z
  rw [sub_mulVec,smul_mulVec,one_mulVec,dotProduct_sub,dotProduct_smul] at h
  refine ⟨i,?_⟩
  simpa [dotProduct,pow_two,smul_eq_mul,e] using sub_nonneg.mp h

private lemma trial_vector (μ : Measure ℝ) (hm : ∀ k : ℕ,Integrable (fun x : ℝ => x^k) μ)
    (hp : ∀ k,0 < moment μ (2*k)) (P : ℝ[X]) (n : ℕ) (hd : P.natDegree≤n) :
    ∃ i : Fin (n+1), (gram_herm μ (n+1)).eigenvalues i *
      (∑ j : Fin (n+1), (P.coeff j.val)^2*moment μ (2*j.val)) ≤
      ∫ x,P.eval x^2 ∂μ := by
  classical
  let d := fun j : Fin (n+1) => Real.sqrt (moment μ (2*j.val))
  let z := fun j : Fin (n+1) => P.coeff j.val*d j
  have hdpos j : d j≠0 := (Real.sqrt_pos.mpr (hp _)).ne'
  have hd2 j : d j^2=moment μ (2*j.val) := Real.sq_sqrt (hp _).le
  have hsq : ∑ j,z j^2=∑ j : Fin (n+1),(P.coeff j.val)^2*moment μ (2*j.val) := by
    simp only [z,mul_pow,hd2]
  have heval x : P.eval x^2 = ∑ i : Fin (n+1),∑ j : Fin (n+1),
      (P.coeff i.val*P.coeff j.val)*x^(i.val+j.val) := by
    rw [eval_eq_sum_range' (by omega : P.natDegree < n+1),← Fin.sum_univ_eq_sum_range]
    simp only [pow_two,sum_mul,mul_sum,pow_add]
    exact sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => by ring))
  have hI i j : Integrable (fun x : ℝ => (P.coeff i*P.coeff j)*x^(i+j)) μ :=
    (hm _).const_mul _
  have hquad : z ⬝ᵥ (gram μ (n+1) *ᵥ z) = ∫ x,P.eval x^2 ∂μ := by
    simp_rw [heval]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI i.val j.val))]
    have hinner (i : Fin (n+1)) : (∫ x, ∑ j : Fin (n+1),
        (P.coeff i.val*P.coeff j.val)*x^(i.val+j.val) ∂μ) =
        ∑ j : Fin (n+1),(P.coeff i.val*P.coeff j.val)*moment μ (i.val+j.val) := by
      rw [integral_finsetSum _ (fun j _ => hI i.val j.val)]
      simp only [integral_const_mul,moment]
    simp only [hinner,mulVec,dotProduct,mul_sum]
    refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ?_))
    change P.coeff i.val * d i * (moment μ (i.val+j.val)/(d i*d j)*(P.coeff j.val*d j)) =
      P.coeff i.val*P.coeff j.val*moment μ (i.val+j.val)
    field_simp [hdpos]
  obtain ⟨i,hi⟩ := rayleigh_min _ (gram_herm μ (n+1)) z
  exact ⟨i,hsq ▸ hquad ▸ hi⟩

private lemma compact_test (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : ∀ k : ℕ,Integrable (fun x : ℝ => x^k) μ)
    (hp : ∀ k,0 < moment μ (2*k)) (hs : ∀ᵐ x ∂μ, |x|≤1) (n : ℕ) :
    ∃ i : Fin (n+1), (gram_herm μ (n+1)).eigenvalues i ≤
      1/((4:ℝ)^(n-1)*moment μ (2*n)) := by
  let P := Chebyshev.T ℝ (n:ℤ)
  have hdeg : P.natDegree=n := by simp [P]
  have hcoeff : P.coeff n=(2:ℝ)^(n-1) := by
    rw [← hdeg,← Polynomial.leadingCoeff, hdeg]
    simp [P]
  obtain ⟨i,hi⟩ := trial_vector μ hm hp P n hdeg.le
  refine ⟨i,?_⟩
  have hI : (∫ x,P.eval x^2 ∂μ)≤1 := by
    have hle : (fun x => P.eval x^2) ≤ᵐ[μ] (fun _ => (1:ℝ)) := by
      filter_upwards [hs] with x hx
      have hh := Chebyshev.abs_eval_T_real_le_one (n:ℤ) hx
      change (Chebyshev.T ℝ (n:ℤ)).eval x^2≤1
      simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) hh 2
    have hpos : 0≤ᵐ[μ] (fun x => P.eval x^2) := Filter.Eventually.of_forall (fun x => sq_nonneg _)
    simpa using integral_mono_of_nonneg hpos (integrable_const (1:ℝ)) hle
  have hs2 : (4:ℝ)^(n-1)*moment μ (2*n)≤∑ j : Fin (n+1),(P.coeff j.val)^2*moment μ (2*j.val) := by
    have h := single_le_sum (s:=Finset.univ)
      (f:=fun j : Fin (n+1) => (P.coeff j.val)^2*moment μ (2*j.val))
      (fun j _ => mul_nonneg (sq_nonneg _) (hp _).le) (mem_univ (Fin.last n))
    have hpow (k : ℕ) : ((2:ℝ)^k)^2=4^k := by
      rw [← pow_mul,mul_comm,pow_mul]
      norm_num
    simpa only [Fin.val_last,hcoeff,hpow] using h
  have hden := mul_pos (pow_pos (by norm_num : (0:ℝ)<4) (n-1)) (hp n)
  by_cases he : 0≤(gram_herm μ (n+1)).eigenvalues i
  · exact (le_div_iff₀ hden).mpr ((mul_le_mul_of_nonneg_left hs2 he).trans (hi.trans hI))
  · exact (lt_of_not_ge he).le.trans (div_nonneg zero_le_one hden.le)

open Polynomial
private lemma uniform_prob : IsProbabilityMeasure symmetricUniform := by
  constructor
  norm_num [symmetricUniform,Measure.smul_apply,Real.volume_Ioc]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

private lemma uniform_bound (n : ℕ) :
    ∃ i : Fin (n+1), (gram_herm symmetricUniform (n+1)).eigenvalues i ≤
      (2*(n:ℝ)+1)/(4:ℝ)^(n-1) := by
  let := uniform_prob
  have hm (k : ℕ) : Integrable (fun x : ℝ => x^k) symmetricUniform := by
    apply Integrable.smul_measure _ (by norm_num : (2:ENNReal)⁻¹≠⊤)
    exact (continuous_pow k).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hs : ∀ᵐ x ∂symmetricUniform, |x|≤1 := by
    apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioc (a:=(-1:ℝ)) (b:=1))]
      with x hx
    exact abs_le.mpr ⟨hx.1.le,hx.2⟩
  have he (k : ℕ) : moment symmetricUniform (2*k)=1/(2*(k:ℝ)+1) := by
    rw [moment,symmetricUniform,integral_smul_measure,
      ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1), integral_pow]
    simp [pow_succ,pow_mul,smul_eq_mul]
    ring
  obtain ⟨i,hi⟩ := compact_test symmetricUniform hm (fun k => by rw [he]; positivity) hs n
  refine ⟨i,hi.trans_eq ?_⟩
  rw [he]
  field_simp

open Polynomial
private noncomputable abbrev normalLaw := gaussianReal 0 1
private lemma gauss_int (k : ℕ) : Integrable (fun x : ℝ => x^k) normalLaw :=
  integrable_pow_of_mem_interior_integrableExpSet (X:=fun x : ℝ => x) (by simp) k

private lemma gauss_rec (k : ℕ) : moment normalLaw (k+2)=(k+1:ℕ)*moment normalLaw k := by
  let F := fun t : ℝ => Real.exp (t^2/2)
  have hD (t : ℝ) : HasDerivAt F (t*F t) t := by
    convert (((hasDerivAt_id t).pow 2).div_const 2).exp using 1 <;> simp [F]
    ring
  have hmg : mgf (fun x : ℝ => x) normalLaw=F := by simp [F,mgf_fun_id_gaussianReal]
  have hm (s : ℕ) : iteratedDeriv s F 0=moment normalLaw s := by
    rw [← hmg]
    exact iteratedDeriv_mgf_zero (X:=fun x : ℝ => x) (μ:=normalLaw) (by simp) s
  rw [← hm,← hm,iteratedDeriv_succ',show deriv F=(fun x : ℝ => x^1)*F by
    funext x; simp [Pi.mul_apply,(hD x).deriv]]
  rw [iteratedDeriv_mul (by fun_prop) (by dsimp [F]; fun_prop)]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro j _ hj
    have hz : iteratedDeriv j (fun x : ℝ => x^1) 0=0 := by
      rw [iteratedDeriv_pow]
      rcases j with _|j
      · simp
      · have hj' : 1<j+1 := by omega
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr hj',Nat.cast_zero,zero_mul]
    rw [hz,mul_zero,zero_mul]
  · simp

private noncomputable def expectation (P : ℝ[X]) : ℝ := ∫ x,P.eval x ∂normalLaw

private lemma poly_int (P : ℝ[X]) : Integrable (fun x : ℝ => P.eval x) normalLaw := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq =>
    rw [show (fun x : ℝ => (P+Q).eval x) = (fun x => P.eval x)+(fun x => Q.eval x) by
      funext x; exact eval_add]
    exact hp.add hq
  | monomial k a => simpa only [eval_monomial] using (gauss_int k).const_mul a

private lemma expectation_add (P Q : ℝ[X]) : expectation (P+Q)=expectation P+expectation Q := by
  simp [expectation,integral_add (poly_int P) (poly_int Q)]

private lemma expectation_sub (P Q : ℝ[X]) : expectation (P-Q)=expectation P-expectation Q := by
  simp [expectation,integral_sub (poly_int P) (poly_int Q)]

private lemma stein (P : ℝ[X]) : expectation (X*P)=expectation P.derivative := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => rw [mul_add,derivative_add,expectation_add,expectation_add,hp,hq]
  | monomial k a =>
    cases k with
    | zero =>
      simp [expectation]
      rw [integral_const_mul,integral_id_gaussianReal,mul_zero]
    | succ k =>
      simp only [derivative_monomial,expectation,eval_monomial,eval_mul,eval_X,Nat.succ_sub_one]
      have hr := gauss_rec k
      have hi : (fun x : ℝ => x*(a*x^(k+1)))=fun x => a*x^(k+2) := by funext x; ring
      rw [hi,integral_const_mul,integral_const_mul]
      change a*moment normalLaw (k+2)=_ * moment normalLaw k
      rw [hr]
      push_cast
      ring

private noncomputable def herm (n : ℕ) : ℝ[X] := (Polynomial.hermite n).map (Int.castRingHom ℝ)
private lemma gaussian_pairing (n : ℕ) (P : ℝ[X]) :
    expectation (herm n*P)=expectation (derivative^[n] P) := by
  induction n generalizing P with
  | zero => simp [herm,hermite_zero]
  | succ n ih =>
    have he : herm (n+1)=X*herm n-(herm n).derivative := by
      simp [herm,hermite_succ,Polynomial.derivative_map]
    have hs := stein (herm n*P)
    rw [derivative_mul,expectation_add] at hs
    rw [he,sub_mul,expectation_sub,mul_assoc,hs,Function.iterate_succ_apply,← ih]
    ring

private lemma herm_norm (n : ℕ) : expectation (herm n*herm n)=n.factorial := by
  rw [gaussian_pairing]
  have hc : derivative^[n] (herm n)=C (n.factorial:ℝ) := by
    ext j
    rw [coeff_iterate_derivative]
    cases j with
    | zero => simp [herm,coeff_hermite_self,Nat.descFactorial_self]
    | succ j =>
      have hj : n<j+1+n := by omega
      simp [herm,coeff_hermite_of_lt hj]
  simp [hc,expectation]

open Polynomial
private lemma normal_even_pos (n : ℕ) : 0 < moment normalLaw (2*n) := by
  induction n with
  | zero => simp [moment]
  | succ n ih =>
    rw [Nat.mul_succ,gauss_rec]
    exact mul_pos (by positivity) ih

private lemma gaussian_bound (n : ℕ) :
    ∃ i : Fin (n+1), (gram_herm normalLaw (n+1)).eigenvalues i ≤
      ((n:ℝ)+1)/(2:ℝ)^n := by
  have hn : (herm n).natDegree=n := by
    rw [herm,(hermite_monic n).natDegree_map, natDegree_hermite]
  have hc : (herm n).coeff n=1 := by simp [herm,coeff_hermite_self]
  obtain ⟨i,hi⟩ := trial_vector normalLaw gauss_int normal_even_pos (herm n) n hn.le
  have he : (∫ x,(herm n).eval x^2 ∂normalLaw) = n.factorial := by
    simpa [expectation,pow_two] using herm_norm n
  rw [he] at hi
  refine ⟨i,?_⟩
  by_cases hg : 0≤(gram_herm normalLaw (n+1)).eigenvalues i
  · have hs := single_le_sum (s:=Finset.univ)
      (f:=fun j : Fin (n+1) => ((herm n).coeff j.val)^2*moment normalLaw (2*j.val))
      (fun j _ => mul_nonneg (sq_nonneg _) (normal_even_pos _).le) (mem_univ (Fin.last n))
    simp only [Fin.val_last,hc,one_pow,one_mul] at hs
    have hquot (k : ℕ) :
        (k.factorial:ℝ)*2^k ≤ ((k:ℝ)+1)*moment normalLaw (2*k) := by
      induction k with
      | zero => simp [moment]
      | succ k ih =>
        rw [Nat.factorial_succ, Nat.cast_mul,pow_succ,Nat.mul_succ,gauss_rec]
        push_cast
        have hnum : (2:ℝ)*(k+1)^2≤(k+2)*(2*k+1) := by nlinarith [Nat.cast_nonneg (α:=ℝ) k]
        calc ((k:ℝ)+1)*k.factorial*(2^k*2) = (2*(k+1))*(k.factorial*2^k) := by ring
             _ ≤ (2*(k+1))*((k+1)*moment normalLaw (2*k)) :=
               mul_le_mul_of_nonneg_left ih (by positivity)
             _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hnum (normal_even_pos k).le]
    have hx := (mul_le_mul_of_nonneg_left hs hg).trans hi
    apply (le_div_iff₀ (by positivity)).mpr
    apply (le_of_mul_le_mul_right · (normal_even_pos n))
    calc _ = ((gram_herm normalLaw (n+1)).eigenvalues i*moment normalLaw (2*n))*2^n := by ring
         _ ≤ (n.factorial:ℝ)*2^n := mul_le_mul_of_nonneg_right hx (by positivity)
         _ ≤ _ := hquot n
  · exact (lt_of_not_ge hg).le.trans (by positivity)

private lemma answer : type_of% @OMA.S_mo_299643.main := by
  have hprob : IsProbabilityMeasure lognormal :=
    Measure.isProbabilityMeasure_map Real.measurable_exp.aemeasurable
  exact ⟨⟨hprob,lognormal_ac,lognormal_integrable,lognormal_gram,lognormal_gap⟩,
    uniform_bound,gaussian_bound,fun _ hn A ha hdiag => trace_estimates hn A ha hdiag⟩
end OMA.S_mo_299643
open OMA.S_mo_299643 in
theorem OMA.solution : type_of% @OMA.S_mo_299643.main := answer

