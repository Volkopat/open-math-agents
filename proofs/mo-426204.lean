import OMAStatements.S_mo_426204

/-!
The normalized Hankel entries are binomial(i+j,j)². They form the Gram
matrix for powers of (1+z)(1+w) on the two-dimensional unit torus.
Real polynomials approximate the continuous resolvents of this symbol.
Their norm tends to zero in L², while their value at the zero of the
symbol stays one. A rank-one determinant identity then identifies the
unique corner entry and gives its limit.

Question: https://mathoverflow.net/questions/426204
-/

namespace OMA.S_mo_426204
open Set Filter Topology Polynomial
open scoped NNReal

/-- Inverting the pencil 1+tA along the nonnegative real axis stays in the uniform
closure of the real polynomials in A, as long as its ambient inverse is continuous. -/
theorem closure_resolvent {B : Type*} [NormedCommRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
    (A : B) (R : ℝ≥0 → B) (hR : Continuous R) (hinv : ∀ t : ℝ≥0, (1+(t:ℝ) • A) * R t = 1)
    (t : ℝ≥0) : R t ∈ (Algebra.adjoin ℝ ({A} : Set B)).topologicalClosure := by
  let S := (Algebra.adjoin ℝ ({A} : Set B)).topologicalClosure
  have hc : IsClosed (S : Set B) := isClosed_closure
  let : CompleteSpace S := hc.completeSpace_coe
  have ha : A ∈ S := subset_closure (Algebra.subset_adjoin (mem_singleton A))
  let c : ℝ≥0 → S := fun s => 1+(s:ℝ) • (⟨A,ha⟩ : S)
  have ccont : Continuous c := by dsimp [c]; fun_prop
  have heq (s : ℝ≥0) : IsUnit (c s) ↔ R s ∈ S := by
    constructor
    · rintro ⟨u,hu⟩
      have he : R s = ((↑(u⁻¹) : S) : B) := by
        have hmul : ((c s : S) : B) * ((↑(u⁻¹) : S) : B) = 1 := by
          rw [← hu, ← Subalgebra.coe_mul]
          simp
        have hcs : ((c s : S) : B) * R s = 1 := hinv s
        calc R s = R s * (((c s:S):B) * ((↑(u⁻¹):S):B)) := by rw [hmul,mul_one]
             _ = ((↑(u⁻¹):S):B) := by rw [←mul_assoc,mul_comm (R s),hcs,one_mul]
      exact he ▸ (↑(u⁻¹) : S).property
    · intro h
      exact IsUnit.of_mul_eq_one (⟨R s,h⟩ : S) (Subtype.ext (hinv s))
  have hset : {s : ℝ≥0 | IsUnit (c s)} = R ⁻¹' (S : Set B) := Set.ext heq
  have ho : IsOpen {s : ℝ≥0 | IsUnit (c s)} := Units.isOpen.preimage ccont
  have hcl : IsClopen {s : ℝ≥0 | IsUnit (c s)} := ⟨hset ▸ hc.preimage hR, ho⟩
  have hzero : IsUnit (c 0) := by
    have he : c 0 = 1 := by apply Subtype.ext; simp [c]
    rw [he]
    exact isUnit_one
  have hall := hcl.eq_univ ⟨0,hzero⟩
  exact (heq t).mp (show t ∈ {s : ℝ≥0 | IsUnit (c s)} from hall ▸ mem_univ t)

end OMA.S_mo_426204

namespace OMA.S_mo_426204

open MeasureTheory Complex
open scoped NNReal ComplexConjugate

abbrev Phase := AddCircle (1 : ℝ)
abbrev Torus := Phase × Phase
noncomputable abbrev circleProb : Measure Phase := AddCircle.haarAddCircle
noncomputable abbrev torusProb : Measure Torus := circleProb.prod circleProb

noncomputable def zeta : C(Phase,ℂ) := fourier 1

theorem norm_zeta (x : Phase) : ‖zeta x‖ = 1 := by rw [zeta, fourier_one]; exact Circle.norm_coe _

noncomputable def symbol : C(Torus,ℂ) :=
  ⟨fun x => (1+zeta x.1)*(1+zeta x.2), by fun_prop⟩

theorem re_one_add_zeta (x : Phase) : 0 ≤ (1+ zeta x).re := by
  have := (zeta x).abs_re_le_norm
  rw [norm_zeta, abs_le] at this
  simp only [add_re, one_re]
  linarith

theorem norm_lt_one_add {u : ℂ} (hu : 0 ≤ u.re) : ‖u‖ < ‖1+u‖ := by
  have he : ‖1+u‖^2 = 1+‖u‖^2+2*u.re := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
    simp
  nlinarith [norm_nonneg u, norm_nonneg (1+u)]

theorem symbol_denom_ne (t : ℝ≥0) (x : Torus) : 1+((t:ℝ):ℂ)*symbol x ≠ 0 := by
  let u : ℂ := (t:ℝ)*(1+zeta x.1)
  have hu : 0 ≤ u.re := by
    change 0 ≤ (((t:ℝ):ℂ)*(1+zeta x.1)).re
    simpa using mul_nonneg t.coe_nonneg (re_one_add_zeta x.1)
  have he : ‖u*zeta x.2‖ < ‖1+u‖ := by simpa [norm_mul, norm_zeta] using norm_lt_one_add hu
  intro h
  have hh : 1+u = -(u*zeta x.2) := by
    dsimp [u]
    change 1 + ((t:ℝ):ℂ)*((1+zeta x.1)*(1+zeta x.2)) = 0 at h
    linear_combination h
  rw [hh, norm_neg] at he
  exact lt_irrefl _ he

noncomputable def torusResolvent (t : ℝ≥0) : C(Torus,ℂ) :=
  ⟨fun x => (1+((t:ℝ):ℂ)*symbol x)⁻¹, (continuous_const.add (continuous_const.mul symbol.continuous)).inv₀ (symbol_denom_ne t)⟩

theorem continuous_torusResolvent : Continuous torusResolvent := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ≥0 × Torus => (1 + ((p.1:ℝ):ℂ)*symbol p.2)⁻¹)
  have h : Continuous (fun p : ℝ≥0 × Torus => 1 + ((p.1:ℝ):ℂ)*symbol p.2) := by fun_prop
  exact h.inv₀ (fun p => symbol_denom_ne p.1 p.2)

theorem torusResolvent_mul (t : ℝ≥0) :
    (1 + (t:ℝ) • symbol) * torusResolvent t = 1 := by
  ext x
  change (1+((t:ℝ):ℂ)*symbol x)*(1+((t:ℝ):ℂ)*symbol x)⁻¹ = 1
  exact mul_inv_cancel₀ (symbol_denom_ne t x)

end OMA.S_mo_426204

namespace OMA.S_mo_426204

open MeasureTheory Complex Finset Polynomial
open scoped ComplexConjugate

private lemma zeta_pow (x : Phase) (n : ℕ) : zeta x ^ n = fourier (n:ℤ) x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Nat.cast_succ, fourier_add]; rfl

theorem circle_orth (i j : ℕ) :
    ∫ z, zeta z ^ i * conj (zeta z ^ j) ∂circleProb = if j=i then 1 else 0 := by
  have ho := orthonormal_iff_ite.mp (orthonormal_fourier (T := 1)) (j:ℤ) (i:ℤ)
  rw [ContinuousMap.inner_toLp circleProb (fourier (j:ℤ)) (fourier (i:ℤ))] at ho
  simpa only [zeta_pow, Int.natCast_inj] using ho

theorem circle_moment (i j : ℕ) :
    ∫ z, (1+zeta z)^i * conj ((1+zeta z)^j) ∂circleProb = ((i+j).choose j : ℂ) := by
  let N := i+j
  have hx (z : Phase) : (1+zeta z)^i * conj ((1+zeta z)^j) =
      ∑ k ∈ range (N+1), ((N.choose k : ℕ):ℂ)*(zeta z^k * conj (zeta z^j)) := by
    have hz : zeta z * conj (zeta z) = 1 := by simp [Complex.mul_conj', norm_zeta]
    have h1 : conj (1+zeta z) = (1+zeta z)*conj (zeta z) := by
      rw [map_add, map_one, add_mul, one_mul, hz, add_comm]
    rw [map_pow, h1, mul_pow, ←mul_assoc, ←pow_add, ←map_pow]
    rw [add_comm (1:ℂ), add_pow, sum_mul]
    apply sum_congr rfl
    intro k hk
    simp
    ring
  simp_rw [hx]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, circle_orth]
    simp [N, mul_ite]
  · intro k hk
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop

theorem torus_moment (i j : ℕ) :
    ∫ z, symbol z ^ i * conj (symbol z ^ j) ∂torusProb = ((i+j).choose j : ℂ)^2 := by
  let f : Phase → ℂ := fun x => (1+zeta x)^i * conj ((1+zeta x)^j)
  have hp (z : Torus) : symbol z ^ i * conj (symbol z ^ j) = f z.1 * f z.2 := by
    simp only [symbol, ContinuousMap.coe_mk, mul_pow,map_mul,f]
    ring
  simp_rw [hp]
  rw [integral_prod_mul]
  change (∫ x, (1+zeta x)^i * conj ((1+zeta x)^j) ∂circleProb) * _ = _
  change (∫ x, (1+zeta x)^i * conj ((1+zeta x)^j) ∂circleProb) *
    (∫ x, (1+zeta x)^i * conj ((1+zeta x)^j) ∂circleProb) = _
  rw [circle_moment, pow_two]

end OMA.S_mo_426204

namespace OMA.S_mo_426204

open MeasureTheory Set Filter Complex
open scoped NNReal Topology ComplexConjugate

private lemma pow_mean (n : ℕ) : ∫ w, zeta w ^ n ∂circleProb = if n=0 then 1 else 0 := by
  have hw (x : Phase) : zeta x ^ n = fourier (n:ℤ) x := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, Nat.cast_succ, fourier_add]; rfl
  have h := congrFun (fourierCoeff_fourier (T := 1) (n:ℤ)) 0
  simpa [fourierCoeff,hw,Pi.single_apply,eq_comm] using h

private lemma circle_geometric_mean (c : ℂ) (hc : ‖c‖ < 1) :
    ∫ w, (1+c*zeta w)⁻¹ ∂circleProb = 1 := by
  let F (n : ℕ) (w : Phase) := (-c)^n*zeta w^n
  have hi (n : ℕ) : Integrable (F n) circleProb := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    dsimp [F]
    fun_prop
  have hs : Summable (fun n => ∫ w, ‖F n w‖ ∂circleProb) := by
    simp only [F,norm_mul,norm_pow,norm_neg,norm_zeta,one_pow,mul_one,integral_const,
      probReal_univ,one_smul]
    exact summable_geometric_of_lt_one (norm_nonneg _) hc
  have hv (w : Phase) : ∑' n : ℕ, F n w = (1+c*zeta w)⁻¹ := by
    simp only [F, ← mul_pow]
    rw [tsum_geometric_of_norm_lt_one (by simpa [norm_mul,norm_zeta] using hc)]
    ring_nf
  have he := integral_tsum_of_summable_integral_norm hi hs
  simp only [hv] at he
  rw [← he]
  simp only [F, integral_const_mul,pow_mean,mul_ite,mul_one,mul_zero]
  simp

private lemma spectral_identity (b : ℂ) (hb : 1+b ≠ 0) :
    (1-‖b‖^2)*‖(1+b)⁻¹‖^2 = 2*((1+b)⁻¹).re-1 := by
  have h0 : Complex.normSq (1+b) ≠ 0 := by simpa using hb
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_inv, Complex.inv_re]
  field_simp [h0]
  rw [Complex.normSq_add]
  simp
  ring

private lemma circle_geometric_energy (c : ℂ) (hc : ‖c‖ < 1) :
    ∫ w, ‖(1+c*zeta w)⁻¹‖^2 ∂circleProb = (1-‖c‖^2)⁻¹ := by
  have h0 (w : Phase) : 1+c*zeta w ≠ 0 := by
    intro hz
    have h : c*zeta w = -1 := by linear_combination hz
    have h' := congrArg norm h
    simp [norm_zeta] at h'
    linarith
  let f (w : Phase) := (1+c*zeta w)⁻¹
  have hf : Continuous f := (continuous_const.add (continuous_const.mul zeta.continuous)).inv₀ h0
  have hi : Integrable f circleProb :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (w : Phase) : (1-‖c‖^2)*‖f w‖^2 = 2*(f w).re-1 := by
    simpa [f,norm_mul,norm_zeta] using spectral_identity (c*zeta w) (h0 w)
  have hre : ∫ w, (f w).re ∂circleProb = 1 := by
    rw [show (fun w => (f w).re) = (fun w => RCLike.re (f w)) from rfl, integral_re hi]
    simp [f,circle_geometric_mean c hc]
  have hle : 0 < 1-‖c‖^2 := by nlinarith [mul_pos (sub_pos.mpr hc) (show 0 < 1+‖c‖ by positivity)]
  apply mul_left_cancel₀ hle.ne'
  rw [mul_inv_cancel₀ hle.ne', ←integral_const_mul]
  change (∫ w, (1-‖c‖^2)*‖f w‖^2 ∂circleProb) = 1
  simp_rw [he]
  rw [integral_sub, integral_const_mul, hre]
  · norm_num
  · exact hi.re.const_mul _
  · exact integrable_const _

private lemma inner_integral (t : ℝ≥0) (z : Phase) :
    ∫ w, ‖torusResolvent t (z,w)‖^2 ∂circleProb = (1+2*(t:ℝ)*(1+zeta z).re)⁻¹ := by
  let u : ℂ := (t:ℝ)*(1+zeta z)
  let b : ℂ := 1+u
  have ure : u.re = (t:ℝ)*(1+zeta z).re := by simp [u]
  have hu : 0 ≤ u.re := ure ▸ mul_nonneg t.coe_nonneg (re_one_add_zeta z)
  have hlt : ‖u‖ < ‖b‖ := norm_lt_one_add hu
  have hb : 0 < ‖b‖ := (norm_nonneg u).trans_lt hlt
  have hb0 := (norm_pos_iff.mp hb)
  have hc : ‖u/b‖ < 1 := by rw [norm_div,div_lt_one hb]; exact hlt
  have hdiff : ‖b‖^2 - ‖u‖^2 = 1+2*u.re := by
    simp only [b, ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
    simp
    ring
  have hdpos : 0 < ‖b‖^2 - ‖u‖^2 := by rw [hdiff]; linarith
  have he (w : Phase) : ‖torusResolvent t (z,w)‖^2 =
      (‖b‖^2)⁻¹ * ‖(1+(u/b)*zeta w)⁻¹‖^2 := by
    have hm : 1+((t:ℝ):ℂ)*symbol (z,w) = b * (1+(u/b)*zeta w) := by
      change 1+((t:ℝ):ℂ)*((1+zeta z)*(1+zeta w)) = _
      dsimp [b,u] at *
      field_simp
      ring
    change ‖(1+((t:ℝ):ℂ)*symbol (z,w))⁻¹‖^2 = _
    rw [hm,mul_inv_rev,norm_mul,mul_pow]
    simp [norm_inv,mul_comm]
  simp_rw [he]
  rw [integral_const_mul, circle_geometric_energy (u/b) hc, norm_div, div_pow, mul_assoc 2 (t:ℝ), ←ure, ←hdiff]
  field_simp

private lemma almost_pos : ∀ᵐ z ∂circleProb, 0 < (1+zeta z).re := by
  have : Infinite Phase := (AddCircle.equivIco 1 0).infinite_iff.mpr
    (Set.infinite_coe_iff.mpr (Set.Ico_infinite (by norm_num)))
  have : (𝓝[≠] (0:Phase)).NeBot := by
    by_contra hc
    rw [not_neBot, ← isOpen_singleton_iff_punctured_nhds] at hc
    have he := (show IsClopen ({0} : Set Phase) from ⟨isClosed_singleton,hc⟩).eq_univ (singleton_nonempty _)
    obtain ⟨w,hw⟩ := exists_ne (0:Phase)
    exact hw (show w ∈ ({0} : Set Phase) from he ▸ mem_univ w)
  rw [ae_iff]
  apply Set.Subsingleton.measure_zero
  have hz (w : Phase) (hw : ¬ 0 < (1+zeta w).re) : zeta w = -1 := by
    have hh := re_one_add_zeta w
    have h1 : (zeta w).re = -1 := by simp only [add_re,one_re] at hh hw; linarith
    have h2 := Complex.normSq_eq_norm_sq (zeta w)
    rw [Complex.normSq_apply,h1,norm_zeta] at h2
    apply Complex.ext
    · simp [h1]
    · simp
      nlinarith
  intro v hv w hw
  apply AddCircle.injective_toCircle one_ne_zero
  apply Subtype.ext
  simpa [zeta,fourier_one] using (hz v hv).trans (hz w hw).symm

theorem resolvent_energy_tendsto :
    Tendsto (fun n : ℕ => ∫ z, ‖torusResolvent (n:ℝ≥0) z‖^2 ∂torusProb) atTop (𝓝 0) := by
  let F (n : ℕ) (z : Phase) := (1+2*(n:ℝ)*(1+zeta z).re)⁻¹
  have he (n : ℕ) : (∫ z, ‖torusResolvent (n:ℝ≥0) z‖^2 ∂torusProb) =
      ∫ z, F n z ∂circleProb := by
    rw [MeasureTheory.integral_prod]
    · simp only [inner_integral, NNReal.coe_natCast,F]
    · apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      fun_prop
  simp_rw [he]
  have hpos (n : ℕ) (z : Phase) : 0 ≤ 2*(n:ℝ)*(1+zeta z).re := by
    exact mul_nonneg (by positivity) (re_one_add_zeta _)
  have hc (n : ℕ) : Continuous (F n) := by
    apply Continuous.inv₀ (by fun_prop) (fun z => by have := hpos n z; linarith)
  have hdom (n : ℕ) : ∀ᵐ z ∂circleProb, ‖F n z‖ ≤ 1 := by
    filter_upwards with z
    have hh := hpos n z
    change ‖(1+2*(n:ℝ)*(1+zeta z).re)⁻¹‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hlim : ∀ᵐ z ∂circleProb, Tendsto (fun n => F n z) atTop (𝓝 0) := by
    filter_upwards [almost_pos] with z hz
    have hp : 0 < 2*(1+zeta z).re := by positivity
    have h : Tendsto (fun n : ℕ => 1 + (2*(1+zeta z).re)*(n:ℝ)) atTop atTop :=
      tendsto_const_nhds.add_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop hp)
    simpa [F,Function.comp_def,mul_assoc,mul_left_comm,mul_comm] using tendsto_inv_atTop_zero.comp h
  simpa using tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
    (fun n => (hc n).aestronglyMeasurable) (integrable_const _)
    hdom (f := fun _ => (0:ℝ)) hlim

end OMA.S_mo_426204

namespace OMA.S_mo_426204

open MeasureTheory Complex Polynomial Set Filter
open scoped Topology NNReal ComplexConjugate InnerProductSpace

noncomputable def energy (f : C(Torus,ℂ)) : ℝ := ∫ x, ‖f x‖^2 ∂torusProb

theorem energy_nonneg (f : C(Torus,ℂ)) : 0 ≤ energy f := integral_nonneg (fun _ => sq_nonneg _)

theorem continuous_energy : Continuous energy := by
  let L := ContinuousMap.toLp 2 torusProb ℂ (E := ℂ)
  have he (f : C(Torus,ℂ)) : energy f = ‖L f‖^2 := by
    apply Complex.ofReal_injective
    have h := ContinuousMap.inner_toLp torusProb f f
    rw [inner_self_eq_norm_sq_to_K] at h
    simpa only [L,energy,← integral_complex_ofReal,Complex.ofReal_pow,Complex.mul_conj'] using! h.symm
  simp_rw [show energy = fun f => ‖L f‖^2 from funext he]
  exact L.continuous.norm.pow 2

/-- A small-norm polynomial with constant coefficient exactly one. -/
theorem small_polynomial
    (hlim : Tendsto (fun n : ℕ => energy (torusResolvent (n:ℝ≥0))) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℝ[X], p.coeff 0 = 1 ∧ energy (aeval symbol p) < ε := by
  obtain ⟨n,hn⟩ := (hlim.eventually_lt_const hε).exists
  let t : ℝ≥0 := n
  let R := torusResolvent t
  have hr : R ∈ closure (Algebra.adjoin ℝ ({symbol} : Set C(Torus,ℂ)) : Set C(Torus,ℂ)) :=
    closure_resolvent symbol _ continuous_torusResolvent torusResolvent_mul t
  let f (g : C(Torus,ℂ)) := 1 - algebraMap ℝ C(Torus,ℂ) (t:ℝ) * (symbol*g)
  have hinv : f R = R := by
    ext z
    change 1-((t:ℝ):ℂ)*(symbol z*(1+((t:ℝ):ℂ)*symbol z)⁻¹) = (1+((t:ℝ):ℂ)*symbol z)⁻¹
    field_simp [symbol_denom_ne t z]
    ring
  have hop : IsOpen {g | energy (f g) < ε} :=
    isOpen_lt (continuous_energy.comp (by dsimp [f]; fun_prop)) continuous_const
  have hm : R ∈ {g | energy (f g) < ε} := by simpa [hinv,R,t] using hn
  obtain ⟨g,hgsmall,hg⟩ := (mem_closure_iff.mp hr) _ hop hm
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hg
  obtain ⟨p,rfl⟩ := hg
  refine ⟨1-C (t:ℝ)*X*p, by simp, ?_⟩
  change energy (f (aeval symbol p)) < ε at hgsmall
  have ee : aeval symbol (1-C (t:ℝ)*X*p) = f (aeval symbol p) := by
    dsimp only [f]
    simp only [map_sub,map_one,map_mul,aeval_C,aeval_X,mul_assoc]
  rwa [ee]

end OMA.S_mo_426204

namespace OMA.S_mo_426204

open MeasureTheory Complex Polynomial Finset Set Matrix
open scoped ComplexConjugate

private def scale (i : ℕ) : ℝ := (i.factorial:ℝ)^2

noncomputable def vecPoly {n : ℕ} (c : Fin (n+1) → ℝ) : ℝ[X] :=
  ∑ i, monomial i.val (c i * scale i.val)

private lemma hentry (n : ℕ) (i j : Fin (n+1)) :
    hankel n 1 i j = ((i.val+j.val).factorial:ℝ)^2 := by
  change (if i.val+j.val=0 then 1 else _) = _
  split <;> simp_all

private lemma eval_vecPoly {n : ℕ} (c : Fin (n+1) → ℝ) (z : Torus) :
    (aeval symbol (vecPoly c)) z = ∑ i, ((c i * scale i.val:ℝ):ℂ) * symbol z^i.val := by
  simp [vecPoly, aeval_monomial, Algebra.algebraMap_eq_smul_one]

theorem energy_vecPoly {n : ℕ} (c : Fin (n+1) → ℝ) :
    (∫ z, ‖(aeval symbol (vecPoly c)) z‖^2 ∂torusProb) = c ⬝ᵥ ((hankel n 1) *ᵥ c) := by
  let d (i : Fin (n+1)) : ℂ := ((c i*scale i.val:ℝ):ℂ)
  let f (i j : Fin (n+1)) (z : Torus) := d i*d j * (symbol z^i.val * conj (symbol z^j.val))
  have he (z : Torus) : ((‖(aeval symbol (vecPoly c)) z‖^2:ℝ):ℂ) = ∑ i, ∑ j, f i j z := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', eval_vecPoly]
    simp only [map_sum,map_mul,Complex.conj_ofReal, sum_mul,mul_sum]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    dsimp [f,d]
    ring
  have hi (i j : Fin (n+1)) : Integrable (f i j) torusProb := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    dsimp [f]
    fun_prop
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [he]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
  simp_rw [integral_finsetSum _ fun j _ => hi _ j]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.ofReal_sum, Complex.ofReal_mul]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  change (∫ z, d i*d j * (symbol z^i.val * conj (symbol z^j.val)) ∂torusProb) = _
  rw [integral_const_mul, torus_moment, hentry]
  have hc : ((i.val+j.val).choose j.val : ℂ) * (j.val.factorial:ℂ) * (i.val.factorial:ℂ) =
      ((i.val+j.val).factorial:ℂ) := by
    exact_mod_cast (by simpa using (Nat.choose_mul_factorial_mul_factorial
      (show j.val ≤ i.val+j.val by omega)))
  simp only [d,scale,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,←hc]
  ring

private lemma symbol_infinite : (Set.range symbol).Infinite := by
  have : Infinite Phase := (AddCircle.equivIco 1 0).infinite_iff.mpr
    (Set.infinite_coe_iff.mpr (Set.Ico_infinite (by norm_num)))
  let f (w : Phase) := symbol (w,0)
  have hinj : Function.Injective f := by
    intro u v h
    change (1+zeta u)*(1+zeta 0) = (1+zeta v)*(1+zeta 0) at h
    have hz : zeta 0 = 1 := fourier_eval_zero _
    rw [hz] at h
    have h' : zeta u = zeta v := by linear_combination (1/2:ℂ)*h
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    simpa [zeta, fourier_one] using h'
  exact (Set.infinite_range_of_injective hinj).mono (by rintro _ ⟨v,rfl⟩; exact ⟨(v,0),rfl⟩)

private lemma coefficient_vec {n : ℕ} (c : Fin (n+1) → ℝ) (j : Fin (n+1)) :
    (vecPoly c).coeff j.val = c j * scale j.val := by
  simp [vecPoly,finsetSum_coeff,coeff_monomial,Fin.val_inj]

theorem factorial_gram_pos (n : ℕ) : (hankel n 1).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp [Matrix.conjTranspose_apply,hentry,add_comm]
  · intro c hc
    rw [star_trivial, ← energy_vecPoly]
    have hi : Integrable (fun z => ‖(aeval symbol (vecPoly c)) z‖^2) torusProb := by
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      fun_prop
    refine lt_of_le_of_ne (integral_nonneg fun _ => sq_nonneg _) ?_
    intro h
    have he := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp h.symm
    have hh := Measure.eq_of_ae_eq he ((aeval symbol (vecPoly c)).continuous.norm.pow 2) continuous_zero
    let p := (vecPoly c).map (algebraMap ℝ ℂ)
    have hr : ∀ z : Torus, p.IsRoot (symbol z) := by
      intro z
      have h0 := congrFun hh z
      have hv : (aeval symbol (vecPoly c)) z = 0 := norm_eq_zero.mp ((sq_eq_zero_iff).mp h0)
      change _ = 0
      simpa [p,eval_map_algebraMap,Polynomial.aeval_algHom,eval_vecPoly,vecPoly,aeval_monomial,
        Algebra.algebraMap_eq_smul_one] using hv
    have hzp : p = 0 := p.eq_zero_of_infinite_isRoot (symbol_infinite.mono (by
      rintro _ ⟨z,rfl⟩; exact hr z))
    have hz : vecPoly c = 0 := (Polynomial.map_injective (algebraMap ℝ ℂ)
      Complex.ofReal_injective) (by simpa [p] using hzp)
    apply hc
    funext j
    have h := coefficient_vec c j
    rw [hz,coeff_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_right (by dsimp [scale]; positivity)

theorem lift_polynomial (p : ℝ[X]) (n : ℕ) (hn : p.natDegree ≤ n) (h0 : p.coeff 0 = 1) :
    ∃ c : Fin (n+1) → ℝ, c 0 = 1 ∧ vecPoly c = p := by
  let c (i : Fin (n+1)) := p.coeff i.val / scale i.val
  refine ⟨c, by simp [c,scale,h0], ?_⟩
  ext k
  by_cases hk : k ≤ n
  · have he := coefficient_vec c (⟨k,by omega⟩ : Fin (n+1))
    have hfac : (k.factorial:ℝ) ≠ 0 := by positivity
    simpa [c,scale,hfac] using he
  · have he : p.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [he]
    simp only [vecPoly,finsetSum_coeff,coeff_monomial]
    apply sum_eq_zero
    intro i _
    simp [show i.val ≠ k by have := i.isLt; omega]

end OMA.S_mo_426204

open Matrix Filter
namespace OMA.S_mo_426204

private lemma corner_formula (n : ℕ) (H : (hankel n 1).PosDef) (x : ℝ) :
    (hankel n x).det = (hankel n 1).det*(1+(x-1)*(hankel n 1)⁻¹ 0 0) := by
  let e : Fin (n+1) → ℝ := Pi.single (0 : Fin (n+1)) (1:ℝ)
  let u : Fin (n+1) → ℝ := Pi.single (0 : Fin (n+1)) (x-1)
  have eqn : hankel n x = hankel n 1 + replicateCol Unit e * replicateRow Unit u := by
    ext i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    all_goals simp [hankel, Matrix.mul_apply, e, u, Pi.single_apply, hi, hj, Matrix.replicateCol,
        Matrix.replicateRow, Nat.add_eq_zero_iff]
  rw [eqn, Matrix.det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr H.det_pos.ne')]
  congr 1
  rw [Matrix.det_unique]
  simp [Matrix.mul_apply, Matrix.replicateRow, Matrix.replicateCol, e, u, Pi.single_apply, mul_ite,
    ite_mul]

private lemma gap_bounds (n : ℕ) (H : (hankel n 1).PosDef) :
    0 < (hankel n 1)⁻¹ 0 0 ∧ ∀ c : Fin (n+1) → ℝ, c 0 = 1 →
        1/(hankel n 1)⁻¹ 0 0 ≤ c ⬝ᵥ ((hankel n 1) *ᵥ c) := by
  let A := hankel n 1
  let e : Fin (n+1) → ℝ := Pi.single (0 : Fin (n+1)) (1:ℝ)
  let v := A⁻¹ *ᵥ e
  have av : A *ᵥ v = e := by
    change A *ᵥ (A⁻¹ *ᵥ e) = e
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr H.det_pos.ne'), Matrix.one_mulVec]
  have vn : v ≠ 0 := by
    intro h
    have ee := congrFun av (0 : Fin (n+1))
    rw [h, Matrix.mulVec_zero] at ee
    simp [e] at ee
  have vd : v 0 = A⁻¹ 0 0 := by simp [v, e]
  have vp : 0 < v 0 := by
    have pos := H.dotProduct_mulVec_pos vn
    change 0 < star v ⬝ᵥ (A *ᵥ v) at pos
    simpa [av, e] using pos
  constructor
  · exact vd ▸ vp
  · intro c hc
    have symmA : A.transpose = A := by ext i j; simp [A, hankel, add_comm, and_comm]
    have vc : v ⬝ᵥ (A *ᵥ c) = 1 := by
      calc
        _ = c ⬝ᵥ (A.transpose *ᵥ v) := (Matrix.dotProduct_transpose_mulVec A c v).symm
        _ = 1 := by rw [symmA, av]; simp [e, hc]
    have zz := H.posSemidef.dotProduct_mulVec_nonneg (v - v 0 • c)
    change 0 ≤ star (v - v 0 • c) ⬝ᵥ (A *ᵥ (v - v 0 • c)) at zz
    simp only [star_trivial, Matrix.mulVec_sub, Matrix.mulVec_smul, av, sub_dotProduct,
      dotProduct_sub, dotProduct_smul, smul_dotProduct, smul_eq_mul, vc, e,
      dotProduct_single_one, Pi.sub_apply, Pi.smul_apply, hc, mul_one] at zz
    change 1 / A⁻¹ 0 0 ≤ c ⬝ᵥ (A *ᵥ c)
    rw [← vd, div_le_iff₀ vp]
    by_contra! h
    nlinarith [mul_pos vp (sub_pos.mpr h)]

theorem solution_of_small_tests
    (pos : ∀ n, (hankel n 1).PosDef)
    (small : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∃ c : Fin (n+1) → ℝ,
      c 0 = 1 ∧ c ⬝ᵥ ((hankel n 1) *ᵥ c) < ε) :
    type_of% @OMA.S_mo_426204.main := by
  refine ⟨fun n => 1 - 1/(hankel n 1)⁻¹ 0 0, ?_, ?_⟩
  · intro n x
    have hp := (gap_bounds n (pos n)).1
    rw [corner_formula n (pos n) x, mul_eq_zero, or_iff_right (pos n).det_pos.ne']
    constructor
    · intro h
      field_simp [hp.ne']
      linarith
    · intro h
      rw [h]
      field_simp [hp.ne']
      ring
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := small ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨c,hc,hq⟩ := hN n hn
    obtain ⟨hp, hl⟩ := gap_bounds n (pos n)
    rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (one_div_pos.mpr hp)]
    exact (hl _ hc).trans_lt hq
end OMA.S_mo_426204

namespace OMA.S_mo_426204
open Matrix Polynomial

theorem small_factorial_test (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ c : Fin (n+1) → ℝ, c 0 = 1 ∧ c ⬝ᵥ ((hankel n 1) *ᵥ c) < ε := by
  obtain ⟨p,h0,hp⟩ := small_polynomial resolvent_energy_tendsto ε hε
  refine ⟨p.natDegree, ?_⟩
  intro n hn
  obtain ⟨c,hc,hv⟩ := lift_polynomial p n hn h0
  refine ⟨c,hc,?_⟩
  rw [← energy_vecPoly,hv]
  exact hp

end OMA.S_mo_426204

theorem OMA.solution : type_of% @OMA.S_mo_426204.main :=
  OMA.S_mo_426204.solution_of_small_tests OMA.S_mo_426204.factorial_gram_pos
    OMA.S_mo_426204.small_factorial_test
