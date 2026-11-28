import OMAReductions.R_Erdos89_erdos_89_R1
import Mathlib

/-! H1 do problema de Erdős nº 89. Crédito pela submissão: @deyvidantonio.

As construções de especialização algébrica e de elemento primitivo foram adaptadas de
OpenAI, OAI/Geometry/UnitDistances/Basic.lean (Apache-2.0), revisão
3344da59991ed94f9ba711217b29c1d760badfa6 de https://github.com/openai/math.
A adaptação preserva igualdades entre comprimentos arbitrários, elimina
denominadores em toda a configuração e compara os mínimos no enunciado de H1.
-/

namespace Especializacao89

namespace PlanarUnitDistances.AlgebraicSpecialization
open Set Filter Polynomial
open scoped Topology

lemma signs_in_nhds {f : ℝ → ℝ} {θ d : ℝ} (hf : HasDerivAt f d θ)
    (hd : d ≠ 0) (hz : f θ = 0) {V : Set ℝ} (hV : V ∈ 𝓝 θ) :
    (∃ a ∈ V, f a < 0) ∧ (∃ b ∈ V, 0 < f b) := by
  constructor
  · by_contra h
    push Not at h
    have hm : IsLocalMin f θ := by
      change ∀ᶠ x in 𝓝 θ, f θ ≤ f x
      exact mem_of_superset hV (fun x hx => by simpa [hz] using h x hx)
    exact hd (hm.hasDerivAt_eq_zero hf)
  · by_contra h
    push Not at h
    have hm : IsLocalMax f θ := by
      change ∀ᶠ x in 𝓝 θ, f x ≤ f θ
      exact mem_of_superset hV (fun x hx => by simpa [hz] using h x hx)
    exact hd (hm.hasDerivAt_eq_zero hf)

theorem dense_parameter_root {A B : Type*} [TopologicalSpace A]
    {φ : B → A} (hφ : DenseRange φ) {F : A × ℝ → ℝ} (hF : Continuous F)
    {u : A} {θ d : ℝ} (hf : HasDerivAt (fun t => F (u,t)) d θ)
    (hd : d ≠ 0) (hz : F (u,θ) = 0) {W : Set (A × ℝ)}
    (hW : W ∈ 𝓝 (u,θ)) :
    ∃ v : B, ∃ τ : ℝ, (φ v,τ) ∈ W ∧ F (φ v,τ) = 0 ∧
      ∃ a : ℝ, F (φ v,a) < 0 := by
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp hW
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨⟨a,ha,haF⟩,⟨b,hb,hbF⟩⟩ := signs_in_nhds hf hd hz
    (Metric.ball_mem_nhds θ hε)
  have hca : Continuous (fun v : A => F (v,a)) :=
    hF.comp (continuous_id.prodMk continuous_const)
  have hcb : Continuous (fun v : A => F (v,b)) :=
    hF.comp (continuous_id.prodMk continuous_const)
  have hna : {v : A | F (v,a) < 0} ∈ 𝓝 u :=
    (isOpen_lt hca continuous_const).mem_nhds haF
  have hpb : {v : A | 0 < F (v,b)} ∈ 𝓝 u :=
    (isOpen_lt continuous_const hcb).mem_nhds hbF
  obtain ⟨v,hvU,hva,hvb⟩ := hφ.mem_nhds (inter_mem hU (inter_mem hna hpb))
  have hc : Continuous (fun t => F (φ v,t)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  obtain ⟨τ,hτ,hτF⟩ := intermediate_value_uIcc hc.continuousOn
    (show 0 ∈ uIcc (F (φ v,a)) (F (φ v,b)) by
      rw [uIcc_of_le (hva.le.trans hvb.le)]; exact ⟨hva.le,hvb.le⟩)
  have hτball : τ ∈ Metric.ball θ ε := by
    rw [Real.ball_eq_Ioo] at ha hb ⊢
    rw [mem_uIcc] at hτ
    rcases hτ with hτ | hτ
    · exact ⟨ha.1.trans_le hτ.1,hτ.2.trans_lt hb.2⟩
    · exact ⟨hb.1.trans_le hτ.1,hτ.2.trans_lt ha.2⟩
  exact ⟨v,τ,hUV ⟨hvU,hεV hτball⟩,hτF,a,hva⟩

abbrev ParameterPolynomial (ι : Type*) := Polynomial (MvPolynomial ι ℚ)

noncomputable def evaluate {ι : Type*} (F : ParameterPolynomial ι)
    (u : ι → ℝ) (θ : ℝ) : ℝ :=
  F.eval₂ (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) u) θ

lemma continuous_parameter_eval {ι : Type*} (F : ParameterPolynomial ι) :
    Continuous (fun p : (ι → ℝ) × ℝ => evaluate F p.1 p.2) := by
  induction F using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hp.add hq using 1
    ext x
    simp [evaluate,eval₂_add]
  | monomial n c =>
    have he : Continuous (fun u : ι → ℝ =>
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) u c) := by
      simpa only [← MvPolynomial.eval_map] using
        (MvPolynomial.continuous_eval (c.map (algebraMap ℚ ℝ)))
    convert (he.comp continuous_fst).mul (continuous_snd.pow n) using 1
    ext x
    simp [evaluate,eval₂_monomial]

theorem rational_simple_root {ι : Type*} (F : ParameterPolynomial ι)
    {u : ι → ℝ} {θ : ℝ} (hz : evaluate F u θ = 0)
    (hd : evaluate F.derivative u θ ≠ 0) {W : Set ((ι → ℝ) × ℝ)}
    (hW : W ∈ 𝓝 (u,θ)) :
    ∃ v : ι → ℚ, ∃ τ : ℝ, ((fun i => (v i : ℝ)),τ) ∈ W ∧
      evaluate F (fun i => (v i : ℝ)) τ = 0 ∧ IsAlgebraic ℚ τ := by
  have hf : HasDerivAt (fun t => evaluate F u t) (evaluate F.derivative u θ) θ := by
    simpa [evaluate,eval₂_eq_eval_map,derivative_map] using
      (F.map (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) u)).hasDerivAt θ
  have hφ : DenseRange (fun v : ι → ℚ => (fun i => (v i : ℝ))) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨v,τ,hτW,hτF,a,ha⟩ := dense_parameter_root hφ
    (continuous_parameter_eval F) hf hd hz hW
  refine ⟨v,τ,hτW,hτF,?_⟩
  let G : Polynomial ℚ := F.map (MvPolynomial.eval v)
  have he (t : ℝ) : G.aeval t = evaluate F (fun i => (v i : ℝ)) t := by
    simp only [G,aeval_def,eval₂_map,evaluate]
    congr 1
    ext i <;> simp
  refine ⟨G,?_,?_⟩
  · intro hG
    have hh := he a
    rw [hG,map_zero] at hh
    linarith
  · rw [he,hτF]

lemma evaluate_rat {ι : Type*} (F : ParameterPolynomial ι) (v : ι → ℚ) (τ : ℝ) :
    evaluate F (fun i => (v i : ℝ)) τ =
      Polynomial.aeval τ (F.map (MvPolynomial.eval v)) := by
  simp only [aeval_def,eval₂_map,evaluate]
  congr 1
  ext i <;> simp

lemma algebraic_polynomial_value (p : Polynomial ℚ) {τ : ℝ}
    (hτ : IsAlgebraic ℚ τ) : IsAlgebraic ℚ (Polynomial.aeval τ p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | monomial n c =>
    simpa only [aeval_monomial] using (isAlgebraic_algebraMap (A := ℝ) c).mul (hτ.pow n)

lemma algebraic_parameter_value {ι : Type*} (F : ParameterPolynomial ι)
    (v : ι → ℚ) {τ : ℝ} (hτ : IsAlgebraic ℚ τ) :
    IsAlgebraic ℚ (evaluate F (fun i => (v i : ℝ)) τ) := by
  rw [evaluate_rat]
  exact algebraic_polynomial_value _ hτ

noncomputable def chartValue {ι κ : Type*} (N D : κ → ParameterPolynomial ι)
    (p : (ι → ℝ) × ℝ) (i : κ) : ℝ := evaluate (N i) p.1 p.2 / evaluate (D i) p.1 p.2

theorem specialize_chart {ι κ η : Type*} [Finite κ] [Finite η]
    (F : ParameterPolynomial ι) (N D : κ → ParameterPolynomial ι)
    (G J : η → ParameterPolynomial ι) (b : η → MvPolynomial ι ℚ)
    {u : ι → ℝ} {θ : ℝ} (hz : evaluate F u θ = 0)
    (hd : evaluate F.derivative u θ ≠ 0)
    (hD : ∀ i, evaluate (D i) u θ ≠ 0)
    (hb : ∀ j, MvPolynomial.eval₂ (algebraMap ℚ ℝ) u (b j) ≠ 0)
    (hId : ∀ j, Polynomial.C (b j)*G j = F*J j)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ι → ℚ, ∃ τ : ℝ, IsAlgebraic ℚ τ ∧
      evaluate F (fun i => (v i : ℝ)) τ = 0 ∧
      (∀ i, evaluate (D i) (fun j => (v j : ℝ)) τ ≠ 0 ∧
        IsAlgebraic ℚ (chartValue N D ((fun j => (v j : ℝ)),τ) i) ∧
        |chartValue N D ((fun j => (v j : ℝ)),τ) i-chartValue N D (u,θ) i| < ε) ∧
      (∀ j, evaluate (G j) (fun i => (v i : ℝ)) τ = 0) := by
  have hden : ∀ᶠ p : (ι → ℝ) × ℝ in 𝓝 (u,θ), ∀ i,
      evaluate (D i) p.1 p.2 ≠ 0 :=
    eventually_all.mpr (fun i => (continuous_parameter_eval (D i)).continuousAt.eventually_ne (hD i))
  have happ : ∀ᶠ p : (ι → ℝ) × ℝ in 𝓝 (u,θ), ∀ i,
      |chartValue N D p i-chartValue N D (u,θ) i| < ε := by
    apply eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun p => chartValue N D p i) (u,θ) :=
      (continuous_parameter_eval (N i)).continuousAt.div
        (continuous_parameter_eval (D i)).continuousAt (hD i)
    have he := hc.eventually (Metric.ball_mem_nhds (chartValue N D (u,θ) i) hε)
    simpa only [Metric.mem_ball,Real.dist_eq] using he
  have hbne : ∀ᶠ p : (ι → ℝ) × ℝ in 𝓝 (u,θ), ∀ j,
      evaluate (Polynomial.C (b j)) p.1 p.2 ≠ 0 := by
    apply eventually_all.mpr
    intro j
    apply (continuous_parameter_eval (Polynomial.C (b j))).continuousAt.eventually_ne
    simpa [evaluate] using hb j
  obtain ⟨v,τ,hW,hF,hτ⟩ := rational_simple_root F hz hd (hden.and (happ.and hbne))
  refine ⟨v,τ,hτ,hF,?_,?_⟩
  · intro i
    refine ⟨hW.1 i,?_,hW.2.1 i⟩
    unfold chartValue
    rw [div_eq_mul_inv]
    exact (algebraic_parameter_value (N i) v hτ).mul
      (IsAlgebraic.inv_iff.mpr (algebraic_parameter_value (D i) v hτ))
  · intro j
    have he := congrArg (Polynomial.eval₂RingHom
      (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (fun i => (v i : ℝ))) τ) (hId j)
    change evaluate (Polynomial.C (b j)*G j) _ τ = evaluate (F*J j) _ τ at he
    simp only [evaluate,eval₂_mul] at he
    change evaluate (Polynomial.C (b j)) _ τ * evaluate (G j) _ τ =
      evaluate F _ τ * evaluate (J j) _ τ at he
    rw [hF,zero_mul] at he
    exact (mul_eq_zero.mp he).resolve_left (hW.2.2 j)

end PlanarUnitDistances.AlgebraicSpecialization

namespace PlanarUnitDistances.PrimitiveChart
open Set Polynomial IntermediateField

theorem finite_coordinates_primitive {K : Type*} [Field K] [CharZero K]
    [Algebra K ℝ] {κ : Type*} [Finite κ] (x : κ → ℝ)
    (hx : ∀ i, IsAlgebraic K (x i)) :
    ∃ θ : ℝ, IsAlgebraic K θ ∧ ∀ i, ∃ p q : Polynomial K,
      Polynomial.aeval θ q ≠ 0 ∧ x i = Polynomial.aeval θ p / Polynomial.aeval θ q := by
  let M := IntermediateField.adjoin K (Set.range x)
  have : Finite (Set.range x) := Set.finite_range x
  have : FiniteDimensional K M := IntermediateField.finiteDimensional_adjoin
    (fun y hy => by obtain ⟨i,rfl⟩ := hy; exact (hx i).isIntegral)
  obtain ⟨θ,hθ⟩ := Field.exists_primitive_element K M
  refine ⟨(θ : ℝ),?_,?_⟩
  · exact (Algebra.IsAlgebraic.isAlgebraic θ).algHom M.val
  · intro i
    by_cases hi : x i = 0
    · exact ⟨0,1,by simp,by simp [hi]⟩
    let y : M := ⟨x i,IntermediateField.subset_adjoin K (Set.range x) (mem_range_self i)⟩
    have hm : y ∈ IntermediateField.adjoin K {θ} := by rw [hθ]; trivial
    obtain ⟨p,q,hpq⟩ := (IntermediateField.mem_adjoin_simple_iff K y).mp hm
    have he : x i = Polynomial.aeval (θ : ℝ) p / Polynomial.aeval (θ : ℝ) q := by
      have hh := congrArg (fun a : M => (a : ℝ)) hpq
      simpa [y] using hh
    refine ⟨p,q,?_,he⟩
    intro hq
    rw [hq,div_zero] at he
    exact hi he

end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances.PrimitiveChart
open Polynomial

theorem clear_polynomial {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    (f : R →+* K)
    (hfrac : ∀ a : K, ∃ r s : R, s ≠ 0 ∧ a * f s = f r)
    (p : Polynomial K) :
    ∃ q : Polynomial R, ∃ d : R, d ≠ 0 ∧ q.map f = C (f d) * p := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨q₁,d₁,hd₁,hq₁⟩ := h₁
    obtain ⟨q₂,d₂,hd₂,hq₂⟩ := h₂
    refine ⟨C d₂ * q₁ + C d₁ * q₂,d₁*d₂,mul_ne_zero hd₁ hd₂,?_⟩
    simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,hq₁,hq₂,
      map_mul]
    ring
  | monomial n a =>
    obtain ⟨r,s,hs,he⟩ := hfrac a
    refine ⟨monomial n r,s,hs,?_⟩
    rw [Polynomial.map_monomial,← he,mul_comm a (f s),← C_mul_monomial]

theorem clear_relation {R K L : Type*} [CommRing R] [IsDomain R]
    [Field K] [Field L] [Algebra K L]
    (f : R →+* K) (hf : Function.Injective f)
    (hfrac : ∀ a : K, ∃ r s : R, s ≠ 0 ∧ a * f s = f r)
    (θ : L) (F : Polynomial R) (d : R) (hd : d ≠ 0)
    (hF : F.map f = C (f d) * minpoly K θ)
    (G : Polynomial R) (hG : Polynomial.aeval θ (G.map f) = 0) :
    ∃ b : R, ∃ J : Polynomial R, b ≠ 0 ∧ C b * G = F * J := by
  obtain ⟨H,hH⟩ := minpoly.dvd K θ hG
  obtain ⟨J,e,he,hJ⟩ := clear_polynomial f hfrac H
  refine ⟨d*e,J,mul_ne_zero hd he,?_⟩
  apply Polynomial.map_injective f hf
  simp only [Polynomial.map_mul,Polynomial.map_C,map_mul,hF,hJ,hH]
  ring

end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances.PrimitiveChart
open Set Polynomial IntermediateField

noncomputable abbrev ParameterField {ι : Type*} (u : ι → ℝ) :=
  IntermediateField.adjoin ℚ (Set.range u)

noncomputable def parameterMap {ι : Type*} (u : ι → ℝ) :
    MvPolynomial ι ℚ →ₐ[ℚ] ParameterField u :=
  MvPolynomial.aeval (fun i =>
    ⟨u i,IntermediateField.subset_adjoin ℚ (Set.range u) (mem_range_self i)⟩)

@[simp] theorem coe_parameterMap {ι : Type*} (u : ι → ℝ) (p : MvPolynomial ι ℚ) :
    ((parameterMap u p : ParameterField u) : ℝ) = MvPolynomial.aeval u p := by
  have he : (IntermediateField.val (ParameterField u)).comp (parameterMap u) =
      MvPolynomial.aeval u := by
    ext i
    change ((parameterMap u (MvPolynomial.X i) : ParameterField u) : ℝ) =
      MvPolynomial.aeval u (MvPolynomial.X i)
    simp only [parameterMap,MvPolynomial.aeval_X]
  exact AlgHom.congr_fun he p

theorem parameterMap_injective {ι : Type*} {u : ι → ℝ}
    (hu : AlgebraicIndependent ℚ u) : Function.Injective (parameterMap u) := by
  intro p q hpq
  apply (algebraicIndependent_iff_injective_aeval.mp hu)
  simpa only [coe_parameterMap] using congrArg (fun a : ParameterField u => (a : ℝ)) hpq

theorem parameterMap_fraction {ι : Type*} (u : ι → ℝ) (a : ParameterField u) :
    ∃ r s : MvPolynomial ι ℚ, s ≠ 0 ∧ a * parameterMap u s = parameterMap u r := by
  by_cases ha : a = 0
  · exact ⟨0,1,one_ne_zero,by simp [ha]⟩
  obtain ⟨r,hr,s,hs,h⟩ := IntermediateField.mem_adjoin_iff_div.mp a.property
  rw [Algebra.adjoin_range_eq_range_aeval] at hr hs
  obtain ⟨r,rfl⟩ := hr
  obtain ⟨s,rfl⟩ := hs
  change (a : ℝ) = MvPolynomial.aeval u r / MvPolynomial.aeval u s at h
  have hsne : MvPolynomial.aeval u s ≠ 0 := by
    intro hz
    rw [hz,div_zero] at h
    exact ha (Subtype.ext h)
  refine ⟨r,s,?_,?_⟩
  · intro hz
    exact hsne (by rw [hz,map_zero])
  · apply Subtype.ext
    change (a : ℝ) * ((parameterMap u s : ParameterField u) : ℝ) =
      ((parameterMap u r : ParameterField u) : ℝ)
    rw [coe_parameterMap,coe_parameterMap,h]
    exact div_mul_cancel₀ _ hsne

theorem cleared_minpoly {ι : Type*} {u : ι → ℝ}
    (hu : AlgebraicIndependent ℚ u) {θ : ℝ}
    (hθ : IsAlgebraic (ParameterField u) θ) :
    ∃ F : AlgebraicSpecialization.ParameterPolynomial ι, ∃ d : MvPolynomial ι ℚ,
      d ≠ 0 ∧
      F.map (parameterMap u).toRingHom =
        C (parameterMap u d) * minpoly (ParameterField u) θ ∧
      AlgebraicSpecialization.evaluate F u θ = 0 ∧
      AlgebraicSpecialization.evaluate F.derivative u θ ≠ 0 := by
  obtain ⟨F,d,hd,hF⟩ := clear_polynomial (parameterMap u).toRingHom
    (parameterMap_fraction u) (minpoly (ParameterField u) θ)
  have hev (p : AlgebraicSpecialization.ParameterPolynomial ι) :
      Polynomial.aeval θ (p.map (parameterMap u).toRingHom) =
        AlgebraicSpecialization.evaluate p u θ := by
    have hcomp : (algebraMap (ParameterField u) ℝ).comp (parameterMap u).toRingHom =
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) u :=
      RingHom.ext (fun p => coe_parameterMap u p)
    simp only [Polynomial.aeval_def,Polynomial.eval₂_map,AlgebraicSpecialization.evaluate,hcomp]
  have hdn : ((parameterMap u d : ParameterField u) : ℝ) ≠ 0 := by
    intro h
    apply hd
    apply parameterMap_injective hu
    apply Subtype.ext
    simpa only [map_zero,ZeroMemClass.coe_zero] using h
  refine ⟨F,d,hd,hF,?_,?_⟩
  · rw [← hev,hF,map_mul,minpoly.aeval (ParameterField u) θ,mul_zero]
  · have hs : (minpoly (ParameterField u) θ).Separable :=
      (minpoly.irreducible hθ.isIntegral).separable
    have hm := hs.aeval_derivative_ne_zero (minpoly.aeval (ParameterField u) θ)
    have hder := congrArg Polynomial.derivative hF
    rw [Polynomial.derivative_map,Polynomial.derivative_C_mul] at hder
    rw [← hev,hder,map_mul,Polynomial.aeval_C]
    exact mul_ne_zero hdn hm

end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances.PrimitiveChart
open Set Polynomial IntermediateField AlgebraicSpecialization

lemma evaluate_as_map {ι : Type*} (u : ι → ℝ) (p : ParameterPolynomial ι) (θ : ℝ) :
    Polynomial.aeval θ (p.map (parameterMap u).toRingHom) = evaluate p u θ := by
  have hcomp : (algebraMap (ParameterField u) ℝ).comp (parameterMap u).toRingHom =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) u :=
    RingHom.ext (fun p => coe_parameterMap u p)
  simp only [Polynomial.aeval_def,Polynomial.eval₂_map,evaluate,hcomp]

theorem coordinate_polynomials {ι κ : Type*} {u : ι → ℝ}
    (hu : AlgebraicIndependent ℚ u) (θ : ℝ) (x : κ → ℝ)
    (hx : ∀ i, ∃ p q : Polynomial (ParameterField u),
      Polynomial.aeval θ q ≠ 0 ∧ x i = Polynomial.aeval θ p / Polynomial.aeval θ q) :
    ∃ N D : κ → ParameterPolynomial ι,
      (∀ i, evaluate (D i) u θ ≠ 0) ∧ ∀ i, chartValue N D (u,θ) i = x i := by
  classical
  have hi (i : κ) : ∃ N D : ParameterPolynomial ι,
      evaluate D u θ ≠ 0 ∧ evaluate N u θ / evaluate D u θ = x i := by
    obtain ⟨p,q,hq,hx⟩ := hx i
    obtain ⟨P,d,hd,hP⟩ := clear_polynomial (parameterMap u).toRingHom
      (parameterMap_fraction u) p
    obtain ⟨Q,e,he,hQ⟩ := clear_polynomial (parameterMap u).toRingHom
      (parameterMap_fraction u) q
    have hn (a : MvPolynomial ι ℚ) (ha : a ≠ 0) :
        ((parameterMap u a : ParameterField u) : ℝ) ≠ 0 := by
      intro hz
      apply ha
      apply parameterMap_injective hu
      apply Subtype.ext
      simpa using hz
    have hPd : evaluate P u θ = ((parameterMap u d : ParameterField u) : ℝ) *
        Polynomial.aeval θ p := by
      rw [← evaluate_as_map,hP,map_mul,Polynomial.aeval_C]
      rfl
    have hQe : evaluate Q u θ = ((parameterMap u e : ParameterField u) : ℝ) *
        Polynomial.aeval θ q := by
      rw [← evaluate_as_map,hQ,map_mul,Polynomial.aeval_C]
      rfl
    have hC (a : MvPolynomial ι ℚ) : evaluate (C a) u θ =
        ((parameterMap u a : ParameterField u) : ℝ) := by
      rw [coe_parameterMap]
      simp only [evaluate,Polynomial.eval₂_C]
      rfl
    have hmul (a b : ParameterPolynomial ι) : evaluate (a*b) u θ =
        evaluate a u θ * evaluate b u θ := Polynomial.eval₂_mul _ _
    refine ⟨C e*P,C d*Q,?_,?_⟩
    · rw [hmul]
      rw [hC,hQe]
      exact mul_ne_zero (hn d hd) (mul_ne_zero (hn e he) hq)
    · rw [hmul,hmul,hC,hC,hPd,hQe,hx]
      have hdR := hn d hd
      have heR := hn e he
      rw [mul_left_comm ((parameterMap u d : ParameterField u) : ℝ)
        ((parameterMap u e : ParameterField u) : ℝ),← mul_assoc,← mul_assoc]
      exact mul_div_mul_left _ _ (mul_ne_zero heR hdR)
  choose N D hD hv using hi
  exact ⟨N,D,hD,hv⟩

end PlanarUnitDistances.PrimitiveChart


namespace PlanarUnitDistances.PrimitiveChart
open Set Polynomial IntermediateField AlgebraicSpecialization

def squaredGap {κ : Type*} (x : κ × Fin 2 → ℝ) (p : κ × κ) : ℝ :=
  (x (p.1, 0) - x (p.2, 0))^2 + (x (p.1, 1) - x (p.2, 1))^2

def gapNum {R κ : Type*} [CommRing R] (N D : κ × Fin 2 → R) (p : κ × κ) : R :=
  (N (p.1,0)*D (p.2,0) - N (p.2,0)*D (p.1,0))^2 * (D (p.1,1)*D (p.2,1))^2 +
  (N (p.1,1)*D (p.2,1) - N (p.2,1)*D (p.1,1))^2 * (D (p.1,0)*D (p.2,0))^2

def gapDen {R κ : Type*} [CommRing R] (D : κ × Fin 2 → R) (p : κ × κ) : R :=
  (D (p.1,0)*D (p.2,0))^2 * (D (p.1,1)*D (p.2,1))^2

lemma gapNum_real (a b c d e f g h : ℝ) (hb : b ≠ 0) (hd : d ≠ 0)
    (hf : f ≠ 0) (hh : h ≠ 0) :
    (a*d-c*b)^2 * (f*h)^2 + (e*h-g*f)^2 * (b*d)^2 =
    ((a/b-c/d)^2+(e/f-g/h)^2) * ((b*d)^2*(f*h)^2) := by
  have hx : (a/b-c/d)*(b*d) = a*d-c*b := by field_simp
  have hy : (e/f-g/h)*(f*h) = e*h-g*f := by field_simp
  rw [← hx, ← hy]
  ring

noncomputable def equalGapPoly {ι κ : Type*} (N D : κ × Fin 2 → ParameterPolynomial ι)
    (p q : κ × κ) : ParameterPolynomial ι :=
  gapNum N D p * gapDen D q - gapNum N D q * gapDen D p

lemma evaluate_equalGapPoly {ι κ : Type*} (N D : κ × Fin 2 → ParameterPolynomial ι)
    (u : ι → ℝ) (θ : ℝ) (hD : ∀ k, evaluate (D k) u θ ≠ 0) (p q : κ × κ) :
    evaluate (equalGapPoly N D p q) u θ = 0 ↔
      squaredGap (chartValue N D (u,θ)) p = squaredGap (chartValue N D (u,θ)) q := by
  let z := chartValue N D (u,θ)
  let den := fun t => evaluate (gapDen D t) u θ
  have hd (t : κ × κ) : den t ≠ 0 := by
    dsimp only [den, gapDen, evaluate]
    simp only [eval₂_mul, eval₂_pow]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (hD _) (hD _)))
      (pow_ne_zero _ (mul_ne_zero (hD _) (hD _)))
  have hn (t : κ × κ) : evaluate (gapNum N D t) u θ = squaredGap z t * den t := by
    dsimp only [den, z, gapNum, gapDen, squaredGap, chartValue, evaluate]
    simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow]
    exact gapNum_real _ _ _ _ _ _ _ _ (hD _) (hD _) (hD _) (hD _)
  have he : evaluate (equalGapPoly N D p q) u θ =
      (squaredGap z p - squaredGap z q) * (den p * den q) := by
    calc
      _ = evaluate (gapNum N D p) u θ * den q - evaluate (gapNum N D q) u θ * den p := by
        simp only [equalGapPoly, den, evaluate, eval₂_sub, eval₂_mul]
      _ = _ := by rw [hn, hn]; ring
  rw [he, mul_eq_zero]
  simp only [mul_ne_zero (hd p) (hd q), or_false, sub_eq_zero, z]


theorem algebraic_equal_approximation {κ : Type*} [Finite κ]
    (x : κ × Fin 2 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : κ × Fin 2 → ℝ, (∀ k, IsAlgebraic ℚ (y k) ∧ |y k-x k| < ε) ∧
      ∀ p q, squaredGap x p = squaredGap x q → squaredGap y p = squaredGap y q := by
  classical
  obtain ⟨s,hs⟩ := exists_isTranscendenceBasis ℚ ℝ
  let u : s → ℝ := Subtype.val
  have hu : AlgebraicIndependent ℚ u := hs.1
  have : Algebra.IsAlgebraic (ParameterField u) ℝ := hs.isAlgebraic_field
  obtain ⟨θ,hθ,hx⟩ := finite_coordinates_primitive x
    (fun k => Algebra.IsAlgebraic.isAlgebraic (x k) : ∀ k, IsAlgebraic (ParameterField u) (x k))
  obtain ⟨F,d,hd,hF,hz,hder⟩ := cleared_minpoly hu hθ
  obtain ⟨N,D,hD,hval⟩ := coordinate_polynomials hu θ x hx
  let η := {e : (κ × κ) × (κ × κ) // squaredGap x e.1 = squaredGap x e.2}
  let G : η → ParameterPolynomial s := fun e => equalGapPoly N D e.val.1 e.val.2
  have hG (e : η) : Polynomial.aeval θ ((G e).map (parameterMap u).toRingHom) = 0 := by
    rw [evaluate_as_map]
    apply (evaluate_equalGapPoly N D u θ hD _ _).mpr
    simpa only [squaredGap,hval] using e.property
  have hId (e : η) : ∃ b : MvPolynomial s ℚ, ∃ J : ParameterPolynomial s,
      b ≠ 0 ∧ C b*G e = F*J :=
    clear_relation (parameterMap u).toRingHom (parameterMap_injective hu)
      (parameterMap_fraction u) θ F d hd hF (G e) (hG e)
  choose b J hb hId using hId
  have hbval (e : η) : MvPolynomial.eval₂ (algebraMap ℚ ℝ) u (b e) ≠ 0 := by
    intro he
    exact hb e ((algebraicIndependent_iff_injective_aeval.mp hu)
      (show MvPolynomial.aeval u (b e) = MvPolynomial.aeval u 0 by
        simpa only [map_zero,MvPolynomial.aeval_def] using he))
  obtain ⟨v,τ,_,_,hcoord,hunit⟩ := specialize_chart F N D G J b hz hder hD hbval hId hε
  refine ⟨chartValue N D ((fun i => (v i : ℝ)),τ),?_,?_⟩
  · intro k
    exact ⟨(hcoord k).2.1,by simpa only [hval] using (hcoord k).2.2⟩
  · intro i j hij
    exact (evaluate_equalGapPoly N D _ τ (fun k => (hcoord k).1) i j).mp
      (hunit ⟨(i,j),hij⟩)


end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances.PrimitiveChart
open Set Filter
open scoped Topology

lemma plane_dist_sq (p q : EuclideanSpace ℝ (Fin 2)) :
    dist p q ^ 2 = (p 0-q 0)^2+(p 1-q 1)^2 := by
  rw [dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  simp only [WithLp.ofLp_sub,Pi.sub_apply,Real.norm_eq_abs,sq_abs]

lemma plane_close_of_coordinates {δ : ℝ} (hδ : 0 < δ)
    (p q : EuclideanSpace ℝ (Fin 2)) (h : ∀ k, |p k-q k| < δ) :
    dist p q < 2*δ := by
  have h0 := (sq_lt_sq₀ (abs_nonneg (p 0-q 0)) hδ.le).mpr (h 0)
  have h1 := (sq_lt_sq₀ (abs_nonneg (p 1-q 1)) hδ.le).mpr (h 1)
  rw [sq_abs] at h0 h1
  have he := plane_dist_sq p q
  nlinarith [dist_nonneg (x := p) (y := q)]

lemma finite_separation {κ : Type*} [Finite κ] {M : Type*} [MetricSpace M]
    (p : κ → M) (hp : Function.Injective p) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i j, i ≠ j → ρ < dist (p i) (p j) := by
  have he : ∀ᶠ ρ : ℝ in 𝓝 0, ∀ i j, i ≠ j → ρ < dist (p i) (p j) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (by simp [hij])
    · have hd : (0 : ℝ) < dist (p i) (p j) := dist_pos.mpr (hp.ne hij)
      have hlt : Iio (dist (p i) (p j)) ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds hd
      exact Filter.mem_of_superset hlt (fun _ h _ => h)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨r/2,by positivity,hball ?_⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0 < r/2)]
  linarith


theorem algebraic_planar_equal {κ : Type*} [Finite κ]
    (p : κ → EuclideanSpace ℝ (Fin 2)) (hp : Function.Injective p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : κ → EuclideanSpace ℝ (Fin 2), Function.Injective q ∧
      (∀ i, dist (q i) (p i) < ε ∧ ∀ k, IsAlgebraic ℚ (q i k)) ∧
      ∀ i j k l, dist (p i) (p j) = dist (p k) (p l) → dist (q i) (q j) = dist (q k) (q l) := by
  classical
  obtain ⟨ρ,hρ,hsep⟩ := finite_separation p hp
  let δ := min (ε/3) (ρ/6)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨y,hy,heq⟩ := algebraic_equal_approximation (fun k => p k.1 k.2) hδ
  let q : κ → EuclideanSpace ℝ (Fin 2) := fun i => WithLp.toLp 2 (fun k => y (i,k))
  have hclose (i : κ) : dist (q i) (p i) < 2*δ :=
    plane_close_of_coordinates hδ _ _ (fun k => (hy (i,k)).2)
  have hερ : 2*δ < ε := by have := min_le_left (ε/3) (ρ/6); dsimp [δ]; linarith
  have hρδ : 4*δ < ρ := by have := min_le_right (ε/3) (ρ/6); dsimp [δ]; linarith
  refine ⟨q,?_,?_,?_⟩
  · intro i j hij
    by_contra hne
    have hdist := dist_triangle (p i) (q i) (p j)
    rw [dist_comm (p i) (q i)] at hdist
    have hi := hclose i
    have hj := hclose j
    have hs := hsep i j hne
    rw [← hij] at hj
    linarith
  · intro i
    exact ⟨(hclose i).trans hερ,fun k => (hy (i,k)).1⟩
  · intro i j k l h
    have anterior : squaredGap (fun k => p k.1 k.2) (i,j) = squaredGap (fun k => p k.1 k.2) (k,l) := by
      calc
        _ = dist (p i) (p j)^2 := (plane_dist_sq (p i) (p j)).symm
        _ = dist (p k) (p l)^2 := congrArg (fun d : ℝ => d^2) h
        _ = _ := plane_dist_sq (p k) (p l)
    have posterior : dist (q i) (q j)^2 = dist (q k) (q l)^2 := by
      simpa only [plane_dist_sq, squaredGap, q, WithLp.ofLp_toLp] using heq (i,j) (k,l) anterior
    simpa only [Real.sqrt_sq dist_nonneg] using congrArg Real.sqrt posterior

end PlanarUnitDistances.PrimitiveChart
end Especializacao89

namespace OMA.Distancias89
open EuclideanGeometry

abbrev PlanoIntegral := {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}

/-- Uma homotetia comum elimina os denominadores de uma família finita. -/
lemma multiplicador {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, IsAlgebraic ℚ (x i)) :
    ∃ z : ℤ, z ≠ 0 ∧ ∀ i, IsIntegral ℤ ((z : ℝ) * x i) := by
  classical
  letI : Algebra.IsAlgebraic ℤ ℚ :=
    IsLocalization.isAlgebraic (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  have h (i : ι) := ((hx i).restrictScalars ℤ).exists_integral_multiple
  choose a ha hb using h
  refine ⟨∏ i, a i, Finset.prod_ne_zero_iff.mpr (fun i _ => ha i), ?_⟩
  intro i
  have hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  have hz : IsIntegral ℤ ((∏ j, a j) • x i) := by
    rw [← Finset.prod_erase_mul _ _ hi, mul_smul]
    exact (hb i).smul _
  simpa only [zsmul_eq_mul] using hz

/-- Qualquer igualdade de distâncias na origem persiste na realização de destino. -/
lemma realiza {E F : Type*} [MetricSpace E] [MetricSpace F] (s : Finset E)
    (f : s → F) (hf : Function.Injective f)
    (h : ∀ i j k l : s, dist (i : E) j = dist (k : E) l → dist (f i) (f j) = dist (f k) (f l)) :
    ∃ t : Finset F, t.card = s.card ∧ distinctDistances t ≤ distinctDistances s := by
  classical
  let t := Finset.univ.image f
  refine ⟨t, ?_, ?_⟩
  · simp [t, Finset.card_image_of_injective _ hf]
  let rep : ℝ → ℝ := fun r =>
    if hr : ∃ a : s × s, dist (a.1 : E) a.2 = r then dist (f hr.choose.1) (f hr.choose.2) else 0
  have hrep (i j : s) : rep (dist (i : E) j) = dist (f i) (f j) := by
    have hr : ∃ a : s × s, dist (a.1 : E) a.2 = dist (i : E) j := ⟨(i,j),rfl⟩
    simpa only [rep, dif_pos hr] using h hr.choose.1 hr.choose.2 i j hr.choose_spec
  apply Finset.card_le_card_of_surjOn rep
  intro d hd
  obtain ⟨⟨v,w⟩, hp, rfl⟩ := Finset.mem_image.mp (show d ∈ distanceSet t from hd)
  obtain ⟨hv,hw,hvw⟩ := Finset.mem_offDiag.mp hp
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hw
  refine ⟨dist (i : E) j, ?_, hrep i j⟩
  apply Finset.mem_image.mpr
  refine ⟨((i : E),(j : E)), Finset.mem_offDiag.mpr ⟨i.property,j.property,?_⟩,rfl⟩
  intro hij
  exact hvw (congrArg f (Subtype.ext hij))

lemma compara_minimos {E F : Type*} [MetricSpace E] [MetricSpace F] (n : ℕ)
    (hex : ∃ s : Finset E, s.card = n)
    (h : ∀ s : Finset E, ∃ t : Finset F, t.card = s.card ∧ distinctDistances t ≤ distinctDistances s) :
    minimalDistinctDistances F n ≤ minimalDistinctDistances E n := by
  classical
  let S := {m : ℕ | ∃ s : Finset E, s.card = n ∧ distinctDistances s = m}
  obtain ⟨s,hs⟩ := hex
  have hS : S.Nonempty := ⟨distinctDistances s,s,hs,rfl⟩
  obtain ⟨p,hp,hmin⟩ := (show ∃ p : Finset E, p.card = n ∧ distinctDistances p = sInf S
    from Nat.sInf_mem hS)
  obtain ⟨t,ht,hd⟩ := h p
  have le_t : minimalDistinctDistances F n ≤ distinctDistances t :=
    Nat.sInf_le (show ∃ q : Finset F, q.card = n ∧ distinctDistances q = distinctDistances t
      from ⟨t,ht.trans hp,rfl⟩)
  exact le_t.trans (hd.trans hmin.le)

lemma realiza_integral (s : Finset ℝ²) :
    ∃ t : Finset PlanoIntegral, t.card = s.card ∧ distinctDistances t ≤ distinctDistances s := by
  classical
  obtain ⟨q,hq,halg,heq⟩ := Especializacao89.PlanarUnitDistances.PrimitiveChart.algebraic_planar_equal
    (fun p : s => (p : ℝ²)) Subtype.val_injective (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨z,hz,hint⟩ := multiplicador (fun k : s × Fin 2 => q k.1 k.2) (fun k => (halg k.1).2 k.2)
  have hn : (z : ℝ) ≠ 0 := by exact_mod_cast hz
  let f : s → PlanoIntegral := fun p => ⟨(z : ℝ) • q p, fun i => by
    change IsIntegral ℤ ((z : ℝ) * q p i)
    exact hint (p,i)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply hq
    have hscaled := congrArg Subtype.val hij
    change (z : ℝ) • q i = (z : ℝ) • q j at hscaled
    have hcancel := congrArg (fun v : ℝ² => (z : ℝ)⁻¹ • v) hscaled
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using hcancel
  apply realiza s f hf
  intro i j k l hij
  change dist ((z : ℝ) • q i) ((z : ℝ) • q j) = dist ((z : ℝ) • q k) ((z : ℝ) • q l)
  simpa only [dist_eq_norm, ← smul_sub, norm_smul] using
    congrArg (fun d : ℝ => ‖(z : ℝ)‖ * d) (heq i j k l hij)

end OMA.Distancias89

open EuclideanGeometry OMA.Distancias89

theorem OMA.solution : OMA.R_Erdos89_erdos_89_R1.H1 := by
  unfold OMA.R_Erdos89_erdos_89_R1.H1
  funext n
  obtain ⟨s,hs⟩ := Infinite.exists_subset_card_eq ℝ² n
  obtain ⟨t,ht,_⟩ := realiza_integral s
  apply Nat.le_antisymm
  · exact compara_minimos n ⟨s,hs⟩ realiza_integral
  · apply compara_minimos n (E := PlanoIntegral) (F := ℝ²) ⟨t,ht.trans hs⟩
    intro a
    exact realiza a (fun p => (p.val : ℝ²)) (Subtype.val_injective.comp Subtype.val_injective)
      (fun _ _ _ _ h => h)

/- Licença do código adaptado
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      ”License” shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      ”Licensor” shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      ”Legal Entity” shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      ”control” means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      ”You” (or ”Your”) shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      ”Source” form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      ”Object” form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      ”Work” shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      ”Derivative Works” shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      ”Contribution” shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, ”submitted”
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as ”Not a Contribution.”

      ”Contributor” shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a ”NOTICE” text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an ”AS IS” BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets ”[]”
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same ”printed page” as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the ”License”);
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an ”AS IS” BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
