import FormalConjectures.Paper.RiemannHypothesisEquivalents
import Mathlib
/-
Ported from https://github.com/ChironTheCentaur/rh-lab-rh-criteria (commit bfe38b29),
Copyright 2026 Sky (GitHub: ChironTheCentaur), licensed under the Apache License, Version 2.0.
Its Zeta23 part is taken from https://github.com/anthropics/zeta-23-lean (zeta23/Zeta23),
Copyright 2026 Anthropic, PBC, Apache License, Version 2.0; the files under Zeta23/FromPNTPlus
derive from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
Copyright the PrimeNumberTheoremAnd contributors, Apache License, Version 2.0, some of them in turn
from mathlib, Copyright the mathlib contributors, Apache License, Version 2.0.
The copied statement definitions are from google-deepmind/formal-conjectures, Copyright The Formal
Conjectures Authors, Apache License, Version 2.0.
Modifications: the import closure of the result was assembled into one file, unused declarations
were removed, local notations were expanded, attributes other than simp were dropped, a few proofs
were adapted to the pinned Mathlib (the positivity of the real part of the logarithmic
derivative of xi under RH is used in its nonnegative form), comments were removed, local names
were shortened and spaces around operators were dropped.
A copy of the Apache License, Version 2.0 is at https://www.apache.org/licenses/LICENSE-2.0.
-/
-- aF.abj
section
namespace aF.Rr
open Real MeasureTheory
open scoped ArithmeticFunction.sigma CompactlySupported Convolution ContDiff
namespace RiemannHypothesis
noncomputable def fractScalarInv (θ:ℝ) (x:ℝ) :ℝ:=Int.fract (θ/x)
theorem aEStronglyMeasurable_fractScalarInv (θ:ℝ) :AEStronglyMeasurable (fractScalarInv θ) :=
  (measurable_fract.comp (measurable_const.div measurable_id)).aestronglyMeasurable
theorem fractScalarInv_memLp2 (θ:ℝ) :
    MemLp (fractScalarInv θ) 2 (volume.restrict (Set.Ioc 0 1)) :=
  .of_bound (aEStronglyMeasurable_fractScalarInv θ).restrict 1 <|
    Filter.Eventually.of_forall fun x↦by
      rw [Real.norm_eq_abs,abs_of_nonneg (Int.fract_nonneg _)]
      exact (Int.fract_lt_one _).le
noncomputable def fractScalarInvSumL2 (n:ℕ) (c θ:Fin n→ℝ) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
  ∑ ν,c ν•(fractScalarInv_memLp2 (θ ν)).toLp _
end RiemannHypothesis
end aF.Rr
end

-- Zeta23.dO.Auxiliary
section
namespace Complex
end Complex
lemma DifferentiableAt.comp_ofReal {e:ℂ→ℂ} {z:ℝ} (hf:DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x:ℝ↦e x) z:=
  hf.hasDerivAt.comp_ofReal.differentiableAt
lemma deriv.comp_ofReal {e:ℂ→ℂ} {z:ℝ} (hf:DifferentiableAt ℂ e z) :
    deriv (fun x:ℝ↦e x) z=deriv e z:=
  hf.hasDerivAt.comp_ofReal.deriv
lemma DifferentiableAt.ofReal_comp {z:ℝ} {f:ℝ→ℝ} (hf:DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun (y:ℝ)↦(f y:ℂ)) z:=
  hf.hasDerivAt.ofReal_comp.differentiableAt
lemma Differentiable.ofReal_comp {f:ℝ→ℝ} (hf:Differentiable ℝ f) :
    Differentiable ℝ (fun (y:ℝ)↦(f y:ℂ)) :=
  fun _↦hf.differentiableAt.ofReal_comp
open Complex ContinuousLinearMap in
lemma HasDerivAt.tQ {z:ℝ} {f:ℝ→ℝ} {u:ℂ}
    (hf:HasDerivAt (fun y↦(f y:ℂ)) u z) :
    ∃ u':ℝ,u=u' ∧ HasDerivAt f u' z:=by
  lift u to ℝ
  · have H:=(imCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt.deriv
    simp only [Function.comp_def,imCLM_apply,ofReal_im,deriv_const] at H
    rwa [eq_comm,comp_apply,imCLM_apply,toSpanSingleton_apply_one] at H
  refine ⟨u,rfl,?_⟩
  convert! (reCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt
  rw [comp_apply,toSpanSingleton_apply_one,reCLM_apply,ofReal_re]
lemma DifferentiableAt.kH {z:ℝ} {f:ℝ→ℝ} :
    DifferentiableAt ℝ (fun (y:ℝ)↦(f y:ℂ)) z↔DifferentiableAt ℝ f z:=by
  refine ⟨fun H↦?_,ofReal_comp⟩
  obtain ⟨u,_,hu₂⟩:=H.hasDerivAt.tQ
  exact HasDerivAt.differentiableAt hu₂
lemma Differentiable.kH {f:ℝ→ℝ} :
    Differentiable ℝ (fun (y:ℝ)↦(f y:ℂ))↔Differentiable ℝ f:=
  forall_congr' fun _↦DifferentiableAt.kH
lemma deriv.ofReal_comp {z:ℝ} {f:ℝ→ℝ} :
    deriv (fun (y:ℝ)↦(f y:ℂ)) z=deriv f z:=by
  by_cases hf:DifferentiableAt ℝ f z
  · exact hf.hasDerivAt.ofReal_comp.deriv
  · have hf':=mt DifferentiableAt.kH.mp hf
    rw [deriv_zero_of_not_differentiableAt hf,deriv_zero_of_not_differentiableAt hf',
      Complex.ofReal_zero]
end

-- Zeta23.dO.Sobolev
section
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n:ℕ}
 structure CS (n:ℕ) (E:Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun:ℝ→E
  h1:ContDiff ℝ n toFun
  h2:HasCompactSupport toFun
structure trunc extends (CS 2 ℝ) where
  h3:(Set.Icc (-1) (1)).indicator 1≤toFun
  h4:toFun≤Set.indicator (Set.Ioo (-2) (2)) 1
structure W1 (n:ℕ) (E:Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun:ℝ→E
  smooth:ContDiff ℝ n toFun
  integrable: ∀ ⦃k⦄,k≤n→ Integrable (iteratedDeriv k toFun)
abbrev QZ:=W1 2 ℂ
section lemmas
lemma JM:ContDiff ℝ ∞ ofReal:=by
  have key x:HasDerivAt ofReal 1 x:=hasDerivAt_id x |>.ofReal_comp
  have key':deriv ofReal=fun _=>1:=by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x=>(key x).differentiableAt,?_⟩
  simpa [key'] using contDiff_const
end lemmas
namespace CS
variable {f:CS n E} {R x v:ℝ}
instance acJ:CoeFun (CS n E) (fun _=>ℝ→E) where coe:=CS.toFun
instance acK:Coe (CS n ℝ) (CS n ℂ) where coe f:=⟨fun x=>f x,
  JM.of_le (mod_cast le_top) |>.comp f.h1,f.h2.comp_left (g:=ofReal) rfl⟩
lemma continuous (f:CS n E) :Continuous f:=f.h1.continuous
noncomputable def deriv (f:CS (n+1) E) :CS n E where
  toFun:=_root_.deriv f
  h1:=(contDiff_succ_iff_deriv.mp f.h1).2.2
  h2:=f.h2.deriv
end CS
namespace trunc
instance acL:CoeFun trunc (fun _=>ℝ→ℝ) where coe f:=f.toFun
instance acM:Coe trunc (CS 2 ℝ) where coe:=trunc.toCS
end trunc
namespace W1
instance acN:CoeFun (W1 n E) (fun _=>ℝ→E) where coe:=W1.toFun
lemma continuous (f:W1 n E) :Continuous f:=f.smooth.continuous
noncomputable def deriv (f:W1 (n+1) E) :W1 n E where
  toFun:=_root_.deriv f
  smooth:=contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk:=by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)
lemma nY {f:𝓢(ℝ,ℂ)} :Integrable (iteratedDeriv n f) :=by
  induction n generalizing f with
  | zero=>exact f.integrable
  | succ n ih=>simpa [iteratedDeriv_succ'] using! ih (f:=SchwartzMap.derivCLM ℝ ℂ f)
noncomputable def QD (f:𝓢(ℝ,ℂ)) :W1 n ℂ where
  toFun:=f
  smooth:=f.smooth n
  integrable _ _:=nY
end W1
namespace QZ
variable {f:QZ}
noncomputable instance acz:Coe 𝓢(ℝ,ℂ) QZ where coe:=W1.QD
def ZI (f:CS 2 ℂ) :QZ:=by
  refine ⟨f,f.h1,fun k hk=>?_⟩ ; match k with
  | 0=>exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1=>simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2=>simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv
instance acA:Coe (CS 2 ℂ) QZ where coe:=ZI
end QZ
end

-- Zeta23.dO.Fourier
section
open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators
local instance acB {E:Type*} :Coe (E→ℝ) (E→ℂ) :=⟨fun f n=>f n⟩
section lemmas
end lemmas
end

-- Zeta23.dO.Mathlib.Analysis.SpecialFunctions.Log.Basic
section
open Filter Real
end

-- Zeta23.dO.Rectangle
section
open Complex Set Topology
open scoped Interval
variable {z w:ℂ} {c:ℝ}
namespace Rectangle
end Rectangle
def aO (z w:ℂ) :Set ℂ:=
  [[z.re,w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im,w.im]] ∪
    [[z.re,w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im,w.im]]
theorem Set.FL {a b:ℝ} :a∉Set.uIoo a b:=
  fun ⟨h1,h2⟩↦(left_lt_sup.mp h2) (le_of_not_ge (inf_lt_left.mp h1))
theorem Set.DS {a b:ℝ} :b∉Set.uIoo a b:=
  fun ⟨h1,h2⟩↦(right_lt_sup.mp h2) (le_of_not_ge (inf_lt_right.mp h1))
theorem Set.qv {a b c:ℝ} (hc:c∈Set.uIoo a b) :c≠a:=
  fun h↦Set.FL (h ▸ hc)
theorem Set.oN {a b c:ℝ} (hc:c∈Set.uIoo a b) :c≠b:=
  fun h↦Set.DS (h ▸ hc)
lemma cO (z w:ℂ) :aO z w⊆Rectangle z w:=by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h:=hx
  · exact ⟨h.1,h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc,h.2⟩
  · exact ⟨h.1,h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc,h.2⟩
lemma lW {z w p:ℂ}
    (h:p.re≠z.re ∧ p.re≠w.re ∧ p.im≠z.im ∧ p.im≠w.im) :
    Disjoint (aO z w) {p} :=by
  refine disjoint_singleton_right.mpr ?_
  simp_rw [aO,Set.mem_union,not_or]
  exact ⟨⟨⟨fun hc↦h.2.2.1 hc.2,fun hc↦h.1 hc.1⟩,fun hc↦h.2.2.2 hc.2⟩,
    fun hc↦h.2.1 hc.1⟩
lemma eo {z w p:ℂ} :
    Rectangle z w∈𝓝 p↔p∈(Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) :=by
  simp_rw [← mem_interior_iff_mem_nhds,Rectangle,Complex.interior_reProdIm,uIoo,uIcc,
    interior_Icc]
lemma je (z w:ℂ) :
    MapsTo (fun (y:ℝ)=>↑z.re+↑y* I) [[z.im,w.im]] (aO z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _↦
    by simp_all [verticalSegment_eq,aO]
lemma iJ (z w:ℂ) :
    MapsTo (fun (y:ℝ)=>↑w.re+↑y* I) [[z.im,w.im]] (aO z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _↦
    by simp_all [verticalSegment_eq,aO]
lemma jf (z w:ℂ) :
    MapsTo (fun (x:ℝ)=>↑x+z.im* I) [[z.re,w.re]] (aO z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _↦
    by simp_all [horizontalSegment_eq,aO]
lemma iO (z w:ℂ) :
    MapsTo (fun (x:ℝ)=>↑x+w.im* I) [[z.re,w.re]] (aO z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _↦
    by simp_all [horizontalSegment_eq,aO]
theorem bU {z w p:ℂ}
    (hp:Rectangle z w∈𝓝 p) :
    p∉aO z w:=by
  refine Set.disjoint_right.mp (lW ?_) rfl
  have h1:=eo.mp hp
  exact ⟨Set.qv h1.1,Set.oN h1.1,
    Set.qv h1.2,Set.oN h1.2⟩
end

-- Zeta23.dO.QC
section
open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics
open scoped Interval
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g:ℂ→E} {z w p c A:ℂ} {x x₁ x₂ y y₁ y₂ σ:ℝ}
noncomputable def dK (f:ℂ→E) (x₁ x₂ y:ℝ) :E:=
    ∫ x in x₁..x₂,f (x+y* I)
noncomputable def eW (f:ℂ→E) (x y₁ y₂:ℝ) :E:=
    I• ∫ y in y₁..y₂,f (x+y* I)
noncomputable def aV (f:ℂ→E) (z w:ℂ) :E:=
    dK f z.re w.re z.im-dK f z.re w.re w.im+
    eW f w.re z.im w.im-eW f z.re z.im w.im
noncomputable abbrev aW (f:ℂ→E) (z w:ℂ) :E:=
    (1/(2*π* I))•aV f z w
abbrev dG (f:ℂ→E) (s:Set ℂ) :Prop:=
    DifferentiableOn ℂ f s
theorem dG.qw [CompleteSpace E]
    {U:Set ℂ} (XR:dG f U)
    (hU:Rectangle z w⊆U) :
    aV f z w=0:=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (XR.mono hU)
theorem xO (h:Set.EqOn f g (aO z w)) :
    aV f z w=aV g z w:=by
  unfold aV eW
  congrm ?_-?_+I•?_-I•?_
  all_goals refine integral_congr fun _ _↦h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa,by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa,by simp⟩
  · exact Or.inr ⟨by simp,by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp,by simpa⟩
theorem kP (h:Set.EqOn f g (aO z w)) :
    aW f z w=aW g z w:=by
  rw [aW,xO h]
def aY (f:ℂ→E) (z w:ℂ) :Prop:=
    IntervalIntegrable (fun x=>f (x+z.im* I)) volume z.re w.re ∧
    IntervalIntegrable (fun x=>f (x+w.im* I)) volume z.re w.re ∧
    IntervalIntegrable (fun y=>f (w.re+y* I)) volume z.im w.im ∧
    IntervalIntegrable (fun y=>f (z.re+y* I)) volume z.im w.im
theorem aY.add {f g:ℂ→E}
    (hf:aY f z w) (hg:aY g z w) :
    aV (f+g) z w=aV f z w+aV g z w:=by
  dsimp [aV,dK,eW]
  have h₁:=intervalIntegral.integral_add hf.1 hg.1
  have h₂:=intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃:=intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄:=intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁,h₂,h₃,h₄]
  module
omit [NormedSpace ℂ E] in
theorem ContinuousOn.eO (hf:ContinuousOn f (aO z w)) :
    aY f z w:=
  ⟨(hf.comp (by fun_prop) (jf z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (iO z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (iJ z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (je z w)).intervalIntegrable⟩
omit [NormedSpace ℂ E] in
theorem ContinuousOn.gR (hf:ContinuousOn f (Rectangle z w)) :
    aY f z w:=
  ContinuousOn.eO (hf.mono (cO z w))
omit [NormedSpace ℂ E] in
theorem ContinuousOn.qG
    (hf:ContinuousOn f (Rectangle z w \ {p})) (Ou:p∉aO z w) :
    aY f z w:=by
  refine ContinuousOn.eO (hf.mono (Set.subset_sdiff.mpr ?_))
  exact ⟨cO z w,disjoint_singleton_right.mpr Ou⟩
theorem dG.rJ
    (hf:dG f (Rectangle z w \ {p})) (hp:Rectangle z w∈nhds p) :
    aY f z w:=
  hf.continuousOn.qG (bU hp)
theorem dG.gR (hf:dG f (Rectangle z w)) :
    aY f z w:=hf.continuousOn.gR
theorem aV.translate (f:ℂ→E) (z w p:ℂ) :
    aV (fun s=>f (s-p)) z w=aV f (z-p) (w-p) :=by
  simp_rw [aV,dK,eW,sub_re,sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]
theorem aV.Rw (f:ℂ→E) (z w p:ℂ) :
    aW (fun s=>f (s-p)) z w=aW f (z-p) (w-p) :=by
  simp_rw [aW,aV.translate]
lemma Complex.NC:(x+y* I)⁻¹=(x-I*y)/(x^2+y^2) :=by
  rw [Complex.inv_def,div_eq_mul_inv]
  congr <;> simp [conj_ofReal,normSq] <;> ring
lemma sq_add_sq_ne_zero (hy:y≠0) :x^2+y^2≠0:=by
  linarith [sq_nonneg x,sq_pos_iff.mpr hy]
lemma jw (hy:y≠0) :
    Continuous fun x=>x/(x^2+y^2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (fun _=>sq_add_sq_ne_zero hy)
lemma qX (hy:y≠0) :
    ∫ x in x₁..x₂,x/(x^2+y^2)=
    Real.log (x₂^2+y^2)/2 -Real.log (x₁^2+y^2)/2:=by
  let f (x:ℝ) :ℝ:=Real.log (x^2+y^2)/2
  have e1 {x} :=HasDerivAt.add_const (y^2) (by simpa using hasDerivAt_pow 2 x)
  have e2 {x} :HasDerivAt f (x/(x^2+y^2)) x:=by
    convert! (e1.log (sq_add_sq_ne_zero hy)).div_const 2 using 1
    field_simp
  have e3:deriv f=fun x=>x/(x^2+y^2) :=funext (fun _=>e2.deriv)
  have e4:Continuous (deriv f) :=by simpa only [e3] using jw hy
  simp_rw [← e2.deriv]
  exact integral_deriv_eq_sub (fun _ _=>e2.differentiableAt) (e4.intervalIntegrable _ _)
lemma qH (hy:y≠0) :
    ∫ x in x₁..x₂,y/(x^2+y^2)=Real.arctan (x₂/y)-Real.arctan (x₁/y) :=by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr fun x _=>by
    field_simp
    ring
lemma fD (hy:y≠0) :
    ∫ x:ℝ in x₁..x₂,A/(x+y* I)=
    A*(Real.log (x₂^2+y^2)/2 -Real.log (x₁^2+y^2)/2)-
    A* I*(Real.arctan (x₂/y)-Real.arctan (x₁/y)) :=by
  have e1 {x:ℝ} :A/(x+y* I)=A*x/(x^2+y^2)-A* I*y/(x^2+y^2) :=by
    ring_nf
    simp_rw [NC]
    ring
  have e2:IntervalIntegrable (fun x↦A*x/(x^2+y^2)) volume x₁ x₂:=by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul (continuous_ofReal.comp (jw hy))
  have e3:IntervalIntegrable (fun x↦A* I*y/(x^2+y^2)) volume x₁ x₂:=by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x=>?_)
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (fun _ _=>e1),integral_sub e2 e3,mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal,
    qX hy,qH hy]
lemma jg (hx:x≠0) :
    ∫ y:ℝ in y₁..y₂,A/(x+y* I)=
    A/I*(Real.log (y₂^2+(-x)^2)/2 -Real.log (y₁^2+(-x)^2)/2)-
    A/I* I*(Real.arctan (y₂/ -x)-Real.arctan (y₁/ -x)) :=by
  have l1 {y:ℝ} :A/(x+y* I)=A/I/(y+↑(-x)* I) :=by
    have e1:x+y* I≠0:=by
      contrapose! hx
      simpa using congr_arg re hx
    have e2:y+I*↑(-x)≠0:=by
      contrapose! hx
      simpa using congr_arg im hx
    field_simp [*]
    push_cast
    ring_nf
    simp
  have l2: -x≠0:=by rwa [neg_ne_zero]
  simp_rw [l1,fD l2]
lemma xP {z w c:ℂ}
    (h1:z.re<0) (h2:z.im<0) (h3:0<w.re) (h4:0<w.im) :
    aV (fun s=>c/s) z w=2* I*π*c:=by
  simp only [aV,dK,eW,smul_eq_mul]
  rw [jg h1.ne,jg h3.ne.symm]
  rw [fD h2.ne,fD h4.ne.symm]
  have l1:z.im*w.re⁻¹=(w.re*z.im⁻¹)⁻¹:=by group
  have l3:=arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
  have l4:w.im*z.re⁻¹=(z.re*w.im⁻¹)⁻¹:=by group
  have l6:=arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
  have r1:z.im*z.re⁻¹=(z.re*z.im⁻¹)⁻¹:=by group
  have r3:=arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
  have r4:w.im*w.re⁻¹=(w.re*w.im⁻¹)⁻¹:=by group
  have r6:=arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
  ring_nf
  simp only [one_div,inv_I,mul_neg,neg_mul,I_sq,neg_neg,arctan_neg,ofReal_neg,
    sub_neg_eq_add]
  rw [l1,l3,l4,l6,r1,r3,r4,r6]
  ring_nf
  simp only [I_sq,ofReal_sub,ofReal_mul,ofReal_ofNat,ofReal_div,ofReal_neg,ofReal_one]
  ring_nf
theorem kJ
    (BJ:z.re≤w.re) (BK:z.im≤w.im)
    (jh:Rectangle z w∈𝓝 p) :
    aW (fun s=>c/(s-p)) z w=c:=by
  simp only [eo,uIoo_of_le BJ,uIoo_of_le BK,
    mem_reProdIm,mem_Ioo] at jh
  rw [aV.Rw,aW]
  have:1/(2*↑π* I)*(2* I*↑π*c)=c:=by
    field_simp
  rwa [xP]
  all_goals simp [*]
lemma jW {f g:ℂ→ℂ} {z w p A:ℂ}
    (BJ:z.re≤w.re) (BK:z.im≤w.im)
    (jh:Rectangle z w∈𝓝 p) (WC:dG g (Rectangle z w))
    (ND:Set.EqOn (f-fun s↦A/(s-p)) g (Rectangle z w \ {p})) :
    aW f z w=A:=by
  have LW:Set.EqOn f (g+(fun s↦A/(s-p))) (Rectangle z w \ {p}) :=
    fun s hs=>by rw [Pi.add_apply, ← ND hs,Pi.sub_apply,sub_add_cancel]
  have:Set.EqOn f (g+(fun s↦A/(s-p))) (aO z w) :=
    LW.mono <| Set.subset_sdiff.mpr
      ⟨cO z w,
        disjoint_singleton_right.mpr
          (bU jh)⟩
  rw [kP this]
  have t1:aY g z w:=
    WC.gR
  have t2:dG (fun s↦A/(s-p)) (Rectangle z w \ {p}) :=by
    apply DifferentiableOn.mono (t:={p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx=>by
          rw [sub_ne_zero]
          exact hx
    · rintro s ⟨_,hs⟩
      exact hs
  have t3:aY (fun s↦A/(s-p)) z w:=
    dG.rJ t2 jh
  rw [aW,aY.add t1 t3,smul_add]
  rw [WC.qw (by rfl),smul_zero,zero_add]
  exact kJ BJ BK jh
lemma DU {f:ℂ→ℂ} {p:ℂ}
    (Ov:f =O[𝓝[≠] p] (1:ℂ→ℂ)) :
    ∃ U∈𝓝 p,BddAbove (norm∘f '' (U \ {p})) :=by
  simp only [isBigO_iff,Pi.one_apply,one_mem,CStarRing.norm_of_mem_unitary,mul_one] at Ov
  obtain ⟨c,hc⟩:=Ov
  dsimp [Filter.Eventually,nhdsWithin] at hc
  rw [mem_inf_principal'] at hc
  obtain ⟨U,hU,⟨TP,XS⟩⟩:=mem_nhds_iff.mp hc
  use U
  constructor
  · exact IsOpen.mem_nhds TP XS
  · refine bddAbove_def.mpr ?_
    use c
    intro y hy
    simp only [Function.comp_apply,mem_image,Set.mem_sdiff,mem_singleton_iff] at hy
    obtain ⟨x,⟨x_in_U,Xf⟩,fxy⟩:=hy
    rw [← fxy]
    simpa [Xf] using hU x_in_U
end

-- Zeta23.dO.Xg
section
 public section
open Finset Interval MeasureTheory
variable {𝕜:Type*} [RCLike 𝕜] {f:ℝ→𝕜} {a b:ℝ}
noncomputable def B1 (x:ℝ) :ℝ:=x- ⌊x⌋₊ -1/2
lemma lP:AEStronglyMeasurable B1:=by
  unfold B1
  fun_prop
lemma LX {x:ℝ} (hx:0≤x) : |B1 x| ≤1/2:=by
  unfold B1
  refine abs_le.mpr ⟨?_,?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]
lemma qI (c:𝕜) (hab:a≤b) (h_int:IntervalIntegrable (deriv f) volume a b)
    (hf_diff: ∀ t∈Set.Icc a b,DifferentiableAt ℝ f t) :
    ∫ t in a..b,(t+c)*deriv f t=(b+c)*f b-(a+c)*f a- ∫ t in a..b,f t:=by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have: ∀ t∈[[a,b]],HasDerivAt (fun (t:ℝ)↦t+c) 1 t:=by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K:=𝕜)) using 1
    simp
  replace hf_diff:=fun t ht↦(hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp
lemma oK (ha:0≤a) (hab:a≤b) (h_cont:ContinuousOn (deriv f) [[a,b]]) :
    IntervalIntegrable (fun t↦deriv f t*B1 t) volume a b:=by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by first | exact RCLike.continuous_ofReal.comp_aestronglyMeasurable lP | exact (RCLike.continuous_ofReal.comp_aestronglyMeasurable lP).restrict) (M:=1/2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab,Set.mem_Icc] at hx
  norm_cast
  exact LX (by linarith)
lemma nZ (ha:0≤a) (hab:a≤b)
    (hf_diff: ∀ t∈Set.Icc a b,DifferentiableAt ℝ f t) (h_cont:ContinuousOn (deriv f) [[a,b]]) :
    ∫ t in a..b,deriv f t*(⌊t⌋₊ +1)=(b+1/2)*f b-(a+1/2)*f a-(∫ t in a..b,f t)- ∫ t in a..b,deriv f t*B1 t:=by
  calc
  _= ∫ t in a..b,(deriv f t*(t+1/2) -deriv f t*B1 t) :=by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _=(∫ t in a..b,deriv f t*(t+1/2))- ∫ t in a..b,deriv f t*B1 t:=by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (oK ha hab h_cont)
  _=_:=by
    conv=>lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [qI _ hab h_cont.intervalIntegrable hf_diff]
theorem lX (ha:0≤a) (hab:a≤b)
    (hf_diff: ∀ t∈Set.Icc a b,DifferentiableAt ℝ f t)
    (h_cont:ContinuousOn (deriv f) [[a,b]]) :
    ∑ k∈Ioc ⌊a⌋₊ ⌊b⌋₊,f k=
      f a*B1 a-f b*B1 b+(∫ t in a..b,f t)+ ∫ t in a..b,deriv f t*B1 t  :=by
  have:=sum_mul_eq_sub_sub_integral_mul (fun _↦1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one,sum_const,Nat.card_Icc,tsub_zero,nsmul_eq_mul,Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [nZ ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring
end

-- Zeta23.dO.ZJ
section
open Complex Topology Filter Interval Set Asymptotics
lemma gT (a x s:ℂ) :a/x^s=a*x^(-s) :=by
  rw [div_eq_mul_inv,cpow_neg]
lemma vW (x s:ℂ) :1/x^s=x^(-s) :=by
  convert gT 1 x s using 1; simp
lemma BL (a x s:ℝ) (hx:0≤x) :a/x^s=a*x^(-s) :=by
  rw [div_eq_mul_inv,Real.rpow_neg hx]
lemma gY {x y s:ℝ} (hx:0≤x) (hy:0≤y) :
    x^(-s)/y^(-s)=(y/x)^s:=by
  rw [div_eq_mul_inv,Real.rpow_neg hx,Real.rpow_neg hy,Real.div_rpow hy hx]; field_simp
lemma vX {x y s:ℝ} (hx:0≤x) (hy:0≤y) :
    x^s/y^s=(y/x)^(-s) :=by
  convert gY (s:= -s) hx hy using 1; simp only [neg_neg]
noncomputable def fF (N:ℕ) (s:ℂ) :ℂ:=
  (∑ n∈Finset.range (N+1),1/(n:ℂ)^s)+
  (- N^(1-s))/(1-s)+(- N^(-s))/2
      +s* ∫ x in Ioi (N:ℝ),(⌊x⌋ +1/2 -x)/(x:ℂ)^(s+1)
lemma qZ (N:ℕ) (s:ℂ) :(fF) N s=
    (∑ n∈Finset.range (N+1),1/(n:ℂ)^s)+
    ((- N^(1-s))/(1-s)+(- N^(-s))/2
      +s* ∫ x in Ioi (N:ℝ),(⌊x⌋ +1/2 -x)*(x:ℂ)^(-(s+1))) :=by
  simp_rw [fF,gT]; ring
lemma Real.nF (s:ℂ) {x:ℝ} (xpos:0<x) :
    DifferentiableAt ℝ (fun (x:ℝ)↦(x:ℂ)^s) x:=by
  apply DifferentiableAt.comp_ofReal (e:=fun z↦z^s)
  apply DifferentiableAt.cpow (by simp) (by simp) (by simp [xpos])
lemma Complex.JN {s:ℂ} {x:ℝ} (x_ne:x≠0) :
    1/(x:ℂ)^s=(x:ℂ)^(-s) :=by
  refine (eq_one_div_of_mul_eq_one_left ?_).symm
  rw [← cpow_add _ _ <| mod_cast x_ne,neg_add_cancel,cpow_zero]
lemma Ih {φ:ℝ→ℂ} {a b:ℝ} (apos:0≤a) (a_lt_b:a<b)
    (JO: ∀ x∈[[a,b]],HasDerivAt φ (deriv φ x) x)
    (zG:ContinuousOn (deriv φ) [[a,b]]) :
    ∑ n∈Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,φ n=
      (∫ x in a..b,φ x)+(⌊b⌋₊ +1/2 -b)*φ b-(⌊a⌋₊ +1/2 -a)*φ a
        - ∫ x in a..b,(⌊x⌋ +1/2 -x)*deriv φ x:=by
  rw [uIcc_of_le a_lt_b.le] at JO
  convert lX apos a_lt_b.le (fun t ht↦(JO t ht).differentiableAt) zG using 1
  unfold B1
  push_cast
  suffices ∫ (x:ℝ) in a..b,(↑⌊x⌋ +1/2 -↑x)*deriv φ x= -∫ (t:ℝ) in a..b,deriv φ t*(↑t-↑⌊t⌋₊ -1/2) by
    rw [this]
    ring_nf!
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx↦?_
  rw [uIcc_of_le a_lt_b.le,mem_Icc] at hx
  rw [← Int.natCast_floor_eq_floor (by linarith)]
  norm_cast
  push_cast
  ring
lemma kQ {a b:ℕ} (ha:a∈Ioo 0 b) {x:ℝ} (x_in:x∈[[(a:ℝ),b]]) :
    0<x:=by
  rw [uIcc_of_le (by exact_mod_cast ha.2.le),mem_Icc] at x_in
  linarith [(by exact_mod_cast ha.1:(0:ℝ)<a)]
lemma JQ {a b:ℕ} {s:ℂ} (kR:s≠1) (ha:a∈Ioo 0 b) :
    (∫ (x:ℝ) in a..b,1/(x:ℂ)^s)=
    (b^(1-s)-a^(1-s))/(1-s) :=by
  convert integral_cpow (a:=a) (b:=b) (r:= -s) ?_ using 1
  · refine intervalIntegral.integral_congr fun x hx↦JN ?_
    exact (kQ ha hx).ne'
  · norm_cast; ring_nf
  · right; refine ⟨(by grind),?_⟩
    exact fun hx↦(lt_self_iff_false 0).mp <| kQ ha hx
lemma DX {s:ℂ} {x:ℝ} (xpos:0<x) :
    HasDerivAt (fun (t:ℝ)↦1/(t:ℂ)^s) (deriv (fun (t:ℝ)↦1/(t:ℂ)^s) x) x:=by
  exact hasDerivAt_deriv_iff.mpr <|
    DifferentiableAt.div (differentiableAt_const _)
      (Real.nF s xpos) (by simp [cpow_eq_zero_iff,xpos.ne'])
lemma qz {s:ℂ} (gI:s≠0) {x:ℝ} (xpos:0<x) :
    deriv (fun (t:ℝ)↦1/(t:ℂ)^s) x=(fun (x:ℝ)↦ -s*(x:ℂ)^(-(s+1))) x:=by
  let r:= -s-1
  have AH:r+1≠0:=fun hr↦by simp [neg_ne_zero.mpr gI,r] at hr
  have TQ:r≠ -1:=fun hr↦(hr ▸ AH) <| by norm_num
  have Ow:=hasDerivAt_ofReal_cpow_const' xpos.ne' TQ
  have:=Ow.deriv ▸ deriv_const_mul (-s) (Ow).differentiableAt
  convert! this using 2
  · ext y
    by_cases y_zero:(y:ℂ)=0
    · simp only [y_zero,ne_eq,gI,not_false_eq_true,zero_cpow,div_zero,
      AH,zero_div,mul_zero]
    · have:(y:ℂ)^s≠0:=fun hy↦y_zero ((cpow_eq_zero_iff _ _).mp hy).1
      simp only [one_div,sub_add_cancel,cpow_neg,neg_mul,r]
      field_simp
  · simp only [r]
    ring_nf
lemma xQ {s:ℂ} (gI:s≠0) {a b:ℕ} (ha:a∈Ioo 0 b) :
    ContinuousOn (deriv (fun (t:ℝ)↦1/(t:ℂ)^s)) [[a,b]]:=by
  have:EqOn _ (fun (t:ℝ)↦ -s*(t:ℂ)^(-(s+1))) [[a,b]]:=
    fun x hx↦qz gI <| kQ ha hx
  refine continuous_ofReal.continuousOn.cpow_const ?_ |>.const_smul (c:= -s) |>.congr this
  exact fun x hx↦ofReal_mem_slitPlane.mpr <| kQ ha hx
lemma Ox {a b:ℕ} {s:ℂ} (kR:s≠1) (gI:s≠0) (ha:a∈Ioo 0 b) :
    ∑ n∈Finset.Ioc a b,1/(n:ℂ)^s=
    (b^(1-s)-a^(1-s))/(1-s)+1/2*(1/b^(s))-1/2*(1/a^s)
      +s* ∫ x in a..b,(⌊x⌋ +1/2 -x)*(x:ℂ)^(-(s+1)) :=by
  let φ:=fun (x:ℝ)↦1/(x:ℂ)^s
  let φ':=fun (x:ℝ)↦ -s*(x:ℂ)^(-(s+1))
  have xpos: ∀ x∈[[(a:ℝ),b]],0<x:=fun x hx↦kQ ha hx
  have JO: ∀ x∈[[(a:ℝ),b]],HasDerivAt φ (deriv φ x) x:=
    fun x hx↦DX (xpos x hx)
  have Ra: ∀ x∈[[(a:ℝ),b]],deriv φ x=φ' x:=by
    exact fun x hx↦qz gI (xpos x hx)
  have zG:ContinuousOn (deriv φ) [[a,b]]:=xQ gI ha
  convert Ih (by linarith) (by exact_mod_cast ha.2) JO zG using 1
  · congr <;> simp only [Nat.floor_natCast]
  · rw [Nat.floor_natCast,Nat.floor_natCast, ← intervalIntegral.integral_const_mul]
    simp_rw [mul_div, ← mul_div,φ,JQ kR ha]
    conv=>rhs; rw [sub_eq_add_neg]
    congr; any_goals norm_cast; simp only [one_div,add_sub_cancel_left]
    rw [← intervalIntegral.integral_neg,intervalIntegral.integral_congr]
    simp only [φ,one_div] at Ra
    intro x hx; simp_rw [Ra x hx,φ']; ring_nf
lemma oO {a b x:ℝ} (apos:0<a) (hx:x∈Icc a b) :0<x:=
  lt_of_lt_of_le apos hx.1
lemma qJ {a b x:ℝ} (apos:0<a) (a_lt_b:a<b) (hx:x∈[[a,b]]) :0<x:=
  lt_of_lt_of_le apos (uIcc_of_le a_lt_b.le ▸ hx).1
lemma LY {a b:ℝ} {c:ℝ} (apos:0<a) (a_lt_b:a<b)
    (h:c≠0 ∧ 0∉[[a,b]]) :
    ∫ (x:ℝ) in a..b,1/x^(c+1)=(a^(-c)-b^(-c))/c:=by
  rw [(by ring:(a^(-c)-b^(-c))/c=(b^(-c)-a^(-c))/(-c))]
  have:=integral_rpow (a:=a) (b:=b) (r:= -c-1) (Or.inr ⟨by simp [h.1],h.2⟩)
  simp only [sub_add_cancel] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro x hx
  have:0≤x:=(qJ apos a_lt_b hx).le
  simp [BL _ _ _ this,sub_eq_add_neg,add_comm]
lemma lH (x:ℝ) : ‖(⌊x⌋ +1/2 -x)‖ ≤1/2:=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]),(by linarith [Int.floor_le x])⟩
lemma JR (x:ℝ) (hx:0<x) (s:ℂ) :
      ‖(⌊x⌋ +1/2 -(x:ℝ))/(x:ℂ)^(s+1)‖ =
      ‖⌊x⌋ +1/2 -x‖ /x^((s+1).re) :=by
  simp_rw [norm_div,Complex.norm_cpow_eq_rpow_re_of_pos hx, ← norm_real]
  simp
lemma LZ {a b:ℝ} (apos:0<a) (a_lt_b:a<b) {s:ℂ} :
  ∫ (x:ℝ) in a..b, ‖(↑⌊x⌋ +(1:ℝ)/2 -↑x)/(x:ℂ)^(s+1)‖ =
    ∫ (x:ℝ) in a..b, |⌊x⌋ +1/2 -x| /x^(s+1).re:=by
  apply intervalIntegral.integral_congr
  exact fun x hx↦JR x (qJ apos a_lt_b hx) s
lemma JT {a b:ℝ} (apos:0<a) {s:ℂ} (x:ℝ)
  (h:x∈Icc a b) : |↑⌊x⌋ +1/2 -x| /x^(s.re+1)≤1/x^(s.re+1) :=by
  apply div_le_div_of_nonneg_right _ _
  · exact le_trans (lH x) (by norm_num)
  · apply Real.rpow_nonneg <| le_of_lt (oO apos h)
lemma yT {a b:ℝ} (apos:0<a) (a_lt_b:a<b) {s:ℂ} (kL:0<s.re) :
  IntervalIntegrable (fun u↦1/u^(s.re+1)) MeasureTheory.volume a b:=by
  refine continuousOn_const.div ?_ ?_ |>.intervalIntegrable_of_Icc (le_of_lt a_lt_b)
  · exact continuousOn_id.rpow_const fun x hx↦Or.inl (ne_of_gt <| oO apos hx)
  · exact fun x hx h↦by rw [Real.rpow_eq_zero] at h <;> linarith [oO apos hx]
open MeasureTheory in
lemma pU:Measurable fun (u:ℝ)↦↑⌊u⌋ +1/2 -u:=by
  refine Measurable.add ?_ measurable_const |>.sub measurable_id
  exact Measurable.comp (by exact fun _ _↦trivial) Int.measurable_floor
open MeasureTheory in
lemma JX {a b:ℝ} {s:ℂ} :
    let g:ℝ→ℝ:=fun u↦ |↑⌊u⌋ +1/2 -u| /u^(s.re+1);
    AEStronglyMeasurable g
      (Measure.restrict volume (Ι a b)) :=by
  intro
  refine (Measurable.div ?_ <| measurable_id.pow_const _).aestronglyMeasurable
  exact _root_.continuous_abs.measurable.comp pU
lemma JY {a b:ℝ} (apos:0<a) (a_lt_b:a<b) {s:ℂ} (kL:0<s.re) :
  IntervalIntegrable (fun u↦ |↑⌊u⌋ +1/2 -u| /u^(s.re+1)) MeasureTheory.volume a b:=by
  set g:ℝ→ℝ:=(fun u↦ |↑⌊u⌋ +1/2 -u| /u^(s.re+1))
  apply yT apos a_lt_b kL |>.mono_fun JX ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs,one_div,norm_inv,abs_div,_root_.abs_abs]
  conv=>rw [div_eq_mul_inv, ← one_div]; rhs; rw [← one_mul |x^(s.re+1)|⁻¹]
  refine mul_le_mul ?_ (le_refl _) (by simp) <| by norm_num
  exact le_trans (lH x) <| by norm_num
lemma Me {a b:ℝ} (apos:0<a) (a_lt_b:a<b) {s:ℂ} (kL:0<s.re) :
  ∫ (x:ℝ) in a..b, |⌊x⌋ +1/2 -x| /x^(s.re+1)≤
    ∫ (x:ℝ) in a..b,1/x^(s.re+1) :=by
  apply intervalIntegral.integral_mono_on (le_of_lt a_lt_b) ?_ ?_
  · exact JT apos
  · exact JY apos a_lt_b kL
  · exact yT apos a_lt_b kL
lemma NR {a b:ℝ} (apos:0<a) (a_lt_b:a<b) {s:ℂ} (kL:0<s.re) :
    ∫ x in a..b, ‖(⌊x⌋ +1/2 -x)/(x:ℂ)^(s+1)‖ ≤
      (a^(-s.re)-b^(-s.re))/s.re:=by
  calc
    _= ∫ x in a..b, |(⌊x⌋ +1/2 -x)| /x^(s+1).re:=LZ apos a_lt_b
    _≤ ∫ x in a..b,1/x^(s.re+1) :=Me apos a_lt_b kL
    _=(a^(-s.re)-b^(-s.re))/s.re:=?_
  refine LY (c:=s.re) apos a_lt_b ⟨ne_of_gt kL,?_⟩
  exact fun h↦(lt_self_iff_false 0).mp <| qJ apos a_lt_b h
lemma Finset.Ry (M N:ℕ) :Finset.Ioc N M=Finset.Ico (N+1) (M+1) :=by
  ext a; simp only [Finset.mem_Ioc,Finset.mem_Ico]; constructor <;> intro ⟨h₁,h₂⟩ <;> omega
lemma zH {N:ℕ} {f:ℕ→ℂ} (hf:Summable f) :
    Tendsto (fun (k:ℕ)↦ ∑ n∈Finset.Ico N k,f n) atTop (𝓝 (∑' (n:ℕ),f (n+N))) :=by
  have:=Summable.hasSum_iff_tendsto_nat hf (m:= ∑' (n:ℕ),f n) |>.mp hf.hasSum
  have const:=tendsto_const_nhds (α:=ℕ) (x:= ∑ i∈Finset.range N,f i) (f:=atTop)
  have:=Filter.Tendsto.sub this const
  rw [← hf.sum_add_tsum_nat_add N,add_comm,add_sub_cancel_right] at this
  apply this.congr'
  filter_upwards [Filter.mem_atTop (N+1)]
  intro M hM
  rw [Finset.sum_Ico_eq_sub]
  linarith
lemma Complex.Oy {s:ℂ} (jD:1<s.re) :
    Tendsto (fun (x:ℕ)↦(x:ℂ)^(1-s)) atTop (𝓝 0) :=by
  have JZ:(1-s).re≠0:=by simp only [sub_re,one_re]; linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (JZ)]
  rw [(by simp only [sub_re,one_re,neg_sub]:(1-s).re= -(s-1).re)]
  apply (tendsto_rpow_neg_atTop _).comp tendsto_natCast_atTop_atTop; simp [jD]
lemma Complex.Ij {s:ℂ} (hs:0<s.re) :
    Tendsto (fun (x:ℕ)↦((x:ℂ)^s)⁻¹) atTop (𝓝 0) :=by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_inv,Complex.norm_natCast_cpow_of_re_ne_zero _ <| ne_of_gt hs]
  apply Filter.Tendsto.inv_tendsto_atTop
  exact (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
lemma Dd: ∃ C, ∀ (x:ℝ), ‖⌊x⌋ +1/2 -x‖ ≤C:=by
  use 1/2; exact lH
lemma Oz {N:ℕ} {s:ℂ} (jD:1<s.re) :
    Tendsto (fun k↦ ∑ n∈Finset.Ioc N k,1/(n:ℂ)^s) atTop
    (𝓝 (∑' (n:ℕ),1/(n+N+1:ℂ)^s)) :=by
  let f:=fun (n:ℕ)↦1/(n:ℂ)^s
  have hf:=summable_one_div_nat_cpow.mpr jD
  simp_rw [Finset.Ry]
  convert zH (f:=fun n↦f (n+1)) (N:=N) ?_ using 1
  · ext k
    rw [Finset.sum_Ico_add']
  · congr; ext n; simp only [one_div,Nat.cast_add,Nat.cast_one,f]
  · rwa [summable_nat_add_iff (k:=1)]
lemma fq {N:ℕ} (N_pos:0<N) {s:ℂ} (jD:0<s.re) :
    MeasureTheory.IntegrableOn (fun (x:ℝ)↦(⌊x⌋ +1/2 -x)*(x:ℂ)^(-(s+1))) (Ioi N)
    MeasureTheory.volume:=by
  obtain ⟨c,hc⟩:=Dd
  apply MeasureTheory.Integrable.bdd_mul (c:=c) ?_ ?_
  · apply MeasureTheory.ae_of_all
    convert hc; simp only [← Complex.norm_real]; simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [jD])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (by exact fun _ _↦trivial) Int.measurable_floor
lemma OC {N:ℕ} (N_pos:0<N) {s:ℂ} (jD:1<s.re) :
    ∑' (n:ℕ),1/(n+N+1:ℂ)^s=
    (- N^(1-s))/(1-s)-N^(-s)/2
      +s* ∫ x in Ioi (N:ℝ),(⌊x⌋ +1/2 -x)*(x:ℂ)^(-(s+1)) :=by
  have gI:s≠0:=fun hs↦by linarith [zero_re ▸ hs ▸ jD]
  have kR:s≠1:=fun hs↦(lt_self_iff_false _).mp <| one_re ▸ hs ▸ jD
  apply tendsto_nhds_unique (X:=ℂ) (Y:=ℕ) (l:=atTop)
    (f:=fun k↦((k:ℂ)^(1-s)-(N:ℂ)^(1-s))/(1-s)+
      1/2*(1/↑k^s)-1/2*(1/↑N^s)
      +s* ∫ (x:ℝ) in (N:ℝ)..k,(⌊x⌋ +1/2 -x)*(x:ℂ)^(-(s+1)))
    (b:=(- N^(1-s))/(1-s)-N^(-s)/2
      +s* ∫ x in Ioi (N:ℝ),(⌊x⌋ +1/2 -x)*(x:ℂ)^(-(s+1)))
  · apply Filter.Tendsto.congr'
      (f₁:=fun (k:ℕ)↦ ∑ n∈Finset.Ioc N k,1/(n:ℂ)^s) (l₁:=atTop)
    · apply Filter.eventually_atTop.mpr
      use N+1
      intro k hk
      exact Ox (a:=N) (b:=k) kR gI ⟨N_pos,hk⟩
    · exact Oz jD
  · apply (Tendsto.sub ?_ ?_).add (Tendsto.const_mul _ ?_)
    · rw [(by ring: -↑N^(1-s)/(1-s)=(0-↑N^(1-s))/(1-s)+0)]
      apply Oy jD |>.sub_const _ |>.div_const _ |>.add
      simp_rw [mul_comm_div,one_mul,one_div,(by congr; ring:𝓝 (0:ℂ)=𝓝 ((0:ℂ)/2))]
      apply Tendsto.div_const <| Ij (by positivity)
    · simp_rw [mul_comm_div,one_mul,one_div,cpow_neg]; exact tendsto_const_nhds
    · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a:=N)
        (b:=(fun (n:ℕ)↦(n:ℝ)))
        (fq N_pos <| by positivity) tendsto_natCast_atTop_atTop
open MeasureTheory in
lemma Dh (N:ℕ) (Npos:1≤N) {σ t:ℝ} (kL:0<σ) :
    ‖∫ x in Ioi (N:ℝ),(⌊x⌋ +1/2 -x)/(x:ℂ)^((σ+t* I)+1)‖
    ≤N^(-σ)/σ:=by
  apply le_trans (by apply norm_integral_le_integral_norm)
  apply le_of_tendsto (x:=atTop (α:=ℝ)) (f:=fun (t:ℝ)↦ ∫ (x:ℝ) in N..t,
    ‖(⌊x⌋ +1/2 -x)/(x:ℂ)^(σ+t* I+1)‖) ?_ ?_
  · apply intervalIntegral_tendsto_integral_Ioi (μ:=volume) (l:=atTop) (b:=id)
      (f:=fun (x:ℝ)↦ ‖(⌊x⌋ +1/2 -x)/(x:ℂ)^(σ+t* I+1)‖) N ?_ ?_ |>.congr' ?_
    · filter_upwards [Filter.mem_atTop ((N:ℝ))]
      intro u hu
      simp only [id_eq,intervalIntegral.integral_of_le hu,norm_div]
      apply setIntegral_congr_fun (by simp)
      intro x hx; beta_reduce
      iterate 2 (rw [norm_cpow_eq_rpow_re_of_pos (by linarith [hx.1])])
      simp
    · apply IntegrableOn.integrable ?_ |>.norm
      convert! fq (s:=σ+t* I) Npos (by simp [kL]) using 1
      simp_rw [div_eq_mul_inv,cpow_neg]
    · exact fun ⦃_⦄ a↦a
  · filter_upwards [mem_atTop (N+1:ℝ)] with t ht
    have:(N^(-σ)-t^(-σ))/σ≤N^(-σ)/σ:=
      div_le_div_iff_of_pos_right kL |>.mpr (by simp [Real.rpow_nonneg (by linarith)])
    apply le_trans ?_ this
    convert! NR (a:=N) (b:=t) (by positivity) (by linarith) ?_ <;> simp [kL]
lemma DY (N:ℕ) (Npos:1≤N) {σ t:ℝ} (hσ:σ∈Ioc 0 2) (ht:2≤ |t|) :
    ‖(σ+t* I)* ∫ x in Ioi (N:ℝ),(⌊x⌋ +1/2 -x)/(x:ℂ)^((σ+t* I)+1)‖
    ≤2* |t| *N^(-σ)/σ:=by
  rw [norm_mul,mul_div_assoc]
  rw [Set.mem_Ioc] at hσ
  apply mul_le_mul ?_ (Dh N Npos hσ.1) (norm_nonneg _) (by positivity)
  refine le_trans (by apply norm_add_le) ?_
  simp only [Complex.norm_of_nonneg hσ.1.le,Complex.norm_mul,norm_real,Real.norm_eq_abs,norm_I,
    mul_one]
  linarith [hσ.2]
lemma Ka:IsOpen {z:ℂ | z≠1 ∧ 0<z.re} :=by
  refine IsOpen.inter isOpen_ne ?_
  exact isOpen_lt (g:=fun (z:ℂ)↦z.re) (by continuity) (by continuity)
open MeasureTheory in
lemma lQ {r:ℝ} (rneg:r<0) {N:ℕ} (Npos:0<N) :
    IntegrableOn (fun (x:ℝ)↦ ‖x^(r-1)‖ * ‖Real.log x‖) <| Ioi N:=by
  apply IntegrableOn.mono_set (hst:=Set.Ioi_subset_Ici <| le_refl (N:ℝ))
  apply LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g:=fun x↦x^(r/2 -1))
  · apply ContinuousOn.abs ?_ |>.mul ?_ |>.locallyIntegrableOn (by simp)
    · apply ContinuousOn.rpow (by fun_prop) (by fun_prop)
      intro x hx; left; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
    · apply continuous_id.continuousOn.log ?_ |>.abs
      intro x hx; simp only [id_eq]; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
  · have:=isLittleO_log_rpow_atTop (r:= -r/2) (by linarith) |>.isBigO
    rw [Asymptotics.isBigO_iff_eventually,Filter.eventually_atTop] at this
    obtain ⟨C,hC⟩:=this
    have hh:=hC C (by simp)
    rw [Asymptotics.isBigO_atTop_iff_eventually_exists]
    have:=Filter.eventually_atTop.mp hh
    obtain ⟨x₀,hx₀ ⟩:=this
    filter_upwards [hh,Filter.mem_atTop x₀,Filter.mem_atTop 1]
    intro x hx adO x_pos
    use C
    intro y hy
    simp only [norm_mul,Real.norm_eq_abs,_root_.abs_abs]
    simp only [Real.norm_eq_abs] at hx
    have y_pos:0<y:=by linarith
    have:y^(r/2 -1)=y^(r-1)*y^(-r/2) :=by
      rw [← Real.rpow_add y_pos]; ring_nf
    rw [this,abs_mul]
    have abk:y≥x₀:=by linarith
    have:=hx₀ y abk
    simp only [Real.norm_eq_abs] at this
    rw [← mul_assoc,mul_comm C,mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbc:=this) (a:= |y^(r-1)|) (ha:=by simp)
  · have:=integrableOn_Ioi_rpow_iff (s:=r/2 -1) (t:=N) (by simp [Npos]) |>.mpr
      (by linarith [rneg])
    exact integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp this |>.1
open MeasureTheory in
lemma pW {N:ℕ} (Npos:0<N) {s:ℂ} (jD:0<s.re) :
    IntegrableOn (fun (x:ℝ)↦(⌊x⌋ +1/2 -x)*(x:ℂ)^(-(s+1))*(-Real.log x)) (Ioi N)
    volume:=by
  simp_rw [mul_assoc]
  obtain ⟨c,hc⟩:=Dd
  apply Integrable.bdd_mul (c:=c) ?_ ?_ ?_
  · simp only [neg_add_rev,mul_neg,add_comm, ← sub_eq_add_neg]
    apply integrable_norm_iff ?_ |>.mp ?_ |>.neg
    · apply ContinuousOn.mul ?_ ?_ |>.aestronglyMeasurable (by simp)
      · intro x hx
        apply ContinuousWithinAt.cpow ?_ continuous_const.continuousWithinAt ?_
        · exact RCLike.continuous_ofReal.continuousWithinAt
        · simp only [ofReal_mem_slitPlane]; linarith [mem_Ioi.mp hx]
      · apply RCLike.continuous_ofReal.continuousOn.comp ?_ (mapsTo_image _ _)
        refine continuous_id.continuousOn.log ?_
        intro x hx; simp only [id_eq]; linarith [mem_Ioi.mp hx]
    · simp only [norm_mul,norm_real]
      have:=lQ (r:= -s.re) (by linarith) Npos
      apply IntegrableOn.congr_fun this ?_ (by simp)
      intro x hx
      simp only [mul_eq_mul_right_iff,norm_eq_zero,Real.log_eq_zero]
      left
      have xpos:0<x:=by linarith [mem_Ioi.mp hx]
      simp [norm_cpow_eq_rpow_re_of_pos xpos,Real.abs_rpow_of_nonneg xpos.le,
        abs_eq_self.mpr xpos.le]
  · apply Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (fun _ _↦trivial) Int.measurable_floor
  · apply MeasureTheory.ae_of_all
    convert hc with _ x; simp only [← Complex.norm_real]; simp
open MeasureTheory in
lemma vY {N:ℕ} (Npos:0<N) {s:ℂ} (hs:s∈{s | 0<s.re}) :
  HasDerivAt (fun z↦ ∫ x in Ioi (N:ℝ),(⌊x⌋ +1/2 -x)*(x:ℂ)^(-z-1))
    (∫ x in Ioi (N:ℝ),(⌊x⌋ +1/2 -x)*(x:ℂ)^(- s-1)*(- Real.log x)) s:=by
  simp only [mem_setOf_eq] at hs
  set f:ℝ→ℂ:=fun x↦(⌊x⌋ :ℂ)+1/2 -x
  set F:ℂ→ℝ→ℂ:=fun s x↦(x:ℂ)^(- s-1)*f x
  set F':ℂ→ℝ→ℂ:=fun s x↦(x:ℂ)^(- s-1)*(- Real.log x)*f x
  set ε:=s.re/2
  have ε_pos:0<ε:=by aesop
  set bound:ℝ→ℝ:=fun x↦ |x^(- s.re/2 -1)| * |Real.log x|
  let μ:Measure ℝ:=volume.restrict (Ioi (N:ℝ))
  have hF_meas: ∀ᶠ (z:ℂ) in 𝓝 s,AEStronglyMeasurable (F z) μ:=by
    have:{z:ℂ | 0<z.re}∈𝓝 s:=by
      rw [mem_nhds_iff]
      refine ⟨{z | 0<z.re},fun ⦃a⦄ a↦a,isOpen_lt continuous_const Complex.continuous_re,hs⟩
    filter_upwards [this] with z hz
    convert! fq Npos hz |>.aestronglyMeasurable using 1
    simp only [F,f]; ext x; ring_nf
  have hF_int:Integrable (F s) μ:=by
    convert! fq Npos hs |>.integrable using 1
    simp only [F,f]; ext x; ring_nf
  have hF'_meas:AEStronglyMeasurable (F' s) μ:=by
    convert! pW Npos hs |>.aestronglyMeasurable using 1
    simp only [F',f]; ext x; ring_nf
  have Kd:(Ioi (N:ℝ))⊆{x | 1<x} :=
      fun x hx↦lt_of_le_of_lt (by simp only [Nat.one_le_cast]; omega) <| mem_Ioi.mp hx
  have GI:MeasurableSet {x:ℝ | 1<x} :=(isOpen_lt' 1).measurableSet
  have OD:
    ∀ᵐ (x:ℝ) ∂volume.restrict {x | 1<x}, ∀ z∈Metric.ball s ε, ‖F' z x‖ ≤bound x:=by
    filter_upwards [self_mem_ae_restrict GI] with x hx
    intro z hz
    simp only [F',f,bound]
    calc _= ‖(x:ℂ)^(-z-1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ +1/2 -x)‖ :=by
            simp only [mul_neg,one_div,neg_mul,norm_neg,norm_mul,norm_real,Real.norm_eq_abs,
              ← (by simp:(((⌊x⌋ +2⁻¹-x) :ℝ) :ℂ)=(⌊x⌋ :ℂ)+2⁻¹-↑x),
              Complex.norm_real]
         _= ‖x^(-z.re-1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ +1/2 -x)‖ :=?_
         _= |x^(-z.re-1)| * |(Real.log x)| * |(⌊x⌋ +1/2 -x)| :=by simp
         _≤_:=?_
    · congr! 2
      simp only [Real.norm_eq_abs,norm_cpow_eq_rpow_re_of_pos (by linarith),
        sub_re,neg_re,one_re]
      apply abs_eq_self.mpr ?_ |>.symm
      positivity
    · rw [mul_comm, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right ?_ <| abs_nonneg _
      simp only [Metric.mem_ball,ε,Complex.dist_eq] at hz
      apply le_trans (b:=1* |x^(-z.re-1)|)
      · apply mul_le_mul_of_nonneg_right (le_trans (lH _) (by norm_num)) <| abs_nonneg _
      · simp_rw [one_mul,Real.abs_rpow_of_nonneg (by linarith:0≤x)]
        apply Real.rpow_le_rpow_of_exponent_le <| le_abs.mpr (by left; exact hx.le)
        have:=abs_le.mp <| le_trans (abs_re_le_norm (z-s)) hz.le
        simp only [sub_re,neg_le_sub_iff_le_add,tsub_le_iff_right] at this
        linarith [this.1]
  have h_bound: ∀ᵐ x ∂μ, ∀ z∈Metric.ball s ε, ‖F' z x‖ ≤bound x:=by
    apply ae_restrict_of_ae_restrict_of_subset Kd
    exact OD
  have bound_integrable:Integrable bound μ:=by
    simp only [bound]
    convert! lQ (r:= -s.re/2) (by linarith) Npos using 0
  have h_diff: ∀ᵐ x ∂μ, ∀ z∈Metric.ball s ε,HasDerivAt (fun w↦F w x) (F' z x) z:=by
    simp only [F,F',f]
    apply ae_restrict_of_ae_restrict_of_subset Kd
    filter_upwards [OD,self_mem_ae_restrict GI] with x _ abl
    intro z hz
    convert! HasDerivAt.mul_const (c:=fun (w:ℂ)↦(x:ℂ)^(-w-1))
      (c':=(x:ℂ)^(-z-1)* -Real.log x) (d:=(⌊x⌋ :ℝ)+1/2 -x) ?_ using 1
    convert! HasDerivAt.comp (h:=fun w↦ -w-1) (h':= -1) (h₂:=fun w↦x^w)
      (h₂':=x^(-z-1)*Real.log x) (x:=z) ?_ ?_ using 0
    · simp only [mul_neg,mul_one]; congr! 2
    · convert! HasDerivAt.const_cpow (c:=(x:ℂ)) (f:=fun w↦w) (f':=1) (x:= -z-1)
        (hasDerivAt_id _) ?_ using 1
      · simp only [mul_one,mul_eq_mul_left_iff,cpow_eq_zero_iff,ofReal_eq_zero,ne_eq]
        left
        rw [Complex.ofReal_log]
        linarith
      · right
        intro h
        simp only [Metric.mem_ball,ε,Complex.dist_eq,
          neg_eq_iff_eq_neg.mp <| sub_eq_zero.mp h] at hz
        have:=(abs_le.mp <| le_trans (abs_re_le_norm (-1-s)) hz.le).1
        simp only [sub_re,neg_re,one_re,neg_le_sub_iff_le_add,le_neg_add_iff_add_le] at this
        linarith
    · apply hasDerivAt_id _ |>.neg |>.sub_const
  convert! (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=F) (F':=F') (x₀:=s)
    (s:=Metric.ball s ε) (bound:=bound) (μ:=μ) (Metric.ball_mem_nhds s ε_pos)
    hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2 using 3
  · ext a; simp only [one_div,F,f]; ring_nf
  · simp only [one_div,mul_neg,neg_mul,neg_inj,F',f]; ring_nf
noncomputable def TU (N:ℕ) (s:ℂ) :ℂ:=
    ∑ n∈Finset.range (N+1), -1/(n:ℂ)^s*Real.log n+
    (-N^(1-s)/(1-s)^2+Real.log N*N^(1-s)/(1-s))+
    Real.log N*N^(-s)/2+
    (1*(∫ x in Ioi (N:ℝ),(⌊x⌋ +1/2 -x)*(x:ℂ)^(- s-1))+
    s* ∫ x in Ioi (N:ℝ),(⌊x⌋ +1/2 -x)*(x:ℂ)^(- s-1)*(- Real.log x))
lemma tW {N:ℕ} (Npos:0<N) (s:ℂ) :
    HasDerivAt (fun x:ℂ↦ -(N:ℂ)^(-x)/2) (-((- Real.log N)*(N:ℂ)^(-s))/2) s:=by
  convert! hasDerivAt_neg' s |>.const_cpow (c:=N) (by aesop) |>.neg |>.div_const _ using 1
  simp [mul_comm]
lemma vZ (N:ℕ) {z:ℂ} (z_ne_zero:z≠0) :
    HasDerivAt (fun z↦ -(N:ℂ)^z/z)
      (((N:ℂ)^z/z^2)-(Real.log N*N^z/z)) z:=by
  simp_rw [div_eq_mul_inv]
  convert! HasDerivAt.mul (c:=fun z↦ -(N:ℂ)^z) (d:=fun z↦z⁻¹)
    (c':= -(N:ℂ)^z*Real.log N)
    (d':= -(z^2)⁻¹) ?_ ?_ using 1
  · simp only [natCast_log,neg_mul,mul_neg,neg_neg]
    ring_nf
  · simp only [natCast_log,neg_mul]
    apply HasDerivAt.neg
    convert! HasDerivAt.const_cpow (c:=(N:ℂ)) (f:=id) (f':=1) (x:=z) (hasDerivAt_id z)
      (by simp [z_ne_zero]) using 1
    simp only [id_eq,mul_one]
  · exact hasDerivAt_inv z_ne_zero
lemma Kh {N:ℕ} (Npos:0<N) {s:ℂ} (Mh:0<s.re) (kR:s≠1) :
    HasDerivAt ((fF) N) (TU N s) s:=by
  unfold fF TU
  apply HasDerivAt.fun_sum ?_ |>.add ?_ |>.add ?_ |>.add ?_
  · intro n _
    convert! hasDerivAt_neg' s |>.const_cpow (c:=n) (by aesop) using 1
    all_goals (ring_nf; simp [cpow_neg])
  · convert! HasDerivAt.comp (h₂:=fun z↦ -(N:ℂ)^z/z) (h:=fun z↦1-z) (h':= -1)
      (h₂':=((N:ℂ)^(1-s)/(1-s)^2 -Real.log (N:ℝ)*(N:ℂ)^(1-s)/(1-s)))
      (x:=s) ?_ ?_ using 1
    · ring_nf
    · exact vZ N (by rw [sub_ne_zero]; exact kR.symm)
    · convert! hasDerivAt_const s _ |>.sub (hasDerivAt_id _) using 1; simp
  · convert! tW Npos s using 1; simp only [natCast_log,neg_mul,neg_neg]
  · simp_rw [gT,neg_add, ← sub_eq_add_neg]
    convert! hasDerivAt_id s |>.mul <| vY Npos Mh using 1
lemma rO {N:ℕ} (N_pos:0<N) :
    dG ((fF) N) {s:ℂ | s≠1 ∧ 0<s.re} :=
  fun _ ⟨hs₁,hs₂⟩↦(Kh N_pos hs₂ hs₁).differentiableAt.differentiableWithinAt
lemma tZ:
    dG (riemannZeta) {s:ℂ | s≠1} :=by
  intro z hz
  simp only [mem_setOf_eq] at hz
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt
lemma Dv:IsPathConnected {z:ℂ | z≠1 ∧ 0<z.re} :=by
  use (2:ℂ)
  constructor
  · simp
  intro w hw; simp only [ne_eq,mem_setOf_eq] at hw
  by_cases OE:w.im=0
  · apply JoinedIn.trans (y:=1+I)
    · let f:ℝ→ℂ:=fun t↦(1+I)*t+2*(1-t)
      have cont:Continuous f:=by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval,ne_eq,image_subset_iff,preimage_setOf_eq,add_re,mul_re,one_re,
        I_re,add_zero,ofReal_re,one_mul,add_im,one_im,I_im,zero_add,ofReal_im,mul_zero,
        sub_zero,re_ofNat,sub_re,im_ofNat,sub_im,sub_self,f]
      intro x hx; simp only [mem_Icc] at hx
      refine ⟨?_,by linarith⟩
      intro h
      rw [Complex.ext_iff] at h; simp [(by apply And.right; simpa [OE] using h:x=0)] at h
    · let f:ℝ→ℂ:=fun t↦w*t+(1+I)*(1-t)
      have cont:Continuous f:=by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval,ne_eq,image_subset_iff,preimage_setOf_eq,add_re,mul_re,
        ofReal_re,ofReal_im,mul_zero,sub_zero,one_re,I_re,add_zero,sub_re,one_mul,add_im,
        one_im,I_im,zero_add,sub_im,sub_self,f]
      intro x hx; simp only [mem_Icc] at hx
      simp only [mem_setOf_eq]
      constructor
      · intro h
        refine hw.1 ?_
        rw [Complex.ext_iff] at h
        have:x=1:=by linarith [(by apply And.right; simpa [OE] using h:1-x=0)]
        rw [Complex.ext_iff,one_re,one_im]; exact ⟨by simpa [this,OE] using h,OE⟩
      · by_cases hxx:x=0
        · simp only [hxx]; linarith
        · have:0<x:=lt_of_le_of_ne hx.1 (Ne.symm hxx)
          have:0≤1-x:=by linarith
          have:=hw.2
          positivity
  · let f:ℝ→ℂ:=fun t↦w*t+2*(1-t)
    have cont:Continuous f:=by continuity
    apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
    simp only [unitInterval,ne_eq,image_subset_iff,preimage_setOf_eq,add_re,mul_re,ofReal_re,
      ofReal_im,mul_zero,sub_zero,re_ofNat,sub_re,one_re,im_ofNat,sub_im,one_im,sub_self,
      f]
    intro x hx; simp only [mem_Icc] at hx
    constructor
    · intro h
      rw [Complex.ext_iff] at h;
      simp [(by apply And.right; simpa [OE] using h:x=0)] at h
    · by_cases hxx:x=0
      · simp only [hxx]; linarith
      · have:0<x:=lt_of_le_of_ne hx.1 (Ne.symm hxx)
        have:0≤1-x:=by linarith
        have:=hw.2
        positivity
lemma qW {N:ℕ} (N_pos:0<N) {s:ℂ} (Mh:0<s.re) (kR:s≠1) :
    (fF) N s=riemannZeta s:=by
  let f:=riemannZeta
  let g:=(fF) N
  let U:={z:ℂ | z≠1 ∧ 0<z.re}
  have f_an:AnalyticOnNhd ℂ f U:=by
    apply (tZ.analyticOnNhd isOpen_ne).mono
    simp only [ne_eq,setOf_subset_setOf,and_imp,U]
    exact fun a ha _↦ha
  have g_an:AnalyticOnNhd ℂ g U:=(rO N_pos).analyticOnNhd Ka
  have Xh:IsPreconnected U:=by
    apply IsConnected.isPreconnected
    apply (IsOpen.isConnected_iff_isPathConnected Ka).mpr Dv
  have h2:(2:ℂ)∈U:=by simp [U]
  have s_mem:s∈U:=by simp [U,Mh,kR]
  convert (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq f_an g_an Xh h2 ?_ s_mem).symm
  have u_mem:{z:ℂ | 1<z.re}∈𝓝 (2:ℂ) :=by
    apply mem_nhds_iff.mpr
    use {z:ℂ | 1<z.re}
    simp only [setOf_subset_setOf,imp_self,forall_const,mem_setOf_eq,re_ofNat,
      Nat.one_lt_ofNat,and_true,true_and]
    exact isOpen_lt (by continuity) (by continuity)
  filter_upwards [u_mem]
  intro z hz
  simp only [f,g,zeta_eq_tsum_one_div_nat_cpow hz,qZ]
  nth_rewrite 2 [neg_div]
  rw [← sub_eq_add_neg, ← OC N_pos hz,
    ← (summable_one_div_nat_cpow.mpr hz).sum_add_tsum_nat_add (N+1)]
  norm_cast
lemma QE {α:Type*} [Preorder α] {a b c d:α} :a≤b→b≤c→c≤d→a≤d:=
  fun hab hbc hcd↦le_trans (le_trans hab hbc) hcd
lemma OH {n:ℕ} {t A σ:ℝ} (Apos:0<A) (kL:0<σ) (TW:n≤ |t|)
    (uj:(1:ℝ)-A/Real.log |t| ≤σ) :
    ‖(n:ℂ)^(-(σ+t* I))‖ ≤(n:ℝ)⁻¹*Real.exp A:=by
  set s:=σ+t* I
  by_cases n0:n=0
  · simp_rw [n0,CharP.cast_eq_zero,inv_zero,zero_mul]
    rw [Complex.zero_cpow ?_]
    · simp
    · exact fun h↦kL.ne' <| zero_eq_neg.mp <| zero_re ▸ h ▸ (by simp [s])
  have n_gt_0:0<n:=Nat.pos_of_ne_zero n0
  have Fj:(0:ℝ)<(n:ℝ) :=Nat.cast_pos.mpr n_gt_0
  have TY:1≤(n:ℝ) :=Nat.one_le_cast.mpr <| Nat.succ_le_of_lt n_gt_0
  calc
    _= |((n:ℝ)^(-σ))| :=?_
    _≤Real.exp (Real.log n* -σ) :=Real.abs_rpow_le_exp_log_mul (n:ℝ) (-σ)
    _≤Real.exp (Real.log n*  -(1-A/Real.log t)) :=?_
    _≤Real.exp (- Real.log n+A) :=Real.exp_le_exp_of_le ?_
    _≤_:=by rw [Real.exp_add,Real.exp_neg,Real.exp_log Fj]
  · have: ‖(n:ℂ)^(-s)‖ =n^(-s.re) :=norm_cpow_eq_rpow_re_of_pos Fj (-s)
    rw [this,abs_eq_self.mpr <| Real.rpow_nonneg Fj.le _]; simp [s]
  · apply Real.exp_le_exp_of_le <| mul_le_mul_of_nonneg_left _ <| Real.log_nonneg TY
    rw [neg_sub,neg_le_sub_iff_le_add,add_comm, ← Real.log_abs]; linarith
  · simp only [neg_sub,le_neg_add_iff_add_le]
    ring_nf
    conv=>rw [mul_comm, ← mul_assoc, ← Real.log_abs]; rhs; rw [← one_mul A]
    gcongr
    by_cases ht1: |t| =1
    · simp [ht1]
    apply (inv_mul_le_iff₀ ?_).mpr
    · convert! Real.log_le_log Fj TW using 1; rw [mul_one]
    · exact Real.log_pos <| lt_of_le_of_ne (le_trans TY TW) <| fun t↦ht1 (t.symm)
lemma GJ {t:ℝ} (OI:3≤t) :1<Real.log t:=
  (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
lemma wA {A σ t:ℝ} (hA:A∈Ioc 0 (1/2)) (oq:3< |t|)
    (uj:1-A/Real.log |t| ≤σ) :
    let N:= ⌊|t|⌋₊;
    0<N ∧ N≤ |t| ∧ 1<Real.log |t| ∧ 1-A<σ ∧ 0<σ ∧ σ+t* I≠1:=by
  intro N
  have Npos:0<N:=Nat.floor_pos.mpr (by linarith)
  have oP:N≤ |t| :=Nat.floor_le <| abs_nonneg _
  have qK:=GJ oq.le
  have Kj:1-A<σ:=by
    apply lt_of_lt_of_le ((sub_lt_sub_iff_left (a:=1)).mpr ?_) uj
    exact (div_lt_iff₀ (by linarith)).mpr <| lt_mul_right hA.1 qK
  refine ⟨Npos,oP,qK,Kj,by linarith [hA.2],?_⟩
  contrapose! oq
  simp only [Complex.ext_iff,add_re,ofReal_re,mul_re,I_re,mul_zero,ofReal_im,I_im,mul_one,
    sub_self,add_zero,one_re,add_im,mul_im,zero_add,one_im] at oq
  norm_num [oq.2]
lemma NU {A σ t:ℝ} (OI:3< |t|) (uj:1-A/Real.log |t| ≤σ) :
      |t| ^(1-σ)≤Real.exp A:=by
  have: |t| ^(1-σ)≤ |t| ^(A/Real.log |t|) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  apply le_trans this ?_
  conv=>lhs; lhs; rw [← Real.exp_log (by linarith:0< |t|)]
  rw [div_eq_mul_inv,Real.rpow_mul (by positivity), ← Real.exp_mul, ← Real.exp_mul,mul_comm,
    ← mul_assoc,inv_mul_cancel₀,one_mul]
  apply Real.log_ne_zero.mpr; split_ands <;> linarith
lemma AN (N:ℕ) (Npos:0<N) :
    ∑ x∈Finset.Ico 0 N,((x:ℝ))⁻¹= ∑ x∈Finset.Ico 1 N,((x:ℝ))⁻¹:=by
  have:Finset.Ico 1 N⊆Finset.Ico 0 N:=by
    intro x hx
    simp only [Finset.mem_Ico,Nat.Ico_zero_eq_range,Finset.mem_range] at hx ⊢
    exact hx.2
  rw [← Finset.sum_sdiff (s₁:=Finset.Ico 1 N) (s₂:=Finset.Ico 0 N) this]
  have:Finset.Ico 0 N \ Finset.Ico 1 N=Finset.range 1:=by
    ext a
    simp only [Nat.Ico_zero_eq_range,Finset.mem_sdiff,Finset.mem_range,Finset.mem_Ico,not_and,
      not_lt,Finset.range_one,Finset.mem_singleton]
    exact ⟨fun _↦by omega,fun ha↦⟨by simp [ha,Npos],by omega⟩⟩
  rw [this]; simp
lemma NV {A C σ t:ℝ} (hA:A∈Ioc 0 (1/2))
    (uj:1-A/Real.log |t| ≤σ) (oq:3< |t|) (hC:2≤C) :let N:= ⌊|t|⌋₊;
    ‖∑ n∈Finset.range (N+1),(n:ℂ)^(-(σ+t* I))‖ ≤
      Real.exp A*C*Real.log |t| :=by
  intro N
  obtain ⟨Npos,oP,_,_,Kk,_⟩:=wA hA oq uj
  have qK:=GJ oq.le
  have (n:ℕ) (hn:n∈Finset.range (N+1)) :=OH (n:=n) hA.1 Kk ?_ uj
  · replace:=norm_sum_le_of_le (Finset.range (N+1)) this
    rw [← Finset.sum_mul,mul_comm _ (Real.exp A)] at this
    rw [mul_assoc]
    apply le_trans this <| (mul_le_mul_iff_right₀ A.exp_pos).mpr ?_
    have:1+Real.log (N:ℝ)≤C*Real.log |t| :=by
      by_cases hN:N=1
      · simp only [hN,Nat.cast_one,Real.log_one,add_zero]
        have:2*1≤C*Real.log |t| :=mul_le_mul hC qK.le (by linarith) (by linarith)
        linarith
      · rw [(by ring:C*Real.log |t| =Real.log |t| +(C-1)*Real.log |t|),
          ← one_mul <| Real.log (N: ℝ)]
        apply add_le_add qK.le
        refine mul_le_mul (by linarith) ?_ (by positivity) (by linarith)
        exact Real.log_le_log (by positivity) oP
    refine le_trans ?_ this
    convert! harmonic_eq_sum_Icc ▸ harmonic_le_one_add_log N
    · simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,Finset.range_eq_Ico]
      rw [AN (N+1) (by linarith)]; congr! 1
  · simp only [Finset.mem_range] at hn
    linarith [(by exact_mod_cast (by omega:n≤N) :(n:ℝ)≤N)]
lemma Nat.BT {t:ℝ} (OI:1≤ |t|) :let N:= ⌊|t|⌋₊;
    (|t| /N)∈Icc 1 2:=by
  intro N
  have Npos:0<N:=Nat.floor_pos.mpr (by linarith)
  have oP:N≤ |t| :=Nat.floor_le <| abs_nonneg _
  constructor
  · apply le_div_iff₀ (by simp [Npos]) |>.mpr; simp [oP]
  · apply div_le_iff₀ (by positivity) |>.mpr
    suffices |t| <N+1 by linarith [(by exact_mod_cast (by omega) :1≤(N:ℝ))]
    apply Nat.lt_floor_add_one
lemma NW {σ t:ℝ} (OI:3< |t|) (Rz:σ≤2) :(|t| / ⌊|t|⌋₊)^σ≤4:=by
  obtain ⟨h₁,h₂⟩:=Nat.BT (by linarith)
  calc _≤((|t| /↑⌊|t|⌋₊)^(2:ℝ)) :=by gcongr
       _≤(2:ℝ)^(2:ℝ) :=by gcongr
       _=4:=by norm_num
lemma NX {σ t:ℝ} (OI:3< |t|) (hσ:σ∈Ioc (1/2) 2)
    (Km:σ+t* I≠1) (Npos:0< ⌊|t|⌋₊) (oP: ⌊|t|⌋₊ ≤ |t|) :
    ⌊|t|⌋₊ ^(1-σ)/ ‖1-(σ+t* I)‖ ≤ |t| ^(1-σ)*2 ∧
    ⌊|t|⌋₊ ^(-σ)/2≤ |t| ^(1-σ) ∧ ⌊|t|⌋₊ ^(-σ)/σ≤8* |t| ^(-σ) :=by
  have bnd:=NW OI hσ.2
  have XT:(|t| / ⌊|t|⌋₊)^σ≤2* |t| :=by linarith
  split_ands
  · apply (div_le_iff₀ <| norm_pos_iff.mpr <| sub_ne_zero_of_ne Km.symm).mpr
    conv=>rw [mul_assoc]; rhs; rw [mul_comm]
    apply (div_le_iff₀ <| Real.rpow_pos_of_pos (by linarith) _).mp
    rw [vX (by positivity) (by positivity),neg_sub]
    refine QE ?_ XT ?_
    · exact Real.rpow_le_rpow_of_exponent_le (one_le_div (by positivity) |>.mpr oP) (by simp)
    · apply (mul_le_mul_iff_right₀ (by norm_num)).mpr; simpa using abs_im_le_norm (1-(σ+t* I))
  · apply div_le_iff₀ (by norm_num) |>.mpr
    rw [Real.rpow_sub (by linarith),Real.rpow_one,div_mul_eq_mul_div,mul_comm]
    apply div_le_iff₀ (by positivity) |>.mp
    convert! XT using 1
    rw [← Real.rpow_neg (by linarith),gY (by positivity) (by positivity)]
  · apply div_le_iff₀ (by linarith [hσ.1]) |>.mpr
    rw [mul_assoc,mul_comm,mul_assoc]
    apply div_le_iff₀' (by positivity) |>.mp
    apply le_trans ?_ (by linarith [hσ.1]:4≤σ*8)
    convert! bnd using 1; exact gY (by positivity) (by positivity)
lemma NY {A σ t:ℝ} (hA:A∈Ioc 0 (1/2)) (oq:3< |t|)
    (hσ:σ∈Icc (1-A/Real.log |t|) 2) :
    let C:=Real.exp A*(5+8*2); 
    let N:= ⌊|t|⌋₊;
    let s:=σ+t* I;
    ‖∑ n∈Finset.range (N+1),1/(n:ℂ)^s‖ + ‖(N:ℂ)^(1-s)/(1-s)‖
    + ‖(N:ℂ)^(-s)/2‖
    + ‖s* ∫ (x:ℝ) in Ioi (N:ℝ),(⌊x⌋ +1/2 -x)/(x:ℂ)^(s+1)‖
    ≤C*Real.log |t| :=by
  intros C N s
  obtain ⟨Npos,oP,qK,Kj,Kk,Km⟩:=wA hA oq hσ.1
  replace Kj:1/2<σ:=by linarith [hA.2]
  calc
    _≤Real.exp A*2*Real.log |t| + ‖N^(1-s)/(1-s)‖ + ‖(N:ℂ)^(-s)/2‖ +
      ‖s* ∫ x in Ioi (N:ℝ),(⌊x⌋ +1/2 -x)/(x:ℂ)^(s+1)‖ :=?_
    _≤Real.exp A*2*Real.log |t| + ‖N^(1-s)/(1-s)‖ + ‖(N:ℂ)^(-s)/2‖ +
      2* |t| *N^(-σ)/σ  :=?_
    _=Real.exp A*2*Real.log |t| +N^(1-σ)/ ‖(1-s)‖ +N^(-σ)/2+
      2* |t| *N^(-σ)/σ  :=?_
    _≤Real.exp A*2*Real.log |t| + |t| ^(1-σ)*2+
        |t| ^(1-σ)+2* |t| *(8* |t| ^(-σ)) :=?_
    _=Real.exp A*2*Real.log |t| +(3+8*2)* |t| ^(1-σ) :=?_
    _≤Real.exp A*2*Real.log |t| +(3+8*2)*Real.exp A*1:=?_
    _≤Real.exp A*2*Real.log |t| +(3+8*2)*Real.exp A*Real.log |t| :=?_
    _=_:=by ring
  · simp only [add_le_add_iff_right,vW]
    convert NV (C:=2) hA hσ.1 oq le_rfl using 1
  · simp only [add_le_add_iff_left]; exact DY N (by linarith) ⟨Kk,hσ.2⟩ (by linarith)
  · simp only [norm_div,RCLike.norm_ofNat,s]
    congr <;> (convert norm_natCast_cpow_of_pos Npos _; simp)
  · have ⟨h₁,h₂,h₃⟩:=NX oq ⟨Kj,hσ.2⟩ Km Npos oP
    gcongr
    rw [mul_div_assoc]
    gcongr
  · ring_nf; conv=>lhs; rhs; lhs; rw [mul_comm |t|]
    rw [← Real.rpow_add_one (by positivity)]; ring_nf
  · simp only [Real.log_abs,add_le_add_iff_left,mul_one]
    exact mul_le_mul_iff_right₀ (by positivity) |>.mpr <| NU oq hσ.1
  · simp only [add_le_add_iff_left]
    apply mul_le_mul_iff_right₀ (by norm_num [Real.exp_pos]) |>.mpr <| qK.le
lemma DZ:
    ∃ (A:ℝ) (_:A∈Ioc 0 (1/2)) (C:ℝ) (_:0<C), ∀ (σ:ℝ) (t:ℝ) (_:3< |t|)
    (_:σ∈Icc (1-A/Real.log |t|) 2), ‖(riemannZeta) (σ+t* I)‖ ≤C*Real.log |t| :=by
  let A:=(1/2:ℝ)
  let C:=Real.exp A*(5+8*2) 
  refine ⟨A,⟨by norm_num,by norm_num⟩,C,(by positivity),?_⟩
  intro σ t oq ⟨uj,Rz⟩
  obtain ⟨Npos,_,_,_,Kk,Km⟩:=wA ⟨by norm_num,by norm_num⟩ oq uj
  rw [← qW Npos (by simp [Kk]) Km]
  apply le_trans (by apply norm_add₄_le) ?_
  convert! NY ⟨by norm_num,le_rfl⟩ oq ⟨uj,Rz⟩ using 1; simp
open ArithmeticFunction (vonMangoldt)
end

-- aF.Nyman
section
open Complex MeasureTheory Set Filter
noncomputable section
namespace aF.Nyman
def K (s:ℂ) :ℂ:= ∫ u in Ioi (1:ℝ),((Int.fract u:ℝ) :ℂ)*(u:ℂ)^(-s-1)
lemma AO (s:ℂ) :
    Measurable (fun u:ℝ=>((Int.fract u:ℝ) :ℂ)*(u:ℂ)^(-s-1)) :=
  (Complex.measurable_ofReal.comp measurable_fract).mul
    (Complex.measurable_ofReal.pow_const _)
lemma norm_fract_le (u:ℝ) : ‖((Int.fract u:ℝ) :ℂ)‖ ≤1:=by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Int.fract_nonneg u)]
  exact (Int.fract_lt_one u).le
lemma lT {s:ℂ} (hs:0<s.re) {a:ℝ} (ha:0<a) :
    IntegrableOn (fun u:ℝ=>((Int.fract u:ℝ) :ℂ)*(u:ℂ)^(-s-1)) (Ioi a) :=by
  have hint:IntegrableOn (fun u:ℝ=>u^(-s.re-1)) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ha
  refine hint.mono' (AO s).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0:0<u:=ha.trans hu
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  calc ‖((Int.fract u:ℝ) :ℂ)‖ *u^(-s-1).re≤1*u^(-s-1).re:=
        mul_le_mul_of_nonneg_right (norm_fract_le u) (by positivity)
    _=u^(-s.re-1) :=by simp
lemma Ud {s:ℂ} (hs:0<s.re) (hs1:s≠1) :
    riemannZeta s=s/(s-1)-s*K s:=by
  have hs0:s≠0:=fun h=>by simp [h] at hs
  have VE:s-1≠0:=sub_ne_zero.2 hs1
  have h1s:1-s≠0:=sub_ne_zero.2 (Ne.symm hs1)
  rw [← qW (N:=1) one_pos hs hs1]
  have hI1:IntegrableOn (fun x:ℝ=>(x:ℂ)^(-s-1)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  have hval: ∫ x in Ioi (1:ℝ),(x:ℂ)^(-s-1)=1/s:=by
    rw [integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
    rw [show -s-1+1= -s by ring]
    simp
  have hJ: ∫ x in Ioi (1:ℝ),((⌊x⌋ :ℂ)+1/2 -x)/(x:ℂ)^(s+1)=
      1/2*(1/s)-K s:=by
    rw [← hval, ← integral_const_mul,K,
      ← integral_sub (hI1.const_mul _) (lT hs one_pos)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx=>?_
    have hx0:(0:ℝ)<x:=zero_lt_one.trans hx
    have hxc:(x:ℂ)^(s+1)≠0:=by
      rw [Ne,Complex.cpow_eq_zero_iff]; simp [hx0.ne']
    have hneg:(x:ℂ)^(-s-1)=((x:ℂ)^(s+1))⁻¹:=by
      rw [show -s-1= -(s+1) by ring,Complex.cpow_neg]
    rw [hneg,Int.fract]
    push_cast
    field_simp
    ring
  simp only [fF,Finset.sum_range_succ,Finset.sum_range_zero,Nat.cast_zero,
    Complex.zero_cpow hs0,Nat.cast_one,Complex.one_cpow,div_zero,zero_add]
  rw [hJ]
  field_simp
  ring
def H (θ:ℝ) :ℝ→ℂ:=(Ici θ).indicator fun u=>((Int.fract u:ℝ) :ℂ)
theorem jM {θ:ℝ} (hθ:0<θ) (Mj:θ≤1) {s:ℂ} (hs:0<s.re)
    (hs1:s.re<1) :
    ∫ x in Ioc (0:ℝ) 1,((Int.fract (θ/x) :ℝ) :ℂ)*(x:ℂ)^(s-1)=
      -(θ:ℂ)/(1-s)-(θ:ℂ)^s*riemannZeta s/s:=by
  have hs0:s≠0:=fun h=>by simp [h] at hs
  have RA:s≠1:=fun h=>by simp [h] at hs1
  have h1s:1-s≠0:=sub_ne_zero.2 (Ne.symm RA)
  have VE:s-1≠0:=sub_ne_zero.2 RA
  have abm:(θ:ℂ)≠0:=by exact_mod_cast hθ.ne'
  have step1: ∫ x in Ioc (0:ℝ) 1,((Int.fract (θ/x) :ℝ) :ℂ)*(x:ℂ)^(s-1)=
      mellin (fun t=>H θ (θ*t⁻¹)) s:=by
    rw [mellin, ← Ioi_inter_Iic, ← setIntegral_indicator measurableSet_Iic]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht=>?_
    have ht0:(0:ℝ)<t:=ht
    simp only [H,Set.indicator,mem_Iic,mem_Ici,smul_eq_mul]
    by_cases h1:t≤1
    · have:θ≤θ*t⁻¹:=le_mul_of_one_le_right hθ.le ((one_le_inv₀ ht0).2 h1)
      rw [if_pos h1,if_pos this,div_eq_mul_inv,mul_comm]
    · have: ¬ θ≤θ*t⁻¹:=by
        intro h
        exact h1 ((one_le_inv₀ ht0).1 ((le_mul_iff_one_le_right hθ).1 h))
      rw [if_neg h1,if_neg this,mul_zero]
  have step2:mellin (fun t=>H θ (θ*t⁻¹)) s=(θ:ℂ)^s*mellin (H θ) (-s) :=by
    rw [show mellin (fun t=>H θ (θ*t⁻¹)) s=mellin (fun u=>H θ (θ*u)) (-s) from
      mellin_comp_inv (fun u=>H θ (θ*u)) s,mellin_comp_mul_left (H θ) (-s) hθ,neg_neg,
      smul_eq_mul]
  have step4:mellin (H θ) (-s)=
      ∫ u in Ioi θ,((Int.fract u:ℝ) :ℂ)*(u:ℂ)^(-s-1) :=by
    rw [mellin]
    conv_rhs=>rw [← integral_Ici_eq_integral_Ioi]
    have hset:Ici θ=Ioi 0 ∩ Ici θ:=by
      ext u
      simp only [mem_Ici,mem_inter_iff,mem_Ioi]
      constructor
      · intro h; exact ⟨by linarith,h⟩
      · exact fun h=>h.2
    rw [hset, ← setIntegral_indicator measurableSet_Ici]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _=>?_
    simp only [H,Set.indicator,mem_Ici,smul_eq_mul]
    split_ifs <;> ring
  have hInt:=lT hs hθ
  have step5: ∫ u in Ioi θ,((Int.fract u:ℝ) :ℂ)*(u:ℂ)^(-s-1)=
      (∫ u in Ioc θ 1,((Int.fract u:ℝ) :ℂ)*(u:ℂ)^(-s-1))+K s:=by
    have h1:IntegrableOn (fun u:ℝ=>((Int.fract u:ℝ) :ℂ)*(u:ℂ)^(-s-1)) (Ioi 1) :=
      hInt.mono_set (Ioi_subset_Ioi Mj)
    rw [← Ioc_union_Ioi_eq_Ioi Mj,setIntegral_union
      (Set.disjoint_left.2 fun u hu hu'=>(not_lt.2 hu.2) hu':Disjoint (Ioc θ 1) (Ioi (1:ℝ)))
      (measurableSet_Ioi:MeasurableSet (Ioi (1:ℝ)))
      (hInt.mono_set Ioc_subset_Ioi_self) h1]
    rfl
  have step6: ∫ u in Ioc θ 1,((Int.fract u:ℝ) :ℂ)*(u:ℂ)^(-s-1)=
      (1-(θ:ℂ)^(1-s))/(1-s) :=by
    rw [integral_Ioc_eq_integral_Ioo]
    have: ∫ u in Ioo θ 1,((Int.fract u:ℝ) :ℂ)*(u:ℂ)^(-s-1)=
        ∫ u in Ioo θ 1,(u:ℂ)^(-s) :=by
      refine setIntegral_congr_fun measurableSet_Ioo fun u hu=>?_
      have hu0:(0:ℝ)<u:=hθ.trans hu.1
      have abo:(u:ℂ)≠0:=by exact_mod_cast hu0.ne'
      rw [Int.fract_eq_self.2 ⟨hu0.le,hu.2⟩,Complex.cpow_sub _ _ abo,Complex.cpow_one]
      field_simp
    rw [this, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le Mj,
      integral_cpow (Or.inl (by simp; linarith)),show -s+1=1-s by ring]
    push_cast
    rw [Complex.one_cpow]
  have hKs:K s=(s/(s-1)-riemannZeta s)/s:=by
    rw [Ud hs RA]; field_simp; ring
  have hθs:(θ:ℂ)^s*(θ:ℂ)^(1-s)=θ:=by
    rw [← Complex.cpow_add _ _ abm,show s+(1-s)=1 by ring,Complex.cpow_one]
  have hz:1/(1-s)+1/(s-1)=0:=by field_simp; ring
  rw [step1,step2,step4,step5,step6,hKs]
  rw [show (θ:ℂ)^s*((1-(θ:ℂ)^(1-s))/(1-s)+(s/(s-1)-riemannZeta s)/s)=
      (θ:ℂ)^s*(1/(1-s)+1/(s-1))-((θ:ℂ)^s*(θ:ℂ)^(1-s))/(1-s)-
        (θ:ℂ)^s*riemannZeta s/s by field_simp; ring,hθs,hz]
  ring
lemma rP
    (h: ∀ s:ℂ,1/2<s.re→s.re<1→ riemannZeta s≠0) :RiemannHypothesis:=by
  have hgt: ∀ s:ℂ,1/2<s.re→ riemannZeta s≠0:=fun s hs=>by
    rcases lt_or_ge s.re 1 with h1 | h1
    · exact h s hs h1
    · exact riemannZeta_ne_zero_of_one_le_re h1
  intro s hz htriv hs1
  by_contra hre
  rcases lt_or_gt_of_ne hre with hlt | hgt'
  · have hs0:s≠0:=by rintro rfl; simp [riemannZeta_zero] at hz
    have hΓ:Gammaℝ s≠0:=by
      rw [Ne,Gammaℝ_eq_zero_iff]
      rintro ⟨n,rfl⟩
      rcases n with _ | n
      · simp at hs0
      · exact htriv ⟨n,by push_cast; ring⟩
    have hΛ:completedRiemannZeta s=0:=by
      rw [riemannZeta_def_of_ne_zero hs0,div_eq_zero_iff] at hz
      exact hz.resolve_right hΓ
    have h1s:riemannZeta (1-s)=0:=by
      have:(1-s)≠0:=by
        intro h; rw [sub_eq_zero] at h; rw [← h] at hlt; simp at hlt; norm_num at hlt
      rw [riemannZeta_def_of_ne_zero this,completedRiemannZeta_one_sub,hΛ,zero_div]
    exact hgt (1-s) (by simp; linarith) h1s
  · exact hgt s hgt' hz
theorem rS
    (h: ∀ ε:ℝ,0<ε→ ∃ (n:ℕ) (c:Fin n→ℂ) (θ:Fin n→ℝ),
      (∀ k,0<θ k ∧ θ k≤1) ∧ ∑ k,c k*(θ k:ℂ)=0 ∧
      ∫ x in Ioc (0:ℝ) 1, ‖1- ∑ k,c k*((Int.fract (θ k/x) :ℝ) :ℂ)‖ ^2<ε) :
    RiemannHypothesis:=by
  refine rP fun ρ hρ Ml hz=>?_
  have Eb:ρ≠0:=fun h=>by simp [h] at hρ; linarith
  have XV:0<ρ.re:=by linarith
  have adP:0< ‖ρ‖ :=norm_pos_iff.2 Eb
  have hh:IntegrableOn (fun x:ℝ=>(x:ℂ)^(ρ-1)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith))
  have hBint:IntegrableOn (fun x:ℝ=>x^(2*ρ.re-2)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  set B:ℝ:= ∫ x in Ioc (0:ℝ) 1,x^(2*ρ.re-2) with hB
  have hB0:0≤B:=setIntegral_nonneg measurableSet_Ioc fun x hx=>by
    have:(0:ℝ)<x:=hx.1
    positivity
  set a:ℝ:=1/ ‖ρ‖ with ha
  have ha0:0<a:=by positivity
  set t:ℝ:=2*(B+1)/a with ht
  have ht0:0<t:=by positivity
  obtain ⟨n,c,θ,hθ,hsum,hA⟩:=h (a/(2*t)) (by positivity)
  set g:ℝ→ℂ:=fun x=>1- ∑ k,c k*((Int.fract (θ k/x) :ℝ) :ℂ) with hg
  have hfm: ∀ k,Measurable (fun x:ℝ=>((Int.fract (θ k/x) :ℝ) :ℂ)) :=fun k=>
    Complex.measurable_ofReal.comp (measurable_fract.comp (measurable_const.div measurable_id))
  have hgm:Measurable g:=
    measurable_const.sub (Finset.measurable_fun_sum _ fun k _=>measurable_const.mul (hfm k))
  have hgb: ∀ x, ‖g x‖ ≤1+ ∑ k, ‖c k‖ :=fun x=>by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]
    refine add_le_add le_rfl ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _=>?_))
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_fract_le _)
  have hg2:IntegrableOn (fun x=> ‖g x‖ ^2) (Ioc (0:ℝ) 1) :=by
    refine Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (hgm.norm.pow_const 2).aestronglyMeasurable (M:=(1+ ∑ k, ‖c k‖)^2) ?_
    refine Eventually.of_forall fun x=>?_
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hgb x) 2
  have hfrac: ∀ k,IntegrableOn
      (fun x:ℝ=>((Int.fract (θ k/x) :ℝ) :ℂ)*(x:ℂ)^(ρ-1)) (Ioc 0 1) :=fun k=>by
    refine hh.norm.mono' ((hfm k).mul (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable
      (Eventually.of_forall fun x=>?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_fract_le _)
  have hid: ∫ x in Ioc (0:ℝ) 1,g x*(x:ℂ)^(ρ-1)=1/ρ:=by
    have hpt: ∀ x,g x*(x:ℂ)^(ρ-1)=(x:ℂ)^(ρ-1)-
        ∑ k,c k*(((Int.fract (θ k/x) :ℝ) :ℂ)*(x:ℂ)^(ρ-1)) :=fun x=>by
      simp only [hg,sub_mul,one_mul,Finset.sum_mul,mul_assoc]
    simp_rw [hpt]
    rw [integral_sub hh (integrable_finsetSum _ fun k _=>(hfrac k).const_mul (c k)),
      integral_finsetSum _ fun k _=>(hfrac k).const_mul (c k)]
    simp_rw [integral_const_mul]
    have hk: ∀ k,c k* ∫ x in Ioc (0:ℝ) 1,
        ((Int.fract (θ k/x) :ℝ) :ℂ)*(x:ℂ)^(ρ-1)= -(c k*θ k)/(1-ρ) :=fun k=>by
      rw [jM (hθ k).1 (hθ k).2 XV Ml,hz]; ring
    simp_rw [hk]
    have h1: ∫ x in Ioc (0:ℝ) 1,(x:ℂ)^(ρ-1)=1/ρ:=by
      rw [← intervalIntegral.integral_of_le zero_le_one,
        integral_cpow (Or.inl (by simp; linarith)),show ρ-1+1=ρ by ring]
      simp [Complex.zero_cpow Eb]
    rw [h1, ← Finset.sum_div,Finset.sum_neg_distrib,hsum]
    simp
  have ZK: ∀ u v:ℝ,u*v≤(t*u^2+v^2/t)/2:=fun u v=>by
    have key:(t*u^2+v^2/t)/2 -u*v=(t*u- v)^2/(2*t) :=by
      field_simp; ring
    have:0≤(t*u- v)^2/(2*t) :=by positivity
    linarith
  have Xj: ∀ x∈Ioc (0:ℝ) 1, ‖(x:ℂ)^(ρ-1)‖ ^2=x^(2*ρ.re-2) :=by
    intro x hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1, ← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]
    congr 1; simp; ring
  have hbound: ‖∫ x in Ioc (0:ℝ) 1,g x*(x:ℂ)^(ρ-1)‖ ≤
      (t* ∫ x in Ioc (0:ℝ) 1, ‖g x‖ ^2)/2+B/t/2:=by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hR:IntegrableOn (fun x:ℝ=>(t* ‖g x‖ ^2+x^(2*ρ.re-2)/t)/2) (Ioc 0 1) :=
      ((hg2.const_mul t).add (hBint.div_const t)).div_const 2
    calc ∫ x in Ioc (0:ℝ) 1, ‖g x*(x:ℂ)^(ρ-1)‖
        ≤ ∫ x in Ioc (0:ℝ) 1,(t* ‖g x‖ ^2+x^(2*ρ.re-2)/t)/2:=by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x=>norm_nonneg _) hR
            ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx=>?_))
          simp only
          rw [norm_mul, ← Xj x hx]; exact ZK _ _
      _=(t* ∫ x in Ioc (0:ℝ) 1, ‖g x‖ ^2)/2+B/t/2:=by
          rw [integral_div,integral_add (hg2.const_mul t) (hBint.div_const t),integral_const_mul,
            integral_div]
          ring
  rw [hid,norm_div,norm_one] at hbound
  have hA0:0≤ ∫ x in Ioc (0:ℝ) 1, ‖g x‖ ^2:=
    setIntegral_nonneg measurableSet_Ioc fun x _=>by positivity
  have h1:t*(∫ x in Ioc (0:ℝ) 1, ‖g x‖ ^2)<a/2:=by
    have:=mul_lt_mul_of_pos_left hA ht0
    calc _<t*(a/(2*t)) :=this
      _=a/2:=by field_simp
  have h2:B/t≤a/2:=by
    rw [ht,div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have:1/ ‖ρ‖ <1/ ‖ρ‖ :=by
    calc 1/ ‖ρ‖ ≤_:=hbound
      _<a/2/2+a/2/2+a/2:=by linarith
      _=1/ ‖ρ‖ :=by rw [ha]; ring
  exact lt_irrefl _ this
end aF.Nyman
end
end

-- aF.WD
section
open MeasureTheory FourierTransform Complex Set
open scoped ContDiff
noncomputable section
namespace aF.Nyman.gW
lemma Dj (F:Lp ℂ 2 (volume:Measure ℝ)) : ‖F‖ ^2= ∫ x, ‖F x‖ ^2:=by
  rw [@norm_sq_eq_re_inner ℂ,MeasureTheory.L2.inner_def, ← integral_re (L2.integrable_inner F F)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x=>?_)
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
theorem integral_norm_sq_fourier {f:ℝ→ℂ} (hf1:Integrable f) (hf2:MemLp f 2) :
    ∫ ξ, ‖𝓕 f ξ‖ ^2= ∫ x, ‖f x‖ ^2:=by
  set F:Lp ℂ 2 (volume:Measure ℝ) :=hf2.toLp f with hF
  have hcont:Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf1
  have hae:(𝓕 F:Lp ℂ 2 (volume:Measure ℝ)) =ᵐ[volume] 𝓕 f:=by
    refine ae_eq_of_integral_contDiff_smul_eq
      ((Lp.memLp _).locallyIntegrable (by norm_num)) hcont.locallyIntegrable ?_
    intro g hg hgs
    have hgc:ContDiff ℝ ∞ (fun x=>(g x:ℂ)) :=ofRealCLM.contDiff.comp hg
    have abp:HasCompactSupport (fun x=>(g x:ℂ)) :=hgs.comp_left Complex.ofReal_zero
    set G:SchwartzMap ℝ ℂ:=abp.toSchwartzMap hgc with hG
    have hGx: ∀ x,G x=(g x:ℂ) :=fun x=>rfl
    have h1: ∫ x,g x•(𝓕 F:Lp ℂ 2 (volume:Measure ℝ)) x=
        Lp.toTemperedDistribution (𝓕 F:Lp ℂ 2 (volume:Measure ℝ)) G:=by
      rw [Lp.toTemperedDistribution_apply]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x=>?_)
      simp only [hGx,Complex.real_smul,smul_eq_mul]
    rw [h1, ← Lp.fourier_toTemperedDistribution_eq,TemperedDistribution.fourier_apply,
      Lp.toTemperedDistribution_apply (μ:=volume)]
    have h2: ∫ x,(𝓕 G) x•F x= ∫ x,(𝓕 (G:ℝ→ℂ)) x•f x:=by
      refine integral_congr_ae ?_
      filter_upwards [hf2.coeFn_toLp] with x hx
      rw [hF,hx]; rfl
    rw [h2]
    have h3:=VectorFourier.integral_fourierIntegral_smul_eq_flip (L:=innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner (G.integrable (μ:=volume)) hf1
    have h4: ∫ x,(𝓕 (G:ℝ→ℂ)) x•f x= ∫ x,G x•𝓕 f x:=by
      have ZL:(innerₗ ℝ:ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip=innerₗ ℝ:=by
        ext; simp
      simp only [smul_eq_mul,ZL] at h3 ⊢; exact h3
    rw [h4]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x=>?_)
    simp only [hGx,Complex.real_smul,smul_eq_mul]
  have hnorm: ‖(𝓕 F:Lp ℂ 2 (volume:Measure ℝ))‖ = ‖F‖ :=Lp.norm_fourier_eq F
  have e1:=Dj (𝓕 F)
  have e2:=Dj F
  have e3: ∫ x, ‖(𝓕 F:Lp ℂ 2 (volume:Measure ℝ)) x‖ ^2= ∫ ξ, ‖𝓕 f ξ‖ ^2:=by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx; rw [hx]
  have e4: ∫ x, ‖F x‖ ^2= ∫ x, ‖f x‖ ^2:=by
    refine integral_congr_ae ?_
    filter_upwards [hf2.coeFn_toLp] with x hx; rw [hF,hx]
  rw [← e3, ← e1,hnorm,e2,e4]
abbrev aZ (ξ:ℝ) :ℂ:=1/2+2*Real.pi*ξ* I
theorem xT {g:ℝ→ℂ} (hg:Measurable g) {B:ℝ}
    (hB: ∀ x∈Ioc (0:ℝ) 1, ‖g x‖ ≤B) :
    ∫ x in Ioc (0:ℝ) 1, ‖g x‖ ^2=
      ∫ ξ:ℝ, ‖∫ x in Ioc (0:ℝ) 1,g x*(x:ℂ)^(aZ ξ-1)‖ ^2:=by
  set gt:ℝ→ℂ:=(Ioc (0:ℝ) 1).indicator g with hgt
  have abq:Measurable gt:=hg.indicator measurableSet_Ioc
  have hB0:0≤B:=by
    have:=hB 1 ⟨one_pos,le_rfl⟩; exact (norm_nonneg _).trans this
  have abr: ∀ x, ‖gt x‖ ≤B:=fun x=>by
    by_cases hx:x∈Ioc (0:ℝ) 1
    · simp only [hgt,indicator_of_mem hx]; exact hB x hx
    · simp only [hgt,indicator_of_notMem hx,norm_zero]; exact hB0
  set φ:ℝ→ℂ:=fun u=>Real.exp (-(1/2)*u)•gt (Real.exp (-u)) with hφ
  have hφm:Measurable φ:=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).smul
      (abq.comp (Real.measurable_exp.comp measurable_neg))
  have hφ0: ∀ u,u<0→φ u=0:=fun u hu=>by
    have:Real.exp (-u)∉Ioc (0:ℝ) 1:=fun h=>by
      have:=h.2; rw [Real.exp_le_one_iff] at this; linarith
    simp [hφ,hgt,indicator_of_notMem this]
  set E:ℝ→ℝ:=(Ici (0:ℝ)).indicator fun u=>Real.exp (-(1/2)*u) with hE
  have WE:Integrable E:=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (exp_neg_integrableOn_Ioi 0 (by norm_num:(0:ℝ)<1/2))).integrable_indicator
      measurableSet_Ici
  have XZ: ∀ u, ‖φ u‖ ≤B*E u:=fun u=>by
    rcases lt_or_ge u 0 with hu | hu
    · rw [hφ0 u hu,norm_zero]
      exact mul_nonneg hB0 (indicator_nonneg (fun _ _=>(Real.exp_pos _).le) _)
    · simp only [hφ,hE,indicator_of_mem (show u∈Ici (0:ℝ) from hu),norm_smul,
        Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      rw [mul_comm B]
      exact mul_le_mul_of_nonneg_left (abr _) (Real.exp_pos _).le
  have hφ1:Integrable φ:=
    (WE.const_mul B).mono' hφm.aestronglyMeasurable (Filter.Eventually.of_forall XZ)
  have hφ2:MemLp φ 2:=by
    refine (memLp_two_iff_integrable_sq_norm hφm.aestronglyMeasurable).mpr ?_
    refine ((WE.const_mul (B^2))).mono' (hφm.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u=>?_)
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hEu:E u≤1:=by
      simp only [hE]
      by_cases hu:u∈Ici (0:ℝ)
      · rw [indicator_of_mem hu,Real.exp_le_one_iff]
        have:(0:ℝ)≤u:=hu
        linarith
      · rw [indicator_of_notMem hu]; norm_num
    have hE0:0≤E u:=indicator_nonneg (fun _ _=>(Real.exp_pos _).le) _
    calc ‖φ u‖ ^2≤(B*E u)^2:=pow_le_pow_left₀ (norm_nonneg _) (XZ u) 2
      _=B^2*(E u*E u) :=by ring
      _≤B^2*(E u*1) :=by gcongr
      _=B^2*E u:=by ring
  have hP:=integral_norm_sq_fourier hφ1 hφ2
  have hF: ∀ ξ:ℝ,𝓕 φ ξ= ∫ x in Ioc (0:ℝ) 1,g x*(x:ℂ)^(aZ ξ-1) :=by
    intro ξ
    have h:=mellin_eq_fourier gt (s:=aZ ξ)
    have hre:(aZ ξ).re=1/2:=by simp [aZ]
    have him:(aZ ξ).im/(2*Real.pi)=ξ:=by
      simp [aZ]
    rw [hre,him] at h
    rw [show φ=fun u:ℝ=>Real.exp (-(1/2)*u)•gt (Real.exp (-u)) from rfl, ← h,mellin,
      ← Ioi_inter_Iic, ← setIntegral_indicator measurableSet_Iic]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx=>?_
    by_cases h1:x∈Iic (1:ℝ)
    · have hx':x∈Ioc (0:ℝ) 1:=⟨hx,h1⟩
      simp only [indicator_of_mem h1,hgt,indicator_of_mem hx',smul_eq_mul]; ring
    · have hx':x∉Ioc (0:ℝ) 1:=fun h=>h1 h.2
      simp [indicator_of_notMem h1,hgt,indicator_of_notMem hx']
  have hL: ∫ u, ‖φ u‖ ^2= ∫ x in Ioc (0:ℝ) 1, ‖g x‖ ^2:=by
    set h:ℝ→ℂ:=fun x=>((‖gt x‖ ^2:ℝ) :ℂ) with hh
    have hm:=mellin_eq_fourier h (s:=1)
    simp only [Complex.one_re,Complex.one_im,zero_div] at hm
    have hlhs:mellin h 1= ∫ x in Ioc (0:ℝ) 1,(((‖g x‖ ^2:ℝ)) :ℂ) :=by
      rw [mellin,show Ioc (0:ℝ) 1=Ioi 0 ∩ Iic 1 from (Ioi_inter_Iic).symm,
        ← setIntegral_indicator measurableSet_Iic]
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx=>?_
      by_cases h1:x∈Iic (1:ℝ)
      · have hx':x∈Ioc (0:ℝ) 1:=⟨hx,h1⟩
        simp [hh,hgt,indicator_of_mem h1,indicator_of_mem hx']
      · have hx':x∉Ioc (0:ℝ) 1:=fun h=>h1 h.2
        simp [hh,hgt,indicator_of_notMem h1,indicator_of_notMem hx']
    have hrhs:𝓕 (fun u:ℝ=>Real.exp (-1*u)•h (Real.exp (-u))) 0=
        ∫ u,(((‖φ u‖ ^2:ℝ)) :ℂ) :=by
      rw [Real.fourier_real_eq]
      congr 1; ext u
      simp only [mul_zero,neg_zero,AddChar.map_zero_eq_one,one_smul,hh,hφ,norm_smul,
        Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      rw [Complex.real_smul]
      push_cast
      rw [mul_pow, ← Complex.exp_nat_mul]
      push_cast; ring_nf
    rw [hlhs,hrhs,integral_complex_ofReal,integral_complex_ofReal] at hm
    exact_mod_cast hm.symm
  rw [← hL, ← hP]
  congr 1; ext ξ; rw [hF]
end aF.Nyman.gW
end
end

-- Zeta23.Defs
section
open scoped BigOperators ArithmeticFunction
open Complex MeasureTheory Set
noncomputable section
namespace Zeta23
def l (T:ℝ) :ℝ:=Real.log (T/(2*Real.pi))
def VF (T:ℝ) :ℝ:=l T+2*Real.log 2 -1
def mu (τ:ℝ) :ℝ:=
  (1/(2*Real.pi))*(Complex.digamma (1/4+Complex.I*τ/2)).re
    -Real.log Real.pi/(2*Real.pi)
def bZ (ρ:ℂ) :ℂ:=(ρ-1/2)/Complex.I
def reflect (ρ:ℂ) :ℂ:=1-(starRingEnd ℂ) ρ
structure bT where
  carrier:Set ℂ
  mult:ℂ→ℕ
  one_le_mult: ∀ ρ∈carrier,1≤ mult ρ
  strip: ∀ ρ∈carrier,0≤ρ.re ∧ ρ.re≤1
  nI: ∀ ρ∈carrier,reflect ρ∈carrier
  eD: ∀ ρ∈carrier,mult (reflect ρ)=mult ρ
  dH: ∀ T₁ T₂:ℝ,(carrier ∩ {ρ | T₁<ρ.im ∧ ρ.im≤T₂}).Finite
namespace bT
variable (Z:bT)
def window (T₁ T₂:ℝ) :Set ℂ:=Z.carrier ∩ {ρ | T₁<ρ.im ∧ ρ.im≤T₂}
def simple:Set ℂ:={ρ | Z.mult ρ=1}
def N (T₁ T₂:ℝ) :ℕ:= ∑ᶠ ρ∈Z.window T₁ T₂,Z.mult ρ
end bT
namespace Params
variable (T:ℝ)
end Params
namespace bT
end bT
end Zeta23
end
end

-- Zeta23.cE.Defs
section
open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set
noncomputable section
namespace Zeta23
namespace cE
def xi (s:ℂ) :ℂ:=s*(s-1)/2*completedRiemannZeta₀ s+1/2
def lJ:ℂ→ℂ:=deriv xi
def gQ (ρ:ℂ) :Prop:=lJ ρ=0
def nJ (ρ:ℂ) :ℕ:=(analyticOrderAt lJ ρ).toNat
end cE
namespace Params
variable (T:ℝ)
end Params
namespace cE
def ZM (s:ℂ) :ℂ:=Complex.Gammaℝ (1-s)/Complex.Gammaℝ s
def L2 (s:ℂ) :ℂ:= -(1/2)*logDeriv ZM s
def Ue (s:ℂ) :ℂ:=deriv riemannZeta s+L2 s*riemannZeta s
def AY (ρ:ℂ) :Prop:=Ue ρ=0 ∧ ρ.im≠0
def RB (ρ:ℂ) :ℕ:=(analyticOrderAt Ue ρ).toNat
end cE
end Zeta23
end
end

-- Zeta23.Hypotheses
section
open scoped BigOperators ArithmeticFunction ComplexConjugate ContDiff
open Complex MeasureTheory Set
noncomputable section
namespace Zeta23
structure lK:Prop where
  even: ∀ τ:ℝ,mu (-τ)=mu τ
  smooth:ContDiff ℝ ∞ mu
  monotoneOn:MonotoneOn mu (Ici 0)
  Kp: ∀ τ:ℝ,mu 0≤ mu τ
  rD: -1< mu 0
  OJ: ∃ C:ℝ, ∀ τ:ℝ,1≤ |τ| →
    |mu τ-(1/(2*Real.pi))*Real.log (|τ| /(2*Real.pi))| ≤C/τ^2
  GK: ∃ C:ℝ, ∀ τ:ℝ,1≤ |τ| → |deriv mu τ| ≤C/ |τ|
  Uh: ∃ C T₀:ℝ, ∀ T:ℝ,T₀≤T→
    |(∫ τ in T..(2*T),mu τ)-T*VF T/(2*Real.pi)| ≤C/T
  Nr: ∃ C T₀:ℝ, ∀ T:ℝ,T₀≤T→
    |(∫ τ in T..(2*T),mu τ^2)-T*VF T^2/(4*Real.pi^2)|
      ≤C*(T*VF T^2/(4*Real.pi^2))/l T^2
end Zeta23
end
end

-- Zeta23.XL
section
noncomputable section
open Real
namespace Zeta23
namespace Params
variable (T:ℝ)
end Params
end Zeta23
end
end

-- Zeta23.wB.abt
section
noncomputable section
open Matrix Finset
open scoped ComplexOrder
namespace dS
variable {𝕜:Type*} [RCLike 𝕜]
variable {n:Type*} [Fintype n] [DecidableEq n]
section Reindex
variable {A:Matrix n n 𝕜} (hA:A.IsHermitian)
end Reindex
end dS
end
end

-- Zeta23.wB.VG
section
noncomputable section
open Matrix Finset Unitary
open scoped ComplexOrder
namespace dS
variable {𝕜:Type*} [RCLike 𝕜]
variable {n:Type*} [Fintype n] [DecidableEq n]
section RD
variable {A:Matrix n n 𝕜} (hA:A.IsHermitian)
end RD
end dS
end
end

-- Zeta23.wB.Sylvester
section
noncomputable section
open Matrix Finset Submodule
open scoped ComplexOrder
namespace dS
variable {𝕜:Type*} [RCLike 𝕜]
variable {n:Type*} [Fintype n] [DecidableEq n]
end dS
end
end

-- Zeta23.wB.Inertia
section
noncomputable section
open Matrix Finset Submodule
open scoped ComplexOrder
namespace dS
variable {𝕜:Type*} [RCLike 𝕜]
variable {m d:Type*} [Fintype m] [DecidableEq m] [Fintype d] [DecidableEq d]
end dS
end
end

-- Zeta23.wB.VonNeumann
section
noncomputable section
open Matrix Finset
open scoped ComplexOrder
namespace dS
variable {𝕜:Type*} [RCLike 𝕜]
variable {n:Type*} [Fintype n] [DecidableEq n]
section Bilinear
end Bilinear
section Rearrangement
end Rearrangement
end dS
end
end

-- Zeta23.wB.aaV
section
noncomputable section
open Matrix Finset
open scoped ComplexOrder
namespace dS
variable {𝕜:Type*} [RCLike 𝕜]
variable {n:Type*} [Fintype n] [DecidableEq n]
section Elementary
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
end Elementary
end dS
end
end

-- Zeta23.wB.Weyl
section
noncomputable section
open Matrix Finset
open scoped ComplexOrder
namespace dS
variable {𝕜:Type*} [RCLike 𝕜]
variable {n:Type*} [Fintype n] [DecidableEq n]
end dS
end
end

-- Zeta23.wB
section
end

-- Zeta23.cE.Statement
section
open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set Filter dS
noncomputable section
namespace Zeta23
namespace cE
theorem fO:Differentiable ℂ xi:=by
  unfold xi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).div_const 2).mul
    differentiable_completedZeta₀).add_const _
theorem RH (s:ℂ) (hs0:s≠0) (hs1:s≠1) :
    xi s=s*(s-1)/2*completedRiemannZeta s:=by
  unfold xi
  rw [completedRiemannZeta_eq]
  have h1s:(1:ℂ)-s≠0:=sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring
theorem Kq (s:ℂ) :xi (1-s)=xi s:=by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring
def qA:Prop:= ∀ ρ:ℂ,lJ ρ=0→0<ρ.re ∧ ρ.re<1
structure GO:Prop where
  one_le_mult: ∀ ρ,gQ ρ→1≤nJ ρ
  reflect_zero: ∀ ρ,gQ ρ→ gQ (reflect ρ)
  eD: ∀ ρ,gQ ρ→nJ (reflect ρ)=nJ ρ
  dH: ∀ T₁ T₂:ℝ,({ρ | gQ ρ} ∩ {ρ | T₁<ρ.im ∧ ρ.im≤T₂}).Finite
def Ec (hF2:qA) (hs:GO) :bT where
  carrier:={ρ | gQ ρ}
  mult:=nJ
  one_le_mult:=hs.one_le_mult
  strip:=fun _ h=>⟨(hF2 _ h).1.le,(hF2 _ h).2.le⟩
  nI:=hs.reflect_zero
  eD:=hs.eD
  dH:=hs.dH
section Io
variable (hF2:qA) (hs:GO) (T₁ T₂:ℝ)
@[simp] lemma RJ:(Ec hF2 hs).carrier={ρ | gQ ρ} :=rfl
@[simp] lemma Vw:(Ec hF2 hs).mult=nJ:=rfl
end Io
structure ZO (t₀:ℝ) :Prop where
  pos:0<t₀
  one_le_mult: ∀ ρ,AY ρ→t₀≤ |ρ.im| →1≤RB ρ
  reflect_zero: ∀ ρ,AY ρ→t₀≤ |ρ.im| →AY (reflect ρ)
  eD: ∀ ρ,AY ρ→t₀≤ |ρ.im| →RB (reflect ρ)=RB ρ
  dH: ∀ T₁ T₂:ℝ,({ρ | AY ρ ∧ t₀≤ |ρ.im|} ∩ {ρ | T₁<ρ.im ∧ ρ.im≤T₂}).Finite
section ZP
variable {t₀:ℝ} (hs:ZO t₀)
end ZP
end cE
end Zeta23
end
end

-- Zeta23.Defs.Counting
section
open Set
noncomputable section
namespace Zeta23.bT
variable (Z:bT) (T₁ T₂:ℝ)
lemma nS:(Z.window T₁ T₂).Finite:=Z.dH T₁ T₂
lemma wC {s t:Set ℂ} (hst:s⊆t) (ht:t⊆Z.window T₁ T₂) :
    ∑ᶠ ρ∈s,Z.mult ρ≤ ∑ᶠ ρ∈t,Z.mult ρ:=by
  have htf:t.Finite:=(Z.nS T₁ T₂).subset ht
  have hsf:s.Finite:=htf.subset hst
  rw [finsum_mem_eq_finite_toFinset_sum _ hsf,finsum_mem_eq_finite_toFinset_sum _ htf]
  apply Finset.sum_le_sum_of_subset
  exact Set.Finite.toFinset_subset_toFinset.mpr hst
end Zeta23.bT
end
end

-- Zeta23.Statement
section
open scoped BigOperators ComplexConjugate
open Complex Set
noncomputable section
namespace Zeta23
def aE (ρ:ℂ) :Prop:=riemannZeta ρ=0 ∧ 0<ρ.re ∧ ρ.re<1
def aP (ρ:ℂ) :ℕ:=(analyticOrderAt riemannZeta ρ).toNat
def Bc (T₁ T₂:ℝ) :Set ℂ:={ρ | aE ρ ∧ T₁<ρ.im ∧ ρ.im≤T₂}
def nL (T₁ T₂:ℝ) :ℕ:= ∑ᶠ ρ∈Bc T₁ T₂,aP ρ
structure iw:Prop where
  one_le_mult: ∀ ρ,aE ρ→1≤aP ρ
  reflect_zero: ∀ ρ,aE ρ→aE (reflect ρ)
  eD: ∀ ρ,aE ρ→aP (reflect ρ)=aP ρ
  dH: ∀ T₁ T₂:ℝ,({ρ | aE ρ} ∩ {ρ | T₁<ρ.im ∧ ρ.im≤T₂}).Finite
def jo (hs:iw) :bT where
  carrier:={ρ | aE ρ}
  mult:=aP
  one_le_mult:=hs.one_le_mult
  strip:=fun _ h=>⟨h.2.1.le,h.2.2.le⟩
  nI:=hs.reflect_zero
  eD:=hs.eD
  dH:=hs.dH
section Io
variable (hs:iw) (T₁ T₂:ℝ)
@[simp] lemma Vz:(jo hs).carrier={ρ | aE ρ} :=rfl
@[simp] lemma Xk:(jo hs).mult=aP:=rfl
@[simp] lemma VJ:(jo hs).simple={ρ | aP ρ=1} :=rfl
lemma wD:(jo hs).window T₁ T₂=Bc T₁ T₂:=by
  ext ρ; simp [bT.window,Bc]
@[simp] lemma GQ:(jo hs).N T₁ T₂=nL T₁ T₂:=by
  simp [bT.N,nL,wD]
end Io
lemma aE.zK {ρ:ℂ} (h:aE ρ) :
    (¬∃ n:ℕ,ρ= -2*(n+1)) ∧ ρ≠1:=by
  refine ⟨?_,?_⟩
  · rintro ⟨n,rfl⟩
    have:=h.2.1
    simp at this
    linarith
  · rintro rfl
    simpa using h.2.2
end Zeta23
end
end

-- Zeta23.ZC
section
open Complex
open scoped ComplexConjugate
namespace Zeta23
private lemma zL {s:ℂ} (hs:1<s.re) :
    conj (riemannZeta (conj s))=riemannZeta s:=by
  have hs':(1:ℝ)<(conj s).re:=by rwa [Complex.conj_re]
  rw [zeta_eq_tsum_one_div_nat_cpow hs',zeta_eq_tsum_one_div_nat_cpow hs]
  have hstar:star (∑' (n:ℕ),(1:ℂ)/(n:ℂ)^(conj s))
      = ∑' (n:ℕ),star ((1:ℂ)/(n:ℂ)^(conj s)) :=tsum_star
  calc conj (∑' (n:ℕ),(1:ℂ)/(n:ℂ)^(conj s))
      = ∑' (n:ℕ),star ((1:ℂ)/(n:ℂ)^(conj s)) :=hstar
    _= ∑' (n:ℕ),(1:ℂ)/(n:ℂ)^s:=by
        congr 1
        funext n
        have harg:((n:ℂ)).arg≠Real.pi:=by
          rw [Complex.natCast_arg]
          exact Ne.symm Real.pi_ne_zero
        have hpow:(n:ℂ)^(conj s)=conj ((n:ℂ)^s) :=by
          have h:=Complex.cpow_conj (n:ℂ) s harg
          rwa [Complex.conj_natCast] at h
        show star ((1:ℂ)/(n:ℂ)^(conj s))=1/(n:ℂ)^s
        rw [star_div₀,star_one,hpow]
        simp
theorem riemannZeta_conj {s:ℂ} (hs:s≠1) :
    riemannZeta (conj s)=conj (riemannZeta s) :=by
  have hrank:1<Module.rank ℝ ℂ:=by
    rw [Complex.rank_real_complex]
    norm_num
  have Xl:IsPreconnected ({(1:ℂ)}ᶜ) :=
    (isPathConnected_compl_singleton_of_one_lt_rank hrank 1).isConnected.isPreconnected
  have hζ:AnalyticOnNhd ℂ riemannZeta ({(1:ℂ)}ᶜ) :=by
    refine DifferentiableOn.analyticOnNhd (fun z hz=>?_) isOpen_compl_singleton
    exact (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
  have abw:AnalyticOnNhd ℂ (fun z=>conj (riemannZeta (conj z))) ({(1:ℂ)}ᶜ) :=by
    refine DifferentiableOn.analyticOnNhd (fun z hz=>?_) isOpen_compl_singleton
    have hz1:conj z≠1:=by
      intro h
      have h2:=congrArg (starRingEnd ℂ) h
      simp only [Complex.conj_conj,map_one] at h2
      exact (by simpa using hz:z≠1) h2
    have hd:DifferentiableAt ℂ riemannZeta (conj z) :=differentiableAt_riemannZeta hz1
    have h3:=hd.conj_conj
    rw [Complex.conj_conj] at h3
    exact h3.differentiableWithinAt
  have h2mem:(2:ℂ)∈({(1:ℂ)}ᶜ:Set ℂ) :=by
    simp only [Set.mem_compl_iff,Set.mem_singleton_iff]
    intro h
    have:=congrArg Complex.re h
    norm_num at this
  have hagree:(fun z=>conj (riemannZeta (conj z))) =ᶠ[nhds (2:ℂ)] riemannZeta:=by
    have hopen:IsOpen {z:ℂ | 1<z.re} :=isOpen_lt continuous_const Complex.continuous_re
    have h2:(2:ℂ)∈{z:ℂ | 1<z.re} :=by
      simp only [Set.mem_setOf_eq]
      norm_num
    filter_upwards [hopen.mem_nhds h2] with z hz
    exact zL hz
  have heq:=abw.eqOn_of_preconnected_of_eventuallyEq hζ Xl h2mem hagree
  have h3:conj (riemannZeta (conj s))=riemannZeta s:=heq (by simpa using hs)
  calc riemannZeta (conj s)=conj (conj (riemannZeta (conj s))) :=(Complex.conj_conj _).symm
    _=conj (riemannZeta s) :=by rw [h3]
private lemma lY (w:ℂ) :
    Filter.Tendsto (fun z=>conj z) (nhds (conj w)) (nhds w) :=by
  have h:=(Complex.continuous_conj).tendsto (conj w)
  rwa [Complex.conj_conj] at h
private lemma jQ {f:ℂ→ℂ} {w:ℂ} (hf:AnalyticAt ℂ f w) :
    AnalyticAt ℂ (fun z=>conj (f (conj z))) (conj w) :=by
  rw [analyticAt_iff_eventually_differentiableAt] at hf ⊢
  filter_upwards [(lY w).eventually hf] with z hz
  have h2:=hz.conj_conj
  rw [Complex.conj_conj] at h2
  exact h2
theorem uq (f:ℂ→ℂ) (w:ℂ) :
    analyticOrderAt (fun z=>conj (f (conj z))) (conj w)=analyticOrderAt f w:=by
  by_cases hf:AnalyticAt ℂ f w
  · by_cases htop:analyticOrderAt f w= ⊤
    · rw [htop,analyticOrderAt_eq_top]
      filter_upwards [(lY w).eventually (analyticOrderAt_eq_top.mp htop)] with z hz
      simp [hz]
    · obtain ⟨n,hn⟩:=ENat.ne_top_iff_exists.mp htop
      rw [← hn]
      rw [Eq.comm,hf.analyticOrderAt_eq_natCast] at hn
      obtain ⟨g,hg,hgne,hfg⟩:=hn
      rw [(jQ hf).analyticOrderAt_eq_natCast]
      refine ⟨fun z=>conj (g (conj z)),jQ hg,by simpa using hgne,?_⟩
      filter_upwards [(lY w).eventually hfg] with z hz
      have:conj (f (conj z))=conj ((conj z-w)^n*g (conj z)) :=by rw [hz]; rfl
      rw [this]
      simp only [map_mul,map_pow,map_sub,Complex.conj_conj]
      rfl
  · have hf': ¬ AnalyticAt ℂ (fun z=>conj (f (conj z))) (conj w) :=by
      intro hcon
      apply hf
      have h2:=jQ hcon
      rw [Complex.conj_conj] at h2
      exact h2.congr (Filter.Eventually.of_forall fun u=>by
        simp only [Complex.conj_conj])
    rw [analyticOrderAt_of_not_analyticAt hf,analyticOrderAt_of_not_analyticAt hf']
theorem uO {w:ℂ} (hw:w≠1) :
    analyticOrderAt riemannZeta (conj w)=analyticOrderAt riemannZeta w:=by
  have hne:conj w≠1:=by
    intro h
    have h2:=congrArg (starRingEnd ℂ) h
    simp only [Complex.conj_conj,map_one] at h2
    exact hw h2
  have hcong:(fun z=>conj (riemannZeta (conj z))) =ᶠ[nhds (conj w)] riemannZeta:=by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hne:
      conj w∈({(1:ℂ)}ᶜ))] with z hz
    rw [riemannZeta_conj (by simpa using hz),Complex.conj_conj]
  calc analyticOrderAt riemannZeta (conj w)
      =analyticOrderAt (fun z=>conj (riemannZeta (conj z))) (conj w) :=
        (analyticOrderAt_congr hcong).symm
    _=analyticOrderAt riemannZeta w:=uq _ _
private noncomputable def BU (s:ℂ) :ℂ:=
  2*(2*(Real.pi:ℂ))^(-s)*Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)
private lemma yW:(2*(Real.pi:ℂ))≠0:=by
  simp only [ne_eq,mul_eq_zero,not_or]
  exact ⟨two_ne_zero,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero⟩
private lemma OL {s:ℂ} (h0:0<s.re) (h1:s.re<1) :BU s≠0:=by
  have hsne: ∀ m:ℕ,s≠ -m:=by
    intro m h
    rw [h] at h0
    simp only [Complex.neg_re,Complex.natCast_re] at h0
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) h0
  have RK:(2*(Real.pi:ℂ))^(-s)≠0:=by
    rw [Complex.cpow_def_of_ne_zero yW]
    exact Complex.exp_ne_zero _
  have hcos:Complex.cos ((Real.pi:ℂ)*s/2)≠0:=by
    intro hc
    rw [Complex.cos_eq_zero_iff] at hc
    obtain ⟨k,hk⟩:=hc
    have hπ:((Real.pi:ℂ))≠0:=Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h2:(Real.pi:ℂ)*s=(Real.pi:ℂ)*(2*(k:ℂ)+1) :=by
      linear_combination (2:ℂ)*hk
    have hs_eq:s=((2*k+1:ℤ) :ℂ) :=by
      have h3:=mul_left_cancel₀ hπ h2
      rw [h3]
      push_cast
      ring
    rw [hs_eq,Complex.intCast_re] at h0 h1
    have h0':(0:ℤ)<2*k+1:=by exact_mod_cast h0
    have h1':(2*k+1:ℤ)<1:=by exact_mod_cast h1
    omega
  have hΓ:Complex.Gamma s≠0:=Complex.Gamma_ne_zero hsne
  unfold BU
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero RK) hΓ) hcos
private lemma Kr {s:ℂ} (h0:0<s.re) :AnalyticAt ℂ BU s:=by
  have h1:AnalyticAt ℂ (fun z:ℂ=>(2*(Real.pi:ℂ))^(-z)) s:=by
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards with z
    exact (differentiableAt_id.neg).const_cpow (Or.inl yW)
  have h2:AnalyticAt ℂ Complex.Gamma s:=by
    rw [analyticAt_iff_eventually_differentiableAt]
    have hopen:IsOpen {z:ℂ | 0<z.re} :=isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds h0] with z hz
    refine Complex.differentiableAt_Gamma z fun m=>?_
    intro h
    rw [h] at hz
    simp only [Complex.neg_re,Complex.natCast_re] at hz
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) hz
  have h3:AnalyticAt ℂ (fun z:ℂ=>Complex.cos ((Real.pi:ℂ)*z/2)) s:=by
    have hlin:AnalyticAt ℂ (fun z:ℂ=>(Real.pi:ℂ)*z/2) s:=by
      apply AnalyticAt.div_const
      exact analyticAt_const.mul analyticAt_id
    exact Complex.analyticAt_cos.comp hlin
  have h4:AnalyticAt ℂ (fun z:ℂ=>2*(2*(Real.pi:ℂ))^(-z)) s:=
    analyticAt_const.mul h1
  exact (h4.mul h2).mul h3
theorem qL {w:ℂ} (h0:0<w.re) (h1:w.re<1) :
    analyticOrderAt riemannZeta (1-w)=analyticOrderAt riemannZeta w:=by
  have hopen:IsOpen {z:ℂ | 0<z.re ∧ z.re<1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hev:(riemannZeta∘(fun z:ℂ=>1-z)) =ᶠ[nhds w]
      (BU*riemannZeta) :=by
    filter_upwards [hopen.mem_nhds ⟨h0,h1⟩] with z hz
    have hzne: ∀ n:ℕ,z≠ -n:=by
      intro n h
      rw [h] at hz
      simp only [Complex.neg_re,Complex.natCast_re] at hz
      exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) hz.1
    have ZQ:z≠1:=by
      intro h
      rw [h] at hz
      simp only [Complex.one_re] at hz
      exact lt_irrefl 1 hz.2
    show riemannZeta (1-z)=BU z*riemannZeta z
    rw [riemannZeta_one_sub hzne ZQ]
    unfold BU
    ring
  have hg:AnalyticAt ℂ (fun z:ℂ=>1-z) w:=analyticAt_const.sub analyticAt_id
  have hg':deriv (fun z:ℂ=>1-z) w≠0:=by
    have:deriv (fun z:ℂ=>1-z) w= -1:=by
      rw [deriv_const_sub]
      simp
    rw [this]
    simp
  have WG:=Kr h0
  have ZR:analyticOrderAt BU w=0:=
    WG.analyticOrderAt_eq_zero.mpr (OL h0 h1)
  calc analyticOrderAt riemannZeta (1-w)
      =analyticOrderAt (riemannZeta∘(fun z:ℂ=>1-z)) w:=by
        rw [analyticOrderAt_comp_of_deriv_ne_zero hg hg']
    _=analyticOrderAt (BU*riemannZeta) w:=analyticOrderAt_congr hev
    _=analyticOrderAt BU w+analyticOrderAt riemannZeta w:=by
        by_cases VK:AnalyticAt ℂ riemannZeta w
        · exact analyticOrderAt_mul WG VK
        · exfalso
          exact VK (by
            rw [analyticAt_iff_eventually_differentiableAt]
            have hne1:w≠1:=by
              intro h
              rw [h] at h1
              simp at h1
            filter_upwards [isOpen_compl_singleton.mem_nhds
              (by simpa using hne1:w∈({(1:ℂ)}ᶜ))] with z hz
            exact differentiableAt_riemannZeta (by simpa using hz))
    _=analyticOrderAt riemannZeta w:=by rw [ZR,zero_add]
theorem FN: ∀ ρ,aE ρ→aE (reflect ρ) :=by
  rintro ρ ⟨hzero,h0,h1⟩
  have ZS: ∀ n:ℕ,ρ≠ -n:=by
    intro n h
    rw [h] at h0
    simp only [Complex.neg_re,Complex.natCast_re] at h0
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) h0
  have Yb:ρ≠1:=by
    intro h
    rw [h] at h1
    simp at h1
  have Mr:(1:ℂ)-ρ≠1:=by
    intro h
    have:ρ=0:=by
      have:=congrArg (fun z=>(1:ℂ)-z) h
      simpa using this
    rw [this] at h0
    simp at h0
  have Ip:reflect ρ=conj (1-ρ) :=by
    unfold reflect
    rw [map_sub,map_one]
  constructor
  · 
    rw [Ip,riemannZeta_conj Mr,riemannZeta_one_sub ZS Yb,hzero]
    simp
  constructor
  · 
    unfold reflect
    simp only [Complex.sub_re,Complex.one_re,Complex.conj_re]
    linarith
  · 
    unfold reflect
    simp only [Complex.sub_re,Complex.one_re,Complex.conj_re]
    linarith
theorem FQ: ∀ ρ,aE ρ→aP (reflect ρ)=aP ρ:=by
  rintro ρ ⟨_,h0,h1⟩
  have Mr:(1:ℂ)-ρ≠1:=by
    intro h
    have Eb:ρ=0:=by
      have:=congrArg (fun z=>(1:ℂ)-z) h
      simpa using this
    rw [Eb] at h0
    simp at h0
  have Ip:reflect ρ=conj (1-ρ) :=by
    unfold reflect
    rw [map_sub,map_one]
  unfold aP
  rw [Ip,uO Mr,qL h0 h1]
end Zeta23
end

-- Zeta23.Statement.abx
section
open Complex Set Filter Topology
noncomputable section
namespace Zeta23
lemma cQ:AnalyticOnNhd ℂ riemannZeta ({1}ᶜ:Set ℂ) :=by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro s hs
  exact (differentiableAt_riemannZeta hs).differentiableWithinAt
lemma oG:IsConnected ({1}ᶜ:Set ℂ) :=
  isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 1
lemma lZ {s:ℂ} (hs:s≠1) :
    analyticOrderAt riemannZeta s≠ ⊤ :=by
  have h2:(2:ℂ)∈({1}ᶜ:Set ℂ) :=by norm_num
  refine cQ.analyticOrderAt_ne_top_of_isPreconnected
    oG.isPreconnected h2 hs ?_
  rw [(cQ 2 h2).analyticOrderAt_eq_zero.mpr
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
  exact ENat.zero_ne_top
theorem iw.FU: ∀ ρ,aE ρ→1≤aP ρ:=by
  intro ρ h
  have Ml:ρ≠1:=h.zK.2
  have han:AnalyticAt ℂ riemannZeta ρ:=cQ ρ Ml
  have hne0:analyticOrderAt riemannZeta ρ≠0:=han.analyticOrderAt_ne_zero.mpr h.1
  have Yc:=lZ Ml
  unfold aP
  obtain ⟨n,hn⟩:=ENat.ne_top_iff_exists.mp Yc
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_coe,ne_eq,Nat.cast_eq_zero] at hne0 ⊢
  omega
lemma iQ (z:ℂ) :
    ∃ t∈𝓝 z,(t ∩ {ρ:ℂ | ρ≠1 ∧ riemannZeta ρ=0}).Finite:=by
  by_cases hz:z=1
  · 
    subst hz
    have hres:=riemannZeta_residue_one
    have hev: ∀ᶠ s in 𝓝[≠] (1:ℂ),riemannZeta s≠0:=by
      have: ∀ᶠ s in 𝓝[≠] (1:ℂ),(s-1)*riemannZeta s≠0:=
        hres.eventually_ne one_ne_zero
      exact this.mono fun s hs h=>hs (by simp [h])
    rw [eventually_nhdsWithin_iff] at hev
    refine ⟨{s | s∈({1}ᶜ:Set ℂ)→ riemannZeta s≠0},hev,?_⟩
    refine (Set.finite_empty).subset ?_
    rintro s ⟨hs,hs1,hz⟩
    exact hs hs1 hz
  · have Iq:=(cQ).eqOn_zero_or_eventually_ne_zero_of_preconnected
      oG.isPreconnected
    rcases Iq with hzero | Iq
    · exfalso
      have:riemannZeta 2=0:=hzero (by norm_num:(2:ℂ)∈({1}ᶜ:Set ℂ))
      exact riemannZeta_ne_zero_of_one_lt_re (by norm_num) this
    · rw [Filter.Eventually,codiscreteWithin_iff_locallyFiniteComplementWithin] at Iq
      obtain ⟨t,ht,hfin⟩:=Iq z hz
      refine ⟨t,ht,hfin.subset ?_⟩
      rintro s ⟨hst,hs1,hs0⟩
      exact ⟨hst,hs1,by simpa using hs0⟩
theorem iw.Dw (T₁ T₂:ℝ) :
    ({ρ | aE ρ} ∩ {ρ | T₁<ρ.im ∧ ρ.im≤T₂}).Finite:=by
  set K:Set ℂ:=(Icc 0 1) ×ℂ (Icc T₁ T₂) with hK
  have hKc:IsCompact K:=isCompact_Icc.reProdIm isCompact_Icc
  choose t ht hfin using iQ
  obtain ⟨I, -,hcover⟩:=hKc.elim_nhds_subcover t (fun z _=>ht z)
  have ZT:(⋃ z∈I,(t z ∩ {ρ:ℂ | ρ≠1 ∧ riemannZeta ρ=0})).Finite:=
    I.finite_toSet.biUnion fun z _=>hfin z
  refine ZT.subset ?_
  rintro ρ ⟨hρ,hT₁,hT₂⟩
  have VL:ρ∈K:=by
    refine ⟨⟨hρ.2.1.le,hρ.2.2.le⟩,⟨hT₁.le,hT₂⟩⟩
  obtain ⟨z,hzI,Iv⟩:=mem_iUnion₂.mp (hcover VL)
  exact mem_iUnion₂.mpr ⟨z,hzI,Iv,hρ.zK.2,hρ.1⟩
theorem iw.RM
    (h₁: ∀ ρ,aE ρ→aE (reflect ρ))
    (h₂: ∀ ρ,aE ρ→aP (reflect ρ)=aP ρ) :iw:=
  ⟨iw.FU,h₁,h₂,iw.Dw⟩
end Zeta23
end
end

-- Zeta23.Statement.ZV
section
noncomputable section
namespace Zeta23
theorem kS:iw:=iw.RM FN FQ
def aD:bT:=jo kS
@[simp] lemma zO:aD.carrier={ρ | aE ρ} :=rfl
@[simp] lemma TN:aD.mult=aP:=rfl
@[simp] lemma jR (T₁ T₂:ℝ) :aD.N T₁ T₂=nL T₁ T₂:=
  GQ _ _ _
theorem Mt (T₁ T₂:ℝ) :(Bc T₁ T₂).Finite:=by
  simpa [wD] using (jo kS).nS T₁ T₂
end Zeta23
end
end

-- Zeta23.dQ.Defs
section
open Complex
noncomputable section
namespace Zeta23.dQ
end Zeta23.dQ
end
end

-- Zeta23.Analytic.VA
section
open Complex Set Topology Filter Asymptotics Real
noncomputable section
namespace Zeta23
namespace Analytic
theorem Bd {f:ℂ→ℂ} {z w:ℂ} (hre:z.re≤w.re) (him:z.im≤w.im)
    (S:Finset ℂ) (A:ℂ→ℂ)
    (hS: ∀ p∈S,Rectangle z w∈𝓝 p)
    (RO:dG f (Rectangle z w \ (S:Set ℂ)))
    (near: ∀ p∈S,(f-fun s=>A p/(s-p)) =O[𝓝[≠] p] (1:ℂ→ℂ)) :
    aW f z w= ∑ p∈S,A p:=by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty=>
    simp only [Finset.coe_empty,sdiff_empty] at RO
    rw [Finset.sum_empty]
    show (1/(2*π* I))•aV f z w=0
    rw [RO.qw subset_rfl,smul_zero]
  | @insert p S hpS ih=>
    have hp:Rectangle z w∈𝓝 p:=hS p (Finset.mem_insert_self p S)
    have hS': ∀ q∈S,Rectangle z w∈𝓝 q:=fun q hq=>hS q (Finset.mem_insert_of_mem hq)
    set P:ℂ→ℂ:=fun s=>A p/(s-p) with hP
    set f₁:ℂ→ℂ:=f-P with hf₁
    set f₂:ℂ→ℂ:=Function.update f₁ p (limUnder (𝓝[≠] p) f₁) with hf₂
    have Ee: ∀ s,s≠p→DifferentiableAt ℂ P s:=by
      intro s hs
      have:s-p≠0:=sub_ne_zero.mpr hs
      simp only [hP]
      fun_prop (disch:=assumption)
    have Nu:dG f₁ (Rectangle z w \ ((insert p S:Finset ℂ) :Set ℂ)) :=by
      refine RO.sub ?_
      intro s hs
      apply (Ee s ?_).differentiableWithinAt
      intro h
      apply hs.2
      simp [h]
    have VN:IsClosed (S:Set ℂ) :=S.finite_toSet.isClosed
    have hRS:Rectangle z w \ (S:Set ℂ)∈𝓝 p:=by
      apply Filter.inter_mem hp
      exact VN.isOpen_compl.mem_nhds (by simpa using hpS)
    obtain ⟨U,hU,hbdd⟩:=DU (near p (Finset.mem_insert_self p S))
    have hV:U ∩ (Rectangle z w \ (S:Set ℂ))∈𝓝 p:=Filter.inter_mem hU hRS
    have Yd:DifferentiableOn ℂ f₁ ((U ∩ (Rectangle z w \ (S:Set ℂ))) \ {p}) :=by
      apply Nu.mono
      rintro s ⟨⟨_,Kt,hsS⟩,hsp⟩
      refine ⟨Kt,?_⟩
      simp only [Finset.coe_insert,mem_insert_iff,Finset.mem_coe,not_or]
      exact ⟨by simpa using hsp,by simpa using hsS⟩
    have ZW:BddAbove (norm∘f₁ '' ((U ∩ (Rectangle z w \ (S:Set ℂ))) \ {p})) :=
      hbdd.mono (image_mono (Set.sdiff_subset_sdiff_left inter_subset_left))
    have Yf:DifferentiableOn ℂ f₂ (U ∩ (Rectangle z w \ (S:Set ℂ))) :=
      differentiableOn_update_limUnder_of_bddAbove hV Yd ZW
    have Fk: ∀ s,s≠p→f₂ s=f₁ s:=fun s hs=>Function.update_of_ne hs _ _
    have Nv:dG f₂ (Rectangle z w \ (S:Set ℂ)) :=by
      intro s hs
      by_cases hsp:s=p
      · rw [hsp]
        exact (Yf.differentiableAt hV).differentiableWithinAt
      · have h1:DifferentiableWithinAt ℂ f₁
            (Rectangle z w \ ((insert p S:Finset ℂ) :Set ℂ)) s:=
          Nu s ⟨hs.1,by
            simp only [Finset.coe_insert,mem_insert_iff,Finset.mem_coe,not_or]
            exact ⟨hsp,by simpa using hs.2⟩⟩
        have hset:(Rectangle z w \ ((insert p S:Finset ℂ) :Set ℂ))
            =(Rectangle z w \ (S:Set ℂ)) ∩ {p}ᶜ:=by
          ext x
          simp only [Finset.coe_insert,Set.mem_sdiff,mem_insert_iff,Finset.mem_coe,not_or,
            mem_inter_iff,mem_compl_iff,mem_singleton_iff]
          tauto
        rw [hset] at h1
        have hpc:{p}ᶜ∈𝓝[Rectangle z w \ (S:Set ℂ)] s:=
          mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hsp)
        rw [differentiableWithinAt_inter' hpc] at h1
        refine h1.congr_of_eventuallyEq ?_ (Fk s hsp)
        filter_upwards [hpc] with x hx
        exact Fk x hx
    have Xm: ∀ q∈S,(f₂-fun s=>A q/(s-q)) =O[𝓝[≠] q] (1:ℂ→ℂ) :=by
      intro q hq
      have hqp:q≠p:=fun h=>hpS (h ▸ hq)
      have hev:((f-fun s=>A q/(s-q))-P)
          =ᶠ[𝓝[≠] q] (f₂-fun s=>A q/(s-q)) :=by
        have:{p}ᶜ∈𝓝[≠] q:=
          mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hqp)
        filter_upwards [this] with s hs
        simp only [Pi.sub_apply,Fk s hs,hf₁]
        ring
      have hPO:P =O[𝓝[≠] q] (1:ℂ→ℂ) :=by
        have hc:ContinuousAt P q:=(Ee q hqp).continuousAt
        exact (hc.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
      exact ((near q (Finset.mem_insert_of_mem hq)).sub hPO).congr' hev EventuallyEq.rfl
    have ih':=ih hS' Nv Xm
    have vV:EqOn f (f₂+P) (aO z w) :=by
      intro s hs
      have hsp:s≠p:=fun h=>bU hp (h ▸ hs)
      simp only [Pi.add_apply,Fk s hsp,hf₁,Pi.sub_apply,sub_add_cancel]
    have hbS: ∀ s∈aO z w,s∈Rectangle z w \ (S:Set ℂ) :=fun s hs=>
      ⟨cO z w hs,
        fun hsS=>bU (hS' s hsS) hs⟩
    have hi₂:aY f₂ z w:=
      ContinuousOn.eO (Nv.continuousOn.mono hbS)
    have hiP:aY P z w:=by
      apply ContinuousOn.eO
      intro s hs
      have hsp:s≠p:=fun h=>bU hp (h ▸ hs)
      exact (Ee s hsp).continuousAt.continuousWithinAt
    rw [kP vV,Finset.sum_insert hpS]
    show (1/(2*π* I))•aV (f₂+P) z w=_
    rw [aY.add hi₂ hiP,smul_add]
    show aW f₂ z w+aW P z w=_
    rw [ih',kJ hre him hp,add_comm]
end Analytic
end Zeta23
end
end

-- Zeta23.dQ.WH
section
open Complex Set Topology Filter Real
noncomputable section
namespace Zeta23
namespace dQ
lemma iW {s:ℂ} (h0:s≠0) (h1:s≠1) :
    AnalyticAt ℂ completedRiemannZeta s:=by
  have hopen:IsOpen (({0,1} :Set ℂ)ᶜ) :=(Set.toFinite _).isClosed.isOpen_compl
  have hdiff:DifferentiableOn ℂ completedRiemannZeta (({0,1} :Set ℂ)ᶜ) :=by
    intro z hz
    simp only [mem_compl_iff,mem_insert_iff,mem_singleton_iff,not_or] at hz
    exact (differentiableAt_completedZeta hz.1 hz.2).differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds (by simp [h0,h1]))
lemma gJ {s:ℂ} (hs:s≠0) (hG:Gammaℝ s≠0) :
    completedRiemannZeta s=Gammaℝ s*riemannZeta s:=by
  rw [riemannZeta_def_of_ne_zero hs]
  field_simp
lemma dM {s:ℂ} (hs:0<s.re) :
    completedRiemannZeta s=0↔riemannZeta s=0:=by
  have h0:s≠0:=fun h=>by simp [h] at hs
  have hG:=Gammaℝ_ne_zero_of_re_pos hs
  rw [gJ h0 hG,mul_eq_zero]
  simp [hG]
lemma dN {s:ℂ} (hs:1≤ s.re) :
    completedRiemannZeta s≠0:=by
  rw [Ne,dM (by linarith)]
  exact riemannZeta_ne_zero_of_one_le_re hs
lemma jK {s:ℂ} (hs:s.re≤0) :
    completedRiemannZeta s≠0:=by
  rw [← completedRiemannZeta_one_sub]
  exact dN (by simp; linarith)
lemma iz {s:ℂ} :
    completedRiemannZeta s=0↔aE s:=by
  constructor
  · intro h
    have h1:0<s.re:=by
      by_contra hle
      exact jK (not_lt.mp hle) h
    have h2:s.re<1:=by
      by_contra hle
      exact dN (not_lt.mp hle) h
    exact ⟨(dM h1).mp h,h1,h2⟩
  · rintro ⟨hz,h1,_⟩
    exact (dM h1).mpr hz
lemma jX {ρ:ℂ} (h:0<ρ.re) (h1:ρ≠1) :
    analyticOrderNatAt completedRiemannZeta ρ=aP ρ:=by
  have h0:ρ≠0:=fun h'=>by simp [h'] at h
  have hev:riemannZeta =ᶠ[𝓝 ρ] (completedRiemannZeta*fun s=>(Gammaℝ s)⁻¹) :=by
    filter_upwards [isOpen_compl_singleton.mem_nhds h0] with s hs
    rw [Pi.mul_apply,riemannZeta_def_of_ne_zero hs,div_eq_mul_inv]
  have hΛ:=iW h0 h1
  have WI:AnalyticAt ℂ (fun s=>(Gammaℝ s)⁻¹) ρ:=differentiable_Gammaℝ_inv.analyticAt ρ
  have hG0:analyticOrderAt (fun s=>(Gammaℝ s)⁻¹) ρ=0:=
    WI.analyticOrderAt_eq_zero.mpr (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos h))
  unfold aP analyticOrderNatAt
  rw [analyticOrderAt_congr hev,analyticOrderAt_mul hΛ WI,hG0,add_zero]
end dQ
end Zeta23
end
end

-- Zeta23.bR.aac
section
noncomputable section
namespace Zeta23
namespace bR
open Complex Filter Topology
lemma kM {s:ℂ} (hs:0<s.re) :DifferentiableAt ℂ Gammaℝ s:=by
  have h1:DifferentiableAt ℂ (fun u:ℂ=>(Real.pi:ℂ)^(-u/2)) s:=
    (differentiableAt_id.neg.div_const (2:ℂ)).const_cpow
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h2:DifferentiableAt ℂ (fun u:ℂ=>Gamma (u/2)) s:=by
    refine (Complex.differentiableAt_Gamma _ fun m hm=>?_).comp s (differentiableAt_id.div_const _)
    have:=congrArg Complex.re hm
    simp at this
    have hm0:(0:ℝ)≤ m:=Nat.cast_nonneg m
    linarith
  have:Gammaℝ=fun u:ℂ=>(Real.pi:ℂ)^(-u/2)*Gamma (u/2) :=funext Gammaℝ_def
  rw [this]
  exact h1.mul h2
lemma Dx {s:ℂ} (hs:0<s.re) :AnalyticAt ℂ Gammaℝ s:=by
  have hopen:IsOpen {u:ℂ | 0<u.re} :=isOpen_lt continuous_const Complex.continuous_re
  exact DifferentiableOn.analyticAt (fun u hu=>(kM hu).differentiableWithinAt)
    (hopen.mem_nhds hs)
lemma oQ {s:ℂ} (hs:0<s.re) :
    completedRiemannZeta =ᶠ[𝓝 s] fun u=>Gammaℝ u*riemannZeta u:=by
  have hopen:IsOpen {u:ℂ | 0<u.re} :=isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with u hu
  have hu0:u≠0:=fun h0=>by simp [h0] at hu
  have hΓ:=Gammaℝ_ne_zero_of_re_pos hu
  rw [riemannZeta_def_of_ne_zero hu0]
  field_simp
lemma zP {s:ℂ} (hs:s≠1) :AnalyticAt ℂ riemannZeta s:=
  DifferentiableOn.analyticAt (s:=({1}ᶜ:Set ℂ))
    (fun _ hu=>(differentiableAt_riemannZeta hu).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)
theorem uW {ρ:ℂ} (h:0<ρ.re) (h':ρ.re<1) :
    (completedRiemannZeta ρ=0↔aE ρ) ∧
    analyticOrderAt completedRiemannZeta ρ=analyticOrderAt riemannZeta ρ:=by
  have Ml:ρ≠1:=fun e=>by simp [e] at h'
  have hΓ:Gammaℝ ρ≠0:=Gammaℝ_ne_zero_of_re_pos h
  have hev:=oQ h
  have hval:completedRiemannZeta ρ=Gammaℝ ρ*riemannZeta ρ:=hev.eq_of_nhds
  have yZ:=Dx h
  have aad:=zP Ml
  refine ⟨?_,?_⟩
  · rw [hval,mul_eq_zero,aE]
    constructor
    · rintro (aby | hz)
      · exact absurd aby hΓ
      · exact ⟨hz,h,h'⟩
    · rintro ⟨hz, -, -⟩
      exact Or.inr hz
  · rw [analyticOrderAt_congr hev]
    have hmul:=analyticOrderAt_mul yZ aad
    rw [show (Gammaℝ *riemannZeta)=(fun u=>Gammaℝ u*riemannZeta u) from rfl] at hmul
    rw [hmul,yZ.analyticOrderAt_eq_zero.mpr hΓ,zero_add]
end bR
end Zeta23
end
end

-- Zeta23.dO.abz
section
open scoped Complex ComplexConjugate
end

-- Zeta23.dQ.Fold
section
open Complex MeasureTheory Set intervalIntegral
noncomputable section
namespace Zeta23.dQ
section OM
lemma Iw {x:ℝ} (hx:0<x) (w:ℂ) :
    (x:ℂ)^(starRingEnd ℂ w)=starRingEnd ℂ ((x:ℂ)^w) :=by
  have hx0:(x:ℂ)≠0:=by exact_mod_cast hx.ne'
  rw [cpow_def_of_ne_zero hx0,cpow_def_of_ne_zero hx0, ← Complex.exp_conj,map_mul,
    ← Complex.ofReal_log hx.le,Complex.conj_ofReal]
lemma NZ (s:ℂ) :Complex.Gammaℝ (starRingEnd ℂ s)=starRingEnd ℂ (Complex.Gammaℝ s) :=by
  have h1: -(starRingEnd ℂ s)/2=starRingEnd ℂ (-s/2) :=by
    simp [map_div₀,map_neg,map_ofNat]
  have h2:starRingEnd ℂ s/2=starRingEnd ℂ (s/2) :=by
    simp [map_div₀,map_ofNat]
  rw [Complex.Gammaℝ_def,Complex.Gammaℝ_def,h1,h2,Iw Real.pi_pos,
    Complex.Gamma_conj,map_mul]
end OM
end Zeta23.dQ
end
end

-- Zeta23.dQ.aaW
section
open Complex MeasureTheory Set
open scoped Interval
noncomputable section
namespace Zeta23.dQ
def jE:Set ℂ:={s:ℂ | 0<s.re}
lemma Bj:IsOpen jE:=
  isOpen_lt continuous_const Complex.continuous_re
lemma gN {s:ℂ} (hs:0<s.re) :DifferentiableAt ℂ Complex.Gamma (s/2) :=by
  apply Complex.differentiableAt_Gamma
  intro m h
  have:=congrArg Complex.re h
  simp at this
  have:(0:ℝ)≤ m:=Nat.cast_nonneg m
  linarith
lemma uY:DifferentiableOn ℂ Complex.Gammaℝ jE:=by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  have h1:DifferentiableAt ℂ (fun s:ℂ=>(Real.pi:ℂ)^(-s/2)) s:=by
    apply DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have h2:DifferentiableAt ℂ (fun s:ℂ=>Complex.Gamma (s/2)) s:=
    (gN hs).comp s (by fun_prop)
  have:Complex.Gammaℝ=fun s=>(Real.pi:ℂ)^(-s/2)*Complex.Gamma (s/2) :=by
    funext s; rw [Complex.Gammaℝ_def]
  rw [this]
  exact h1.mul h2
lemma zQ:AnalyticOnNhd ℂ Complex.Gammaℝ jE:=
  uY.analyticOnNhd Bj
lemma mo:DifferentiableOn ℂ (logDeriv Complex.Gammaℝ) jE:=by
  have hA:=zQ
  have hd:DifferentiableOn ℂ (deriv Complex.Gammaℝ) jE:=hA.deriv.differentiableOn
  have:logDeriv Complex.Gammaℝ=fun s=>deriv Complex.Gammaℝ s/Complex.Gammaℝ s:=by
    funext s; rfl
  rw [this]
  exact hd.div hA.differentiableOn fun s hs=>Complex.Gammaℝ_ne_zero_of_re_pos hs
theorem jB {s:ℂ} (hs:0<s.re) :
    logDeriv Complex.Gammaℝ s= -(Real.log Real.pi:ℂ)/2+(1/2:ℂ)*Complex.digamma (s/2) :=by
  have hπ:(Real.pi:ℂ)≠0:=by exact_mod_cast Real.pi_ne_zero
  have e:Complex.Gammaℝ=fun s:ℂ=>(Real.pi:ℂ)^(-s/2)*Complex.Gamma (s/2) :=by
    funext s; rw [Complex.Gammaℝ_def]
  have hf:(fun s:ℂ=>(Real.pi:ℂ)^(-s/2)) s≠0:=by
    simp only [ne_eq,cpow_eq_zero_iff,hπ,false_and,not_false_eq_true]
  have hg:(fun s:ℂ=>Complex.Gamma (s/2)) s≠0:=by
    apply Complex.Gamma_ne_zero
    intro m h
    have:=congrArg Complex.re h
    simp at this
    have:(0:ℝ)≤ m:=Nat.cast_nonneg m
    linarith
  have hdf:DifferentiableAt ℂ (fun s:ℂ=>(Real.pi:ℂ)^(-s/2)) s:=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hπ)
  have hdg:DifferentiableAt ℂ (fun s:ℂ=>Complex.Gamma (s/2)) s:=
    (gN hs).comp s (by fun_prop)
  rw [e,logDeriv_mul (f:=fun s:ℂ=>(Real.pi:ℂ)^(-s/2)) (g:=fun s:ℂ=>Complex.Gamma (s/2)) s hf hg hdf hdg]
  have h1:logDeriv (fun s:ℂ=>(Real.pi:ℂ)^(-s/2)) s= -(Real.log Real.pi:ℂ)/2:=by
    have hder:HasDerivAt (fun s:ℂ=>(Real.pi:ℂ)^(-s/2))
        ((Real.pi:ℂ)^(-s/2)*Complex.log Real.pi*(-1/2)) s:=by
      have:HasDerivAt (fun s:ℂ=> -s/2) (-1/2:ℂ) s:=by
        simpa using ((hasDerivAt_id s).neg.div_const (2:ℂ))
      exact this.const_cpow (Or.inl hπ)
    rw [logDeriv_apply,hder.deriv]
    have hne:(Real.pi:ℂ)^(-s/2)≠0:=hf
    rw [Complex.ofReal_log Real.pi_pos.le]
    field_simp
  have h2:logDeriv (fun s:ℂ=>Complex.Gamma (s/2)) s=(1/2:ℂ)*Complex.digamma (s/2) :=by
    have:=logDeriv_comp (f:=Complex.Gamma) (g:=fun s:ℂ=>s/2) (x:=s)
      (gN hs) (by fun_prop)
    rw [show (Complex.Gamma∘fun s:ℂ=>s/2)=fun s=>Complex.Gamma (s/2) from rfl] at this
    rw [this,Complex.digamma_def]
    have:deriv (fun s:ℂ=>s/2) s=1/2:=by
      rw [deriv_div_const,deriv_id'']
    rw [this]; ring
  rw [h1,h2]
end Zeta23.dQ
end
end

-- Zeta23.dQ.aae
section
open Complex Set MeasureTheory Real
noncomputable section
namespace Zeta23
namespace dQ
theorem uZ {S:Set ℂ} (hS:(1:ℂ)∉S) :
    AnalyticOnNhd ℂ riemannZeta S:=by
  have h:AnalyticOnNhd ℂ riemannZeta ({1}ᶜ:Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun s hs=>(differentiableAt_riemannZeta hs).differentiableWithinAt) isOpen_compl_singleton
  exact h.mono (Set.subset_compl_singleton_iff.mpr hS)
theorem jz {s:ℂ} (hσ:0<s.re) (hs:s≠1) :
    ‖riemannZeta s‖ ≤1/2+1/ ‖1-s‖ + ‖s‖ /s.re:=by
  have hs0:s≠0:=fun h=>by simp [h] at hσ
  have hint:=Dh 1 le_rfl (σ:=s.re) (t:=s.im) hσ
  rw [re_add_im] at hint
  simp only [Nat.cast_one,Real.one_rpow] at hint
  rw [← qW (N:=1) one_pos hσ hs]
  simp only [fF,Finset.sum_range_succ,Finset.sum_range_zero,Nat.cast_zero,
    Complex.zero_cpow hs0,Nat.cast_one,Complex.one_cpow,div_one,div_zero,zero_add]
  set J:= ∫ x in Ioi (1:ℝ),((⌊x⌋ :ℂ)+1/2 -x)/(x:ℂ)^(s+1) with hJ
  calc ‖(1:ℂ)+ -1/(1-s)+ -1/2+s*J‖
      = ‖(1/2:ℂ)+ -(1/(1-s))+s*J‖ :=by ring_nf
    _≤ ‖(1/2:ℂ)‖ + ‖-(1/(1-s))‖ + ‖s*J‖ :=norm_add₃_le
    _=1/2+1/ ‖1-s‖ + ‖s‖ * ‖J‖ :=by
        simp [norm_neg]
    _≤1/2+1/ ‖1-s‖ + ‖s‖ *(1/s.re) :=by gcongr
    _=1/2+1/ ‖1-s‖ + ‖s‖ /s.re:=by ring
theorem vh {δ:ℝ} (hδ:0<δ) {s:ℂ} (hσ:δ≤ s.re)
    (ht:1≤ |s.im|) : ‖riemannZeta s‖ ≤(5/2+δ⁻¹)* |s.im| :=by
  have Eh:0<s.re:=lt_of_lt_of_le hδ hσ
  have hs1:s≠1:=by
    rintro rfl
    norm_num at ht
  have h:=jz Eh hs1
  have him: |s.im| ≤ ‖1-s‖ :=by
    simpa using Complex.abs_im_le_norm (1-s)
  have h1:1/ ‖1-s‖ ≤1:=by
    rw [div_le_one (by linarith)]
    linarith
  have h2: ‖s‖ /s.re≤1+δ⁻¹* |s.im| :=by
    have hn: ‖s‖ ≤ |s.re| + |s.im| :=Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos Eh] at hn
    calc ‖s‖ /s.re≤(s.re+ |s.im|)/s.re:=by gcongr
      _=1+ |s.im| /s.re:=by field_simp
      _≤1+ |s.im| /δ:=by gcongr
      _=1+δ⁻¹* |s.im| :=by rw [div_eq_inv_mul]
  have h3:(5/2:ℝ)≤5/2* |s.im| :=by nlinarith
  nlinarith [h,h1,h2,h3]
theorem QF {δ:ℝ} (hδ:0<δ) :
    ∃ C:ℝ,0<C ∧ ∀ s:ℂ,δ≤ s.re→1≤ |s.im| → ‖riemannZeta s‖ ≤C* |s.im| :=by
  refine ⟨5/2+δ⁻¹,by positivity,fun s hσ ht=>vh hδ hσ ht⟩
theorem Dz:
    ∃ A C:ℝ,0<C ∧ ∀ s:ℂ,(1/4:ℝ)≤ s.re→s.re≤2→1≤ |s.im| →
      ‖riemannZeta s‖ ≤C* |s.im| ^A:=by
  obtain ⟨C,hC,h⟩:=QF (δ:=1/4) (by norm_num)
  refine ⟨1,C,hC,fun s h₁ _ h₃=>?_⟩
  simpa [Real.rpow_one] using h s h₁ h₃
theorem BW (s:ℂ) (hσ:(0.15:ℝ)≤ s.re) (h1:1≤ ‖s-1‖) :
    ‖riemannZeta s‖ ≤20/3*(|s.im| +3)^(1:ℝ) :=by
  rw [Real.rpow_one]
  have Eh:0<s.re:=by linarith
  have hs1:s≠1:=by
    rintro rfl
    norm_num at h1
  have h:=jz Eh hs1
  have h1':1/ ‖1-s‖ ≤1:=by
    rw [norm_sub_rev] at h1
    rw [div_le_one (by linarith)]
    exact h1
  have hσ':(3:ℝ)/20≤ s.re:=by
    have:=hσ; norm_num at this ⊢; linarith
  have h2: ‖s‖ /s.re≤1+20/3* |s.im| :=by
    have hn: ‖s‖ ≤ |s.re| + |s.im| :=Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos Eh] at hn
    calc ‖s‖ /s.re≤(s.re+ |s.im|)/s.re:=by gcongr
      _=1+ |s.im| /s.re:=by field_simp
      _≤1+ |s.im| /(3/20) :=by gcongr
      _=1+20/3* |s.im| :=by ring
  have ht:0≤ |s.im| :=abs_nonneg _
  linarith [h,h1',h2,ht]
theorem FZ:
    ∃ A C:ℝ,0<C ∧ ∀ s:ℂ,(0.15:ℝ)≤ s.re→1≤ ‖s-1‖ →
      ‖riemannZeta s‖ ≤C*(|s.im| +3)^A:=
  ⟨1,20/3,by norm_num,BW⟩
theorem jN {s:ℂ} (hs:2≤ s.re) :
    ‖riemannZeta s-1‖ ≤Real.pi^2/6-1:=by
  have hs1:1<s.re:=by linarith
  set f:ℕ→ℂ:=fun n=>1/((n:ℂ)+1)^s with hf
  have hsum:Summable f:=by
    have h0:=Complex.summable_one_div_nat_cpow.mpr hs1
    have:=(summable_nat_add_iff 1).mpr h0
    simpa [f] using this
  have aaf:riemannZeta s= ∑' n,f n:=zeta_eq_tsum_one_div_nat_add_one_cpow hs1
  have hf0:f 0=1:=by simp [f]
  have hsplit:riemannZeta s-1= ∑' n,f (n+1) :=by
    rw [aaf,hsum.tsum_eq_zero_add,hf0]; ring
  have hle: ∀ n:ℕ, ‖f (n+1)‖ ≤1/((n:ℝ)+2)^2:=by
    intro n
    have hpos:0<n+2:=by omega
    have hf1:f (n+1)=1/((n+2:ℕ) :ℂ)^s:=by
      simp only [f]
      congr 2
      push_cast
      ring
    rw [hf1,norm_div,norm_one,Complex.norm_natCast_cpow_of_pos hpos]
    have hbase:(1:ℝ)≤((n+2:ℕ) :ℝ) :=by exact_mod_cast hpos
    have hpow:((n+2:ℕ) :ℝ)^(2:ℝ)≤((n+2:ℕ) :ℝ)^s.re:=
      Real.rpow_le_rpow_of_exponent_le hbase hs
    rw [Real.rpow_two] at hpow
    have h2pos:(0:ℝ)<((n+2:ℕ) :ℝ)^2:=by positivity
    calc 1/((n+2:ℕ) :ℝ)^s.re≤1/((n+2:ℕ) :ℝ)^2:=
          one_div_le_one_div_of_le h2pos hpow
      _=1/((n:ℝ)+2)^2:=by push_cast; ring
  have htwo:HasSum (fun n:ℕ=>1/((n:ℝ)+2)^2) (Real.pi^2/6-1) :=by
    have h:=(hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    norm_num [Finset.sum_range_succ] at h
    exact h.congr_fun fun n=>by ring
  rw [hsplit]
  have hsum':Summable (fun n=>f (n+1)) :=(summable_nat_add_iff 1).mpr hsum
  calc ‖∑' n,f (n+1)‖ ≤ ∑' n, ‖f (n+1)‖ :=norm_tsum_le_tsum_norm hsum'.norm
    _≤ ∑' n:ℕ,1/((n:ℝ)+2)^2:=hsum'.norm.tsum_le_tsum hle htwo.summable
    _=Real.pi^2/6-1:=htwo.tsum_eq
theorem ow {s:ℂ} (hs:2≤ s.re) :
    2 -Real.pi^2/6≤ ‖riemannZeta s‖ :=by
  have h:=jN hs
  have h': ‖(1:ℂ)‖ - ‖1-riemannZeta s‖ ≤ ‖riemannZeta s‖ :=by
    simpa using norm_sub_norm_le (1:ℂ) (1-riemannZeta s)
  rw [norm_sub_rev] at h'
  simp only [norm_one] at h'
  linarith
lemma mC:(1/3:ℝ)<2 -Real.pi^2/6:=by
  have:=Real.pi_lt_d2
  nlinarith [Real.pi_pos]
theorem oR: ∀ t:ℝ,(1/3:ℝ)≤ ‖riemannZeta (2+t* I)‖ :=by
  intro t
  have h:=ow (s:=2+t* I) (by simp)
  linarith [mC]
theorem oz {s:ℂ} (hs:2≤ s.re) :
    ‖riemannZeta s‖ ≤Real.pi^2/6:=by
  have h:=jN hs
  have h': ‖riemannZeta s‖ ≤ ‖riemannZeta s-1‖ + ‖(1:ℂ)‖ :=by
    simpa using norm_le_norm_sub_add (riemannZeta s) (1:ℂ)
  simp only [norm_one] at h'
  linarith
end dQ
end Zeta23
end
end

-- Zeta23.Prelude.Uj
section
end

-- Zeta23.dO.WJ
section
open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory
lemma AnalyticOn.jF {C r R:ℝ} {f:ℂ→ℂ} {w:ℂ}
    (Ol:r≤R)
    (analytic:AnalyticOn ℂ f (Metric.closedBall 0 R))
    (cond: ∀ z∈Metric.sphere 0 r, ‖f z‖ ≤C)
    (abA:w∈Metric.closedBall 0 r) :
    ‖f w‖ ≤C:=by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U:=Metric.closedBall 0 r) Metric.isBounded_closedBall
  · apply DifferentiableOn.diffContOnCl
    rw [Metric.closure_closedBall]
    exact AnalyticOn.differentiableOn
      (AnalyticOn.mono analytic
        (Metric.closedBall_subset_closedBall Ol))
  · rw [frontier_closedBall']
    exact cond
  · rw [Metric.closure_closedBall]
    exact abA
theorem Ej {M r R:ℝ} {f:ℂ→ℂ} {z:ℂ}
    (Mpos:0<M) (Rpos:0<R) (Ol:r<R)
    (analytic:AnalyticOn ℂ f (Metric.ball 0 R))
    (BX:f 0=0)
    (oT: ∀ z∈Metric.ball 0 R,(f z).re≤M)
    (Kw:z∈Metric.closedBall 0 r) :
    ‖f z‖ ≤(2*M*r)/(R-r) :=by
  have DA: ∀ ε>0, ‖f z‖ ≤(2*(M+ε)* ‖z‖)/(R- ‖z‖) :=by
    intro ε εpos;
    apply Complex.borelCaratheodory_zero;
    exacts [by linarith,analytic.differentiableOn,fun z hz=>by rw [Set.mem_setOf_eq]; linarith [oT z hz],Rpos,by exact Metric.mem_ball.mpr ( lt_of_le_of_lt ( Metric.mem_closedBall.mp Kw ) Ol ),BX]
  have Mv: ‖f z‖ ≤(2*M* ‖z‖)/(R- ‖z‖) :=by
    have Mv:Filter.Tendsto (fun ε=>(2*(M+ε)* ‖z‖)/(R- ‖z‖)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2*M* ‖z‖)/(R- ‖z‖))) :=by
      refine tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' ?_ _ _ (by ring_nf))
      exact ((continuous_const.mul (continuous_const.add continuous_id)).mul continuous_const).div_const _
    exact le_of_tendsto_of_tendsto tendsto_const_nhds Mv ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε=>DA ε hε );
  rw [mem_closedBall_iff_norm,sub_zero] at Kw
  refine le_trans Mv ?_;
  gcongr
  · exact mul_nonneg (mul_nonneg (zero_le_two) (le_of_lt Mpos)) (le_trans (norm_nonneg z) Kw)
lemma BZ {r r' R:ℝ} {f:ℂ→ℂ} {z:ℂ}
    (Mw:r<r') (Fo:r'<R)
    (RP:DifferentiableOn ℂ f (Metric.ball 0 R))
    (hz:z∈Metric.closedBall 0 r) :
    deriv f z=(1/(2*Real.pi* I))• ∮ w in C(0,r'),(w-z)⁻¹^2•f w:=by
  have RQ:z∈Metric.ball 0 r':=
    Metric.mem_ball.mpr <| (Metric.mem_closedBall.mp hz).trans_lt Mw
  simp [← Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      Metric.isOpen_ball (Metric.closedBall_subset_ball Fo) RP RQ]
lemma Kz {M r r' R:ℝ} {f:ℂ→ℂ} {z:ℂ}
    (Mpos:0<M) (adv:0<r) (Mw:r<r') (Fo:r'<R)
    (vk:AnalyticOn ℂ f (Metric.ball 0 R))
    (Mz:f 0=0)
    (Uk: ∀ z∈Metric.ball 0 R,(f z).re≤M)
    (OO:z∈Metric.closedBall 0 r) :
    ‖(deriv f) z‖ ≤2*M*(r')^2/((R-r')*(r'-r)^2) :=by
  rw [BZ Mw Fo vk.differentiableOn  OO,one_div]
  grw [circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by linarith) (C:=2*M*r'/((R-r')*(r'-r)^2))]
  · exact le_of_eq (by ring)
  · intro z' hz'
    rw [smul_eq_mul,norm_mul]
    grw[Ej Mpos (by grind) Fo vk Mz  Uk
      (Metric.sphere_subset_closedBall hz')]
    suffices ‖(z'-z)⁻¹^2‖ ≤1/(r'-r)^2 by
      grw [this]
      · exact le_of_eq (by field)
      · refine mul_nonneg (mul_nonneg ?_ ?_) (inv_nonneg.mpr ?_) <;> linarith
    have hdist:r'-r≤ ‖z'-z‖ :=by
      simp only [mem_sphere_iff_norm,sub_zero,Metric.mem_closedBall,
        dist_zero_right] at hz' OO
      rw [← hz']
      have hzr: ‖z‖ ≤r:=by simpa [Complex.dist_eq] using OO
      exact le_trans (by linarith) (norm_sub_norm_le z' z)
    rw [norm_pow,norm_inv,one_div,inv_pow]
    gcongr
theorem zR {M r R:ℝ} {f:ℂ→ℂ} {z:ℂ}
    (Mpos:0<M) (rpos:0<r) (Ol:r<R)
    (vk:AnalyticOn ℂ f (Metric.ball 0 R))
    (BX:f 0=0)
    (oT: ∀ z∈Metric.ball 0 R,(f z).re≤M)
    (Kw:z∈Metric.closedBall 0 r) :
    ‖deriv f z‖ ≤16*M*R^2/(R-r)^3:=by
  have hr':2*M*((R+r)/2)^2/((R-(R+r)/2)*((R+r)/2 -r)^2)=
      4*M*(R+r)^2/(R-r)^3:=by field_simp; ring
  calc ‖deriv f z‖
      _≤4*M*(R+r)^2/(R-r)^3:=hr' ▸
          Kz Mpos rpos (by linarith) (by linarith) vk BX oT Kw
      _≤16*M*R^2/(R-r)^3:=by
          have:16*M*R^2=4*M*(2*R)^2:=by ring_nf
          rw [this]; bound
theorem jG {r R:ℝ} {B:ℂ→ℂ}
    (aaX:0<r) (r_lt_R:r<R)
    (kT:AnalyticOnNhd ℂ B (Metric.closedBall (0:ℂ) R))
    (wI: ∀ z∈Metric.closedBall (0:ℂ) R,B z≠0) :
    ∃ (GR:ℂ→ℂ),(AnalyticOnNhd ℂ GR (Metric.ball 0 R)) ∧
      (GR 0=0) ∧
      (∀ z∈Metric.closedBall 0 r,(deriv GR) z=(deriv B) z/(B z)) ∧
      (∀ z∈Metric.ball 0 R,Real.log ‖B z‖ -Real.log ‖B 0‖ =(GR z).re) :=by
  obtain ⟨GR,hJB⟩: ∃ GR:ℂ→ℂ,(∀ z∈Metric.ball 0 R,(HasDerivAt GR (deriv B z/B z) z)) ∧ GR 0=0 ∧ (∀ z∈Metric.ball 0 R,Real.log ‖B z‖ -Real.log ‖B 0‖ =(GR z).re) :=by
    set f:ℂ→ℂ:=fun z=>deriv B z/B z;
    have hf:AnalyticOnNhd ℂ f (Metric.ball 0 R) :=
      (kT.deriv.mono Metric.ball_subset_closedBall).div
        (kT.mono Metric.ball_subset_closedBall)
        (fun z hz=>wI z <| Metric.ball_subset_closedBall hz)
    obtain ⟨J,hJ⟩:=DifferentiableOn.isExactOn_ball hf.differentiableOn
    refine ⟨fun z↦J z-J 0,fun z hz↦(hJ z hz).sub_const _,by simp,?_⟩
    set H:ℂ→ℂ:=fun z=>Complex.exp (J z-J 0)/B z
    have Um: ∀ z∈Metric.ball 0 R,HasDerivAt (fun z↦J z-J 0) (f z) z:=
      fun z hz↦(hJ z hz).sub_const _
    have OP: ∀ z∈Metric.ball 0 R,HasDerivAt H 0 z:=by
      intro z hz
      have:=(Complex.hasDerivAt_exp _).comp z (Um z hz)
      convert! this.div (kT.differentiableOn.differentiableAt
        (Metric.closedBall_mem_nhds_of_mem hz) |>.hasDerivAt)
        (wI z <| Metric.ball_subset_closedBall hz) using 1
      ring_nf!; grind
    have VO: ∀ z∈Metric.ball 0 R,H z=H 0:=by
      intro z hz
      have VQ:DifferentiableOn ℂ H (Metric.ball 0 R) :=
        fun z hz↦(OP z hz).differentiableAt.differentiableWithinAt
      refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball 0 R) VQ ?_ hz
        (Metric.mem_ball_self (Metric.pos_of_mem_ball hz))
      intro x hx
      rw [fderivWithin_of_isOpen Metric.isOpen_ball hx,
        ← ContinuousLinearMap.toSpanSingleton_zero]
      exact (OP x hx).hasFDerivAt.fderiv
    have VR: ∀ z∈Metric.ball 0 R,Real.exp (J z-J 0).re= ‖B z‖ / ‖B 0‖ :=by
      intro z hz
      have hc:=VO z hz
      simp only [H,sub_self,Complex.exp_zero,one_div] at hc
      rw [div_eq_iff (wI z (Metric.ball_subset_closedBall hz)),mul_comm] at hc
      rw [← Complex.norm_exp, ← norm_div,div_eq_mul_inv]
      exact enorm_eq_iff_norm_eq.mp (congrArg enorm hc)
    intro z hz
    have hBz:=wI z (Metric.ball_subset_closedBall hz)
    have hB0:=wI 0 (by norm_num; linarith)
    rw [← Real.log_div (norm_ne_zero_iff.mpr hBz) (norm_ne_zero_iff.mpr hB0),
      ← VR z hz,Real.log_exp]
  have hmem: ∀ z,z∈Metric.ball (0:ℂ) r→z∈Metric.closedBall (0:ℂ) R:=by
    intro z hz
    apply Metric.mem_closedBall.mpr
    rw [Metric.mem_ball] at hz
    linarith
  refine ⟨GR,?_,hJB.2.1,?_,hJB.2.2⟩
  · intro z hz
    exact DifferentiableOn.analyticAt (fun w hw↦(hJB.1 w hw).differentiableAt.differentiableWithinAt) (IsOpen.mem_nhds Metric.isOpen_ball hz)
  · intro z hz
    exact (hJB.1 z (Metric.closedBall_subset_ball r_lt_R hz)).deriv
def bD (R:ℝ) (f:ℂ→ℂ) :Set ℂ:={ρ:ℂ | ‖ρ‖ ≤R ∧ f ρ=0}
lemma aR {r:ℝ} {f:ℂ→ℂ}
    (fG:r<1)
    (cZ:(bD 1 f).Finite) :
    (bD r f).Finite:=by
  apply Set.Finite.subset cZ
  unfold bD
  refine setOf_subset_setOf.mpr ?_
  intro z hz
  exact ⟨by linarith,hz.2⟩
open Classical
noncomputable def vq (f:ℂ→ℂ) (z:ℂ) :ℂ:=
  if h1:AnalyticAt ℂ f z then
    if h2:analyticOrderAt f z≠ ⊤ then
      (h1.analyticOrderAt_ne_top.mp h2).choose z
    else 0
  else 0
lemma tK {R:ℝ} {f:ℂ→ℂ} {ρ:ℂ}
    (acR:R<1)
    (dV:AnalyticOnNhd ℂ f (Metric.closedBall (0:ℂ) 1))
    (cV:f 0≠0)
    (hρ:ρ∈bD R f) :
    ∃ Iz:ℂ→ℂ,AnalyticAt ℂ Iz ρ ∧ Iz ρ≠0 ∧ vq f ρ=Iz ρ ∧
      f =ᶠ[nhds ρ] fun z↦(z-ρ)^analyticOrderNatAt f ρ* Iz z:=by
  have DB:0∈Metric.closedBall (0:ℂ) 1:=by
    rw[mem_closedBall_iff_norm,sub_zero,norm_zero]
    exact zero_le_one
  have tL:ρ∈Metric.closedBall (0:ℂ) 1:=by
    rw[mem_closedBall_iff_norm,sub_zero]
    linarith[hρ.1]
  have Ga:analyticOrderAt f 0=0:=by
    rw[analyticOrderAt_eq_zero]
    exact Or.symm (Decidable.not_or_of_imp fun a a_1↦cV a)
  have zS:analyticOrderAt f ρ≠ ⊤ :=by
    refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected dV (Metric.isPreconnected_closedBall) DB tL (lt_top_iff_ne_top.mp ?_)
    rw[Ga]
    exact ENat.top_pos
  have rT:AnalyticAt ℂ f ρ:=by exact (dV ρ tL)
  obtain ⟨Iz,Bk,f_eq⟩:=(rT.analyticOrderAt_ne_top.mp zS).choose_spec
  set g:=(rT.analyticOrderAt_ne_top.mp zS).choose
  refine ⟨g,Iz,Bk,?_,f_eq⟩
  simp only [vq,rT, ↓reduceDIte,ne_eq,zS,not_false_eq_true,
    smul_eq_mul,g]
noncomputable def Cf (r:ℝ) (f:ℂ→ℂ) (z:ℂ) :ℂ:=
  if bF:(bD r f).Finite then
    if _:z∈bD r f then
      vq f z/ ∏ ρ∈(bF.toFinset \ {z}),(z-ρ)^(analyticOrderNatAt f ρ)
    else
      f z/ ∏ ρ∈(bF.toFinset),(z-ρ)^(analyticOrderNatAt f ρ)
  else 1
lemma jt (s:Finset ℂ) (g:ℂ→ℕ) (w:ℂ) :
    AnalyticAt ℂ (fun z=> ∏ ρ∈s,(z-ρ)^g ρ) w:=by
  induction s using Finset.induction with
  | empty=>
    simp only [Finset.prod_empty]
    exact analyticAt_const
  | @insert a s' hne ih=>
    have:(fun z=> ∏ ρ∈insert a s',(z-ρ)^g ρ)=fun z=>(z-a)^g a* ∏ ρ∈s',(z-ρ)^g ρ:=
      funext fun z=>Finset.prod_insert hne
    rw [this]
    exact ((analyticAt_id.sub analyticAt_const).pow _).mul ih
lemma vE {r R:ℝ} {f:ℂ→ℂ}
    (r_lt_R:r<R) (kV:R<1)
    (dV:AnalyticOnNhd ℂ f (Metric.closedBall (0:ℂ) 1))
    (cV:f 0≠0) :
    AnalyticOnNhd ℂ (Cf r f) (Metric.closedBall (0:ℂ) R) :=by
  intro w hw
  unfold Cf
  by_cases bF:(bD r f).Finite
  · simp only [bF, ↓reduceDIte]
    by_cases oW:w∈bD r f
    · obtain ⟨h_w,Dk,ME,Rb⟩:=tK (by linarith) (dV.mono (Metric.closedBall_subset_closedBall (by linarith))) cV oW;
      have h_eq: ∀ᶠ z in nhds w,(if h:z∈bD r f then vq f z/ ∏ ρ∈bF.toFinset \ {z},(z-ρ)^analyticOrderNatAt f ρ else f z/ ∏ ρ∈bF.toFinset,(z-ρ)^analyticOrderNatAt f ρ)=h_w z/ ∏ ρ∈bF.toFinset \ {w},(z-ρ)^analyticOrderNatAt f ρ:=by
        filter_upwards [ Rb.2,Dk.continuousAt.eventually_ne ME ] with z hz hz';
        by_cases h:z=w
        · subst h
          rw [dif_pos oW]
          congr 1
          exact Rb.1
        · have VY:z∉bD r f:=by
            intro hmem
            have hfz:f z=0:=hmem.2
            rw [hz] at hfz
            exact absurd hfz (mul_ne_zero (pow_ne_zero _ (sub_ne_zero_of_ne h)) hz')
          rw [dif_neg VY,hz]
          have Yh:w∈bF.toFinset:=bF.mem_toFinset.mpr oW
          rw [Finset.prod_eq_prod_sdiff_singleton_mul Yh (fun ρ=>(z-ρ)^analyticOrderNatAt f ρ)]
          rw [mul_comm ((z-w)^analyticOrderNatAt f w) (h_w z)]
          rw [mul_div_mul_right _ _ (pow_ne_zero _ (sub_ne_zero_of_ne h))]
      apply Dk.div _ _ |> fun h=>h.congr _;
      · use fun z=> ∏ ρ∈bF.toFinset \ { w },( z-ρ )^analyticOrderNatAt f ρ;
      · exact jt _ _ _
      · simp only [Finset.prod_eq_zero_iff,ne_eq,pow_eq_zero_iff',Finset.mem_sdiff,Finite.mem_toFinset,Finset.mem_singleton,not_exists,not_and,
          Decidable.not_not,and_imp]
        intro x _ Yj
        exact fun Yk=>absurd (sub_eq_zero.mp Yk).symm Yj
      · filter_upwards [ h_eq ] with z hz using hz.symm
    · apply AnalyticAt.congr _ _
      · exact fun z=>f z/ ∏ ρ∈bF.toFinset,( z-ρ )^analyticOrderNatAt f ρ
      · refine AnalyticAt.div ?_ ?_ ?_
        · exact dV w ( Metric.mem_closedBall.mpr <| le_trans hw.out <| by linarith )
        · exact jt _ _ _
        · simp only [ ne_eq,Finset.prod_eq_zero_iff,Finite.mem_toFinset,pow_eq_zero_iff',
          sub_eq_zero, ↓existsAndEq,true_and,not_and,Decidable.not_not]
          exact fun h=>absurd h oW
      · filter_upwards [ IsOpen.mem_nhds ( isOpen_compl_iff.mpr bF.isClosed ) oW ] with z hz
        split_ifs with h
        · exact absurd h hz
        · rfl
  · simp only [bF, ↓reduceDIte]
    exact analyticAt_const
noncomputable def kW (r R:ℝ) (f:ℂ→ℂ) (z:ℂ) :ℂ:=
  if bF:(bD r f).Finite then
    (Cf r f) z*(∏ ρ∈bF.toFinset,(R-z*(conj ρ)/R)^(analyticOrderNatAt f ρ))
  else 1
lemma IG {r R:ℝ} {f:ℂ→ℂ}
    (r_pos:0<r) (r_lt_R:r<R) (kV:R<1)
    (cZ:(bD 1 f).Finite)
    (dV:AnalyticOnNhd ℂ f (Metric.closedBall (0:ℂ) 1))
    (cV:f 0≠0) :
    AnalyticOnNhd ℂ (kW r R f) (Metric.closedBall (0:ℂ) R) :=by
  have R_pos:0<R:=lt_trans r_pos r_lt_R
  have fG:r<1:=lt_trans r_lt_R kV
  unfold kW
  by_cases bF:(bD r f).Finite
  · simp only [bF, ↓reduceDIte]
    refine AnalyticOnNhd.mul (vE r_lt_R kV dV cV) (Finset.analyticOnNhd_fun_prod (aR fG cZ).toFinset ?_)
    intro w hw
    refine AnalyticOnNhd.fun_pow (AnalyticOnNhd.sub (analyticOnNhd_const) (AnalyticOnNhd.div (AnalyticOnNhd.mul (analyticOnNhd_id) (analyticOnNhd_const)) (analyticOnNhd_const) ?_)) (analyticOrderAt f w).toNat
    intro w' hw'
    exact_mod_cast ne_of_gt R_pos
  · simp only [bF, ↓reduceDIte]
    exact analyticOnNhd_const
lemma MG {r R:ℝ} {f:ℂ→ℂ}
    (r_pos:0<r) (fG:r<1) (r_lt_R:r<R)
    (cZ:(bD 1 f).Finite)
    (cV:f 0≠0) :
    ‖kW r R f 0‖ =
      ‖f 0‖ *(∏ ρ∈(aR fG cZ).toFinset,(R/ ‖ρ‖)^(analyticOrderNatAt f ρ)) :=by
  have Oa: ¬(0∈bD r f) :=by
    apply notMem_setOf_iff.mpr
    simp only [norm_zero,not_and]
    intro r
    exact mem_support.mp cV
  unfold kW Cf
  simp only [aR fG cZ,Oa, ↓reduceDIte,zero_sub,zero_mul,zero_div,sub_zero,
    Complex.norm_mul,Complex.norm_div,norm_prod,norm_pow,norm_neg,norm_real,norm_eq_abs]
  rw[div_eq_mul_inv,mul_assoc,abs_of_pos (by linarith)]
  refine (mul_right_inj' (norm_ne_zero_iff.mpr cV)).mpr ?_
  rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  simp only [div_eq_inv_mul,mul_pow,inv_pow]
lemma Uq {B r R:ℝ} {f:ℂ→ℂ} {z:ℂ}
    (r_pos:0<r) (r_lt_R:r<R) (kV:R<1)
    (cZ:(bD 1 f).Finite)
    (dV:AnalyticOnNhd ℂ f (Metric.closedBall (0:ℂ) 1))
    (cV:f 0≠0) (IQ: ∀ (z:ℂ), ‖z‖ ≤R→ ‖f z‖ ≤B)
    (hz:z∈Metric.closedBall (0:ℂ) R) :
    ‖kW r R f z‖ ≤B:=by
  have fG:r<1:=lt_trans r_lt_R kV
  have R_pos:0<R:=lt_trans r_pos r_lt_R
  refine AnalyticOn.jF (Std.IsPreorder.le_refl R) (AnalyticOnNhd.analyticOn (IG r_pos r_lt_R kV cZ dV cV)) ?_ hz
  intro w hw
  rw[mem_sphere_iff_norm,sub_zero] at hw
  have Nw: ¬(w∈bD r f) :=by
    apply notMem_setOf_iff.mpr
    intro adQ
    linarith
  have OQ: ‖kW r R f w‖ = ‖f w‖ :=by
    unfold kW Cf
    simp only [aR fG cZ,Nw, ↓reduceDIte,Complex.norm_mul,Complex.norm_div,norm_prod,norm_pow]
    rw[div_eq_mul_inv,mul_assoc,mul_right_eq_self₀]
    by_cases QG: ‖f w‖ =0
    · exact Or.inr QG
    · apply Or.inl
      rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro w' Ur
      have hfact:(R:ℂ)-w*starRingEnd ℂ w'/R=(conj w-conj w')*w/R:=by
        rw[sub_mul, ← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hw,ofReal_pow]
        field_simp
      rw [hfact,norm_div,norm_mul, ← map_sub,norm_conj,Complex.norm_real,hw,Real.norm_of_nonneg (le_of_lt R_pos)]
      field_simp
      rw[← div_pow,div_self,one_pow]
      rw[Set.Finite.mem_toFinset] at Ur
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun h=>Nw (h ▸ Ur)))
  rw[OQ]
  exact IQ w (le_of_eq hw)
theorem Cc {B r R:ℝ} {f:ℂ→ℂ}
    (r_pos:0<r) (fG:r<1) (r_lt_R:r<R) (kV:R<1)
    (dV:AnalyticOnNhd ℂ f (Metric.closedBall (0:ℂ) 1)) (KD:f 0=1)
    (cZ:(bD 1 f).Finite) (IQ: ∀ z:ℂ, ‖z‖ ≤R→ ‖f z‖ ≤B) :
    ∑ ρ∈(aR fG cZ).toFinset,analyticOrderNatAt f ρ≤
      1/Real.log (R/r)*Real.log B:=by
  have R_pos:0<R:=lt_trans r_pos r_lt_R
  have zU:f 0≠0:=by rw [KD]; exact one_ne_zero
  have GS:=MG r_pos fG r_lt_R cZ zU
  rw[KD,norm_one,one_mul] at GS
  rw [one_div,inv_mul_eq_div,le_div_iff₀ (Real.log_pos (by simp only [lt_div_iff₀ r_pos,one_mul,r_lt_R])), ← Real.log_pow]
  refine Real.log_le_log (pow_pos (div_pos R_pos r_pos) _) ?_
  calc (R/r)^ ∑ ρ∈(aR fG cZ).toFinset,analyticOrderNatAt f ρ
      = ∏ ρ∈(aR fG cZ).toFinset,(R/r)^analyticOrderNatAt f ρ:=by
        rw [Finset.prod_pow_eq_pow_sum]
    _≤ ∏ ρ∈(aR fG cZ).toFinset,(R/ ‖ρ‖)^analyticOrderNatAt f ρ:=by
      apply Finset.prod_le_prod
      · intro ρ _
        exact pow_nonneg (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) _
      · intro ρ hρ
        have Rd:=(aR fG cZ).mem_toFinset.mp hρ
        refine pow_le_pow_left₀ (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) ?_ _
        refine div_le_div_of_nonneg_left (le_of_lt R_pos) (norm_pos_iff.mpr ?_) (Rd.1)
        rintro rfl
        exact zU Rd.2
    _≤B:=by
      rw[← GS]
      exact Uq r_pos r_lt_R kV cZ dV
        zU IQ (Metric.mem_closedBall_self (le_of_lt R_pos))
end

-- Zeta23.dQ.acC
section
open Set
noncomputable section
namespace Zeta23
@[simp] lemma RU (ρ:ℂ) :(reflect ρ).re=1-ρ.re:=by simp [reflect]
@[simp] lemma RV (ρ:ℂ) :(reflect ρ).im=ρ.im:=by simp [reflect]
@[simp] lemma reflect_reflect (ρ:ℂ) :reflect (reflect ρ)=ρ:=by
  simp [reflect]
lemma Gb:Function.Injective reflect:=
  Function.LeftInverse.injective reflect_reflect
namespace bT
variable (Z:bT) (T₁ T₂:ℝ)
lemma Ek {ρ:ℂ} (h:ρ∈Z.window T₁ T₂) :reflect ρ∈Z.window T₁ T₂:=
  ⟨Z.nI ρ h.1,by simpa [RV] using h.2⟩
theorem Gd:
    (Z.N T₁ T₂:ℝ)≤2* ∑ᶠ ρ∈Z.window T₁ T₂ ∩ {ρ | 1/2≤ρ.re},(Z.mult ρ:ℝ) :=by
  have hW:(Z.window T₁ T₂).Finite:=Z.nS T₁ T₂
  set A:=Z.window T₁ T₂ ∩ {ρ | ρ.re<1/2} with aag
  set B:=Z.window T₁ T₂ ∩ {ρ | 1/2≤ρ.re} with hBdef
  have hA:A.Finite:=hW.subset inter_subset_left
  have hB:B.Finite:=hW.subset inter_subset_left
  have abB:Z.window T₁ T₂=A ∪ B:=by
    ext ρ
    simp only [aag,hBdef,mem_union,mem_inter_iff,mem_setOf_eq]
    constructor
    · intro h
      rcases lt_or_ge ρ.re (1/2) with h' | h'
      · exact Or.inl ⟨h,h'⟩
      · exact Or.inr ⟨h,h'⟩
    · rintro (⟨h,_⟩ | ⟨h,_⟩) <;> exact h
  have hdisj:Disjoint A B:=by
    rw [Set.disjoint_left]
    rintro ρ ⟨_,h1⟩ ⟨_,h2⟩
    simp only [mem_setOf_eq] at h1 h2
    linarith
  have hN:Z.N T₁ T₂= ∑ᶠ ρ∈A,Z.mult ρ+ ∑ᶠ ρ∈B,Z.mult ρ:=by
    unfold bT.N
    rw [abB,finsum_mem_union hdisj hA hB]
  have himage:reflect '' A⊆B:=by
    rintro _ ⟨ρ,⟨abC,hlt⟩,rfl⟩
    refine ⟨Z.Ek T₁ T₂ abC,?_⟩
    simp only [mem_setOf_eq,RU] at hlt ⊢
    linarith
  have hAB: ∑ᶠ ρ∈A,Z.mult ρ≤ ∑ᶠ ρ∈B,Z.mult ρ:=by
    calc ∑ᶠ ρ∈A,Z.mult ρ= ∑ᶠ ρ∈A,Z.mult (reflect ρ) :=
          finsum_mem_congr rfl (fun ρ hρ=>(Z.eD ρ hρ.1.1).symm)
      _= ∑ᶠ σ∈reflect '' A,Z.mult σ:=(finsum_mem_image Gb.injOn).symm
      _≤ ∑ᶠ σ∈B,Z.mult σ:=Z.wC T₁ T₂ himage inter_subset_left
  have hcast:(∑ᶠ ρ∈B,(Z.mult ρ:ℝ))=((∑ᶠ ρ∈B,Z.mult ρ:ℕ) :ℝ) :=by
    rw [finsum_mem_eq_finite_toFinset_sum _ hB,finsum_mem_eq_finite_toFinset_sum _ hB,
      Nat.cast_sum]
  rw [hcast,hN]
  have hAB':((∑ᶠ ρ∈A,Z.mult ρ:ℕ) :ℝ)≤((∑ᶠ ρ∈B,Z.mult ρ:ℕ) :ℝ) :=by
    exact_mod_cast hAB
  push_cast
  linarith
end bT
end Zeta23
end
end

-- Zeta23.dQ.ju
section
open Complex Set Filter Topology Metric
noncomputable section
namespace Zeta23.dQ
theorem kO {K:Set ℂ} (hK:IsCompact K) :
    (K ∩ {ρ:ℂ | ρ≠1 ∧ riemannZeta ρ=0}).Finite:=by
  choose t ht hfin using iQ
  obtain ⟨I, -,hcover⟩:=hK.elim_nhds_subcover t (fun z _=>ht z)
  refine (I.finite_toSet.biUnion fun z _=>hfin z).subset ?_
  rintro ρ ⟨VL,hρ⟩
  obtain ⟨z,hzI,Iv⟩:=mem_iUnion₂.mp (hcover VL)
  exact mem_iUnion₂.mpr ⟨z,hzI,Iv,hρ⟩
def En (s₀ c u:ℂ) (z:ℂ) :ℂ:=riemannZeta (s₀+c*z)*u
lemma nO {s₀ c z:ℂ} (h:s₀+c*z≠1) :
    AnalyticAt ℂ (fun z:ℂ=>riemannZeta (s₀+c*z)) z:=by
  have hζ:AnalyticAt ℂ riemannZeta (s₀+c*z) :=cQ _ h
  have haff:AnalyticAt ℂ (fun z:ℂ=>s₀+c*z) z:=by fun_prop
  exact hζ.comp_of_eq haff rfl
lemma KE {s₀ c u z:ℂ} (h:s₀+c*z≠1) :AnalyticAt ℂ (En s₀ c u) z:=by
  have h1:=nO h
  have h2:AnalyticAt ℂ (fun _:ℂ=>u) z:=analyticAt_const
  have:=h1.mul h2
  exact this
lemma xW {s₀ c u w:ℂ} (hc:c≠0) (hu:u≠0) (h:s₀+c*w≠1) :
    analyticOrderNatAt (En s₀ c u) w=aP (s₀+c*w) :=by
  unfold analyticOrderNatAt aP En
  congr 1
  have haff:AnalyticAt ℂ (fun z:ℂ=>s₀+c*z) w:=by fun_prop
  have hcomp:AnalyticAt ℂ (fun z=>riemannZeta (s₀+c*z)) w:=nO h
  have hmul:(fun z↦riemannZeta (s₀+c*z)*u)=
      (fun z=>riemannZeta (s₀+c*z))*fun _=>u:=rfl
  rw [hmul,analyticOrderAt_mul hcomp analyticAt_const]
  have hconst:analyticOrderAt (fun _:ℂ=>u) w=0:=
    (analyticAt_const).analyticOrderAt_eq_zero.mpr hu
  rw [hconst,add_zero]
  have hderiv:deriv (fun z:ℂ=>s₀+c*z) w≠0:=by
    rw [deriv_const_add,deriv_const_mul _ differentiableAt_id,deriv_id'']; simpa using hc
  have:=analyticOrderAt_comp_of_deriv_ne_zero (f:=riemannZeta) haff hderiv
  simpa [Function.comp_def] using this
def wJ (t:ℝ) :ℝ:= ∑ᶠ ρ∈aD.window t (t+1) ∩ {ρ | 1/2≤ρ.re},(aP ρ:ℝ)
theorem IT:
    ∃ A₁:ℝ, ∀ t:ℝ,4≤ |t| →wJ t≤A₁*Real.log (|t| +3) :=by
  obtain ⟨A,C,hC,hgrowth⟩:=FZ
  have hL:=oR
  set A':ℝ:=max A 0 with hA'
  have Eo:0≤A':=le_max_right _ _
  set r:ℝ:=0.84 with hr
  set R:ℝ:=0.95 with hR
  have acS:0<Real.log (R/r) :=Real.log_pos (by norm_num [hr,hR])
  refine ⟨1/Real.log (R/r)*(|Real.log (3*C)| +2*A'),fun t ht=>?_⟩
  set c₀:ℂ:=2+(t+1/2:ℝ)* I with hc₀
  set κ:ℂ:=((19/10:ℝ) :ℂ) with hκ
  have VZ:κ≠0:=by simp [hκ]
  have MH: ‖κ‖ =1.9:=by simp [hκ]; norm_num
  have Rg:(1/3:ℝ)≤ ‖riemannZeta c₀‖ :=by simpa [hc₀] using hL (t+1/2)
  have Ny:riemannZeta c₀≠0:=by
    intro h; rw [h,norm_zero] at Rg; norm_num at Rg
  set u:ℂ:=(riemannZeta c₀)⁻¹ with hu
  have hu0:u≠0:=inv_ne_zero Ny
  have hnu: ‖u‖ ≤3:=by
    rw [hu,norm_inv]; rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  set g:ℂ→ℂ:=En c₀ κ u with hg
  have acT: |t+1/2| ≤ ‖c₀-1‖ :=by
    have:(c₀-1).im=t+1/2:=by simp [hc₀]
    rw [← this]; exact Complex.abs_im_le_norm _
  have ht':3.5≤ |t+1/2| :=by
    rcases le_abs'.mp ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hdist: ∀ z:ℂ, ‖z‖ ≤1→ |t+1/2| -1.9* ‖z‖ ≤ ‖c₀+κ*z-1‖ :=by
    intro z hz
    have h1: ‖c₀-1‖ - ‖κ*z‖ ≤ ‖c₀+κ*z-1‖ :=by
      have:=norm_sub_norm_le (c₀-1) (-(κ*z))
      rw [norm_neg] at this
      have e:c₀-1- -(κ*z)=c₀+κ*z-1:=by ring
      rw [e] at this; linarith
    rw [norm_mul,MH] at h1; linarith
  have hne1: ∀ z:ℂ, ‖z‖ ≤1→c₀+κ*z≠1:=by
    intro z hz h
    have:=hdist z hz
    rw [h,sub_self,norm_zero] at this
    nlinarith
  have dV:AnalyticOnNhd ℂ g (Metric.closedBall (0:ℂ) 1) :=by
    intro z hz
    rw [Metric.mem_closedBall,dist_zero_right] at hz
    exact KE (hne1 z hz)
  have hg0:g 0=1:=by simp [hg,En,hu,Ny]
  have hfin:(bD 1 g).Finite:=by
    have hK:=kO (isCompact_closedBall c₀ (1.9:ℝ))
    refine (hK.image fun ρ=>(ρ-c₀)/κ).subset ?_
    rintro z ⟨hz,hgz⟩
    refine ⟨c₀+κ*z,⟨?_,hne1 z hz,?_⟩,?_⟩
    · rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_mul,MH]; nlinarith [norm_nonneg z]
    · simpa [hg,En,hu0] using hgz
    · show (c₀+κ*z-c₀)/κ=z
      rw [add_sub_cancel_left,mul_div_cancel_left₀ _ VZ]
  set B:ℝ:=3*C*(|t| +6)^A' with hB
  have adw:0<B:=by positivity
  have hfz: ∀ z:ℂ, ‖z‖ ≤R→ ‖g z‖ ≤B:=by
    intro z hz
    have hz1: ‖z‖ ≤1:=hz.trans (by norm_num [hR])
    set s:ℂ:=c₀+κ*z with hs
    have hsre:(0.15:ℝ)≤ s.re:=by
      have:s.re=2+1.9*z.re:=by norm_num [hs,hc₀,hκ]
      rw [this]
      obtain ⟨h1, -⟩:=abs_le.mp ((abs_re_le_norm z).trans hz)
      rw [hR] at h1; nlinarith
    have hs1:1≤ ‖s-1‖ :=by have:=hdist z hz1; rw [hR] at hz; nlinarith
    have OT: |s.im| +3≤ |t| +6:=by
      have:s.im=t+1/2+1.9*z.im:=by norm_num [hs,hc₀,hκ]
      rw [this]
      have hzi:=(abs_im_le_norm z).trans hz; rw [hR] at hzi
      have h1:=abs_add_le (t+1/2) (1.9*z.im)
      have h2: |1.9*z.im| ≤1.9*0.95:=by
        rw [abs_mul,abs_of_pos (by norm_num:(0:ℝ)<1.9)]; nlinarith
      have h3: |t+1/2| ≤ |t| +1/2:=by simpa using abs_add_le t (1/2)
      linarith
    have h1: ‖riemannZeta s‖ ≤C*(|s.im| +3)^A:=hgrowth s hsre hs1
    have hbase:1≤ |s.im| +3:=by linarith [abs_nonneg s.im]
    have h2:(|s.im| +3)^A≤(|s.im| +3)^A':=Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _)
    have h3:(|s.im| +3)^A'≤(|t| +6)^A':=Real.rpow_le_rpow (by linarith [abs_nonneg s.im]) OT Eo
    calc ‖g z‖ = ‖riemannZeta s‖ * ‖u‖ :=by simp [hg,En,hs]
      _≤(C*(|t| +6)^A')*3:=by
          apply mul_le_mul (h1.trans ((mul_le_mul_of_nonneg_left (h2.trans h3) hC.le))) hnu (norm_nonneg _)
          positivity
      _=B:=by rw [hB]; ring
  have hZ:=Cc (B:=B) (r:=r) (R:=R) (by norm_num [hr]) (by norm_num [hr])
    (by norm_num [hr,hR]) (by norm_num [hR]) dV hg0 hfin hfz
  set W:Set ℂ:=aD.window t (t+1) ∩ {ρ | 1/2≤ρ.re} with hW
  have RW:W.Finite:=(aD.nS t (t+1)).subset inter_subset_left
  set φ:ℂ→ℂ:=fun ρ=>(ρ-c₀)/κ with hφ
  have KI:Function.Injective φ:=by
    intro a b h; simp only [hφ] at h
    have:=congrArg (fun w=>c₀+κ*w) h
    simpa [mul_div_cancel₀ _ VZ] using this
  have OU: ∀ ρ,c₀+κ*φ ρ=ρ:=by intro ρ; simp only [hφ]; field_simp; ring
  have aah: ∀ ρ∈W,φ ρ∈(aR (by norm_num [hr]:r<1) hfin).toFinset:=by
    rintro ρ ⟨⟨Wa,adR,adx⟩,aai⟩
    simp only [Set.Finite.mem_toFinset]
    have hρ:aE ρ:=Wa
    refine ⟨?_,?_⟩
    · 
      simp only [hφ,norm_div,MH]
      rw [div_le_iff₀ (by norm_num),hr]
      have hre:(ρ-c₀).re=ρ.re-2:=by simp [hc₀]
      have him:(ρ-c₀).im=ρ.im-(t+1/2) :=by simp [hc₀]
      have hsq: ‖ρ-c₀‖ ^2≤(0.84*1.9)^2:=by
        rw [Complex.sq_norm,Complex.normSq_apply,hre,him]
        have:=hρ.2.2; have:=aai.out
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq
    · show g (φ ρ)=0
      simp only [hg,En,OU]; rw [hρ.1,zero_mul]
  have aaj: ∀ ρ∈W,(aP ρ:ℝ)=(analyticOrderNatAt g (φ ρ) :ℝ) :=by
    rintro ρ ⟨⟨Wa, -, -⟩, -⟩
    have hρ:aE ρ:=Wa
    rw [xW VZ hu0 (by rw [OU]; exact hρ.zK.2),OU]
  have hsum:wJ t≤((∑ ρ'∈(aR (by norm_num [hr]:r<1) hfin).toFinset,
      analyticOrderNatAt g ρ':ℕ) :ℝ) :=by
    unfold wJ
    rw [← hW,finsum_mem_eq_finite_toFinset_sum _ RW,
      Finset.sum_congr rfl (fun ρ hρ=>aaj ρ (RW.mem_toFinset.mp hρ)),
      ← Finset.sum_image (f:=fun w=>(analyticOrderNatAt g w:ℝ))
        (fun a _ b _ h=>KI h)]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro w hw
      obtain ⟨ρ,hρ,rfl⟩:=Finset.mem_image.mp hw
      exact aah ρ (RW.mem_toFinset.mp hρ)
    · intros; positivity
  have RY:1≤Real.log (|t| +3) :=by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have:=Real.exp_one_lt_d9; linarith [abs_nonneg t]
  have aak:Real.log (|t| +6)≤2*Real.log (|t| +3) :=by
    rw [← Real.log_rpow (by positivity),Real.rpow_two]
    apply Real.log_le_log (by positivity); nlinarith [abs_nonneg t]
  have Fv:Real.log B≤(|Real.log (3*C)| +2*A')*Real.log (|t| +3) :=by
    rw [hB,Real.log_mul (by positivity) (by positivity),Real.log_rpow (by positivity)]
    have h1:=le_abs_self (Real.log (3*C))
    have h2: |Real.log (3*C)| ≤ |Real.log (3*C)| *Real.log (|t| +3) :=
      le_mul_of_one_le_right (abs_nonneg _) RY
    have h3:A'*Real.log (|t| +6)≤A'*(2*Real.log (|t| +3)) :=
      mul_le_mul_of_nonneg_left aak Eo
    linarith
  calc wJ t≤_:=hsum
    _≤1/Real.log (R/r)*Real.log B:=by exact_mod_cast hZ
    _≤1/Real.log (R/r)*((|Real.log (3*C)| +2*A')*Real.log (|t| +3)) :=
        mul_le_mul_of_nonneg_left Fv (by positivity)
    _=_:=by ring
theorem QH (t:ℝ) (ht: |t| ≤4) :(nL t (t+1) :ℝ)≤nL (-4) 5:=by
  obtain ⟨h1,h2⟩:=abs_le.mp ht
  have hsub:aD.window t (t+1)⊆aD.window (-4) 5:=by
    rintro ρ ⟨hρ,ha,hb⟩; exact ⟨hρ,by linarith,by linarith⟩
  have h':aD.N t (t+1)≤aD.N (-4) 5:=
    aD.wC (-4) 5 hsub subset_rfl
  rw [jR,jR] at h'
  exact_mod_cast h'
theorem oH: ∃ A₀:ℝ,1≤A₀ ∧ ∀ t:ℝ,
    (nL t (t+1) :ℝ)≤A₀*Real.log (|t| +3) :=by
  obtain ⟨A₁,hA₁⟩:=IT
  set K:ℝ:=(nL (-4) 5:ℝ) with hK
  have hK0:0≤K:=by positivity
  refine ⟨max 1 (max (2*A₁) K),le_max_left _ _,fun t=>?_⟩
  have RY:1≤Real.log (|t| +3) :=by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have:=Real.exp_one_lt_d9; linarith [abs_nonneg t]
  have hhalf:(nL t (t+1) :ℝ)≤2*wJ t:=by
    have:=aD.Gd t (t+1)
    simpa [wJ,jR] using this
  rcases le_or_gt 4 |t| with ht | ht
  · calc (nL t (t+1) :ℝ)≤2*wJ t:=hhalf
      _≤2*(A₁*Real.log (|t| +3)) :=by
          have:=hA₁ t ht; nlinarith
      _=(2*A₁)*Real.log (|t| +3) :=by ring
      _≤ max 1 (max (2*A₁) K)*Real.log (|t| +3) :=by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact le_trans (le_max_left _ _) (le_max_right _ _)
  · calc (nL t (t+1) :ℝ)≤K:=QH t ht.le
      _≤K*Real.log (|t| +3) :=le_mul_of_one_le_right hK0 RY
      _≤ max 1 (max (2*A₁) K)*Real.log (|t| +3) :=by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact le_trans (le_max_right _ _) (le_max_right _ _)
theorem rV: ∃ A₀:ℝ,1≤A₀ ∧ ∀ t:ℝ,
    (aD.N t (t+1) :ℝ)≤A₀*Real.log (|t| +3) :=by
  simpa only [jR] using oH
end Zeta23.dQ
end
end

-- Zeta23.lK
section
namespace Zeta23
open Complex
open scoped ContDiff
end Zeta23
end

-- Zeta23.lK.Series
section
noncomputable section
namespace Zeta23
namespace nT
open Complex Filter Topology
def cW (n:ℕ) (z:ℂ) :ℂ:=(1+z/(n+1))*Complex.exp (-(z/(n+1)))-1
lemma rW (n:ℕ) (z:ℂ) :
    1+cW n z=(1+z/(n+1))*Complex.exp (-(z/(n+1))) :=by
  unfold cW
  ring
lemma jS (n:ℕ) : ‖((n:ℂ)+1)‖ =(n:ℝ)+1:=by
  rw [show ((n:ℂ)+1)=(((n:ℝ)+1:ℝ) :ℂ) by push_cast; ring,Complex.norm_real]
  rw [Real.norm_eq_abs,abs_of_pos (by positivity)]
lemma Dm {z:ℂ} {n:ℕ} (h: ‖z‖ ≤(n:ℝ)+1) :
    ‖cW n z‖ ≤3*(‖z‖ /((n:ℝ)+1))^2:=by
  set w:ℂ:=z/((n:ℂ)+1) with hwdef
  have hn1:(0:ℝ)<(n:ℝ)+1:=by positivity
  have Ut: ‖w‖ = ‖z‖ /((n:ℝ)+1) :=by
    rw [hwdef,norm_div,jS]
  have hwn: ‖w‖ ≤1:=by
    rw [Ut,div_le_one hn1]
    exact h
  have hr: ‖Complex.exp (-w)-1+w‖ ≤ ‖w‖ ^2:=by
    have hx: ‖(-w:ℂ)‖ ≤1:=by rwa [norm_neg]
    have h2:=norm_exp_sub_one_sub_id_le hx
    rw [norm_neg] at h2
    calc ‖Complex.exp (-w)-1+w‖ = ‖Complex.exp (-w)-1-(-w)‖ :=by ring_nf
      _≤ ‖w‖ ^2:=h2
  have hident:cW n z=(Complex.exp (-w)-1+w)-w^2
      +w*(Complex.exp (-w)-1+w) :=by
    unfold cW
    ring
  have abD: ‖(w:ℂ)^2‖ = ‖w‖ ^2:=norm_pow _ _
  calc ‖cW n z‖
      ≤ ‖(Complex.exp (-w)-1+w)-w^2‖ + ‖w*(Complex.exp (-w)-1+w)‖ :=by
        rw [hident]
        exact norm_add_le _ _
    _≤(‖w‖ ^2+ ‖w‖ ^2)+ ‖w‖ * ‖w‖ ^2:=by
        have h1: ‖(Complex.exp (-w)-1+w)-w^2‖ ≤ ‖w‖ ^2+ ‖w‖ ^2:=by
          calc ‖(Complex.exp (-w)-1+w)-w^2‖
              ≤ ‖Complex.exp (-w)-1+w‖ + ‖(w:ℂ)^2‖ :=norm_sub_le _ _
            _≤ ‖w‖ ^2+ ‖w‖ ^2:=by
                rw [abD]
                exact add_le_add hr le_rfl
        have h2: ‖w*(Complex.exp (-w)-1+w)‖ ≤ ‖w‖ * ‖w‖ ^2:=by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hr (norm_nonneg _)
        linarith
    _≤3* ‖w‖ ^2:=by nlinarith [norm_nonneg w,hwn,sq_nonneg ‖w‖]
    _=3*(‖z‖ /((n:ℝ)+1))^2:=by rw [Ut]
lemma zj (R:ℝ) :Summable (fun n:ℕ=>3*(R/((n:ℝ)+1))^2) :=by
  have h1:Summable (fun n:ℕ=>(((n:ℝ)+1)^2)⁻¹) :=by
    have h2:Summable (fun n:ℕ=>(((n:ℝ))^2)⁻¹) :=by
      have:=Real.summable_nat_rpow_inv.mpr (by norm_num:(1:ℝ)<2)
      have heq:(fun n:ℕ=>((n:ℝ)^(2:ℝ))⁻¹)=fun n:ℕ=>(((n:ℝ))^2)⁻¹:=by
        funext n
        rw [show ((2:ℝ))=((2:ℕ) :ℝ) by norm_num,Real.rpow_natCast]
      rwa [heq] at this
    have:=(summable_nat_add_iff 1).mpr h2
    simpa [add_comm] using this
  have h3:(fun n:ℕ=>3*(R/((n:ℝ)+1))^2)
      =fun n:ℕ=>(3*R^2)*((((n:ℝ)+1)^2)⁻¹) :=by
    funext n
    rw [div_pow]
    ring
  rw [h3]
  exact h1.mul_left _
lemma DE (z:ℂ) :Summable (fun n=> ‖cW n z‖) :=by
  refine (zj ‖z‖).of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖⌉₊] with n hn
  rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  refine Dm ?_
  calc ‖z‖ ≤(⌈‖z‖⌉₊ :ℝ) :=Nat.le_ceil _
    _≤(n:ℝ) :=by exact_mod_cast hn
    _≤(n:ℝ)+1:=by linarith
lemma sw (z:ℂ) :Multipliable fun n=>1+cW n z:=
  Complex.multipliable_one_add_of_summable ((DE z).of_norm)
lemma oA (N:ℕ) :
    ((harmonic N:ℚ) :ℝ)= ∑ m∈Finset.range N,(1:ℝ)/((m:ℝ)+1) :=by
  rw [harmonic]
  push_cast
  refine Finset.sum_congr rfl fun m _=>?_
  rw [one_div]
lemma KM {z:ℂ} (_hz:z∈Complex.integerComplement) {N:ℕ} (hN:1≤N) :
    (Complex.GammaSeq z N)⁻¹
      =z*Complex.exp ((((∑ m∈Finset.range N,(1:ℝ)/((m:ℝ)+1))
            -Real.log N:ℝ) :ℂ)*z)
          * ∏ n∈Finset.range N,(1+cW n z) :=by
  have hNR:(0:ℝ)<(N:ℝ) :=by exact_mod_cast hN
  have hprod: ∏ n∈Finset.range N,(1+cW n z)
      =(∏ n∈Finset.range N,(1+z/((n:ℂ)+1)))
          *Complex.exp (-(∑ m∈Finset.range N,z/((m:ℂ)+1))) :=by
    calc ∏ n∈Finset.range N,(1+cW n z)
        = ∏ n∈Finset.range N,(1+z/((n:ℂ)+1))
            *Complex.exp (-(z/((n:ℂ)+1))) :=
          Finset.prod_congr rfl fun n _=>rW n z
      _=(∏ n∈Finset.range N,(1+z/((n:ℂ)+1)))
            * ∏ n∈Finset.range N,Complex.exp (-(z/((n:ℂ)+1))) :=
          Finset.prod_mul_distrib
      _=(∏ n∈Finset.range N,(1+z/((n:ℂ)+1)))
            *Complex.exp (∑ n∈Finset.range N, -(z/((n:ℂ)+1))) :=by
          rw [Complex.exp_sum]
      _=_:=by rw [← Finset.sum_neg_distrib]
  have abE:((N.factorial:ℕ) :ℂ)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have Yl:((N:ℂ))≠0:=Nat.cast_ne_zero.mpr (by omega)
  have RK:(N:ℂ)^z=Complex.exp (((Real.log N:ℝ) :ℂ)*z) :=by
    rw [Complex.cpow_def_of_ne_zero Yl]
    congr 2
    rw [show ((N:ℂ))=(((N:ℝ) :ℝ) :ℂ) by push_cast; ring]
    exact (Complex.ofReal_log hNR.le).symm
  have hdenom: ∏ j∈Finset.range (N+1),(z+(j:ℂ))
      =z* ∏ n∈Finset.range N,(z+((n:ℂ)+1)) :=by
    rw [Finset.prod_range_succ']
    rw [Nat.cast_zero,add_zero,mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun n _=>?_
    push_cast
    ring
  have Uv:((N.factorial:ℕ) :ℂ)= ∏ n∈Finset.range N,((n:ℂ)+1) :=by
    rw [show N.factorial= ∏ n∈Finset.range N,(n+1) from
      (Finset.prod_range_add_one_eq_factorial N).symm]
    push_cast
    rfl
  have hfrac: ∏ n∈Finset.range N,(1+z/((n:ℂ)+1))
      =(∏ n∈Finset.range N,(z+((n:ℂ)+1)))/((N.factorial:ℕ) :ℂ) :=by
    have h1: ∀ n∈Finset.range N,(1+z/((n:ℂ)+1))
        =(z+((n:ℂ)+1))/((n:ℂ)+1) :=by
      intro n _
      have hne:((n:ℂ)+1)≠0:=Nat.cast_add_one_ne_zero n
      field_simp
      ring
    rw [Finset.prod_congr rfl h1,Finset.prod_div_distrib,Uv]
  have Wb:(((∑ m∈Finset.range N,(1:ℝ)/((m:ℝ)+1)) :ℝ) :ℂ)
      = ∑ m∈Finset.range N,1/((m:ℂ)+1) :=by
    push_cast
    rfl
  have aal: ∑ m∈Finset.range N,z/((m:ℂ)+1)
      =z* ∑ m∈Finset.range N,1/((m:ℂ)+1) :=by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _=>?_
    ring
  rw [Complex.GammaSeq,hprod,hfrac,hdenom,RK,aal, ← Wb]
  rw [Complex.ofReal_sub,sub_mul,Complex.exp_sub]
  set A:ℂ:= ∏ n∈Finset.range N,(z+((n:ℂ)+1)) with hA
  set E1:ℂ:=Complex.exp ((((∑ m∈Finset.range N,(1:ℝ)/((m:ℝ)+1)) :ℝ) :ℂ)*z)
    with hE1
  set E2:ℂ:=Complex.exp (((Real.log N:ℝ) :ℂ)*z) with hE2
  have ady:E1≠0:=Complex.exp_ne_zero _
  have adz:E2≠0:=Complex.exp_ne_zero _
  have Xn:Complex.exp (-(z*(((∑ m∈Finset.range N,(1:ℝ)/((m:ℝ)+1)) :ℝ) :ℂ)))
      =E1⁻¹:=by
    rw [hE1, ← Complex.exp_neg]
    congr 1
    ring
  rw [Xn]
  field_simp
theorem mD {z:ℂ} (hz:z∈Complex.integerComplement) :
    (Complex.Gamma z)⁻¹
      =z*Complex.exp ((Real.eulerMascheroniConstant:ℂ)*z)
          * ∏' n:ℕ,(1+cW n z) :=by
  have hzero: ∀ m:ℕ,z≠ -(m:ℂ) :=by
    intro m h
    exact hz ⟨-(m:ℤ),by push_cast; rw [h]⟩
  have hL:Tendsto (fun N=>(Complex.GammaSeq z N)⁻¹) atTop (𝓝 ((Complex.Gamma z)⁻¹)) :=
    (Complex.GammaSeq_tendsto_Gamma z).inv₀ (Complex.Gamma_ne_zero hzero)
  have abF:Tendsto (fun N:ℕ=>
      ((∑ m∈Finset.range N,(1:ℝ)/((m:ℝ)+1))-Real.log N:ℝ))
      atTop (𝓝 Real.eulerMascheroniConstant) :=by
    refine Real.tendsto_harmonic_sub_log.congr fun n=>?_
    rw [oA]
  have hexp:Tendsto (fun N:ℕ=>Complex.exp
      ((((∑ m∈Finset.range N,(1:ℝ)/((m:ℝ)+1))-Real.log N:ℝ) :ℂ)*z))
      atTop (𝓝 (Complex.exp ((Real.eulerMascheroniConstant:ℂ)*z))) :=by
    have h2:Tendsto (fun N:ℕ=>
        ((((∑ m∈Finset.range N,(1:ℝ)/((m:ℝ)+1))-Real.log N:ℝ) :ℂ)))
        atTop (𝓝 ((Real.eulerMascheroniConstant:ℝ) :ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp abF
    exact (Complex.continuous_exp.tendsto _).comp (h2.mul_const z)
  have hP:Tendsto (fun N=> ∏ n∈Finset.range N,(1+cW n z)) atTop
      (𝓝 (∏' n:ℕ,(1+cW n z))) :=
    (sw z).hasProd.tendsto_prod_nat
  have hRHS:Tendsto (fun N:ℕ=>z*Complex.exp
      ((((∑ m∈Finset.range N,(1:ℝ)/((m:ℝ)+1))-Real.log N:ℝ) :ℂ)*z)
      * ∏ n∈Finset.range N,(1+cW n z)) atTop
      (𝓝 (z*Complex.exp ((Real.eulerMascheroniConstant:ℂ)*z)
        * ∏' n:ℕ,(1+cW n z))) :=
    (tendsto_const_nhds.mul hexp).mul hP
  have heq: ∀ᶠ N in atTop,(Complex.GammaSeq z N)⁻¹
      =z*Complex.exp
        ((((∑ m∈Finset.range N,(1:ℝ)/((m:ℝ)+1))-Real.log N:ℝ) :ℂ)*z)
      * ∏ n∈Finset.range N,(1+cW n z) :=by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact KM hz hN
  exact tendsto_nhds_unique (hL.congr' heq) hRHS
lemma nP {z:ℂ} (hz:z∈Complex.integerComplement) (n:ℕ) :
    logDeriv (fun s=>1+cW n s) z=1/(z+n+1)-1/((n:ℂ)+1) :=by
  have hn1:((n:ℂ)+1)≠0:=Nat.cast_add_one_ne_zero n
  have hzn:z+((n:ℂ)+1)≠0:=by
    have:=Complex.integerComplement_add_ne_zero hz ((n:ℤ)+1)
    push_cast at this ⊢
    convert this using 2
  have Ym:z+(n:ℂ)+1≠0:=by
    rw [add_assoc]
    exact hzn
  have hfun:(fun s=>1+cW n s)
      =fun s:ℂ=>(1+s/((n:ℂ)+1))*Complex.exp (-(s/((n:ℂ)+1))) :=by
    funext s
    exact rW n s
  rw [hfun]
  have h1z:(1+z/((n:ℂ)+1))≠0:=by
    intro h
    apply hzn
    have h2:=congrArg (fun t=>t*((n:ℂ)+1)) h
    simp only [add_mul,one_mul,zero_mul] at h2
    rw [div_mul_cancel₀ _ hn1] at h2
    rw [← h2]
    ring
  have hd1:HasDerivAt (fun s:ℂ=>1+s/((n:ℂ)+1)) (1/((n:ℂ)+1)) z:=by
    have h3:=((hasDerivAt_id z).div_const ((n:ℂ)+1)).const_add 1
    simpa [one_div] using h3
  have hd2:HasDerivAt (fun s:ℂ=>Complex.exp (-(s/((n:ℂ)+1))))
      (-(1/((n:ℂ)+1))*Complex.exp (-(z/((n:ℂ)+1)))) z:=by
    have hlin:HasDerivAt (fun s:ℂ=> -(s/((n:ℂ)+1))) (-(1/((n:ℂ)+1))) z:=by
      exact ((hasDerivAt_id z).div_const ((n:ℂ)+1)).neg
    have h5:=hlin.cexp
    simpa [mul_comm] using h5
  have hprod:HasDerivAt
      (fun s:ℂ=>(1+s/((n:ℂ)+1))*Complex.exp (-(s/((n:ℂ)+1))))
      (1/((n:ℂ)+1)*Complex.exp (-(z/((n:ℂ)+1)))
        +(1+z/((n:ℂ)+1))*(-(1/((n:ℂ)+1))*Complex.exp (-(z/((n:ℂ)+1))))) z:=
    hd1.mul hd2
  unfold logDeriv
  rw [Pi.div_apply,hprod.deriv]
  have acV:Complex.exp (-(z/((n:ℂ)+1)))≠0:=Complex.exp_ne_zero _
  have h3:(1:ℂ)+(n:ℂ)+z≠0:=by
    intro h
    apply Ym
    linear_combination h
  field_simp [h3]
  have h4:((1:ℂ)+(n:ℂ)+z)*((1+(n:ℂ)+z)⁻¹)=1:=mul_inv_cancel₀ h3
  linear_combination (-z)*h4
theorem lU {z:ℂ} (hz:z∈Complex.integerComplement) :
    Summable (fun n:ℕ=>1/((n:ℂ)+1)-1/(z+n+1)) :=by
  refine Summable.of_norm ?_
  refine Summable.of_norm_bounded_eventually
    (g:=fun n:ℕ=>2* ‖z‖ *((((n:ℝ)+1)^2)⁻¹)) ?_ ?_
  · have h1:Summable (fun n:ℕ=>(((n:ℝ)+1)^2)⁻¹) :=by
      have h2:Summable (fun n:ℕ=>(((n:ℝ))^2)⁻¹) :=by
        have h3:=Real.summable_nat_rpow_inv.mpr (by norm_num:(1:ℝ)<2)
        have heq:(fun n:ℕ=>((n:ℝ)^(2:ℝ))⁻¹)=fun n:ℕ=>(((n:ℝ))^2)⁻¹:=by
          funext n
          rw [show ((2:ℝ))=((2:ℕ) :ℝ) by norm_num,Real.rpow_natCast]
        rwa [heq] at h3
      have h4:=(summable_nat_add_iff 1).mpr h2
      simpa [add_comm] using h4
    exact h1.mul_left _
  · rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop ⌈2* ‖z‖⌉₊] with n hn
    have hn1:((n:ℂ)+1)≠0:=Nat.cast_add_one_ne_zero n
    have hzn:z+((n:ℂ)+1)≠0:=by
      have:=Complex.integerComplement_add_ne_zero hz ((n:ℤ)+1)
      push_cast at this ⊢
      convert this using 2
    have Ym:z+(n:ℂ)+1≠0:=by
      rw [add_assoc]
      exact hzn
    have hident:1/((n:ℂ)+1)-1/(z+n+1)
        =z/(((n:ℂ)+1)*(z+n+1)) :=by
      field_simp
      ring
    have h2n:2* ‖z‖ ≤(n:ℝ) :=by
      calc 2* ‖z‖ ≤(⌈2* ‖z‖⌉₊ :ℝ) :=Nat.le_ceil _
        _≤(n:ℝ) :=by exact_mod_cast hn
    have hlow:((n:ℝ)+1)/2≤ ‖z+(n:ℂ)+1‖ :=by
      have h1: ‖((n:ℂ)+1)‖ - ‖z‖ ≤ ‖z+(n:ℂ)+1‖ :=by
        have h2:=norm_sub_le (z+(n:ℂ)+1) z
        have h3:(z+(n:ℂ)+1)-z=((n:ℂ)+1) :=by ring
        rw [h3] at h2
        linarith
      rw [jS] at h1
      linarith [norm_nonneg z]
    rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),hident,norm_div,norm_mul,
      jS]
    calc ‖z‖ /(((n:ℝ)+1)* ‖z+(n:ℂ)+1‖)
        ≤ ‖z‖ /(((n:ℝ)+1)*(((n:ℝ)+1)/2)) :=by
          gcongr
      _=2* ‖z‖ *((((n:ℝ)+1)^2)⁻¹) :=by
          field_simp
theorem Bm {z:ℂ} (hz:z∈Complex.integerComplement) :
    HasSum (fun n:ℕ=>1/((n:ℂ)+1)-1/(z+n+1))
      (Complex.digamma z+(Real.eulerMascheroniConstant:ℂ)+1/z) :=by
  set γc:ℂ:=((Real.eulerMascheroniConstant:ℝ) :ℂ) with Wd
  have hz0:z≠0:=Complex.integerComplement.ne_zero hz
  have hzero: ∀ m:ℕ,z≠ -(m:ℂ) :=by
    intro m h
    exact hz ⟨-(m:ℤ),by push_cast; rw [h]⟩
  have Fw:Complex.Gamma z≠0:=Complex.Gamma_ne_zero hzero
  have Uw:IsOpen Complex.integerComplement:=isOpen_compl_range_intCast
  set U:Set ℂ:=Metric.ball (0:ℂ) (‖z‖ +1) with hU
  have hUopen:IsOpen U:=Metric.isOpen_ball
  have hzU:z∈U:=by
    rw [hU,Metric.mem_ball,dist_zero_right]
    linarith [norm_nonneg z]
  have htend:MultipliableLocallyUniformlyOn (fun n (s:ℂ)=>1+cW n s) U:=by
    refine Summable.multipliableLocallyUniformlyOn_nat_one_add hUopen
      (zj (‖z‖ +1)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖ +1⌉₊] with n hn x hx
      have hx1: ‖x‖ ≤ ‖z‖ +1:=by
        rw [hU,Metric.mem_ball,dist_zero_right] at hx
        linarith
      have hn1: ‖z‖ +1≤(n:ℝ)+1:=by
        calc ‖z‖ +1≤(⌈‖z‖ +1⌉₊ :ℝ) :=Nat.le_ceil _
          _≤(n:ℝ) :=by exact_mod_cast hn
          _≤(n:ℝ)+1:=by linarith
      calc ‖cW n x‖ ≤3*(‖x‖ /((n:ℝ)+1))^2:=
            Dm (le_trans hx1 hn1)
        _≤3*((‖z‖ +1)/((n:ℝ)+1))^2:=by
            gcongr
    · intro n
      have hc:Continuous (cW n) :=by
        unfold cW
        fun_prop
      exact hc.continuousOn
  have hfne: ∀ n:ℕ,(fun s:ℂ=>1+cW n s) z≠0:=by
    intro n
    have hn1:((n:ℂ)+1)≠0:=Nat.cast_add_one_ne_zero n
    have hzn:z+((n:ℂ)+1)≠0:=by
      have:=Complex.integerComplement_add_ne_zero hz ((n:ℤ)+1)
      push_cast at this ⊢
      convert this using 2
    simp only [rW]
    apply mul_ne_zero _ (Complex.exp_ne_zero _)
    intro h
    apply hzn
    have h2:=congrArg (fun t=>t*((n:ℂ)+1)) h
    simp only [add_mul,one_mul,zero_mul] at h2
    rw [div_mul_cancel₀ _ hn1] at h2
    rw [← h2]
    ring
  have hgne:z*Complex.exp (γc*z)≠0:=mul_ne_zero hz0 (Complex.exp_ne_zero _)
  have Yn:(∏' n:ℕ,(1+cW n z))≠0:=by
    intro h
    have h2:=mD hz
    rw [← Wd,h,mul_zero] at h2
    exact inv_ne_zero Fw h2
  have Uz:Summable fun n:ℕ=>logDeriv (fun s=>1+cW n s) z:=by
    have hcongr:(fun n:ℕ=>logDeriv (fun s=>1+cW n s) z)
        =fun n:ℕ=> -(1/((n:ℂ)+1)-1/(z+n+1)) :=by
      funext n
      rw [nP hz n]
      ring
    rw [hcongr]
    exact (lU hz).neg
  have aam:logDeriv (fun s=> ∏' n:ℕ,(1+cW n s)) z
      = ∑' n:ℕ,logDeriv (fun s=>1+cW n s) z:=by
    refine logDeriv_tprod_eq_tsum hUopen hzU hfne ?_ Uz htend Yn
    intro n
    have hd:Differentiable ℂ fun s:ℂ=>1+cW n s:=by
      unfold cW
      fun_prop
    exact hd.differentiableOn
  have UA:Differentiable ℂ fun s:ℂ=>s*Complex.exp (γc*s) :=by
    fun_prop
  have Ee:DifferentiableAt ℂ (fun s=> ∏' n:ℕ,(1+cW n s)) z:=by
    have hev:(fun s:ℂ=>(Complex.Gamma s)⁻¹/(s*Complex.exp (γc*s)))
        =ᶠ[nhds z] (fun s=> ∏' n:ℕ,(1+cW n s)) :=by
      filter_upwards [Uw.mem_nhds hz] with s hs
      have h2:=mD hs
      rw [← Wd] at h2
      have hsne:s*Complex.exp (γc*s)≠0:=
        mul_ne_zero (Complex.integerComplement.ne_zero hs) (Complex.exp_ne_zero _)
      rw [h2]
      exact mul_div_cancel_left₀ _ hsne
    have hd:DifferentiableAt ℂ
        (fun s:ℂ=>(Complex.Gamma s)⁻¹/(s*Complex.exp (γc*s))) z:=by
      refine DifferentiableAt.div ?_ (UA z) hgne
      exact Complex.differentiable_one_div_Gamma z
    exact hd.congr_of_eventuallyEq hev.symm
  have Yo:logDeriv (fun s=>(Complex.Gamma s)⁻¹) z= -Complex.digamma z:=by
    have h1:logDeriv ((·⁻¹)∘Complex.Gamma) z
        =logDeriv (·⁻¹) (Complex.Gamma z)*deriv Complex.Gamma z:=by
      refine logDeriv_comp ?_ (Complex.differentiableAt_Gamma z hzero)
      exact differentiableAt_inv Fw
    rw [show (fun s=>(Complex.Gamma s)⁻¹)=(·⁻¹)∘Complex.Gamma from rfl,h1,logDeriv_inv]
    rw [Complex.digamma_def,logDeriv_apply]
    field_simp
  have Yp:(fun s=>(Complex.Gamma s)⁻¹)
      =ᶠ[nhds z] fun s=>(s*Complex.exp (γc*s))* ∏' n:ℕ,(1+cW n s) :=by
    filter_upwards [Uw.mem_nhds hz] with s hs
    have h2:=mD hs
    rw [← Wd] at h2
    rw [h2]
  have Yq:logDeriv (fun s=>(Complex.Gamma s)⁻¹) z
      =logDeriv (fun s=>(s*Complex.exp (γc*s))* ∏' n:ℕ,(1+cW n s)) z:=by
    unfold logDeriv
    rw [Pi.div_apply,Pi.div_apply,Yp.deriv_eq,Yp.eq_of_nhds]
  have hmul:logDeriv (fun s=>(s*Complex.exp (γc*s))* ∏' n:ℕ,(1+cW n s)) z
      =logDeriv (fun s:ℂ=>s*Complex.exp (γc*s)) z
        +logDeriv (fun s=> ∏' n:ℕ,(1+cW n s)) z:=
    logDeriv_mul z hgne Yn (UA z) Ee
  have abG:logDeriv (fun s:ℂ=>s*Complex.exp (γc*s)) z=1/z+γc:=by
    have hder:HasDerivAt (fun s:ℂ=>s*Complex.exp (γc*s))
        (1*Complex.exp (γc*z)+z*(γc*Complex.exp (γc*z))) z:=by
      have h1:HasDerivAt (fun s:ℂ=>Complex.exp (γc*s)) (γc*Complex.exp (γc*z)) z:=by
        have hlin:HasDerivAt (fun s:ℂ=>γc*s) γc z:=by
          simpa using (hasDerivAt_id z).const_mul γc
        have h5:=hlin.cexp
        simpa [mul_comm] using h5
      exact (hasDerivAt_id z).mul h1
    unfold logDeriv
    rw [Pi.div_apply,hder.deriv]
    have he:Complex.exp (γc*z)≠0:=Complex.exp_ne_zero _
    field_simp
  have hmain: -Complex.digamma z
      =(1/z+γc)+ ∑' n:ℕ,logDeriv (fun s=>1+cW n s) z:=by
    rw [← Yo,Yq,hmul,abG,aam]
  have aan: ∑' n:ℕ,(1/((n:ℂ)+1)-1/(z+n+1))
      =Complex.digamma z+γc+1/z:=by
    have h1: ∑' n:ℕ,logDeriv (fun s=>1+cW n s) z
        = ∑' n:ℕ, -(1/((n:ℂ)+1)-1/(z+n+1)) :=by
      congr 1
      funext n
      rw [nP hz n]
      ring
    rw [h1,tsum_neg] at hmain
    linear_combination hmain
  have h:=(lU hz).hasSum
  rwa [aan] at h
end nT
end Zeta23
end
end

-- Zeta23.Analytic.Stirling
section
noncomputable section
namespace Zeta23
namespace Stirling
open Complex Filter Topology
end Stirling
end Zeta23
end
end

-- Zeta23.lK.Mu
section
noncomputable section
namespace Zeta23
namespace Wf
open Complex Filter Topology
variable {a:ℝ}
end Wf
end Zeta23
end
end

-- Zeta23.lK.kZ
section
noncomputable section
namespace Zeta23
namespace kZ
open Complex Filter Topology MeasureTheory intervalIntegral Set
theorem qM (c:ℂ) (f:ℝ→ℂ) (a b:ℝ) :
    ∫ x in a..b,f x*c=(∫ x in a..b,f x)*c:=
  intervalIntegral.integral_mul_const c f
theorem Ep {w:ℂ} (x:ℝ) : |w.im| ≤ ‖(x:ℂ)+w‖ :=by
  have:=Complex.abs_im_le_norm ((x:ℂ)+w)
  simpa using this
theorem KO {w:ℂ} (hw:0<w.re) {x:ℝ} (hx:0≤x) :0<((x:ℂ)+w).re:=by
  simp; linarith
theorem Gh {w:ℂ} (hw:0<w.re) {x:ℝ} (hx:0≤x) :
    (x:ℂ)+w∈Complex.slitPlane:=
  Complex.mem_slitPlane_iff.mpr (Or.inl (KO hw hx))
theorem add_ne_zero {w:ℂ} (hw:0<w.re) {x:ℝ} (hx:0≤x) :(x:ℂ)+w≠0:=
  fun h=>by have:=KO hw hx; rw [h] at this; simp at this
theorem Er {w:ℂ} (hw:0<w.re) {x:ℝ} (hx:0≤x) :
    HasDerivAt (fun y:ℝ=>Complex.log ((y:ℂ)+w)) (((x:ℂ)+w)⁻¹) x:=by
  have h1:HasDerivAt (fun z:ℂ=>Complex.log (z+w)) (((x:ℂ)+w)⁻¹) (x:ℂ) :=by
    have:=(Complex.hasDerivAt_log (Gh hw hx)).comp (x:ℂ)
      ((hasDerivAt_id (x:ℂ)).add_const w)
    simpa [Function.comp_def] using this
  exact h1.comp_ofReal
theorem jO {w:ℂ} (hw:0<w.re) {m:ℝ} (hm:0≤ m) :
    ∫ x in m..(m+1),((x:ℂ)+w)⁻¹
      =Complex.log (((m+1:ℝ) :ℂ)+w)-Complex.log ((m:ℂ)+w) :=by
  have hcont:ContinuousOn (fun x:ℝ=>((x:ℂ)+w)⁻¹) (uIcc m (m+1)) :=by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact add_ne_zero hw (by linarith [hx.1])
  rw [integral_eq_sub_of_hasDerivAt (f:=fun y:ℝ=>Complex.log ((y:ℂ)+w))
    (fun x hx=>by
      rw [uIcc_of_le (by linarith)] at hx
      exact Er hw (by linarith [hx.1]))
    (hcont.intervalIntegrable)]
theorem MJ {w:ℂ} {x m:ℝ} (hxw:(x:ℂ)+w≠0) (hmw:(m:ℂ)+w≠0) :
    ((x:ℂ)+w)⁻¹
      =((m:ℂ)+w)⁻¹-((x-m:ℝ) :ℂ)/((m:ℂ)+w)^2
        +((x-m:ℝ) :ℂ)^2/(((m:ℂ)+w)^2*((x:ℂ)+w)) :=by
  field_simp
  push_cast
  ring
def eps (w:ℂ) (m:ℝ) :ℂ:=
  ∫ x in m..(m+1),((x-m:ℝ) :ℂ)^2/(((m:ℂ)+w)^2*((x:ℂ)+w))
theorem qB {w:ℂ} (hw:0<w.re) {m:ℝ} (hm:0≤ m) :
    ∫ x in m..(m+1),((x:ℂ)+w)⁻¹
      =((m:ℂ)+w)⁻¹-(1/2:ℂ)/((m:ℂ)+w)^2+eps w m:=by
  have hmw:=add_ne_zero hw hm
  have hcongr: ∫ x in m..(m+1),((x:ℂ)+w)⁻¹= ∫ x in m..(m+1),
      (((m:ℂ)+w)⁻¹-((x-m:ℝ) :ℂ)/((m:ℂ)+w)^2
        +((x-m:ℝ) :ℂ)^2/(((m:ℂ)+w)^2*((x:ℂ)+w))) :=by
    apply integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact MJ (add_ne_zero hw (by linarith [hx.1])) hmw
  rw [hcongr]
  have hI: ∀ {f:ℝ→ℂ},Continuous f→ IntervalIntegrable f volume m (m+1) :=
    fun hf=>hf.intervalIntegrable _ _
  have hR:IntervalIntegrable (fun x:ℝ=>
      ((x-m:ℝ) :ℂ)^2/(((m:ℂ)+w)^2*((x:ℂ)+w))) volume m (m+1) :=by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact mul_ne_zero (pow_ne_zero _ hmw) (add_ne_zero hw (by linarith [hx.1]))
  have hmid: ∫ x in m..(m+1),((x-m:ℝ) :ℂ)/((m:ℂ)+w)^2
      =((1/2:ℝ) :ℂ)*((((m:ℂ)+w)^2)⁻¹) :=by
    have e:(fun x:ℝ=>((x-m:ℝ) :ℂ)/((m:ℂ)+w)^2)
        =fun x:ℝ=>((x-m:ℝ) :ℂ)*((((m:ℂ)+w)^2)⁻¹) :=by
      funext x; rw [div_eq_mul_inv]
    rw [e,qM,intervalIntegral.integral_ofReal,
      intervalIntegral.integral_comp_sub_right (fun u:ℝ=>u) m]
    simp only [sub_self,add_sub_cancel_left,integral_id]
    norm_num
  rw [integral_add ((hI (by fun_prop)).sub (hI (by fun_prop))) hR,
    integral_sub (hI (by fun_prop)) (hI (by fun_prop)),intervalIntegral.integral_const,hmid,
    show m+1-m=(1:ℝ) by ring,one_smul]
  unfold eps
  push_cast
  ring
theorem GU {w:ℂ} (hw:0<w.re) (ht:1/2≤ |w.im|) {m:ℝ} (hm:0≤ m) :
    ‖eps w m‖ ≤1/(3* ‖(m:ℂ)+w‖ ^2* |w.im|) :=by
  have hmw:=add_ne_zero hw hm
  have hM:0< ‖(m:ℂ)+w‖ :=norm_pos_iff.mpr hmw
  have ht0:0< |w.im| :=by linarith
  unfold eps
  calc ‖∫ x in m..(m+1),((x-m:ℝ) :ℂ)^2/(((m:ℂ)+w)^2*((x:ℂ)+w))‖
      ≤ ∫ x in m..(m+1), ‖((x-m:ℝ) :ℂ)^2/(((m:ℂ)+w)^2*((x:ℂ)+w))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _≤ ∫ x in m..(m+1),(x-m)^2/(‖(m:ℂ)+w‖ ^2* |w.im|) :=by
        apply intervalIntegral.integral_mono_on (by linarith)
        · refine (ContinuousOn.intervalIntegrable ?_).norm
          apply ContinuousOn.div (by fun_prop) (by fun_prop)
          intro x hx
          rw [uIcc_of_le (by linarith)] at hx
          exact mul_ne_zero (pow_ne_zero _ hmw) (add_ne_zero hw (by linarith [hx.1]))
        · exact (by fun_prop:Continuous fun x:ℝ=>(x-m)^2/(‖(m:ℂ)+w‖ ^2* |w.im|))
            |>.intervalIntegrable _ _
        · intro x hx
          have hx0:0≤x:=by linarith [hx.1]
          have hxw: |w.im| ≤ ‖(x:ℂ)+w‖ :=Ep x
          rw [norm_div,norm_mul,norm_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,
            sq_abs]
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hxw (by positivity)
    _=1/(3* ‖(m:ℂ)+w‖ ^2* |w.im|) :=by
        rw [intervalIntegral.integral_div,intervalIntegral.integral_comp_sub_right (fun u:ℝ=>u^2) m]
        simp only [sub_self,add_sub_cancel_left,integral_pow]
        norm_num
        field_simp
section Seq
variable {w:ℂ}
theorem OV (hw:0<w.re) (n:ℕ) :0<((n:ℂ)+1+w).re:=by
  simp; positivity
theorem nU (hw:0<w.re) (n:ℕ) :(n:ℂ)+1+w≠0:=fun h=>by
  have:=OV hw n; rw [h] at this; simp at this
theorem Dp (hw:0<w.re) (n:ℕ) :(n:ℝ)+1≤ ‖(n:ℂ)+1+w‖ :=by
  have h:=Complex.re_le_norm ((n:ℂ)+1+w)
  simp at h; linarith
theorem OW (hw:0<w.re) (n:ℕ) :
    ((n:ℂ)+1+w)⁻¹
      =(Complex.log (((n+1:ℕ) :ℂ)+1+w)-Complex.log ((n:ℂ)+1+w))
        +(1/2:ℂ)/((n:ℂ)+1+w)^2 -eps w ((n:ℝ)+1) :=by
  have hm:(0:ℝ)≤(n:ℝ)+1:=by positivity
  have h1:=qB hw hm
  have h2:=jO hw hm
  rw [h2] at h1
  have e1:((((n:ℝ)+1:ℝ)) :ℂ)+w=(n:ℂ)+1+w:=by push_cast; ring
  have e2:((((n:ℝ)+1+1:ℝ)) :ℂ)+w=((n+1:ℕ) :ℂ)+1+w:=by push_cast; ring
  rw [e1,e2] at h1
  linear_combination (-1:ℂ)*h1
def rho (w:ℂ) (n:ℕ) :ℂ:=1/(((n:ℂ)+1+w)^2*((n:ℂ)+2+w))
theorem KQ (hw:0<w.re) (n:ℕ) :
    1/((n:ℂ)+1+w)^2
      =(((n:ℂ)+1+w)⁻¹-(((n+1:ℕ) :ℂ)+1+w)⁻¹)+rho w n:=by
  have h1:=nU hw n
  have h2:=nU hw (n+1)
  have e:((n+1:ℕ) :ℂ)+1+w=(n:ℂ)+2+w:=by push_cast; ring
  rw [e] at h2 ⊢
  unfold rho
  field_simp
  ring
theorem zV (hw:0<w.re) (ht:1/2≤ |w.im|) (n:ℕ) :
    ‖rho w n‖ ≤1/(‖(n:ℂ)+1+w‖ ^2* |w.im|) :=by
  have h1:=nU hw n
  have hn2: |w.im| ≤ ‖(n:ℂ)+2+w‖ :=by
    have:=Complex.abs_im_le_norm ((n:ℂ)+2+w); simpa using this
  have ht0:0< |w.im| :=by linarith
  unfold rho
  rw [norm_div,norm_one,norm_mul,norm_pow]
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  exact mul_le_mul_of_nonneg_left hn2 (by positivity)
theorem mJ (hw:0<w.re) (ht:1/2≤ |w.im|) (n:ℕ) :
    ‖eps w ((n:ℝ)+1)‖ ≤1/(3* ‖(n:ℂ)+1+w‖ ^2* |w.im|) :=by
  have:=GU hw ht (m:=(n:ℝ)+1) (by positivity)
  rw [show ((((n:ℝ)+1:ℝ)) :ℂ)+w=(n:ℂ)+1+w by push_cast; ring] at this
  exact this
theorem ML (hw:0<w.re) (N:ℕ) :
    ∑ n∈Finset.range N,(1/((n:ℂ)+1)-1/(w+n+1))
      =(∑ n∈Finset.range N,1/((n:ℂ)+1))
        -(Complex.log ((N:ℂ)+1+w)-Complex.log ((0:ℕ)+1+w:ℂ))
        -(1/2:ℂ)*(((0:ℕ)+1+w:ℂ)⁻¹-((N:ℂ)+1+w)⁻¹
            + ∑ n∈Finset.range N,rho w n)
        + ∑ n∈Finset.range N,eps w ((n:ℝ)+1) :=by
  rw [Finset.sum_sub_distrib]
  have hterm: ∀ n∈Finset.range N,(1:ℂ)/(w+n+1)
      =(Complex.log (((n+1:ℕ) :ℂ)+1+w)-Complex.log ((n:ℂ)+1+w))
        +(1/2:ℂ)*((((n:ℂ)+1+w)⁻¹-(((n+1:ℕ) :ℂ)+1+w)⁻¹)+rho w n)
        -eps w ((n:ℝ)+1) :=by
    intro n _
    have A:=OW hw n
    have B:=KQ hw n
    rw [show (1:ℂ)/(w+n+1)=((n:ℂ)+1+w)⁻¹ by rw [one_div]; ring_nf]
    linear_combination A+(1/2:ℂ)*B
  rw [Finset.sum_congr rfl hterm,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    Finset.sum_range_sub (fun n=>Complex.log ((n:ℂ)+1+w)) N, ← Finset.mul_sum,
    Finset.sum_add_distrib,Finset.sum_range_sub' (fun n=>((n:ℂ)+1+w)⁻¹) N]
  push_cast
  ring
theorem IU (hw:0<w.re) (n:ℕ) :
    ((n:ℝ)+1)^2+w.im^2≤ ‖(n:ℂ)+1+w‖ ^2:=by
  rw [Complex.sq_norm,Complex.normSq_apply]
  have hre:((n:ℂ)+1+w).re=(n:ℝ)+1+w.re:=by simp
  have him:((n:ℂ)+1+w).im=w.im:=by simp
  rw [hre,him]
  nlinarith
theorem wL (hw:0<w.re) (ht:1/2≤ |w.im|) (n:ℕ) :
    1/ ‖(n:ℂ)+1+w‖ ^2≤2*(1/((n:ℝ)+ |w.im|)-1/((n:ℝ)+1+ |w.im|)) :=by
  have h1:=IU hw n
  have ht0:0< |w.im| :=by linarith
  have hpos:0<((n:ℝ)+1)^2+w.im^2:=by positivity
  have aao:1/((n:ℝ)+ |w.im|)-1/((n:ℝ)+1+ |w.im|)
      =1/(((n:ℝ)+ |w.im|)*((n:ℝ)+1+ |w.im|)) :=by
    field_simp; ring
  rw [aao]
  have hsq:w.im^2= |w.im| ^2:=(sq_abs _).symm
  calc 1/ ‖(n:ℂ)+1+w‖ ^2≤1/(((n:ℝ)+1)^2+w.im^2) :=
        div_le_div_of_nonneg_left zero_le_one hpos h1
    _≤2*(1/(((n:ℝ)+ |w.im|)*((n:ℝ)+1+ |w.im|))) :=by
        rw [hsq, ← div_eq_mul_one_div,div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg ((n:ℝ)+1- |w.im|)]
theorem Et (hw:0<w.re) (ht:1/2≤ |w.im|) (N:ℕ) :
    ∑ n∈Finset.range N,1/ ‖(n:ℂ)+1+w‖ ^2≤2/ |w.im| :=by
  have ht0:0< |w.im| :=by linarith
  calc ∑ n∈Finset.range N,1/ ‖(n:ℂ)+1+w‖ ^2
      ≤ ∑ n∈Finset.range N,2*(1/((n:ℝ)+ |w.im|)-1/((n:ℝ)+1+ |w.im|)) :=
        Finset.sum_le_sum fun n _=>wL hw ht n
    _=2*(1/ |w.im| -1/((N:ℝ)+ |w.im|)) :=by
        rw [← Finset.mul_sum,Finset.sum_congr rfl (fun (i:ℕ) _=>by
          rw [show ((i:ℝ)+1+ |w.im|)=(((i+1:ℕ) :ℝ)+ |w.im|) by push_cast; ring]),
          Finset.sum_range_sub' (fun n:ℕ=>1/((n:ℝ)+ |w.im|)) N]
        push_cast
        ring
    _≤2/ |w.im| :=by
        have:0≤1/((N:ℝ)+ |w.im|) :=by positivity
        rw [div_eq_mul_one_div 2]
        linarith
theorem dW (hw:0<w.re) :
    Summable (fun n:ℕ=>1/ ‖(n:ℂ)+1+w‖ ^2) :=by
  have hs:Summable (fun n:ℕ=>1/((n:ℝ)+1)^2) :=by
    have:=(Real.summable_one_div_nat_pow.mpr one_lt_two)
    exact_mod_cast (summable_nat_add_iff 1).mpr this
  refine Summable.of_nonneg_of_le (fun n=>by positivity) (fun n=>?_) hs
  exact div_le_div_of_nonneg_left zero_le_one (by positivity)
    (pow_le_pow_left₀ (by positivity) (Dp hw n) 2)
theorem OX (hw:0<w.re) (ht:1/2≤ |w.im|) :Summable (rho w) :=by
  refine Summable.of_norm_bounded ((dW hw).mul_left (1/ |w.im|)) fun n=>?_
  refine le_trans (zV hw ht n) (le_of_eq ?_)
  field_simp
theorem OY (hw:0<w.re) (ht:1/2≤ |w.im|) :
    Summable (fun n:ℕ=>eps w ((n:ℝ)+1)) :=by
  refine Summable.of_norm_bounded ((dW hw).mul_left (1/(3* |w.im|)))
    fun n=>?_
  refine le_trans (mJ hw ht n) (le_of_eq ?_)
  field_simp
theorem tM (hw:0<w.re) (ht:1/2≤ |w.im|) :Summable (fun n=> ‖rho w n‖) :=by
  refine Summable.of_nonneg_of_le (fun n=>norm_nonneg _) (fun n=>?_)
    ((dW hw).mul_left (1/ |w.im|))
  refine le_trans (zV hw ht n) (le_of_eq ?_)
  field_simp
theorem tO (hw:0<w.re) (ht:1/2≤ |w.im|) :
    Summable (fun n:ℕ=> ‖eps w ((n:ℝ)+1)‖) :=by
  refine Summable.of_nonneg_of_le (fun n=>norm_nonneg _) (fun n=>?_)
    ((dW hw).mul_left (1/(3* |w.im|)))
  refine le_trans (mJ hw ht n) (le_of_eq ?_)
  field_simp
theorem qC (hw:0<w.re) (ht:1/2≤ |w.im|) :
    ∑' n:ℕ,1/ ‖(n:ℂ)+1+w‖ ^2≤2/ |w.im| :=
  Real.tsum_le_of_sum_range_le (fun n=>by positivity) (Et hw ht)
theorem IZ (hw:0<w.re) (ht:1/2≤ |w.im|) :
    ‖∑' n,rho w n‖ ≤2/w.im^2:=by
  have ht0:0< |w.im| :=by linarith
  have hS:=qC hw ht
  calc ‖∑' n,rho w n‖ ≤ ∑' n, ‖rho w n‖ :=norm_tsum_le_tsum_norm (tM hw ht)
    _≤ ∑' n:ℕ,(1/ |w.im|)*(1/ ‖(n:ℂ)+1+w‖ ^2) :=by
        refine Summable.tsum_le_tsum (fun n=>?_) (tM hw ht)
          ((dW hw).mul_left _)
        refine le_trans (zV hw ht n) (le_of_eq ?_)
        field_simp
    _=(1/ |w.im|)* ∑' n:ℕ,1/ ‖(n:ℂ)+1+w‖ ^2:=tsum_mul_left
    _≤(1/ |w.im|)*(2/ |w.im|) :=by gcongr
    _=2/w.im^2:=by rw [← sq_abs]; field_simp
theorem Ja (hw:0<w.re) (ht:1/2≤ |w.im|) :
    ‖∑' n:ℕ,eps w ((n:ℝ)+1)‖ ≤(2/3)/w.im^2:=by
  have ht0:0< |w.im| :=by linarith
  have hS:=qC hw ht
  calc ‖∑' n:ℕ,eps w ((n:ℝ)+1)‖ ≤ ∑' n:ℕ, ‖eps w ((n:ℝ)+1)‖ :=
        norm_tsum_le_tsum_norm (tO hw ht)
    _≤ ∑' n:ℕ,(1/(3* |w.im|))*(1/ ‖(n:ℂ)+1+w‖ ^2) :=by
        refine Summable.tsum_le_tsum (fun n=>?_) (tO hw ht)
          ((dW hw).mul_left _)
        refine le_trans (mJ hw ht n) (le_of_eq ?_)
        field_simp
    _=(1/(3* |w.im|))* ∑' n:ℕ,1/ ‖(n:ℂ)+1+w‖ ^2:=tsum_mul_left
    _≤(1/(3* |w.im|))*(2/ |w.im|) :=by gcongr
    _=(2/3)/w.im^2:=by rw [← sq_abs]; field_simp
theorem vF (hw:0<w.re) :
    Tendsto (fun N:ℕ=>(∑ n∈Finset.range N,1/((n:ℂ)+1))
      -Complex.log ((N:ℂ)+1+w)) atTop (𝓝 (Real.eulerMascheroniConstant:ℂ)) :=by
  have hdecomp: ∀ N:ℕ,(∑ n∈Finset.range N,1/((n:ℂ)+1))
      -Complex.log ((N:ℂ)+1+w)
      =(((harmonic N:ℚ) :ℝ)-Real.log ((N:ℝ)+1) :ℝ)
        -Complex.log (1+w/((N:ℂ)+1)) :=by
    intro N
    have hN:(0:ℝ)<(N:ℝ)+1:=by positivity
    have hN1:(N:ℂ)+1≠0:=Nat.cast_add_one_ne_zero N
    have hq':1+w/((N:ℂ)+1)=((N:ℂ)+1+w)/((N:ℂ)+1) :=by
      field_simp
    have hq:1+w/((N:ℂ)+1)≠0:=by
      rw [hq']; exact div_ne_zero (nU hw N) hN1
    have hlog:Complex.log ((N:ℂ)+1+w)
        =Real.log ((N:ℝ)+1)+Complex.log (1+w/((N:ℂ)+1)) :=by
      rw [← Complex.log_ofReal_mul hN hq,hq']
      congr 1
      push_cast
      field_simp
    rw [hlog,Zeta23.nT.oA]
    push_cast
    ring
  simp_rw [hdecomp]
  have h1:Tendsto (fun N:ℕ=>((((harmonic N:ℚ) :ℝ)-Real.log ((N:ℝ)+1) :ℝ) :ℂ))
      atTop (𝓝 (Real.eulerMascheroniConstant:ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log_add_one
  have h2:Tendsto (fun N:ℕ=>Complex.log (1+w/((N:ℂ)+1))) atTop (𝓝 0) :=by
    have hq:Tendsto (fun N:ℕ=>w/((N:ℂ)+1)) atTop (𝓝 0) :=by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have:(fun N:ℕ=> ‖w/((N:ℂ)+1)‖)=fun N:ℕ=> ‖w‖ *(1/((N:ℝ)+1)) :=by
        funext N
        rw [norm_div,show ((N:ℂ)+1)=(((N:ℝ)+1:ℝ) :ℂ) by push_cast; ring,
          Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
        ring
      rw [this]
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ‖w‖
    have hcont:ContinuousAt Complex.log 1:=continuousAt_clog (by simp)
    have:=hcont.tendsto.comp (by simpa using hq.const_add 1)
    simpa [Function.comp_def] using this
  simpa using h1.sub h2
theorem Gk (hw:0<w.re) :
    Tendsto (fun N:ℕ=>((N:ℂ)+1+w)⁻¹) atTop (𝓝 0) :=by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun N=>norm_nonneg _) (fun N=>?_)
  rw [norm_inv]
  have h:=Dp hw N
  have hpos:(0:ℝ)<(N:ℝ)+1:=by positivity
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos h
theorem RZ (hw:0<w.re) (ht:1/2≤ |w.im|) :
    Complex.digamma w=Complex.log (1+w)-1/w-(1/2:ℂ)*(1+w)⁻¹
      -(1/2:ℂ)*(∑' n,rho w n)+ ∑' n:ℕ,eps w ((n:ℝ)+1) :=by
  have hmem:w∈Complex.integerComplement:=by
    rintro ⟨k,hk⟩
    have:=congrArg Complex.im hk
    simp at this
    rw [← this] at ht; simp at ht; linarith
  have hL:=(Zeta23.nT.Bm hmem).tendsto_sum_nat
  have hR:Tendsto (fun N:ℕ=> ∑ n∈Finset.range N,(1/((n:ℂ)+1)-1/(w+n+1)))
      atTop (𝓝 ((Real.eulerMascheroniConstant:ℂ)+Complex.log (1+w)
        -(1/2:ℂ)*((1+w)⁻¹- 0+ ∑' n,rho w n)+ ∑' n:ℕ,eps w ((n:ℝ)+1))) :=by
    have e: ∀ N:ℕ, ∑ n∈Finset.range N,(1/((n:ℂ)+1)-1/(w+n+1))
        =((∑ n∈Finset.range N,1/((n:ℂ)+1))-Complex.log ((N:ℂ)+1+w))
          +Complex.log (1+w)
          -(1/2:ℂ)*((1+w)⁻¹-((N:ℂ)+1+w)⁻¹+ ∑ n∈Finset.range N,rho w n)
          + ∑ n∈Finset.range N,eps w ((n:ℝ)+1) :=by
      intro N
      rw [ML hw N]
      push_cast
      ring
    simp_rw [e]
    refine (((vF hw).add tendsto_const_nhds).sub
      (((tendsto_const_nhds.sub (Gk hw)).add
        (OX hw ht).hasSum.tendsto_sum_nat).const_mul _)).add
      (OY hw ht).hasSum.tendsto_sum_nat
  have:=tendsto_nhds_unique hL hR
  rw [sub_zero] at this
  linear_combination this
theorem DG (hw:0<w.re) :
    Complex.log (1+w)-Complex.log w=w⁻¹-(1/2:ℂ)/w^2+eps w 0:=by
  have h1:=qB hw (m:=0) le_rfl
  have h2:=jO hw (m:=0) le_rfl
  rw [h2] at h1
  simpa [add_comm] using h1
theorem Jb (hw:0<w.re) (ht:1/2≤ |w.im|) : ‖eps w 0‖ ≤(1/3)/ |w.im| ^3:=by
  have h:=GU hw ht (m:=0) le_rfl
  have ht0:0< |w.im| :=by linarith
  have hw': |w.im| ≤ ‖w‖ :=Complex.abs_im_le_norm w
  simp only [Complex.ofReal_zero,zero_add] at h
  calc ‖eps w 0‖ ≤1/(3* ‖w‖ ^2* |w.im|) :=h
    _≤1/(3* |w.im| ^2* |w.im|) :=by
        apply div_le_div_of_nonneg_left zero_le_one (by positivity)
        gcongr
    _=(1/3)/ |w.im| ^3:=by field_simp
theorem oB (hw:0<w.re) (ht:1/2≤ |w.im|) :
    ‖Complex.digamma w-Complex.log w+(1/2:ℂ)/w‖ ≤3/w.im^2:=by
  have hw0:w≠0:=fun h=>by rw [h] at hw; simp at hw
  have h1w:1+w≠0:=fun h=>by
    have:=congrArg Complex.re h; simp at this; linarith
  have ht0:0< |w.im| :=by linarith
  have hwn: |w.im| ≤ ‖w‖ :=Complex.abs_im_le_norm w
  have adS: |w.im| ≤ ‖1+w‖ :=by have:=Complex.abs_im_le_norm (1+w); simpa using this
  have hid:=RZ hw ht
  have hlog:=DG hw
  have key:Complex.digamma w-Complex.log w+(1/2:ℂ)/w
      = -(1/2:ℂ)/(w^2*(1+w))+eps w 0
        -(1/2:ℂ)*(∑' n,rho w n)+ ∑' n:ℕ,eps w ((n:ℝ)+1) :=by
    rw [hid,show Complex.log (1+w)=Complex.log w+(w⁻¹-(1/2:ℂ)/w^2+eps w 0) by
      rw [← hlog]; ring]
    field_simp
    ring
  rw [key]
  have hsq: |w.im| ^2=w.im^2:=sq_abs _
  have b1: ‖-(1/2:ℂ)/(w^2*(1+w))‖ ≤(1/2)/w.im^2:=by
    rw [norm_div,norm_neg,norm_mul,norm_pow]
    have: ‖(1/2:ℂ)‖ =1/2:=by norm_num
    rw [this, ← hsq]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have h1:1≤ ‖1+w‖ :=le_trans (by simp; linarith) (Complex.re_le_norm (1+w))
    calc |w.im| ^2= |w.im| ^2*1:=(mul_one _).symm
      _≤ ‖w‖ ^2* ‖1+w‖ :=by gcongr
  have b2: ‖eps w 0‖ ≤(2/3)/w.im^2:=by
    refine le_trans (Jb hw ht) ?_
    rw [← hsq,div_le_div_iff₀ (by positivity) (by positivity)]
    have h3: |w.im| ^3= |w.im| ^2* |w.im| :=by ring
    rw [h3]
    have:0< |w.im| ^2:=by positivity
    nlinarith
  have b3: ‖(1/2:ℂ)* ∑' n,rho w n‖ ≤1/w.im^2:=by
    rw [norm_mul,show ‖(1/2:ℂ)‖ =1/2 by norm_num]
    have h:=mul_le_mul_of_nonneg_left (IZ hw ht) (by norm_num:(0:ℝ)≤1/2)
    calc 1/2* ‖∑' n,rho w n‖ ≤1/2*(2/w.im^2) :=h
      _=1/w.im^2:=by ring
  have b4:=Ja hw ht
  calc ‖-(1/2:ℂ)/(w^2*(1+w))+eps w 0-(1/2:ℂ)* ∑' n,rho w n
        + ∑' n:ℕ,eps w ((n:ℝ)+1)‖
      ≤ ‖-(1/2:ℂ)/(w^2*(1+w))‖ + ‖eps w 0‖ + ‖(1/2:ℂ)* ∑' n,rho w n‖
        + ‖∑' n:ℕ,eps w ((n:ℝ)+1)‖ :=by
        have s1:=norm_add_le (-(1/2:ℂ)/(w^2*(1+w))+eps w 0-(1/2:ℂ)* ∑' n,rho w n)
          (∑' n:ℕ,eps w ((n:ℝ)+1))
        have s2:=norm_sub_le (-(1/2:ℂ)/(w^2*(1+w))+eps w 0) ((1/2:ℂ)* ∑' n,rho w n)
        have s3:=norm_add_le (-(1/2:ℂ)/(w^2*(1+w))) (eps w 0)
        linarith
    _≤(1/2)/w.im^2+(2/3)/w.im^2+1/w.im^2+(2/3)/w.im^2:=by
        gcongr
    _≤3/w.im^2:=by
        have hpos:0<w.im^2:=by rw [← hsq]; positivity
        rw [show (1/2)/w.im^2+(2/3)/w.im^2+1/w.im^2+(2/3)/w.im^2
          =(17/6)/w.im^2 by ring]
        apply div_le_div_of_nonneg_right _ hpos.le
        norm_num
end Seq
section Yr
end Yr
end kZ
end Zeta23
end
end

-- Zeta23.bR.Landau
section
noncomputable section
namespace Zeta23
namespace bR
open Complex Set
section Wg
open Metric
lemma KR {f:ℂ→ℂ} (hfa:AnalyticOnNhd ℂ f (Metric.closedBall (0:ℂ) 1))
    (hf0:f 0≠0) {r:ℝ} (hr1:r<1) (hfin:(bD 1 f).Finite)
    {z:ℂ} (hz: ‖z‖ ≤r) :Cf r f z≠0:=by
  have nV:=aR hr1 hfin
  by_cases hmem:z∈bD r f
  · 
    obtain ⟨Iz,_,Eb,hZF,_⟩:=tK hr1 hfa hf0 hmem
    unfold Cf
    rw [dif_pos nV,dif_pos hmem,hZF]
    apply div_ne_zero Eb
    refine Finset.prod_ne_zero_iff.mpr fun ρ hρ=>?_
    have hne:z≠ρ:=by
      intro h
      rw [Finset.mem_sdiff,Finset.mem_singleton] at hρ
      exact hρ.2 h.symm
    exact pow_ne_zero _ (sub_ne_zero.mpr hne)
  · unfold Cf
    rw [dif_pos nV,dif_neg hmem]
    have hfz:f z≠0:=by
      intro h
      exact hmem ⟨hz,h⟩
    apply div_ne_zero hfz
    refine Finset.prod_ne_zero_iff.mpr fun ρ hρ=>?_
    have hρ':=nV.mem_toFinset.mp hρ
    have hne:z≠ρ:=by
      rintro rfl
      exact hmem hρ'
    exact pow_ne_zero _ (sub_ne_zero.mpr hne)
lemma Je {f:ℂ→ℂ} {r:ℝ} (hr1:r<1) (hfin:(bD 1 f).Finite)
    {z:ℂ} (hz:z∉bD r f) :
    f z=(∏ ρ∈(aR hr1 hfin).toFinset,(z-ρ)^analyticOrderNatAt f ρ)
      *Cf r f z:=by
  have nV:=aR hr1 hfin
  unfold Cf
  rw [dif_pos nV,dif_neg hz]
  rw [mul_div_cancel₀]
  refine Finset.prod_ne_zero_iff.mpr fun ρ hρ=>?_
  have hρ':=nV.mem_toFinset.mp hρ
  have hne:z≠ρ:=by
    rintro rfl
    exact hz hρ'
  exact pow_ne_zero _ (sub_ne_zero.mpr hne)
lemma Ew {s:Finset ℂ} {m:ℂ→ℕ} {z:ℂ} (hz: ∀ ρ∈s,z≠ρ) :
    logDeriv (fun w=> ∏ ρ∈s,(w-ρ)^m ρ) z= ∑ ρ∈s,(m ρ:ℂ)/(z-ρ) :=by
  rw [logDeriv_prod (f:=fun ρ w=>(w-ρ)^m ρ)
    (fun ρ hρ=>pow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ))) (fun ρ _=>by fun_prop)]
  refine Finset.sum_congr rfl fun ρ _=>?_
  have hd:HasDerivAt (fun w:ℂ=>w-ρ) 1 z:=(hasDerivAt_id z).sub_const ρ
  rw [logDeriv_fun_pow hd.differentiableAt,logDeriv_apply,hd.deriv]
  ring
lemma MO {f:ℂ→ℂ} (hfa:AnalyticOnNhd ℂ f (Metric.closedBall (0:ℂ) 1))
    (hf0:f 0≠0) {r:ℝ} (hr1:r<1) (hfin:(bD 1 f).Finite)
    {z:ℂ} (hz: ‖z‖ <r) (hfz:f z≠0) :
    logDeriv f z=(∑ ρ∈(aR hr1 hfin).toFinset,
        (analyticOrderNatAt f ρ:ℂ)/(z-ρ))+logDeriv (Cf r f) z:=by
  have nV:=aR hr1 hfin
  set P0:ℂ→ℂ:=fun w=> ∏ ρ∈nV.toFinset,(w-ρ)^analyticOrderNatAt f ρ with hP0
  have hU:IsOpen (Metric.ball (0:ℂ) r \ bD r f) :=
    Metric.isOpen_ball.sdiff nV.isClosed
  have hzU:z∈Metric.ball (0:ℂ) r \ bD r f:=
    ⟨mem_ball_zero_iff.mpr hz,fun h=>hfz h.2⟩
  have heq:f =ᶠ[nhds z] fun w=>P0 w*Cf r f w:=by
    filter_upwards [hU.mem_nhds hzU] with w hw
    exact Je hr1 hfin hw.2
  have hzne: ∀ ρ∈nV.toFinset,z≠ρ:=by
    intro ρ hρ
    rintro rfl
    exact hfz (nV.mem_toFinset.mp hρ).2
  have abH:P0 z≠0:=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ=>pow_ne_zero _ (sub_ne_zero.mpr (hzne ρ hρ))
  have abI:Cf r f z≠0:=KR hfa hf0 hr1 hfin hz.le
  have abJ:DifferentiableAt ℂ P0 z:=
    DifferentiableAt.fun_finsetProd fun ρ _=>
      ((differentiable_id.sub_const ρ).differentiableAt).pow _
  have abK:DifferentiableAt ℂ (Cf r f) z:=by
    have hR:r<(r+1)/2:=by linarith
    have hR1:(r+1)/2<1:=by linarith
    exact ((vE hR hR1 hfa hf0) z (by
      rw [Metric.mem_closedBall,Complex.dist_eq,sub_zero]
      calc ‖z‖ ≤r:=hz.le
        _≤(r+1)/2:=by linarith)).differentiableAt
  calc logDeriv f z=logDeriv (fun w=>P0 w*Cf r f w) z:=by
        unfold logDeriv
        simp only [Pi.div_apply]
        rw [heq.deriv_eq,heq.eq_of_nhds]
    _=logDeriv P0 z+logDeriv (Cf r f) z:=logDeriv_mul z abH abI abJ abK
    _=_:=by rw [hP0,Ew hzne]
lemma DH {f:ℂ→ℂ} {B:ℝ}
    (hfa:AnalyticOnNhd ℂ f (Metric.closedBall (0:ℂ) 1)) (hf0:f 0=1)
    (hfin:(bD 1 f).Finite) (Rh:2≤B)
    (hfB: ∀ w:ℂ, ‖w‖ ≤24/25→ ‖f w‖ ≤B)
    {z:ℂ} (hz: ‖z‖ ≤83/100) :
    ‖logDeriv (Cf (22/25) f) z‖ ≤44795000*Real.log B:=by
  have hf0':f 0≠0:=by rw [hf0]; exact one_ne_zero
  have nV:(bD (22/25) f).Finite:=aR (by norm_num) hfin
  have Fv:0<Real.log B:=Real.log_pos (by linarith)
  have hcount:((∑ ρ∈(aR (by norm_num:(22/25:ℝ)<1) hfin).toFinset,
      analyticOrderNatAt f ρ:ℕ) :ℝ)≤1/Real.log ((24/25)/(22/25))*Real.log B:=by
    exact_mod_cast Cc (by norm_num) (by norm_num)
      (by norm_num:(22/25:ℝ)<24/25) (by norm_num) hfa hf0 hfin (fun w hw=>hfB w hw)
  set K:ℕ:= ∑ ρ∈(aR (by norm_num:(22/25:ℝ)<1) hfin).toFinset,
    analyticOrderNatAt f ρ with hK
  have hsphere: ∀ w:ℂ, ‖w‖ =24/25→ ‖Cf (22/25) f w‖ ≤B*(25/2:ℝ)^K:=by
    intro w hw
    have aap:w∉bD (22/25) f:=by
      intro h
      have:=h.1
      rw [hw] at this
      norm_num at this
    have kD:=aR (by norm_num:(22/25:ℝ)<1) hfin
    have hdist: ∀ ρ∈kD.toFinset,(2/25:ℝ)≤ ‖w-ρ‖ :=by
      intro ρ hρ
      have hρ':=kD.mem_toFinset.mp hρ
      calc (2/25:ℝ)=24/25-22/25:=by norm_num
        _≤ ‖w‖ - ‖ρ‖ :=by
            have:=hρ'.1
            rw [hw]
            linarith
        _≤ ‖w-ρ‖ :=norm_sub_norm_le w ρ
    have OZ:((2/25:ℝ))^K≤ ‖∏ ρ∈kD.toFinset,(w-ρ)^analyticOrderNatAt f ρ‖ :=by
      rw [norm_prod,hK, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun ρ _=>by positivity) (fun ρ hρ=>?_)
      rw [norm_pow]
      exact pow_le_pow_left₀ (by norm_num) (hdist ρ hρ) _
    unfold Cf
    rw [dif_pos kD,dif_neg aap]
    rw [norm_div]
    have UC:(0:ℝ)< ‖∏ ρ∈kD.toFinset,(w-ρ)^analyticOrderNatAt f ρ‖ :=
      lt_of_lt_of_le (by positivity) OZ
    rw [div_le_iff₀ UC]
    calc ‖f w‖ ≤B:=hfB w (le_of_eq hw)
      _=B*(25/2:ℝ)^K*(2/25:ℝ)^K:=by
          rw [mul_assoc, ← mul_pow]
          norm_num
      _≤B*(25/2:ℝ)^K* ‖∏ ρ∈kD.toFinset,(w-ρ)^analyticOrderNatAt f ρ‖ :=by
          have hB0:(0:ℝ)≤B*(25/2:ℝ)^K:=by positivity
          exact mul_le_mul_of_nonneg_left OZ hB0
  have hball: ∀ w:ℂ, ‖w‖ ≤24/25→ ‖Cf (22/25) f w‖ ≤B*(25/2:ℝ)^K:=by
    intro w hw
    have abL:AnalyticOn ℂ (Cf (22/25) f) (Metric.closedBall 0 (24/25)) :=
      ((vE (by norm_num:(22/25:ℝ)<39/40) (by norm_num) hfa hf0').mono
        (Metric.closedBall_subset_closedBall (by norm_num))).analyticOn
    refine AnalyticOn.jF le_rfl abL (fun v hv=>?_)
      (by rwa [Metric.mem_closedBall,Complex.dist_eq,sub_zero])
    refine hsphere v ?_
    rw [mem_sphere_iff_norm,sub_zero] at hv
    exact hv
  have abM:(1:ℝ)≤ ‖Cf (22/25) f 0‖ :=by
    have aaq:(0:ℂ)∉bD (22/25) f:=fun h=>hf0' h.2
    have kD:=aR (by norm_num:(22/25:ℝ)<1) hfin
    unfold Cf
    rw [dif_pos kD,dif_neg aaq,norm_div,hf0,norm_one]
    rw [le_div_iff₀]
    · rw [one_mul,norm_prod]
      refine Finset.prod_le_one (fun ρ _=>by positivity) (fun ρ hρ=>?_)
      have hρ':=kD.mem_toFinset.mp hρ
      rw [norm_pow]
      refine pow_le_one₀ (norm_nonneg _) ?_
      rw [zero_sub,norm_neg]
      linarith [hρ'.1]
    · rw [norm_prod]
      refine Finset.prod_pos (fun ρ hρ=>?_)
      have hρ':=kD.mem_toFinset.mp hρ
      have Eb:ρ≠0:=by
        rintro rfl
        exact hf0' hρ'.2
      rw [norm_pow,zero_sub,norm_neg]
      exact pow_pos (norm_pos_iff.mpr Eb) _
  obtain ⟨J,hJa,hJ0,hJd,Ez⟩:=jG
    (by norm_num:(0:ℝ)<17/20) (by norm_num:(17/20:ℝ)<22/25)
    ((vE (by norm_num:(22/25:ℝ)<9/10) (by norm_num) hfa hf0').mono
      (Metric.closedBall_subset_closedBall (by norm_num)))
    (fun v hv=>KR hfa hf0' (by norm_num) hfin
      (by rwa [Metric.mem_closedBall,Complex.dist_eq,sub_zero] at hv))
  set M':ℝ:=(1+Real.log (25/2)/Real.log ((24/25)/(22/25)))*Real.log B with hM'
  have Yt:(0:ℝ)<Real.log ((24/25)/(22/25)) :=Real.log_pos (by norm_num)
  have Yv:0<M':=by
    rw [hM']
    have:(0:ℝ)<1+Real.log (25/2)/Real.log ((24/25)/(22/25)) :=by positivity
    positivity
  have hre: ∀ v∈Metric.closedBall (0:ℂ) (17/20),(J v).re≤M':=by
    intro v hv
    rw [← (Ez v (Metric.closedBall_subset_ball (by norm_num) hv))]
    have hv': ‖v‖ ≤24/25:=by
      rw [Metric.mem_closedBall,Complex.dist_eq,sub_zero] at hv
      linarith
    have h1:Real.log ‖Cf (22/25) f v‖ ≤Real.log (B*(25/2:ℝ)^K) :=by
      rcases eq_or_ne (Cf (22/25) f v) 0 with h | h
      · rw [h,norm_zero,Real.log_zero]
        refine Real.log_nonneg ?_
        calc (1:ℝ)=1*1:=by ring
          _≤B*(25/2:ℝ)^K:=by
              refine mul_le_mul (by linarith) (one_le_pow₀ (by norm_num)) (by norm_num)
                (by linarith)
      · exact Real.log_le_log (norm_pos_iff.mpr h) (hball v hv')
    have h2:(0:ℝ)≤Real.log ‖Cf (22/25) f 0‖ :=Real.log_nonneg abM
    have h3:Real.log (B*(25/2:ℝ)^K)=Real.log B+K*Real.log (25/2) :=by
      rw [Real.log_mul (by linarith) (by positivity),Real.log_pow]
    have h4:(K:ℝ)*Real.log (25/2)≤(Real.log B/Real.log ((24/25)/(22/25)))*Real.log (25/2) :=by
      have aar:(0:ℝ)≤Real.log (25/2) :=Real.log_nonneg (by norm_num)
      have abN:(K:ℝ)≤Real.log B/Real.log ((24/25)/(22/25)) :=by
        rw [div_eq_inv_mul, ← one_div]
        exact hcount
      exact mul_le_mul_of_nonneg_right abN aar
    have h5:Real.log ‖Cf (22/25) f v‖ -Real.log ‖Cf (22/25) f 0‖
        ≤Real.log B+(K:ℝ)*Real.log (25/2) :=by
      rw [← h3]
      linarith
    rw [hM']
    calc Real.log ‖Cf (22/25) f v‖ -Real.log ‖Cf (22/25) f 0‖
        ≤Real.log B+(K:ℝ)*Real.log (25/2) :=h5
      _≤Real.log B+(Real.log B/Real.log ((24/25)/(22/25)))*Real.log (25/2) :=by linarith
      _=(1+Real.log (25/2)/Real.log ((24/25)/(22/25)))*Real.log B:=by
          field_simp
  have hbc:=zR Yv (by norm_num:(0:ℝ)<83/100)
    (by norm_num:(83/100:ℝ)<17/20)
    ((hJa.mono (Metric.ball_subset_ball (by norm_num))).analyticOn) hJ0
    (fun v hv=>hre v (Metric.ball_subset_closedBall hv))
    (by rwa [Metric.mem_closedBall,Complex.dist_eq,sub_zero])
  have hzmem:z∈Metric.closedBall (0:ℂ) (17/20) :=by
    rw [Metric.mem_closedBall,Complex.dist_eq,sub_zero]
    linarith
  have Xo:deriv J z=logDeriv (Cf (22/25) f) z:=by
    rw [hJd z (by
      rw [Metric.mem_closedBall,Complex.dist_eq,sub_zero]
      linarith),logDeriv]
    rfl
  rw [← Xo]
  refine hbc.trans ?_
  have aas:M'≤31*Real.log B:=by
    rw [hM']
    have h8:Real.log (25/2)≤30*Real.log ((24/25)/(22/25)) :=by
      have abO:(25/2:ℝ)≤((24/25)/(22/25))^(30:ℕ) :=by norm_num
      calc Real.log (25/2)≤Real.log (((24/25)/(22/25))^(30:ℕ)) :=
            Real.log_le_log (by norm_num) abO
        _=30*Real.log ((24/25)/(22/25)) :=by rw [Real.log_pow]; push_cast; ring
    have hcoef:1+Real.log (25/2)/Real.log ((24/25)/(22/25))≤31:=by
      have hd:Real.log (25/2)/Real.log ((24/25)/(22/25))≤30:=
        (div_le_iff₀ Yt).mpr (by linarith)
      linarith
    exact mul_le_mul_of_nonneg_right hcoef Fv.le
  calc 16*M'*(17/20:ℝ)^2/((17/20:ℝ)-83/100)^3=1445000*M':=by
        field_simp
        ring
    _≤1445000*(31*Real.log B) :=by
        exact mul_le_mul_of_nonneg_left aas (by norm_num)
    _=44795000*Real.log B:=by ring
theorem oX {f:ℂ→ℂ} {B:ℝ}
    (hfa:AnalyticOnNhd ℂ f (Metric.closedBall (0:ℂ) 1)) (hf0:f 0=1)
    (hfin:(bD 1 f).Finite) (Rh:2≤B)
    (hfB: ∀ w:ℂ, ‖w‖ ≤24/25→ ‖f w‖ ≤B)
    {z:ℂ} (hz: ‖z‖ ≤83/100) (hfz:f z≠0) :
    ‖logDeriv f z- ∑ ρ∈(aR (by norm_num:(22/25:ℝ)<1) hfin).toFinset,
        (analyticOrderNatAt f ρ:ℂ)/(z-ρ)‖ ≤44795000*Real.log B:=by
  have hf0':f 0≠0:=by rw [hf0]; exact one_ne_zero
  have hsplit:=MO hfa hf0' (by norm_num:(22/25:ℝ)<1) hfin
    (lt_of_le_of_lt hz (by norm_num)) hfz
  rw [hsplit]
  rw [add_sub_cancel_left]
  exact DH hfa hf0 hfin Rh hfB hz
lemma Gm {f:ℂ→ℂ}
    (hfa:AnalyticOnNhd ℂ f (Metric.closedBall (0:ℂ) 1)) (hf0:f 0≠0) :
    (bD 1 f).Finite:=by
  set U:=Metric.closedBall (0:ℂ) 1 with hU
  have h0U:(0:ℂ)∈U:=by
    rw [hU,Metric.mem_closedBall,dist_self]
    norm_num
  have Iq:{z:ℂ | f z≠0}∈Filter.codiscreteWithin U:=by
    rcases hfa.eqOn_zero_or_eventually_ne_zero_of_preconnected
        (by rw [hU]; exact Metric.isPreconnected_closedBall) with h | h
    · exact absurd (h h0U) hf0
    · exact h
  rw [codiscreteWithin_iff_locallyFiniteComplementWithin] at Iq
  have hsub1:Metric.closedBall (0:ℂ) 1⊆U:=subset_rfl
  choose t ht aat using fun z (hz:z∈Metric.closedBall (0:ℂ) 1)=>Iq z (hsub1 hz)
  obtain ⟨s,hs⟩:=(isCompact_closedBall (0:ℂ) 1).elim_nhds_subcover'
    (fun z hz=>t z hz) (fun z hz=>ht z hz)
  refine Set.Finite.subset (Set.Finite.biUnion s.finite_toSet
    (fun z _=>aat z.1 z.2)) ?_
  intro ρ hρ
  have hρball:ρ∈Metric.closedBall (0:ℂ) 1:=by
    rw [Metric.mem_closedBall,Complex.dist_eq,sub_zero]
    exact hρ.1
  obtain ⟨z,hz,Iv⟩:=Set.mem_iUnion₂.mp (hs hρball)
  refine Set.mem_biUnion hz ?_
  refine ⟨Iv,hsub1 hρball,?_⟩
  simp only [Set.mem_setOf_eq,not_not]
  exact hρ.2
theorem oY {f:ℂ→ℂ} {s₀:ℂ} {R B:ℝ}
    (hR:0<R) (hfa:AnalyticOnNhd ℂ f (Metric.closedBall s₀ R)) (hf0:f s₀≠0)
    (Rh:2≤B) (hfB: ∀ w∈Metric.closedBall s₀ (24/25*R), ‖f w‖ ≤B* ‖f s₀‖) :
    ∃ Z:Finset ℂ,
      (↑Z={ρ∈Metric.closedBall s₀ (22/25*R) | f ρ=0}) ∧
      ((∑ ρ∈Z,(analyticOrderNatAt f ρ:ℝ))≤1/Real.log ((24/25)/(22/25))*Real.log B) ∧
      ∀ s∈Metric.closedBall s₀ (83/100*R),f s≠0→
        ‖logDeriv f s- ∑ ρ∈Z,(analyticOrderNatAt f ρ:ℂ)/(s-ρ)‖
          ≤44795000/R*Real.log B:=by
  have hRC:(R:ℂ)≠0:=by
    exact_mod_cast ne_of_gt hR
  set φ:ℂ→ℂ:=fun w=>s₀+(R:ℂ)*w with hφ
  have KS: ∀ {w:ℂ} {r:ℝ}, ‖w‖ ≤r→φ w∈Metric.closedBall s₀ (r*R) :=by
    intro w r hw
    rw [Metric.mem_closedBall,Complex.dist_eq,hφ]
    simp only [add_sub_cancel_left]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
    calc R* ‖w‖ ≤R*r:=mul_le_mul_of_nonneg_left hw hR.le
      _=r*R:=mul_comm _ _
  set c:ℂ:=(f s₀)⁻¹ with hc
  have hcne:c≠0:=inv_ne_zero hf0
  set g:ℂ→ℂ:=fun w=>c*f (φ w) with hg
  have hφa: ∀ w:ℂ,AnalyticAt ℂ φ w:=fun w=>by
    rw [hφ]
    exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have Yw: ∀ w:ℂ,deriv φ w=(R:ℂ) :=by
    intro w
    rw [hφ]
    simp
  have KI:Function.Injective φ:=by
    intro a b hab
    rw [hφ] at hab
    simp only [add_right_inj] at hab
    exact mul_left_cancel₀ hRC hab
  have hga:AnalyticOnNhd ℂ g (Metric.closedBall (0:ℂ) 1) :=by
    intro w hw
    have hwn: ‖w‖ ≤1:=by rwa [Metric.mem_closedBall,Complex.dist_eq,sub_zero] at hw
    have hmem:φ w∈Metric.closedBall s₀ R:=by
      have:=KS (r:=1) hwn
      simpa using this
    exact analyticAt_const.mul ((hfa (φ w) hmem).comp (hφa w))
  have hg0:g 0=1:=by
    rw [hg,hc]
    simp only [hφ,mul_zero,add_zero]
    exact inv_mul_cancel₀ hf0
  have abP:g 0≠0:=by rw [hg0]; exact one_ne_zero
  have hfin:(bD 1 g).Finite:=Gm hga abP
  have hgB: ∀ w:ℂ, ‖w‖ ≤24/25→ ‖g w‖ ≤B:=by
    intro w hw
    rw [hg]
    simp only
    rw [norm_mul,hc,norm_inv]
    rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hf0)]
    calc ‖f (φ w)‖ ≤B* ‖f s₀‖ :=hfB (φ w) (KS hw)
      _= ‖f s₀‖ *B:=mul_comm _ _
  have Pd: ∀ ρg:ℂ,g ρg=0↔f (φ ρg)=0:=by
    intro ρg
    rw [hg]
    simp only
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hcne
      · exact h
    · intro h
      rw [h,mul_zero]
  set Zg:=(aR (by norm_num:(22/25:ℝ)<1) hfin).toFinset with hZg
  have KV: ∀ ρg:ℂ,ρg∈Zg↔(‖ρg‖ ≤22/25 ∧ f (φ ρg)=0) :=by
    intro ρg
    rw [hZg,Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨h1,(Pd ρg).mp h2⟩
    · rintro ⟨h1,h2⟩
      exact ⟨h1,(Pd ρg).mpr h2⟩
  have hord: ∀ ρg:ℂ, ‖ρg‖ ≤1→analyticOrderNatAt g ρg=analyticOrderNatAt f (φ ρg) :=by
    intro ρg Jg
    have hcomp:analyticOrderAt (f∘φ) ρg=analyticOrderAt f (φ ρg) :=
      analyticOrderAt_comp_of_deriv_ne_zero (hφa ρg) (by rw [Yw]; exact hRC)
    have hsmul:analyticOrderAt g ρg=analyticOrderAt (f∘φ) ρg:=by
      have heq:g=(fun _:ℂ=>c)•(f∘φ) :=by
        funext w
        simp [hg,smul_eq_mul]
      rw [heq,analyticOrderAt_smul analyticAt_const
        (((hfa (φ ρg) (by simpa using KS (r:=1) Jg)).comp (hφa ρg)))]
      rw [(analyticAt_const (v:=c)).analyticOrderAt_eq_zero.mpr hcne,zero_add]
    rw [analyticOrderNatAt,analyticOrderNatAt,hsmul,hcomp]
  refine ⟨Zg.image φ,?_,?_,?_⟩
  · ext ρ
    simp only [Finset.coe_image,Set.mem_image,Finset.mem_coe,Set.mem_setOf_eq]
    constructor
    · rintro ⟨ρg,Jg,rfl⟩
      obtain ⟨h1,h2⟩:=(KV ρg).mp Jg
      exact ⟨by simpa using KS h1,h2⟩
    · rintro ⟨h1,h2⟩
      refine ⟨(ρ-s₀)/(R:ℂ),?_,?_⟩
      · rw [KV]
        constructor
        · rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR,
            div_le_iff₀ hR]
          rw [Metric.mem_closedBall,Complex.dist_eq] at h1
          linarith [h1]
        · rw [show φ ((ρ-s₀)/(R:ℂ))=ρ by rw [hφ]; field_simp; ring]
          exact h2
      · rw [hφ]; field_simp; ring
  · have hcount:=Cc (by norm_num) (by norm_num)
      (by norm_num:(22/25:ℝ)<24/25) (by norm_num) hga hg0 hfin hgB
    rw [Finset.sum_image (fun a _ b _ hab=>KI hab)]
    have hcongr: ∀ ρg∈Zg,(analyticOrderNatAt f (φ ρg) :ℝ)=(analyticOrderNatAt g ρg:ℝ) :=by
      intro ρg Jg
      rw [hord ρg (le_trans ((KV ρg).mp Jg).1 (by norm_num))]
    rw [Finset.sum_congr rfl hcongr]
    exact_mod_cast hcount
  · intro s hs hfs
    set w:ℂ:=(s-s₀)/(R:ℂ) with hw
    have hφw:φ w=s:=by rw [hφ,hw]; field_simp; ring
    have hwn: ‖w‖ ≤83/100:=by
      rw [hw,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR,div_le_iff₀ hR]
      rw [Metric.mem_closedBall,Complex.dist_eq] at hs
      linarith [hs]
    have hgw:g w≠0:=by
      rw [hg]
      simp only
      rw [hφw]
      exact mul_ne_zero hcne hfs
    have hunit:=oX hga hg0 hfin Rh hgB hwn hgw
    have Kt:s∈Metric.closedBall s₀ R:=
      Metric.closedBall_subset_closedBall (by nlinarith) hs
    have hld:logDeriv g w=(R:ℂ)*logDeriv f s:=by
      have hstep:logDeriv g w=logDeriv (f∘φ) w:=by
        rw [hg]
        exact logDeriv_const_mul w c hcne
      have hdf:DifferentiableAt ℂ f (φ w) :=by
        rw [hφw]
        exact (hfa s Kt).differentiableAt
      rw [hstep,logDeriv_comp hdf (hφa w).differentiableAt,hφw,Yw,mul_comm]
    have hsum: ∑ ρ∈Zg.image φ,(analyticOrderNatAt f ρ:ℂ)/(s-ρ)
        =(R:ℂ)⁻¹* ∑ ρg∈Zg,(analyticOrderNatAt g ρg:ℂ)/(w-ρg) :=by
      rw [Finset.sum_image (fun a _ b _ hab=>KI hab),Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρg Jg=>?_
      have h34: ‖ρg‖ ≤22/25:=((KV ρg).mp Jg).1
      rw [hord ρg (by linarith)]
      have hsub:s-φ ρg=(R:ℂ)*(w-ρg) :=by
        rw [← hφw,hφ]
        ring
      rw [hsub]
      rw [div_mul_eq_div_div_swap]
      field_simp
    rw [hsum]
    have abQ:logDeriv f s=(R:ℂ)⁻¹*logDeriv g w:=by
      rw [hld]
      field_simp
    rw [abQ, ← mul_sub,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hR]
    rw [div_eq_inv_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left hunit (inv_nonneg.mpr hR.le)
end Wg
theorem oZ: ∃ C:ℝ,0<C ∧ ∀ t:ℝ,6≤ |t| →
    ∃ Z:Finset ℂ,
      (↑Z={ρ∈Metric.closedBall (2+t* I) (22/25*(91/50)) | riemannZeta ρ=0}) ∧
      ((∑ ρ∈Z,(analyticOrderNatAt riemannZeta ρ:ℝ))≤C*Real.log (|t| +3)) ∧
      ∀ s∈Metric.closedBall (2+t* I) (3/2),riemannZeta s≠0→
        ‖logDeriv riemannZeta s- ∑ ρ∈Z,(analyticOrderNatAt riemannZeta ρ:ℂ)/(s-ρ)‖
          ≤C*Real.log (|t| +3) :=by
  obtain ⟨A,C₀,hC₀,hgrow⟩:=Zeta23.dQ.Dz
  set A':ℝ:=max A 0 with hA'
  have Eo:0≤A':=le_max_right _ _
  have hCpos:(0:ℝ)<(44795000*50/91)*(Real.log 3+Real.log (C₀+2)+A'+1) :=by
    have h1:(0:ℝ)≤Real.log 3:=Real.log_nonneg (by norm_num)
    have h2:(0:ℝ)≤Real.log (C₀+2) :=Real.log_nonneg (by linarith)
    positivity
  refine ⟨(44795000*50/91)*(Real.log 3+Real.log (C₀+2)+A'+1),hCpos,
    fun t ht=>?_⟩
  set s₀:ℂ:=2+t* I with hs₀
  have Xp:s₀.re=2:=by simp [hs₀]
  have acD:s₀.im=t:=by simp [hs₀]
  have Xq:riemannZeta s₀≠0:=
    riemannZeta_ne_zero_of_one_lt_re (by rw [Xp]; norm_num)
  have hlow:(1/3:ℝ)≤ ‖riemannZeta s₀‖ :=Zeta23.dQ.oR t
  have hone:(1:ℂ)∉Metric.closedBall s₀ (91/50) :=by
    intro h
    rw [Metric.mem_closedBall,Complex.dist_eq] at h
    have him:((1:ℂ)-s₀).im= -t:=by simp [hs₀]
    have: |t| ≤ ‖(1:ℂ)-s₀‖ :=by
      calc |t| = |((1:ℂ)-s₀).im| :=by rw [him,abs_neg]
        _≤ ‖(1:ℂ)-s₀‖ :=Complex.abs_im_le_norm _
    linarith
  have hfa:AnalyticOnNhd ℂ riemannZeta (Metric.closedBall s₀ (91/50)) :=
    Zeta23.dQ.uZ hone
  set B:ℝ:=3*(C₀*(|t| +2)^A'+2) with hB
  have ht2:(1:ℝ)≤ |t| +2:=by linarith
  have Sd:(1:ℝ)≤(|t| +2)^A':=Real.one_le_rpow ht2 Eo
  have Rh:2≤B:=by
    rw [hB]
    nlinarith [mul_nonneg hC₀.le (le_trans zero_le_one Sd)]
  have hfB: ∀ w∈Metric.closedBall s₀ (24/25*(91/50)), ‖riemannZeta w‖ ≤B* ‖riemannZeta s₀‖ :=by
    intro w hw
    rw [Metric.mem_closedBall,Complex.dist_eq] at hw
    have pC: |w.re-2| ≤24/25*(91/50) :=by
      have:=Complex.abs_re_le_norm (w-s₀)
      have hre:(w-s₀).re=w.re-2:=by simp [hs₀]
      rw [hre] at this
      linarith
    have Ci: |w.im-t| ≤24/25*(91/50) :=by
      have:=Complex.abs_im_le_norm (w-s₀)
      have him:(w-s₀).im=w.im-t:=by simp [hs₀]
      rw [him] at this
      linarith
    have WK:1≤ |w.im| :=by
      have h3: |t| - |w.im| ≤ |t-w.im| :=abs_sub_abs_le_abs_sub t w.im
      have h4: |t-w.im| = |w.im-t| :=abs_sub_comm t w.im
      linarith [Ci]
    have aau: |w.im| ≤ |t| +2:=by
      have:=abs_sub_abs_le_abs_sub w.im t
      have h2: |w.im| - |t| ≤ |w.im-t| :=this
      linarith [Ci]
    have hbound: ‖riemannZeta w‖ ≤C₀*(|t| +2)^A'+2:=by
      rcases le_or_gt w.re 2 with Se | Se
      · have h14:(1/4:ℝ)≤w.re:=by
          rw [abs_le] at pC
          linarith
        have:=hgrow w h14 Se WK
        calc ‖riemannZeta w‖ ≤C₀* |w.im| ^A:=this
          _≤C₀*(|t| +2)^A':=by
              refine mul_le_mul_of_nonneg_left ?_ hC₀.le
              calc |w.im| ^A≤ |w.im| ^A':=
                    Real.rpow_le_rpow_of_exponent_le WK (le_max_left _ _)
                _≤(|t| +2)^A':=Real.rpow_le_rpow (by linarith) aau Eo
          _≤C₀*(|t| +2)^A'+2:=by linarith
      · have:=Zeta23.dQ.oz (s:=w) (by linarith)
        have hπ:(Real.pi:ℝ)^2/6≤2:=by nlinarith [Real.pi_lt_d2,Real.pi_gt_three]
        calc ‖riemannZeta w‖ ≤Real.pi^2/6:=this
          _≤2:=hπ
          _≤C₀*(|t| +2)^A'+2:=by
              nlinarith [mul_nonneg hC₀.le (le_trans zero_le_one Sd)]
    calc ‖riemannZeta w‖ ≤C₀*(|t| +2)^A'+2:=hbound
      _=(B*(1/3)) :=by rw [hB]; ring
      _≤B* ‖riemannZeta s₀‖ :=by
          refine mul_le_mul_of_nonneg_left hlow (by rw [hB]; positivity)
  obtain ⟨Z,aav,Xr,Wh⟩:=oY (f:=riemannZeta)
    (by norm_num:(0:ℝ)<91/50) hfa Xq Rh hfB
  have Yx:(2:ℝ)≤Real.log (|t| +3) :=by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h1:=Real.exp_one_lt_d9
    calc Real.exp 2=Real.exp 1*Real.exp 1:=by rw [← Real.exp_add]; norm_num
      _≤2.7182818286*2.7182818286:=by nlinarith [Real.exp_pos 1]
      _≤9:=by norm_num
      _≤ |t| +3:=by linarith
  have Fv:Real.log B≤(Real.log 3+Real.log (C₀+2)+A')*Real.log (|t| +3) :=by
    have h1:B≤3*((C₀+2)*(|t| +2)^A') :=by
      rw [hB]
      nlinarith [Sd,hC₀]
    have h2:Real.log B≤Real.log (3*((C₀+2)*(|t| +2)^A')) :=
      Real.log_le_log (by rw [hB]; positivity) h1
    rw [Real.log_mul (by norm_num:(3:ℝ)≠0) (by positivity),
      Real.log_mul (by norm_num:(3:ℝ)≠0) (by positivity),
      Real.log_mul (by positivity:(C₀+2:ℝ)≠0) (by positivity),
      Real.log_rpow (by linarith:(0:ℝ)< |t| +2)] at h2
    have h3:Real.log (|t| +2)≤Real.log (|t| +3) :=
      Real.log_le_log (by linarith) (by linarith)
    have h4:(0:ℝ)≤Real.log 3:=Real.log_nonneg (by norm_num)
    have h5:(0:ℝ)≤Real.log (C₀+2) :=Real.log_nonneg (by linarith)
    have hBeq:Real.log B=Real.log 3+Real.log (C₀*(|t| +2)^A'+2) :=by
      rw [hB,Real.log_mul (by norm_num:(3:ℝ)≠0) (by positivity)]
    rw [hBeq]
    nlinarith [mul_nonneg Eo (by linarith:(0:ℝ)≤Real.log (|t|+3)-Real.log (|t|+2)),
      mul_nonneg h4 (by linarith:(0:ℝ)≤Real.log (|t|+3)-1),
      mul_nonneg h5 (by linarith:(0:ℝ)≤Real.log (|t|+3)-1),Yx]
  have h4:(0:ℝ)≤Real.log 3:=Real.log_nonneg (by norm_num)
  have h5:(0:ℝ)≤Real.log (C₀+2) :=Real.log_nonneg (by linarith)
  refine ⟨Z,?_,?_,?_⟩
  · rw [aav]
  · refine Xr.trans ?_
    have hratio:((24/25:ℝ))/(22/25)=12/11:=by norm_num
    have abR:(1:ℝ)/12≤Real.log ((24/25)/(22/25)) :=by
      rw [hratio]
      have h:=Real.log_le_sub_one_of_pos (show (0:ℝ)<11/12 by norm_num)
      rw [show (11/12:ℝ)=(12/11)⁻¹ by norm_num,Real.log_inv] at h
      linarith
    have MQ:(0:ℝ)<Real.log ((24/25)/(22/25)) :=by
      rw [hratio]
      exact Real.log_pos (by norm_num)
    have Xt:(0:ℝ)≤Real.log B:=Real.log_nonneg (by linarith)
    calc 1/Real.log ((24/25)/(22/25))*Real.log B≤12*Real.log B:=by
          refine mul_le_mul_of_nonneg_right ?_ Xt
          rw [div_le_iff₀ MQ]
          linarith
      _≤12*((Real.log 3+Real.log (C₀+2)+A')*Real.log (|t| +3)) :=
          mul_le_mul_of_nonneg_left Fv (by norm_num)
      _≤44795000*50/91*(Real.log 3+Real.log (C₀+2)+A'+1)*Real.log (|t| +3) :=by
          nlinarith [Yx,Eo]
  · intro s hs abS
    have hs':s∈Metric.closedBall s₀ (83/100*(91/50)) :=
      Metric.closedBall_subset_closedBall (by norm_num) hs
    refine (Wh s hs' abS).trans ?_
    calc 44795000/(91/50)*Real.log B
        ≤44795000/(91/50)*((Real.log 3+Real.log (C₀+2)+A')*Real.log (|t| +3)) :=
          mul_le_mul_of_nonneg_left Fv (by norm_num)
      _≤(44795000*50/91)*(Real.log 3+Real.log (C₀+2)+A'+1)*Real.log (|t| +3) :=by
          nlinarith [Yx,Eo]
end bR
end Zeta23
end
end

-- Zeta23.ThmE.Hypotheses
section
open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set
noncomputable section
namespace Zeta23
namespace ThmE
def Fy (q:ℕ) (T:ℝ) :ℝ:=Real.log (q*T/(2*Real.pi))+2*Real.log 2 -1
def lV (κ:ℕ) (q:ℕ) (τ:ℝ) :ℝ:=
  (1/(2*Real.pi))*
    (Real.log (q/Real.pi)+(Complex.digamma (1/4+(κ:ℂ)/2+Complex.I*τ/2)).re)
structure XM (κ q:ℕ) :Prop where
  even: ∀ τ:ℝ,lV κ q (-τ)=lV κ q τ
  smooth:ContDiff ℝ ⊤ (lV κ q)
  monotoneOn:MonotoneOn (lV κ q) (Ici 0)
  Kp: ∀ τ:ℝ,lV κ q 0≤lV κ q τ
  rD: -1<lV κ q 0
  OJ: ∃ C:ℝ, ∀ τ:ℝ,1≤ |τ| →
    |lV κ q τ-(1/(2*Real.pi))*Real.log (q* |τ| /(2*Real.pi))| ≤C/τ^2
  GK: ∃ C:ℝ, ∀ τ:ℝ,1≤ |τ| → |deriv (lV κ q) τ| ≤C/ |τ|
  Uh: ∃ C T₀:ℝ, ∀ T:ℝ,T₀≤T→
    |(∫ τ in T..(2*T),lV κ q τ)-T*Fy q T/(2*Real.pi)| ≤C/T
  Nr: ∃ C T₀:ℝ, ∀ T:ℝ,T₀≤T→
    |(∫ τ in T..(2*T),lV κ q τ^2)-T*Fy q T^2/(4*Real.pi^2)|
      ≤C*(T*Fy q T^2/(4*Real.pi^2))/l T^2
section UE
end UE
structure Sj (κ q:ℕ) (C:ℝ) :Prop where
  even: ∀ τ:ℝ,lV κ q (-τ)=lV κ q τ
  smooth:ContDiff ℝ ⊤ (lV κ q)
  monotoneOn:MonotoneOn (lV κ q) (Ici 0)
  Kp: ∀ τ:ℝ,lV κ q 0≤lV κ q τ
  rD: -1<lV κ q 0
  OJ: ∀ τ:ℝ,1≤ |τ| →
    |lV κ q τ-(1/(2*Real.pi))*Real.log (q* |τ| /(2*Real.pi))| ≤C/τ^2
  GK: ∀ τ:ℝ,1≤ |τ| → |deriv (lV κ q) τ| ≤C/ |τ|
  Uh: ∀ T:ℝ,C≤T→
    |(∫ τ in T..(2*T),lV κ q τ)-T*Fy q T/(2*Real.pi)| ≤C/T
  Nr: ∀ T:ℝ,C≤T→
    |(∫ τ in T..(2*T),lV κ q τ^2)-T*Fy q T^2/(4*Real.pi^2)|
      ≤C*(T*Fy q T^2/(4*Real.pi^2))/l T^2
end ThmE
end Zeta23
end
end

-- Zeta23.lK.adA
section
noncomputable section
namespace Zeta23
namespace Yy
open MeasureTheory intervalIntegral
end Yy
end Zeta23
end
end

-- Zeta23.lK.Complete
section
noncomputable section
namespace Zeta23
end Zeta23
end
end

-- Zeta23.bR.XO
section
noncomputable section
namespace Zeta23
namespace bR
open Complex
theorem jB {s:ℂ} (hs:0<s.re) :
    logDeriv Complex.Gammaℝ s= -((Real.log Real.pi:ℝ) :ℂ)/2+(1/2)*Complex.digamma (s/2) :=by
  have hπ:(Real.pi:ℂ)≠0:=Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hs2:0<(s/2).re:=by simp; linarith
  have hGne:Complex.Gamma (s/2)≠0:=Complex.Gamma_ne_zero_of_re_pos hs2
  have Xv:(Real.pi:ℂ)^(-s/2)≠0:=by
    rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _
  have hfun:Complex.Gammaℝ=fun s=>(fun s:ℂ=>(Real.pi:ℂ)^(-s/2)) s
      *(Complex.Gamma∘fun s:ℂ=>s/2) s:=by
    funext s; rw [Complex.Gammaℝ_def]; rfl
  have WL:HasDerivAt (fun s:ℂ=>(Real.pi:ℂ)^(-s/2))
      ((Real.pi:ℂ)^(-s/2)*Complex.log Real.pi*(-1/2)) s:=by
    have h:=((hasDerivAt_id s).neg.div_const 2).const_cpow (c:=(Real.pi:ℂ)) (Or.inl hπ)
    convert h using 1
    · funext x; simp
    · simp
  have UF:DifferentiableAt ℂ (fun s:ℂ=>(Real.pi:ℂ)^(-s/2)) s:=
    WL.differentiableAt
  have Ri:DifferentiableAt ℂ Complex.Gamma (s/2) :=by
    apply Complex.differentiableAt_Gamma
    intro m h
    have:=congrArg Complex.re h
    simp at this
    have:(0:ℝ)≤ m:=Nat.cast_nonneg m
    linarith
  have hhalf:DifferentiableAt ℂ (fun s:ℂ=>s/2) s:=differentiableAt_id.div_const 2
  have Xw:DifferentiableAt ℂ (Complex.Gamma∘fun s:ℂ=>s/2) s:=Ri.comp s hhalf
  rw [hfun,logDeriv_mul s Xv (by exact hGne) UF Xw,
    logDeriv_comp (g:=fun s:ℂ=>s/2) (x:=s) Ri hhalf, ← Complex.digamma_def]
  have h1:logDeriv (fun s:ℂ=>(Real.pi:ℂ)^(-s/2)) s=Complex.log Real.pi*(-1/2) :=by
    rw [logDeriv_apply,WL.deriv]
    field_simp
  have h2:deriv (fun s:ℂ=>s/2) s=1/2:=by
    have:HasDerivAt (fun s:ℂ=>s/2) (1/2) s:=by
      simpa using (hasDerivAt_id s).div_const 2
    exact this.deriv
  rw [h1,h2,(Complex.ofReal_log Real.pi_pos.le).symm]
  ring
end bR
end Zeta23
end
end

-- Zeta23.ThmE.Pe
section
noncomputable section
namespace Zeta23
namespace ThmE
namespace Pe
open MeasureTheory intervalIntegral
section Generic
variable {g:ℝ→ℝ}
end Generic
variable {κ q:ℕ}
end Pe
end ThmE
end Zeta23
end
end

-- Zeta23.ThmE.UG
section
noncomputable section
namespace Zeta23
namespace ThmE
namespace Wi
open Complex MeasureTheory intervalIntegral
variable {κ q:ℕ}
end Wi
end ThmE
end Zeta23
end
end

-- Zeta23.bR.Effective
section
noncomputable section
open Complex MeasureTheory Real Set
namespace Zeta23
namespace bR
end bR
end Zeta23
end
end

-- Zeta23.cE.abx
section
open Complex Set Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace Zeta23
namespace cE
theorem Ob (s:ℂ) :AnalyticAt ℂ xi s:=
  fO.analyticAt s
theorem gd {s:ℂ} (hs:0<s.re) (hs1:s≠1) :
    xi s=s*(s-1)/2*(Gammaℝ s*riemannZeta s) :=by
  have hs0:s≠0:=fun h=>by simp [h] at hs
  rw [RH s hs0 hs1,Zeta23.dQ.gJ hs0 (Gammaℝ_ne_zero_of_re_pos hs)]
private lemma QI {s:ℂ} (hs:s≠1) :conj s≠1:=fun h=>by
  have h2:=congrArg (starRingEnd ℂ) h
  simp only [Complex.conj_conj,map_one] at h2
  exact hs h2
private lemma Cj {s:ℂ} (hs:1<s.re) :conj (xi (conj s))=xi s:=by
  have hs':1<(conj s).re:=by rwa [Complex.conj_re]
  have h1:s≠1:=fun h=>by rw [h] at hs; simp at hs
  rw [gd (by linarith) (QI h1),gd (by linarith) h1,
    Zeta23.dQ.NZ,_root_.riemannZeta_conj]
  simp only [map_mul,map_sub,map_div₀,map_one,Complex.conj_conj,map_ofNat]
theorem MS (s:ℂ) :xi (conj s)=conj (xi s) :=by
  have hξ:AnalyticOnNhd ℂ xi univ:=fun z _=>Ob z
  have abT:AnalyticOnNhd ℂ (fun z=>conj (xi (conj z))) univ:=by
    refine DifferentiableOn.analyticOnNhd (fun z _=>?_) isOpen_univ
    have h3:=(fO (conj z)).conj_conj
    rw [Complex.conj_conj] at h3
    exact h3.differentiableWithinAt
  have hagree:(fun z=>conj (xi (conj z))) =ᶠ[𝓝 (2:ℂ)] xi:=by
    have hopen:IsOpen {z:ℂ | 1<z.re} :=isOpen_lt continuous_const Complex.continuous_re
    have h2:(2:ℂ)∈{z:ℂ | 1<z.re} :=by simp
    filter_upwards [hopen.mem_nhds h2] with z hz
    exact Cj hz
  have heq:=abT.eqOn_of_preconnected_of_eventuallyEq hξ isPreconnected_univ (mem_univ _) hagree
  have h3:conj (xi (conj (conj s)))=xi (conj s) :=heq (mem_univ (conj s))
  rw [Complex.conj_conj] at h3
  exact h3.symm
private lemma KW {f:ℂ→ℂ} (hf:Differentiable ℂ f)
    (h: ∀ z,f (conj z)=conj (f z)) (s:ℂ) :deriv f (conj s)=conj (deriv f s) :=by
  have hd:=((hf s).hasDerivAt).conj_conj
  have hfun:(fun z=>conj (f (conj z)))=f:=funext fun z=>by rw [h,Complex.conj_conj]
  have hd':HasDerivAt f (conj (deriv f s)) (conj s) :=by
    have:=hd
    simp only [Function.comp_def] at this
    rwa [hfun] at this
  exact hd'.deriv
theorem Pq (s:ℂ) :lJ (conj s)=conj (lJ s) :=
  KW fO MS s
def WM (s:ℂ) :ℂ:=logDeriv Complex.Gammaℝ s+1/s+1/(s-1)
theorem Cu {s:ℂ} (hs:0<s.re) (hs1:s≠1) :
    lJ s=((2*s-1)/2*Gammaℝ s+s*(s-1)/2*deriv Gammaℝ s)*riemannZeta s
      +s*(s-1)/2*Gammaℝ s*deriv riemannZeta s:=by
  have hopen:IsOpen ({z:ℂ | 0<z.re} ∩ {(1:ℂ)}ᶜ) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton
  have hev:xi =ᶠ[𝓝 s] fun z=>z*(z-1)/2*(Gammaℝ z*riemannZeta z) :=by
    filter_upwards [hopen.mem_nhds ⟨hs,hs1⟩] with z hz
    exact gd hz.1 hz.2
  unfold lJ
  rw [hev.deriv_eq]
  have h1:HasDerivAt (fun z:ℂ=>z*(z-1)/2) ((2*s-1)/2) s:=by
    have:=((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).div_const 2
    exact this.congr_deriv (by simp only [id_eq]; ring)
  have h2:HasDerivAt Gammaℝ (deriv Gammaℝ s) s:=(Zeta23.bR.kM hs).hasDerivAt
  have h3:HasDerivAt riemannZeta (deriv riemannZeta s) s:=
    (differentiableAt_riemannZeta hs1).hasDerivAt
  have h:HasDerivAt (fun z:ℂ=>z*(z-1)/2*(Gammaℝ z*riemannZeta z))
      ((2*s-1)/2*(Gammaℝ s*riemannZeta s)
        +s*(s-1)/2*(deriv Gammaℝ s*riemannZeta s+Gammaℝ s*deriv riemannZeta s)) s:=
    h1.mul (h2.mul h3)
  rw [h.deriv]
  ring
theorem Bp {s:ℂ} (hs:0<s.re) (hs1:s≠1) (hζ:riemannZeta s≠0) :
    logDeriv xi s=WM s+logDeriv riemannZeta s:=by
  have hs0:s≠0:=fun h=>by simp [h] at hs
  have adT:s-1≠0:=sub_ne_zero.mpr hs1
  have hG:=Gammaℝ_ne_zero_of_re_pos hs
  rw [logDeriv_apply,show deriv xi s=lJ s from rfl,Cu hs hs1,
    gd hs hs1,WM,logDeriv_apply,logDeriv_apply]
  field_simp
  ring
end cE
end Zeta23
end
end

-- Zeta23.Assembly.Inputs
section
noncomputable section
open Matrix dS
open scoped ComplexOrder
namespace Zeta23
namespace Assembly
variable (Z:bT) (T:ℝ)
end Assembly
end Zeta23
end
end

-- Zeta23.Tail.Basic
section
noncomputable section
namespace Zeta23
namespace Tail
structure ju {ι:Type*} (γ:ι→ℝ) (m:ι→ℕ) (A₀:ℝ) :Prop where
  one_le:1≤A₀
  window: ∀ t:ℝ, ∀ s:Finset ι,(∀ ρ∈s,t<γ ρ ∧ γ ρ≤t+1)→
    (∑ ρ∈s,(m ρ:ℝ))≤A₀*Real.log (|t| +3)
lemma ju.Cv {ι:Type*} {γ:ι→ℝ} {m:ι→ℕ} {A₀:ℝ}
    (h:ju γ m A₀) :0<A₀:=lt_of_lt_of_le one_pos h.one_le
end Tail
end Zeta23
end
end

-- Zeta23.Tail.adU
section
noncomputable section
open Finset Real
namespace Zeta23
namespace Tail
end Tail
end Zeta23
end
end

-- Zeta23.Tail.Count
section
noncomputable section
open Finset Real
namespace Zeta23
namespace Tail
lemma zW {ι:Type*} (s:Finset ι) (m:ι→ℕ) (key:ι→ℕ) (K:ℕ)
    {C:ℝ} (hkey: ∀ ρ∈s,key ρ<K)
    (hcount: ∀ j<K, ∑ ρ∈s with key ρ=j,(m ρ:ℝ)≤C) :
    ∑ ρ∈s,(m ρ:ℝ)≤K*C:=by
  rw [← sum_fiberwise_of_maps_to (g:=key) (t:=range K)
    (fun ρ hρ=>mem_range.mpr (hkey ρ hρ))]
  calc ∑ j∈range K, ∑ ρ∈s with key ρ=j,(m ρ:ℝ)
      ≤ ∑ j∈range K,C:=sum_le_sum fun j hj=>hcount j (mem_range.mp hj)
    _=K*C:=by rw [sum_const,card_range,nsmul_eq_mul]
end Tail
end Zeta23
end
end

-- Zeta23.Tail.RankOne
section
noncomputable section
open Matrix Finset
open scoped ComplexOrder
namespace Zeta23
namespace Tail
open dS
variable {n:Type*} [Fintype n] [DecidableEq n]
end Tail
end Zeta23
end
end

-- Zeta23.Tail
section
noncomputable section
open Matrix Finset Complex
open scoped ComplexOrder
namespace Zeta23
namespace Tail
open dS
theorem ju.Dq (Z:bT) {A₀:ℝ} (hA₀:1≤A₀)
    (hloc: ∀ t:ℝ,(Z.N t (t+1) :ℝ)≤A₀*Real.log (|t| +3)) :
    ju (fun ρ:Z.carrier=>(ρ:ℂ).im) (fun ρ:Z.carrier=>Z.mult ρ) A₀ where
  one_le:=hA₀
  window t s hs:=by
    classical
    refine le_trans ?_ (hloc t)
    have hfin:(Z.window t (t+1)).Finite:=Z.dH t (t+1)
    unfold bT.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hsub:s.map (Function.Embedding.subtype _)⊆hfin.toFinset:=by
      intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨ρ,hρ,rfl⟩:=hx
      rw [Set.Finite.mem_toFinset]
      exact ⟨ρ.2,hs ρ hρ⟩
    have h:=Finset.sum_le_sum_of_subset (f:=Z.mult) hsub
    rw [Finset.sum_map] at h
    exact_mod_cast h
section Concrete
variable (Z:bT) (T:ℝ)
variable {P T}
variable {Z}
end Concrete
section Series
variable {Z:bT} {T A₀ C₁:ℝ}
namespace Xx
end Xx
end Series
section Hermitian
variable {T:ℝ}
variable {Z:bT} {A₀ C₁:ℝ}
end Hermitian
section Export
open Filter
variable {Z:bT} {T A₀ C₁:ℝ}
end Export
end Tail
end Zeta23
end
end

-- Zeta23.pD
section
open MeasureTheory Complex Filter Set
open scoped Real FourierTransform Convolution ComplexConjugate ArithmeticFunction
noncomputable section
namespace Zeta23
namespace EF
end EF
namespace EF
end EF
end Zeta23
end
end

-- Zeta23.Poisson.acE
section
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
namespace Zeta23
end Zeta23
end

-- Zeta23.bR.WO
section
noncomputable section
namespace Zeta23
namespace bR
open Complex Set Filter MeasureTheory
lemma KX (ρ:ℂ) :(bZ ρ).re=ρ.im:=by
  simp [bZ,Complex.div_I]
lemma Sl (ρ:ℂ) :(bZ ρ).im=1/2 -ρ.re:=by
  simp [bZ,Complex.div_I]
lemma UH (n:ℤ) (hn:n≠0) :
    Real.log (|(n:ℝ)| +3)/(1+(n:ℝ)^2)≤4* |(n:ℝ)| ^(-(3/2:ℝ)) :=by
  have hn1:(1:ℝ)≤ |(n:ℝ)| :=by exact_mod_cast Int.one_le_abs hn
  have hn0:(0:ℝ)< |(n:ℝ)| :=by linarith
  have h1:=Real.log_le_rpow_div (show (0:ℝ)≤ |(n:ℝ)| +3 by positivity)
    (show (0:ℝ)<1/2 by norm_num)
  have h2:(|(n:ℝ)| +3)^(1/2:ℝ)≤(4* |(n:ℝ)|)^(1/2:ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h3:(4* |(n:ℝ)|)^(1/2:ℝ)=2* |(n:ℝ)| ^(1/2:ℝ) :=by
    rw [Real.mul_rpow (by norm_num) hn0.le,show (4:ℝ)^(1/2:ℝ)=2 by
      rw [show (4:ℝ)=2^(2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num]
  have hA:Real.log (|(n:ℝ)| +3)≤4* |(n:ℝ)| ^(1/2:ℝ) :=by
    have:(|(n:ℝ)| +3)^(1/2:ℝ)/(1/2)=2*(|(n:ℝ)| +3)^(1/2:ℝ) :=by ring
    rw [this] at h1; rw [h3] at h2; linarith
  have hB:1/(1+(n:ℝ)^2)≤ |(n:ℝ)| ^(-2:ℝ) :=by
    rw [Real.rpow_neg hn0.le,show (2:ℝ)=((2:ℕ):ℝ) by norm_num,Real.rpow_natCast,sq_abs,
      one_div]
    exact inv_anti₀ (by positivity) (by linarith)
  calc Real.log (|(n:ℝ)| +3)/(1+(n:ℝ)^2)
      =Real.log (|(n:ℝ)| +3)*(1/(1+(n:ℝ)^2)) :=by ring
    _≤(4* |(n:ℝ)| ^(1/2:ℝ))* |(n:ℝ)| ^(-2:ℝ) :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _=4* |(n:ℝ)| ^(-(3/2:ℝ)) :=by
        rw [mul_assoc, ← Real.rpow_add hn0]; norm_num
lemma KY:
    Summable (fun n:ℤ=>Real.log (|(n:ℝ)| +3)/(1+(n:ℝ)^2)) :=by
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_abs_int_rpow (show (1:ℝ)<3/2 by norm_num)).mul_left 4) ?_
  filter_upwards [eventually_cofinite_ne 0] with n hn
  have h0:0≤Real.log (|(n:ℝ)| +3)/(1+(n:ℝ)^2) :=
    div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n:ℝ)])) (by positivity)
  rw [Real.norm_eq_abs,abs_of_nonneg h0]
  exact UH n hn
def totalWeight:ℝ:= ∑' n:ℤ,Real.log (|(n:ℝ)| +3)/(1+(n:ℝ)^2)
def key (y:ℝ) :ℤ:= ⌈y⌉ -1
lemma UJ (y:ℝ) :(key y:ℝ)<y:=by
  have:=Int.ceil_lt_add_one y; unfold key; push_cast; linarith
lemma Bq (y:ℝ) :y≤(key y:ℝ)+1:=by
  have:=Int.le_ceil y; unfold key; push_cast; linarith
lemma Oc {y:ℝ} {n:ℤ} (h1:(n:ℝ)<y) (h2:y≤(n:ℝ)+1) :
    (1+(n:ℝ)^2)/4≤1+y^2:=by
  rcases le_or_gt 0 (n:ℝ) with hn | hn
  · nlinarith
  · have hn':n<0:=by exact_mod_cast hn
    have hn1:(n:ℝ)≤ -1:=by exact_mod_cast (show n≤ -1 by omega)
    have hy:((n:ℝ)+1)^2≤y^2:=by
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by linarith:(0:ℝ)≤ -(y+((n:ℝ)+1)))]
    nlinarith [hy,sq_nonneg ((n:ℝ)+4/3)]
theorem DJ (Z:bT) {A₀:ℝ} (hA₀:1≤A₀)
    (aaw: ∀ t:ℝ,(Z.N t (t+1) :ℝ)≤A₀*Real.log (|t| +3)) :
    Summable (fun ρ:Z.carrier=>
      (Z.mult ρ:ℝ)/(1+Complex.normSq (bZ ρ))) :=by
  classical
  have GW:=Tail.ju.Dq Z hA₀ aaw
  have hW:=KY
  refine summable_of_sum_le (c:=4*A₀*totalWeight) (fun ρ=>div_nonneg (Nat.cast_nonneg _)
    (by linarith [Complex.normSq_nonneg (bZ (ρ:ℂ))])) fun s=>?_
  set κ:Z.carrier→ℤ:=fun ρ=>key (ρ:ℂ).im with hκ
  rw [← Finset.sum_fiberwise_of_maps_to (g:=κ) (t:=s.image κ) (fun ρ hρ=>Finset.mem_image_of_mem κ hρ)]
  have Yz: ∀ n∈s.image κ,
      ∑ ρ∈s with κ ρ=n,(Z.mult (ρ:ℂ) :ℝ)/(1+Complex.normSq (bZ ρ))
        ≤4*A₀*(Real.log (|(n:ℝ)| +3)/(1+(n:ℝ)^2)) :=by
    intro n _
    have hwin:=GW.window n (s.filter fun ρ=>κ ρ=n) (fun ρ hρ=>by
      simp only [Finset.mem_filter] at hρ
      rw [← hρ.2]; exact ⟨UJ _,Bq _⟩)
    have hpt: ∀ ρ∈s.filter (fun ρ=>κ ρ=n),
        (Z.mult (ρ:ℂ) :ℝ)/(1+Complex.normSq (bZ ρ))
          ≤(4/(1+(n:ℝ)^2))*(Z.mult ρ:ℝ) :=by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      have h1:(n:ℝ)<(ρ:ℂ).im:=by rw [← hρ.2]; exact UJ _
      have h2:(ρ:ℂ).im≤(n:ℝ)+1:=by rw [← hρ.2]; exact Bq _
      have hge:=Oc h1 h2
      have hnorm:1+((ρ:ℂ).im)^2≤1+Complex.normSq (bZ ρ) :=by
        rw [Complex.normSq_apply,KX]; nlinarith [sq_nonneg ((bZ (ρ:ℂ)).im)]
      have hm:(0:ℝ)≤Z.mult (ρ:ℂ) :=Nat.cast_nonneg _
      have hN0:0<1+Complex.normSq (bZ (ρ:ℂ)) :=by
        linarith [Complex.normSq_nonneg (bZ (ρ:ℂ))]
      have hinv:1/(1+Complex.normSq (bZ (ρ:ℂ)))≤4/(1+(n:ℝ)^2) :=by
        rw [div_le_div_iff₀ hN0 (by positivity)]; nlinarith [hge,hnorm]
      calc (Z.mult (ρ:ℂ) :ℝ)/(1+Complex.normSq (bZ ρ))
          =(Z.mult (ρ:ℂ) :ℝ)*(1/(1+Complex.normSq (bZ (ρ:ℂ)))) :=by ring
        _≤(Z.mult (ρ:ℂ) :ℝ)*(4/(1+(n:ℝ)^2)) :=mul_le_mul_of_nonneg_left hinv hm
        _=(4/(1+(n:ℝ)^2))*(Z.mult ρ:ℝ) :=by ring
    calc ∑ ρ∈s with κ ρ=n,(Z.mult (ρ:ℂ) :ℝ)/(1+Complex.normSq (bZ ρ))
        ≤ ∑ ρ∈s with κ ρ=n,(4/(1+(n:ℝ)^2))*(Z.mult ρ:ℝ) :=
          Finset.sum_le_sum hpt
      _=(4/(1+(n:ℝ)^2))* ∑ ρ∈s with κ ρ=n,(Z.mult ρ:ℝ) :=by
          rw [Finset.mul_sum]
      _≤(4/(1+(n:ℝ)^2))*(A₀*Real.log (|(n:ℝ)| +3)) :=
          mul_le_mul_of_nonneg_left hwin (by positivity)
      _=4*A₀*(Real.log (|(n:ℝ)| +3)/(1+(n:ℝ)^2)) :=by ring
  calc ∑ n∈s.image κ, ∑ ρ∈s with κ ρ=n,(Z.mult (ρ:ℂ) :ℝ)/(1+Complex.normSq (bZ ρ))
      ≤ ∑ n∈s.image κ,4*A₀*(Real.log (|(n:ℝ)| +3)/(1+(n:ℝ)^2)) :=
        Finset.sum_le_sum Yz
    _=4*A₀* ∑ n∈s.image κ,Real.log (|(n:ℝ)| +3)/(1+(n:ℝ)^2) :=by
        rw [Finset.mul_sum]
    _≤4*A₀*totalWeight:=by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact hW.sum_le_tsum _ fun n _=>
          div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n:ℝ)])) (by positivity)
theorem zA (hs:iw) :
    Summable (fun ρ:(jo hs).carrier=>
      (aP ρ:ℝ)/(1+Complex.normSq (bZ ρ))) :=by
  obtain ⟨A₀,hA₀,hloc⟩:=Zeta23.dQ.oH
  exact DJ (jo hs) hA₀ (fun t=>by rw [GQ]; exact hloc t)
end bR
end Zeta23
end
end

-- Zeta23.pD.Bridge
section
open MeasureTheory Complex Filter Set
open scoped Real FourierTransform ComplexConjugate
noncomputable section
namespace Zeta23
namespace EF
end EF
end Zeta23
end
end

-- Zeta23.bR.YA
section
noncomputable section
namespace Zeta23
namespace bR
open Complex MeasureTheory
open scoped ArithmeticFunction
theorem Cw: ∃ C:ℝ,0<C ∧ ∀ s:ℂ,1/4≤ s.re→s.re≤1→
    ‖Complex.digamma s‖ ≤C*Real.log (2+ |s.im|) :=by
  have hdiff: ∀ s:ℂ,0<s.re→DifferentiableAt ℂ Complex.digamma s:=by
    intro s hs
    have hzero: ∀ m:ℕ,s≠ -(m:ℂ) :=by
      intro m h
      rw [h] at hs
      simp only [Complex.neg_re,Complex.natCast_re] at hs
      nlinarith [Nat.cast_nonneg (α:=ℝ) m]
    have hopen:IsOpen {w:ℂ | 0<w.re} :=isOpen_lt continuous_const Complex.continuous_re
    have yZ:AnalyticAt ℂ Complex.Gamma s:=by
      rw [Complex.analyticAt_iff_eventually_differentiableAt]
      filter_upwards [hopen.mem_nhds hs] with w hw
      refine Complex.differentiableAt_Gamma w fun m=>?_
      intro h
      rw [h] at hw
      simp only [Complex.neg_re,Complex.natCast_re] at hw
      nlinarith [Nat.cast_nonneg (α:=ℝ) m]
    have Fw:Complex.Gamma s≠0:=Complex.Gamma_ne_zero hzero
    have Sm:AnalyticAt ℂ Complex.digamma s:=by
      have h1:AnalyticAt ℂ (deriv Complex.Gamma) s:=yZ.deriv
      have h2:=h1.div yZ Fw
      exact h2.congr (by
        filter_upwards with w
        rw [Complex.digamma_def,logDeriv_apply]
        rfl)
    exact Sm.differentiableAt
  have hK:IsCompact (Complex.reProdIm (Set.Icc (1/4:ℝ) 1) (Set.Icc (-(1/2) :ℝ) (1/2))) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have YB:ContinuousOn Complex.digamma
      (Complex.reProdIm (Set.Icc (1/4:ℝ) 1) (Set.Icc (-(1/2) :ℝ) (1/2))) :=by
    intro s hs
    have hsre:1/4≤ s.re:=(Complex.mem_reProdIm.mp hs).1.1
    exact ((hdiff s (by linarith)).continuousAt).continuousWithinAt
  obtain ⟨M,hM⟩:=hK.exists_bound_of_continuousOn YB
  have hM0:(0:ℝ)≤M:=by
    have h:=hM (1/2:ℂ) (by
      rw [Complex.mem_reProdIm]
      constructor
      · simp only [Complex.div_ofNat_re,Complex.one_re]
        norm_num
      · simp only [Complex.div_ofNat_im,Complex.one_im]
        norm_num)
    exact le_trans (norm_nonneg _) h
  have zC:(0:ℝ)<Real.log 2:=Real.log_pos (by norm_num)
  have hπ:(0:ℝ)<Real.pi:=Real.pi_pos
  set K₀:ℝ:=14+Real.pi+Real.log 4 with hK₀
  have YC:(0:ℝ)<K₀:=by positivity
  refine ⟨max (M/Real.log 2) (1+K₀/Real.log 2)+1,by positivity,fun s MW Se=>?_⟩
  have Jh:Real.log 2≤Real.log (2+ |s.im|) :=by
    apply Real.log_le_log (by norm_num)
    have:=abs_nonneg s.im
    linarith
  have MQ:(0:ℝ)<Real.log (2+ |s.im|) :=lt_of_lt_of_le zC Jh
  rcases le_or_gt (|s.im|) (1/2) with him | him
  · 
    have hsK:s∈Complex.reProdIm (Set.Icc (1/4:ℝ) 1) (Set.Icc (-(1/2) :ℝ) (1/2)) :=by
      rw [Complex.mem_reProdIm]
      refine ⟨⟨MW,Se⟩,?_⟩
      rw [Set.mem_Icc]
      constructor <;> [linarith [neg_abs_le s.im]; linarith [le_abs_self s.im]]
    calc ‖Complex.digamma s‖ ≤M:=hM s hsK
      _=(M/Real.log 2)*Real.log 2:=by
          field_simp
      _≤(max (M/Real.log 2) (1+K₀/Real.log 2)+1)*Real.log (2+ |s.im|) :=by
          apply mul_le_mul ?_ Jh zC.le (by positivity)
          calc M/Real.log 2≤ max (M/Real.log 2) (1+K₀/Real.log 2) :=le_max_left _ _
            _≤ max (M/Real.log 2) (1+K₀/Real.log 2)+1:=by linarith
  · 
    have aax:(0:ℝ)<s.re:=by linarith
    have hst:=Zeta23.kZ.oB (w:=s) aax (by linarith)
    have UK:(1/4:ℝ)≤ ‖s‖ :=
      le_trans MW (le_trans (le_abs_self _) (Complex.abs_re_le_norm s))
    have Fz:(0:ℝ)< ‖s‖ :=by linarith
    have hs0:s≠0:=by
      intro h
      rw [h,norm_zero] at Fz
      exact lt_irrefl 0 Fz
    have abb: ‖s‖ ≤1+ |s.im| :=by
      calc ‖s‖ ≤ |s.re| + |s.im| :=Complex.norm_le_abs_re_add_abs_im s
        _≤1+ |s.im| :=by
            have: |s.re| ≤1:=by
              rw [abs_le]
              constructor <;> linarith
            linarith
    have UL: ‖Complex.log s‖ ≤ |Real.log ‖s‖| +Real.pi:=by
      calc ‖Complex.log s‖ ≤ |(Complex.log s).re| + |(Complex.log s).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _≤ |Real.log ‖s‖| +Real.pi:=by
            rw [Complex.log_re,Complex.log_im]
            have:=Complex.abs_arg_le_pi s
            linarith [abs_nonneg (Complex.arg s)]
    have Pv: |Real.log ‖s‖| ≤Real.log 4+Real.log (2+ |s.im|) :=by
      rcases le_or_gt (Real.log ‖s‖) 0 with hneg | hpos
      · 
        have h1:Real.log (1/4:ℝ)≤Real.log ‖s‖ :=Real.log_le_log (by norm_num) UK
        have h2:Real.log (1/4:ℝ)= -Real.log 4:=by
          rw [show (1/4:ℝ)=4⁻¹ by norm_num,Real.log_inv]
        rw [abs_of_nonpos hneg]
        have h3:(0:ℝ)≤Real.log (2+ |s.im|) :=by
          apply Real.log_nonneg
          have:=abs_nonneg s.im
          linarith
        linarith
      · rw [abs_of_pos hpos]
        have h1:Real.log ‖s‖ ≤Real.log (2+ |s.im|) :=by
          apply Real.log_le_log Fz
          have:=abs_nonneg s.im
          linarith
        have h2:(0:ℝ)≤Real.log 4:=Real.log_nonneg (by norm_num)
        linarith
    have YD: ‖(1/2:ℂ)/s‖ ≤2:=by
      rw [norm_div]
      have h1: ‖(1/2:ℂ)‖ =1/2:=by
        rw [show (1/2:ℂ)=((1/2:ℝ) :ℂ) by norm_num,Complex.norm_real,
          Real.norm_eq_abs,abs_of_pos (by norm_num)]
      rw [h1,div_le_iff₀ Fz]
      linarith
    have Wj:3/s.im^2≤12:=by
      have h1:(1/4:ℝ)≤ s.im^2:=by
        have h2:(1/2:ℝ)≤ |s.im| :=him.le
        nlinarith [abs_nonneg s.im,sq_abs s.im]
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith
    have Pw: ‖Complex.digamma s‖
        ≤Real.log (2+ |s.im|)+K₀:=by
      have h1: ‖Complex.digamma s‖
          ≤ ‖Complex.digamma s-Complex.log s+(1/2:ℂ)/s‖ + ‖Complex.log s‖
            + ‖(1/2:ℂ)/s‖ :=by
        have h2:Complex.digamma s=(Complex.digamma s-Complex.log s+(1/2:ℂ)/s)
            +Complex.log s-(1/2:ℂ)/s:=by ring
        calc ‖Complex.digamma s‖
            = ‖(Complex.digamma s-Complex.log s+(1/2:ℂ)/s)
                +Complex.log s-(1/2:ℂ)/s‖ :=by rw [← h2]
          _≤ ‖(Complex.digamma s-Complex.log s+(1/2:ℂ)/s)+Complex.log s‖
              + ‖(1/2:ℂ)/s‖ :=norm_sub_le _ _
          _≤ ‖Complex.digamma s-Complex.log s+(1/2:ℂ)/s‖ + ‖Complex.log s‖
              + ‖(1/2:ℂ)/s‖ :=by
              have:=norm_add_le (Complex.digamma s-Complex.log s+(1/2:ℂ)/s)
                (Complex.log s)
              linarith
      rw [hK₀]
      have adV:Real.pi<4:=Real.pi_lt_four
      calc ‖Complex.digamma s‖
          ≤ ‖Complex.digamma s-Complex.log s+(1/2:ℂ)/s‖ + ‖Complex.log s‖
            + ‖(1/2:ℂ)/s‖ :=h1
        _≤3/s.im^2+(|Real.log ‖s‖| +Real.pi)+2:=by
            have:=hst
            linarith [UL,YD]
        _≤12+((Real.log 4+Real.log (2+ |s.im|))+Real.pi)+2:=by
            linarith [Wj,Pv]
        _≤Real.log (2+ |s.im|)+(14+Real.pi+Real.log 4) :=by linarith
    calc ‖Complex.digamma s‖ ≤Real.log (2+ |s.im|)+K₀:=Pw
      _≤Real.log (2+ |s.im|)+(K₀/Real.log 2)*Real.log (2+ |s.im|) :=by
          have h3:K₀/Real.log 2*Real.log 2≤K₀/Real.log 2*Real.log (2+ |s.im|) :=
            mul_le_mul_of_nonneg_left Jh (by positivity)
          have h4:K₀/Real.log 2*Real.log 2=K₀:=by field_simp
          linarith
      _=(1+K₀/Real.log 2)*Real.log (2+ |s.im|) :=by ring
      _≤(max (M/Real.log 2) (1+K₀/Real.log 2)+1)*Real.log (2+ |s.im|) :=by
          apply mul_le_mul_of_nonneg_right ?_ MQ.le
          calc (1+K₀/Real.log 2)≤ max (M/Real.log 2) (1+K₀/Real.log 2) :=
                le_max_right _ _
            _≤ max (M/Real.log 2) (1+K₀/Real.log 2)+1:=by linarith
lemma vG: ∃ C:ℝ,0<C ∧ ∀ σ t:ℝ,1/2≤σ→σ≤3/2→
    ‖logDeriv Complex.Gammaℝ (σ+t* I)‖ ≤C*Real.log (2+ |t|) :=by
  obtain ⟨C,hC,hψ⟩:=Cw
  have acF:0<Real.log Real.pi:=Real.log_pos (by linarith [Real.pi_gt_three])
  refine ⟨2*Real.log Real.pi+C,by positivity,?_⟩
  intro σ t h1 h2
  have hre:0<((σ:ℂ)+t* I).re:=by simp; linarith
  rw [jB hre]
  have hs2:((σ:ℂ)+t* I)/2=((σ/2:ℝ) :ℂ)+((t/2:ℝ) :ℂ)* I:=by
    push_cast; ring
  have abV:=hψ (((σ:ℂ)+t* I)/2) (by rw [hs2]; simp; linarith) (by rw [hs2]; simp; linarith)
  have him:(((σ:ℂ)+t* I)/2).im=t/2:=by rw [hs2]; simp
  rw [him] at abV
  have zC:Real.log 2≤Real.log (2+ |t|) :=Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have ada:(1:ℝ)/2<Real.log 2:=by have:=Real.log_two_gt_d9; linarith
  have YF:Real.log (2+ |t/2|)≤Real.log (2+ |t|) :=by
    apply Real.log_le_log (by positivity)
    rw [abs_div,abs_two]; linarith [abs_nonneg t]
  have Py:0<Real.log Real.pi:=Real.log_pos (by linarith [Real.pi_gt_three])
  calc ‖-((Real.log Real.pi:ℝ) :ℂ)/2+1/2*Complex.digamma (((σ:ℂ)+t* I)/2)‖
      ≤ ‖-((Real.log Real.pi:ℝ) :ℂ)/2‖ + ‖1/2*Complex.digamma (((σ:ℂ)+t* I)/2)‖ :=
        norm_add_le _ _
    _=Real.log Real.pi/2+(1/2)* ‖Complex.digamma (((σ:ℂ)+t* I)/2)‖ :=by
        rw [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Py,norm_mul]
        norm_num
    _≤Real.log Real.pi/2+(1/2)*(C*Real.log (2+ |t/2|)) :=by gcongr
    _≤Real.log Real.pi*Real.log (2+ |t|)*2+C*Real.log (2+ |t|) :=by
        nlinarith [hC.le,YF,Real.log_nonneg (show (1:ℝ)≤2+ |t/2| by linarith [abs_nonneg (t/2)])]
    _=(2*Real.log Real.pi+C)*Real.log (2+ |t|) :=by ring
end bR
end Zeta23
end
end

-- Zeta23.bR.ZD
section
noncomputable section
namespace Zeta23
namespace bR
open Complex Set Filter Finset
lemma Jj (S:Finset ℝ) (a:ℝ) :
    ∃ R:ℝ,a≤R ∧ R≤a+1 ∧ ∀ y∈S,1/(2*((S.card:ℝ)+1))≤ |R-y| :=by
  classical
  set n:ℕ:=S.card with hn
  set δ:ℝ:=1/(2*((n:ℝ)+1)) with hδ
  have hδpos:0<δ:=by rw [hδ]; positivity
  have hδn:2*((n:ℝ)+1)*δ=1:=by rw [hδ]; field_simp
  set cand:ℕ→ℝ:=fun k=>a+(2*(k:ℝ)+1)*δ with Sz
  by_contra hcon
  push Not at hcon
  have hbad: ∀ k∈Finset.range (n+1), ∃ y∈S, |cand k-y| <δ:=by
    intro k hk
    have hk':(k:ℝ)≤n:=by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1:a≤cand k:=by simp only [Sz]; nlinarith
    have h2:cand k≤a+1:=by
      simp only [Sz]
      have:(2*(k:ℝ)+1)*δ≤(2*(n:ℝ)+1)*δ:=by gcongr
      nlinarith
    obtain ⟨y,hy,hlt⟩:=hcon (cand k) h1 h2
    exact ⟨y,hy,hlt⟩
  choose! f hf using hbad
  have hmaps:Set.MapsTo f (Finset.range (n+1)) S:=fun k hk=>(hf k hk).1
  obtain ⟨x,hx,y,hy,hxy,hfxy⟩:=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simp [hn]) hmaps
  have h1:=(hf x hx).2
  have h2:=(hf y hy).2
  rw [hfxy] at h1
  have hdist: |cand x-cand y| =2* |(x:ℝ)-y| *δ:=by
    simp only [Sz]
    rw [show a+(2*(x:ℝ)+1)*δ-(a+(2*(y:ℝ)+1)*δ)=(2*δ)*((x:ℝ)-y) by ring,
      abs_mul,abs_of_pos (by positivity)]
    ring
  have hxy1:(1:ℝ)≤ |(x:ℝ)-y| :=by
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · have:(x:ℝ)+1≤y:=by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]; linarith
    · have:(y:ℝ)+1≤x:=by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
  have htri: |cand x-cand y| <2*δ:=by
    calc |cand x-cand y| = |(cand x-f y)-(cand y-f y)| :=by ring_nf
      _≤ |cand x-f y| + |cand y-f y| :=abs_sub _ _
      _<δ+δ:=add_lt_add h1 h2
      _=2*δ:=by ring
  rw [hdist] at htri
  nlinarith
lemma zX (s ρ:ℂ) : |s.im-ρ.im| ≤ ‖s-ρ‖ :=by
  rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
lemma mK {t r:ℝ} (hr:r<2) {ρ:ℂ}
    (hρ:ρ∈Metric.closedBall (2+t* I) r) (hz:riemannZeta ρ=0) :aE ρ:=by
  rw [Metric.mem_closedBall,dist_eq_norm] at hρ
  have hre: |ρ.re-2| ≤r:=by
    have:=Complex.abs_re_le_norm (ρ-(2+t* I))
    simp at this; linarith
  refine ⟨hz,by rw [abs_le] at hre; linarith,?_⟩
  by_contra h
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
lemma wM {t r:ℝ} {ρ:ℂ} (hρ:ρ∈Metric.closedBall (2+t* I) r) :
    |ρ.im-t| ≤r:=by
  rw [Metric.mem_closedBall,dist_eq_norm] at hρ
  have:=Complex.abs_im_le_norm (ρ-(2+t* I))
  simp at this; linarith
lemma pH {A₀:ℝ}
    (GW:Tail.ju (fun ρ:aD.carrier=>(ρ:ℂ).im)
      (fun ρ:aD.carrier=>aD.mult ρ) A₀)
    {a:ℤ} (F:Finset aD.carrier)
    (hF: ∀ ρ∈F,(a:ℝ)<(ρ:ℂ).im ∧ (ρ:ℂ).im≤(a:ℝ)+6) :
    ∑ ρ∈F,(aD.mult ρ:ℝ)≤6*(A₀*Real.log (|(a:ℝ)| +9)) :=by
  classical
  have hA₀:=GW.Cv.le
  set key:aD.carrier→ℕ:=fun ρ=>(⌈(ρ:ℂ).im⌉ -a-1).toNat with hkey
  have Nz: ∀ ρ∈F,((a:ℝ)+key ρ<(ρ:ℂ).im ∧ (ρ:ℂ).im≤(a:ℝ)+key ρ+1)
      ∧ key ρ<6:=by
    intro ρ hρ
    obtain ⟨h1,h2⟩:=hF ρ hρ
    have hc1:=Int.le_ceil (ρ:ℂ).im
    have hc2:=Int.ceil_lt_add_one (ρ:ℂ).im
    have hlo:a+1≤ ⌈(ρ:ℂ).im⌉ :=by
      have:(a:ℝ)< ⌈(ρ:ℂ).im⌉ :=lt_of_lt_of_le h1 hc1
      have:a< ⌈(ρ:ℂ).im⌉ :=by exact_mod_cast this
      omega
    have hhi: ⌈(ρ:ℂ).im⌉ ≤a+6:=by
      have:(⌈(ρ:ℂ).im⌉ :ℝ)<(a:ℝ)+6+1:=by linarith
      have: ⌈(ρ:ℂ).im⌉ <a+6+1:=by exact_mod_cast this
      omega
    have hk:((key ρ:ℕ) :ℤ)= ⌈(ρ:ℂ).im⌉ -a-1:=by
      simp only [hkey]; rw [Int.toNat_of_nonneg (by omega)]
    have hkR:((key ρ:ℕ) :ℝ)=(⌈(ρ:ℂ).im⌉ :ℝ)-a-1:=by exact_mod_cast hk
    refine ⟨⟨by linarith,by linarith⟩,?_⟩
    have:((key ρ:ℕ) :ℤ)<6:=by omega
    exact_mod_cast this
  have h:=Tail.zW F (fun ρ=>aD.mult ρ) key 6
    (C:=A₀*Real.log (|(a:ℝ)| +9)) (fun ρ hρ=>(Nz ρ hρ).2) (fun k hk=>by
      have hw:=GW.window ((a:ℝ)+k) (F.filter fun ρ=>key ρ=k) (fun ρ hρ=>by
        simp only [Finset.mem_filter] at hρ
        have:=(Nz ρ hρ.1).1
        rw [hρ.2] at this; exact this)
      refine hw.trans (mul_le_mul_of_nonneg_left ?_ hA₀)
      apply Real.log_le_log (by positivity)
      have: |(a:ℝ)+k| ≤ |(a:ℝ)| +k:=by
        calc |(a:ℝ)+k| ≤ |(a:ℝ)| + |(k:ℝ)| :=abs_add_le _ _
          _= |(a:ℝ)| +k:=by rw [Nat.abs_cast]
      have hk6:(k:ℝ)<6:=by exact_mod_cast hk
      linarith)
  simpa using h
lemma wN (F:Finset aD.carrier) :
    (F.card:ℝ)≤ ∑ ρ∈F,(aD.mult ρ:ℝ) :=by
  rw [Finset.card_eq_sum_ones,Nat.cast_sum]
  refine Finset.sum_le_sum fun ρ _=>?_
  exact_mod_cast aD.one_le_mult ρ ρ.2
theorem KZ: ∃ C:ℝ,0<C ∧ ∀ j:ℕ,7≤j→
    ∃ R:ℝ,(j:ℝ)≤R ∧ R≤(j:ℝ)+1 ∧
    ∀ s:ℂ,(s.im=R ∨ s.im= -R)→1/2≤ s.re→s.re≤2→
      riemannZeta s≠0 ∧ ‖logDeriv riemannZeta s‖ ≤C*(Real.log ((j:ℝ)+3))^2:=by
  classical
  obtain ⟨C,hC,hpf⟩:=oZ
  obtain ⟨A₀,hA₀,hloc⟩:=Zeta23.dQ.rV
  have GW:=Tail.ju.Dq aD hA₀ hloc
  refine ⟨2*C*(48*A₀+3),by positivity,fun j hj=>?_⟩
  have hj7:(7:ℝ)≤j:=by exact_mod_cast hj
  set Lg:ℝ:=Real.log ((j:ℝ)+3) with hLg
  have adW:1≤Lg:=by
    rw [hLg, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have:=Real.exp_one_lt_d9; linarith
  have zC:Real.log 2≤Lg:=by
    rw [hLg]; exact Real.log_le_log (by norm_num) (by linarith)
  set Wp:Set ℂ:=aD.window ((j:ℝ)-3) ((j:ℝ)+3) with hWp
  set Wm:Set ℂ:=aD.window (-(j:ℝ)-4) (-(j:ℝ)+2) with hWm
  have YG:((fun ρ:aD.carrier=>(ρ:ℂ)) ⁻¹' Wp).Finite:=
    (aD.dH _ _).preimage Subtype.val_injective.injOn
  have YH:((fun ρ:aD.carrier=>(ρ:ℂ)) ⁻¹' Wm).Finite:=
    (aD.dH _ _).preimage Subtype.val_injective.injOn
  set Fp:Finset aD.carrier:=YG.toFinset with hFp
  set Fm:Finset aD.carrier:=YH.toFinset with hFm
  have Rj: ∀ ρ:aD.carrier,ρ∈Fp↔(ρ:ℂ)∈Wp:=fun ρ=>by
    rw [hFp,Set.Finite.mem_toFinset]; rfl
  have Rk: ∀ ρ:aD.carrier,ρ∈Fm↔(ρ:ℂ)∈Wm:=fun ρ=>by
    rw [hFm,Set.Finite.mem_toFinset]; rfl
  set S:Finset ℝ:=Fp.image (fun ρ:aD.carrier=>(ρ:ℂ).im)
    ∪ Fm.image (fun ρ:aD.carrier=> -(ρ:ℂ).im) with hS
  have acG: ∑ ρ∈Fp,(aD.mult ρ:ℝ)≤6*(A₀*(2*Lg)) :=by
    have h:=pH GW (a:=(j:ℤ)-3) Fp (fun ρ hρ=>by
      have:=((Rj ρ).mp hρ).2; push_cast; constructor <;> linarith [this.1,this.2])
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ GW.Cv.le)
      (by norm_num))
    · have: |((j:ℤ)-3:ℤ)| =(j:ℤ)-3:=abs_of_nonneg (by omega)
      have habs: |(((j:ℤ)-3:ℤ) :ℝ)| =(j:ℝ)-3:=by
        rw [← Int.cast_abs,this]; push_cast; ring
      rw [habs]
      calc Real.log ((j:ℝ)-3+9)≤Real.log (2*((j:ℝ)+3)) :=
            Real.log_le_log (by linarith) (by linarith)
        _=Real.log 2+Lg:=by rw [Real.log_mul (by norm_num) (by linarith)]
        _≤2*Lg:=by linarith
  have hcountm: ∑ ρ∈Fm,(aD.mult ρ:ℝ)≤6*(A₀*(2*Lg)) :=by
    have h:=pH GW (a:= -(j:ℤ)-4) Fm (fun ρ hρ=>by
      have:=((Rk ρ).mp hρ).2; push_cast; constructor <;> linarith [this.1,this.2])
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ GW.Cv.le)
      (by norm_num))
    · have: |(-(j:ℤ)-4:ℤ)| =(j:ℤ)+4:=by
        rw [abs_of_nonpos (by omega)]; ring
      have habs: |((-(j:ℤ)-4:ℤ) :ℝ)| =(j:ℝ)+4:=by
        rw [← Int.cast_abs,this]; push_cast; ring
      rw [habs]
      calc Real.log ((j:ℝ)+4+9)≤Real.log (((j:ℝ)+3)^2) :=by
            apply Real.log_le_log (by linarith); nlinarith
        _=2*Lg:=by rw [Real.log_pow]; push_cast; ring
  have hcard:(S.card:ℝ)≤24*A₀*Lg:=by
    have h1:S.card≤Fp.card+Fm.card:=
      (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    have h1':(S.card:ℝ)≤Fp.card+Fm.card:=by exact_mod_cast h1
    linarith [wN Fp,wN Fm]
  obtain ⟨R,hR1,hR2,Pz⟩:=Jj S j
  set δ:ℝ:=1/(2*((S.card:ℝ)+1)) with hδ
  have hδpos:0<δ:=by rw [hδ]; positivity
  have YI:1/δ=2*((S.card:ℝ)+1) :=by rw [hδ,one_div_one_div]
  refine ⟨R,hR1,hR2,fun s hs hσ1 hσ2=>?_⟩
  have hR6:(6:ℝ)≤ |R| :=by rw [abs_of_nonneg (by linarith)]; linarith
  have adX:(6:ℝ)≤ |-R| :=by rwa [abs_neg]
  have WQ:Real.log (|R| +3)≤2*Lg:=by
    rw [abs_of_nonneg (by linarith)]
    calc Real.log (R+3)≤Real.log (2*((j:ℝ)+3)) :=Real.log_le_log (by linarith) (by linarith)
      _=Real.log 2+Lg:=by rw [Real.log_mul (by norm_num) (by linarith)]
      _≤2*Lg:=by linarith
  have UN:s∈Metric.closedBall (2+s.im* I) (3/2) :=by
    rw [Metric.mem_closedBall,dist_eq_norm]
    have:s-(2+s.im* I)=((s.re-2:ℝ) :ℂ) :=by
      apply Complex.ext <;> simp
    rw [this,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm,abs_of_nonneg (by linarith)]
    linarith
  have WR: ∀ ρ:ℂ,ρ∈Metric.closedBall (2+s.im* I) (22/25*(91/50))→
      riemannZeta ρ=0→δ≤ ‖s-ρ‖ :=by
    intro ρ hρ hz
    have hnt:=mK (by norm_num) hρ hz
    have him:=wM hρ
    rw [abs_le] at him
    have MY:ρ∈aD.carrier:=by rw [zO]; exact hnt
    refine le_trans ?_ (zX s ρ)
    rcases hs with Kt | Kt
    · 
      have hmem:(⟨ρ,MY⟩:aD.carrier)∈Fp:=by
        rw [Rj]
        refine ⟨MY,?_,?_⟩ <;> rw [Kt] at him <;> nlinarith
      have:ρ.im∈S:=by
        rw [hS,Finset.mem_union]; left
        exact Finset.mem_image.mpr ⟨(⟨ρ,MY⟩:aD.carrier),hmem,rfl⟩
      have:=Pz _ this
      rwa [Kt]
    · have hmem:(⟨ρ,MY⟩:aD.carrier)∈Fm:=by
        rw [Rk]
        refine ⟨MY,?_,?_⟩ <;> rw [Kt] at him <;> nlinarith
      have: -ρ.im∈S:=by
        rw [hS,Finset.mem_union]; right
        exact Finset.mem_image.mpr ⟨(⟨ρ,MY⟩:aD.carrier),hmem,rfl⟩
      have:=Pz _ this
      rw [Kt,show |(-R)-ρ.im| = |R-(-ρ.im)| by rw [← abs_neg]; ring_nf]
      exact this
  have hζ:riemannZeta s≠0:=by
    intro hz
    have h0:=WR s (Metric.closedBall_subset_closedBall (by norm_num) UN) hz
    simp at h0; linarith
  refine ⟨hζ,?_⟩
  have ht6:(6:ℝ)≤ |s.im| :=by rcases hs with h | h <;> rw [h] <;> assumption
  obtain ⟨Z,hZ,Lb,Wh⟩:=hpf s.im ht6
  have aay:=Wh s UN hζ
  have FH:Real.log (|s.im| +3)≤2*Lg:=by
    rcases hs with h | h
    · rw [h]; exact WQ
    · rw [h,abs_neg]; exact WQ
  have FI: ∀ ρ∈Z,ρ∈Metric.closedBall (2+s.im* I) (22/25*(91/50)) ∧ riemannZeta ρ=0:=by
    intro ρ hρ
    have:ρ∈(↑Z:Set ℂ) :=hρ
    rw [hZ] at this
    exact this
  have aaz: ‖∑ ρ∈Z,(analyticOrderNatAt riemannZeta ρ:ℂ)/(s-ρ)‖
      ≤(C*(2*Lg))*(1/δ) :=by
    calc ‖∑ ρ∈Z,(analyticOrderNatAt riemannZeta ρ:ℂ)/(s-ρ)‖
        ≤ ∑ ρ∈Z, ‖(analyticOrderNatAt riemannZeta ρ:ℂ)/(s-ρ)‖ :=norm_sum_le _ _
      _≤ ∑ ρ∈Z,(analyticOrderNatAt riemannZeta ρ:ℝ)*(1/δ) :=by
          refine Finset.sum_le_sum fun ρ hρ=>?_
          obtain ⟨abW,Iv⟩:=FI ρ hρ
          have hd:=WR ρ abW Iv
          have YJ:0< ‖s-ρ‖ :=lt_of_lt_of_le hδpos hd
          rw [norm_div,Complex.norm_natCast,div_eq_mul_one_div]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact one_div_le_one_div_of_le hδpos hd
      _=(∑ ρ∈Z,(analyticOrderNatAt riemannZeta ρ:ℝ))*(1/δ) :=by rw [Finset.sum_mul]
      _≤(C*(2*Lg))*(1/δ) :=by
          refine mul_le_mul_of_nonneg_right (Lb.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left FH hC.le
  have hmain: ‖logDeriv riemannZeta s‖ ≤C*(2*Lg)+(C*(2*Lg))*(1/δ) :=by
    have h1: ‖logDeriv riemannZeta s‖
        ≤ ‖logDeriv riemannZeta s- ∑ ρ∈Z,(analyticOrderNatAt riemannZeta ρ:ℂ)/(s-ρ)‖
          + ‖∑ ρ∈Z,(analyticOrderNatAt riemannZeta ρ:ℂ)/(s-ρ)‖ :=norm_le_norm_sub_add _ _
    have h2:=aay.trans (mul_le_mul_of_nonneg_left FH hC.le)
    linarith [aaz]
  refine hmain.trans ?_
  rw [YI]
  have hc:=hcard
  have hA:=GW.Cv.le
  have:C*(2*Lg)+C*(2*Lg)*(2*((S.card:ℝ)+1))
      =2*C*Lg*(2*(S.card:ℝ)+3) :=by ring
  rw [this]
  have hn:2*(S.card:ℝ)+3≤(48*A₀+3)*Lg:=by nlinarith
  calc 2*C*Lg*(2*(S.card:ℝ)+3)≤2*C*Lg*((48*A₀+3)*Lg) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
    _=2*C*(48*A₀+3)*Real.log ((j:ℝ)+3)^2:=by rw [hLg]; ring
theorem PI: ∃ Cg:ℝ,0<Cg ∧ ∃ R:ℕ→ℝ, ∀ j:ℕ,
    (j:ℝ)+7≤R j ∧ R j≤(j:ℝ)+8 ∧
    ∀ s:ℂ,(s.im=R j ∨ s.im= -R j)→1/2≤ s.re→s.re≤2→
      riemannZeta s≠0 ∧ ‖logDeriv riemannZeta s‖ ≤Cg*(Real.log ((j:ℝ)+10))^2:=by
  obtain ⟨C,hC,h⟩:=KZ
  have hex: ∀ j:ℕ, ∃ R:ℝ,((j+7:ℕ) :ℝ)≤R ∧ R≤((j+7:ℕ) :ℝ)+1 ∧
      ∀ s:ℂ,(s.im=R ∨ s.im= -R)→1/2≤ s.re→s.re≤2→
        riemannZeta s≠0 ∧ ‖logDeriv riemannZeta s‖ ≤C*(Real.log (((j+7:ℕ) :ℝ)+3))^2:=
    fun j=>h (j+7) (by omega)
  refine ⟨C,hC,fun j=>(hex j).choose,fun j=>?_⟩
  dsimp only
  obtain ⟨hs1,hs2,hs3⟩:=(hex j).choose_spec
  have e:((j+7:ℕ) :ℝ)=(j:ℝ)+7:=by push_cast; ring
  refine ⟨?_,?_,?_⟩
  · calc (j:ℝ)+7=((j+7:ℕ) :ℝ) :=e.symm
      _≤_:=hs1
  · exact hs2.trans (by rw [e]; linarith)
  · intro s him h1 h2
    have e3:Real.log (((j+7:ℕ) :ℝ)+3)=Real.log ((j:ℝ)+10) :=by rw [e]; ring_nf
    obtain ⟨h3,h4⟩:=hs3 s him h1 h2
    exact ⟨h3,by rwa [e3] at h4⟩
end bR
end Zeta23
end
end

-- Zeta23.bR.acH
section
noncomputable section
namespace Zeta23
namespace bR
open Complex Topology Filter Set
end bR
end Zeta23
end
end

-- Zeta23.bR.abX
section
noncomputable section
namespace Zeta23
namespace bR
open Complex Topology Filter Set MeasureTheory
open scoped ArithmeticFunction
section UO
end UO
section Heights
theorem lA {c:ℝ} (hc1:1<c) (hc2:c≤3/2) {R:ℝ}
    (hζ: ∀ s:ℂ,(s.im=R ∨ s.im= -R)→1/2≤ s.re→s.re≤2→ riemannZeta s≠0) :
    ∀ s:ℂ,(s.im=R ∨ s.im= -R)→1-c≤ s.re→s.re≤c→completedRiemannZeta s≠0:=by
  have aux: ∀ s:ℂ,(s.im=R ∨ s.im= -R)→1/2≤ s.re→s.re≤2→
      completedRiemannZeta s≠0:=by
    intro s him h1 h2 h0
    rcases lt_or_ge s.re 1 with hlt | hge
    · have hnt:=((uW (by linarith) hlt).1).mp h0
      exact hζ s him h1 h2 hnt.1
    · exact Zeta23.dQ.dN hge h0
  intro s him h1 h2
  rcases le_or_gt (1/2:ℝ) s.re with hre | hre
  · exact aux s him hre (by linarith)
  · 
    have e:completedRiemannZeta s=completedRiemannZeta (1-s) :=
      (completedRiemannZeta_one_sub s).symm
    rw [e]
    apply aux (1-s)
    · rcases him with h | h
      · right; simp [h]
      · left; simp [h]
    · simp; linarith
    · simp; linarith
end Heights
section UQ
variable {k:ℝ→ℂ}
end UQ
end bR
end Zeta23
end
end

-- Zeta23.bR.Horizontal
section
noncomputable section
namespace Zeta23
namespace bR
open Complex Topology Filter Set MeasureTheory
end bR
end Zeta23
end
end

-- Zeta23.bR.YK
section
noncomputable section
namespace Zeta23
namespace bR
open Complex Topology Filter Set
end bR
end Zeta23
end
end

-- Zeta23.bR.Wk
section
noncomputable section
namespace Zeta23
namespace bR
open Complex Topology Filter Set MeasureTheory
end bR
end Zeta23
end
end

-- Zeta23.bR.Main
section
noncomputable section
namespace Zeta23
namespace bR
open Complex MeasureTheory
open scoped ArithmeticFunction
end bR
end Zeta23
end
end

-- Zeta23.cE.pD
section
open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace Zeta23
namespace cE
end cE
end Zeta23
end
end

-- Zeta23.dQ.YL
section
open Complex
noncomputable section
namespace Zeta23
namespace dQ
end dQ
end Zeta23
end
end

-- Zeta23.dQ.ZE
section
open Complex Set Metric
noncomputable section
namespace Zeta23.dQ
end Zeta23.dQ
end
end

-- Zeta23.dQ.abY
section
open Complex Set MeasureTheory Real intervalIntegral
noncomputable section
namespace Zeta23
namespace dQ
section Variation
variable {T:ℝ}
end Variation
end dQ
end Zeta23
end
end

-- Zeta23.dQ.YM
section
noncomputable section
namespace Zeta23
end Zeta23
end
end

-- Zeta23.dQ.abZ
section
open Complex MeasureTheory
noncomputable section
namespace Zeta23.dQ
end Zeta23.dQ
end
end

-- Zeta23.dQ.Statement
section
noncomputable section
namespace Zeta23.dQ
end Zeta23.dQ
end
end

-- Zeta23.XP
section
noncomputable section
open Filter Topology Real
namespace Zeta23
end Zeta23
end
end

-- Zeta23.Assembly
section
noncomputable section
open Matrix Finset dS
open scoped ComplexOrder
namespace Zeta23
namespace Assembly
section QJ
variable {𝕜:Type*} [RCLike 𝕜]
variable {n:Type*} [Fintype n] [DecidableEq n]
end QJ
section Frob
open scoped Matrix.Norms.Frobenius
variable {𝕜:Type*} [RCLike 𝕜]
variable {n:Type*} [Fintype n]
end Frob
section PO
variable {𝕜:Type*} [RCLike 𝕜]
variable {n:Type*} [Fintype n] [DecidableEq n]
end PO
section HF
open Real
end HF
section YN
end YN
section Units
open Complex
variable {m:Type*} [Fintype m]
variable (T:ℝ)
end Units
section QK
end QK
section Asymptotic
open Filter Asymptotics Topology
end Asymptotic
section Growth
open Filter Asymptotics Topology Real
end Growth
section Windows
open Set
variable (Z:bT)
variable (T:ℝ)
variable {T}
end Windows
section MZ
variable (Z:bT) (T:ℝ)
variable {Z P T}
end MZ
section Main
open Filter Asymptotics Topology
end Main
section YO
open Filter Asymptotics Topology
variable {m:Type*} [Fintype m]
end YO
section ace
open Filter Topology Real
end ace
end Assembly
end Zeta23
end
end

-- Zeta23.cE.pD.lB
section
open scoped BigOperators ComplexConjugate
open Complex MeasureTheory Set Filter Topology Asymptotics
noncomputable section
namespace Zeta23
namespace cE
namespace lB
theorem qd {f g:ℂ→ℂ} {ρ:ℂ} (hf:AnalyticAt ℂ f ρ)
    (hord:analyticOrderAt f ρ≠ ⊤) (hg:AnalyticAt ℂ g ρ) :
    ((fun s=>g s*logDeriv f s)-fun s=>(analyticOrderNatAt f ρ:ℂ)*g ρ/(s-ρ))
      =O[𝓝[≠] ρ] (1:ℂ→ℂ) :=by
  obtain ⟨h,hh,hh0,hfh⟩:=hf.analyticOrderAt_ne_top.mp hord
  have aaA: ∀ᶠ s in 𝓝 ρ,h s≠0:=hh.continuousAt.eventually_ne hh0
  have h2: ∀ᶠ s in 𝓝 ρ,f =ᶠ[𝓝 s] (fun s=>(s-ρ)^analyticOrderNatAt f ρ•h s) :=
    hfh.eventually_nhds
  have h3: ∀ᶠ s in 𝓝 ρ,AnalyticAt ℂ h s:=hh.eventually_analyticAt
  have hexp: ∀ᶠ s in 𝓝[≠] ρ,
      (analyticOrderNatAt f ρ:ℂ)*((g s-g ρ)/(s-ρ))+g s*logDeriv h s
        =((fun s=>g s*logDeriv f s)-fun s=>
            (analyticOrderNatAt f ρ:ℂ)*g ρ/(s-ρ)) s:=by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds h2,
      mem_nhdsWithin_of_mem_nhds aaA,mem_nhdsWithin_of_mem_nhds h3]
      with s hs hfs hhs acf
    have YJ:s-ρ≠0:=sub_ne_zero.mpr (by simpa using hs)
    have hld:logDeriv f s=(analyticOrderNatAt f ρ:ℂ)/(s-ρ)+logDeriv h s:=by
      have e1:logDeriv f s=logDeriv (fun s=>(s-ρ)^analyticOrderNatAt f ρ*h s) s:=by
        simp only [logDeriv_apply,hfs.deriv_eq,hfs.self_of_nhds,smul_eq_mul]
      rw [e1,logDeriv_mul (f:=fun s:ℂ=>(s-ρ)^analyticOrderNatAt f ρ) (g:=h) s
        (pow_ne_zero _ YJ) hhs (by fun_prop) acf.differentiableAt]
      have e2:logDeriv (fun s:ℂ=>(s-ρ)^analyticOrderNatAt f ρ) s
          =(analyticOrderNatAt f ρ:ℂ)/(s-ρ) :=by
        rw [show (fun s:ℂ=>(s-ρ)^analyticOrderNatAt f ρ)
            =(fun x:ℂ=>x^analyticOrderNatAt f ρ)∘(fun s=>s-ρ) from rfl,
          logDeriv_comp (by fun_prop) (by fun_prop),logDeriv_pow]
        simp
      rw [e2]
    simp only [Pi.sub_apply,hld]
    ring
  have hslope:Tendsto (fun s=>(g s-g ρ)/(s-ρ)) (𝓝[≠] ρ) (𝓝 (deriv g ρ)) :=by
    have:=hasDerivAt_iff_tendsto_slope.mp hg.differentiableAt.hasDerivAt
    simpa only [slope_fun_def_field] using this
  have hcont:Tendsto (fun s=>g s*logDeriv h s) (𝓝[≠] ρ) (𝓝 (g ρ*logDeriv h ρ)) :=by
    have:ContinuousAt (fun s=>g s*logDeriv h s) ρ:=by
      show ContinuousAt (fun s=>g s*(deriv h s/h s)) ρ
      exact hg.continuousAt.mul (hh.deriv.continuousAt.div hh.continuousAt hh0)
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hO:(fun s=>(analyticOrderNatAt f ρ:ℂ)*((g s-g ρ)/(s-ρ))
      +g s*logDeriv h s) =O[𝓝[≠] ρ] (1:ℂ→ℂ) :=
    ((hslope.const_mul (analyticOrderNatAt f ρ:ℂ)).add hcont).isBigO_one ℂ
  exact hO.congr' hexp EventuallyEq.rfl
theorem sI {F g:ℂ→ℂ} {q r:ℂ} (hF:DifferentiableAt ℂ F q)
    (hg:(g-fun s=>r/(s-q)) =O[𝓝[≠] q] (1:ℂ→ℂ)) :
    ((fun s=>g s*F s)-fun s=>r*F q/(s-q)) =O[𝓝[≠] q] (1:ℂ→ℂ) :=by
  have hFc:Tendsto F (𝓝[≠] q) (𝓝 (F q)) :=hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hFO:F =O[𝓝[≠] q] (1:ℂ→ℂ) :=hFc.isBigO_one ℂ
  have hslope:Tendsto (fun s=>(F s-F q)/(s-q)) (𝓝[≠] q) (𝓝 (deriv F q)) :=by
    have:=hasDerivAt_iff_tendsto_slope.mp hF.hasDerivAt
    simpa only [slope_fun_def_field] using this
  have h1:(fun s=>(g-fun s=>r/(s-q)) s*F s) =O[𝓝[≠] q] (1:ℂ→ℂ) :=by
    have:=hg.mul hFO
    simpa only [Pi.one_apply,mul_one,Pi.one_def] using this
  have h2:(fun s=>r*((F s-F q)/(s-q))) =O[𝓝[≠] q] (1:ℂ→ℂ) :=
    (hslope.const_mul r).isBigO_one ℂ
  refine (h1.add h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsq:s-q≠0:=sub_ne_zero.mpr hs
  simp only [Pi.sub_apply]
  field_simp
  ring
theorem jA {f g:ℂ→ℂ} {z w:ℂ} (hre:z.re≤w.re)
    (him:z.im≤w.im) (Z Q:Finset ℂ) (UR:Disjoint Z Q)
    (Om: ∀ q∈Q,Rectangle z w∈𝓝 q)
    (hf:AnalyticOnNhd ℂ f (Rectangle z w))
    (hg: ∀ p∈Rectangle z w \ (Q:Set ℂ),AnalyticAt ℂ g p)
    (vV: ∀ p∈aO z w,f p≠0)
    (hZ: ∀ p∈Rectangle z w,f p=0↔p∈Z) (FJ:(Z:Set ℂ)⊆Rectangle z w)
    (r:ℂ→ℂ) (SD: ∀ q∈Q,(g-fun s=>r q/(s-q)) =O[𝓝[≠] q] (1:ℂ→ℂ)) :
    aW (fun s=>g s*logDeriv f s) z w
      = ∑ ρ∈Z,(analyticOrderNatAt f ρ:ℂ)*g ρ+ ∑ q∈Q,r q*logDeriv f q:=by
  classical
  have PS: ∀ ρ∈Z,ρ∉Q:=fun ρ hρ acg=>Finset.disjoint_left.mp UR hρ acg
  have YP: ∀ q∈Q,q∉Z:=fun q hq YQ=>Finset.disjoint_left.mp UR YQ hq
  have hzB:z∈aO z w:=Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc,rfl⟩))
  have hz0:f z≠0:=vV z hzB
  have hzR:z∈Rectangle z w:=cO z w hzB
  have hpre:IsPreconnected (Rectangle z w) :=by
    rw [rectangle_eq_convexHull]; exact (convex_convexHull ℝ _).isPreconnected
  have aaB:analyticOrderAt f z≠ ⊤ :=by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hz0)]
    exact ENat.zero_ne_top
  have hord: ∀ ρ∈Z,analyticOrderAt f ρ≠ ⊤ :=fun ρ hρ=>
    hf.analyticOrderAt_ne_top_of_isPreconnected hpre hzR (FJ hρ) aaB
  have aaC: ∀ ρ∈Z,Rectangle z w∈𝓝 ρ:=by
    intro ρ hρ
    have YS:ρ∈Rectangle z w:=FJ hρ
    have YV:ρ∉aO z w:=fun h=>vV ρ h ((hZ ρ YS).mpr hρ)
    obtain ⟨h1,h2⟩:=YS
    have h1':z.re≤ρ.re ∧ ρ.re≤w.re:=by simpa [uIcc_of_le hre] using h1
    have h2':z.im≤ρ.im ∧ ρ.im≤w.im:=by simpa [uIcc_of_le him] using h2
    simp only [aO,mem_union,mem_reProdIm,mem_singleton_iff,not_or] at YV
    obtain ⟨⟨⟨hb1,hb2⟩,hb3⟩,hb4⟩:=YV
    rw [eo,mem_reProdIm,uIoo_of_le hre,uIoo_of_le him]
    refine ⟨⟨lt_of_le_of_ne h1'.1 (fun h=>hb2 ⟨h.symm,h2⟩),
      lt_of_le_of_ne h1'.2 (fun h=>hb4 ⟨h,h2⟩)⟩,
      ⟨lt_of_le_of_ne h2'.1 (fun h=>hb1 ⟨h1,h.symm⟩),
      lt_of_le_of_ne h2'.2 (fun h=>hb3 ⟨h1,h⟩)⟩⟩
  let A:ℂ→ℂ:=fun p=>if p∈Q then r p*logDeriv f p else (analyticOrderNatAt f p:ℂ)*g p
  have hint: ∀ p∈Z ∪ Q,Rectangle z w∈𝓝 p:=by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    exacts [aaC p hp,Om p hp]
  have key:=Zeta23.Analytic.Bd (f:=fun s=>g s*logDeriv f s) hre him
    (Z ∪ Q) A hint ?holo ?near
  · rw [key,Finset.sum_union UR]
    have Lb: ∑ p∈Z,A p= ∑ ρ∈Z,(analyticOrderNatAt f ρ:ℂ)*g ρ:=
      Finset.sum_congr rfl (fun p hp=>by simp [A,PS p hp])
    have SH: ∑ p∈Q,A p= ∑ q∈Q,r q*logDeriv f q:=
      Finset.sum_congr rfl (fun p hp=>by simp [A,hp])
    rw [Lb,SH]
  case holo=>
    intro s hs
    have hsQ:s∉Q:=fun h=>hs.2 (by simp [h])
    have hsZ:s∉Z:=fun h=>hs.2 (by simp [h])
    have hfs:f s≠0:=fun h=>hsZ ((hZ s hs.1).mp h)
    have hfa:=hf s hs.1
    have hga:=hg s ⟨hs.1,by simpa using hsQ⟩
    apply DifferentiableAt.differentiableWithinAt
    show DifferentiableAt ℂ (fun s=>g s*(deriv f s/f s)) s
    exact hga.differentiableAt.mul (hfa.deriv.differentiableAt.div hfa.differentiableAt hfs)
  case near=>
    intro p hp
    rcases Finset.mem_union.mp hp with hρ | hq
    · have hA:A p=(analyticOrderNatAt f p:ℂ)*g p:=by simp [A,PS p hρ]
      have hga:=hg p ⟨FJ hρ,by simpa using PS p hρ⟩
      rw [hA]
      exact qd (hf p (FJ hρ)) (hord p hρ) hga
    · have hA:A p=r p*logDeriv f p:=by simp [A,hq]
      have hpR:p∈Rectangle z w:=mem_of_mem_nhds (Om p hq)
      have hfp:f p≠0:=fun h=>YP p hq ((hZ p hpR).mp h)
      have hfa:=hf p hpR
      have hF:DifferentiableAt ℂ (logDeriv f) p:=by
        have:logDeriv f=fun s=>deriv f s/f s:=by funext s; exact logDeriv_apply f s
        rw [this]
        exact hfa.deriv.differentiableAt.div hfa.differentiableAt hfp
      rw [hA]
      exact sI (F:=logDeriv f) hF (SD p hq)
theorem vH {f:ℂ→ℂ} {z w:ℂ} (hre:z.re≤w.re) (him:z.im≤w.im)
    {M:ℝ} (hf: ∀ p∈aO z w, ‖f p‖ ≤M) :
    ‖aV f z w‖ ≤M*(2*(w.re-z.re)+2*(w.im-z.im)) :=by
  have hH: ∀ y:ℝ,(∀ x∈Set.uIcc z.re w.re,((x:ℂ)+y* I)∈aO z w)→
      ‖dK f z.re w.re y‖ ≤M*(w.re-z.re) :=by
    intro y hy
    have:=intervalIntegral.norm_integral_le_of_norm_le_const (a:=z.re) (b:=w.re) (C:=M)
      (f:=fun x:ℝ=>f (x+y* I)) (fun x hx=>hf _ (hy x (Set.uIoc_subset_uIcc hx)))
    rw [abs_of_nonneg (by linarith)] at this
    exact this
  have hV: ∀ x:ℝ,(∀ y∈Set.uIcc z.im w.im,((x:ℂ)+y* I)∈aO z w)→
      ‖eW f x z.im w.im‖ ≤M*(w.im-z.im) :=by
    intro x hx
    have:=intervalIntegral.norm_integral_le_of_norm_le_const (a:=z.im) (b:=w.im) (C:=M)
      (f:=fun y:ℝ=>f (x+y* I)) (fun y hy=>hf _ (hx y (Set.uIoc_subset_uIcc hy)))
    rw [abs_of_nonneg (by linarith)] at this
    rw [eW,norm_smul,Complex.norm_I,one_mul]
    exact this
  have h1:=hH z.im (fun x hx=>jf z w hx)
  have h2:=hH w.im (fun x hx=>iO z w hx)
  have h3:=hV w.re (fun y hy=>iJ z w hy)
  have h4:=hV z.re (fun y hy=>je z w hy)
  unfold aV
  calc ‖dK f z.re w.re z.im-dK f z.re w.re w.im
        +eW f w.re z.im w.im-eW f z.re z.im w.im‖
      ≤ ‖dK f z.re w.re z.im‖ + ‖dK f z.re w.re w.im‖
        + ‖eW f w.re z.im w.im‖ + ‖eW f z.re z.im w.im‖ :=by
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl
    _≤M*(2*(w.re-z.re)+2*(w.im-z.im)) :=by linarith
theorem dY (s:ℂ) :xi s=0↔aE s:=by
  by_cases h0:s=0
  · subst h0
    have:xi 0=1/2:=by simp [xi]
    rw [this]
    constructor
    · intro h; norm_num at h
    · rintro ⟨_,h,_⟩; simp at h
  by_cases h1:s=1
  · subst h1
    have:xi 1=1/2:=by simp [xi]
    rw [this]
    constructor
    · intro h; norm_num at h
    · rintro ⟨_,_,h⟩; simp at h
  rw [RH s h0 h1,mul_eq_zero, ← Zeta23.dQ.iz]
  have:s*(s-1)/2≠0:=div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) two_ne_zero
  simp [this]
theorem Lc {ρ:ℂ} (h0:ρ≠0) (h1:ρ≠1) :
    xi =ᶠ[𝓝 ρ] fun s=>s*(s-1)/2*completedRiemannZeta s:=by
  filter_upwards [isOpen_compl_singleton.mem_nhds h0,isOpen_compl_singleton.mem_nhds h1]
    with s hs0 hs1
  exact RH s (by simpa using hs0) (by simpa using hs1)
theorem Br {ρ:ℂ} (hρ:aE ρ) :
    analyticOrderNatAt xi ρ=aP ρ:=by
  have h0:ρ≠0:=fun h=>by have:=hρ.2.1; simp [h] at this
  have h1:ρ≠1:=fun h=>by have:=hρ.2.2; simp [h] at this
  have hev:=Lc h0 h1
  have hΛ:=Zeta23.dQ.iW h0 h1
  have hp:AnalyticAt ℂ (fun s:ℂ=>s*(s-1)/2) ρ:=
    (by fun_prop:Differentiable ℂ (fun s:ℂ=>s*(s-1)/2)).analyticAt ρ
  have hp0:analyticOrderAt (fun s:ℂ=>s*(s-1)/2) ρ=0:=
    hp.analyticOrderAt_eq_zero.mpr (div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) two_ne_zero)
  have hmul:=analyticOrderAt_mul hp hΛ
  rw [show ((fun s:ℂ=>s*(s-1)/2)*completedRiemannZeta)
      =fun s=>s*(s-1)/2*completedRiemannZeta s from rfl] at hmul
  rw [← Zeta23.dQ.jX hρ.2.1 h1]
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr hev,hmul,hp0,zero_add]
theorem kF (s:ℂ) :logDeriv xi (1-s)= -logDeriv xi s:=by
  have hcomp:xi=xi∘(fun u:ℂ=>1-u) :=by
    funext u; simp [Kq]
  have hd:DifferentiableAt ℂ xi (1-s) :=fO _
  have hg:DifferentiableAt ℂ (fun u:ℂ=>1-u) s:=
    (differentiableAt_const _).sub differentiableAt_id
  have key:=logDeriv_comp (x:=s) hd hg
  rw [← hcomp] at key
  have hderiv:deriv (fun u:ℂ=>1-u) s= -1:=by
    rw [deriv_const_sub,deriv_id'']
  rw [key,hderiv]
  ring
theorem Jm (s:ℂ) :logDeriv xi (conj s)=conj (logDeriv xi s) :=by
  rw [logDeriv_apply,logDeriv_apply,show deriv xi=lJ from rfl,Pq,MS,
    ← map_div₀]
theorem Ld (s:ℂ) :xi (reflect s)=conj (xi s) :=by
  show xi (1-conj s)=_
  rw [Kq,MS]
theorem DK (s:ℂ) :logDeriv xi (reflect s)= -conj (logDeriv xi s) :=by
  show logDeriv xi (1-conj s)=_
  rw [kF,Jm]
theorem wO {s:ℂ} (hs:0<s.re) :
    DifferentiableAt ℂ Complex.digamma s:=by
  have hzero: ∀ m:ℕ,s≠ -(m:ℂ) :=by
    intro m h
    rw [h] at hs
    simp only [Complex.neg_re,Complex.natCast_re] at hs
    nlinarith [Nat.cast_nonneg (α:=ℝ) m]
  have hopen:IsOpen {w:ℂ | 0<w.re} :=isOpen_lt continuous_const Complex.continuous_re
  have yZ:AnalyticAt ℂ Complex.Gamma s:=by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hopen.mem_nhds hs] with w hw
    refine Complex.differentiableAt_Gamma w fun m=>?_
    intro h
    rw [h] at hw
    simp only [Complex.neg_re,Complex.natCast_re] at hw
    nlinarith [Nat.cast_nonneg (α:=ℝ) m]
  have Fw:Complex.Gamma s≠0:=Complex.Gamma_ne_zero hzero
  have Sm:AnalyticAt ℂ Complex.digamma s:=by
    have h1:AnalyticAt ℂ (deriv Complex.Gamma) s:=yZ.deriv
    have h2:=h1.div yZ Fw
    exact h2.congr (by
      filter_upwards with w
      rw [Complex.digamma_def,logDeriv_apply]
      rfl)
  exact Sm.differentiableAt
theorem Lh {z:ℂ} (hz:0<z.re) (n:ℕ) :
    Complex.digamma (z+n)=Complex.digamma z+ ∑ k∈Finset.range n,1/(z+k) :=by
  induction n with
  | zero=>simp
  | succ n ih=>
    have hne: ∀ m:ℕ,z+n≠ -(m:ℂ) :=by
      intro m h
      have:=congrArg Complex.re h
      simp only [Complex.add_re,Complex.natCast_re,Complex.neg_re] at this
      linarith [Nat.cast_nonneg (α:=ℝ) m,Nat.cast_nonneg (α:=ℝ) n]
    rw [Nat.cast_succ, ← add_assoc,Complex.digamma_apply_add_one _ hne,ih,Finset.sum_range_succ,
      one_div]
    ring
theorem Lj: ∃ C:ℝ,0<C ∧ ∀ z:ℂ,1/2≤z.re→
    ‖Complex.digamma z‖ ≤C*Real.log (2+ ‖z‖) :=by
  have hK:IsCompact (Set.Icc (1/2:ℝ) (3/2) ×ℂ Set.Icc (-(1/2) :ℝ) (1/2)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcont:ContinuousOn Complex.digamma (Set.Icc (1/2:ℝ) (3/2) ×ℂ Set.Icc (-(1/2) :ℝ) (1/2)) :=by
    intro s hs
    have:1/2≤ s.re:=(Complex.mem_reProdIm.mp hs).1.1
    exact (wO (by linarith)).continuousAt.continuousWithinAt
  obtain ⟨M,hM⟩:=hK.exists_bound_of_continuousOn hcont
  have hM0:0≤M:=le_trans (norm_nonneg _) (hM 1 (by
    rw [Complex.mem_reProdIm,Complex.one_re,Complex.one_im,Set.mem_Icc,Set.mem_Icc]; norm_num))
  have zC:0<Real.log 2:=Real.log_pos one_lt_two
  have adB:0≤Real.log 4:=Real.log_nonneg (by norm_num)
  set K₀:ℝ:=14+Real.pi+Real.log 4 with hK₀
  have YC:0≤K₀:=by have:=Real.pi_pos; rw [hK₀]; linarith
  refine ⟨(K₀+M+4)/Real.log 2+2,by positivity,fun z hz=>?_⟩
  have hL:Real.log 2≤Real.log (2+ ‖z‖) :=
    Real.log_le_log two_pos (by linarith [norm_nonneg z])
  have hL0:0<Real.log (2+ ‖z‖) :=zC.trans_le hL
  suffices h: ‖Complex.digamma z‖ ≤2*Real.log (2+ ‖z‖)+(K₀+M+4) by
    calc ‖Complex.digamma z‖ ≤2*Real.log (2+ ‖z‖)+(K₀+M+4) :=h
      _=2*Real.log (2+ ‖z‖)+((K₀+M+4)/Real.log 2)*Real.log 2:=by field_simp
      _≤2*Real.log (2+ ‖z‖)+((K₀+M+4)/Real.log 2)*Real.log (2+ ‖z‖) :=by
          have:0≤(K₀+M+4)/Real.log 2:=by positivity
          nlinarith
      _=((K₀+M+4)/Real.log 2+2)*Real.log (2+ ‖z‖) :=by ring
  have aaD:0<z.re:=by linarith
  have ach:1/2≤ ‖z‖ :=le_trans hz (le_trans (le_abs_self _) (Complex.abs_re_le_norm z))
  have UZ:0< ‖z‖ :=by linarith
  rcases le_or_gt (1/2:ℝ) |z.im| with him | him
  · 
    have hst:=Zeta23.kZ.oB (w:=z) aaD him
    have UL: ‖Complex.log z‖ ≤ |Real.log ‖z‖| +Real.pi:=by
      calc ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _≤ |Real.log ‖z‖| +Real.pi:=by
            rw [Complex.log_re,Complex.log_im]
            have:=Complex.abs_arg_le_pi z
            linarith
    have Pv: |Real.log ‖z‖| ≤Real.log 4+Real.log (2+ ‖z‖) :=by
      rcases le_or_gt (Real.log ‖z‖) 0 with hneg | hpos
      · have h1:Real.log (1/4:ℝ)≤Real.log ‖z‖ :=Real.log_le_log (by norm_num) (by linarith)
        have h2:Real.log (1/4:ℝ)= -Real.log 4:=by
          rw [show (1/4:ℝ)=4⁻¹ by norm_num,Real.log_inv]
        rw [abs_of_nonpos hneg]
        linarith
      · rw [abs_of_pos hpos]
        have h1:Real.log ‖z‖ ≤Real.log (2+ ‖z‖) :=Real.log_le_log UZ (by linarith)
        linarith
    have hinv: ‖(1/2:ℂ)/z‖ ≤2:=by
      rw [norm_div,div_le_iff₀ UZ]
      have h1: ‖(1/2:ℂ)‖ =1/2:=by
        rw [show (1/2:ℂ)=((1/2:ℝ) :ℂ) by norm_num,Complex.norm_real,
          Real.norm_eq_abs,abs_of_pos (by norm_num)]
      rw [h1]; linarith
    have Wj:3/z.im^2≤12:=by
      have h1:(1/4:ℝ)≤z.im^2:=by nlinarith [abs_nonneg z.im,sq_abs z.im]
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith
    have hsplit: ‖Complex.digamma z‖
        ≤ ‖Complex.digamma z-Complex.log z+(1/2:ℂ)/z‖ + ‖Complex.log z‖
          + ‖(1/2:ℂ)/z‖ :=by
      have h2:Complex.digamma z=(Complex.digamma z-Complex.log z+(1/2:ℂ)/z)
          +Complex.log z-(1/2:ℂ)/z:=by ring
      calc ‖Complex.digamma z‖
          = ‖(Complex.digamma z-Complex.log z+(1/2:ℂ)/z)+Complex.log z
              -(1/2:ℂ)/z‖ :=by rw [← h2]
        _≤ ‖(Complex.digamma z-Complex.log z+(1/2:ℂ)/z)+Complex.log z‖
            + ‖(1/2:ℂ)/z‖ :=norm_sub_le _ _
        _≤_:=by
            have:=norm_add_le (Complex.digamma z-Complex.log z+(1/2:ℂ)/z) (Complex.log z)
            linarith
    rw [hK₀]
    linarith [hL0]
  · 
    set n:ℕ:= ⌊z.re-1/2⌋₊ with hn
    set z₀:ℂ:=z-n with hz₀
    have hfl:(n:ℝ)≤z.re-1/2:=Nat.floor_le (by linarith)
    have adY:z.re-1/2<n+1:=Nat.lt_floor_add_one (z.re-1/2)
    have Rm:z₀.re=z.re-n:=by simp [hz₀]
    have Xy:z₀.im=z.im:=by simp [hz₀]
    have Vc:z₀∈Set.Icc (1/2:ℝ) (3/2) ×ℂ Set.Icc (-(1/2) :ℝ) (1/2) :=by
      rw [Complex.mem_reProdIm,Rm,Xy,Set.mem_Icc,Set.mem_Icc]
      have:=abs_lt.mp him
      refine ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩
    have Wn:0<z₀.re:=by rw [Rm]; linarith
    have hzeq:z=z₀+n:=by simp [hz₀]
    have hψ:Complex.digamma z=Complex.digamma z₀+ ∑ k∈Finset.range n,1/(z₀+k) :=by
      rw [hzeq]; exact Lh Wn n
    have hterm: ∀ k∈Finset.range n, ‖1/(z₀+(k:ℂ))‖ ≤2*(1/((k:ℝ)+1)) :=by
      intro k _
      have hre:(z₀+(k:ℂ)).re=z₀.re+k:=by simp
      have hpos:0<z₀.re+k:=by positivity
      have hnk:z₀.re+k≤ ‖z₀+(k:ℂ)‖ :=by
        calc z₀.re+k= |(z₀+(k:ℂ)).re| :=by rw [hre,abs_of_pos hpos]
          _≤ ‖z₀+(k:ℂ)‖ :=Complex.abs_re_le_norm _
      rw [norm_div,norm_one]
      calc 1/ ‖z₀+(k:ℂ)‖ ≤1/(z₀.re+k) :=one_div_le_one_div_of_le hpos hnk
        _≤1/(1/2+k) :=one_div_le_one_div_of_le (by positivity) (by linarith [Vc.1.1])
        _≤2*(1/((k:ℝ)+1)) :=by
            rw [div_le_iff₀ (by positivity)]
            have hk0:(0:ℝ)≤k:=Nat.cast_nonneg k
            field_simp
            nlinarith
    have adC:Real.log n≤Real.log (2+ ‖z‖) :=by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0,Nat.cast_zero,Real.log_zero]; exact hL0.le
      · apply Real.log_le_log (by exact_mod_cast hpos)
        have:z.re≤ ‖z‖ :=le_trans (le_abs_self _) (Complex.abs_re_le_norm z)
        linarith
    have hsum: ‖∑ k∈Finset.range n,1/(z₀+(k:ℂ))‖ ≤2*(1+Real.log (2+ ‖z‖)) :=by
      calc ‖∑ k∈Finset.range n,1/(z₀+(k:ℂ))‖
          ≤ ∑ k∈Finset.range n, ‖1/(z₀+(k:ℂ))‖ :=norm_sum_le _ _
        _≤ ∑ k∈Finset.range n,2*(1/((k:ℝ)+1)) :=Finset.sum_le_sum hterm
        _=2*((harmonic n:ℚ) :ℝ) :=by
            rw [← Finset.mul_sum,Zeta23.nT.oA]
        _≤2*(1+Real.log n) :=by
            have:=harmonic_le_one_add_log n
            linarith
        _≤2*(1+Real.log (2+ ‖z‖)) :=by linarith
    calc ‖Complex.digamma z‖ = ‖Complex.digamma z₀+ ∑ k∈Finset.range n,1/(z₀+(k:ℂ))‖ :=by
          rw [hψ]
      _≤ ‖Complex.digamma z₀‖ + ‖∑ k∈Finset.range n,1/(z₀+(k:ℂ))‖ :=norm_add_le _ _
      _≤M+2*(1+Real.log (2+ ‖z‖)) :=add_le_add (hM z₀ Vc) hsum
      _≤2*Real.log (2+ ‖z‖)+(K₀+M+4) :=by linarith
theorem qg: ∃ C:ℝ,0<C ∧ ∀ w:ℂ,1≤w.re→
    ‖logDeriv Complex.Gammaℝ w‖ ≤C*Real.log (2+ ‖w‖) :=by
  obtain ⟨C,hC,hψ⟩:=Lj
  have zC:0<Real.log 2:=Real.log_pos one_lt_two
  have Py:0<Real.log Real.pi:=Real.log_pos (by linarith [Real.pi_gt_three])
  refine ⟨Real.log Real.pi/(2*Real.log 2)+C/2,by positivity,fun w hw=>?_⟩
  have hL:Real.log 2≤Real.log (2+ ‖w‖) :=
    Real.log_le_log two_pos (by linarith [norm_nonneg w])
  rw [Zeta23.dQ.jB (by linarith)]
  have h1: ‖-(Real.log Real.pi:ℂ)/2‖ =Real.log Real.pi/2:=by
    rw [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Py,
      Complex.norm_ofNat]
  have h2: ‖(1/2:ℂ)*Complex.digamma (w/2)‖ ≤C/2*Real.log (2+ ‖w‖) :=by
    rw [norm_mul,show (1/2:ℂ)=((1/2:ℝ) :ℂ) by norm_num,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (by norm_num)]
    have hw2:1/2≤(w/2).re:=by simp; linarith
    have h3:=hψ (w/2) hw2
    have h4:Real.log (2+ ‖w/2‖)≤Real.log (2+ ‖w‖) :=by
      apply Real.log_le_log (by positivity)
      rw [norm_div,Complex.norm_ofNat]
      linarith [norm_nonneg w]
    calc 1/2* ‖Complex.digamma (w/2)‖ ≤1/2*(C*Real.log (2+ ‖w‖)) :=by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact h3.trans (mul_le_mul_of_nonneg_left h4 hC.le)
      _=C/2*Real.log (2+ ‖w‖) :=by ring
  calc ‖-(Real.log Real.pi:ℂ)/2+(1/2:ℂ)*Complex.digamma (w/2)‖
      ≤ ‖-(Real.log Real.pi:ℂ)/2‖ + ‖(1/2:ℂ)*Complex.digamma (w/2)‖ :=norm_add_le _ _
    _≤Real.log Real.pi/2+C/2*Real.log (2+ ‖w‖) :=by rw [h1]; linarith
    _=Real.log Real.pi/(2*Real.log 2)*Real.log 2+C/2*Real.log (2+ ‖w‖) :=by
        field_simp
    _≤Real.log Real.pi/(2*Real.log 2)*Real.log (2+ ‖w‖)+C/2*Real.log (2+ ‖w‖) :=by
        have:0≤Real.log Real.pi/(2*Real.log 2) :=by positivity
        nlinarith
    _=(Real.log Real.pi/(2*Real.log 2)+C/2)*Real.log (2+ ‖w‖) :=by ring
theorem vI: ∃ M:ℝ,0≤M ∧ ∀ w:ℂ,3/2≤w.re→
    ‖logDeriv riemannZeta w‖ ≤M:=by
  set a:ℕ→ℂ:=fun n=>((ArithmeticFunction.vonMangoldt n:ℝ) :ℂ) with ha
  have hsum:Summable (fun n:ℕ=> ‖LSeries.term a ((3/2:ℝ) :ℂ) n‖) :=by
    have h:=ArithmeticFunction.LSeriesSummable_vonMangoldt (s:=((3/2:ℝ) :ℂ))
      (by simp only [Complex.ofReal_re]; norm_num)
    exact summable_norm_iff.mpr h
  refine ⟨∑' n:ℕ, ‖LSeries.term a ((3/2:ℝ) :ℂ) n‖,tsum_nonneg fun _=>norm_nonneg _,
    fun w hw=>?_⟩
  have MW:1<w.re:=by linarith
  have h1:logDeriv riemannZeta w= -LSeries a w:=by
    have h2:=ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div MW
    rw [logDeriv,Pi.div_apply,ha,h2]; ring
  have hle: ∀ n:ℕ, ‖LSeries.term a w n‖ ≤ ‖LSeries.term a ((3/2:ℝ) :ℂ) n‖ :=by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · simp [h0,LSeries.term_zero]
    rw [LSeries.norm_term_eq,LSeries.norm_term_eq]
    simp only [hn.ne',if_false,Complex.ofReal_re]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hw
  have hsum':Summable (fun n:ℕ=> ‖LSeries.term a w n‖) :=
    Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hle hsum
  rw [h1,norm_neg,LSeries]
  calc ‖∑' n,LSeries.term a w n‖ ≤ ∑' n, ‖LSeries.term a w n‖ :=norm_tsum_le_tsum_norm hsum'
    _≤ ∑' n, ‖LSeries.term a ((3/2:ℝ) :ℂ) n‖ :=hsum'.tsum_le_tsum hle hsum
theorem xZ: ∃ C:ℝ,0<C ∧ ∀ w:ℂ,3/2≤w.re→
    ‖logDeriv xi w‖ ≤C*Real.log (2+ ‖w‖) :=by
  obtain ⟨C,hC,hΓ⟩:=qg
  obtain ⟨M,hM0,hζ⟩:=vI
  have zC:0<Real.log 2:=Real.log_pos one_lt_two
  refine ⟨C+(3+M)/Real.log 2,by positivity,fun w hw=>?_⟩
  have hL:Real.log 2≤Real.log (2+ ‖w‖) :=
    Real.log_le_log two_pos (by linarith [norm_nonneg w])
  have hw0:0<w.re:=by linarith
  have hw1:w≠1:=fun h=>by rw [h,Complex.one_re] at hw; norm_num at hw
  have SI:riemannZeta w≠0:=riemannZeta_ne_zero_of_one_le_re (by linarith)
  rw [Bp hw0 hw1 SI,WM]
  have hn1: ‖1/w‖ ≤1:=by
    rw [norm_div,norm_one,div_le_one (by
      linarith [le_trans (le_abs_self _) (Complex.abs_re_le_norm w)])]
    linarith [le_trans (le_abs_self _) (Complex.abs_re_le_norm w)]
  have hn2: ‖1/(w-1)‖ ≤2:=by
    have:1/2≤ ‖w-1‖ :=by
      calc (1/2:ℝ)≤ |(w-1).re| :=by
            rw [Complex.sub_re,Complex.one_re,abs_of_pos (by linarith)]; linarith
        _≤ ‖w-1‖ :=Complex.abs_re_le_norm _
    rw [norm_div,norm_one,div_le_iff₀ (by linarith)]
    linarith
  calc ‖logDeriv Gammaℝ w+1/w+1/(w-1)+logDeriv riemannZeta w‖
      ≤ ‖logDeriv Gammaℝ w‖ + ‖1/w‖ + ‖1/(w-1)‖ + ‖logDeriv riemannZeta w‖ :=by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _≤C*Real.log (2+ ‖w‖)+1+2+M:=by
        linarith [hΓ w (by linarith),hζ w hw]
    _=C*Real.log (2+ ‖w‖)+((3+M)/Real.log 2)*Real.log 2:=by field_simp; ring
    _≤C*Real.log (2+ ‖w‖)+((3+M)/Real.log 2)*Real.log (2+ ‖w‖) :=by
        have:0≤(3+M)/Real.log 2:=by positivity
        nlinarith
    _=(C+(3+M)/Real.log 2)*Real.log (2+ ‖w‖) :=by ring
theorem pI: ∃ C:ℝ,0<C ∧ ∀ (L R:ℝ),1≤L→1≤R→
    (∀ p:ℂ,(p.im=R ∨ p.im= -R)→1/2≤p.re→p.re≤2→
      riemannZeta p≠0 ∧ ‖logDeriv riemannZeta p‖ ≤L)→
    ∀ w:ℂ,(w.im=R ∨ w.im= -R)→ -1/2≤w.re→w.re≤3/2→
      ‖logDeriv xi w‖ ≤C*(L+Real.log (2+R)) :=by
  obtain ⟨CΓ,adZ,hΓ⟩:=Zeta23.bR.vG
  refine ⟨CΓ+3,by positivity,fun L R hL hR vN=>?_⟩
  have aux: ∀ w:ℂ,(w.im=R ∨ w.im= -R)→1/2≤w.re→w.re≤3/2→
      ‖logDeriv xi w‖ ≤(CΓ+3)*(L+Real.log (2+R)) :=by
    intro w him h1 h2
    have habs: |w.im| =R:=by
      rcases him with h | h
      · rw [h,abs_of_pos (by linarith)]
      · rw [h,abs_neg,abs_of_pos (by linarith)]
    have hw0:0<w.re:=by linarith
    have hw1:w≠1:=fun h=>by
      rw [h,Complex.one_im] at habs; rw [← habs] at hR; simp at hR; linarith
    obtain ⟨SI,aea⟩:=vN w him h1 (by linarith)
    rw [Bp hw0 hw1 SI,WM]
    have hnorm:R≤ ‖w‖ :=habs ▸ Complex.abs_im_le_norm w
    have hn1: ‖1/w‖ ≤1:=by
      rw [norm_div,norm_one,div_le_one (by linarith)]; linarith
    have hn2: ‖1/(w-1)‖ ≤1:=by
      have:R≤ ‖w-1‖ :=by
        have:=Complex.abs_im_le_norm (w-1)
        rwa [Complex.sub_im,Complex.one_im,sub_zero,habs] at this
      rw [norm_div,norm_one,div_le_one (by linarith)]; linarith
    have hG: ‖logDeriv Gammaℝ w‖ ≤CΓ*Real.log (2+R) :=by
      have:=hΓ w.re w.im h1 h2
      rwa [Complex.re_add_im,habs] at this
    have Oo:0≤Real.log (2+R) :=Real.log_nonneg (by linarith)
    calc ‖logDeriv Gammaℝ w+1/w+1/(w-1)+logDeriv riemannZeta w‖
        ≤ ‖logDeriv Gammaℝ w‖ + ‖1/w‖ + ‖1/(w-1)‖ + ‖logDeriv riemannZeta w‖ :=by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _≤CΓ*Real.log (2+R)+1+1+L:=by linarith
      _≤(CΓ+3)*(L+Real.log (2+R)) :=by nlinarith
  intro w him h1 h2
  rcases le_or_gt (1/2:ℝ) w.re with hre | hre
  · exact aux w him hre h2
  · 
    have e:logDeriv xi w= -logDeriv xi (1-w) :=by
      rw [← kF (1-w),sub_sub_cancel]
    rw [e,norm_neg]
    apply aux (1-w)
    · rcases him with h | h
      · right; simp [h]
      · left; simp [h]
    · simp; linarith
    · simp; linarith
def zc (R:ℝ) :ℂ:=((1-R:ℝ) :ℂ)+((-R:ℝ) :ℂ)* I
def wc (R:ℝ) :ℂ:=((R:ℝ) :ℂ)+((R:ℝ) :ℂ)* I
@[simp] theorem Cz (R:ℝ) :(zc R).re=1-R:=by simp [zc]
@[simp] theorem CJ (R:ℝ) :(zc R).im= -R:=by simp [zc]
@[simp] theorem CQ (R:ℝ) :(wc R).re=R:=by simp [wc]
@[simp] theorem CX (R:ℝ) :(wc R).im=R:=by simp [wc]
theorem sK: ∃ C:ℝ,0<C ∧ ∀ (L R:ℝ),1≤L→2≤R→
    (∀ p:ℂ,(p.im=R ∨ p.im= -R)→1/2≤p.re→p.re≤2→
      riemannZeta p≠0 ∧ ‖logDeriv riemannZeta p‖ ≤L)→
    ∀ p∈aO (zc R) (wc R), ‖logDeriv xi p‖ ≤C*(L+Real.log (2+R)) :=by
  obtain ⟨C₁,hC₁,hmid⟩:=pI
  obtain ⟨C₂,hC₂,Pz⟩:=xZ
  refine ⟨C₁+2*C₂,by positivity,fun L R hL hR vN p hp=>?_⟩
  have Oo:0≤Real.log (2+R) :=Real.log_nonneg (by linarith)
  have hLl:Real.log (2+R)≤L+Real.log (2+R) :=by linarith
  have hpR:p∈Rectangle (zc R) (wc R) :=cO _ _ hp
  have hmem:(1-R≤p.re ∧ p.re≤R) ∧ (-R≤p.im ∧ p.im≤R) :=by
    simpa only [Rectangle,Complex.mem_reProdIm,Cz,CJ,CQ,CX,
      Set.uIcc_of_le (show (1-R:ℝ)≤R by linarith),
      Set.uIcc_of_le (show (-R:ℝ)≤R by linarith),Set.mem_Icc] using hpR
  have hpn: ‖p‖ ≤2*R:=by
    calc ‖p‖ ≤ |p.re| + |p.im| :=Complex.norm_le_abs_re_add_abs_im p
      _≤R+R:=add_le_add (abs_le.mpr ⟨by linarith [hmem.1.1],hmem.1.2⟩)
          (abs_le.mpr ⟨hmem.2.1,hmem.2.2⟩)
      _=2*R:=by ring
  have aaE: ∀ q:ℂ, ‖q‖ ≤2*R+2→Real.log (2+ ‖q‖)≤2*Real.log (2+R) :=by
    intro q hq
    have e:2*Real.log (2+R)=Real.log ((2+R)^2) :=by
      rw [Real.log_pow]; norm_num
    rw [e]
    apply Real.log_le_log (by positivity)
    nlinarith [norm_nonneg q]
  have hR': ∀ q:ℂ, ‖q‖ ≤2*R+2→3/2≤q.re→
      ‖logDeriv xi q‖ ≤2*C₂*Real.log (2+R) :=by
    intro q hq hre
    calc ‖logDeriv xi q‖ ≤C₂*Real.log (2+ ‖q‖) :=Pz q hre
      _≤C₂*(2*Real.log (2+R)) :=mul_le_mul_of_nonneg_left (aaE q hq) hC₂.le
      _=2*C₂*Real.log (2+R) :=by ring
  have hL': ∀ q:ℂ, ‖q‖ ≤2*R+1→q.re≤ -1/2→
      ‖logDeriv xi q‖ ≤2*C₂*Real.log (2+R) :=by
    intro q hq hre
    have e:logDeriv xi q= -logDeriv xi (1-q) :=by
      rw [← kF (1-q),sub_sub_cancel]
    rw [e,norm_neg]
    apply hR' (1-q)
    · calc ‖1-q‖ ≤ ‖(1:ℂ)‖ + ‖q‖ :=norm_sub_le _ _
        _≤2*R+2:=by rw [norm_one]; linarith
    · simp; linarith
  have Pw: ‖logDeriv xi p‖ ≤2*C₂*Real.log (2+R) ∨
      ‖logDeriv xi p‖ ≤C₁*(L+Real.log (2+R)) :=by
    rcases le_or_gt (3/2:ℝ) p.re with h1 | h1
    · exact Or.inl (hR' p (by linarith) h1)
    rcases le_or_gt p.re (-1/2:ℝ) with h2 | h2
    · exact Or.inl (hL' p (by linarith) h2)
    right
    have him:p.im=R ∨ p.im= -R:=by
      simp only [aO,Set.mem_union,Complex.mem_reProdIm,Set.mem_singleton_iff,
        Cz,CJ,CQ,CX] at hp
      rcases hp with ((⟨_,h'⟩ | ⟨h',_⟩) | ⟨_,h'⟩) | ⟨h',_⟩
      · exact Or.inr h'
      · exfalso; linarith
      · exact Or.inl h'
      · exfalso; linarith
    exact hmid L R hL (by linarith) vN p him (by linarith) (by linarith)
  rcases Pw with h | h
  · calc ‖logDeriv xi p‖ ≤2*C₂*Real.log (2+R) :=h
      _≤2*C₂*(L+Real.log (2+R)) :=mul_le_mul_of_nonneg_left hLl (by positivity)
      _≤(C₁+2*C₂)*(L+Real.log (2+R)) :=by nlinarith
  · calc ‖logDeriv xi p‖ ≤C₁*(L+Real.log (2+R)) :=h
      _≤(C₁+2*C₂)*(L+Real.log (2+R)) :=by nlinarith
def wt (s w:ℂ) :ℂ:=1/(s-w)-1/(reflect s-w)
theorem WS (s w:ℂ) (h1:s-w≠0) (h2:reflect s-w≠0) :
    wt s w=(reflect s-s)/((s-w)*(reflect s-w)) :=by
  unfold wt
  field_simp
  ring
theorem Gp {s:ℂ} {R:ℝ} (hR:2* ‖s‖ +4≤R) :
    ∀ p∈aO (zc R) (wc R), ‖wt s p‖ ≤4* ‖s-reflect s‖ /R^2:=by
  have hR0:0<R:=by linarith [norm_nonneg s]
  have hdist: ∀ a:ℂ,2* ‖a‖ +2≤R→ ∀ p∈aO (zc R) (wc R),R/2≤ ‖a-p‖ :=by
    intro a ha p hp
    have hare: |a.re| ≤ ‖a‖ :=Complex.abs_re_le_norm a
    have haim: |a.im| ≤ ‖a‖ :=Complex.abs_im_le_norm a
    have h1: |(a-p).re| ≤ ‖a-p‖ :=Complex.abs_re_le_norm _
    have h2: |(a-p).im| ≤ ‖a-p‖ :=Complex.abs_im_le_norm _
    rw [Complex.sub_re] at h1
    rw [Complex.sub_im] at h2
    have adD:=abs_le.mp hare
    have adG:=abs_le.mp haim
    simp only [aO,Set.mem_union,Complex.mem_reProdIm,Set.mem_singleton_iff,
      Cz,CJ,CQ,CX] at hp
    rcases hp with ((⟨_,h'⟩ | ⟨h',_⟩) | ⟨_,h'⟩) | ⟨h',_⟩
    · 
      have:R/2≤ |a.im-p.im| :=by rw [h']; rw [abs_of_nonneg (by linarith)]; linarith
      linarith
    · 
      have:R/2≤ |a.re-p.re| :=by rw [h']; rw [abs_of_nonneg (by linarith)]; linarith
      linarith
    · 
      have:R/2≤ |a.im-p.im| :=by rw [h']; rw [abs_of_nonpos (by linarith)]; linarith
      linarith
    · 
      have:R/2≤ |a.re-p.re| :=by rw [h']; rw [abs_of_nonpos (by linarith)]; linarith
      linarith
  intro p hp
  have hrs: ‖reflect s‖ ≤1+ ‖s‖ :=by
    calc ‖reflect s‖ = ‖1-conj s‖ :=rfl
      _≤ ‖(1:ℂ)‖ + ‖conj s‖ :=norm_sub_le _ _
      _=1+ ‖s‖ :=by rw [norm_one,Complex.norm_conj]
  have d1:=hdist s (by linarith) p hp
  have d2:=hdist (reflect s) (by linarith) p hp
  have h1:s-p≠0:=norm_pos_iff.mp (by linarith)
  have h2:reflect s-p≠0:=norm_pos_iff.mp (by linarith)
  rw [WS s p h1 h2,norm_div,norm_mul,norm_sub_rev (reflect s) s]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have:=mul_le_mul d1 d2 (by positivity) (norm_nonneg _)
  nlinarith [norm_nonneg (s-reflect s)]
theorem square_identity {s:ℂ} (hxi:xi s≠0) (hs:s.re≠1/2) {R:ℝ} (hR: ‖s‖ +2≤R)
    (hζ: ∀ p:ℂ,(p.im=R ∨ p.im= -R)→1/2≤p.re→p.re≤2→ riemannZeta p≠0) :
    ∃ Z:Finset ℂ,((Z:Set ℂ)={ρ:ℂ | aE ρ ∧ -R<ρ.im ∧ ρ.im<R}) ∧
      aW (fun p=>wt s p*logDeriv xi p) (zc R) (wc R)
        =(∑ ρ∈Z,(aP ρ:ℂ)*wt s ρ)-logDeriv xi s+logDeriv xi (reflect s) :=by
  classical
  have hσ:=abs_le.mp (Complex.abs_re_le_norm s)
  have ht:=abs_le.mp (Complex.abs_im_le_norm s)
  have hR1:2≤R:=by linarith [norm_nonneg s]
  have hre:(zc R).re≤(wc R).re:=by simp; linarith
  have him:(zc R).im≤(wc R).im:=by simp; linarith
  have hmem: ∀ p:ℂ,p∈Rectangle (zc R) (wc R)↔
      (1-R≤p.re ∧ p.re≤R) ∧ (-R≤p.im ∧ p.im≤R) :=by
    intro p
    simp only [Rectangle,Complex.mem_reProdIm,Cz,CJ,CQ,CX,
      Set.uIcc_of_le (show (1-R:ℝ)≤R by linarith),
      Set.uIcc_of_le (show (-R:ℝ)≤R by linarith),Set.mem_Icc]
  have hint: ∀ p:ℂ,Rectangle (zc R) (wc R)∈𝓝 p↔
      (1-R<p.re ∧ p.re<R) ∧ (-R<p.im ∧ p.im<R) :=by
    intro p
    rw [eo,Complex.mem_reProdIm,Set.uIoo_of_le hre,Set.uIoo_of_le him,
      Cz,CJ,CQ,CX,Set.mem_Ioo,Set.mem_Ioo]
  have hΛ:=Zeta23.bR.lA (c:=3/2) (R:=R)
    (by norm_num) le_rfl hζ
  have SJ: ∀ p:ℂ,(p.im=R ∨ p.im= -R)→xi p≠0:=by
    intro p hp h0
    have hnz:=(dY p).mp h0
    exact hΛ p hp (by linarith [hnz.2.1]) (by linarith [hnz.2.2])
      (Zeta23.dQ.iz.mpr hnz)
  have hfin:{ρ:ℂ | aE ρ ∧ -R<ρ.im ∧ ρ.im<R}.Finite:=
    (kS.dH (-R) R).subset (fun ρ ⟨h1,h2,h3⟩=>⟨h1,h2,h3.le⟩)
  set Z:Finset ℂ:=hfin.toFinset with aaF
  have FI: ∀ ρ,ρ∈Z↔aE ρ ∧ -R<ρ.im ∧ ρ.im<R:=by
    intro ρ; rw [aaF,Set.Finite.mem_toFinset]; rfl
  refine ⟨Z,hfin.coe_toFinset,?_⟩
  have hsr:s≠reflect s:=by
    intro h; apply hs
    have:=congrArg Complex.re h
    simp [reflect] at this; linarith
  have SK:xi (reflect s)≠0:=by rw [Ld]; exact (map_ne_zero _).mpr hxi
  set Q:Finset ℂ:={s,reflect s} with hQdef
  have UR:Disjoint Z Q:=by
    rw [Finset.disjoint_right]
    intro q hq YQ
    have hz:=(dY q).mpr ((FI q).mp YQ).1
    simp only [hQdef,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    exacts [hxi hz,SK hz]
  have hsint:Rectangle (zc R) (wc R)∈𝓝 s:=by
    rw [hint]
    exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩
  have YW:Rectangle (zc R) (wc R)∈𝓝 (reflect s) :=by
    rw [hint]
    have e1:(reflect s).re=1-s.re:=by simp [reflect]
    have e2:(reflect s).im=s.im:=by simp [reflect]
    rw [e1,e2]
    exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩
  have Om: ∀ q∈Q,Rectangle (zc R) (wc R)∈𝓝 q:=by
    intro q hq
    simp only [hQdef,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    exacts [hsint,YW]
  have hf:AnalyticOnNhd ℂ xi (Rectangle (zc R) (wc R)) :=fun p _=>fO.analyticAt p
  have hg: ∀ p∈Rectangle (zc R) (wc R) \ (Q:Set ℂ),AnalyticAt ℂ (wt s) p:=by
    rintro p ⟨_,hpQ⟩
    simp only [hQdef,Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,
      Set.mem_singleton_iff,not_or] at hpQ
    have hopen:IsOpen (({s,reflect s} :Set ℂ)ᶜ) :=(Set.toFinite _).isClosed.isOpen_compl
    apply DifferentiableOn.analyticAt (s:=(({s,reflect s} :Set ℂ)ᶜ))
    · intro w hw
      simp only [Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_singleton_iff,not_or] at hw
      have h1:s-w≠0:=sub_ne_zero.mpr (Ne.symm hw.1)
      have h2:reflect s-w≠0:=sub_ne_zero.mpr (Ne.symm hw.2)
      apply DifferentiableAt.differentiableWithinAt
      show DifferentiableAt ℂ (fun w=>1/(s-w)-1/(reflect s-w)) w
      fun_prop (disch:=assumption)
    · exact hopen.mem_nhds (by simp [hpQ.1,hpQ.2])
  have vV: ∀ p∈aO (zc R) (wc R),xi p≠0:=by
    intro p hp h0
    have hnz:=(dY p).mp h0
    simp only [aO,Set.mem_union,Complex.mem_reProdIm,Set.mem_singleton_iff,
      Cz,CJ,CQ,CX] at hp
    rcases hp with ((⟨_,h'⟩ | ⟨h',_⟩) | ⟨_,h'⟩) | ⟨h',_⟩
    · exact SJ p (Or.inr h') h0
    · linarith [hnz.2.1]
    · exact SJ p (Or.inl h') h0
    · linarith [hnz.2.2]
  have YZ: ∀ p∈Rectangle (zc R) (wc R),xi p=0↔p∈Z:=by
    intro p hp
    rw [FI,dY]
    obtain ⟨⟨hr1,hr2⟩,⟨hi1,hi2⟩⟩:=(hmem p).mp hp
    constructor
    · intro hnz
      refine ⟨hnz,lt_of_le_of_ne hi1 (fun h=>?_),lt_of_le_of_ne hi2 (fun h=>?_)⟩
      · exact SJ p (Or.inr h.symm) ((dY p).mpr hnz)
      · exact SJ p (Or.inl h) ((dY p).mpr hnz)
    · exact fun h=>h.1
  have FJ:(Z:Set ℂ)⊆Rectangle (zc R) (wc R) :=by
    intro ρ hρ
    rw [Finset.mem_coe,FI] at hρ
    obtain ⟨h1,h2,h3⟩:=hρ
    exact (hmem ρ).mpr ⟨⟨by linarith [h1.2.1],by linarith [h1.2.2]⟩,h2.le,h3.le⟩
  set r:ℂ→ℂ:=fun q=>if q=s then -1 else 1 with WT
  have hr1:r s= -1:=by simp [WT]
  have hr2:r (reflect s)=1:=by simp [WT,hsr.symm]
  have SD: ∀ q∈Q,(wt s-fun w=>r q/(w-q)) =O[𝓝[≠] q] (1:ℂ→ℂ) :=by
    intro q hq
    simp only [hQdef,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with h | h
    · subst h
      have hne:reflect q-q≠0:=sub_ne_zero.mpr (Ne.symm hsr)
      have hc:ContinuousAt (fun w=> -(1/(reflect q-w))) q:=by
        have h1:ContinuousAt (fun w:ℂ=>reflect q-w) q:=by fun_prop
        exact (continuousAt_const.div h1 hne).neg
      have hO:(fun w=> -(1/(reflect q-w))) =O[𝓝[≠] q] (1:ℂ→ℂ) :=
        (hc.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
      refine hO.congr' ?_ EventuallyEq.rfl
      have hev: ∀ᶠ w in 𝓝 q,reflect q-w≠0:=
        (continuous_const.sub continuous_id).continuousAt.eventually_ne hne
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hev] with w hw hw2
      have hwq:w-q≠0:=sub_ne_zero.mpr hw
      have hqw:q-w≠0:=sub_ne_zero.mpr (Ne.symm hw)
      simp only [Pi.sub_apply,wt,hr1]
      field_simp
      ring
    · subst h
      have hne:s-reflect s≠0:=sub_ne_zero.mpr hsr
      have hc:ContinuousAt (fun w=>1/(s-w)) (reflect s) :=by
        have h1:ContinuousAt (fun w:ℂ=>s-w) (reflect s) :=by fun_prop
        exact continuousAt_const.div h1 hne
      have hO:(fun w=>1/(s-w)) =O[𝓝[≠] (reflect s)] (1:ℂ→ℂ) :=
        (hc.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
      refine hO.congr' ?_ EventuallyEq.rfl
      have hev: ∀ᶠ w in 𝓝 (reflect s),s-w≠0:=
        (continuous_const.sub continuous_id).continuousAt.eventually_ne hne
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hev] with w hw hw2
      have hwq:w-reflect s≠0:=sub_ne_zero.mpr hw
      have hqw:reflect s-w≠0:=sub_ne_zero.mpr (Ne.symm hw)
      simp only [Pi.sub_apply,wt,hr2]
      field_simp
      ring
  have key:=jA hre him Z Q UR Om hf hg vV
    YZ FJ r SD
  rw [key]
  have Lb: ∑ ρ∈Z,(analyticOrderNatAt xi ρ:ℂ)*wt s ρ= ∑ ρ∈Z,(aP ρ:ℂ)*wt s ρ:=
    Finset.sum_congr rfl (fun ρ hρ=>by rw [Br ((FI ρ).mp hρ).1])
  have SH: ∑ q∈Q,r q*logDeriv xi q= -logDeriv xi s+logDeriv xi (reflect s) :=by
    rw [hQdef,Finset.sum_insert (by simpa using hsr),Finset.sum_singleton,hr1,hr2]
    ring
  rw [Lb,SH]
  ring
theorem vO (s:ℂ) {Cg:ℝ} (hCg:0<Cg) {R:ℕ→ℝ}
    (hR: ∀ j:ℕ,(j:ℝ)+7≤R j ∧ R j≤(j:ℝ)+8)
    (vN: ∀ j:ℕ, ∀ p:ℂ,(p.im=R j ∨ p.im= -R j)→1/2≤p.re→p.re≤2→
      riemannZeta p≠0 ∧ ‖logDeriv riemannZeta p‖ ≤Cg*(Real.log ((j:ℝ)+10))^2) :
    Tendsto (fun j:ℕ=>aW (fun p=>wt s p*logDeriv xi p) (zc (R j)) (wc (R j)))
      atTop (𝓝 0) :=by
  obtain ⟨C,hC,hb⟩:=sK
  set K:ℝ:=32* ‖s-reflect s‖ *C*(Cg+2) with hK
  have hlim:Tendsto (fun j:ℕ=>K*(Real.log ((j:ℝ)+10)^2/((j:ℝ)+7)))
      atTop (𝓝 0) :=by
    have h1:=Real.tendsto_pow_log_div_mul_add_atTop 1 (-3) 2 one_ne_zero
    have h2:Tendsto (fun j:ℕ=>(j:ℝ)+10) atTop atTop:=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have h3:=(h1.comp h2).const_mul K
    rw [mul_zero] at h3
    refine h3.congr (fun j=>?_)
    simp only [Function.comp_apply]
    ring_nf
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun j=>norm_nonneg _)) ?_ hlim
  filter_upwards [eventually_ge_atTop (Nat.ceil (2* ‖s‖))] with j hj
  have WU:=hR j
  have hj':2* ‖s‖ ≤j:=le_trans (Nat.le_ceil _) (by exact_mod_cast hj)
  have hR4:2* ‖s‖ +4≤R j:=by linarith
  have hR2:2≤R j:=by linarith [norm_nonneg s]
  have hR0:0<R j:=by linarith
  set L:ℝ:=Cg*Real.log ((j:ℝ)+10)^2+1 with hL
  have adk:1≤Real.log ((j:ℝ)+10) :=by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have:=Real.exp_one_lt_d9
    linarith [(Nat.cast_nonneg j:(0:ℝ)≤j)]
  have adl:Real.log ((j:ℝ)+10)≤Real.log ((j:ℝ)+10)^2:=by nlinarith
  have hL1:1≤L:=by
    have:0≤Cg*Real.log ((j:ℝ)+10)^2:=by positivity
    rw [hL]; linarith
  have Zb: ∀ p:ℂ,(p.im=R j ∨ p.im= -R j)→1/2≤p.re→p.re≤2→
      riemannZeta p≠0 ∧ ‖logDeriv riemannZeta p‖ ≤L:=
    fun p hp h1 h2=>⟨(vN j p hp h1 h2).1,by rw [hL]; linarith [(vN j p hp h1 h2).2]⟩
  have hM: ∀ p∈aO (zc (R j)) (wc (R j)),
      ‖wt s p*logDeriv xi p‖ ≤(4* ‖s-reflect s‖ /R j^2)*(C*(L+Real.log (2+R j))) :=by
    intro p hp
    rw [norm_mul]
    exact mul_le_mul (Gp hR4 p hp) (hb L (R j) hL1 hR2 Zb p hp)
      (norm_nonneg _) (by positivity)
  have hI:=vH (f:=fun p=>wt s p*logDeriv xi p)
    (by simp; linarith) (by simp; linarith) hM
  simp only [Cz,CQ,CJ,CX] at hI
  have hA:L+Real.log (2+R j)≤(Cg+2)*Real.log ((j:ℝ)+10)^2:=by
    have h1:Real.log (2+R j)≤Real.log ((j:ℝ)+10) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [hL]; nlinarith
  have hB:(4* ‖s-reflect s‖ /R j^2)*(C*(L+Real.log (2+R j)))
      *(2*(R j-(1-R j))+2*(R j- -R j))
      ≤K*(Real.log ((j:ℝ)+10)^2/((j:ℝ)+7)) :=by
    calc (4* ‖s-reflect s‖ /R j^2)*(C*(L+Real.log (2+R j)))
          *(2*(R j-(1-R j))+2*(R j- -R j))
        ≤(4* ‖s-reflect s‖ /R j^2)*(C*((Cg+2)*Real.log ((j:ℝ)+10)^2))
          *(8*R j) :=by
          apply mul_le_mul _ (by linarith) (by linarith) (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA hC.le) (by positivity)
      _=K*Real.log ((j:ℝ)+10)^2/R j:=by
          rw [hK]; field_simp; ring
      _≤K*Real.log ((j:ℝ)+10)^2/((j:ℝ)+7) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) WU.1
      _=K*(Real.log ((j:ℝ)+10)^2/((j:ℝ)+7)) :=by ring
  have h2π: ‖(1/(2*(Real.pi:ℂ)* I) :ℂ)‖ ≤1:=by
    rw [norm_div,norm_one,norm_mul,norm_mul,Complex.norm_I,mul_one,Complex.norm_ofNat,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  calc ‖aW (fun p=>wt s p*logDeriv xi p) (zc (R j)) (wc (R j))‖
      = ‖(1/(2*(Real.pi:ℂ)* I) :ℂ)‖
        * ‖aV (fun p=>wt s p*logDeriv xi p) (zc (R j)) (wc (R j))‖ :=by
        rw [aW,norm_smul]
    _≤1* ‖aV (fun p=>wt s p*logDeriv xi p) (zc (R j)) (wc (R j))‖ :=
        mul_le_mul_of_nonneg_right h2π (norm_nonneg _)
    _≤K*(Real.log ((j:ℝ)+10)^2/((j:ℝ)+7)) :=by rw [one_mul]; exact hI.trans hB
theorem jT {s:ℂ} (hxi:xi s≠0) : ∃ c:ℝ,0<c ∧ ∀ ρ:ℂ,
    aE ρ→c*(1+Complex.normSq (bZ ρ))≤Complex.normSq (s-ρ) :=by
  classical
  set t:ℝ:=s.im with ht
  have hfin:=kS.dH (t-1) (t+1)
  set F:Finset ℂ:=hfin.toFinset with hF
  have WV: ∀ ρ:ℂ,ρ∈F↔aE ρ ∧ t-1<ρ.im ∧ ρ.im≤t+1:=by
    intro ρ; rw [hF,Set.Finite.mem_toFinset]; rfl
  obtain ⟨d,hd0,hd⟩: ∃ d:ℝ,0<d ∧ ∀ ρ∈F,d≤Complex.normSq (s-ρ) :=by
    by_cases hne:F.Nonempty
    · refine ⟨F.inf' hne (fun ρ=>Complex.normSq (s-ρ)),?_,fun ρ hρ=>Finset.inf'_le _ hρ⟩
      obtain ⟨ρ₀,Zd,heq⟩:=Finset.exists_mem_eq_inf' hne (fun ρ=>Complex.normSq (s-ρ))
      rw [heq]
      refine Complex.normSq_pos.mpr (sub_ne_zero.mpr (fun h=>hxi ?_))
      rw [h]
      exact (dY ρ₀).mpr ((WV ρ₀).mp Zd).1
    · exact ⟨1,one_pos,fun ρ hρ=>(hne ⟨ρ,hρ⟩).elim⟩
  refine ⟨min (d/(5/4+(|t| +1)^2)) (1/(13/4+2*t^2)),lt_min (by positivity)
    (by positivity),fun ρ hρ=>?_⟩
  have hN:Complex.normSq (bZ ρ)=ρ.im^2+(1/2 -ρ.re)^2:=by
    rw [Complex.normSq_apply,Zeta23.bR.KX,Zeta23.bR.Sl]; ring
  have aec:=hρ.2.1
  have aed:=hρ.2.2
  have aee:Complex.normSq (bZ ρ)≤ρ.im^2+1/4:=by
    rw [hN]; nlinarith
  have hns:Complex.normSq (s-ρ)=(s.re-ρ.re)^2+(t-ρ.im)^2:=by
    rw [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,ht]; ring
  by_cases hwin:t-1<ρ.im ∧ ρ.im≤t+1
  · 
    have aci:ρ∈F:=(WV ρ).mpr ⟨hρ,hwin⟩
    have h1:1+Complex.normSq (bZ ρ)≤5/4+(|t| +1)^2:=by
      have:ρ.im^2≤(|t| +1)^2:=by
        have h: |ρ.im| ≤ |t| +1:=
          abs_le.mpr ⟨by linarith [hwin.1,neg_abs_le t],by linarith [hwin.2,le_abs_self t]⟩
        calc ρ.im^2= |ρ.im| ^2:=(sq_abs _).symm
          _≤(|t| +1)^2:=pow_le_pow_left₀ (abs_nonneg _) h 2
      linarith
    calc min (d/(5/4+(|t| +1)^2)) (1/(13/4+2*t^2))*(1+Complex.normSq (bZ ρ))
        ≤(d/(5/4+(|t| +1)^2))*(5/4+(|t| +1)^2) :=by
          apply mul_le_mul (min_le_left _ _) h1
            (by linarith [Complex.normSq_nonneg (bZ ρ)]) (by positivity)
      _=d:=by field_simp
      _≤Complex.normSq (s-ρ) :=hd ρ aci
  · 
    have Pz:1≤(t-ρ.im)^2:=by
      rcases not_and_or.mp hwin with h | h
      · push Not at h; nlinarith
      · push Not at h; nlinarith
    have h1:1+Complex.normSq (bZ ρ)≤(13/4+2*t^2)*(t-ρ.im)^2:=by
      have:ρ.im^2≤2*(ρ.im-t)^2+2*t^2:=by nlinarith [sq_nonneg (ρ.im-2*t)]
      nlinarith
    calc min (d/(5/4+(|t| +1)^2)) (1/(13/4+2*t^2))*(1+Complex.normSq (bZ ρ))
        ≤(1/(13/4+2*t^2))*((13/4+2*t^2)*(t-ρ.im)^2) :=by
          apply mul_le_mul (min_le_right _ _) h1
            (by linarith [Complex.normSq_nonneg (bZ ρ)]) (by positivity)
      _=(t-ρ.im)^2:=by field_simp
      _≤Complex.normSq (s-ρ) :=by rw [hns]; nlinarith
theorem Lk {s:ℂ} (hxi:xi s≠0) : ∃ C:ℝ, ∀ ρ:ℂ,aE ρ→
    ‖wt s ρ‖ ≤C/(1+Complex.normSq (bZ ρ)) :=by
  have SK:xi (reflect s)≠0:=by
    rw [Ld]; exact (map_ne_zero _).mpr hxi
  obtain ⟨c,hc,h⟩:=jT hxi
  obtain ⟨c',hc',h'⟩:=jT SK
  refine ⟨‖reflect s-s‖ /2*(1/c+1/c'),fun ρ hρ=>?_⟩
  have hz:xi ρ=0:=(dY ρ).mpr hρ
  have h1:s-ρ≠0:=sub_ne_zero.mpr (fun e=>hxi (e ▸ hz))
  have h2:reflect s-ρ≠0:=sub_ne_zero.mpr (fun e=>SK (e ▸ hz))
  set N:ℝ:=1+Complex.normSq (bZ ρ) with SM
  have hN:0<N:=by rw [SM]; linarith [Complex.normSq_nonneg (bZ ρ)]
  have ha:c*N≤ ‖s-ρ‖ ^2:=by rw [Complex.sq_norm]; exact h ρ hρ
  have hb:c'*N≤ ‖reflect s-ρ‖ ^2:=by rw [Complex.sq_norm]; exact h' ρ hρ
  have ha0:0< ‖s-ρ‖ :=norm_pos_iff.mpr h1
  have hb0:0< ‖reflect s-ρ‖ :=norm_pos_iff.mpr h2
  rw [WS s ρ h1 h2,norm_div,norm_mul]
  have key:1/(‖s-ρ‖ * ‖reflect s-ρ‖)≤(1/(c*N)+1/(c'*N))/2:=by
    have hab:1/(‖s-ρ‖ * ‖reflect s-ρ‖)≤(1/ ‖s-ρ‖ ^2+1/ ‖reflect s-ρ‖ ^2)/2:=by
      rw [div_add_div _ _ (by positivity) (by positivity),div_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (‖s-ρ‖ - ‖reflect s-ρ‖),mul_pos ha0 hb0]
    have h3:1/ ‖s-ρ‖ ^2≤1/(c*N) :=
      one_div_le_one_div_of_le (by positivity) ha
    have h4:1/ ‖reflect s-ρ‖ ^2≤1/(c'*N) :=
      one_div_le_one_div_of_le (by positivity) hb
    linarith
  calc ‖reflect s-s‖ /(‖s-ρ‖ * ‖reflect s-ρ‖)
      = ‖reflect s-s‖ *(1/(‖s-ρ‖ * ‖reflect s-ρ‖)) :=by ring
    _≤ ‖reflect s-s‖ *((1/(c*N)+1/(c'*N))/2) :=
        mul_le_mul_of_nonneg_left key (norm_nonneg _)
    _= ‖reflect s-s‖ /2*(1/c+1/c')/N:=by
        field_simp
theorem Gq {φ:ℂ→ℂ} {C:ℝ}
    (hφ: ∀ ρ:ℂ,aE ρ→ ‖φ ρ‖ ≤C/(1+Complex.normSq (bZ ρ))) :
    Summable (fun ρ:aD.carrier=>(aP ρ:ℂ)*φ ρ) :=by
  have hS:=(Zeta23.bR.zA kS).mul_left C
  refine Summable.of_norm_bounded hS (fun ρ=>?_)
  have hρ:aE (ρ:ℂ) :=ρ.2
  rw [norm_mul,Complex.norm_natCast]
  have hN:0<1+Complex.normSq (bZ (ρ:ℂ)) :=by
    linarith [Complex.normSq_nonneg (bZ (ρ:ℂ))]
  calc (aP (ρ:ℂ) :ℝ)* ‖φ ρ‖
      ≤(aP (ρ:ℂ) :ℝ)*(C/(1+Complex.normSq (bZ (ρ:ℂ)))) :=
        mul_le_mul_of_nonneg_left (hφ ρ hρ) (Nat.cast_nonneg _)
    _=C*((aP (ρ:ℂ) :ℝ)/(1+Complex.normSq (bZ (ρ:ℂ)))) :=by
        field_simp
theorem ED {φ:ℂ→ℂ}
    (hφ:Summable (fun ρ:aD.carrier=>(aP ρ:ℂ)*φ ρ))
    {R:ℕ→ℝ} (hR: ∀ j:ℕ,(j:ℝ)+7≤R j ∧ R j≤(j:ℝ)+8) {Z:ℕ→Finset ℂ}
    (hZ: ∀ j:ℕ,((Z j:Set ℂ)={ρ:ℂ | aE ρ ∧ -R j<ρ.im ∧ ρ.im<R j})) :
    Tendsto (fun j:ℕ=> ∑ ρ∈Z j,(aP ρ:ℂ)*φ ρ) atTop
      (𝓝 (∑' ρ:aD.carrier,(aP ρ:ℂ)*φ ρ)) :=by
  classical
  set g:aD.carrier→ℂ:=fun ρ=>(aP ρ:ℂ)*φ ρ with hg
  have hsum:Summable g:=hφ
  have SN: ∀ j ρ,ρ∈Z j↔aE ρ ∧ -R j<ρ.im ∧ ρ.im<R j:=by
    intro j ρ
    rw [← Finset.mem_coe,hZ j]
    rfl
  set sF:ℕ→Finset aD.carrier:=
    fun j=>(Z j).subtype (· ∈aD.carrier) with adH
  have Xz: ∀ j, ∑ x∈sF j,g x= ∑ ρ∈Z j,(aP ρ:ℂ)*φ ρ:=by
    intro j
    have h1:=Finset.sum_subtype_eq_sum_filter (s:=Z j)
      (p:=(· ∈aD.carrier)) (fun ρ:ℂ=>(aP ρ:ℂ)*φ ρ)
    have h2:(Z j).filter (· ∈aD.carrier)=Z j:=by
      apply Finset.filter_true_of_mem
      intro ρ hρ
      exact ((SN j ρ).mp hρ).1
    rw [h2] at h1
    rw [← h1]
  have Ze: ∀ i j:ℕ,i≤j→R i≤R j:=by
    intro i j hij
    rcases hij.eq_or_lt with h | h
    · rw [h]
    · have:(i:ℝ)+1≤j:=by exact_mod_cast h
      linarith [(hR i).2,(hR j).1]
  have hmono:Monotone sF:=by
    intro i j hij x hx
    rw [Finset.mem_subtype,SN] at hx ⊢
    obtain ⟨h1,h2,h3⟩:=hx
    have:=Ze i j hij
    exact ⟨h1,by linarith,by linarith⟩
  have hexh: ∀ b:Finset aD.carrier, ∃ j,b≤ sF j:=by
    intro b
    set M:ℝ:= ∑ x∈b, |((x:ℂ)).im| with hM
    have acj: ∀ x∈b, |((x:ℂ)).im| ≤M:=fun x hx=>
      Finset.single_le_sum (f:=fun x:aD.carrier=> |((x:ℂ)).im|)
        (fun _ _=>abs_nonneg _) hx
    obtain ⟨j,hj⟩:=exists_nat_gt M
    refine ⟨j,fun x hx=>?_⟩
    rw [Finset.mem_subtype,SN]
    have hx0:aE (x:ℂ) :=x.2
    have habs:=abs_le.mp (acj x hx)
    have WU:=(hR j).1
    exact ⟨hx0,by linarith [habs.1],by linarith [habs.2]⟩
  have XB:Tendsto sF atTop atTop:=tendsto_atTop_atTop_of_monotone hmono hexh
  have hT:Tendsto (fun S:Finset aD.carrier=> ∑ x∈S,g x) atTop
      (𝓝 (∑' x,g x)) :=by
    have Zj:=hsum.hasSum
    simp only [HasSum,SummationFilter.unconditional_filter] at Zj
    exact Zj
  have:=hT.comp XB
  refine this.congr (fun j=>?_)
  simp only [Function.comp_apply,Xz]
theorem GZ {s:ℂ} (hxi:xi s≠0) :
    Summable (fun ρ:aD.carrier=>(aP ρ:ℂ)*wt s ρ) :=by
  obtain ⟨C,hC⟩:=Lk hxi
  exact Gq hC
theorem yA {s:ℂ} (hxi:xi s≠0) :
    logDeriv xi s-logDeriv xi (reflect s)
      = ∑' ρ:aD.carrier,(aP ρ:ℂ)*wt s ρ:=by
  by_cases hs:s.re=1/2
  · 
    have hsr:reflect s=s:=by
      apply Complex.ext <;> norm_num [reflect,hs]
    have hwt: ∀ w,wt s w=0:=fun w=>by simp [wt,hsr]
    simp [hsr,hwt]
  obtain ⟨Cg,hCg,R,hR⟩:=Zeta23.bR.PI
  have hRb: ∀ j:ℕ,(j:ℝ)+7≤R j ∧ R j≤(j:ℝ)+8:=fun j=>⟨(hR j).1,(hR j).2.1⟩
  have vN: ∀ j:ℕ, ∀ p:ℂ,(p.im=R j ∨ p.im= -R j)→1/2≤p.re→p.re≤2→
      riemannZeta p≠0 ∧ ‖logDeriv riemannZeta p‖ ≤Cg*(Real.log ((j:ℝ)+10))^2:=
    fun j=>(hR j).2.2
  have acn: ∀ j:ℕ, ∃ Z:Finset ℂ,
      ((Z:Set ℂ)={ρ:ℂ | aE ρ ∧ -R j<ρ.im ∧ ρ.im<R j}) :=by
    intro j
    have hfin:{ρ:ℂ | aE ρ ∧ -R j<ρ.im ∧ ρ.im<R j}.Finite:=
      (kS.dH (-R j) (R j)).subset (fun ρ ⟨h1,h2,h3⟩=>⟨h1,h2,h3.le⟩)
    exact ⟨hfin.toFinset,hfin.coe_toFinset⟩
  choose Z hZ using acn
  have hlim:=ED (GZ hxi) hRb hZ
  have hI:=vO s hCg hRb vN
  have hev: ∀ᶠ j:ℕ in atTop,
      aW (fun p=>wt s p*logDeriv xi p) (zc (R j)) (wc (R j))
        =(∑ ρ∈Z j,(aP ρ:ℂ)*wt s ρ)-logDeriv xi s+logDeriv xi (reflect s) :=by
    filter_upwards [eventually_ge_atTop (Nat.ceil ‖s‖)] with j hj
    have WU: ‖s‖ +2≤R j:=by
      have h1:=(hRb j).1
      have h2:(⌈‖s‖⌉₊ :ℝ)≤j:=by exact_mod_cast hj
      linarith [Nat.le_ceil ‖s‖]
    obtain ⟨Z',hZ',hid⟩:=square_identity hxi hs WU (fun p hp h1 h2=>(vN j p hp h1 h2).1)
    have:Z'=Z j:=Finset.coe_injective (hZ'.trans (hZ j).symm)
    rw [← this]
    exact hid
  have h2:Tendsto (fun j=>(∑ ρ∈Z j,(aP ρ:ℂ)*wt s ρ)-logDeriv xi s
      +logDeriv xi (reflect s)) atTop (𝓝 0) :=hI.congr' hev
  have h3:Tendsto (fun j=>(∑ ρ∈Z j,(aP ρ:ℂ)*wt s ρ)-logDeriv xi s
      +logDeriv xi (reflect s)) atTop
      (𝓝 ((∑' ρ:aD.carrier,(aP ρ:ℂ)*wt s ρ)-logDeriv xi s
        +logDeriv xi (reflect s))) :=
    (hlim.sub_const _).add_const _
  have:=tendsto_nhds_unique h2 h3
  linear_combination this
theorem Lq (s ρ:ℂ) :((1:ℂ)/(s-ρ)).re=(s.re-ρ.re)/Complex.normSq (s-ρ) :=by
  rw [one_div,Complex.inv_re,Complex.sub_re]
theorem aaG (s ρ:ℂ) :
    (wt s ρ).re=((1:ℂ)/(s-ρ)).re+((1:ℂ)/(s-reflect ρ)).re:=by
  have h:reflect s-ρ= -conj (s-reflect ρ) :=by
    simp only [reflect,map_sub,map_one,Complex.conj_conj]; ring
  unfold wt
  rw [Complex.sub_re,h,one_div,one_div,one_div,Complex.inv_re,Complex.inv_re,Complex.inv_re,
    Complex.normSq_neg,Complex.normSq_conj,Complex.neg_re,Complex.conj_re]
  ring
theorem qE {s:ℂ} (hxi:xi s≠0) :
    Summable (fun ρ:aD.carrier=>
      (aP ρ:ℝ)*((s.re-(ρ:ℂ).re)/Complex.normSq (s-ρ))) :=by
  obtain ⟨c,hc,h⟩:=jT hxi
  have hS:=(Zeta23.bR.zA kS).mul_left ((|s.re| +1)/c)
  refine Summable.of_norm_bounded hS (fun ρ=>?_)
  have hρ:aE (ρ:ℂ) :=ρ.2
  set N:ℝ:=1+Complex.normSq (bZ (ρ:ℂ)) with SM
  have hN:0<N:=by rw [SM]; linarith [Complex.normSq_nonneg (bZ (ρ:ℂ))]
  have hcN:c*N≤Complex.normSq (s-ρ) :=h ρ hρ
  have hpos:0<Complex.normSq (s-ρ) :=lt_of_lt_of_le (by positivity) hcN
  have hnum: |s.re-(ρ:ℂ).re| ≤ |s.re| +1:=by
    have:=hρ.2.1; have:=hρ.2.2
    calc |s.re-(ρ:ℂ).re| ≤ |s.re| + |(ρ:ℂ).re| :=abs_sub _ _
      _≤ |s.re| +1:=by rw [abs_of_pos (a:=(ρ:ℂ).re) (by assumption)]; linarith
  rw [Real.norm_eq_abs,abs_mul,Nat.abs_cast,abs_div,abs_of_pos hpos]
  calc (aP (ρ:ℂ) :ℝ)*(|s.re-(ρ:ℂ).re| /Complex.normSq (s-ρ))
      ≤(aP (ρ:ℂ) :ℝ)*((|s.re| +1)/(c*N)) :=by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact div_le_div₀ (by positivity) hnum (by positivity) hcN
    _=(|s.re| +1)/c*((aP (ρ:ℂ) :ℝ)/N) :=by
        field_simp
def pJ:aD.carrier ≃ aD.carrier where
  toFun ρ:=⟨reflect ρ,aD.nI ρ ρ.2⟩
  invFun ρ:=⟨reflect ρ,aD.nI ρ ρ.2⟩
  left_inv ρ:=by ext; simp [reflect]
  right_inv ρ:=by ext; simp [reflect]
theorem yD (s:ℂ) :
    ∑' ρ:aD.carrier,(aP ρ:ℝ)*((1:ℂ)/(s-reflect ρ)).re
      = ∑' ρ:aD.carrier,(aP ρ:ℝ)*((1:ℂ)/(s-ρ)).re:=by
  rw [← Equiv.tsum_eq pJ
    (fun ρ:aD.carrier=>(aP ρ:ℝ)*((1:ℂ)/(s-ρ)).re)]
  refine tsum_congr (fun ρ=>?_)
  have hm:aP (reflect (ρ:ℂ))=aP ρ:=aD.eD ρ ρ.2
  simp only [pJ,Equiv.coe_fn_mk,hm]
theorem zY {s:ℂ} (hxi:xi s≠0) :
    (logDeriv xi s).re= ∑' ρ:aD.carrier,
      (aP ρ:ℝ)*((s.re-(ρ:ℂ).re)/Complex.normSq (s-ρ)) :=by
  have hmain:=congrArg Complex.re (yA hxi)
  rw [DK,Complex.sub_re,Complex.neg_re,Complex.conj_re,sub_neg_eq_add,
    Complex.re_tsum (GZ hxi)] at hmain
  have hterm: ∀ ρ:aD.carrier,((aP ρ:ℂ)*wt s ρ).re
      =(aP ρ:ℝ)*((1:ℂ)/(s-ρ)).re
        +(aP ρ:ℝ)*((1:ℂ)/(s-reflect ρ)).re:=by
    intro ρ
    rw [show (aP (ρ:ℂ) :ℂ)=((aP (ρ:ℂ) :ℝ) :ℂ) by norm_cast,
      Complex.re_ofReal_mul,aaG]
    ring
  simp_rw [hterm] at hmain
  have hS1:Summable fun ρ:aD.carrier=>
      (aP ρ:ℝ)*((1:ℂ)/(s-ρ)).re:=
    (qE hxi).congr (fun ρ=>by rw [Lq])
  have hS2:Summable fun ρ:aD.carrier=>
      (aP ρ:ℝ)*((1:ℂ)/(s-reflect ρ)).re:=by
    have:=(Equiv.summable_iff pJ (f:=fun ρ:aD.carrier=>
      (aP ρ:ℝ)*((1:ℂ)/(s-ρ)).re)).mpr hS1
    refine this.congr (fun ρ=>?_)
    have hm:aP (reflect (ρ:ℂ))=aP ρ:=aD.eD ρ ρ.2
    simp only [Function.comp_apply,pJ,Equiv.coe_fn_mk,hm]
  rw [hS1.tsum_add hS2,yD, ← two_mul] at hmain
  have:(logDeriv xi s).re
      = ∑' ρ:aD.carrier,(aP ρ:ℝ)*((1:ℂ)/(s-ρ)).re:=by
    linarith
  rw [this]
  exact tsum_congr (fun ρ=>by rw [Lq])
end lB
end cE
end Zeta23
end
end

-- aF.Zk
section
open Filter Asymptotics Complex ArithmeticFunction
open scoped ArithmeticFunction.vonMangoldt
noncomputable section
namespace aF.Psi
section
end
end aF.Psi
end
end

-- aF.Lagarias
section
open Complex
noncomputable section
namespace aF.Lagarias
abbrev ξ (s:ℂ) :ℂ:=s*(s-1)/2*completedRiemannZeta₀ s+1/2
lemma aaH:ξ=Zeta23.cE.xi:=rfl
lemma Od (hRH:RiemannHypothesis) {s:ℂ} (hs:1/2<s.re) (hξ:ξ s≠0) :
    0≤(logDeriv ξ s).re:=by
  rw [aaH] at hξ ⊢
  rw [Zeta23.cE.lB.zY hξ]
  have hsum:=Zeta23.cE.lB.qE hξ
  have hpos: ∀ ρ:Zeta23.aD.carrier,
      0<(Zeta23.aP ρ:ℝ)*((s.re-(ρ:ℂ).re)/Complex.normSq (s-ρ)) :=by
    intro ρ
    have hρ:Zeta23.aE (ρ:ℂ) :=ρ.2
    have hhalf:(ρ:ℂ).re=1/2:=by
      refine hRH ρ hρ.1 ?_ ?_
      · rintro ⟨n,hn⟩
        have:=congrArg Complex.re hn
        simp at this
        have:=hρ.2.1
        have hn0:(0:ℝ)≤n:=Nat.cast_nonneg n
        linarith
      · intro h; have:=hρ.2.2; rw [h] at this; simp at this
    have hm:(1:ℝ)≤Zeta23.aP (ρ:ℂ) :=by
      exact_mod_cast Zeta23.kS.one_le_mult ρ hρ
    have hne:s-ρ≠0:=by
      intro h
      rw [sub_eq_zero] at h
      apply hξ
      rw [h]
      exact (Zeta23.cE.lB.dY _).mpr hρ
    have h1:0<s.re-(ρ:ℂ).re:=by linarith
    exact mul_pos (by linarith) (div_pos h1 (Complex.normSq_pos.mpr hne))
  exact tsum_nonneg (fun ρ=>(hpos ρ).le)
end aF.Lagarias
end
end

-- aF.WX
section
open Complex
noncomputable section
namespace aF.qO
open Zeta23 Zeta23.cE Zeta23.cE.lB
end aF.qO
end
end

-- aF.Hadamard
section
open Complex Filter Topology
noncomputable section
namespace aF.qO
open Zeta23 Zeta23.cE Zeta23.cE.lB
end aF.qO
end
end

-- aF.SO
section
open Complex Filter Topology
noncomputable section
namespace aF.qO
open Zeta23 Zeta23.cE Zeta23.cE.lB
lemma wP {s:ℂ} (h0:s≠0) (hz:riemannZeta s≠0) :Gammaℝ s≠0:=by
  intro hg
  obtain ⟨n,hn⟩:=Gammaℝ_eq_zero_iff.mp hg
  rcases n with _ | n
  · exact h0 (by simpa using hn)
  · apply hz
    rw [hn]
    have:=riemannZeta_neg_two_mul_nat_add_one n
    convert this using 2; push_cast; ring
lemma mL {z:ℂ} (h0:z≠0) (h1:z≠1) :
    riemannZeta z=2*xi z/(z*(z-1))*(Gammaℝ z)⁻¹:=by
  rw [riemannZeta_def_of_ne_zero h0,completedRiemannZeta_eq,xi]
  have h1':z-1≠0:=sub_ne_zero.mpr h1
  have aef:1-z≠0:=fun e=>h1' (by linear_combination -e)
  rw [div_eq_mul_inv]
  congr 1
  field_simp
  ring
lemma DM {s:ℂ} (hg:Gammaℝ s≠0) :
    HasDerivAt Gammaℝ (-(deriv (fun z=>(Gammaℝ z)⁻¹) s)/((Gammaℝ s)⁻¹)^2) s:=by
  have hd:=(differentiable_Gammaℝ_inv s).hasDerivAt
  exact (hd.inv (inv_ne_zero hg)).congr_of_eventuallyEq (Eventually.of_forall fun z=>by simp)
theorem yF {s:ℂ} (h0:s≠0) (h1:s≠1) (hz:riemannZeta s≠0) :
    logDeriv riemannZeta s=logDeriv xi s-1/s-1/(s-1)-logDeriv Gammaℝ s:=by
  have hg:=wP h0 hz
  have h1':s-1≠0:=sub_ne_zero.mpr h1
  set f:ℂ→ℂ:=fun z=>2*xi z/(z*(z-1))*(Gammaℝ z)⁻¹ with hf
  have hev:riemannZeta =ᶠ[𝓝 s] f:=by
    have: ∀ᶠ z in 𝓝 s,z≠0 ∧ z≠1:=
      (isOpen_ne.eventually_mem h0).and (isOpen_ne.eventually_mem h1)
    filter_upwards [this] with z hz using mL hz.1 hz.2
  have hxi:xi s≠0:=by
    have:=mL h0 h1
    intro e; rw [e] at this; simp at this; exact hz this
  have hd:=(((fO s).hasDerivAt.const_mul (2:ℂ)).div
      (((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)))
      (mul_ne_zero h0 h1')).mul (differentiable_Gammaℝ_inv s).hasDerivAt
  have hd':HasDerivAt f _ s:=hd
  rw [logDeriv_apply,hev.deriv_eq,hev.eq_of_nhds,hd'.deriv,logDeriv_apply,logDeriv_apply,
    (DM hg).deriv]
  simp only [hf,id,Pi.mul_apply,Pi.div_apply]
  have hgi:(Gammaℝ s)⁻¹≠0:=inv_ne_zero hg
  field_simp
  ring
end aF.qO
end
end

-- aF.Lindelof
section
open Complex Real Set Filter
noncomputable section
namespace aF.Lindelof
lemma Aa {t:ℝ} (ht:t≠0) :
    Complex.Gamma (1-t* I)*(starRingEnd ℂ) (Complex.Gamma (1-t* I))
      =((Real.pi*t/Real.sinh (Real.pi*t) :ℝ) :ℂ) :=by
  have htI:(t:ℂ)* I≠0:=mul_ne_zero (ofReal_ne_zero.mpr ht) I_ne_zero
  have hc:(starRingEnd ℂ) (1-t* I)=t* I+1:=by
    simp [map_sub,map_mul,Complex.conj_ofReal,Complex.conj_I]; ring
  rw [← Complex.Gamma_conj,hc,Complex.Gamma_add_one _ htI]
  have hr:=Complex.Gamma_mul_Gamma_one_sub ((t:ℂ)* I)
  have hs:Complex.sin (Real.pi*((t:ℂ)* I))=((Real.sinh (Real.pi*t) :ℝ) :ℂ)* I:=by
    rw [← mul_assoc,show (Real.pi:ℂ)*t=((Real.pi*t:ℝ) :ℂ) by push_cast; ring,
      Complex.sin_mul_I,Complex.ofReal_sinh]
  have hsh:Real.sinh (Real.pi*t)≠0:=by
    rw [Ne,Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero ht
  rw [hs] at hr
  have aeg:((Real.sinh (Real.pi*t) :ℝ) :ℂ)≠0:=ofReal_ne_zero.mpr hsh
  calc Complex.Gamma (1-t* I)*(t* I*Complex.Gamma (t* I))
      =t* I*(Complex.Gamma (t* I)*Complex.Gamma (1-t* I)) :=by ring
    _=t* I*(Real.pi/(((Real.sinh (Real.pi*t) :ℝ) :ℂ)* I)) :=by rw [hr]
    _=((Real.pi*t/Real.sinh (Real.pi*t) :ℝ) :ℂ) :=by
        push_cast; field_simp
lemma Bv {t:ℝ} (ht:t≠0) :
    ‖Complex.Gamma (1-t* I)‖ ^2=Real.pi*t/Real.sinh (Real.pi*t) :=by
  have h:=Aa ht
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h
lemma Jp {t:ℝ} :
    ‖Complex.cos (Real.pi*(1-t* I)/2)‖ = |Real.sinh (Real.pi*t/2)| :=by
  have:Real.pi*(1-t* I)/2=(Real.pi/2:ℂ)-((Real.pi*t/2:ℝ) :ℂ)* I:=by
    push_cast; ring
  rw [this,Complex.cos_pi_div_two_sub,Complex.sin_mul_I, ← Complex.ofReal_sinh,norm_mul,
    Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
lemma Nb {t:ℝ} (ht:t≠0) :
    ‖riemannZeta (t* I)‖ ≤Real.sqrt |t| * ‖riemannZeta (1-t* I)‖ :=by
  have hn: ∀ n:ℕ,(1:ℂ)-t* I≠ -n:=by
    intro n h
    have:=congrArg Complex.re h
    simp at this
    linarith [n.cast_nonneg (α:=ℝ)]
  have h1:(1:ℂ)-t* I≠1:=by
    intro h
    have:=congrArg Complex.im h
    simp at this
    exact ht this
  have hfe:=riemannZeta_one_sub hn h1
  rw [show (1:ℂ)-(1-t* I)=t* I by ring] at hfe
  have hpow: ‖(2*(Real.pi:ℂ))^(-(1-t* I))‖ =(2*Real.pi)⁻¹:=by
    rw [show (2*(Real.pi:ℂ))=((2*Real.pi:ℝ) :ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [Real.rpow_neg_one]
  rw [hfe,norm_mul,norm_mul,norm_mul,norm_mul,hpow,Jp]
  set X:ℝ:= ‖Complex.Gamma (1-t* I)‖ * |Real.sinh (Real.pi*t/2)| with hX
  have hX0:0≤X:=by positivity
  set y:ℝ:=Real.pi*t/2 with hy
  have Zl:Real.sinh (Real.pi*t)=2*Real.sinh y*Real.cosh y:=by
    rw [← Real.sinh_two_mul]; congr 1; rw [hy]; ring
  have adI:0<Real.cosh y:=Real.cosh_pos y
  have hty:t*Real.sinh y≤ |t| *Real.cosh y:=by
    have hsl: |Real.sinh y| ≤Real.cosh y:=by
      have:=Real.cosh_sq y
      rw [abs_le]; constructor <;> nlinarith [Real.cosh_pos y]
    calc t*Real.sinh y≤ |t*Real.sinh y| :=le_abs_self _
      _= |t| * |Real.sinh y| :=abs_mul _ _
      _≤ |t| *Real.cosh y:=by gcongr
  have hsy:Real.sinh y≠0:=by
    rw [Ne,Real.sinh_eq_zero,hy]; exact div_ne_zero (mul_ne_zero Real.pi_ne_zero ht) two_ne_zero
  have hX2:X^2≤Real.pi^2* |t| :=by
    have hG:=Bv ht
    have:X^2=Real.pi*(t*Real.sinh y)/(2*Real.cosh y) :=by
      rw [hX,mul_pow,sq_abs,hG,Zl]
      field_simp
    rw [this,div_le_iff₀ (by positivity)]
    have hπ:1≤Real.pi:=by linarith [Real.pi_gt_three]
    have h0:0≤ |t| *Real.cosh y:=by positivity
    have h3:Real.pi*(t*Real.sinh y)≤Real.pi*(|t| *Real.cosh y) :=
      mul_le_mul_of_nonneg_left hty Real.pi_pos.le
    have h4:0≤(Real.pi^2*2 -Real.pi)*(|t| *Real.cosh y) :=
      mul_nonneg (by nlinarith) h0
    nlinarith
  have aeh:X≤Real.pi*Real.sqrt |t| :=by
    rw [← Real.sqrt_sq hX0, ← Real.sqrt_sq Real.pi_pos.le, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt hX2
  have hz:0≤ ‖riemannZeta (1-t* I)‖ :=norm_nonneg _
  have h2: ‖(2:ℂ)‖ =2:=by simp
  rw [h2]
  calc 2*(2*Real.pi)⁻¹* ‖Complex.Gamma (1-t* I)‖ * |Real.sinh (Real.pi*t/2)|
        * ‖riemannZeta (1-t* I)‖
      =X/Real.pi* ‖riemannZeta (1-t* I)‖ :=by
        rw [hX,hy]; field_simp
    _≤Real.sqrt |t| * ‖riemannZeta (1-t* I)‖ :=by
        gcongr
        rw [div_le_iff₀ Real.pi_pos]; linarith
lemma Ac {s:ℂ} (hs:0<s.re) : ‖Complex.Gamma s‖ ≤Real.Gamma s.re:=by
  rw [Complex.Gamma_eq_integral hs,Complex.GammaIntegral,Real.Gamma_eq_integral hs]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx=>?_)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp
lemma PW {σ:ℝ} (h0:0<σ) (h1:σ≤1) :Real.Gamma σ≤1/σ:=by
  have hadd:=Real.Gamma_add_one h0.ne'
  have hle:Real.Gamma (σ+1)≤1:=by
    have hseg:σ+1∈segment ℝ (1:ℝ) 2:=by
      rw [segment_eq_Icc (by norm_num)]; constructor <;> linarith
    have:=Real.convexOn_Gamma.le_on_segment (by norm_num:(1:ℝ)∈Ioi 0)
      (by norm_num:(2:ℝ)∈Ioi 0) hseg
    have h2:Real.Gamma 2=1:=by
      rw [show (2:ℝ)=1+1 by norm_num,Real.Gamma_add_one one_ne_zero,Real.Gamma_one]; ring
    rw [Real.Gamma_one,h2,max_self] at this
    exact this
  rw [le_div_iff₀ h0,mul_comm, ← hadd]
  exact hle
lemma Ly (z:ℂ) : ‖Complex.cos z‖ ≤Real.exp |z.im| :=by
  rw [Complex.cos]
  have h1: ‖Complex.exp (z* I)‖ =Real.exp (-z.im) :=by rw [Complex.norm_exp]; simp
  have h2: ‖Complex.exp (-z* I)‖ =Real.exp z.im:=by rw [Complex.norm_exp]; simp
  rw [norm_div,Complex.norm_two]
  calc ‖Complex.exp (z* I)+Complex.exp (-z* I)‖ /2
      ≤(‖Complex.exp (z* I)‖ + ‖Complex.exp (-z* I)‖)/2:=by gcongr; exact norm_add_le _ _
    _=(Real.exp (-z.im)+Real.exp z.im)/2:=by rw [h1,h2]
    _≤Real.exp |z.im| :=by
        have:=Real.exp_le_exp.mpr (neg_le_abs z.im)
        have:=Real.exp_le_exp.mpr (le_abs_self z.im)
        linarith
lemma lC {s:ℂ} (h0:1/2≤ s.re) (h1:s.re≤1) (ht:2≤ |s.im|) :
    ‖riemannZeta s‖ ≤2+4* |s.im| :=by
  set σ:=s.re with hσ
  set t:=s.im with ht'
  have hs:s=σ+t* I:=(Complex.re_add_im s).symm
  have oC:0<σ:=by linarith
  have ht0:t≠0:=by intro h; rw [h] at ht; norm_num at ht
  have hs1:s≠1:=by intro h; apply ht0; rw [ht',h]; simp
  have hs0:s≠0:=by intro h; apply ht0; rw [ht',h]; simp
  rw [← qW (N:=1) one_pos (by rw [← hσ]; exact oC) hs1,qZ]
  have hD:=DY 1 le_rfl ⟨oC,by linarith⟩ ht
  simp only [gT,Nat.cast_one,Real.one_rpow,mul_one] at hD
  rw [← hs] at hD
  have hA: ∑ n∈Finset.range (1+1),1/(n:ℂ)^s=1:=by
    simp [Finset.sum_range_succ,Complex.zero_cpow hs0]
  have h1s: ‖(1:ℂ)-s‖ ≥2:=by
    calc ‖(1:ℂ)-s‖ ≥ |((1:ℂ)-s).im| :=Complex.abs_im_le_norm _
      _= |t| :=by simp [ht']
      _≥2:=ht
  have hB: ‖-((1:ℕ) :ℂ)^(1-s)/(1-s)‖ ≤1/2:=by
    rw [Nat.cast_one,Complex.one_cpow,norm_div,norm_neg,norm_one]
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hC: ‖-((1:ℕ) :ℂ)^(-s)/2‖ =1/2:=by
    rw [Nat.cast_one,Complex.one_cpow]; simp
  rw [hA]
  calc ‖1+(-((1:ℕ) :ℂ)^(1-s)/(1-s)+ -((1:ℕ) :ℂ)^(-s)/2+
        s* ∫ x in Ioi ((1:ℕ) :ℝ),(⌊x⌋ +1/2 -x)*(x:ℂ)^(-(s+1)))‖
      ≤ ‖(1:ℂ)‖ +(‖-((1:ℕ) :ℂ)^(1-s)/(1-s)‖ + ‖-((1:ℕ) :ℂ)^(-s)/2‖ +
        ‖s* ∫ x in Ioi ((1:ℕ) :ℝ),(⌊x⌋ +1/2 -x)*(x:ℂ)^(-(s+1))‖) :=by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_add_le _ _
    _≤1+(1/2+1/2+2* |t| /σ) :=by
        rw [norm_one,hC]
        gcongr
        simpa using hD
    _≤2+4* |s.im| :=by
        rw [← ht']
        have:2* |t| /σ≤4* |t| :=by
          rw [div_le_iff₀ oC]; nlinarith [abs_nonneg t]
        linarith
lemma EH {s:ℂ} (h0:0≤ s.re) (h1:s.re≤1) (ht:2≤ |s.im|) :
    ‖riemannZeta s‖ ≤4*(2+4* |s.im|)*Real.exp (2* |s.im|) :=by
  have hpos:0≤2+4* |s.im| :=by positivity
  have adJ:1≤Real.exp (2* |s.im|) :=Real.one_le_exp (by positivity)
  rcases le_or_gt (1/2) s.re with hh | hh
  · have:=lC hh h1 ht
    nlinarith
  set w:ℂ:=1-s with hw
  have pC:w.re=1-s.re:=by simp [hw]
  have Ci:w.im= -s.im:=by simp [hw]
  have hwn: ∀ n:ℕ,w≠ -n:=by
    intro n h
    have:=congrArg Complex.re h
    simp only [Complex.neg_re,Complex.natCast_re] at this
    linarith [n.cast_nonneg (α:=ℝ)]
  have hw1:w≠1:=by
    intro h
    have:=congrArg Complex.im h
    rw [Ci] at this; simp at this
    rw [this] at ht; norm_num at ht
  have hfe:=riemannZeta_one_sub hwn hw1
  rw [show 1-w=s by simp [hw]] at hfe
  have VK: ‖riemannZeta w‖ ≤2+4* |s.im| :=by
    have:=lC (s:=w) (by rw [pC]; linarith) (by rw [pC]; linarith)
      (by rw [Ci,abs_neg]; exact ht)
    rwa [Ci,abs_neg] at this
  have hpow: ‖(2*(Real.pi:ℂ))^(-w)‖ ≤1:=by
    rw [show (2*(Real.pi:ℂ))=((2*Real.pi:ℝ) :ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp [pC]; linarith
  have hΓ: ‖Complex.Gamma w‖ ≤2:=by
    refine (Ac (by rw [pC]; linarith)).trans ?_
    rw [pC]
    refine (PW (by linarith) (by linarith)).trans ?_
    rw [div_le_iff₀ (by linarith)]; linarith
  have hcos: ‖Complex.cos (Real.pi*w/2)‖ ≤Real.exp (2* |s.im|) :=by
    refine (Ly _).trans (Real.exp_le_exp.mpr ?_)
    have:(↑Real.pi*w/2).im=Real.pi*w.im/2:=by simp
    rw [this,Ci,abs_div,abs_mul,abs_neg,abs_of_pos Real.pi_pos,abs_two]
    have:=abs_nonneg s.im
    nlinarith [Real.pi_lt_four]
  rw [hfe,norm_mul,norm_mul,norm_mul,norm_mul,Complex.norm_two]
  calc 2* ‖(2*(Real.pi:ℂ))^(-w)‖ * ‖Complex.Gamma w‖ * ‖Complex.cos (Real.pi*w/2)‖
        * ‖riemannZeta w‖
      ≤2*1*2*Real.exp (2* |s.im|)*(2+4* |s.im|) :=by gcongr
    _=4*(2+4* |s.im|)*Real.exp (2* |s.im|) :=by ring
abbrev F:ℂ→ℂ:=riemannZeta₁
lemma F_eq {s:ℂ} (hs:s≠1) :F s=(s-1)*riemannZeta s:=by
  rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc,mul_inv_cancel₀ (sub_ne_zero.mpr hs),one_mul]
lemma wQ:Continuous F:=differentiable_riemannZeta₁.continuous
lemma gG {t:ℝ} :1≤Real.log (|t| +3) :=by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9,abs_nonneg t])
lemma Oe: ∃ K:ℝ,0≤K ∧ ∀ t:ℝ,
    ‖F (1+t* I)‖ ≤K*(1+ |t|)^(1:ℝ)*Real.log (|t| +3) ∧
    ‖F (t* I)‖ ≤K*(1+ |t|)^(3/2:ℝ)*Real.log (|t| +3) :=by
  obtain ⟨A,hA,C,hC,SX⟩:=DZ
  have Zm:IsCompact (Set.Icc (-3:ℝ) 3) :=isCompact_Icc
  obtain ⟨M1,hM1⟩:=Zm.exists_bound_of_continuousOn
    (f:=fun t:ℝ=>F (1+t* I)) (wQ.comp (by fun_prop)).continuousOn
  obtain ⟨M0,hM0⟩:=Zm.exists_bound_of_continuousOn
    (f:=fun t:ℝ=>F (t* I)) (wQ.comp (by fun_prop)).continuousOn
  refine ⟨max (max M1 M0) C,by positivity,fun t=>?_⟩
  have hl:=gG (t:=t)
  have h1t:(1:ℝ)≤1+ |t| :=le_add_of_nonneg_right (abs_nonneg t)
  have hp1:1≤(1+ |t|)^(1:ℝ) :=Real.one_le_rpow h1t (by norm_num)
  have hp3:1≤(1+ |t|)^(3/2:ℝ) :=Real.one_le_rpow h1t (by norm_num)
  have hK0:0≤ max (max M1 M0) C:=by positivity
  rcases le_or_gt |t| 3 with ht | ht
  · have hmem:t∈Set.Icc (-3:ℝ) 3:=abs_le.mp ht
    have h1:=hM1 t hmem
    have h0:=hM0 t hmem
    constructor
    · calc ‖F (1+t* I)‖ ≤ max (max M1 M0) C:=h1.trans (by simp)
        _=max (max M1 M0) C*1*1:=by ring
        _≤_:=by gcongr
    · calc ‖F (t* I)‖ ≤ max (max M1 M0) C:=h0.trans (by simp)
        _=max (max M1 M0) C*1*1:=by ring
        _≤_:=by gcongr
  have ht0:t≠0:=by intro h; rw [h] at ht; norm_num at ht
  have FH:Real.log |t| ≤Real.log (|t| +3) :=
    Real.log_le_log (by linarith) (by linarith)
  have Oo:0≤Real.log |t| :=Real.log_nonneg (by linarith)
  have hCK:C≤ max (max M1 M0) C:=le_max_right _ _
  constructor
  · have hne:(1:ℂ)+t* I≠1:=by
      intro h; have:=congrArg Complex.im h; simp at this; exact ht0 this
    rw [F_eq hne,norm_mul,show (1:ℂ)+t* I-1=t* I by ring,norm_mul,Complex.norm_I,
      mul_one,Complex.norm_real,Real.norm_eq_abs,Real.rpow_one]
    have hz:=SX 1 t ht ⟨by
      have:0<A/Real.log |t| :=div_pos hA.1 (Real.log_pos (by linarith))
      linarith,by norm_num⟩
    push_cast at hz
    calc |t| * ‖riemannZeta (1+t* I)‖ ≤(1+ |t|)*(C*Real.log |t|) :=by
          gcongr; linarith
      _≤ max (max M1 M0) C*(1+ |t|)*Real.log (|t| +3) :=by
          have:0≤1+ |t| :=by positivity
          calc (1+ |t|)*(C*Real.log |t|)=C*(1+ |t|)*Real.log |t| :=by ring
            _≤ max (max M1 M0) C*(1+ |t|)*Real.log (|t| +3) :=by gcongr
  · have hne:(t:ℂ)* I≠1:=by
      intro h; have:=congrArg Complex.re h; simp at this
    rw [F_eq hne,norm_mul]
    have hz:=Nb ht0
    have hz': ‖riemannZeta (1-t* I)‖ ≤C*Real.log |t| :=by
      have:=SX 1 (-t) (by rwa [abs_neg]) ⟨by
        have:0<A/Real.log |-t| :=div_pos hA.1 (Real.log_pos (by rw [abs_neg]; linarith))
        linarith,by norm_num⟩
      push_cast at this
      rw [abs_neg] at this
      simpa [sub_eq_add_neg] using this
    have hn1: ‖(t:ℂ)* I-1‖ ≤1+ |t| :=by
      refine (norm_sub_le _ _).trans ?_
      simp [Complex.norm_real]; linarith
    have hsq:Real.sqrt |t| ≤(1+ |t|)^(1/2:ℝ) :=by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by norm_num)
    have hsplit:(1+ |t|)^(3/2:ℝ)=(1+ |t|)*(1+ |t|)^(1/2:ℝ) :=by
      rw [show (3/2:ℝ)=1+1/2 by norm_num,
        Real.rpow_add (by positivity),Real.rpow_one]
    rw [hsplit]
    calc ‖(t:ℂ)* I-1‖ * ‖riemannZeta (t* I)‖
        ≤(1+ |t|)*(Real.sqrt |t| *(C*Real.log |t|)) :=by
          gcongr
          exact hz.trans (by gcongr)
      _≤(1+ |t|)*((1+ |t|)^(1/2:ℝ)*(max (max M1 M0) C*Real.log (|t| +3))) :=by
          gcongr
      _=_:=by ring
lemma bound_aux {u:ℝ} :(1+ |u|)^3*Real.exp (-u^2)≤Real.exp (9/4) :=by
  have h1:1+ |u| ≤Real.exp |u| :=by linarith [Real.add_one_le_exp |u|]
  have h3:(1+ |u|)^3≤Real.exp (3* |u|) :=by
    calc (1+ |u|)^3≤Real.exp |u| ^3:=by gcongr
      _=Real.exp (3* |u|) :=by rw [← Real.exp_nat_mul]; norm_num
  calc (1+ |u|)^3*Real.exp (-u^2)≤Real.exp (3* |u|)*Real.exp (-u^2) :=by gcongr
    _=Real.exp (3* |u| -u^2) :=by rw [← Real.exp_add]; ring_nf
    _≤Real.exp (9/4) :=by
        apply Real.exp_le_exp.mpr
        have:u^2= |u| ^2:=(sq_abs u).symm
        nlinarith [sq_nonneg (|u| -3/2)]
lemma SY {x:ℝ} (hx:0≤x) :
    (1+x)*(4*(2+4*x)*Real.exp (2*x))*Real.exp 1≤Real.exp (5*Real.exp (2*x)) :=by
  have h1:1+x≤Real.exp x:=by linarith [Real.add_one_le_exp x]
  have h2:2+4*x≤2*Real.exp (2*x) :=by linarith [Real.add_one_le_exp (2*x)]
  have h8:(8:ℝ)≤Real.exp 3:=by
    have:=Real.add_one_le_exp 1
    have he:Real.exp 3=Real.exp 1^3:=by rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    calc (8:ℝ)=2^3:=by norm_num
      _≤Real.exp 1^3:=by gcongr; linarith
  have hx2:4+5*x≤5*Real.exp (2*x) :=by
    have:=Real.add_one_le_exp (2*x); nlinarith
  calc (1+x)*(4*(2+4*x)*Real.exp (2*x))*Real.exp 1
      ≤Real.exp x*(4*(2*Real.exp (2*x))*Real.exp (2*x))*Real.exp 1:=by
        gcongr
    _=8*Real.exp (5*x+1) :=by
        rw [show 5*x+1=x+2*x+2*x+1 by ring,Real.exp_add,Real.exp_add,
          Real.exp_add]; ring
    _≤Real.exp 3*Real.exp (5*x+1) :=by gcongr
    _=Real.exp (4+5*x) :=by rw [← Real.exp_add]; ring_nf
    _≤Real.exp (5*Real.exp (2*x)) :=Real.exp_le_exp.mpr hx2
end aF.Lindelof
end
end

-- aF.lN
section
open Complex Real Set Filter Topology
noncomputable section
namespace aF.lN
lemma gO (hRH:RiemannHypothesis) {s:ℂ} (hs:1/2<s.re) (h1:s≠1) :
    riemannZeta s≠0:=by
  intro hz
  have:=hRH s hz (by
    rintro ⟨n,rfl⟩
    have:(-2*((n:ℂ)+1)).re<0:=by simp; positivity
    linarith) h1
  linarith
lemma tP (n:ℕ) (s:ℂ) :
    ‖1/((n:ℂ)+1)^s‖ =1/((n:ℝ)+1)^s.re:=by
  rw [norm_div,norm_one,show ((n:ℂ)+1)=((n+1:ℕ) :ℂ) by push_cast; ring,
    Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n)]
  push_cast; ring
lemma summable_one_div_rpow {σ:ℝ} (hσ:1<σ) :
    Summable (fun n:ℕ=>1/((n:ℝ)+1)^σ) :=by
  have h:=(Real.summable_one_div_nat_rpow.mpr hσ)
  have:=(summable_nat_add_iff 1).mpr h
  simpa [Nat.cast_add,Nat.cast_one] using this
lemma rE {σ₀:ℝ} (hσ₀:1<σ₀) {s:ℂ} (hs:σ₀≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n:ℕ,1/((n:ℝ)+1)^σ₀:=by
  have hs1:1<s.re:=by linarith
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs1]
  have hsum:=summable_one_div_rpow hσ₀
  have hle: ∀ n:ℕ, ‖1/((n:ℂ)+1)^s‖ ≤1/((n:ℝ)+1)^σ₀:=fun n=>by
    rw [tP]
    gcongr
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  refine (norm_tsum_le_tsum_norm (hsum.of_nonneg_of_le (fun _=>norm_nonneg _) hle)).trans ?_
  exact Summable.tsum_le_tsum hle (hsum.of_nonneg_of_le (fun _=>norm_nonneg _) hle) hsum
lemma gX {s:ℂ} (hs:2≤ s.re) : ‖riemannZeta s-1‖ ≤Real.pi^2/6-1:=by
  have hs1:1<s.re:=by linarith
  have hsum2:=summable_one_div_rpow (σ:=2) (by norm_num)
  have hle: ∀ n:ℕ, ‖1/((n:ℂ)+1)^s‖ ≤1/((n:ℝ)+1)^(2:ℝ) :=fun n=>by
    rw [tP]
    gcongr
    · exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hsC:Summable (fun n:ℕ=>1/((n:ℂ)+1)^s) :=
    Summable.of_norm (hsum2.of_nonneg_of_le (fun _=>norm_nonneg _) hle)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs1,hsC.tsum_eq_zero_add]
  simp only [Nat.cast_zero,zero_add,one_cpow,div_one,add_sub_cancel_left]
  have hle': ∀ n:ℕ, ‖1/((((n+1:ℕ) :ℂ))+1)^s‖ ≤1/(((n+1:ℕ) :ℝ)+1)^(2:ℝ) :=
    fun n=>hle (n+1)
  have PX:=(summable_nat_add_iff 1).mpr hsum2
  refine (norm_tsum_le_tsum_norm ((PX.of_nonneg_of_le (fun _=>norm_nonneg _) hle'))).trans ?_
  refine (Summable.tsum_le_tsum hle' (PX.of_nonneg_of_le (fun _=>norm_nonneg _) hle') PX).trans ?_
  have hz:=hasSum_zeta_two
  have h1:HasSum (fun n:ℕ=>(1:ℝ)/((n+1:ℕ) :ℝ)^2) (Real.pi^2/6) :=by
    have:=(hasSum_nat_add_iff' 1).mpr hz
    simpa using this
  have h2:=(hasSum_nat_add_iff' 1).mpr h1
  simp only [Finset.range_one,Finset.sum_singleton,Nat.cast_add,Nat.cast_one,Nat.cast_zero,
    zero_add,one_pow,div_one] at h2
  refine le_of_eq ?_
  rw [← h2.tsum_eq]
  refine tsum_congr fun n=>?_
  push_cast
  rw [Real.rpow_two]
lemma EI {s:ℂ} (hs:2≤ s.re) :1/3≤ ‖riemannZeta s‖ :=by
  have h:=gX hs
  have hpi:Real.pi^2<10:=by nlinarith [Real.pi_lt_d2,Real.pi_pos]
  have:=norm_sub_norm_le (1:ℂ) (1-riemannZeta s)
  rw [norm_one,sub_sub_cancel] at this
  have h': ‖1-riemannZeta s‖ = ‖riemannZeta s-1‖ :=norm_sub_rev _ _
  linarith
lemma wR: ∃ K:ℝ,1≤K ∧ ∀ s:ℂ,1/2≤ s.re→4≤ |s.im| →
    ‖riemannZeta s‖ ≤K* |s.im| :=by
  obtain ⟨A,hA,C,hC,SX⟩:=DZ
  refine ⟨max 5 C,le_trans (by norm_num) (le_max_left _ _),fun s h0 ht=>?_⟩
  have hK5:(5:ℝ)≤ max 5 C:=le_max_left _ _
  have hKC:C≤ max 5 C:=le_max_right _ _
  rcases le_or_gt s.re 1 with h1 | h1
  · have:=Lindelof.lC h0 h1 (by linarith)
    nlinarith
  rcases le_or_gt s.re 2 with h2 | h2
  · have hs:(s.re:ℂ)+s.im* I=s:=Complex.re_add_im s
    have hl:0<Real.log |s.im| :=Real.log_pos (by linarith)
    have:=SX s.re s.im (by linarith) ⟨by
      have:0<A/Real.log |s.im| :=div_pos hA.1 hl
      linarith,h2⟩
    rw [hs] at this
    have hlog:Real.log |s.im| ≤ |s.im| :=
      (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    exact this.trans (mul_le_mul hKC hlog hl.le (by linarith))
  · have h:=gX h2.le
    have hpi:Real.pi^2<10:=by nlinarith [Real.pi_lt_d2,Real.pi_pos]
    have h3:=norm_le_norm_sub_add (riemannZeta s) 1
    rw [norm_one] at h3
    nlinarith
lemma CY {J:ℂ→ℂ} {R M r:ℝ} (hM:0<M) (hJ:DifferentiableOn ℂ J (Metric.ball 0 R))
    (hre: ∀ z∈Metric.ball (0:ℂ) R,(J z).re≤M) (h0:J 0=0) (hr0:0≤r) (hr:r<R)
    {z:ℂ} (hz: ‖z‖ ≤r) : ‖J z‖ ≤2*M*r/(R-r) :=by
  have hR:0<R:=by linarith
  have hzb:z∈Metric.ball (0:ℂ) R:=mem_ball_zero_iff.mpr (by linarith)
  refine (Complex.borelCaratheodory_zero hM hJ (fun w hw=>hre w hw) hR hzb h0).trans ?_
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg hM.le hR.le) (sub_nonneg.mpr hz)]
lemma Dr {J:ℂ→ℂ} {R r₁ r₂ r₃ a b:ℝ} (h1:0<r₁) (h12:r₁≤r₂) (h23:r₂≤r₃)
    (h13:r₁<r₃) (h3R:r₃<R) (hJ:DifferentiableOn ℂ J (Metric.ball 0 R))
    (ha: ∀ z:ℂ, ‖z‖ =r₁→ ‖J z‖ ≤a) (hb: ∀ z:ℂ, ‖z‖ =r₃→ ‖J z‖ ≤b)
    {z:ℂ} (hz: ‖z‖ =r₂) :
    ‖J z‖ ≤a^(1-(Real.log r₂-Real.log r₁)/(Real.log r₃-Real.log r₁))*
      b^((Real.log r₂-Real.log r₁)/(Real.log r₃-Real.log r₁)) :=by
  have hz0:z≠0:=by
    intro h; rw [h,norm_zero] at hz; linarith
  set g:ℂ→ℂ:=fun w=>J (Complex.exp w) with hg
  have hlu:Real.log r₁<Real.log r₃:=Real.log_lt_log h1 h13
  have hexp: ∀ w:ℂ, ‖Complex.exp w‖ =Real.exp w.re:=Complex.norm_exp
  have hdiff: ∀ w:ℂ,w.re≤Real.log r₃→DifferentiableAt ℂ g w:=by
    intro w hw
    have hmem:Complex.exp w∈Metric.ball (0:ℂ) R:=by
      rw [mem_ball_zero_iff,hexp]
      calc Real.exp w.re≤Real.exp (Real.log r₃) :=Real.exp_le_exp.mpr hw
        _=r₃:=Real.exp_log (by linarith)
        _<R:=h3R
    exact (hJ.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)).comp w
      Complex.differentiableAt_exp
  have hcl:closure (Complex.HadamardThreeLines.verticalStrip (Real.log r₁) (Real.log r₃))⊆
      Complex.HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₃) :=
    closure_minimal (Set.preimage_mono Set.Ioo_subset_Icc_self)
      (isClosed_Icc.preimage Complex.continuous_re)
  have hd:DiffContOnCl ℂ g
      (Complex.HadamardThreeLines.verticalStrip (Real.log r₁) (Real.log r₃)) :=
    ⟨fun w hw=>(hdiff w (le_of_lt hw.2)).differentiableWithinAt,
     fun w hw=>(hdiff w (hcl hw).2).continuousAt.continuousWithinAt⟩
  obtain ⟨Mb,hMb⟩:=(isCompact_closedBall (0:ℂ) r₃).exists_bound_of_continuousOn
    (hJ.continuousOn.mono (Metric.closedBall_subset_ball h3R))
  have hB:BddAbove ((norm∘g) ''
      Complex.HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₃)) :=by
    refine ⟨Mb,?_⟩
    rintro _ ⟨w,hw,rfl⟩
    have hwm:Complex.exp w∈Metric.closedBall (0:ℂ) r₃:=by
      rw [mem_closedBall_zero_iff,hexp]
      calc Real.exp w.re≤Real.exp (Real.log r₃) :=Real.exp_le_exp.mpr hw.2
        _=r₃:=Real.exp_log (by linarith)
    exact hMb _ hwm
  have hlz:Complex.log z∈
      Complex.HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₃) :=by
    show (Complex.log z).re∈Set.Icc _ _
    rw [Complex.log_re,hz]
    exact ⟨Real.log_le_log h1 h12,Real.log_le_log (by linarith) h23⟩
  have key:=Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f:=g) (a:=a) (b:=b) hlu hlz hd hB
    (fun w hw=>by
      have hw':w.re=Real.log r₁:=hw
      apply ha
      rw [hexp,hw',Real.exp_log h1])
    (fun w hw=>by
      have hw':w.re=Real.log r₃:=hw
      apply hb
      rw [hexp,hw',Real.exp_log (by linarith)])
  simp only [g,Complex.exp_log hz0,Complex.log_re,hz] at key
  exact key
def Z (σ:ℝ) :ℝ:= ∑' n:ℕ,1/((n:ℝ)+1)^σ
lemma qP (σ:ℝ) :0≤Z σ:=tsum_nonneg fun n=>by positivity
def theta (δ:ℝ) :ℝ:=
  (Real.log (3/2 -2*δ)-Real.log (1/2))/(Real.log (3/2 -δ)-Real.log (1/2))
lemma theta_nonneg {δ:ℝ} (hδ:δ≤1/4) :0≤theta δ:=by
  unfold theta
  apply div_nonneg
  · linarith [Real.log_le_log (by norm_num:(0:ℝ)<1/2) (show (1:ℝ)/2≤3/2 -2*δ by linarith)]
  · linarith [Real.log_le_log (by norm_num:(0:ℝ)<1/2) (show (1:ℝ)/2≤3/2 -δ by linarith)]
lemma wS {δ:ℝ} (hδ0:0<δ) (hδ:δ≤1/4) :theta δ<1:=by
  unfold theta
  have h1:Real.log (1/2)<Real.log (3/2 -δ) :=Real.log_lt_log (by norm_num) (by linarith)
  have h2:Real.log (3/2 -2*δ)<Real.log (3/2 -δ) :=
    Real.log_lt_log (by linarith) (by linarith)
  rw [div_lt_one (by linarith)]; linarith
lemma Gt (hRH:RiemannHypothesis) {δ:ℝ} (hδ0:0<δ) (hδ:δ≤1/4)
    {K:ℝ} (hK:1≤K)
    (PY: ∀ s:ℂ,1/2≤ s.re→4≤ |s.im| → ‖riemannZeta s‖ ≤K* |s.im|)
    {t:ℝ} (ht:6≤t) :
    ‖riemannZeta (((1/2+2*δ:ℝ) :ℂ)+t* I)‖ ≤
      2*Real.exp ((4*Real.log (3*(Z (5/4)+1)))^(1-theta δ)*
        (6*Real.log (6*K*t)/δ)^(theta δ)) ∧
    ‖riemannZeta (((1/2+2*δ:ℝ) :ℂ)+t* I)‖⁻¹≤
      3*Real.exp ((4*Real.log (3*(Z (5/4)+1)))^(1-theta δ)*
        (6*Real.log (6*K*t)/δ)^(theta δ)) :=by
  set c:ℂ:=2+t* I with hc
  set B:ℂ→ℂ:=fun z=>riemannZeta (c+z) with hB
  set R:ℝ:=3/2 -δ/4 with hR
  have hre: ∀ z:ℂ,(c+z).re=2+z.re:=fun z=>by simp [hc]
  have him: ∀ z:ℂ,(c+z).im=t+z.im:=fun z=>by simp [hc]
  have hzre: ∀ z:ℂ, -‖z‖ ≤z.re:=fun z=>by
    linarith [neg_abs_le z.re,Complex.abs_re_le_norm z]
  have hzim: ∀ z:ℂ, |z.im| ≤ ‖z‖ :=Complex.abs_im_le_norm
  have hne1: ∀ z:ℂ, ‖z‖ ≤3/2→c+z≠1:=by
    intro z hz h
    have h':=congrArg Complex.im h
    rw [him] at h'
    simp only [Complex.one_im] at h'
    have:=(abs_le.mp ((hzim z).trans hz)).1
    linarith
  have Wq:AnalyticOnNhd ℂ B (Metric.closedBall 0 R) :=by
    intro z hz
    have hzR: ‖z‖ ≤R:=mem_closedBall_zero_iff.mp hz
    have hU:{w:ℂ | c+w≠1}∈𝓝 z:=
      (isOpen_ne_fun (continuous_const.add continuous_id) continuous_const).mem_nhds
        (hne1 z (by linarith))
    refine DifferentiableOn.analyticAt (s:={w:ℂ | c+w≠1}) (fun w hw=>?_) hU
    exact ((differentiableAt_riemannZeta hw).comp w
      ((differentiableAt_const c).add differentiableAt_id)).differentiableWithinAt
  have Jq: ∀ z∈Metric.closedBall (0:ℂ) R,B z≠0:=by
    intro z hz
    have hzR: ‖z‖ ≤R:=mem_closedBall_zero_iff.mp hz
    refine gO hRH ?_ (hne1 z (by linarith))
    rw [hre]; linarith [hzre z]
  obtain ⟨J,Wr,hJ0, -,Ez⟩:=jG (r:=1) one_pos (by linarith) Wq Jq
  have hJd:DifferentiableOn ℂ J (Metric.ball 0 R) :=Wr.differentiableOn
  have Lz:(2:ℝ)≤(c+0).re:=by rw [hre]; simp
  have LD:1/3≤ ‖B 0‖ :=EI Lz
  have WZ: ‖B 0‖ ≤2:=by
    have h1:=gX Lz
    have hpi:Real.pi^2<10:=by nlinarith [Real.pi_lt_d2,Real.pi_pos]
    have h2:=norm_le_norm_sub_add (B 0) 1
    rw [norm_one] at h2
    have: ‖B 0-1‖ ≤Real.pi^2/6-1:=h1
    linarith
  have PZ: ∀ z∈Metric.ball (0:ℂ) R, ∀ U:ℝ,0<U→ ‖B z‖ ≤U→
      (J z).re≤Real.log (3*U) :=by
    intro z hz U hU hBz
    rw [← Ez z hz]
    have Qa:0< ‖B z‖ :=norm_pos_iff.mpr (Jq z (Metric.ball_subset_closedBall hz))
    have Jt:0< ‖B 0‖ :=by linarith
    rw [← Real.log_div Qa.ne' Jt.ne']
    apply Real.log_le_log (div_pos Qa Jt)
    rw [div_le_iff₀ Jt]
    nlinarith [mul_le_mul_of_nonneg_left LD (by linarith:(0:ℝ)≤3*U)]
  set M₁:ℝ:=Real.log (3*(Z (5/4)+1)) with hM₁
  have Jv:0<M₁:=Real.log_pos (by linarith [qP (5/4)])
  have Jw: ∀ w∈Metric.ball (0:ℂ) (3/4),(J w).re≤M₁:=by
    intro w hw
    have hw': ‖w‖ <3/4:=mem_ball_zero_iff.mp hw
    refine PZ w (Metric.ball_subset_ball (by linarith) hw) (Z (5/4)+1)
      (by linarith [qP (5/4)]) ?_
    exact (rE (σ₀:=5/4) (s:=c+w) (by norm_num)
      (by rw [hre]; linarith [hzre w])).trans (le_add_of_nonneg_right zero_le_one)
  have hinner: ∀ z:ℂ, ‖z‖ ≤1/2→ ‖J z‖ ≤4*M₁:=by
    intro z hz
    have:=CY (J:=J) (R:=3/4) (r:=1/2) Jv
      (hJd.mono (Metric.ball_subset_ball (by linarith))) Jw hJ0 (by norm_num) (by norm_num) hz
    have e:2*M₁*(1/2)/(3/4-1/2)=4*M₁:=by ring
    linarith
  set M₃:ℝ:=Real.log (6*K*t) with hM₃
  have wT:0<M₃:=Real.log_pos (by nlinarith)
  have Jx: ∀ w∈Metric.ball (0:ℂ) (3/2 -δ/2),(J w).re≤M₃:=by
    intro w hw
    have hw': ‖w‖ <3/2 -δ/2:=mem_ball_zero_iff.mp hw
    have h6:6*K*t=3*(2*K*t) :=by ring
    rw [hM₃,h6]
    refine PZ w (Metric.ball_subset_ball (by linarith) hw) _ (by positivity) ?_
    have hi:=abs_le.mp ((hzim w).trans hw'.le)
    have OT:4≤ |(c+w).im| :=by rw [him,abs_of_pos (by linarith)]; linarith
    refine (PY (c+w) (by rw [hre]; linarith [hzre w]) OT).trans ?_
    rw [him,abs_of_pos (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left (show w.im≤t by linarith) (by linarith:(0:ℝ)≤K)]
  have Qb: ∀ z:ℂ, ‖z‖ ≤3/2 -δ→ ‖J z‖ ≤6*M₃/δ:=by
    intro z hz
    have:=CY (J:=J) wT (hJd.mono (Metric.ball_subset_ball (by linarith))) Jx
      hJ0 (by linarith) (by linarith) hz
    refine this.trans ?_
    rw [div_le_div_iff₀ (by linarith) hδ0]
    nlinarith [mul_pos wT (mul_pos hδ0 hδ0)]
  set z₂:ℂ:= -(((3/2 -2*δ:ℝ)) :ℂ) with hz₂
  have hr2: ‖z₂‖ =3/2 -2*δ:=by
    rw [hz₂,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
  have h3c:=Dr (J:=J) (R:=R) (r₁:=1/2) (r₂:=3/2 -2*δ)
    (r₃:=3/2 -δ) (a:=4*M₁) (b:=6*M₃/δ) (by norm_num) (by linarith) (by linarith)
    (by linarith) (by linarith) hJd (fun z hz=>hinner z hz.le) (fun z hz=>Qb z hz.le) hr2
  have hcz:c+z₂=((1/2+2*δ:ℝ) :ℂ)+t* I:=by
    rw [hc,hz₂]; push_cast; ring
  have Nc:z₂∈Metric.ball (0:ℂ) R:=mem_ball_zero_iff.mpr (by rw [hr2]; linarith)
  have SZ:0< ‖B z₂‖ :=norm_pos_iff.mpr (Jq z₂ (Metric.ball_subset_closedBall Nc))
  have hlog:Real.log ‖B z₂‖ ≤ ‖J z₂‖ +Real.log 2:=by
    have h1:=Ez z₂ Nc
    have h2:(J z₂).re≤ ‖J z₂‖ :=Complex.re_le_norm _
    have h3:Real.log ‖B 0‖ ≤Real.log 2:=Real.log_le_log (by linarith) WZ
    linarith
  have hfin: ‖B z₂‖ ≤2*Real.exp ‖J z₂‖ :=by
    calc ‖B z₂‖ =Real.exp (Real.log ‖B z₂‖) :=(Real.exp_log SZ).symm
      _≤Real.exp (‖J z₂‖ +Real.log 2) :=Real.exp_le_exp.mpr hlog
      _=2*Real.exp ‖J z₂‖ :=by rw [Real.exp_add,Real.exp_log (by norm_num)]; ring
  have Tf:B z₂=riemannZeta (((1/2+2*δ:ℝ) :ℂ)+t* I) :=by
    simp only [hB,hcz]
  have aaI: -‖J z₂‖ -Real.log 3≤Real.log ‖B z₂‖ :=by
    have h1:=Ez z₂ Nc
    have h2: -‖J z₂‖ ≤(J z₂).re:=by
      linarith [Complex.abs_re_le_norm (J z₂),neg_abs_le (J z₂).re]
    have h3:Real.log (1/3)≤Real.log ‖B 0‖ :=Real.log_le_log (by norm_num) LD
    have h4:Real.log (1/3)= -Real.log 3:=by rw [one_div,Real.log_inv]
    linarith
  have Tj: ‖B z₂‖⁻¹≤3*Real.exp ‖J z₂‖ :=by
    calc ‖B z₂‖⁻¹=Real.exp (-Real.log ‖B z₂‖) :=by rw [Real.exp_neg,Real.exp_log SZ]
      _≤Real.exp (‖J z₂‖ +Real.log 3) :=Real.exp_le_exp.mpr (by linarith)
      _=3*Real.exp ‖J z₂‖ :=by rw [Real.exp_add,Real.exp_log (by norm_num)]; ring
  rw [← Tf]
  exact ⟨hfin.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h3c) (by norm_num)),
    Tj.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h3c) (by norm_num))⟩
lemma pL (hRH:RiemannHypothesis) {δ:ℝ} (hδ0:0<δ) (hδ:δ≤1/4)
    {ε:ℝ} (hε:0<ε) : ∃ T:ℝ,6≤T ∧ ∀ t:ℝ,T≤t→
      ‖riemannZeta (((1/2+2*δ:ℝ) :ℂ)+t* I)‖ ≤2*t^ε ∧
      ‖riemannZeta (((1/2+2*δ:ℝ) :ℂ)+t* I)‖⁻¹≤3*t^ε:=by
  obtain ⟨K,hK,PY⟩:=wR
  have Tk:0≤theta δ:=theta_nonneg hδ
  have Mj:theta δ<1:=wS hδ0 hδ
  set θ:=theta δ with hθ
  set M₁:ℝ:=Real.log (3*(Z (5/4)+1)) with hM₁
  have Vd:0≤M₁:=(Real.log_pos (by linarith [qP (5/4)])).le
  set D:ℝ:=(4*M₁)^(1-θ)*(6/δ)^θ*2^θ with hD
  have hev: ∀ᶠ t:ℝ in atTop,D/ε≤Real.log t^(1-θ) :=
    ((tendsto_rpow_atTop (by linarith)).comp Real.tendsto_log_atTop).eventually_ge_atTop _
  obtain ⟨T₁,hT₁⟩:=eventually_atTop.mp hev
  refine ⟨max (max T₁ 6) (6*K),le_trans (le_max_right _ _) (le_max_left _ _),fun t ht=>?_⟩
  have Qc:T₁≤t:=le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have ht6:6≤t:=le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have htK:6*K≤t:=le_trans (le_max_right _ _) ht
  have hmain:=Gt hRH hδ0 hδ hK PY ht6
  have hlt:0<Real.log t:=Real.log_pos (by linarith)
  have hL:Real.log (6*K*t)≤2*Real.log t:=by
    rw [show 2*Real.log t=Real.log (t*t) by
      rw [Real.log_mul (by linarith) (by linarith)]; ring]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hstep:(4*M₁)^(1-θ)*(6*Real.log (6*K*t)/δ)^θ≤ε*Real.log t:=by
    calc (4*M₁)^(1-θ)*(6*Real.log (6*K*t)/δ)^θ
        ≤(4*M₁)^(1-θ)*((6/δ)*(2*Real.log t))^θ:=by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine Real.rpow_le_rpow (by
            have:0≤Real.log (6*K*t) :=Real.log_nonneg (by nlinarith)
            positivity) ?_ Tk
          rw [mul_div_right_comm]
          exact mul_le_mul_of_nonneg_left hL (by positivity)
      _=D*Real.log t^θ:=by
          rw [Real.mul_rpow (x:=6/δ) (by positivity) (by positivity),
            Real.mul_rpow (x:=(2:ℝ)) (by norm_num) hlt.le,hD]
          ring
      _≤(ε*Real.log t^(1-θ))*Real.log t^θ:=by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have:=hT₁ t Qc
          rwa [div_le_iff₀ hε,mul_comm] at this
      _=ε*Real.log t:=by
          rw [mul_assoc, ← Real.rpow_add hlt]; simp
  have hX:Real.exp ((4*M₁)^(1-θ)*(6*Real.log (6*K*t)/δ)^θ)≤t^ε:=by
    calc Real.exp ((4*M₁)^(1-θ)*(6*Real.log (6*K*t)/δ)^θ)
        ≤Real.exp (ε*Real.log t) :=Real.exp_le_exp.mpr hstep
      _=t^ε:=by rw [Real.rpow_def_of_pos (by linarith),mul_comm ε]
  exact ⟨hmain.1.trans (mul_le_mul_of_nonneg_left hX (by norm_num)),
    hmain.2.trans (mul_le_mul_of_nonneg_left hX (by norm_num))⟩
lemma Ws (hRH:RiemannHypothesis) {δ:ℝ} (hδ0:0<δ) (hδ:δ≤1/4)
    {ε:ℝ} (hε:0<ε) : ∃ C:ℝ,0≤C ∧ ∀ t:ℝ,
      ‖Lindelof.F (((1/2+2*δ:ℝ) :ℂ)+t* I)‖ ≤
        C*(1+ |t|)^(1+ε)*Real.log (|t| +3) :=by
  obtain ⟨T,hT6,hT⟩:=pL hRH hδ0 hδ hε
  set b:ℝ:=1/2+2*δ with hb
  obtain ⟨Mc,hMc⟩:=(isCompact_Icc (a:= -T) (b:=T)).exists_bound_of_continuousOn
    (f:=fun t:ℝ=>Lindelof.F (b+t* I)) (Lindelof.wQ.comp (by fun_prop)).continuousOn
  have hC0:0≤ max Mc 2:=le_trans (by norm_num) (le_max_right _ _)
  refine ⟨max Mc 2,hC0,fun t=>?_⟩
  have hl:=Lindelof.gG (t:=t)
  have h1t:(1:ℝ)≤1+ |t| :=le_add_of_nonneg_right (abs_nonneg t)
  have hp:1≤(1+ |t|)^(1+ε) :=Real.one_le_rpow h1t (by linarith)
  rcases le_or_gt |t| T with htT | htT
  · have:=hMc t (abs_le.mp htT)
    calc ‖Lindelof.F (b+t* I)‖ ≤ max Mc 2:=this.trans (le_max_left _ _)
      _=max Mc 2*1*1:=by ring
      _≤_:=by gcongr
  have ht0:0< |t| :=by linarith
  have hζ: ‖riemannZeta (b+t* I)‖ ≤2* |t| ^ε:=by
    rcases le_or_gt 0 t with h0 | h0
    · rw [abs_of_nonneg h0] at htT ⊢; exact (hT t htT.le).1
    · rw [abs_of_neg h0] at htT ⊢
      have:=(hT (-t) htT.le).1
      have hconj:(starRingEnd ℂ) ((b:ℂ)+((-t:ℝ) :ℂ)* I)=(b:ℂ)+t* I:=by
        apply Complex.ext <;> simp
      rw [← hconj,riemannZeta_conj,Complex.norm_conj]
      exact this
  have hne:(b:ℂ)+t* I≠1:=by
    intro h; have:=congrArg Complex.im h; simp at this; rw [this] at ht0; simp at ht0
  rw [Lindelof.F_eq hne,norm_mul]
  have hn1: ‖(b:ℂ)+t* I-1‖ ≤1+ |t| :=by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hre:((b:ℂ)+t* I-1).re=b-1:=by simp
    have him:((b:ℂ)+t* I-1).im=t:=by simp
    rw [hre,him]
    have: |b-1| ≤1:=abs_le.mpr ⟨by linarith,by linarith⟩
    linarith
  have hpow: |t| ^ε≤(1+ |t|)^ε:=Real.rpow_le_rpow ht0.le (by linarith) hε.le
  calc ‖(b:ℂ)+t* I-1‖ * ‖riemannZeta (b+t* I)‖
      ≤(1+ |t|)*(2*(1+ |t|)^ε) :=
        mul_le_mul hn1 (hζ.trans (by gcongr)) (norm_nonneg _) (by positivity)
    _=2*(1+ |t|)^(1+ε) :=by rw [Real.rpow_add (by positivity),Real.rpow_one]; ring
    _=2*(1+ |t|)^(1+ε)*1:=by ring
    _≤ max Mc 2*(1+ |t|)^(1+ε)*Real.log (|t| +3) :=by
        gcongr
        exact le_max_right _ _
def hg (α β t₀:ℝ) (s:ℂ) :ℂ:=
  Lindelof.F s*Complex.exp ((s-t₀* I)^2)*
    Complex.exp (-((α:ℂ)-β *s)*(Real.log (1+ |t₀|) :ℂ))
lemma Gv (α β t₀:ℝ) :Differentiable ℂ (hg α β t₀) :=by
  unfold hg
  exact (differentiable_riemannZeta₁.mul (by fun_prop)).mul (by fun_prop)
lemma Nh (α β t₀:ℝ) (s:ℂ) :
    ‖hg α β t₀ s‖ = ‖Lindelof.F s‖ *Real.exp (s.re^2 -(s.im-t₀)^2)*
      (1+ |t₀|)^(-(α-β *s.re)) :=by
  unfold hg
  rw [norm_mul,norm_mul,Complex.norm_exp,Complex.norm_exp]
  congr 2
  · simp [sq,Complex.mul_re]
  · rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    simp only [Complex.mul_re,Complex.neg_re,Complex.sub_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.neg_im,Complex.sub_im,mul_zero,sub_zero,Complex.mul_im,
      zero_mul,add_zero]
    ring
lemma Ds {α β σ K t₀ t:ℝ} (oC:0≤σ) (hσ1:σ≤1) (hK:0≤K)
    (he0:0≤α-β *σ) (he2:α-β *σ≤2)
    (hF: ‖Lindelof.F (σ+t* I)‖ ≤K*(1+ |t|)^(α-β *σ)*Real.log (|t| +3)) :
    ‖hg α β t₀ (σ+t* I)‖ ≤K*Real.exp (13/4)*Real.log (|t₀| +3) :=by
  rw [Nh]
  have hre:((σ:ℂ)+t* I).re=σ:=by simp
  have him:((σ:ℂ)+t* I).im=t:=by simp
  rw [hre,him]
  set e:ℝ:=α-β *σ with he
  set a:ℝ:=1+ |t₀| with ha
  set b:ℝ:=1+ |t-t₀| with hb
  set ℓ:ℝ:=Real.log (|t₀| +3) with hℓ
  have ha1:1≤a:=le_add_of_nonneg_right (abs_nonneg _)
  have hb1:1≤b:=le_add_of_nonneg_right (abs_nonneg _)
  have adK:1≤ℓ:=Lindelof.gG
  have htri: |t| ≤ |t₀| + |t-t₀| :=by
    calc |t| = |t₀+(t-t₀)| :=by ring_nf
      _≤ |t₀| + |t-t₀| :=abs_add_le _ _
  have hab:1+ |t| ≤a*b:=by
    rw [ha,hb]; nlinarith [abs_nonneg t₀,abs_nonneg (t-t₀)]
  have hpow:(1+ |t|)^e≤a^e*b^e:=by
    rw [← Real.mul_rpow (by linarith) (by linarith)]
    exact Real.rpow_le_rpow (by positivity) hab he0
  have hbe:b^e≤b^2:=by
    calc b^e≤b^(2:ℝ) :=Real.rpow_le_rpow_of_exponent_le hb1 he2
      _=b^2:=Real.rpow_two b
  have hlog:Real.log (|t| +3)≤ℓ*b:=by
    have h1: |t| +3≤(|t₀| +3)*b:=by
      rw [hb]; nlinarith [abs_nonneg t₀,abs_nonneg (t-t₀)]
    have h2:Real.log (|t| +3)≤ℓ+Real.log b:=by
      rw [hℓ, ← Real.log_mul (by positivity) (by linarith)]
      exact Real.log_le_log (by positivity) h1
    have h3:Real.log b≤b-1:=Real.log_le_sub_one_of_pos (by linarith)
    nlinarith
  have haa:a^e*a^(-e)=1:=by
    rw [← Real.rpow_add (by linarith)]; simp
  have hexp:Real.exp (σ^2 -(t-t₀)^2)≤Real.exp 1*Real.exp (-(t-t₀)^2) :=by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
  have hbu:b^3*Real.exp (-(t-t₀)^2)≤Real.exp (9/4) :=by
    have:=Lindelof.bound_aux (u:=t-t₀); rwa [← hb] at this
  have FH:0≤Real.log (|t| +3) :=by linarith [Lindelof.gG (t:=t)]
  have aei:0≤a^(-e) :=by positivity
  calc ‖Lindelof.F (σ+t* I)‖ *Real.exp (σ^2 -(t-t₀)^2)*a^(-e)
      ≤(K*(a^e*b^e)*Real.log (|t| +3))*
          (Real.exp 1*Real.exp (-(t-t₀)^2))*a^(-e) :=by
        gcongr
        exact hF.trans (by gcongr)
    _=K*b^e*Real.log (|t| +3)*Real.exp 1*Real.exp (-(t-t₀)^2)*
          (a^e*a^(-e)) :=by ring
    _≤K*b^2*(ℓ*b)*Real.exp 1*Real.exp (-(t-t₀)^2)*1:=by
        rw [haa]; gcongr
    _=K*Real.exp 1*ℓ*(b^3*Real.exp (-(t-t₀)^2)) :=by ring
    _≤K*Real.exp 1*ℓ*Real.exp (9/4) :=by gcongr
    _=K*Real.exp (13/4)*ℓ:=by
        rw [show (13/4:ℝ)=1+9/4 by norm_num,Real.exp_add]; ring
lemma Ve {α β b:ℝ} (t₀:ℝ) (hb0:0<b) (hb1:b≤1)
    (he: ∀ σ:ℝ,0<σ→σ<b→0≤α-β *σ) :
    ∃ c<Real.pi/(b- 0), ∃ B,
    hg α β t₀ =O[comap (_root_.abs∘Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo 0 b)]
      fun z=>Real.exp (B*Real.exp (c* |z.im|)) :=by
  refine ⟨2,?_,5,?_⟩
  · rw [sub_zero,lt_div_iff₀ hb0]; nlinarith [Real.pi_gt_three]
  refine Asymptotics.IsBigO.of_bound 1 ?_
  have h1: ∀ᶠ z in comap (_root_.abs∘Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo 0 b),
      2≤ |z.im| :=
    (tendsto_comap.eventually (eventually_ge_atTop 2)).filter_mono inf_le_left
  have h2: ∀ᶠ z in comap (_root_.abs∘Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo 0 b),
      z∈Complex.re ⁻¹' Ioo 0 b:=
    (eventually_principal.mpr fun z hz=>hz).filter_mono inf_le_right
  filter_upwards [h1,h2] with z hz hU
  obtain ⟨Zn,Zo⟩:=hU
  have MW:z.re<1:=lt_of_lt_of_le Zo hb1
  rw [one_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Nh]
  have hz1:z≠1:=by
    intro h; rw [h] at hz; norm_num at hz
  have hF: ‖Lindelof.F z‖ ≤(1+ |z.im|)*(4*(2+4* |z.im|)*Real.exp (2* |z.im|)) :=by
    rw [Lindelof.F_eq hz1,norm_mul]
    gcongr
    · calc ‖z-1‖ ≤ |(z-1).re| + |(z-1).im| :=Complex.norm_le_abs_re_add_abs_im _
        _≤1+ |z.im| :=by
          simp only [Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,sub_zero]
          rw [abs_of_neg (by linarith)]; linarith
    · exact Lindelof.EH Zn.le MW.le hz
  have hE:Real.exp (z.re^2 -(z.im-t₀)^2)≤Real.exp 1:=by
    apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg (z.im-t₀)]
  have hA:(1+ |t₀|)^(-(α-β *z.re))≤1:=
    Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (abs_nonneg _))
      (by linarith [he z.re Zn Zo])
  calc ‖Lindelof.F z‖ *Real.exp (z.re^2 -(z.im-t₀)^2)*(1+ |t₀|)^(-(α-β *z.re))
      ≤(1+ |z.im|)*(4*(2+4* |z.im|)*Real.exp (2* |z.im|))*Real.exp 1*1:=by
        gcongr
    _≤Real.exp (5*Real.exp (2* |z.im|)) :=by
        rw [mul_one]; exact Lindelof.SY (abs_nonneg _)
lemma Gw {α β b K:ℝ} (hb0:0<b) (hb1:b≤1) (hK:0≤K)
    (he: ∀ σ:ℝ,0≤σ→σ≤b→0≤α-β *σ ∧ α-β *σ≤2)
    (h0: ∀ t:ℝ, ‖Lindelof.F (t* I)‖ ≤K*(1+ |t|)^α*Real.log (|t| +3))
    (hb: ∀ t:ℝ, ‖Lindelof.F (b+t* I)‖ ≤K*(1+ |t|)^(α-β *b)*Real.log (|t| +3))
    {σ t₀:ℝ} (oC:0≤σ) (hσ1:σ≤b) :
    ‖Lindelof.F (σ+t₀* I)‖ ≤
      K*Real.exp (13/4)*(1+ |t₀|)^(α-β *σ)*Real.log (|t₀| +3) :=by
  have hPL:=PhragmenLindelof.vertical_strip (f:=hg α β t₀) (a:=0) (b:=b)
    (C:=K*Real.exp (13/4)*Real.log (|t₀| +3)) (z:=(σ:ℂ)+t₀* I)
    (Gv α β t₀).diffContOnCl
    (Ve t₀ hb0 hb1 (fun σ h0 h1=>(he σ h0.le h1.le).1))
    (fun z hz=>by
      have hz':z=((0:ℝ) :ℂ)+z.im* I:=by
        apply Complex.ext <;> simp [hz]
      rw [hz']
      have h00:=he 0 le_rfl hb0.le
      refine Ds le_rfl zero_le_one hK h00.1 h00.2 ?_
      rw [mul_zero,sub_zero]
      simpa using h0 z.im)
    (fun z hz=>by
      have hz':z=((b:ℝ) :ℂ)+z.im* I:=by
        apply Complex.ext <;> simp [hz]
      rw [hz']
      have hbb:=he b hb0.le le_rfl
      exact Ds hb0.le hb1 hK hbb.1 hbb.2 (hb z.im))
    (by simpa using oC) (by simpa using hσ1)
  rw [Nh] at hPL
  have hre:((σ:ℂ)+t₀* I).re=σ:=by simp
  have him:((σ:ℂ)+t₀* I).im=t₀:=by simp
  rw [hre,him,sub_self] at hPL
  set e:ℝ:=α-β *σ with he'
  have ha:0<(1+ |t₀|)^(-e) :=by positivity
  have hae:(1+ |t₀|)^e*(1+ |t₀|)^(-e)=1:=by
    rw [← Real.rpow_add (by positivity)]; simp
  have hexp:1≤Real.exp (σ^2 - 0^2) :=Real.one_le_exp (by nlinarith)
  have hF0:0≤ ‖Lindelof.F (σ+t₀* I)‖ :=norm_nonneg _
  have key: ‖Lindelof.F (σ+t₀* I)‖ *(1+ |t₀|)^(-e)
      ≤K*Real.exp (13/4)*Real.log (|t₀| +3) :=by
    refine le_trans ?_ hPL
    have:=mul_le_mul_of_nonneg_left hexp (mul_nonneg hF0 ha.le)
    nlinarith
  calc ‖Lindelof.F (σ+t₀* I)‖
      = ‖Lindelof.F (σ+t₀* I)‖ *(1+ |t₀|)^(-e)*(1+ |t₀|)^e:=by
        rw [mul_assoc,mul_comm ((1+ |t₀|)^(-e)),hae,mul_one]
    _≤K*Real.exp (13/4)*Real.log (|t₀| +3)*(1+ |t₀|)^e:=by gcongr
    _=_:=by ring
theorem qo (hRH:RiemannHypothesis) :
    ∀ ε:ℝ,0<ε→ ∃ C:ℝ, ∀ t:ℝ,3≤ |t| → ‖riemannZeta (1/2+t* I)‖ ≤C* |t| ^ε:=by
  intro ε₀ hε₀
  set ε:ℝ:=min ε₀ 1 with Zp
  have hε:0<ε:=lt_min hε₀ one_pos
  have hε1:ε≤1:=min_le_right _ _
  have Wt:ε≤ε₀:=min_le_left _ _
  have hδ0:0<ε/8:=by positivity
  have hδ:ε/8≤1/4:=by linarith
  obtain ⟨C₁,hC₁,hF⟩:=Ws hRH hδ0 hδ (ε:=ε/4) (by positivity)
  obtain ⟨K₀,hK₀,Zq⟩:=Lindelof.Oe
  set b:ℝ:=1/2+2*(ε/8) with hb
  have hb0:0<b:=by positivity
  have hb1:b≤1:=by linarith
  set K:ℝ:=max C₁ K₀ with hK
  have hK0:0≤K:=le_trans hC₁ (le_max_left _ _)
  set β:ℝ:=(1/2 -ε/4)/b with hβ
  have hβb:β *b=1/2 -ε/4:=by rw [hβ]; field_simp
  have Zr:0≤β:=by rw [hβ]; exact div_nonneg (by linarith) hb0.le
  have he: ∀ σ:ℝ,0≤σ→σ≤b→0≤3/2 -β *σ ∧ 3/2 -β *σ≤2:=by
    intro σ h0 h1
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left h1 Zr]
    · nlinarith [mul_nonneg Zr h0]
  have h0: ∀ t:ℝ,
      ‖Lindelof.F (t* I)‖ ≤K*(1+ |t|)^(3/2:ℝ)*Real.log (|t| +3) :=by
    intro t
    refine (Zq t).2.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (by positivity)) (by linarith [Lindelof.gG (t:=t)])
  have hbl: ∀ t:ℝ, ‖Lindelof.F (b+t* I)‖ ≤
      K*(1+ |t|)^(3/2 -β *b)*Real.log (|t| +3) :=by
    intro t
    rw [hβb,show (3/2:ℝ)-(1/2 -ε/4)=1+ε/4 by ring]
    refine (hF t).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity)) (by linarith [Lindelof.gG (t:=t)])
  refine ⟨16*(K*Real.exp (13/4))/ε,fun t ht=>?_⟩
  have hPL:=Gw (α:=3/2) (β:=β) hb0 hb1 hK0 he h0 hbl
    (σ:=1/2) (t₀:=t) (by norm_num) (by linarith)
  set Kc:ℝ:=K*Real.exp (13/4) with hKc
  have aco:0≤Kc:=by positivity
  have adL:1-ε≤β:=by
    by_contra h
    push Not at h
    have:(β-(1-ε))*b<0:=mul_neg_of_neg_of_pos (by linarith) hb0
    have e:(β-(1-ε))*b=ε^2/4:=by rw [sub_mul,hβb,hb]; ring
    nlinarith
  have hexp:3/2 -β *(1/2)≤1+ε/2:=by linarith
  have ht1:1≤ |t| :=by linarith
  have ht0:0< |t| :=by linarith
  have hcast:(1/2:ℂ)+t* I=((1/2:ℝ) :ℂ)+t* I:=by push_cast; ring
  rw [hcast]
  have hne:((1/2:ℝ) :ℂ)+t* I≠1:=by
    intro h; have:=congrArg Complex.re h; simp at this
  have hden: |t| ≤ ‖((1/2:ℝ) :ℂ)+t* I-1‖ :=by
    calc |t| = |(((1/2:ℝ) :ℂ)+t* I-1).im| :=by simp
      _≤_:=Complex.abs_im_le_norm _
  have hζ: ‖riemannZeta (((1/2:ℝ) :ℂ)+t* I)‖ * |t| ≤
      ‖Lindelof.F (((1/2:ℝ) :ℂ)+t* I)‖ :=by
    rw [Lindelof.F_eq hne,norm_mul,mul_comm]
    exact mul_le_mul_of_nonneg_right hden (norm_nonneg _)
  have FH:Real.log (|t| +3)≤2*Real.log |t| :=by
    have h1:Real.log (|t| +3)≤Real.log (2* |t|) :=
      Real.log_le_log (by positivity) (by linarith)
    have h2:Real.log (2* |t|)=Real.log 2+Real.log |t| :=Real.log_mul (by norm_num) ht0.ne'
    have h3:Real.log 2≤Real.log |t| :=Real.log_le_log (by norm_num) (by linarith)
    linarith
  have adM:Real.log |t| ≤ |t| ^(ε/2)/(ε/2) :=
    Real.log_le_rpow_div ht0.le (by positivity)
  have hL:Real.log (|t| +3)≤4/ε* |t| ^(ε/2) :=by
    calc Real.log (|t| +3)≤2*Real.log |t| :=FH
      _≤2*(|t| ^(ε/2)/(ε/2)) :=by gcongr
      _=4/ε* |t| ^(ε/2) :=by field_simp; ring
  have hP:(1+ |t|)^(3/2 -β *(1/2))≤4* |t| ^(1+ε/2) :=by
    calc (1+ |t|)^(3/2 -β *(1/2))≤(1+ |t|)^(1+ε/2) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
      _≤(2* |t|)^(1+ε/2) :=Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _=2^(1+ε/2)* |t| ^(1+ε/2) :=Real.mul_rpow (by norm_num) ht0.le
      _≤4* |t| ^(1+ε/2) :=by
          gcongr
          calc (2:ℝ)^(1+ε/2)≤2^(2:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _=4:=by norm_num
  have aaJ: |t| ^(1+ε/2)* |t| ^(ε/2)= |t| ^ε* |t| :=by
    rw [← Real.rpow_add ht0, ← Real.rpow_add_one ht0.ne']; congr 1; ring
  have hmain: ‖riemannZeta (((1/2:ℝ) :ℂ)+t* I)‖ * |t| ≤
      (16*Kc/ε* |t| ^ε)* |t| :=by
    refine hζ.trans (hPL.trans ?_)
    have Oo:0≤Real.log (|t| +3) :=by linarith [Lindelof.gG (t:=t)]
    calc Kc*(1+ |t|)^(3/2 -β *(1/2))*Real.log (|t| +3)
        ≤Kc*(4* |t| ^(1+ε/2))*(4/ε* |t| ^(ε/2)) :=by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hP aco) hL Oo (by positivity)
      _=16*Kc/ε*(|t| ^(1+ε/2)* |t| ^(ε/2)) :=by ring
      _=16*Kc/ε* |t| ^ε* |t| :=by rw [aaJ]; ring
  have hfin:=le_of_mul_le_mul_right hmain ht0
  refine hfin.trans ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1 Wt) (by positivity)
end aF.lN
end
end

-- Zeta23.cE.EK.Y
section
open Complex Set Filter Topology Metric
open scoped ComplexConjugate
noncomputable section
namespace Zeta23
namespace cE
namespace EK
lemma qu {s:ℂ} (hre:0<s.re) (Zt:s.re≤4) (him:2≤ |s.im|) :
    ‖logDeriv Gammaℝ s‖ ≤Real.log (|s.im| +3)+5:=by
  rw [Zeta23.dQ.jB hre]
  set w:ℂ:=s/2 with hw
  have pC:0<w.re:=by simp [hw]; linarith
  have Ci:w.im=s.im/2:=by simp [hw]
  have hw':1≤ |w.im| :=by rw [Ci,abs_div,abs_two]; linarith
  have h:=Zeta23.kZ.oB pC (by linarith)
  have Wj:1≤w.im^2:=by have:=sq_abs w.im; nlinarith [abs_nonneg w.im]
  have h3:3/w.im^2≤3:=by rw [div_le_iff₀ (by positivity)]; nlinarith
  have hw1:1≤ ‖w‖ :=le_trans hw' (Complex.abs_im_le_norm w)
  have hwle: ‖w‖ ≤ |s.im| +3:=by
    have: ‖w‖ = ‖s‖ /2:=by rw [hw,norm_div]; norm_num
    rw [this]
    have:=Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hre] at this
    linarith
  have hlog: ‖Complex.log w‖ ≤Real.log (|s.im| +3)+Real.pi:=by
    calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _= |Real.log ‖w‖| + |Complex.arg w| :=by rw [Complex.log_re,Complex.log_im]
      _≤Real.log (|s.im| +3)+Real.pi:=by
          apply add_le_add _ (Complex.abs_arg_le_pi w)
          rw [abs_of_nonneg (Real.log_nonneg hw1)]
          exact Real.log_le_log (by linarith) hwle
  have hinv: ‖(1/2:ℂ)/w‖ ≤1/2:=by
    rw [norm_div]
    have: ‖(1/2:ℂ)‖ =1/2:=by norm_num
    rw [this,div_le_iff₀ (by linarith)]
    nlinarith
  have hψ: ‖Complex.digamma w‖ ≤Real.log (|s.im| +3)+Real.pi+7/2:=by
    calc ‖Complex.digamma w‖
        = ‖(Complex.digamma w-Complex.log w+(1/2:ℂ)/w)+Complex.log w-(1/2:ℂ)/w‖ :=by
          ring_nf
      _≤ ‖Complex.digamma w-Complex.log w+(1/2:ℂ)/w‖ + ‖Complex.log w‖ + ‖(1/2:ℂ)/w‖ :=by
          refine le_trans (norm_sub_le _ _) ?_
          gcongr
          exact norm_add_le _ _
      _≤3+(Real.log (|s.im| +3)+Real.pi)+1/2:=by linarith
      _=Real.log (|s.im| +3)+Real.pi+7/2:=by ring
  have adr: ‖-(Real.log Real.pi:ℂ)/2‖ ≤1:=by
    rw [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have:Real.log Real.pi≤2:=by
      have h4:Real.log Real.pi≤Real.log 4:=Real.log_le_log Real.pi_pos Real.pi_lt_four.le
      have h4':Real.log 4=2*Real.log 2:=by
        rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; push_cast; ring
      linarith [Real.log_two_lt_d9]
    have h2: ‖(2:ℂ)‖ =2:=by norm_num
    rw [h2]; linarith
  calc ‖-(Real.log Real.pi:ℂ)/2+(1/2:ℂ)*Complex.digamma w‖
      ≤ ‖-(Real.log Real.pi:ℂ)/2‖ + ‖(1/2:ℂ)*Complex.digamma w‖ :=norm_add_le _ _
    _≤1+1/2*(Real.log (|s.im| +3)+Real.pi+7/2) :=by
        gcongr
        rw [norm_mul]
        have: ‖(1/2:ℂ)‖ =1/2:=by norm_num
        rw [this]
        gcongr
    _≤Real.log (|s.im| +3)+5:=by
        have:=Real.log_nonneg (by linarith [abs_nonneg s.im]:(1:ℝ)≤ |s.im| +3)
        nlinarith [Real.pi_lt_four]
end EK
end cE
end Zeta23
end
end

-- aF.aaK
section
open Complex Set Filter Topology
noncomputable section
namespace aF.Nyman.Ratio
lemma Bw: ∃ B:ℝ,0≤B ∧ ∀ s:ℂ,1/2≤ s.re→s.re≤3/4→
    |s.im| ≤2→ ‖logDeriv Gammaℝ s‖ ≤B:=by
  set S:Set ℂ:=(Icc (1/2:ℝ) (3/4)) ×ℂ (Icc (-2:ℝ) 2) with hS
  have hc:IsCompact S:=(isCompact_Icc).reProdIm isCompact_Icc
  have hcont:ContinuousOn (logDeriv Gammaℝ) S:=by
    refine (Zeta23.dQ.mo.continuousOn).mono ?_
    intro s hs
    simp only [hS,mem_reProdIm,mem_Icc] at hs
    show 0<s.re
    linarith [hs.1.1]
  obtain ⟨B,hB⟩:=hc.exists_bound_of_continuousOn hcont
  refine ⟨max B 0,le_max_right _ _,fun s h1 h2 h3=>?_⟩
  have:s∈S:=by
    simp only [hS,mem_reProdIm,mem_Icc]
    exact ⟨⟨h1,h2⟩,abs_le.mp h3⟩
  exact (hB s this).trans (le_max_left _ _)
lemma gG (t:ℝ) :1≤Real.log (|t| +3) :=by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have:=Real.exp_one_lt_d9
  linarith [abs_nonneg t]
lemma Gz (hRH:RiemannHypothesis) :
    ∃ K:ℝ,0≤K ∧ ∀ σ t:ℝ,1/2<σ→σ≤3/4→
      -(K*Real.log (|t| +3))≤(logDeriv riemannZeta ((σ:ℂ)+t* I)).re:=by
  obtain ⟨B,hB0,hB⟩:=Bw
  refine ⟨12+B,by positivity,fun σ t hσ hσ'=>?_⟩
  set s:ℂ:=(σ:ℂ)+t* I with hs
  have hre:s.re=σ:=by simp [hs]
  have him:s.im=t:=by simp [hs]
  have hs0:s≠0:=fun h=>by
    have:=congrArg Complex.re h; rw [hre] at this; simp at this; linarith
  have hs1:s≠1:=fun h=>by
    have:=congrArg Complex.re h; rw [hre] at this; simp at this; linarith
  have hz:riemannZeta s≠0:=lN.gO hRH (by rw [hre]; exact hσ) hs1
  have hxi:Zeta23.cE.xi s≠0:=by
    have:=qO.mL hs0 hs1
    intro e; rw [e] at this; simp at this; exact hz this
  have hpos:0≤(logDeriv Zeta23.cE.xi s).re:=
    Lagarias.Od hRH (by rw [hre]; exact hσ) hxi
  rw [qO.yF hs0 hs1 hz]
  have hL:=gG t
  have h1: ‖1/s‖ ≤2:=by
    rw [norm_div,norm_one,div_le_iff₀ (norm_pos_iff.mpr hs0)]
    have:σ≤ ‖s‖ :=by rw [← hre]; exact Complex.re_le_norm s
    linarith
  have h2: ‖1/(s-1)‖ ≤4:=by
    have VE:s-1≠0:=sub_ne_zero.mpr hs1
    rw [norm_div,norm_one,div_le_iff₀ (norm_pos_iff.mpr VE)]
    have:1-σ≤ ‖s-1‖ :=by
      have:=Complex.abs_re_le_norm (s-1)
      rw [Complex.sub_re,hre,Complex.one_re] at this
      rw [abs_sub_comm] at this
      linarith [le_abs_self (1-σ)]
    linarith
  have h3: ‖logDeriv Gammaℝ s‖ ≤Real.log (|t| +3)+5+B:=by
    rcases le_or_gt 2 |t| with ht | ht
    · have:=Zeta23.cE.EK.qu (s:=s)
        (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; exact ht)
      rw [him] at this; linarith
    · have:=hB s (by rw [hre]; linarith) (by rw [hre]; exact hσ') (by rw [him]; exact ht.le)
      have:0≤Real.log (|t| +3) :=by linarith
      linarith
  have e1:=Complex.re_le_norm (1/s)
  have e2:=Complex.re_le_norm (1/(s-1))
  have e3:=Complex.re_le_norm (logDeriv Gammaℝ s)
  simp only [Complex.sub_re]
  nlinarith
theorem GA (hRH:RiemannHypothesis) :
    ∃ K:ℝ,0≤K ∧ ∀ t ε:ℝ,0<ε→ε≤1/4→
      ‖riemannZeta ((1/2:ℂ)+t* I)‖ ≤
        ‖riemannZeta (((1/2+ε:ℝ) :ℂ)+t* I)‖ *
          Real.exp (K* ε*Real.log (|t| +3)) :=by
  obtain ⟨K,hK0,hK⟩:=Gz hRH
  refine ⟨K,hK0,fun t ε hε wW=>?_⟩
  set a:ℝ:=K*Real.log (|t| +3) with ha
  have ha0:0≤a:=mul_nonneg hK0 (by linarith [gG t])
  set p:ℝ→ℂ:=fun σ=>(σ:ℂ)+t* I with hp
  have hp1: ∀ σ:ℝ,σ<1→p σ≠1:=fun σ hσ h=>by
    have:=congrArg Complex.re h; simp [hp] at this; linarith
  set v:ℝ→ℝ:=fun σ=> ‖riemannZeta (p σ)‖ ^2*Real.exp (2*a*σ) with hv
  have hderiv: ∀ σ:ℝ,σ<1→HasDerivAt v
      ((2*inner ℝ (riemannZeta (p σ)) (deriv riemannZeta (p σ)))*Real.exp (2*a*σ)+
        ‖riemannZeta (p σ)‖ ^2*(Real.exp (2*a*σ)*(2*a))) σ:=by
    intro σ hσ
    have hd:DifferentiableAt ℂ riemannZeta (p σ) :=differentiableAt_riemannZeta (hp1 σ hσ)
    have h:=(hd.hasDerivAt.comp (σ:ℂ) ((hasDerivAt_id (σ:ℂ)).add_const (t* I)))
    simp only [mul_one] at h
    have hn:=h.comp_ofReal.norm_sq
    have he:HasDerivAt (fun σ:ℝ=>Real.exp (2*a*σ)) (Real.exp (2*a*σ)*(2*a)) σ:=by
      have:=((hasDerivAt_id σ).const_mul (2*a)).exp
      simpa [mul_comm] using this
    exact hn.mul he
  have hmono:MonotoneOn v (Icc (1/2) (1/2+ε)) :=by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · intro σ hσ
      exact (hderiv σ (by linarith [hσ.2])).continuousAt.continuousWithinAt
    · intro σ hσ
      rw [interior_Icc] at hσ
      exact (hderiv σ (by linarith [hσ.2])).differentiableAt.differentiableWithinAt
    · intro σ hσ
      rw [interior_Icc] at hσ
      rw [(hderiv σ (by linarith [hσ.2])).deriv]
      have hre:(p σ).re=σ:=by simp [hp]
      have hz:riemannZeta (p σ)≠0:=
        lN.gO hRH (by rw [hre]; exact hσ.1) (hp1 σ (by linarith [hσ.2]))
      have hinner:inner ℝ (riemannZeta (p σ)) (deriv riemannZeta (p σ))=
          Complex.normSq (riemannZeta (p σ))*(logDeriv riemannZeta (p σ)).re:=by
        have hd:deriv riemannZeta (p σ)=riemannZeta (p σ)*logDeriv riemannZeta (p σ) :=by
          rw [logDeriv_apply,mul_div_cancel₀ _ hz]
        rw [Complex.inner,hd,mul_comm (riemannZeta (p σ)),mul_assoc,Complex.mul_conj,
          Complex.re_mul_ofReal,mul_comm]
      have hlow:=hK σ t hσ.1 (by linarith [hσ.2])
      rw [hinner,Complex.normSq_eq_norm_sq]
      have hE:=Real.exp_pos (2*a*σ)
      have hN:=sq_nonneg ‖riemannZeta (p σ)‖
      have:0≤(logDeriv riemannZeta (p σ)).re+a:=by
        simp only [hp] at hlow ⊢; linarith
      have:0≤ ‖riemannZeta (p σ)‖ ^2*Real.exp (2*a*σ)*
          (2*((logDeriv riemannZeta (p σ)).re+a)) :=by positivity
      nlinarith
  have hle:=hmono (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
    (by linarith:(1/2:ℝ)≤1/2+ε)
  simp only [hv] at hle
  have hp0:p (1/2)=(1/2:ℂ)+t* I:=by simp [hp]
  rw [hp0] at hle
  have e:Real.exp (2*a*(1/2+ε))=Real.exp (2*a*(1/2))*
      Real.exp (a* ε)^2:=by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  rw [e] at hle
  have hE:=Real.exp_pos (2*a*(1/2))
  have hsq: ‖riemannZeta ((1/2:ℂ)+t* I)‖ ^2≤
      (‖riemannZeta (p (1/2+ε))‖ *Real.exp (a* ε))^2:=by
    rw [mul_pow]
    nlinarith
  have:=(pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  have hpe:p (1/2+ε)=(((1/2+ε:ℝ) :ℂ)+t* I) :=rfl
  rw [hpe] at this
  calc _≤_:=this
    _=_:=by rw [ha]; ring_nf
end aF.Nyman.Ratio
end
end

-- aF.EO
section
open Complex Real Set Filter
noncomputable section
namespace aF.EO
end aF.EO
end
end

-- aF.Wv
section
open Filter Asymptotics Complex ArithmeticFunction
open scoped ArithmeticFunction.Moebius
noncomputable section
namespace aF.Mertens
section
end
end aF.Mertens
end
end

-- Zeta23.dO.XC
section
open scoped ContDiff
theorem MeasureTheory.vP {α:Type*} {β:Type*} {E:Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ:MeasureTheory.Measure α}
    {ν:MeasureTheory.Measure β} [NormedAddCommGroup E]
    [MeasureTheory.SigmaFinite ν] [NormedSpace ℝ E] [MeasureTheory.SigmaFinite μ]
    (f:α→β→E) {s:Set α} {t:Set β}
    (hf:IntegrableOn (f.uncurry) (s×ˢt) (μ.prod ν)) :
    (∫ (x:α) in s, ∫ (y:β) in t,f x y ∂ν ∂μ)
      = ∫ (y:β) in t, ∫ (x:α) in s,f x y ∂μ ∂ν:=by
  apply integral_integral_swap
  convert hf.integrable
  exact Measure.prod_restrict s t
open Complex Topology Filter Real MeasureTheory Set
variable {𝕂:Type*} [RCLike 𝕂]
lemma MeasureTheory.iE
    (f:ℝ→𝕂) {a:ℝ} (ha:0<a) :
    ∫ (y:ℝ) in Ioi 0,f (y*a)/y= ∫ (y:ℝ) in Ioi 0,f y/y:=by
  have:=integral_comp_mul_right_Ioi (fun y↦f y/y) 0 ha
  simp only [RCLike.ofReal_mul,zero_mul,eq_inv_smul_iff₀ (ne_of_gt ha)] at this
  rw [← integral_smul] at this
  rw [← this,setIntegral_congr_fun (by simp)]
  intro _ _
  simp only [RCLike.real_smul_eq_coe_mul]
  rw [mul_comm (a:𝕂),div_mul,mul_div_assoc,div_self ?_,mul_one]
  exact (RCLike.ofReal_ne_zero).mpr <| ne_of_gt ha
lemma MeasureTheory.oL
    (f:ℝ→𝕂) {a:ℝ} (ha:0<a) :
    ∫ (y:ℝ) in Ioi 0,f (a*y)/y= ∫ (y:ℝ) in Ioi 0,f y/y:=by
  convert iE f ha using 5; ring
lemma MeasureTheory.oD (f:ℝ→ℝ) {p:ℝ} (hp:p≠0) :
    ∫ (y:ℝ) in Ioi 0, |p| *f (y^p)/y= ∫ (y:ℝ) in Ioi 0,f y/y:=by
  rw [← integral_comp_rpow_Ioi (fun y↦f y/y) hp,setIntegral_congr_fun (by simp)]
  intro y hy
  have ypos:0<y:=mem_Ioi.mp hy
  simp only [rpow_sub_one ypos.ne',smul_eq_mul]
  field_simp
lemma MeasureTheory.jY (f:ℝ→𝕂) :
    ∫ (y:ℝ) in Ioi 0,f (1/y)/y= ∫ (y:ℝ) in Ioi 0,f y/y:=by
  have:=integral_comp_rpow_Ioi (fun y↦f y/y) (p:= -1) (by simp)
  rw [← this,setIntegral_congr_fun (by simp)]
  intro y hy
  have:(y:𝕂)≠0:=(RCLike.ofReal_ne_zero).mpr <| LT.lt.ne' hy
  simp only [abs_neg,abs_one,rpow_neg_one,map_inv₀,div_inv_eq_mul,
    RCLike.real_smul_eq_coe_mul,RCLike.algebraMap_eq_ofReal]
  ring_nf
  simp [field]
lemma MeasureTheory.jZ
    (f:ℝ→𝕂) {a:ℝ} (ha:0<a) :
    ∫ (y:ℝ) in Ioi 0,f (a/y)/y= ∫ (y:ℝ) in Ioi 0,f y/y:=by
  calc
    _= ∫ (y:ℝ) in Ioi 0,f (a*y)/y:=?_
    _=_:=oL f ha
  convert (jY fun y↦f (a*(1/y))).symm using 4
  · rw [mul_one_div]
  · rw [one_div_one_div]
@[simp]
lemma Function.support_abs {α:Type*} (f:α→𝕂) :
    (fun x↦ ‖f x‖).support=f.support:=by
  simp only [support,ne_eq]; simp_rw [norm_ne_zero_iff]
@[simp]
lemma Function.Ni {f:ℝ→ℝ} :
    (fun x↦((f x) :ℂ)).support=f.support:=by
  apply Function.support_comp_eq (g:=ofReal); simp
lemma Function.gC {s:Set ℝ} {f g:ℝ→𝕂}
    (jU:f.support⊆s) :(f*g).support⊆s:=by
  simp_rw [support_mul',inter_subset,subset_union_of_subset_right jU]
lemma Function.iF {a b:ℝ} {f:ℝ→𝕂}
    (jU:f.support⊆Set.Icc a b) :
    (deriv f).support⊆Set.Icc a b:=by
    have:=support_deriv_subset (f:=fun x↦f x)
    dsimp [tsupport] at this
    have:=subset_trans this <| closure_mono jU
    rwa [closure_Icc] at this
lemma SetIntegral.jv {μ:Measure ℝ}
    {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t:Set ℝ} {f:ℝ→E} (h:f.support⊆t) (ht:MeasurableSet t) :
    ∫ x in s,f x ∂μ= ∫ x in s ∩ t,f x ∂μ:=by
  rw [← setIntegral_indicator ht,indicator_eq_self.2 h]
lemma SetIntegral.iG {a b} {μ:Measure ℝ}
    {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s:Set ℝ} {f:ℝ→E} (h:f.support⊆Icc a b) (hs:Icc a b⊆s) :
    ∫ x in s,f x ∂μ= ∫ x in Icc a b,f x ∂μ:=by
  rw [SetIntegral.jv h measurableSet_Icc,
      inter_eq_self_of_subset_right hs]
lemma intervalIntegral.norm_integral_le_of_norm_le_const' {a b C:ℝ}
    {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f:ℝ→E} (hab:a≤b) (h: ∀ x∈(Icc a b), ‖f x‖ ≤C) :
    ‖∫ x in a..b,f x‖ ≤C* |b-a| :=by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  exact fun x hx↦h x <| mem_Icc_of_Ioc <| uIoc_of_le hab ▸ hx
lemma Filter.oM {a b:ℝ} (f:ℝ→𝕂) (ha:0<a)
    (jU:f.support⊆Set.Icc a b) :
    Tendsto f (𝓝[>]0) (𝓝 0) :=by
  apply Tendsto.comp (tendsto_nhds_of_eventually_eq ?_) tendsto_id
  filter_upwards [Ioo_mem_nhdsGT ha] with c hc; replace hc:=(mem_Ioo.mp hc).2
  have h:c∉Icc a b:=fun h↦by linarith [mem_Icc.mp h]
  convert mt (Function.support_subset_iff.mp jU c) h; simp
lemma Filter.pO {a b:ℝ} (f:ℝ→𝕂)
    (jU:f.support⊆Set.Icc a b) :
    Tendsto f atTop (𝓝 0) :=by
  apply Tendsto.comp (tendsto_nhds_of_eventually_eq ?_) tendsto_id
  filter_upwards [Ioi_mem_atTop b] with c hc; rw [mem_Ioi] at hc
  have h:c∉Icc a b:=fun h↦by linarith [mem_Icc.mp h]
  convert mt (Function.support_subset_iff.mp jU c) h; simp
lemma Filter.mO {a b:ℝ} (f:ℝ→𝕂) (ha:0<a)
    (jU:f.support⊆Set.Icc a b) :
    f =O[𝓝[>] 0] fun _↦(0:ℝ) :=by
  refine Eventually.isBigO ?_
  filter_upwards [Ioo_mem_nhdsGT (by linarith:(0:ℝ)<a)] with c hc
  refine norm_le_zero_iff.mpr <| Function.support_subset_iff'.mp jU c ?_
  exact fun h↦by linarith [mem_Icc.mp h,(mem_Ioo.mp hc).2]
lemma Filter.nQ {a b:ℝ} (f:ℝ→𝕂)
    (jU:f.support⊆Set.Icc a b) :
    f =O[atTop] fun _↦(0:ℝ) :=by
  refine Eventually.isBigO ?_
  filter_upwards [Ioi_mem_atTop b] with c hc; replace hc:=mem_Ioi.mp hc
  refine norm_le_zero_iff.mpr <| Function.support_subset_iff'.mp jU c ?_
  exact fun h↦by linarith [mem_Icc.mp h]
lemma deriv.Qd {f:ℝ→ℝ} :
    deriv (fun x:ℝ↦(f x:ℂ))=(fun x↦((deriv f) x:ℂ)) :=
  funext fun _↦deriv.ofReal_comp
lemma EU (f g:ℝ→ℂ)
    (Oq:DifferentiableOn ℝ f (Ioi 0))
    (Ot:DifferentiableOn ℝ g (Ioi 0))
    (CZ:IntegrableOn (f*deriv g) (Ioi 0))
    (Da:IntegrableOn (deriv f*g) (Ioi 0))
    (Ao:Tendsto (f*g) (𝓝[>] 0) (𝓝 0))
    (Db:Tendsto (f*g) atTop (𝓝 0)) :
    ∫ x in Ioi 0,f x*deriv g x= -∫ x in Ioi 0,deriv f x*g x:=by
  simpa using integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x hx↦Oq.hasDerivAt (Ioi_mem_nhds hx))
    (fun x hx↦Ot.hasDerivAt (Ioi_mem_nhds hx))
    CZ Da Ao Db
lemma lD {a b:ℝ} (f g:ℝ→ℂ) (ha:0<a)
    (h:a≤b)
    (jU:f.support⊆Set.Icc a b)
    (Oq:DifferentiableOn ℝ f (Ioi 0))
    (Ot:DifferentiableOn ℝ g (Ioi 0))
    (Tm:ContinuousOn (deriv f) (Ioi 0))
    (Tv:ContinuousOn (deriv g) (Ioi 0)) :
    ∫ x in Ioi 0,f x*deriv g x= -∫ x in Ioi 0,deriv f x*g x:=by
  have FK:Icc a b⊆Ioi 0:=(Icc_subset_Ioi_iff h).mpr ha
  have Tw:=Function.iF jU
  have Vf:(f*g).support⊆Icc a b:=Function.gC jU
  have CZ:IntegrableOn (f*deriv g) (Ioi 0) :=by
    apply (integrableOn_iff_integrable_of_support_subset <|
           Function.gC jU).mp
    exact Oq.continuousOn.mono FK |>.mul (Tv.mono FK) |>.integrableOn_Icc
  have Da:IntegrableOn (deriv f*g) (Ioi 0) :=by
    apply (integrableOn_iff_integrable_of_support_subset <|
           Function.gC Tw).mp
    exact Tm.mono FK |>.mul (Ot.continuousOn.mono FK) |>.integrableOn_Icc
  have Ao:Tendsto (f*g) (𝓝[>]0) (𝓝 0) :=
    oM (f*g) ha Vf
  have Db:Tendsto (f*g) atTop (𝓝 0) :=pO (f*g) Vf
  apply EU f g Oq Ot CZ Da Ao Db
noncomputable def cw (f g:ℝ→𝕂) (x:ℝ) :𝕂:=
  ∫ y in Ioi 0,f y*g (x/y)/y
lemma ko (f g:ℝ→𝕂) {x:ℝ} (xpos:0<x) :
    cw f g x=cw g f x:=by
  unfold cw
  calc
    _= ∫ y in Ioi 0,f (y*x)*g (1/y)/y:=?_
    _=_:=?_
  · rw [← iE (fun y↦f y*g (x/y)) xpos]
    simp [div_mul_cancel_right₀ <| ne_of_gt xpos]
  · convert (jY fun y↦f (y*x)*g (1/y)).symm using 3
    rw [one_div_one_div,mul_comm,mul_comm_div,one_mul]
lemma sO (f g:ℝ→ℂ) (s:ℂ)
    (hf:IntegrableOn (fun x y↦f y*g (x/y)/(y:ℂ)*(x:ℂ)^(s-1)).uncurry
      (Ioi 0×ˢIoi 0)) :
    (mellin) (cw f g) s=(mellin) f s*(mellin) g s:=by
  dsimp [mellin,cw]
  set f₁:ℝ × ℝ→ℂ:=
    fun ⟨x,y⟩↦f y*g (x/y)/(y:ℂ)*(x:ℂ)^(s-1)
  calc
    _= ∫ (x:ℝ) in Ioi 0, ∫ (y:ℝ) in Ioi 0,f₁ (x,y) :=?_
    _= ∫ (y:ℝ) in Ioi 0, ∫ (x:ℝ) in Ioi 0,f₁ (x,y) :=
        vP _ hf
    _= ∫ (y:ℝ) in Ioi 0, ∫ (x:ℝ) in Ioi 0,
        f y*g (x/y)/↑y*↑x^(s-1) :=rfl
    _= ∫ (y:ℝ) in Ioi 0, ∫ (x:ℝ) in Ioi 0,
        f y*g (x*y/y)/↑y*↑(x*y)^(s-1)*y:=?_
    _= ∫ (y:ℝ) in Ioi 0, ∫ (x:ℝ) in Ioi 0,
        f y*↑y^(s-1)*(g x*↑x^(s-1)) :=?_
    _= ∫ (y:ℝ) in Ioi 0,
        f y*↑y^(s-1)* ∫ (x:ℝ) in Ioi 0,g x*↑x^(s-1) :=?_
    _=_:=integral_mul_const _ _
  <;> try (rw [setIntegral_congr_fun (by simp)]; intro y hy; simp only [ofReal_mul])
  · simp only [integral_mul_const,f₁,mul_comm]
  · simp only [integral_mul_const]
    have:=integral_comp_mul_right_Ioi
      (fun x↦f y*g (x/y)/(y:ℂ)*(x:ℂ)^(s-1)) 0 hy
    have Qe:(y:ℂ)≠0:=slitPlane_ne_zero (Or.inl hy)
    field_simp at this ⊢
    simp only [ofReal_mul,one_div,mul_zero,real_smul,ofReal_inv,field] at this ⊢
    rw [← this]
    field_simp
    congr with x
    ring_nf
  · rw [setIntegral_congr_fun (by simp)]
    intro x hx
    have Qg:y≠0:=ne_of_gt (mem_Ioi.mp hy)
    have Qe:(y:ℂ)≠0:=by exact_mod_cast Qg
    field_simp
    rw [mul_cpow_ofReal_nonneg hy.le hx.le]
    ring
  · apply integral_const_mul
  · congr <;> ext <;> ring
lemma zD {ν:ℝ→ℝ} (cP:ContDiff ℝ 1 ν)
    (bC:ν.support⊆Set.Icc (1/2) 2)
    {s:ℂ} (hs:s≠0) :
    ∫ (x:ℝ) in Ioi 0,(ν x)*(x:ℂ)^(s-1)=
    -(1/s)* ∫ (x:ℝ) in Ioi 0,(deriv ν x)*(x:ℂ)^s:=by
  let g (s:ℂ) :=fun (x:ℝ)  ↦x^s/s
  have Vg {s:ℂ} (hs:s≠0) {x: ℝ} (hx:x∈Ioi 0) :
      deriv (g s) x=x^(s-1) :=by
    have:=HasDerivAt.cpow_const (c:=s) (hasDerivAt_id (x:ℂ)) (Or.inl hx)
    simp_rw [mul_one,id_eq] at this
    rw [deriv_div_const,deriv.comp_ofReal (e:=fun x↦x^s)]
    · rw [this.deriv,mul_div_right_comm,div_self hs,one_mul]
    · apply hasDerivAt_deriv_iff.mp
      simp only [this.deriv,this]
  calc
    _=  ∫ (x:ℝ) in Ioi 0,↑(ν x)*deriv (@g s) x:=?_
    _= -∫ (x:ℝ) in Ioi 0,deriv (fun x↦↑(ν x)) x* @g s x:=?_
    _= -∫ (x:ℝ) in Ioi 0,deriv ν x* @g s x:=?_
    _= -∫ (x:ℝ) in Ioi 0,deriv ν x*x^s/s:=by simp only [mul_div,g]
    _=_:=?_
  · rw [setIntegral_congr_fun (by simp)]
    intro _ hx
    simp only [Vg hs hx]
  · apply lD (ν ·) (g s)
      (a:=1/2) (b:=2) (by norm_num) (by norm_num)
    · simpa only [Function.support_subset_iff,ne_eq,ofReal_eq_zero]
    · exact (Differentiable.kH.mpr
        (cP.differentiable (by norm_num))).differentiableOn
    · refine DifferentiableOn.div_const ?_ s
      intro a ha
      refine DifferentiableAt.comp_ofReal (e:=fun x↦x^s) ?_ |>.differentiableWithinAt
      apply differentiableAt_fun_id.cpow (differentiableAt_const s) <| by exact Or.inl ha
    · simp only [deriv.Qd]
      exact continuous_ofReal.comp (cP.continuous_deriv (by norm_num)) |>.continuousOn
    · apply ContinuousOn.congr (f:=fun (x:ℝ)↦(x:ℂ)^(s-1)) ?_
        fun x hx↦Vg hs hx
      exact Continuous.continuousOn (by continuity) |>.cpow continuousOn_const (by simp)
  · congr; funext; congr
    apply (hasDerivAt_deriv_iff.mpr ?_).ofReal_comp.deriv
    exact cP.contDiffAt.differentiableAt (by norm_num)
  · simp only [neg_mul,neg_inj]
    conv=>lhs; rhs; intro; rw [← mul_one_div,mul_comm]
    rw [integral_const_mul]
lemma QN {ν:ℝ→ℝ} (cP:ContDiff ℝ 1 ν)
    (bC:ν.support⊆Set.Icc (1/2) 2) :
    ∃ C>0, ∀ (σ₁:ℝ) (_:0<σ₁) (s:ℂ) (_:σ₁≤ s.re) (_:s.re≤2),
    ‖(mellin) (fun x↦(ν x:ℂ)) s‖ ≤C* ‖s‖⁻¹:=by
  let f:=fun (x:ℝ)↦ ‖deriv ν x‖
  have cont:ContinuousOn f (Icc (1/2) 2) :=
    (Continuous.comp (by continuity) <| cP.continuous_deriv (by norm_num)).continuousOn
  obtain ⟨a,_,max⟩:=isCompact_Icc.exists_isMaxOn (f:=f) (by norm_num) cont
  let σ₂:ℝ:=2
  let C:ℝ:=f a*2^σ₂*(3/2)
  have Nj: ∀ (σ₁:ℝ),0<σ₁→ ∀ (s:ℂ),σ₁≤ s.re→s.re≤2→
      ‖(mellin) (fun x↦(ν x:ℂ)) s‖ ≤C* ‖s‖⁻¹:=by
    intro σ₁ Qj s hs₁ hs₂
    have gI: s≠0:=fun h↦by linarith [zero_re ▸ h ▸ hs₁]
    simp only [mellin,f,zD cP bC gI,norm_mul,smul_eq_mul,mul_comm]
    gcongr
    · simp
    calc
      _≤ ∫ (x:ℝ) in Ioi 0, ‖(deriv ν x*(x:ℂ)^s)‖ :=?_
      _= ∫ (x:ℝ) in Icc (1/2) 2, ‖(deriv ν x*(x:ℂ)^s)‖ :=?_
      _≤ ‖∫ (x:ℝ) in Icc (1/2) 2, ‖(deriv ν x*(x:ℂ)^s)‖‖ :=
          le_abs_self _
      _≤_:=?_
    · simp_rw [norm_integral_le_integral_norm]
    · apply SetIntegral.iG
      · simp only [Function.support_abs,Function.support_mul,Function.Ni]
        apply subset_trans (by apply inter_subset_left) <| Function.iF bC
      · exact (Icc_subset_Ioi_iff (by norm_num)).mpr (by norm_num)
    · have:=intervalIntegral.norm_integral_le_of_norm_le_const' (C:=f a*2^σ₂)
        (f:=fun x↦f x* ‖(x:ℂ)^s‖) (a:=(1/2:ℝ)) ( b:=2) (by norm_num) ?_
      · simp only [Real.norm_eq_abs,norm_real,norm_mul] at this ⊢
        rwa [(by norm_num: |(2:ℝ)-1/2| =3/2),
            intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc] at this
      · intro x hx;
        have f_bound:=isMaxOn_iff.mp max x hx
        have Vh: ‖(x:ℂ)^s‖ ≤2^σ₂:=by
          rw [norm_cpow_eq_rpow_re_of_pos (by linarith [mem_Icc.mp hx])]
          have xpos:0≤x:=by linarith [(mem_Icc.mp hx).1]
          have h:=rpow_le_rpow xpos (mem_Icc.mp hx).2 (by linarith:0≤ s.re)
          exact le_trans h <| rpow_le_rpow_of_exponent_le (by norm_num) hs₂
        convert! mul_le_mul f_bound Vh (norm_nonneg _) ?_ using 1 <;> simp [f]
  have Cnonneg:0≤C:=by
    have hh:=Nj 1 (by norm_num) ((3:ℂ)/2) (by norm_num) (by norm_num)
    have hhh:0≤ ‖(mellin) (fun x↦(ν x:ℂ)) ((3:ℂ)/2)‖ :=by positivity
    have acp:0< ‖(3:ℂ)/2‖⁻¹:=by norm_num
    have:=hhh.trans hh
    exact (mul_nonneg_iff_of_pos_right acp).mp this
  by_cases Ro:C=0
  · refine ⟨1,by linarith,?_⟩
    intro ε εpos s hs₁ hs₂
    have:=Nj ε εpos s hs₁ hs₂
    rw [Ro,zero_mul] at this
    have:0≤1* ‖s‖⁻¹:=by positivity
    linarith
  · exact ⟨C,lt_of_le_of_ne Cnonneg fun a↦Ro (id (Eq.symm a)),Nj⟩
noncomputable def bY (ν:ℝ→ℝ) (ε:ℝ) :ℝ→ℝ:=
  fun x↦ν (x^(1/ε))/ε
lemma Nk {ν:ℝ→ℝ} (cD: ∫ x in Ioi 0,ν x/x=1) {ε:ℝ}
    (εpos:0<ε) : ∫ x in Ioi 0,((bY ν ε) x)/x=1:=
  calc
    _= ∫ (x:ℝ) in Ioi 0,(|1/ε| *x^(1/ε-1))•
      ((fun z↦(ν z)/z) (x^(1/ε))) :=by
      apply setIntegral_congr_ae measurableSet_Ioi
      filter_upwards with x hx
      simp only [smul_eq_mul,abs_of_pos (one_div_pos.mpr εpos)]
      symm; calc
        _=(ν (x^(1/ε))/x^(1/ε))*x^(1/ε-1)*(1/ε) :=by ring
        _=_:=by rw [rpow_sub hx,rpow_one]
        _=(ν (x^(1/ε))/x^(1/ε)*x^(1/ε)/x)*(1/ ε) :=by ring
        _=_:=by rw [div_mul_cancel₀ _ (ne_of_gt (rpow_pos_of_pos hx (1/ε)))]
        _=(ν (x^(1/ε))/ε/x) :=by ring
    _=1:=by
      rw [integral_comp_rpow_Ioi (fun z↦(ν z)/z), ← cD]
      simp only [ne_eq,div_eq_zero_iff,one_ne_zero,εpos.ne',or_self,not_false_eq_true]
lemma Bz {ν:ℝ→ℝ} {ε:ℝ} (εpos:0<ε)
    (bC:ν.support⊆Icc (1/2) 2) :
    (fun x↦if x<0 then 0 else bY ν ε x).support⊆Icc (2^(-ε)) (2^ε) :=by
  unfold bY
  simp only [one_div,Function.support_subset_iff,ne_eq,ite_eq_left_iff,not_lt,div_eq_zero_iff,
    not_forall,exists_prop,mem_Icc,and_imp]
  intro x hx h; push Not at h
  have:=bC <| Function.mem_support.mpr h.1
  simp only [one_div,mem_Icc] at this
  have hl:=(le_rpow_inv_iff_of_pos (by norm_num) hx εpos).mp this.1
  rw [inv_rpow (by norm_num) ε, ← rpow_neg (by norm_num)] at hl
  refine ⟨hl,(rpow_inv_le_iff_of_pos ?_ (by norm_num) εpos).mp this.2⟩
  linarith [(by apply rpow_nonneg (by norm_num) :0≤(2:ℝ)^(-ε))]
lemma lG {ν:ℝ→ℝ} {ε x:ℝ} (εpos:0<ε) (Nl:0≤x)
    (bC:ν.support⊆Icc (1/2) 2) :
    bY ν ε x≠0→x∈Icc (2^(-ε)) (2^ε) :=by
  intro h
  have:(fun x↦if x<0 then 0 else bY ν ε x) x=bY ν ε x:=by
    simp [Nl]
  rw [← this] at h
  exact (Function.support_subset_iff.mp <| Bz εpos bC) _ h
lemma nC {ν:ℝ→ℝ} {ε x:ℝ} (εpos:0<ε) (Nl:0≤x)
    (bC:ν.support⊆Icc (1/2) 2) :
    x∉Icc (2^(-ε)) (2^ε)→bY ν ε x=0:=by
  contrapose!; exact lG εpos Nl bC
lemma jV {ν:ℝ→ℝ} {ε:ℝ} (εpos:0<ε)
    (cP:ContDiff ℝ 1 ν) :Continuous (fun x↦bY ν ε x) :=by
  apply cP.continuous.comp (g:=ν) _ |>.div_const
  exact continuous_id.rpow_const fun _↦Or.inr <| div_nonneg (by norm_num) εpos.le
lemma sP {ν:ℝ→ℝ} {ε:ℝ} (εpos:0<ε)
    (cP:ContDiff ℝ 1 ν) :Continuous (fun x↦(bY ν ε x:ℂ)) :=
  continuous_ofReal.comp <| jV εpos cP
theorem EW (ν:ℝ→ℝ) {ε:ℝ} (εpos:ε>0) (s:ℂ) :
    (mellin) (fun x↦(bY ν ε x:ℂ)) s=(mellin) (fun x↦(ν x:ℂ)) (ε*s) :=by
  unfold bY
  push_cast
  rw [mellin_div_const,mellin_comp_rpow (fun x↦(ν x:ℂ)),abs_of_nonneg (by positivity)]
  simp only [one_div,inv_inv,ofReal_inv,div_inv_eq_mul,real_smul]
  rw [mul_div_cancel_left₀ _ (ne_zero_of_re_pos εpos)]
  ring_nf
lemma Vi (s:ℂ) (h:s.re>0) :
    (mellin) ((fun x↦if 0<x ∧ x≤1 then 1 else 0)) s=1/s:=by
  rw [← (hasMellin_one_Ioc h).right]
  congr 1
  ext x
  simp [Set.indicator_apply,Set.mem_Ioc]
noncomputable def dD (ν:ℝ→ℝ) (ε:ℝ) :ℝ→ℝ:=
  cw (fun x↦if 0<x ∧ x≤1 then 1 else 0) (bY ν ε)
lemma kB {ε:ℝ} (εpos:0<ε) :
    (1-2^(-ε))/ε<Real.log 2:=by
  apply (div_lt_iff₀' εpos).mpr
  have:1-1/(2:ℝ)^ε=((2:ℝ)^ε-1)/(2:ℝ)^ε:=by
    rw [sub_div,div_self (by positivity)]
  rw [← Real.log_rpow (by norm_num),rpow_neg (by norm_num),inv_eq_one_div (2^ε),this]
  set c:=(2:ℝ)^ε
  have hc:1<c:=by
    rw [← rpow_zero (2:ℝ)]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) εpos
  apply (div_lt_iff₀' (by positivity)).mpr <| lt_sub_iff_add_lt'.mp ?_
  let f:=(fun x↦x*Real.log x-x)
  rw [(by simp [f]: -1=f 1),(by simp [f]:c*Real.log c-c=f c)]
  have mono: StrictMonoOn f <| Ici 1:=by
    refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
    · apply continuousOn_id.mul (continuousOn_id.log ?_) |>.sub continuousOn_id
      intro x hx; simp only [mem_Ici] at hx; simp only [id_eq,ne_eq]; linarith
    · intro x hx; simp only [nonempty_Iio,interior_Ici',mem_Ioi] at hx
      dsimp only [f]
      rw [deriv_fun_sub,deriv_fun_mul,Real.deriv_log,deriv_id'',one_mul,mul_inv_cancel₀]
      · simp [log_pos hx]
      · linarith
      · simp only [differentiableAt_fun_id]
      · simp only [differentiableAt_log_iff,ne_eq]; linarith
      · exact differentiableAt_fun_id.mul <| differentiableAt_fun_id.log (by linarith)
      · simp only [differentiableAt_fun_id]
  exact mono (by rw [mem_Ici]) (mem_Ici.mpr <| le_of_lt hc) hc
lemma rF {x ε:ℝ} (hx:x≤1-Real.log 2* ε) (εpos:0<ε) :
    x<2^(-ε) :=by
  calc
    x≤1-Real.log 2* ε:=hx
    _<2^(-ε) :=?_
  rw [sub_lt_iff_lt_add,add_comm, ← sub_lt_iff_lt_add]
  exact (div_lt_iff₀ εpos).mp <| kB εpos
lemma yI {ν:ℝ→ℝ} (bC:ν.support⊆Icc (1/2) 2)
    (cD: ∫ x in Ioi 0,ν x/x=1) :
    ∃ (c:ℝ),0<c ∧ c=Real.log 2 ∧
      ∀ (ε x) (_:0<ε),0<x→x≤1-c* ε→dD ν ε x=1:=by
  set c:=Real.log 2; use c
  refine ⟨log_pos (by norm_num),rfl,?_⟩
  intro ε x εpos xpos hx
  have hx2:=rF hx εpos
  rewrite [← Nk cD εpos]
  unfold dD cw
  calc
    _= ∫ (y:ℝ) in Ioi 0,
        indicator (Ioc 0 1) (fun y↦bY ν ε (x/y)/↑y) y:=?_
    _= ∫ (y:ℝ) in Ioi 0,bY ν ε (x/y)/y:=?_
    _=_:=jZ (fun y↦bY ν ε y) xpos
  · rw [setIntegral_congr_fun (by simp)]
    intro y hy
    by_cases h:y≤1 <;> simp [indicator,mem_Ioi.mp hy,h]
  · rw [setIntegral_congr_fun (by simp)]
    intro y hy
    have:y≠0:=by
      rintro rfl
      simp at hy
    simp only [indicator_apply_eq_self,mem_Ioc,not_and,not_le,div_eq_zero_iff,this,or_false]
    intro hy2; replace hy2:=hy2 <| mem_Ioi.mp hy
    apply nC εpos ?_ bC
    · simp only [mem_Icc,not_and,not_le]; intro
      linarith [(by apply (div_lt_iff₀ (by linarith)).mpr; nlinarith:x/y<2^(-ε))]
    · rw [le_div_iff₀ (by linarith),zero_mul]; exact xpos.le
lemma rG {x ε:ℝ} (hx:1+(2*Real.log 2)* ε≤x)
    (hε:ε∈Ioo 0 1) :
    2^ε<x:=by
  calc
    x≥1+(2*Real.log 2)* ε:=hx
    _>2^ε:=?_
  refine lt_add_of_sub_left_lt <| (div_lt_iff₀ hε.1).mp ?_
  calc
    2*Real.log 2>2*(1-2^(-ε))/ε:=?_
    _>2^ε*(1-2^(-ε))/ε:=?_
    _=(2^ε-1)/ε:=?_
  · field_simp
    exact kB hε.1
  · have:(2:ℝ)^ε<2:=by
      have h:=rpow_lt_rpow_of_exponent_lt (x:=2) (by norm_num) hε.2
      rwa [Real.rpow_one] at h
    have pos: 0<(1-2^(-ε))/ε:=by
      refine div_pos ?_ hε.1
      rw [sub_pos]
      have h:=rpow_lt_rpow_of_exponent_lt (x:=2) (by norm_num) (neg_lt_zero.mpr hε.1)
      rwa [Real.rpow_zero] at h
    have:=(mul_lt_mul_iff_left₀ pos).mpr this
    ring_nf at this ⊢
    exact this
  · have:(2:ℝ)^ε*(2:ℝ)^(-ε)=(2:ℝ)^(ε-ε) :=by
      rw [← rpow_add (by norm_num),add_neg_cancel,sub_self]
    conv=>lhs; lhs; ring_nf; rhs; simp [this]
lemma qQ {x y ε:ℝ} (hε:ε∈Ioo 0 1) (hy:y∈Ioc 0 1)
  (hx2:2^ε<x) :
    2<(x/y)^(1/ε) :=by
  obtain ⟨εpos,ε1⟩:=hε
  obtain ⟨ypos,y1⟩:=hy
  calc
    _>(2^ε/y)^(1/ε) :=?_
    _=2/y^(1/ε) :=?_
    _≥2/y:=?_
    _≥2:=?_
  · rw [gt_iff_lt,div_rpow,div_rpow,lt_div_iff₀,mul_comm_div,div_self,mul_one]
    <;> try positivity
    · exact rpow_lt_rpow (by positivity) hx2 (by positivity)
    · exact LT.lt.le <| lt_trans (by positivity) hx2
  · rw [div_rpow, ← rpow_mul,mul_div_cancel₀ 1 <| ne_of_gt εpos,rpow_one] <;> positivity
  · have:y^(1/ε)≤y:=by
      nth_rewrite 2 [← rpow_one y]
      exact rpow_le_rpow_of_exponent_ge ypos y1 (by linarith [one_lt_one_div εpos ε1])
    have pos:0<y^(1/ε) :=rpow_pos_of_pos ypos _
    rw [ge_iff_le,div_le_iff₀,div_mul_eq_mul_div,le_div_iff₀',mul_comm] <;> try linarith
  · rw [ge_iff_le,le_div_iff₀ <| ypos]; exact (mul_le_iff_le_one_right zero_lt_two).mpr y1
lemma jc {ν:ℝ→ℝ} (bC:ν.support⊆Icc (1/2) 2) :
    ∃ (c:ℝ),0<c ∧ c=2*Real.log 2 ∧
      ∀ (ε x) (_:ε∈Ioo 0 1),1+c* ε≤x→dD ν ε x=0:=by
  set c:=2*Real.log 2; use c
  constructor
  · simp only [c,zero_lt_two,mul_pos_iff_of_pos_left]; exact log_pos (by norm_num)
  constructor
  · rfl
  intro ε x hε hx
  have hx2:=rG hx hε
  unfold dD cw
  simp only [ite_mul,one_mul,zero_mul,RCLike.ofReal_real_eq_id,id_eq]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  have ypos:=mem_Ioi.mp hy
  by_cases y1:y≤1
  swap
  · simp [ypos,y1]
  simp only [mem_Ioi.mp hy,y1,and_self, ↓reduceIte,div_eq_zero_iff]; left
  apply nC hε.1 ?_ bC
  on_goal 1=>
    simp only [mem_Icc,not_and,not_le]
  on_goal 2=>
    suffices h:2^ε<x/y by
      linarith [(by apply rpow_pos_of_pos (by norm_num) :0<(2:ℝ)^ε)]
  all_goals
  try intro
  have:x/y=((x/y)^(1/ε))^ε:=by
    rw [← rpow_mul]
    simp only [one_div,inv_mul_cancel₀ (ne_of_gt hε.1),rpow_one]
    apply div_nonneg_iff.mpr; left;
    exact ⟨(le_trans (rpow_pos_of_pos (by norm_num) ε).le) hx2.le,ypos.le⟩
  rw [this]
  refine rpow_lt_rpow (by norm_num) ?_ hε.1
  exact qQ hε ⟨ypos,y1⟩ hx2
lemma kC {ν:ℝ→ℝ} (wX: ∀ x>0,0≤ν x)
     {x ε:ℝ} (xpos:0<x) (εpos:0<ε) :
    0≤bY ν ε x:=by
  dsimp [bY]
  have:0<x^(1/ε) :=by positivity
  have:0≤ν (x^(1/ε)) :=wX _ this
  positivity
lemma sW {f g:ℝ→ℝ} (f_nonneg: ∀ x>0,0≤f x)
    (g_nonneg: ∀ x>0,0≤g x) {x:ℝ} (xpos:0<x) :
    0≤cw f g x:=by
  dsimp [cw]
  apply MeasureTheory.setIntegral_nonneg
  · exact measurableSet_Ioi
  · intro y ypos; simp only [mem_Ioi] at ypos
    have:0≤f y:=f_nonneg _ ypos
    have:0<x/y:=by positivity
    have:0≤g (x/y) :=g_nonneg _ this
    positivity
lemma tj {ν:ℝ→ℝ} (wX: ∀ x>0,0≤ν x) {ε x:ℝ}
    (xpos:0<x) (εpos:0<ε) :0≤dD ν ε x:=by
  dsimp [dD]
  apply sW ?_ ?_ xpos
  · intro y hy; by_cases h:y≤1 <;> simp [h,hy]
  · intro y ypos; exact kC wX ypos εpos
lemma Jy {x ε:ℝ} {ν:ℝ→ℝ} (xpos:0<x) (εpos:0<ε)
    (cD: ∫ x in Ioi 0,ν x/x=1) :
    ∫ (y:ℝ) in Ioi 0,ν ((x/y)^(1/ε))/ε/y=1:=by
    calc
      _= ∫ (y:ℝ) in Ioi 0,(ν (y^(1/ε))/ε)/y:=?_
      _= ∫ (y:ℝ) in Ioi 0,ν y/y:=?_
      _=1:=cD
    · have:=jZ (fun y↦ν ((x/y)^(1/ε))/ε) xpos
      convert! this.symm using 1
      congr; funext y; congr; field_simp [mul_comm]
    · have:=oD (fun y↦ν y) (one_div_ne_zero εpos.ne')
      rw [← this,abs_of_pos <| one_div_pos.mpr εpos]
      field_simp
lemma wY {ν:ℝ→ℝ} (wX: ∀ x>0,0≤ν x)
    (cD: ∫ x in Ioi 0,ν x/x=1) {ε:ℝ} (εpos:0<ε) {x:ℝ} (xpos:0<x) :
    dD ν ε x≤1:=by
  unfold dD cw bY
  have:=Jy xpos εpos cD
  calc
    _= ∫ (y:ℝ) in Ioi 0,
        (fun y↦if y∈Ioc 0 1 then 1 else 0) y*(ν ((x/y)^(1/ε))/ε/y) :=?_
    _≤ ∫ (y:ℝ) in Ioi 0,(ν ((x/y)^(1/ε))/ε)/y:=?_
    _=1:=this
  · rw [setIntegral_congr_fun (by simp)]
    simp only [ite_mul,one_mul,zero_mul,RCLike.ofReal_real_eq_id,id_eq,mem_Ioc]
    intro y hy; aesop
  · refine setIntegral_mono_on ?_ (integrable_of_integral_eq_one this) (by simp) ?_
    · refine integrable_of_integral_eq_one this |>.bdd_mul ?_
        (ae_of_all _ <| by aesop)
      have:(fun x↦if 0<x ∧ x≤1 then 1 else 0)=
          indicator (Ioc 0 1) (1:ℝ→ℝ) :=by
        aesop
      simp only [mem_Ioc,this,measurableSet_Ioc,aestronglyMeasurable_indicator_iff]
      exact aestronglyMeasurable_one
    · simp only [ite_mul,one_mul,zero_mul]
      intro y hy
      by_cases h:y≤1
      · aesop
      field_simp
      simp only [mem_Ioc,h,and_false, ↓reduceIte,one_div,mul_zero]
      simp only [mem_Ioi] at hy
      apply div_nonneg
      · apply wX; exact rpow_pos_of_pos (div_pos xpos <| mem_Ioi.mp hy) _
      · positivity
lemma wZ {ν:ℝ→ℝ} (cP:ContDiff ℝ 1 ν)
    (bC:ν.support⊆Icc (1/2) 2)
    {ε:ℝ} (εpos:0<ε) {s:ℂ} (hs:0<s.re) :
    (mellin) (fun x↦(dD ν ε x:ℂ)) s=
      s⁻¹*(mellin) (fun x↦(ν x:ℂ)) (ε*s) :=by
  let f':ℝ→ℂ:=fun x↦bY ν ε x
  let f:ℝ→ℂ:=fun x↦bY ν ε x/x
  let g:ℝ→ℂ:=fun x↦if 0<x ∧ x≤1 then 1 else 0
  let F:ℝ × ℝ→ℂ:=Function.uncurry fun x y↦f y*g (x/y)*(x:ℂ)^(s-1)
  let S:={⟨x,y⟩:ℝ × ℝ | 0<x  ∧ x≤y ∧ 2^(-ε)≤y ∧ y≤2^ε}
  let F':ℝ × ℝ→ℂ:=piecewise S (fun ⟨x,y⟩↦f y*(x:ℂ)^(s-1))
     (fun _↦0)
  let Tx:=Ioc 0 ((2:ℝ)^ε)
  let Ty:=Icc ((2:ℝ)^(-ε)) ((2:ℝ)^ε)
  have Seq:S=(Tx×ˢTy) ∩ {(x,y) :ℝ × ℝ | x≤y} :=by
    ext ⟨x,y⟩; constructor
    · exact fun h↦⟨⟨⟨h.1,le_trans h.2.1 h.2.2.2⟩,⟨h.2.2.1,h.2.2.2⟩⟩,h.2.1⟩
    · exact fun h↦  ⟨h.1.1.1,⟨h.2,h.1.2.1,h.1.2.2⟩⟩
  have aaL:S⊆Ioi 0×ˢIoi 0:=
    fun z hz↦⟨hz.1,lt_of_lt_of_le (by apply rpow_pos_of_pos; norm_num) hz.2.2.1⟩
  have aaM: S⊆Tx×ˢTy:=by simp_rw [Seq,inter_subset_left]
  have Smeas:MeasurableSet S:=by
    rw [Seq]; apply MeasurableSet.inter ?_ <| measurableSet_le measurable_fst measurable_snd
    simp [measurableSet_prod,Tx,Ty]
  have aaN: IntegrableOn F (Ioi 0×ˢIoi 0) :=by
    apply IntegrableOn.congr_fun (f:=F') ?_ ?_ (by simp [measurableSet_prod]); swap
    · simp only [F,F',f,g,mul_ite,mul_one,mul_zero]
      intro ⟨x,y⟩ hz
      by_cases hS:⟨x,y⟩∈S <;> simp only [hS,piecewise]
      <;> simp only [mem_prod,mem_Ioi,mem_setOf_eq,not_and,not_le,S] at hz hS
      · simp [div_pos hz.1 hz.2,(div_le_one hz.2).mpr hS.2.1]
      · by_cases hxy:x/y≤1
        swap
        · simp [hxy]
        have hy:y∉Icc (2^(-ε)) (2^ε) :=by
          simp only [mem_Icc,not_and,not_le]; exact hS hz.1 <| (div_le_one hz.2).mp hxy
        simp [nC εpos hz.2.le bC hy]
    · apply Integrable.piecewise Smeas ?_ integrableOn_zero
      simp only [IntegrableOn,Measure.restrict_restrict_of_subset aaL]
      apply MeasureTheory.Integrable.mono_measure ?_
      · apply MeasureTheory.Measure.restrict_mono' aaM.eventuallyLE le_rfl
      have:volume.restrict (Tx×ˢTy)=(volume.restrict Tx).prod (volume.restrict Ty) :=by
        rw [Measure.prod_restrict,MeasureTheory.Measure.volume_eq_prod]
      conv=>rw [this]; lhs; intro; rw [mul_comm]
      apply MeasureTheory.Integrable.mul_prod (f:=fun x↦(x:ℂ)^(s-1))
        (μ:=Measure.restrict volume Tx)
      · simp only [Tx]
        rw [← IntegrableOn,integrableOn_Ioc_iff_integrableOn_Ioo,
          intervalIntegral.integrableOn_Ioo_cpow_iff]
        · simp [hs]
        · apply rpow_pos_of_pos (by norm_num)
      · apply (ContinuousOn.div ?_ ?_ ?_).integrableOn_compact isCompact_Icc
        · exact (sP εpos cP).continuousOn
        · exact continuous_ofReal.continuousOn
        · intro x hx; simp only [mem_Icc] at hx; simp only [ofReal_ne_zero]
          linarith [(by apply rpow_pos_of_pos (by norm_num) :(0:ℝ)<2^(-ε))]
  have:(mellin) (cw g f') s=(mellin) g s*(mellin) f' s:=by
    rw [mul_comm, ← sO f' g s
      (by convert aaN using 1; simp only [f',F,f]; field_simp)]
    dsimp [mellin]; rw [setIntegral_congr_fun (by simp)]
    intro x hx; simp_rw [ko _ _ <| mem_Ioi.mp hx]
  convert! this using 1
  · congr; funext x; convert! integral_ofReal.symm
    simp only [cw,RCLike.ofReal_div,ite_mul,one_mul,zero_mul, @apply_ite ℝ ℂ,
      algebraMap.coe_zero,g]; rfl
  · rw [Vi s hs,EW ν εpos s]
    simp
lemma JE {ν:ℝ→ℝ} (cP:ContDiff ℝ 1 ν)
    (bC:ν.support⊆Set.Icc (1/2) 2) :
    ∃ (C:ℝ) (_:0<C), ∀ (σ₁:ℝ) (_:0<σ₁)
    (s) (_:σ₁≤ s.re) (_:s.re≤2) (ε:ℝ) (_:0<ε) (_:ε<1),
    ‖(mellin) (fun x↦(dD ν ε x:ℂ)) s‖ ≤C*(ε* ‖s‖ ^2)⁻¹:=by
  obtain ⟨C,Cpos,hC⟩:=QN cP bC
  refine ⟨C,Cpos,?_⟩
  intro σ₁ Qj s hs1 hs2 ε εpos EY
  rw [wZ cP bC εpos <| lt_of_le_of_lt' hs1 Qj]
  have hh1:ε*σ₁≤(ε*s).re:=by
    simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
    nlinarith
  have hh2:(ε*s).re≤2:=by
    simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
    nlinarith
  calc
    ‖s⁻¹*(mellin) (fun x↦(ν x:ℂ)) (ε*s)‖ =
        ‖s⁻¹‖ * ‖(mellin) (fun x↦(ν x:ℂ)) (ε*s)‖ :=by simp
    _                        ≤ ‖s⁻¹‖ *(C*(ε* ‖s‖)⁻¹) :=by
      gcongr
      convert! hC (ε*σ₁) (by positivity) (ε*s) hh1 hh2
      simp [abs_eq_self.mpr εpos.le]
    _                        =C*(ε* ‖s‖ ^2)⁻¹:=by
      simp only [norm_inv,mul_inv_rev]
      ring
lemma kG {dL:ℝ→ℝ}
    (lO:ContDiff ℝ 1 dL)
    (Dt: ∀ x>0,0≤dL x)
    (jI:dL.support⊆Icc (1/2) 2)
    {ε:ℝ} (εpos:0<ε) {y:ℝ} (ypos:0<y) :
    ContinuousAt (fun x↦dD dL ε x) y:=by
  apply ContinuousAt.congr
    (f:=(fun x↦cw (bY dL ε)
      (fun x↦if 0<x ∧ x≤1 then 1 else 0) x)) _
  · filter_upwards [lt_mem_nhds ypos] with x hx
    apply ko _ _ hx
  apply continuousAt_of_dominated (bound:=(fun x↦2^ε*bY dL ε x))
  · filter_upwards [lt_mem_nhds ypos] with x hx
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · apply Measurable.mul
      · exact Continuous.measurable <| jV εpos lO
      · apply Measurable.ite _ (by fun_prop) (by fun_prop)
        apply MeasurableSet.congr (s:=Ici x) (by measurability)
        ext a
        constructor
        · intro ha
          have apos:0<a:=lt_of_lt_of_le hx ha
          constructor
          · exact div_pos hx apos
          · exact (div_le_one apos).mpr ha
        · intro ha
          have:0<a:=(div_pos_iff_of_pos_left hx).mp ha.1
          exact (div_le_one this).mp ha.2
    · fun_prop
  · filter_upwards [lt_mem_nhds ypos] with x hx
    filter_upwards [ae_restrict_mem (by measurability)] with t ht
    simp only [mul_ite,mul_one,mul_zero,RCLike.ofReal_real_eq_id,id_eq,norm_div,norm_eq_abs]
    by_cases! h:bY dL ε t=0
    · simp [h]
    have:=lG εpos ht.le jI h
    have Qk:0≤bY dL ε t:=by
      apply kC <;> assumption
    calc
      _≤ |bY dL ε t| / |t| :=by
        gcongr
        · split_ifs with h
          · apply le_refl
          · exact Qk
      _≤_:=by
        rw [_root_.abs_of_nonneg Qk,mul_comm,div_eq_mul_one_div,_root_.abs_of_pos ht]
        gcongr
        apply (one_div_le ht (by bound)).mpr
        · convert this.1 using 1
          rw [div_eq_iff (by positivity), ← rpow_add (by norm_num),neg_add_cancel,rpow_zero]
  · apply Integrable.const_mul
    apply (integrable_indicator_iff (by measurability)).mp
    apply (integrableOn_iff_integrable_of_support_subset (s:=Icc (2^(-ε)) (2^ε)) _).mp
    · apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply ContinuousOn.congr  (f:=bY dL ε)
      · apply Continuous.continuousOn
        apply jV<;> assumption
      · intro x hx
        have:x∈Ioi 0:=by
          apply mem_Ioi.mpr
          apply lt_of_lt_of_le (by bound) hx.1
        rw [indicator,if_pos this]
    · unfold indicator
      simp_rw [mem_Ioi]
      apply Function.support_subset_iff.mpr
      simp only [ne_eq,ite_eq_right_iff,Classical.not_imp,mem_Icc,and_imp]
      intro x hx
      apply lG εpos hx.le jI
  · have: ∀ᵐ (a:ℝ) ∂volume.restrict (Ioi 0),a≠y:=by
      apply ae_iff.mpr
      simp
    filter_upwards [ae_restrict_mem (by measurability),this] with x hx hx2
    simp only [mem_Ioi] at hx
    apply ContinuousAt.div_const
    apply ContinuousAt.mul (by fun_prop)
    have:(fun x_1↦if 0<x_1/x ∧ x_1/x≤1 then 1 else 0)=
        (Ioc 0 x).indicator (fun _↦(1:ℝ)) :=by
      ext t
      unfold indicator
      simp [div_pos_iff_of_pos_right,div_le_one₀,hx]
    rw [this]
    apply ContinuousOn.continuousAt_indicator (by fun_prop)
    simp [frontier_Ioc hx,ypos.ne',hx2.symm]
lemma yJ {Ψ:ℝ→ℝ} {ε:ℝ} (Ql:ContDiff ℝ 1 Ψ)
    (EZ:Ψ.support⊆Icc (1/2) 2) (hε:ε∈Ioo 0 1)
    (oF: ∀ x>0,0≤Ψ x) (cD: ∫ x in Ioi 0,Ψ x/x=1)
    {s:ℂ} (hs:0<s.re) :MellinConvergent (fun x↦(dD Ψ ε x:ℂ)) s:=by
  apply mellinConvergent_of_isBigO_rpow_exp zero_lt_one _ _ _ hs
  · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
    apply continuousOn_of_forall_continuousAt
    exact fun x hx↦kG Ql oF EZ hε.1 hx |>.ofReal
  · rw [Asymptotics.isBigO_iff]
    use 1
    obtain ⟨c,cpos,ceq,hc⟩:=jc EZ
    filter_upwards [eventually_ge_atTop (1+c* ε)] with x hx
    rw [hc _ _ hε hx]
    simp only [ofReal_zero,norm_zero,neg_mul,one_mul,norm_eq_abs,abs_exp]
    bound
  · rw [Asymptotics.isBigO_iff]
    use 1
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp only [norm_real,norm_eq_abs,neg_zero,rpow_zero,one_mem,CStarRing.norm_of_mem_unitary,
      mul_one]
    rw [_root_.abs_of_nonneg <| tj oF hx hε.1]
    exact wY oF cD hε.1 hx
lemma jP {Ψ:ℝ→ℝ} {ε:ℝ} (Ql:ContDiff ℝ 1 Ψ)
    (EZ:Ψ.support⊆Icc (1/2) 2) (hε:ε∈Ioo 0 1)
    (oF: ∀ x>0,0≤Ψ x) (cD: ∫ x in Ioi 0,Ψ x/x=1)
    {s:ℂ} (hs:0<s.re) :
    DifferentiableAt ℂ ((mellin) (fun x↦(dD Ψ ε x:ℂ))) s:=by
  apply mellin_differentiableAt_of_isBigO_rpow_exp zero_lt_one _ _ _ hs
  · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
    apply continuousOn_of_forall_continuousAt
    exact fun x hx↦kG Ql oF EZ hε.1 hx |>.ofReal
  · rw [Asymptotics.isBigO_iff]
    use 1
    obtain ⟨c,cpos,ceq,hc⟩:=jc EZ
    filter_upwards [eventually_ge_atTop (1+c* ε)] with x hx
    rw [hc _ _ hε hx]
    simp only [ofReal_zero,norm_zero,neg_mul,one_mul,norm_eq_abs,abs_exp]
    bound
  · rw [Asymptotics.isBigO_iff]
    use 1
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp only [norm_real,norm_eq_abs,neg_zero,rpow_zero,one_mem,CStarRing.norm_of_mem_unitary,
      mul_one]
    rw [_root_.abs_of_nonneg <| tj oF hx hε.1]
    exact wY oF cD hε.1 hx
end

-- Zeta23.dO.Mathlib.Algebra.Notation.Support
section
namespace Function
variable {α:Type*} [Zero α]
theorem Tz:support (id:α→α)={0}ᶜ:=by
  ext; simp
theorem QO {α:Type*} [Zero α]:support (fun x:α↦x)={0}ᶜ:=
  Tz
end Function
end

-- Zeta23.dO.zE
section
open MeasureTheory Set Real
open scoped ContDiff
lemma tq {a b c d:ℝ} (h1:a<b) (h3:c<d) :
    ∃ Ψ:ℝ→ℝ,(ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1≤Ψ ∧ Ψ≤Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ=Set.Ioo a d) :=by
  have:=exists_contMDiff_zero_iff_one_iff_of_isClosed (n:= ⊤)
    (modelWithCornersSelf ℝ ℝ) (s:=Set.Iic a ∪ Set.Ici d) (t:=Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left,Set.disjoint_iff,Set.subset_def,
        Set.mem_inter_iff,Set.mem_Iic,Set.mem_Icc,Set.mem_empty_iff_false,
        and_imp,imp_false,not_le,Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ,Vk,JG,Ww,acq⟩:=this
  simp only [Set.mem_union,Set.mem_Iic,Set.mem_Ici,Set.mem_Icc] at*
  use Ψ
  simp only [range_subset_iff,mem_Icc] at JG
  refine ⟨ContMDiff.contDiff Vk,?_,?_,?_,?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K:=Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff,ne_eq,mem_Icc, ← Ww,not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [acq x |>.mp,Pi.one_apply]
      simpa using hx
    · exact fun x _↦(JG x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _↦(JG x).2
    · intro hx
      rw [← Ww x |>.mp]
      simpa [-not_and,mem_Ioo,not_and_or,not_lt] using hx
  · ext x
    simp only [Function.mem_support,ne_eq,mem_Ioo, ← Ww,not_or,not_le]
lemma zE:
    ∃ (ν:ℝ→ℝ),(ContDiff ℝ ∞ ν) ∧ (∀ x,0≤ν x) ∧
    ν.support⊆Icc (1/2) 2 ∧ ∫ x in Ici 0,ν x/x=1:=by
  suffices h: ∃ (ν:ℝ→ℝ),(ContDiff ℝ ∞ ν) ∧ (∀ x,0≤ν x) ∧
      ν.support⊆Set.Icc (1/2) 2 ∧ 0< ∫ x in Set.Ici 0,ν x/x by
    obtain ⟨ν,hν,Vm,XD,Qm⟩:=h
    let c:=(∫ x in Ici 0,ν x/x)
    use fun y↦ν y/c
    refine ⟨hν.div_const c,fun y↦div_nonneg (Vm y) (le_of_lt Qm),?_,?_⟩
    · rw [Function.support_div,Function.support_const (ne_of_lt Qm).symm,inter_univ]
      convert XD
    · simp only [div_right_comm _ c _,integral_div c,div_self <| ne_of_gt Qm,c]
  have:=tq (a:=1/2) (b:=1) (c:=3/2) (d:=2)
    (by linarith) (by linarith)
  obtain ⟨ν,HW,_,hν0,Zu,vQ⟩:=this
  use ν,HW
  unfold indicator at hν0 Zu
  simp only [mem_Icc,Pi.one_apply,Pi.le_def,mem_Ioo] at hν0 Zu
  simp only [vQ,subset_def,mem_Ioo,mem_Icc,and_imp]
  split_ands
  · exact fun x↦le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy'↦⟨by linarith,by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div,measurableSet_Ici,Measure.restrict_apply',
        vQ,Function.QO]
      have:(Ioo (1/2:ℝ) 2 ∩ {0}ᶜ ∩ Ici 0)=Ioo (1/2) 2:=by
        ext x
        simp only [one_div,mem_inter_iff,mem_Ioo,mem_compl_iff,mem_singleton_iff,mem_Ici]
        bound
      simp only [this,volume_Ioo,ENNReal.ofReal_pos,sub_pos,gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def,Pi.zero_apply]
      intro y
      by_cases h:y∈Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [vQ,mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support,ne_eq,not_not] at h
        simp [h]
    · have:(fun x↦ν x/x).support⊆Icc (1/2) 2:=by
        rw [Function.support_div,vQ]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply HW.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc,ne_eq,and_imp,id_eq]
      intros; linarith
end

-- Zeta23.dO.abf
section
open Set Function Filter Complex Real
open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev
namespace Chebyshev
end Chebyshev
open ComplexConjugate
open MeasureTheory
lemma jL {dL:ℝ→ℝ}
    (lO:ContDiff ℝ 1 dL)
    (Dt: ∀ x>0,0≤dL x)
    (jI:support dL⊆Icc (1/2) 2)
    (cD: ∫ (x:ℝ) in Ioi 0,dL x/x=1)
    {ε:ℝ} (εpos:0<ε) (EY:ε<1) {σ:ℝ} (Kj:1<σ) (Rz:σ≤2) :
    MeasureTheory.Integrable
      (fun (y:ℝ)↦(mellin) (fun x↦(dD dL ε x:ℂ)) (σ+y* I)) :=by
  obtain ⟨c,cpos,hc⟩:=JE lO jI
  apply Integrable.mono' (g:=(fun t↦c/ε*1/(1+t^2)))
  · apply Integrable.const_mul integrable_inv_one_add_sq
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro x
    have:=jP lO jI ⟨εpos,EY⟩
      Dt cD (s:=σ+x* I) (by simp only [add_re,ofReal_re,mul_re,I_re,
        mul_zero,ofReal_im,I_im,mul_one,sub_self,add_zero]; linarith) |>.continuousAt
    fun_prop
  · filter_upwards [] with t
    calc
      _≤ c/ε*1/(σ^2+t^2) :=by
        convert hc (σ/2) (by linarith) (σ+t* I) (by simp only [add_re,ofReal_re,mul_re,
          I_re,mul_zero,ofReal_im,I_im,mul_one,sub_self,add_zero,half_le_self_iff]; linarith)
          (by simp only [add_re,ofReal_re,mul_re,I_re,mul_zero,ofReal_im,I_im,mul_one,
            sub_self,add_zero]; linarith) ε εpos  EY using 1
        simp only [mul_one,Complex.sq_norm,normSq_apply,add_re,ofReal_re,mul_re,I_re,
          mul_zero,ofReal_im,I_im,sub_self,add_zero,add_im,mul_im,zero_add,mul_inv_rev]
        ring_nf
      _≤_:=by
        gcongr; nlinarith
open Filter Topology
end

-- aF.gP
section
open Complex Real Set Filter Topology
open aF.lN
open scoped ArithmeticFunction.Moebius
noncomputable section
namespace aF.gP
lemma Oi {a b θ θ':ℝ} (ha:0<a) (hb:0<b) (h0:0≤θ) (hθ:θ≤θ') :
    a^(1-θ)*b^θ≤a+a^(1-θ')*b^θ':=by
  have hp:0≤a^(1-θ')*b^θ':=by positivity
  rcases le_total b a with hba | hab
  · have:a^(1-θ)*b^θ≤a^(1-θ)*a^θ:=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb.le hba h0) (by positivity)
    rw [← Real.rpow_add ha,show 1-θ+θ=(1:ℝ) by ring,Real.rpow_one] at this
    linarith
  · have e1:a^(1-θ)=a^(1-θ')*a^(θ'-θ) :=by
      rw [← Real.rpow_add ha]; ring_nf
    have e2:b^θ'=b^(θ'-θ)*b^θ:=by
      rw [← Real.rpow_add hb]; ring_nf
    have h3:a^(θ'-θ)≤b^(θ'-θ) :=Real.rpow_le_rpow ha.le hab (by linarith)
    have:a^(1-θ)*b^θ≤a^(1-θ')*b^θ':=by
      rw [e1,e2]
      have:=mul_le_mul_of_nonneg_left h3 (show 0≤a^(1-θ') by positivity)
      have:=mul_le_mul_of_nonneg_right this (show 0≤b^θ by positivity)
      linarith [show a^(1-θ')*a^(θ'-θ)*b^θ=a^(1-θ')*a^(θ'-θ)*b^θ from rfl]
    linarith
lemma Qo (hRH:RiemannHypothesis) {δ:ℝ} (hδ0:0<δ) (hδ:δ≤1/4)
    {K:ℝ} (hK:1≤K)
    (PY: ∀ s:ℂ,1/2≤ s.re→4≤ |s.im| → ‖riemannZeta s‖ ≤K* |s.im|)
    {t:ℝ} (ht:6≤t) {r:ℝ} (hr0:0≤r) (hr:r≤3/2 -2*δ) :
    ‖riemannZeta (((2 -r:ℝ) :ℂ)+t* I)‖⁻¹≤
      3*Real.exp (4*Real.log (3*(Z (5/4)+1))+
        (4*Real.log (3*(Z (5/4)+1)))^(1-theta δ)*
        (6*Real.log (6*K*t)/δ)^(theta δ)) :=by
  set c:ℂ:=2+t* I with hc
  set B:ℂ→ℂ:=fun z=>riemannZeta (c+z) with hB
  set R:ℝ:=3/2 -δ/4 with hR
  have hre: ∀ z:ℂ,(c+z).re=2+z.re:=fun z=>by simp [hc]
  have him: ∀ z:ℂ,(c+z).im=t+z.im:=fun z=>by simp [hc]
  have hzre: ∀ z:ℂ, -‖z‖ ≤z.re:=fun z=>by
    linarith [neg_abs_le z.re,Complex.abs_re_le_norm z]
  have hzim: ∀ z:ℂ, |z.im| ≤ ‖z‖ :=Complex.abs_im_le_norm
  have hne1: ∀ z:ℂ, ‖z‖ ≤3/2→c+z≠1:=by
    intro z hz h
    have h':=congrArg Complex.im h
    rw [him] at h'
    simp only [Complex.one_im] at h'
    have:=(abs_le.mp ((hzim z).trans hz)).1
    linarith
  have Wq:AnalyticOnNhd ℂ B (Metric.closedBall 0 R) :=by
    intro z hz
    have hzR: ‖z‖ ≤R:=mem_closedBall_zero_iff.mp hz
    have hU:{w:ℂ | c+w≠1}∈𝓝 z:=
      (isOpen_ne_fun (continuous_const.add continuous_id) continuous_const).mem_nhds
        (hne1 z (by linarith))
    refine DifferentiableOn.analyticAt (s:={w:ℂ | c+w≠1}) (fun w hw=>?_) hU
    exact ((differentiableAt_riemannZeta hw).comp w
      ((differentiableAt_const c).add differentiableAt_id)).differentiableWithinAt
  have Jq: ∀ z∈Metric.closedBall (0:ℂ) R,B z≠0:=by
    intro z hz
    have hzR: ‖z‖ ≤R:=mem_closedBall_zero_iff.mp hz
    refine gO hRH ?_ (hne1 z (by linarith))
    rw [hre]; linarith [hzre z]
  obtain ⟨J,Wr,hJ0, -,Ez⟩:=jG (r:=1) one_pos (by linarith) Wq Jq
  have hJd:DifferentiableOn ℂ J (Metric.ball 0 R) :=Wr.differentiableOn
  have Lz:(2:ℝ)≤(c+0).re:=by rw [hre]; simp
  have LD:1/3≤ ‖B 0‖ :=EI Lz
  have WZ: ‖B 0‖ ≤2:=by
    have h1:=gX Lz
    have hpi:Real.pi^2<10:=by nlinarith [Real.pi_lt_d2,Real.pi_pos]
    have h2:=norm_le_norm_sub_add (B 0) 1
    rw [norm_one] at h2
    have: ‖B 0-1‖ ≤Real.pi^2/6-1:=h1
    linarith
  have PZ: ∀ z∈Metric.ball (0:ℂ) R, ∀ U:ℝ,0<U→ ‖B z‖ ≤U→
      (J z).re≤Real.log (3*U) :=by
    intro z hz U hU hBz
    rw [← Ez z hz]
    have Qa:0< ‖B z‖ :=norm_pos_iff.mpr (Jq z (Metric.ball_subset_closedBall hz))
    have Jt:0< ‖B 0‖ :=by linarith
    rw [← Real.log_div Qa.ne' Jt.ne']
    apply Real.log_le_log (div_pos Qa Jt)
    rw [div_le_iff₀ Jt]
    nlinarith [mul_le_mul_of_nonneg_left LD (by linarith:(0:ℝ)≤3*U)]
  set M₁:ℝ:=Real.log (3*(Z (5/4)+1)) with hM₁
  have Jv:0<M₁:=Real.log_pos (by linarith [qP (5/4)])
  have Jw: ∀ w∈Metric.ball (0:ℂ) (3/4),(J w).re≤M₁:=by
    intro w hw
    have hw': ‖w‖ <3/4:=mem_ball_zero_iff.mp hw
    refine PZ w (Metric.ball_subset_ball (by linarith) hw) (Z (5/4)+1)
      (by linarith [qP (5/4)]) ?_
    exact (rE (σ₀:=5/4) (s:=c+w) (by norm_num)
      (by rw [hre]; linarith [hzre w])).trans (le_add_of_nonneg_right zero_le_one)
  have hinner: ∀ z:ℂ, ‖z‖ ≤1/2→ ‖J z‖ ≤4*M₁:=by
    intro z hz
    have:=CY (J:=J) (R:=3/4) (r:=1/2) Jv
      (hJd.mono (Metric.ball_subset_ball (by linarith))) Jw hJ0 (by norm_num) (by norm_num) hz
    have e:2*M₁*(1/2)/(3/4-1/2)=4*M₁:=by ring
    linarith
  set M₃:ℝ:=Real.log (6*K*t) with hM₃
  have wT:0<M₃:=Real.log_pos (by nlinarith)
  have Jx: ∀ w∈Metric.ball (0:ℂ) (3/2 -δ/2),(J w).re≤M₃:=by
    intro w hw
    have hw': ‖w‖ <3/2 -δ/2:=mem_ball_zero_iff.mp hw
    have h6:6*K*t=3*(2*K*t) :=by ring
    rw [hM₃,h6]
    refine PZ w (Metric.ball_subset_ball (by linarith) hw) _ (by positivity) ?_
    have hi:=abs_le.mp ((hzim w).trans hw'.le)
    have OT:4≤ |(c+w).im| :=by rw [him,abs_of_pos (by linarith)]; linarith
    refine (PY (c+w) (by rw [hre]; linarith [hzre w]) OT).trans ?_
    rw [him,abs_of_pos (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left (show w.im≤t by linarith) (by linarith:(0:ℝ)≤K)]
  have Qb: ∀ z:ℂ, ‖z‖ ≤3/2 -δ→ ‖J z‖ ≤6*M₃/δ:=by
    intro z hz
    have:=CY (J:=J) wT (hJd.mono (Metric.ball_subset_ball (by linarith))) Jx
      hJ0 (by linarith) (by linarith) hz
    refine this.trans ?_
    rw [div_le_div_iff₀ (by linarith) hδ0]
    nlinarith [mul_pos wT (mul_pos hδ0 hδ0)]
  set z₂:ℂ:= -((r:ℝ) :ℂ) with hz₂
  have hr2: ‖z₂‖ =r:=by
    rw [hz₂,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0]
  have Tk:0≤theta δ:=theta_nonneg hδ
  have Mj:theta δ<1:=wS hδ0 hδ
  have hJz: ‖J z₂‖ ≤4*M₁+(4*M₁)^(1-theta δ)*(6*M₃/δ)^(theta δ) :=by
    rcases le_or_gt r (1/2) with hr1 | hr1
    · have:=hinner z₂ (by rw [hr2]; exact hr1)
      have:0≤(4*M₁)^(1-theta δ)*(6*M₃/δ)^(theta δ) :=by positivity
      linarith
    have h3c:=Dr (J:=J) (R:=R) (r₁:=1/2) (r₂:=r)
      (r₃:=3/2 -δ) (a:=4*M₁) (b:=6*M₃/δ) (by norm_num) hr1.le (by linarith)
      (by linarith) (by linarith) hJd (fun z hz=>hinner z hz.le) (fun z hz=>Qb z hz.le) hr2
    refine h3c.trans (Oi (by positivity) (by positivity) ?_ ?_)
    · apply div_nonneg
      · linarith [Real.log_le_log (by norm_num:(0:ℝ)<1/2) hr1.le]
      · linarith [Real.log_le_log (by norm_num:(0:ℝ)<1/2)
          (show (1:ℝ)/2≤3/2 -δ by linarith)]
    · unfold theta
      have hden:0<Real.log (3/2 -δ)-Real.log (1/2) :=by
        linarith [Real.log_lt_log (by norm_num:(0:ℝ)<1/2)
          (show (1:ℝ)/2<3/2 -δ by linarith)]
      apply div_le_div_of_nonneg_right _ hden.le
      linarith [Real.log_le_log (by linarith:(0:ℝ)<r) hr]
  have hcz:c+z₂=((2 -r:ℝ) :ℂ)+t* I:=by
    rw [hc,hz₂]; push_cast; ring
  have Nc:z₂∈Metric.ball (0:ℂ) R:=mem_ball_zero_iff.mpr (by rw [hr2]; linarith)
  have SZ:0< ‖B z₂‖ :=norm_pos_iff.mpr (Jq z₂ (Metric.ball_subset_closedBall Nc))
  have aaI: -‖J z₂‖ -Real.log 3≤Real.log ‖B z₂‖ :=by
    have h1:=Ez z₂ Nc
    have h2: -‖J z₂‖ ≤(J z₂).re:=by
      linarith [Complex.abs_re_le_norm (J z₂),neg_abs_le (J z₂).re]
    have h3:Real.log (1/3)≤Real.log ‖B 0‖ :=Real.log_le_log (by norm_num) LD
    have h4:Real.log (1/3)= -Real.log 3:=by rw [one_div,Real.log_inv]
    linarith
  have Tj: ‖B z₂‖⁻¹≤3*Real.exp ‖J z₂‖ :=by
    calc ‖B z₂‖⁻¹=Real.exp (-Real.log ‖B z₂‖) :=by rw [Real.exp_neg,Real.exp_log SZ]
      _≤Real.exp (‖J z₂‖ +Real.log 3) :=Real.exp_le_exp.mpr (by linarith)
      _=3*Real.exp ‖J z₂‖ :=by rw [Real.exp_add,Real.exp_log (by norm_num)]; ring
  have Tf:B z₂=riemannZeta (((2 -r:ℝ) :ℂ)+t* I) :=by
    simp only [hB,hcz]
  rw [← Tf]
  exact Tj.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hJz) (by norm_num))
lemma Nm (hRH:RiemannHypothesis) {δ:ℝ} (hδ0:0<δ) (hδ:δ≤1/4)
    {ε:ℝ} (hε:0<ε) : ∃ C T:ℝ,0≤C ∧ 6≤T ∧ ∀ σ t:ℝ,T≤ |t| →
      1/2+2*δ≤σ→σ≤2→ ‖riemannZeta (σ+t* I)‖⁻¹≤C* |t| ^ε:=by
  obtain ⟨K,hK,PY⟩:=wR
  have Tk:0≤theta δ:=theta_nonneg hδ
  have Mj:theta δ<1:=wS hδ0 hδ
  set θ:=theta δ with hθ
  set M₁:ℝ:=Real.log (3*(Z (5/4)+1)) with hM₁
  have Vd:0≤M₁:=(Real.log_pos (by linarith [qP (5/4)])).le
  set D:ℝ:=(4*M₁)^(1-θ)*(6/δ)^θ*2^θ with hD
  have hev: ∀ᶠ t:ℝ in atTop,D/ε≤Real.log t^(1-θ) :=
    ((tendsto_rpow_atTop (by linarith)).comp Real.tendsto_log_atTop).eventually_ge_atTop _
  obtain ⟨T₁,hT₁⟩:=eventually_atTop.mp hev
  set T:ℝ:=max (max T₁ 6) (6*K) with hT
  have hpos: ∀ σ t:ℝ,T≤t→1/2+2*δ≤σ→σ≤2→
      ‖riemannZeta (σ+t* I)‖⁻¹≤3*Real.exp (4*M₁)*t^ε:=by
    intro σ t ht oC hσ1
    have Qc:T₁≤t:=le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
    have ht6:6≤t:=le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
    have htK:6*K≤t:=le_trans (le_max_right _ _) ht
    have hmain:=Qo hRH hδ0 hδ hK PY ht6 (r:=2 -σ) (by linarith) (by linarith)
    rw [show ((2 -(2 -σ) :ℝ))=σ by ring] at hmain
    refine hmain.trans ?_
    have hlt:0<Real.log t:=Real.log_pos (by linarith)
    have hL:Real.log (6*K*t)≤2*Real.log t:=by
      rw [show 2*Real.log t=Real.log (t*t) by
        rw [Real.log_mul (by linarith) (by linarith)]; ring]
      exact Real.log_le_log (by positivity) (by nlinarith)
    have hstep:(4*M₁)^(1-θ)*(6*Real.log (6*K*t)/δ)^θ≤ε*Real.log t:=by
      calc (4*M₁)^(1-θ)*(6*Real.log (6*K*t)/δ)^θ
          ≤(4*M₁)^(1-θ)*((6/δ)*(2*Real.log t))^θ:=by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine Real.rpow_le_rpow (by
              have:0≤Real.log (6*K*t) :=Real.log_nonneg (by nlinarith)
              positivity) ?_ Tk
            rw [mul_div_right_comm]
            exact mul_le_mul_of_nonneg_left hL (by positivity)
        _=D*Real.log t^θ:=by
            rw [Real.mul_rpow (x:=6/δ) (by positivity) (by positivity),
              Real.mul_rpow (x:=(2:ℝ)) (by norm_num) hlt.le,hD]
            ring
        _≤(ε*Real.log t^(1-θ))*Real.log t^θ:=by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have:=hT₁ t Qc
            rwa [div_le_iff₀ hε,mul_comm] at this
        _=ε*Real.log t:=by
            rw [mul_assoc, ← Real.rpow_add hlt]; simp
    calc 3*Real.exp (4*M₁+(4*M₁)^(1-θ)*(6*Real.log (6*K*t)/δ)^θ)
        =3*Real.exp (4*M₁)*
            Real.exp ((4*M₁)^(1-θ)*(6*Real.log (6*K*t)/δ)^θ) :=by
          rw [Real.exp_add]; ring
      _≤3*Real.exp (4*M₁)*Real.exp (ε*Real.log t) :=by gcongr
      _=3*Real.exp (4*M₁)*t^ε:=by
          rw [Real.rpow_def_of_pos (by linarith),mul_comm ε]
  refine ⟨3*Real.exp (4*M₁),T,by positivity,
    le_trans (le_max_right _ _) (le_max_left _ _),fun σ t ht oC hσ1=>?_⟩
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at ht ⊢; exact hpos σ t ht oC hσ1
  · rw [abs_of_neg h0] at ht ⊢
    have hconj:(starRingEnd ℂ) ((σ:ℂ)+((-t:ℝ) :ℂ)* I)=(σ:ℂ)+t* I:=by
      apply Complex.ext <;> simp
    rw [← hconj,riemannZeta_conj,Complex.norm_conj]
    exact hpos σ (-t) ht oC hσ1
def G (s:ℂ) :ℂ:=(s-1)/riemannZeta₁ s
lemma G_eq {s:ℂ} (hs:s≠1) :G s=(riemannZeta s)⁻¹:=by
  have h:=Lindelof.F_eq hs
  unfold G
  rw [show riemannZeta₁ s=Lindelof.F s from rfl,h, ← div_div,
    div_self (sub_ne_zero.mpr hs),one_div]
lemma LG (hRH:RiemannHypothesis) {s:ℂ} (hs:1/2<s.re) :
    riemannZeta₁ s≠0:=by
  rcases eq_or_ne s 1 with rfl | h1
  · rw [riemannZeta₁_one]; exact one_ne_zero
  · rw [show riemannZeta₁ s=Lindelof.F s from rfl,Lindelof.F_eq h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (gO hRH hs h1)
lemma rH (hRH:RiemannHypothesis) {s:ℂ} (hs:1/2<s.re) :
    DifferentiableAt ℂ G s:=
  (differentiableAt_id.sub_const 1).div differentiable_riemannZeta₁.differentiableAt
    (LG hRH hs)
lemma XE (hRH:RiemannHypothesis) {δ:ℝ} (hδ0:0<δ) (hδ:δ≤1/4)
    {η:ℝ} (hη:0<η) : ∃ C:ℝ,0≤C ∧ ∀ σ t:ℝ,1/2+2*δ≤σ→σ≤2→
      ‖G (σ+t* I)‖ ≤C*(1+ |t|)^η:=by
  obtain ⟨C₁,T,hC₁,hT6,hb⟩:=Nm hRH hδ0 hδ hη
  set S:Set ℂ:=(Icc (1/2+2*δ) 2) ×ℂ (Icc (-T) T) with hS
  have hSc:IsCompact S:=isCompact_Icc.reProdIm isCompact_Icc
  have hcont:ContinuousOn G S:=fun s hs=>
    (rH hRH (by have:=hs.1.1; linarith)).continuousAt.continuousWithinAt
  obtain ⟨M₂,hM₂⟩:=hSc.exists_bound_of_continuousOn hcont
  refine ⟨max C₁ M₂,le_trans hC₁ (le_max_left _ _),fun σ t oC hσ1=>?_⟩
  have hu:1≤(1+ |t|)^η:=Real.one_le_rpow (by linarith [abs_nonneg t]) hη.le
  have hC0:0≤ max C₁ M₂:=le_trans hC₁ (le_max_left _ _)
  rcases le_or_gt |t| T with htT | htT
  · have hmem:(σ:ℂ)+t* I∈S:=by
      refine ⟨?_,?_⟩ <;> rw [Set.mem_preimage]
      · have:((σ:ℂ)+t* I).re=σ:=by simp
        rw [this]; exact ⟨oC,hσ1⟩
      · have:((σ:ℂ)+t* I).im=t:=by simp
        rw [this]; exact abs_le.mp htT
    calc ‖G (σ+t* I)‖ ≤M₂:=hM₂ _ hmem
      _≤ max C₁ M₂:=le_max_right _ _
      _≤ max C₁ M₂*(1+ |t|)^η:=le_mul_of_one_le_right hC0 hu
  · have hne:(σ:ℂ)+t* I≠1:=by
      intro h; have:=congrArg Complex.im h; simp at this; rw [this] at htT; simp at htT
      linarith
    rw [G_eq hne,norm_inv]
    refine (hb σ t htT.le oC hσ1).trans ?_
    exact mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow (abs_nonneg t) (by linarith) hη.le)
      (by positivity) hC0
open ArithmeticFunction in
lemma xd {s:ℂ} (hs:1<s.re) :
    (riemannZeta s)⁻¹= ∑' n:ℕ,(μ n:ℂ)/(n:ℂ)^s:=by
  have h1:=LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs] at h1
  rw [inv_eq_of_mul_eq_one_right h1]
  unfold LSeries
  refine tsum_congr fun n=>?_
  rw [LSeries.term_def]
  split_ifs with h
  · simp [h]
  · rfl
end aF.gP
end
end

-- aF.ZG
section
open Complex Real Set Filter Topology MeasureTheory
open scoped ArithmeticFunction.Moebius
noncomputable section
namespace aF.Nyman.Smooth
lemma DN {f g:ℂ→ℂ} {a b:ℝ} {R:ℂ} (ha0:a<0) (hb0:0<b)
    (hg: ∀ s:ℂ,a≤ s.re→s.re≤b→DifferentiableAt ℂ g s)
    (hfg: ∀ s:ℂ,s≠0→a≤ s.re→s.re≤b→f s=g s+R/s)
    (ha:Integrable (fun t:ℝ=>f (a+t* I)))
    (hb:Integrable (fun t:ℝ=>f (b+t* I)))
    (Zv: ∀ η>0, ∃ T₀:ℝ, ∀ T:ℝ,T₀≤ |T| → ∀ σ∈Icc a b, ‖f (σ+T* I)‖ ≤η) :
    (∫ t:ℝ,f (b+t* I))- ∫ t:ℝ,f (a+t* I)=2*π*R:=by
  have hab:a≤b:=by linarith
  have aaO: ∀ T:ℝ,0<T→
      I*((∫ t in (-T)..T,f (b+t* I))- ∫ t in (-T)..T,f (a+t* I))=
        2*π* I*R-dK f a b (-T)+dK f a b T:=by
    intro T hT
    have hz1:((a:ℂ)-T* I).re=a:=by simp
    have hz2:((a:ℂ)-T* I).im= -T:=by simp
    have hw1:((b:ℂ)+T* I).re=b:=by simp
    have hw2:((b:ℂ)+T* I).im=T:=by simp
    have TB: ∀ s∈Rectangle ((a:ℂ)-T* I) ((b:ℂ)+T* I),a≤ s.re ∧ s.re≤b:=by
      intro s hs
      have h1:s.re∈Set.uIcc ((a:ℂ)-T* I).re ((b:ℂ)+T* I).re:=hs.1
      rw [hz1,hw1,Set.uIcc_of_le hab] at h1
      exact ⟨h1.1,h1.2⟩
    have h0:=jW (f:=f) (g:=g) (p:=0) (A:=R)
      (z:=(a:ℂ)-T* I) (w:=(b:ℂ)+T* I) (by rw [hz1,hw1]; exact hab)
      (by rw [hz2,hw2]; linarith)
      (by
        rw [eo,hz1,hw1,hz2,hw2,Set.uIoo_of_le hab,
          Set.uIoo_of_le (by linarith)]
        simp only [mem_reProdIm,Complex.zero_re,Complex.zero_im,mem_Ioo]
        exact ⟨⟨ha0,hb0⟩,⟨by linarith,hT⟩⟩)
      (fun s hs=>(hg s (TB s hs).1 (TB s hs).2).differentiableWithinAt)
      (by
        intro s hs
        have hs0:s≠0:=hs.2
        have hm:=TB s hs.1
        simp only [Pi.sub_apply,sub_zero]
        rw [hfg s hs0 hm.1 hm.2]; ring)
    unfold aW aV at h0
    rw [hz1,hz2,hw1,hw2] at h0
    simp only [eW,smul_eq_mul] at h0
    have h2:(2*↑π* I)≠0:=by
      simp [Real.pi_ne_zero,Complex.I_ne_zero]
    field_simp at h0
    simp only [show ∀ y:ℝ,I*(y:ℂ)=y* I from fun y=>mul_comm _ _] at h0
    linear_combination h0
  have hlim:Tendsto (fun T:ℝ=>I*((∫ t in (-T)..T,f (b+t* I))-
      ∫ t in (-T)..T,f (a+t* I))) atTop
      (𝓝 (I*((∫ t:ℝ,f (b+t* I))- ∫ t:ℝ,f (a+t* I)))) :=
    ((intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id).sub
      (intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id)).const_mul I
  have hsmall: ∀ η>0, ‖I*((∫ t:ℝ,f (b+t* I))- ∫ t:ℝ,f (a+t* I))-
      2*π* I*R‖ ≤2*(η*(b-a)) :=by
    intro η hη
    obtain ⟨T₀,hT₀⟩:=Zv η hη
    refine le_of_tendsto (hlim.sub_const (2*π* I*R)).norm ?_
    filter_upwards [eventually_ge_atTop (max T₀ 1)] with T hT
    have hT0:0<T:=lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hT)
    rw [aaO T hT0]
    have hH: ∀ T':ℝ,T₀≤ |T'| → ‖dK f a b T'‖ ≤η*(b-a) :=by
      intro T' hT'
      unfold dK
      have hpt: ∀ x∈Set.uIoc a b, ‖f (x+T'* I)‖ ≤η:=by
        intro x hx
        rw [Set.uIoc_of_le hab] at hx
        exact hT₀ T' hT' x ⟨hx.1.le,hx.2⟩
      refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans ?_
      rw [abs_of_nonneg (by linarith)]
    have aaP:T₀≤ |T| :=le_trans (le_max_left _ _) (hT.trans (le_abs_self T))
    have Zw:T₀≤ |-T| :=by rwa [abs_neg]
    calc ‖2*π* I*R-dK f a b (-T)+dK f a b T-2*π* I*R‖
        = ‖dK f a b T-dK f a b (-T)‖ :=by ring_nf
      _≤ ‖dK f a b T‖ + ‖dK f a b (-T)‖ :=norm_sub_le _ _
      _≤η*(b-a)+η*(b-a) :=add_le_add (hH T aaP) (hH (-T) Zw)
      _=2*(η*(b-a)) :=by ring
  set x:= ‖I*((∫ t:ℝ,f (b+t* I))- ∫ t:ℝ,f (a+t* I))-2*π* I*R‖ with hx
  have hx0:x=0:=by
    refine le_antisymm ?_ (norm_nonneg _)
    by_contra hpos
    push Not at hpos
    have:=hsmall (x/(4*(b-a+1))) (by positivity)
    have e:2*(x/(4*(b-a+1))*(b-a))≤x/2:=by
      rw [div_mul_eq_mul_div,mul_div_assoc',div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  rw [hx,norm_eq_zero,sub_eq_zero] at hx0
  have hI:I≠0:=Complex.I_ne_zero
  have:I*((∫ t:ℝ,f (b+t* I))- ∫ t:ℝ,f (a+t* I))=I*(2*π*R) :=by
    rw [hx0]; ring
  exact mul_left_cancel₀ hI this
lemma Fd {x r:ℝ} (hx:x∈Icc (1/2:ℝ) 2) (hr0: -2≤r) (hr1:r≤2) :
    x^r≤4:=by
  have hx0:0<x:=by linarith [hx.1]
  rcases le_total 1 x with h1 | h1
  · calc x^r≤x^(2:ℝ) :=Real.rpow_le_rpow_of_exponent_le h1 hr1
      _≤2^(2:ℝ) :=Real.rpow_le_rpow hx0.le hx.2 (by norm_num)
      _=4:=by norm_num
  · calc x^r≤x^(-2:ℝ) :=Real.rpow_le_rpow_of_exponent_ge hx0 h1 hr0
      _=(x^(2:ℝ))⁻¹:=Real.rpow_neg hx0.le _
      _≤((1/2:ℝ)^(2:ℝ))⁻¹:=by
          gcongr
          exact hx.1
      _=4:=by norm_num
variable {ν:ℝ→ℝ}
lemma BG (bC:ν.support⊆Icc (1/2) 2) :
    (fun x:ℝ=>(ν x:ℂ)).support⊆Icc (1/2) 2:=by
  intro x hx; apply bC; intro h; apply hx; simp [h]
lemma tA (hν:Continuous ν) (bC:ν.support⊆Icc (1/2) 2)
    (u:ℂ) :DifferentiableAt ℂ ((mellin) (fun x↦(ν x:ℂ))) u:=by
  have hsupp:=BG bC
  refine mellin_differentiableAt_of_isBigO_rpow (a:=u.re+1) (b:=u.re-1)
    ((continuous_ofReal.comp hν).locallyIntegrable.locallyIntegrableOn _)
    ((Filter.nQ _ hsupp).trans (Asymptotics.isBigO_zero _ _))
    (by linarith)
    ((Filter.mO _ (by norm_num) hsupp).trans
      (Asymptotics.isBigO_zero _ _))
    (by linarith)
lemma pQ {h:ℝ→ℂ} {M:ℝ} (hM:0≤M)
    (hb: ∀ x∈Ioi (0:ℝ), ‖h x‖ ≤(Icc (1/2:ℝ) 2).indicator (fun _=>4*M) x) :
    ‖∫ x in Ioi (0:ℝ),h x‖ ≤6*M:=by
  have hint:Integrable ((Icc (1/2:ℝ) 2).indicator (fun _=>4*M)) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  refine (norm_integral_le_of_norm_le hint.integrableOn
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hb))).trans ?_
  refine (setIntegral_le_integral hint (Eventually.of_forall fun x=>
    indicator_nonneg (fun _ _=>by positivity) x)).trans ?_
  rw [integral_indicator_const _ measurableSet_Icc,Real.volume_real_Icc,smul_eq_mul]
  norm_num
  linarith
lemma JH (cP:ContDiff ℝ 1 ν) (bC:ν.support⊆Icc (1/2) 2) :
    ∃ C:ℝ,0≤C ∧ ∀ s:ℂ, -1≤ s.re→s.re≤2→
      ‖(mellin) (fun x↦(ν x:ℂ)) s‖ ≤C ∧ ‖s‖ * ‖(mellin) (fun x↦(ν x:ℂ)) s‖ ≤C:=by
  have hν:Continuous ν:=cP.continuous
  have hcs:HasCompactSupport ν:=HasCompactSupport.intro isCompact_Icc fun x hx=>by
    by_contra h; exact hx (bC h)
  obtain ⟨M₀,hM₀⟩:=hν.bounded_above_of_compact_support hcs
  have Vq:(deriv ν).support⊆Icc (1/2) 2:=Function.iF bC
  have acr:HasCompactSupport (deriv ν) :=HasCompactSupport.intro isCompact_Icc fun x hx=>by
    by_contra h; exact hx (Vq h)
  obtain ⟨M₁,hM₁⟩:=(cP.continuous_deriv le_rfl).bounded_above_of_compact_support acr
  have LH:0≤M₀:=(norm_nonneg _).trans (hM₀ 0)
  have Vd:0≤M₁:=(norm_nonneg _).trans (hM₁ 0)
  refine ⟨6*max M₀ M₁,by positivity,fun s hs0 hs1=>⟨?_,?_⟩⟩
  · rw [mellin]
    refine pQ (le_max_of_le_left LH) fun x hx=>?_
    by_cases hxI:x∈Icc (1/2:ℝ) 2
    · rw [indicator_of_mem hxI,norm_smul,Complex.norm_cpow_eq_rpow_re_of_pos hx]
      have h4:=Fd hxI (r:=(s-1).re) (by simp; linarith) (by simp; linarith)
      have hn: ‖((ν x:ℝ) :ℂ)‖ ≤ max M₀ M₁:=by
        rw [Complex.norm_real]; exact (hM₀ x).trans (le_max_left _ _)
      calc x^(s-1).re* ‖((ν x:ℝ) :ℂ)‖ ≤4*max M₀ M₁:=
            mul_le_mul h4 hn (norm_nonneg _) (by norm_num)
        _=_:=rfl
    · have:ν x=0:=by by_contra h; exact hxI (bC h)
      rw [indicator_of_notMem hxI,this]; simp
  · rcases eq_or_ne s 0 with rfl | hs
    · simp only [norm_zero,zero_mul]
      exact mul_nonneg (by norm_num) (le_max_of_le_left LH)
    have key:=zD cP bC hs
    have hm:(mellin) (fun x↦(ν x:ℂ)) s= ∫ x in Ioi (0:ℝ),(ν x)*(x:ℂ)^(s-1) :=by
      rw [mellin]; congr 1; ext x; rw [smul_eq_mul,mul_comm]
    rw [hm,key,norm_mul,norm_neg,norm_div,norm_one, ← mul_assoc,mul_one_div_cancel
      (norm_ne_zero_iff.mpr hs),one_mul]
    refine pQ (le_max_of_le_left LH) fun x hx=>?_
    by_cases hxI:x∈Icc (1/2:ℝ) 2
    · rw [indicator_of_mem hxI,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx]
      have h4:=Fd hxI (r:=s.re) (by linarith) hs1
      have hn: ‖((deriv ν x:ℝ) :ℂ)‖ ≤ max M₀ M₁:=by
        rw [Complex.norm_real]; exact (hM₁ x).trans (le_max_right _ _)
      calc ‖((deriv ν x:ℝ) :ℂ)‖ *x^s.re≤ max M₀ M₁*4:=
            mul_le_mul hn h4 (Real.rpow_nonneg hx.le _) (le_max_of_le_left LH)
        _=4*max M₀ M₁:=by ring
    · have:deriv ν x=0:=by by_contra h; exact hxI (Vq h)
      rw [indicator_of_notMem hxI,this]; simp
theorem Np {ν:ℝ→ℝ} (cP:ContDiff ℝ 1 ν) (nW: ∀ x>0,0≤ν x)
    (bC:ν.support⊆Icc (1/2) 2) (cD: ∫ x in Ioi (0:ℝ),ν x/x=1)
    {κ:ℝ} (hκ:0<κ) (JI:κ<1) {N:ℝ} (hN:0<N) {σ:ℝ} (hσ:1<σ) (hσ2:σ≤2)
    {a:ℕ→ℂ} (ha0:a 0=0) (ha: ∀ n, ‖a n‖ ≤1) :
    (∫ t:ℝ,(∑' n:ℕ,a n/(n:ℂ)^((σ:ℂ)+t* I))*
        (mellin) (fun x↦(dD ν κ x:ℂ)) (σ+t* I)*(N:ℂ)^((σ:ℂ)+t* I))=
      2*π* ∑' n:ℕ,a n*(dD ν κ (n/N) :ℂ) :=by
  set F:ℝ→ℂ:=fun t=>(mellin) (fun x↦(dD ν κ x:ℂ)) (σ+t* I) with adN
  have hF:Integrable F:=
    jL cP nW bC cD hκ JI hσ hσ2
  have hFc:Continuous F:=by
    refine continuous_iff_continuousAt.mpr fun t=>?_
    have hc:ContinuousAt (fun t:ℝ=>(σ:ℂ)+t* I) t:=by fun_prop
    exact ContinuousAt.comp (f:=fun t:ℝ=>(σ:ℂ)+t* I)
      (jP cP bC ⟨hκ,JI⟩ nW cD
        (by simp; linarith)).continuousAt hc
  set term:ℕ→ℝ→ℂ:=fun n t=>
    a n/(n:ℂ)^((σ:ℂ)+t* I)*F t*(N:ℂ)^((σ:ℂ)+t* I) with hterm
  have hnorm: ∀ n t, ‖term n t‖ ≤((n:ℝ)^σ)⁻¹*N^σ* ‖F t‖ :=by
    intro n t
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hterm,ha0]; positivity
    simp only [hterm,norm_mul,norm_div,norm_natCast_cpow_of_pos hn,
      Complex.norm_cpow_eq_rpow_re_of_pos hN]
    simp only [add_re,ofReal_re,mul_re,I_re,mul_zero,ofReal_im,I_im,mul_one,sub_self,
      add_zero]
    have h1:=ha n
    have:0<(n:ℝ)^σ:=by positivity
    rw [div_eq_mul_inv]
    calc ‖a n‖ *((n:ℝ)^σ)⁻¹* ‖F t‖ *N^σ≤1*((n:ℝ)^σ)⁻¹* ‖F t‖ *N^σ:=by
          gcongr
      _=_:=by ring
  have hmeas: ∀ n,AEStronglyMeasurable (term n) :=by
    intro n
    refine Measurable.aestronglyMeasurable ?_
    simp only [hterm]
    exact ((measurable_const.div (measurable_const.pow (by fun_prop))).mul
      hFc.measurable).mul (measurable_const.pow (by fun_prop))
  have hint: ∀ n,Integrable (term n) :=fun n=>
    (hF.norm.const_mul (((n:ℝ)^σ)⁻¹*N^σ)).mono' (hmeas n)
      (ae_of_all _ fun t=>hnorm n t)
  have hsum:Summable fun n=> ∫ t, ‖term n t‖ :=by
    refine Summable.of_nonneg_of_le (fun n=>integral_nonneg fun t=>norm_nonneg _)
      (fun n=>?_) ((Real.summable_nat_rpow_inv.mpr hσ).mul_right (N^σ* ∫ t, ‖F t‖))
    calc ∫ t, ‖term n t‖ ≤ ∫ t,((n:ℝ)^σ)⁻¹*N^σ* ‖F t‖ :=
          integral_mono (hint n).norm (hF.norm.const_mul _) (hnorm n)
      _=((n:ℝ)^σ)⁻¹*(N^σ* ∫ t, ‖F t‖) :=by rw [integral_const_mul]; ring
  have hper: ∀ n, ∫ t,term n t=2*π*(a n*(dD ν κ (n/N) :ℂ)) :=by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hterm,ha0]
    have hx:0<(n:ℝ)/N:=by positivity
    have hinv:=mellinInv_mellin_eq σ (fun x↦(dD ν κ x:ℂ)) hx
      (yJ cP bC ⟨hκ,JI⟩ nW cD (by simp; linarith)) hF
      ((kG cP nW bC hκ hx).ofReal)
    simp only [mellinInv,smul_eq_mul] at hinv
    have hpt: ∀ t:ℝ,term n t=a n*((((n:ℝ)/N:ℝ) :ℂ)^(-((σ:ℂ)+t* I))*F t) :=by
      intro t
      have hn0:(n:ℂ)^((σ:ℂ)+t* I)≠0:=
        cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn.ne'))
      rw [cpow_neg,ofReal_div,div_cpow_ofReal_nonneg (by positivity) hN.le]
      simp only [hterm,ofReal_natCast]
      field_simp
    rw [integral_congr_ae (ae_of_all _ hpt),integral_const_mul]
    have h2:(∫ t:ℝ,(((n:ℝ)/N:ℝ) :ℂ)^(-((σ:ℂ)+t* I))*F t)=
        2*π*(dD ν κ (n/N) :ℂ) :=by
      rw [← hinv,Complex.real_smul, ← mul_assoc]
      have h3:(2*(π:ℂ))*((1/(2*π) :ℝ) :ℂ)=1:=by
        push_cast; field_simp
      rw [h3,one_mul]
    rw [h2]; ring
  calc (∫ t:ℝ,(∑' n:ℕ,a n/(n:ℂ)^((σ:ℂ)+t* I))*F t*
          (N:ℂ)^((σ:ℂ)+t* I))= ∫ t, ∑' n,term n t:=by
        congr 1; ext t; rw [← tsum_mul_right, ← tsum_mul_right]
    _= ∑' n, ∫ t,term n t:=(integral_tsum_of_summable_integral_norm hint hsum).symm
    _=_:=by simp_rw [hper]; rw [tsum_mul_left]
def tw (w:ℂ) (n:ℕ) :ℂ:=(μ n:ℂ)*(n:ℂ)^(-w)
lemma XF (w:ℂ) :tw w 0=0:=by simp [tw]
lemma TD {w:ℂ} (hw:0≤w.re) (n:ℕ) : ‖tw w n‖ ≤1:=by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tw]
  rw [tw,norm_mul,norm_natCast_cpow_of_pos hn]
  have h1: ‖(μ n:ℂ)‖ ≤1:=by
    rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have h2:(n:ℝ)^(-w).re≤1:=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by simp; linarith)
  calc ‖(μ n:ℂ)‖ *(n:ℝ)^(-w).re≤1*1:=
        mul_le_mul h1 h2 (by positivity) zero_le_one
    _=1:=one_mul 1
lemma XG {w z:ℂ} (hwz:1<(w+z).re) :
    ∑' n:ℕ,tw w n/(n:ℂ)^z=(riemannZeta (w+z))⁻¹:=by
  rw [gP.xd hwz]
  refine tsum_congr fun n=>?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tw]
  have hn0:(n:ℂ)≠0:=by exact_mod_cast hn.ne'
  rw [tw,cpow_add _ _ hn0,cpow_neg]
  have h1:(n:ℂ)^w≠0:=cpow_ne_zero_iff.mpr (Or.inl hn0)
  have h2:(n:ℂ)^z≠0:=cpow_ne_zero_iff.mpr (Or.inl hn0)
  field_simp
lemma Nq (cD: ∫ x in Ioi (0:ℝ),ν x/x=1) :
    (mellin) (fun x↦(ν x:ℂ)) 0=1:=by
  rw [mellin]
  have: ∀ x∈Ioi (0:ℝ),(x:ℂ)^((0:ℂ)-1)•(ν x:ℂ)=((ν x/x:ℝ) :ℂ) :=by
    intro x _
    rw [zero_sub,cpow_neg_one,smul_eq_mul]; push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi this,integral_complex_ofReal,cD]
  simp
def H (ν:ℝ→ℝ) (κ N:ℝ) (w z:ℂ) :ℂ:=
  (mellin) (fun x↦(ν x:ℂ)) (κ*z)*(N:ℂ)^z*gP.G (w+z)
lemma Fe (hRH:RiemannHypothesis) (hν:Continuous ν)
    (bC:ν.support⊆Icc (1/2) 2) {κ N:ℝ} (hN:0<N) {w z:ℂ}
    (hz:1/2<(w+z).re) :DifferentiableAt ℂ (H ν κ N w) z:=by
  unfold H
  refine ((tA hν bC _).comp z
    ((differentiableAt_id).const_mul _) |>.mul ?_).mul ?_
  · exact (differentiableAt_id (x:=z)).const_cpow (Or.inl (by exact_mod_cast hN.ne'))
  · exact (gP.rH hRH hz).comp z ((differentiableAt_id).const_add w)
lemma H_zero (cD: ∫ x in Ioi (0:ℝ),ν x/x=1) (κ N:ℝ) {w:ℂ} (hw:w≠1) :
    H ν κ N w 0=(riemannZeta w)⁻¹:=by
  simp [H,Nq cD,gP.G_eq hw]
lemma Wz (cP:ContDiff ℝ 1 ν) (bC:ν.support⊆Icc (1/2) 2) {κ N:ℝ}
    (hκ:0<κ) {w z:ℂ} (hz:0<z.re) (hwz:1<(w+z).re) :
    H ν κ N w z/z=(riemannZeta (w+z))⁻¹*(mellin) (fun x↦(dD ν κ x:ℂ)) z*
      (N:ℂ)^z:=by
  have hne:w+z≠1:=by intro h; rw [h] at hwz; simp at hwz
  rw [wZ cP bC hκ hz,H,gP.G_eq hne]
  ring
abbrev wε (ε τ:ℝ) :ℂ:=((1/2+ε:ℝ) :ℂ)+τ* I
lemma yP {p:ℝ} (hp:0≤p) (u v:ℝ) :
    (1+ |u+v|)^p≤(1+ |u|)^p*(1+ |v|)^p:=by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  refine Real.rpow_le_rpow (by positivity) ?_ hp
  nlinarith [abs_add_le u v,abs_nonneg u,abs_nonneg v,mul_nonneg (abs_nonneg u) (abs_nonneg v)]
lemma QS (hRH:RiemannHypothesis) (cP:ContDiff ℝ 1 ν)
    (bC:ν.support⊆Icc (1/2) 2) {κ:ℝ} (hκ:0<κ) (JI:κ<1)
    {ε:ℝ} (hε:0<ε) (wW:ε≤1/4) :
    ∃ K:ℝ,0≤K ∧ ∀ N:ℝ,0<N→ ∀ τ:ℝ, ∀ z:ℂ, -(ε/2)≤z.re→z.re≤5/4→
      z≠0→ ‖H ν κ N (wε ε τ) z/z‖ ≤
        K*N^z.re*(1+ |τ|)^(1/8:ℝ)*((1+ |z.im|)^(1/8:ℝ)/ ‖z‖ ^2) :=by
  obtain ⟨C,hC0,hC⟩:=JH cP bC
  obtain ⟨CG,acs,hG⟩:=gP.XE hRH (δ:=ε/4) (by positivity) (by linarith)
    (η:=1/8) (by norm_num)
  refine ⟨C/κ*CG,by positivity,fun N hN τ z h1 h2 hz=>?_⟩
  have hzn:0< ‖z‖ :=norm_pos_iff.mpr hz
  have hre:((κ:ℂ)*z).re=κ*z.re:=by simp
  obtain ⟨-,hM⟩:=hC ((κ:ℂ)*z) (by rw [hre]; nlinarith) (by rw [hre]; nlinarith)
  have acu: ‖(κ:ℂ)*z‖ =κ* ‖z‖ :=by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hκ]
  rw [acu] at hM
  have hM': ‖(mellin) (fun x↦(ν x:ℂ)) (κ*z)‖ ≤C/κ/ ‖z‖ :=by
    rw [div_div,le_div_iff₀ (by positivity)]; linarith
  have hwz:wε ε τ+z=((1/2+ε+z.re:ℝ) :ℂ)+((τ+z.im:ℝ) :ℂ)* I:=by
    apply Complex.ext <;> simp
  have hGb:=hG (1/2+ε+z.re) (τ+z.im) (by linarith) (by linarith)
  rw [← hwz] at hGb
  have hsplit:=yP (p:=1/8) (by norm_num) τ z.im
  have Yl: ‖(N:ℂ)^z‖ =N^z.re:=Complex.norm_cpow_eq_rpow_re_of_pos hN z
  unfold H
  rw [norm_div,norm_mul,norm_mul,Yl]
  have hG': ‖gP.G (wε ε τ+z)‖ ≤
      CG*((1+ |τ|)^(1/8:ℝ)*(1+ |z.im|)^(1/8:ℝ)) :=
    hGb.trans (mul_le_mul_of_nonneg_left hsplit acs)
  calc ‖(mellin) (fun x↦(ν x:ℂ)) (κ*z)‖ *N^z.re* ‖gP.G (wε ε τ+z)‖ / ‖z‖
      ≤C/κ/ ‖z‖ *N^z.re*
          (CG*((1+ |τ|)^(1/8:ℝ)*(1+ |z.im|)^(1/8:ℝ)))/ ‖z‖ :=by
        gcongr
    _=_:=by field_simp
lemma QV {σ₀:ℝ} (hσ₀:σ₀≠0) (y:ℝ) :
    (1+ |y|)^(1/8:ℝ)/ ‖(σ₀:ℂ)+y* I‖ ^2≤
      4/(min |σ₀| 1)^2*(1+ |y|)^(-(15/8:ℝ)) :=by
  set z:ℂ:=σ₀+y* I
  set m:=min |σ₀| 1
  have hm0:0< m:=lt_min (abs_pos.mpr hσ₀) one_pos
  have hm1:m≤1:=min_le_right _ _
  have hy: |y| ≤ ‖z‖ :=by
    have:=Complex.abs_im_le_norm z; simpa [z] using this
  have hσ: |σ₀| ≤ ‖z‖ :=by
    have:=Complex.abs_re_le_norm z; simpa [z] using this
  have hmz:m*(1+ |y|)/2≤ ‖z‖ :=by
    have:m≤ |σ₀| :=min_le_left _ _
    nlinarith [abs_nonneg y]
  have hu:0<1+ |y| :=by positivity
  have hpos:0< m*(1+ |y|)/2:=by positivity
  calc (1+ |y|)^(1/8:ℝ)/ ‖z‖ ^2≤(1+ |y|)^(1/8:ℝ)/(m*(1+ |y|)/2)^2:=by
        gcongr
    _=4/m^2*((1+ |y|)^(1/8:ℝ)/(1+ |y|)^(2:ℝ)) :=by
        rw [Real.rpow_two]; field_simp; ring
    _=4/m^2*(1+ |y|)^(-(15/8:ℝ)) :=by
        rw [← Real.rpow_sub hu]; norm_num
lemma Vr {B T:ℝ} (hB:0≤B) (hT:1≤ |T|) {z:ℂ} (hz: |T| ≤ ‖z‖) :
    B*((1+ |T|)^(1/8:ℝ)/ ‖z‖ ^2)≤2*B/ |T| :=by
  have hT0:0< |T| :=by linarith
  have h1:(1+ |T|)^(1/8:ℝ)≤2* |T| :=by
    calc (1+ |T|)^(1/8:ℝ)≤(1+ |T|)^(1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _≤2* |T| :=by rw [Real.rpow_one]; linarith
  have h2: |T| ^2≤ ‖z‖ ^2:=pow_le_pow_left₀ hT0.le hz 2
  calc B*((1+ |T|)^(1/8:ℝ)/ ‖z‖ ^2)≤B*(2* |T| / |T| ^2) :=by
        gcongr
    _=2*B/ |T| :=by field_simp
theorem GC (hRH:RiemannHypothesis) (cP:ContDiff ℝ 1 ν)
    (nW: ∀ x>0,0≤ν x) (bC:ν.support⊆Icc (1/2) 2)
    (cD: ∫ x in Ioi (0:ℝ),ν x/x=1) {κ:ℝ} (hκ:0<κ) (JI:κ<1)
    {ε:ℝ} (hε:0<ε) (wW:ε≤1/4) :
    ∃ C:ℝ,0≤C ∧ ∀ N:ℝ,1≤N→ ∀ τ:ℝ,
      ‖(∑' n:ℕ,(μ n:ℂ)*(n:ℂ)^(-wε ε τ)*(dD ν κ (n/N) :ℂ))-
        (riemannZeta (wε ε τ))⁻¹‖ ≤C*N^(-(ε/2))*(1+ |τ|)^(1/8:ℝ) :=by
  obtain ⟨K,hK0,hK⟩:=QS hRH cP bC hκ JI hε wW
  set a:ℝ:= -(ε/2) with ha
  have ha0:a<0:=by rw [ha]; linarith
  set m:ℝ:=min |a| 1 with hm
  have hm0:0< m:=lt_min (abs_pos.mpr ha0.ne) one_pos
  have Xb:Integrable (fun y:ℝ=>(1+ |y|)^(-(15/8:ℝ))) :=by
    have:Integrable (fun x:ℝ=>(1+ ‖x‖)^(-(15/8:ℝ))) :=
      integrable_one_add_norm (by simp; norm_num)
    simpa [Real.norm_eq_abs] using this
  set J:ℝ:= ∫ y:ℝ,(1+ |y|)^(-(15/8:ℝ)) with hJ
  have hJ0:0≤J:=integral_nonneg fun y=>by positivity
  refine ⟨K*(4/m^2)*J/(2*π),by positivity,fun N hN τ=>?_⟩
  have hN0:0<N:=by linarith
  set w:ℂ:=wε ε τ with hw
  have pC:w.re=1/2+ε:=by simp [hw]
  have hw1:w≠1:=by
    intro h; have:=congrArg Complex.re h; rw [pC] at this; simp at this; linarith
  set f:ℂ→ℂ:=fun z=>H ν κ N w z/z with hf
  have hHd: ∀ z:ℂ, -(3/4* ε)<z.re→DifferentiableAt ℂ (H ν κ N w) z:=fun z hz=>
    Fe hRH cP.continuous bC hN0 (by simp [pC]; linarith)
  have hline: ∀ σ₀:ℝ,σ₀≠0→a≤σ₀→σ₀≤5/4→ ∀ y:ℝ,
      ‖f (σ₀+y* I)‖ ≤K*N^σ₀*(1+ |τ|)^(1/8:ℝ)*(4/(min |σ₀| 1)^2)*
        (1+ |y|)^(-(15/8:ℝ)) :=by
    intro σ₀ hσ₀ h1 h2 y
    have hz:(σ₀:ℂ)+y* I≠0:=by
      intro h; apply hσ₀; simpa using congrArg Complex.re h
    have hb:=hK N hN0 τ (σ₀+y* I) (by simpa using h1) (by simpa using h2) hz
    simp only [add_re,ofReal_re,mul_re,I_re,mul_zero,ofReal_im,I_im,mul_one,sub_self,
      add_zero,add_im,mul_im,zero_add] at hb
    calc ‖f (σ₀+y* I)‖ ≤K*N^σ₀*(1+ |τ|)^(1/8:ℝ)*
          ((1+ |y|)^(1/8:ℝ)/ ‖(σ₀:ℂ)+y* I‖ ^2) :=hb
      _≤K*N^σ₀*(1+ |τ|)^(1/8:ℝ)*
          (4/(min |σ₀| 1)^2*(1+ |y|)^(-(15/8:ℝ))) :=
          mul_le_mul_of_nonneg_left (QV hσ₀ y) (by positivity)
      _=_:=by ring
  have hcont: ∀ σ₀:ℝ,σ₀≠0→a≤σ₀→ Continuous (fun y:ℝ=>f (σ₀+y* I)) :=by
    intro σ₀ hσ₀ h1
    refine continuous_iff_continuousAt.mpr fun y=>?_
    have hz:(σ₀:ℂ)+y* I≠0:=by
      intro h; apply hσ₀; simpa using congrArg Complex.re h
    have hc:ContinuousAt (fun y:ℝ=>(σ₀:ℂ)+y* I) y:=by fun_prop
    refine ContinuousAt.comp (f:=fun y:ℝ=>(σ₀:ℂ)+y* I) (g:=f) ?_ hc
    exact ((hHd _ (by simp; linarith)).div differentiableAt_id hz).continuousAt
  have hint: ∀ σ₀:ℝ,σ₀≠0→a≤σ₀→σ₀≤5/4→
      Integrable (fun y:ℝ=>f (σ₀+y* I)) :=fun σ₀ hσ₀ h1 h2=>
    (Xb.const_mul _).mono' (hcont σ₀ hσ₀ h1).aestronglyMeasurable
      (ae_of_all _ (hline σ₀ hσ₀ h1 h2))
  set U:Set ℂ:={z:ℂ | -(3/4* ε)<z.re} with hU
  have hUo:IsOpen U:=isOpen_lt continuous_const Complex.continuous_re
  have hU0:(0:ℂ)∈U:=by simp [hU]; linarith
  have acv:DifferentiableOn ℂ (dslope (H ν κ N w) 0) U:=
    (differentiableOn_dslope (hUo.mem_nhds hU0)).mpr fun z hz=>
      (hHd z hz).differentiableWithinAt
  have hshift:=DN (f:=f) (g:=dslope (H ν κ N w) 0) (a:=a) (b:=5/4)
    (R:=H ν κ N w 0) ha0 (by norm_num)
    (fun s h1 _=>acv.differentiableAt (hUo.mem_nhds (by simp [hU]; linarith)))
    (fun s hs _ _=>by
      rw [hf,dslope_of_ne _ hs,slope_def_field,sub_zero]
      field_simp; ring)
    (hint a ha0.ne le_rfl (by linarith)) (hint (5/4) (by norm_num) (by linarith) le_rfl)
    (by
      intro η hη
      set B:ℝ:=K*N^(5/4:ℝ)*(1+ |τ|)^(1/8:ℝ) with hB
      have hB0:0≤B:=by positivity
      refine ⟨max 1 (2*B/η),fun T hT σ hσ=>?_⟩
      have hT1:1≤ |T| :=(le_max_left _ _).trans hT
      have hz:(σ:ℂ)+T* I≠0:=by
        intro h; have:=congrArg Complex.im h; simp at this; rw [this] at hT1; norm_num at hT1
      have hb:=hK N hN0 τ (σ+T* I) (by simpa using hσ.1) (by simpa using hσ.2) hz
      simp only [add_re,ofReal_re,mul_re,I_re,mul_zero,ofReal_im,I_im,mul_one,sub_self,
        add_zero,add_im,mul_im,zero_add] at hb
      have hzT: |T| ≤ ‖(σ:ℂ)+T* I‖ :=by
        have:=Complex.abs_im_le_norm ((σ:ℂ)+T* I); simpa using this
      have aej:N^σ≤N^(5/4:ℝ) :=Real.rpow_le_rpow_of_exponent_le hN hσ.2
      have hT0:0< |T| :=by linarith
      calc ‖f (σ+T* I)‖ ≤K*N^σ*(1+ |τ|)^(1/8:ℝ)*
            ((1+ |T|)^(1/8:ℝ)/ ‖(σ:ℂ)+T* I‖ ^2) :=hb
        _≤B*((1+ |T|)^(1/8:ℝ)/ ‖(σ:ℂ)+T* I‖ ^2) :=by
            rw [hB]; gcongr
        _≤2*B/ |T| :=Vr hB0 hT1 hzT
        _≤η:=by
            rw [div_le_iff₀ hT0]
            have:=(le_max_right _ _).trans hT
            rw [div_le_iff₀ hη] at this
            linarith)
  have hper:=Np cP nW bC cD hκ JI hN0 (σ:=5/4) (by norm_num)
    (by norm_num) (a:=tw w) (XF w) (TD (by rw [pC]; linarith))
  have hright:(∫ t:ℝ,f ((5/4:ℝ)+t* I))=
      2*π* ∑' n:ℕ,tw w n*(dD ν κ (n/N) :ℂ) :=by
    rw [← hper]
    refine integral_congr_ae (ae_of_all _ fun t=>?_)
    have hre:0<((5/4:ℝ)+t* I:ℂ).re:=by simp
    have hwz:1<(w+((5/4:ℝ)+t* I)).re:=by simp [pC]; linarith
    simp only [hf]
    rw [Wz cP bC hκ hre hwz,XG hwz]
  rw [hright,H_zero cD κ N hw1] at hshift
  have hsum:(∑' n:ℕ,(μ n:ℂ)*(n:ℂ)^(-w)*(dD ν κ (n/N) :ℂ))=
      ∑' n:ℕ,tw w n*(dD ν κ (n/N) :ℂ) :=rfl
  have hpi:(2*π:ℂ)≠0:=by
    have:=Real.pi_pos; exact mul_ne_zero two_ne_zero (by exact_mod_cast this.ne')
  have key:(∑' n:ℕ,tw w n*(dD ν κ (n/N) :ℂ))-(riemannZeta w)⁻¹=
      (∫ t:ℝ,f (a+t* I))/(2*π) :=by
    rw [eq_div_iff hpi]; linear_combination hshift
  have hleft: ‖∫ t:ℝ,f (a+t* I)‖ ≤K*N^a*(1+ |τ|)^(1/8:ℝ)*(4/m^2)*J:=by
    rw [hJ, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (Xb.const_mul _)
      (ae_of_all _ (hline a ha0.ne le_rfl (by linarith)))
  have acw: ‖(2*π:ℂ)‖ =2*π:=by
    rw [norm_mul,Complex.norm_two,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hsum,key,norm_div,acw,div_le_iff₀ (by positivity)]
  calc ‖∫ t:ℝ,f (a+t* I)‖ ≤K*N^a*(1+ |τ|)^(1/8:ℝ)*(4/m^2)*J:=hleft
    _=K*(4/m^2)*J/(2*π)*N^(-(ε/2))*(1+ |τ|)^(1/8:ℝ)*(2*π) :=by
        rw [ha]; field_simp
end aF.Nyman.Smooth
end
end

-- aF.qU
section
open Complex Real Set Filter Topology ZetaAsymptotics
noncomputable section
namespace aF.qU
lemma XH {n:ℕ} (hn:0<n) {s:ℝ} (hs:0<s) :
    term n s≤((n:ℝ)^(-s)-((n:ℝ)+1)^(-s))/s:=by
  have hn0:(0:ℝ)<n:=Nat.cast_pos.mpr hn
  have h0:(0:ℝ)∉uIcc (n:ℝ) (n+1) :=by
    rw [uIcc_of_le (by linarith)]
    exact fun h=>by linarith [h.1]
  have hle:term n s≤ ∫ x:ℝ in n..(n+1),x^(-(s+1)) :=by
    refine intervalIntegral.integral_mono_on (by linarith) (term_welldef hn hs)
      (intervalIntegral.intervalIntegrable_rpow (Or.inr h0)) fun x hx=>?_
    have hx0:0<x:=hn0.trans_le hx.1
    rw [rpow_neg hx0.le, ← one_div]
    exact div_le_div_of_nonneg_right (by linarith [hx.2]) (rpow_nonneg hx0.le _)
  refine hle.trans (le_of_eq ?_)
  rw [integral_rpow (Or.inr ⟨by linarith,h0⟩),show -(s+1)+1= -s by ring]
  field_simp
  ring
lemma QW {s:ℝ} (hs:0<s) :termTSum s≤1/s:=by
  refine Real.tsum_le_of_sum_range_le (fun n=>term_nonneg _ _) fun N=>?_
  have h: ∀ k∈Finset.range N,term (k+1) s≤
      ((((k:ℕ) :ℝ)+1)^(-s)-((((k+1:ℕ) :ℝ))+1)^(-s))/s:=by
    intro k _
    have:=XH (n:=k+1) (by omega) hs
    push_cast at this ⊢
    exact this
  refine (Finset.sum_le_sum h).trans ?_
  rw [← Finset.sum_div,Finset.sum_range_sub' (fun k:ℕ=>(((k:ℕ) :ℝ)+1)^(-s))]
  apply div_le_div_of_nonneg_right _ hs.le
  simp only [Nat.cast_zero,zero_add,one_rpow]
  linarith [rpow_nonneg (by positivity:(0:ℝ)≤(N:ℝ)+1) (-s)]
lemma Qr {σ:ℝ} (hσ:1<σ) :
    riemannZeta (σ:ℂ)=((∑' n:ℕ,1/((n:ℝ)+1)^σ:ℝ) :ℂ) :=by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hσ),Complex.ofReal_tsum]
  refine tsum_congr fun n=>?_
  rw [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_cpow (by positivity)]
  push_cast
  rfl
theorem qV {σ:ℝ} (hσ:1<σ) :
    1/(σ-1)≤ ‖riemannZeta (σ:ℂ)‖ :=by
  have hZ0:0≤ ∑' n:ℕ,1/((n:ℝ)+1)^σ:=
    tsum_nonneg fun n=>by positivity
  rw [Qr hσ,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hZ0]
  have hT:=termTSum_of_lt hσ
  have oC:0<σ:=by linarith
  have hT1:=QW oC
  have hσ1:0<σ-1:=by linarith
  set Z:= ∑' n:ℕ,1/((n:ℝ)+1)^σ
  rw [hT] at hT1
  have key:1/(σ-1)-1/σ≤1/σ*Z:=by linarith
  have e:1/(σ-1)-1/σ=1/σ*(1/(σ-1)) :=by field_simp; ring
  rw [e] at key
  exact le_of_mul_le_mul_left key (by positivity)
end aF.qU
end
end

-- aF.XQ
section
open Complex Real Set Filter Topology MeasureTheory
open scoped ArithmeticFunction.Moebius
noncomputable section
namespace aF.Nyman.Converse
theorem Qt {n:ℕ} (c:Fin n→ℂ) (θ:Fin n→ℝ) (hθ: ∀ k,0<θ k ∧ θ k≤1)
    (hsum: ∑ k,c k*(θ k:ℂ)=0) {s:ℂ} (hs:0<s.re) (hs1:s.re<1) :
    ∫ x in Ioc (0:ℝ) 1,(1- ∑ k,c k*((Int.fract (θ k/x) :ℝ) :ℂ))*(x:ℂ)^(s-1)=
      (1+riemannZeta s* ∑ k,c k*(θ k:ℂ)^s)/s:=by
  have hs0:s≠0:=fun h=>by simp [h] at hs
  have hh:IntegrableOn (fun x:ℝ=>(x:ℂ)^(s-1)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith))
  have hfm: ∀ k,Measurable (fun x:ℝ=>((Int.fract (θ k/x) :ℝ) :ℂ)) :=fun k=>
    Complex.measurable_ofReal.comp (measurable_fract.comp (measurable_const.div measurable_id))
  have hfrac: ∀ k,IntegrableOn
      (fun x:ℝ=>((Int.fract (θ k/x) :ℝ) :ℂ)*(x:ℂ)^(s-1)) (Ioc 0 1) :=fun k=>by
    refine hh.norm.mono' ((hfm k).mul (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable
      (Eventually.of_forall fun x=>?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_fract_le _)
  have hpt: ∀ x:ℝ,(1- ∑ k,c k*((Int.fract (θ k/x) :ℝ) :ℂ))*(x:ℂ)^(s-1)=
      (x:ℂ)^(s-1)- ∑ k,c k*(((Int.fract (θ k/x) :ℝ) :ℂ)*(x:ℂ)^(s-1)) :=
    fun x=>by simp only [sub_mul,one_mul,Finset.sum_mul,mul_assoc]
  simp_rw [hpt]
  rw [integral_sub hh (integrable_finsetSum _ fun k _=>(hfrac k).const_mul (c k)),
    integral_finsetSum _ fun k _=>(hfrac k).const_mul (c k)]
  simp_rw [integral_const_mul]
  have hk: ∀ k,c k* ∫ x in Ioc (0:ℝ) 1,
      ((Int.fract (θ k/x) :ℝ) :ℂ)*(x:ℂ)^(s-1)=
        c k*(θ k:ℂ)*(-1/(1-s))-riemannZeta s/s*(c k*(θ k:ℂ)^s) :=
    fun k=>by rw [jM (hθ k).1 (hθ k).2 hs hs1]; ring
  simp_rw [hk]
  have h1: ∫ x in Ioc (0:ℝ) 1,(x:ℂ)^(s-1)=1/s:=by
    rw [← intervalIntegral.integral_of_le zero_le_one,
      integral_cpow (Or.inl (by simp; linarith)),show s-1+1=s by ring]
    simp [Complex.zero_cpow hs0]
  rw [h1,Finset.sum_sub_distrib, ← Finset.sum_mul,hsum, ← Finset.mul_sum]
  field_simp
  ring
variable (ν:ℝ→ℝ)
def S (x:ℝ) :ℝ:=dD ν (1/2) x
def bco (ε N:ℝ) (n:ℕ) :ℂ:=(μ n:ℂ)*(n:ℂ)^(-(ε:ℂ))*(S ν (n/N) :ℂ)
def Mn (N:ℝ) :ℕ:= ⌈3*N⌉₊
def θN (N:ℝ) :Fin (Mn N)→ℝ:=fun k=>1/((k:ℝ)+1)
def cN (ε N:ℝ) :Fin (Mn N)→ℂ:=fun k=>
  -bco ν ε N (k+1)+
    if (k:ℕ)=0 then ∑ j:Fin (Mn N),bco ν ε N (j+1)/((j:ℂ)+1) else 0
def D (N:ℝ) (w:ℂ) :ℂ:= ∑' n:ℕ,(μ n:ℂ)*(n:ℂ)^(-w)*(S ν (n/N) :ℂ)
lemma XJ (N:ℝ) (k:Fin (Mn N)) :0<θN N k ∧ θN N k≤1:=by
  have:(1:ℝ)≤(k:ℝ)+1:=by linarith [(Nat.cast_nonneg k:(0:ℝ)≤k)]
  refine ⟨by unfold θN; positivity,?_⟩
  unfold θN; rw [div_le_one (by linarith)]; exact this
lemma WA (N:ℝ) (k:Fin (Mn N)) (s:ℂ) :
    ((θN N k:ℝ) :ℂ)^s=((k:ℂ)+1)^(-s) :=by
  have harg:((k:ℂ)+1).arg≠π:=by
    rw [show ((k:ℂ)+1)=(((k:ℝ)+1:ℝ) :ℂ) by push_cast; rfl,
      Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_pos.ne
  simp only [θN]
  push_cast
  rw [one_div,inv_cpow _ _ harg,cpow_neg]
lemma LJ (ε N:ℝ) (hM:0<Mn N) : ∑ k,cN ν ε N k*(θN N k:ℂ)=0:=by
  set T:= ∑ j:Fin (Mn N),bco ν ε N (j+1)/((j:ℂ)+1)
  have hθ: ∀ k:Fin (Mn N),(θN N k:ℂ)=1/((k:ℂ)+1) :=fun k=>by
    simp [θN]
  simp only [cN,add_mul,Finset.sum_add_distrib,hθ]
  have h0: ∑ k:Fin (Mn N),(if (k:ℕ)=0 then T else 0)*(1/((k:ℂ)+1))=T:=by
    rw [Finset.sum_eq_single ⟨0,hM⟩]
    · simp
    · intro b _ hb
      have:(b:ℕ)≠0:=fun h=>hb (Fin.ext h)
      simp [this]
    · simp
  rw [h0]
  have: ∑ k:Fin (Mn N), -bco ν ε N (k+1)*(1/((k:ℂ)+1))= -T:=by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _=>?_
    ring
  rw [this]; ring
lemma Vt (bC:ν.support⊆Icc (1/2) 2) {x:ℝ} (hx:3≤x) :S ν x=0:=by
  obtain ⟨c, -,hc,h⟩:=jc bC
  refine h (1/2) x ⟨by norm_num,by norm_num⟩ ?_
  rw [hc]
  have:=Real.log_two_lt_d9
  linarith
lemma Qv (bC:ν.support⊆Icc (1/2) 2) {N:ℝ} (hN:0<N) (w:ℂ) :
    D ν N w= ∑ k:Fin (Mn N),(μ (k+1) :ℂ)*((k:ℂ)+1)^(-w)*
      (S ν (((k:ℝ)+1)/N) :ℂ) :=by
  unfold D
  rw [tsum_eq_sum (s:=Finset.range (Mn N+1)),Finset.sum_range_succ',
    Fin.sum_univ_eq_sum_range (fun k=>(μ (k+1) :ℂ)*((k:ℂ)+1)^(-w)*
      (S ν (((k:ℝ)+1)/N) :ℂ))]
  · simp
  · intro n hn
    simp only [Finset.mem_range,not_lt] at hn
    have h3:3≤(n:ℝ)/N:=by
      rw [le_div_iff₀ hN]
      have:3*N≤(Mn N:ℝ) :=Nat.le_ceil _
      have:(Mn N:ℝ)+1≤n:=by exact_mod_cast hn
      linarith
    simp [Vt ν bC h3]
lemma QX (bC:ν.support⊆Icc (1/2) 2) {ε N:ℝ} (hN:0<N) (hM:0<Mn N)
    (s:ℂ) : ∑ k,cN ν ε N k*(θN N k:ℂ)^s=D ν N (1+ε)-D ν N (s+ε) :=by
  rw [Qv ν bC hN,Qv ν bC hN]
  have hpos: ∀ k:Fin (Mn N),((k:ℂ)+1)≠0:=fun k=>Nat.cast_add_one_ne_zero (k:ℕ)
  have hb: ∀ k:Fin (Mn N), ∀ z:ℂ,bco ν ε N (k+1)*((k:ℂ)+1)^(-z)=
      (μ (k+1) :ℂ)*((k:ℂ)+1)^(-(z+ε))*(S ν (((k:ℝ)+1)/N) :ℂ) :=by
    intro k z
    simp only [bco]
    push_cast
    rw [show -(z+(ε:ℂ))= -(ε:ℂ)+ -z by ring,cpow_add _ _ (hpos k)]
    ring
  simp only [cN,add_mul,Finset.sum_add_distrib,WA]
  have h0: ∑ k:Fin (Mn N),(if (k:ℕ)=0 then
      ∑ j:Fin (Mn N),bco ν ε N (j+1)/((j:ℂ)+1) else 0)*((k:ℂ)+1)^(-s)=
      ∑ j:Fin (Mn N),bco ν ε N (j+1)/((j:ℂ)+1) :=by
    rw [Finset.sum_eq_single ⟨0,hM⟩]
    · simp
    · intro b _ hb
      have:(b:ℕ)≠0:=fun h=>hb (Fin.ext h)
      simp [this]
    · simp
  rw [h0]
  have h1: ∑ j:Fin (Mn N),bco ν ε N (j+1)/((j:ℂ)+1)=
      ∑ k:Fin (Mn N),(μ (k+1) :ℂ)*((k:ℂ)+1)^(-(1+(ε:ℂ)))*
        (S ν (((k:ℝ)+1)/N) :ℂ) :=by
    refine Finset.sum_congr rfl fun k _=>?_
    rw [← hb k 1,cpow_neg_one,div_eq_mul_inv]
  have h2: ∑ k:Fin (Mn N), -bco ν ε N (k+1)*((k:ℂ)+1)^(-s)=
      -∑ k:Fin (Mn N),(μ (k+1) :ℂ)*((k:ℂ)+1)^(-(s+(ε:ℂ)))*
        (S ν (((k:ℝ)+1)/N) :ℂ) :=by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _=>?_
    rw [neg_mul,hb k s]
  rw [h1,h2]; ring
open gW in
lemma Qw (ξ:ℝ) :aZ ξ=(1/2:ℂ)+((2*π*ξ:ℝ) :ℂ)* I:=by
  simp [aZ]
open gW in
lemma xB (ξ ε:ℝ) :
    aZ ξ+ε=((1/2+ε:ℝ) :ℂ)+((2*π*ξ:ℝ) :ℂ)* I:=by
  simp [aZ]; ring
lemma pL (hRH:RiemannHypothesis) :
    ∃ C:ℝ,0≤C ∧ ∀ t:ℝ, ‖riemannZeta (1/2+t* I)‖ ≤C*(1+ |t|)^(1/16:ℝ) :=by
  obtain ⟨C₀,hC₀⟩:=lN.qo hRH (1/16) (by norm_num)
  have hcont:ContinuousOn (fun t:ℝ=>riemannZeta (1/2+t* I)) (Icc (-3) 3) :=by
    intro t _
    refine ContinuousAt.continuousWithinAt ?_
    have hne:(1/2:ℂ)+t* I≠1:=by
      intro h; have:=congrArg Complex.re h; simp at this
    exact ContinuousAt.comp (g:=riemannZeta) (differentiableAt_riemannZeta hne).continuousAt
      (by fun_prop)
  obtain ⟨M,hM⟩:=isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max (max C₀ 0) M,le_trans (le_max_right _ _) (le_max_left _ _),fun t=>?_⟩
  have hu:1≤(1+ |t|)^(1/16:ℝ) :=Real.one_le_rpow (by linarith [abs_nonneg t])
    (by norm_num)
  have hC:0≤ max (max C₀ 0) M:=le_trans (le_max_right _ _) (le_max_left _ _)
  rcases le_or_gt |t| 3 with ht | ht
  · calc ‖riemannZeta (1/2+t* I)‖ ≤M:=hM t (abs_le.mp ht)
      _≤ max (max C₀ 0) M:=le_max_right _ _
      _≤_:=le_mul_of_one_le_right hC hu
  · calc ‖riemannZeta (1/2+t* I)‖ ≤C₀* |t| ^(1/16:ℝ) :=hC₀ t ht.le
      _≤ max C₀ 0* |t| ^(1/16:ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _≤ max (max C₀ 0) M*(1+ |t|)^(1/16:ℝ) :=
          mul_le_mul (le_max_left _ _)
            (Real.rpow_le_rpow (abs_nonneg t) (by linarith) (by norm_num)) (by positivity) hC
open gW in
lemma Oj (ξ:ℝ) :(1+ |2*π*ξ|)/4≤ ‖aZ ξ‖ :=by
  have h1: |(aZ ξ).re| ≤ ‖aZ ξ‖ :=Complex.abs_re_le_norm _
  have h2: |(aZ ξ).im| ≤ ‖aZ ξ‖ :=Complex.abs_im_le_norm _
  have hre:(aZ ξ).re=1/2:=by simp [aZ]
  have him:(aZ ξ).im=2*π*ξ:=by simp [aZ]
  rw [hre] at h1; rw [him] at h2
  norm_num at h1
  linarith [abs_nonneg (2*π*ξ)]
open gW in
lemma Fh {ξ:ℝ} {X:ℂ} {B p:ℝ}
    (hX: ‖X‖ ≤B*(1+ |2*π*ξ|)^p) :
    ‖X/aZ ξ‖ ^2≤16*B^2*(1+ |2*π*ξ|)^(2*p-2) :=by
  set u:ℝ:=1+ |2*π*ξ| with hu
  have hu0:0<u:=by positivity
  have hs:=Oj ξ
  have hs0:0< ‖aZ ξ‖ :=by linarith
  rw [norm_div,div_pow]
  have hnum: ‖X‖ ^2≤(B*u^p)^2:=pow_le_pow_left₀ (norm_nonneg _) hX 2
  have hden:(u/4)^2≤ ‖aZ ξ‖ ^2:=pow_le_pow_left₀ (by positivity) hs 2
  have hpow:(B*u^p)^2/(u/4)^2=16*B^2*u^(2*p-2) :=by
    have e1:u^(2*p-2)=(u^p)^2/u^2:=by
      rw [Real.rpow_sub hu0,mul_comm 2 p,Real.rpow_mul hu0.le]
      simp only [Real.rpow_two]
    rw [e1]
    field_simp
    ring
  calc ‖X‖ ^2/ ‖aZ ξ‖ ^2≤(B*u^p)^2/(u/4)^2:=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _=_:=hpow
lemma jC {r:ℝ} (hr:1<r) :
    Integrable (fun ξ:ℝ=>(1+ |2*π*ξ|)^(-r)) :=by
  have h:Integrable (fun x:ℝ=>(1+ ‖x‖)^(-r)) :=integrable_one_add_norm (by simpa)
  have:=h.comp_mul_left' (R:=2*π) (by positivity)
  simpa [Real.norm_eq_abs] using this
open gW in
lemma TI:volume {ξ:ℝ | riemannZeta (aZ ξ)=0}=0:=by
  refine Set.Countable.measure_zero ?_ _
  have hsub:{ξ:ℝ | riemannZeta (aZ ξ)=0}⊆
      ⋃ k:ℕ,(fun ρ:ℂ=>ρ.im/(2*π)) '' Zeta23.Bc (-(k:ℝ)) k:=by
    intro ξ hξ
    obtain ⟨k,hk⟩:=exists_nat_gt |2*π*ξ|
    have him:(aZ ξ).im=2*π*ξ:=by simp [aZ]
    refine mem_iUnion.mpr ⟨k,aZ ξ,⟨⟨hξ,by simp [aZ],by simp [aZ]; norm_num⟩,?_,?_⟩,?_⟩
    · rw [him]; linarith [neg_abs_le (2*π*ξ)]
    · rw [him]; linarith [le_abs_self (2*π*ξ)]
    · simp only [him]; field_simp
  refine Set.Countable.mono hsub (Set.countable_iUnion fun k=>?_)
  exact ((Zeta23.Mt _ _).image _).countable
open gW in
lemma oI {σ:ℝ} (hσ:1/2+σ≠1) :
    Continuous (fun ξ:ℝ=>riemannZeta (aZ ξ+σ)) :=by
  refine continuous_iff_continuousAt.mpr fun ξ=>?_
  have hne:aZ ξ+σ≠1:=by
    intro h; have:=congrArg Complex.re h; simp [aZ] at this; exact hσ (by linarith)
  exact ContinuousAt.comp (g:=riemannZeta) (differentiableAt_riemannZeta hne).continuousAt
    (by fun_prop)
open gW in
lemma QY (hRH:RiemannHypothesis) {K:ℝ}
    (hK: ∀ t ε:ℝ,0<ε→ε≤1/4→
      ‖riemannZeta ((1/2:ℂ)+t* I)‖ ≤
        ‖riemannZeta (((1/2+ε:ℝ) :ℂ)+t* I)‖ *Real.exp (K* ε*Real.log (|t| +3)))
    {ε:ℝ} (hε:0<ε) (wW:ε≤1/4) (WB:K* ε≤1/4) (ξ:ℝ) :
    ‖1-riemannZeta (aZ ξ)/riemannZeta (aZ ξ+ε)‖ ≤
      4*(1+ |2*π*ξ|)^(1/4:ℝ) :=by
  set t:ℝ:=2*π*ξ
  have hz:riemannZeta (aZ ξ+ε)≠0:=by
    rw [xB]
    have hre:(((1/2+ε:ℝ) :ℂ)+(t:ℂ)* I).re=1/2+ε:=by simp
    refine fun h=>?_
    have h1:(((1/2+ε:ℝ) :ℂ)+(t:ℂ)* I)≠1:=by
      intro h'; have:=congrArg Complex.re h'; rw [hre] at this; simp at this; linarith
    have:=hRH _ h (fun ⟨n,hn⟩=>by
      have:=congrArg Complex.re hn; rw [hre] at this; simp at this
      have:(0:ℝ)≤n:=Nat.cast_nonneg n
      linarith) h1
    rw [hre] at this; linarith
  have hb:=hK t ε hε wW
  rw [← Qw, ← xB] at hb
  have hu:1≤ |t| +3:=by linarith [abs_nonneg t]
  have hexp:Real.exp (K* ε*Real.log (|t| +3))≤3*(1+ |t|)^(1/4:ℝ) :=by
    rw [mul_comm, ← Real.rpow_def_of_pos (by linarith)]
    calc (|t| +3)^(K* ε)≤(|t| +3)^(1/4:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hu WB
      _≤(3*(1+ |t|))^(1/4:ℝ) :=
          Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg t]) (by norm_num)
      _=3^(1/4:ℝ)*(1+ |t|)^(1/4:ℝ) :=
          Real.mul_rpow (by norm_num) (by positivity)
      _≤3*(1+ |t|)^(1/4:ℝ) :=by
          gcongr
          calc (3:ℝ)^(1/4:ℝ)≤3^(1:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _=3:=Real.rpow_one 3
  have hratio: ‖riemannZeta (aZ ξ)/riemannZeta (aZ ξ+ε)‖ ≤
      3*(1+ |t|)^(1/4:ℝ) :=by
    rw [norm_div,div_le_iff₀ (norm_pos_iff.mpr hz)]
    calc ‖riemannZeta (aZ ξ)‖ ≤ ‖riemannZeta (aZ ξ+ε)‖ *
          Real.exp (K* ε*Real.log (|t| +3)) :=hb
      _≤ ‖riemannZeta (aZ ξ+ε)‖ *(3*(1+ |t|)^(1/4:ℝ)) :=
          mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _=_:=by ring
  have h1:1≤(1+ |t|)^(1/4:ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num)
  calc ‖1-riemannZeta (aZ ξ)/riemannZeta (aZ ξ+ε)‖ ≤
        ‖(1:ℂ)‖ + ‖riemannZeta (aZ ξ)/riemannZeta (aZ ξ+ε)‖ :=norm_sub_le _ _
    _≤1+3*(1+ |t|)^(1/4:ℝ) :=by rw [norm_one]; linarith
    _≤4*(1+ |t|)^(1/4:ℝ) :=by linarith
lemma JK {ε:ℝ} (hε:0<ε) : ‖(riemannZeta (1+ε))⁻¹‖ ≤ε:=by
  have h:=qU.qV (σ:=1+ε) (by linarith)
  rw [show (1+ε)-1=ε by ring] at h
  have hpos:0< ‖riemannZeta ((1+ε:ℝ) :ℂ)‖ :=lt_of_lt_of_le (by positivity) h
  push_cast at h hpos
  rw [norm_inv]
  calc ‖riemannZeta (1+ε)‖⁻¹≤(1/ε)⁻¹:=inv_anti₀ (by positivity) h
    _=ε:=by rw [one_div,inv_inv]
lemma Vv (bC:ν.support⊆Icc (1/2) 2) (nW: ∀ x>0,0≤ν x)
    (cD: ∫ x in Ioi (0:ℝ),ν x/x=1) {ε:ℝ} (hε:0<ε) :
    Tendsto (fun N:ℝ=>D ν N (1+ε)) atTop (𝓝 (riemannZeta (1+ε))⁻¹) :=by
  have hre:1<((1:ℂ)+ε).re:=by simp; linarith
  rw [gP.xd hre]
  unfold D
  have hlim: ∀ n:ℕ,(μ n:ℂ)/(n:ℂ)^((1:ℂ)+ε)=
      (μ n:ℂ)*(n:ℂ)^(-((1:ℂ)+ε))*1:=fun n=>by
    rw [cpow_neg,mul_one,div_eq_mul_inv]
  simp_rw [hlim]
  refine tendsto_tsum_of_dominated_convergence (bound:=fun n:ℕ=>((n:ℝ)^(1+ε))⁻¹)
    (Real.summable_nat_rpow_inv.mpr (by linarith)) (fun n=>?_) ?_
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    obtain ⟨c, -,hc,h⟩:=yI bC cD
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (2*(n:ℝ))] with N hN
    have hn0:(0:ℝ)<n:=by exact_mod_cast hn
    have hN0:0<N:=by linarith
    have hx:(n:ℝ)/N≤1-c*(1/2) :=by
      rw [hc,div_le_iff₀ hN0]
      have:=Real.log_two_lt_d9
      nlinarith
    rw [S,h (1/2) _ (by norm_num) (by positivity) hx]
    simp
  · filter_upwards [eventually_gt_atTop 0] with N hN n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp; positivity
    have hn0:(0:ℝ)<n:=by exact_mod_cast hn
    have hx:(0:ℝ)<n/N:=by positivity
    have hS0:0≤S ν (n/N) :=tj nW hx (by norm_num:(0:ℝ)<1/2)
    have hS1:S ν (n/N)≤1:=wY nW cD (by norm_num:(0:ℝ)<1/2) hx
    rw [norm_mul,norm_mul,norm_natCast_cpow_of_pos hn,Complex.norm_intCast,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hS0]
    have hmu: |(μ n:ℝ)| ≤1:=by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have Zt:(-((1:ℂ)+ε)).re= -(1+ε) :=by simp
    rw [Zt,Real.rpow_neg hn0.le]
    calc |(μ n:ℝ)| *((n:ℝ)^(1+ε))⁻¹*S ν (n/N)≤1*((n:ℝ)^(1+ε))⁻¹*1:=by
          gcongr
      _=((n:ℝ)^(1+ε))⁻¹:=by ring
lemma LL (a b c:ℂ) :
    ‖a-b+c‖ ^2≤3*(‖a‖ ^2+ ‖b‖ ^2+ ‖c‖ ^2) :=by
  have h: ‖a-b+c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have h0:0≤ ‖a-b+c‖ :=norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖),sq_nonneg (‖b‖ - ‖c‖),sq_nonneg (‖a‖ - ‖c‖),
    norm_nonneg a,norm_nonneg b,norm_nonneg c]
open gW in
theorem nD (hRH:RiemannHypothesis) :
    ∀ η:ℝ,0<η→ ∃ (n:ℕ) (c:Fin n→ℂ),
      ∑ k:Fin n,c k*((1/((k:ℝ)+1) :ℝ) :ℂ)=0 ∧
      ∫ x in Ioc (0:ℝ) 1,
        ‖1- ∑ k:Fin n,c k*((Int.fract ((1/((k:ℝ)+1))/x) :ℝ) :ℂ)‖ ^2<η:=by
  intro η hη
  have ⟨ν,TJ,TK,bC,ZH⟩:=zE
  have cP:ContDiff ℝ 1 ν:=TJ.of_le (by simp)
  have nW: ∀ x>0,0≤ν x:=fun x _↦TK x
  have cD: ∫ x in Ioi 0,ν x/x=1:=by
    rwa [← MeasureTheory.integral_Ici_eq_integral_Ioi]
  obtain ⟨K,hK0,hK⟩:=Ratio.GA hRH
  obtain ⟨C₁,hC₁,hζ⟩:=pL hRH
  have Xc: ∀ ξ:ℝ, ‖riemannZeta (aZ ξ)‖ ≤C₁*(1+ |2*π*ξ|)^(1/16:ℝ) :=
    fun ξ=>by rw [Qw]; exact hζ _
  set J₂:ℝ:= ∫ ξ:ℝ,(1+ |2*π*ξ|)^(-(13/8:ℝ)) with hJ₂
  set J₃:ℝ:= ∫ ξ:ℝ,(1+ |2*π*ξ|)^(-(15/8:ℝ)) with hJ₃
  have hsne: ∀ ξ:ℝ,aZ ξ≠0:=fun ξ h=>by
    have:=congrArg Complex.re h; simp [aZ] at this
  have acy: ∀ ε:ℝ,0<ε→ε≤1/4→ ∀ ξ:ℝ,riemannZeta (aZ ξ+ε)≠0:=by
    intro ε hε wW ξ h
    have hre:(aZ ξ+ε).re=1/2+ε:=by simp [aZ]
    have h1:aZ ξ+ε≠1:=by
      intro h'; have:=congrArg Complex.re h'; rw [hre] at this; simp at this; linarith
    have:=hRH _ h (fun ⟨n,hn⟩=>by
      have:=congrArg Complex.re hn; rw [hre] at this; simp at this
      have:(0:ℝ)≤n:=Nat.cast_nonneg n
      linarith) h1
    rw [hre] at this; linarith
  set F₁:ℝ→ℝ→ℝ:=fun ε ξ=>
    ‖(1-riemannZeta (aZ ξ)/riemannZeta (aZ ξ+ε))/aZ ξ‖ ^2 with hF₁
  set ε₀:ℝ:=min (1/4) (1/(4*(K+1))) with hε₀
  have XK:0<ε₀:=lt_min (by norm_num) (by positivity)
  have WB: ∀ ε:ℝ,0<ε→ε≤ε₀→K* ε≤1/4:=by
    intro ε _ hε
    have h1:ε≤1/(4*(K+1)) :=hε.trans (min_le_right _ _)
    calc K* ε≤K*(1/(4*(K+1))) :=mul_le_mul_of_nonneg_left h1 hK0
      _≤1/4:=by rw [mul_one_div,div_le_iff₀ (by positivity)]; linarith
  have Qy: ∀ ε:ℝ,0<ε→ε≤1/4→ Continuous (F₁ ε) :=by
    intro ε hε wW
    have hz0:Continuous fun ξ:ℝ=>riemannZeta (aZ ξ) :=by
      simpa using oI (σ:=0) (by norm_num)
    have aaQ:Continuous fun ξ:ℝ=>riemannZeta (aZ ξ+ε) :=
      oI (by linarith)
    have hs:Continuous fun ξ:ℝ=>aZ ξ:=by unfold aZ; fun_prop
    exact ((continuous_const.sub (hz0.div aaQ (acy ε hε wW))).div hs hsne).norm.pow 2
  have NA: ∀ ε:ℝ,0<ε→ε≤ε₀→ ∀ ξ:ℝ,
      F₁ ε ξ≤16*4^2*(1+ |2*π*ξ|)^(-(3/2:ℝ)) :=by
    intro ε hε Xd ξ
    have h:=Fh (ξ:=ξ)
      (QY hRH hK hε (Xd.trans (min_le_left _ _)) (WB ε hε Xd) ξ)
    rw [show 2*(1/4:ℝ)-2= -(3/2) by norm_num] at h
    exact h
  set εs:ℕ→ℝ:=fun j=>ε₀/((j:ℝ)+1) with hεs
  have hεs0: ∀ j,0<εs j:=fun j=>by positivity
  have LO: ∀ j,εs j≤ε₀:=fun j=>by
    rw [hεs]; exact div_le_self XK.le (by linarith [(Nat.cast_nonneg j:(0:ℝ)≤j)])
  have Rq:Tendsto εs atTop (𝓝 0) :=by
    have:=tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ε₀
    simp only [mul_zero] at this
    refine this.congr fun j=>?_
    rw [hεs]; ring
  have hT1:Tendsto (fun j=> ∫ ξ,F₁ (εs j) ξ) atTop (𝓝 0) :=by
    have hae: ∀ᵐ ξ ∂(volume:Measure ℝ),riemannZeta (aZ ξ)≠0:=by
      rw [ae_iff]; simpa using TI
    have:=tendsto_integral_of_dominated_convergence
      (F:=fun j ξ=>F₁ (εs j) ξ) (f:=fun _=>(0:ℝ))
      (fun ξ=>16*4^2*(1+ |2*π*ξ|)^(-(3/2:ℝ)))
      (fun j=>(Qy _ (hεs0 j) ((LO j).trans (min_le_left _ _))).aestronglyMeasurable)
      ((jC (by norm_num)).const_mul _)
      (fun j=>ae_of_all _ fun ξ=>by
        rw [Real.norm_of_nonneg (by positivity)]
        exact NA _ (hεs0 j) (LO j) ξ)
      (by
        filter_upwards [hae] with ξ hξ
        have hne:aZ ξ≠1:=fun h=>by
          have:=congrArg Complex.re h; simp [aZ] at this
        have h1:Tendsto (fun j=>riemannZeta (aZ ξ+(εs j:ℂ))) atTop
            (𝓝 (riemannZeta (aZ ξ))) :=by
          have h2:Tendsto (fun j=>aZ ξ+(εs j:ℂ)) atTop (𝓝 (aZ ξ+((0:ℝ) :ℂ))) :=
            tendsto_const_nhds.add ((continuous_ofReal.tendsto 0).comp Rq)
          rw [ofReal_zero,add_zero] at h2
          exact ((differentiableAt_riemannZeta hne).continuousAt.tendsto).comp h2
        have h3:=(((tendsto_const_nhds (x:=(1:ℂ))).sub
          ((tendsto_const_nhds (x:=riemannZeta (aZ ξ))).div h1 hξ)).div_const
            (aZ ξ)).norm.pow 2
        rw [div_self hξ,sub_self,zero_div,norm_zero] at h3
        simpa [hF₁] using h3)
    simpa using this
  have Zy:Tendsto (fun j=>16*(C₁*(2* εs j))^2*J₃) atTop (𝓝 0) :=by
    have:=((((Rq.const_mul 2).const_mul C₁).pow 2).const_mul 16).mul_const J₃
    simpa using this
  obtain ⟨j,hj1,hj3⟩:=((hT1.eventually (gt_mem_nhds (by positivity:(0:ℝ)<η/9))).and
    (Zy.eventually (gt_mem_nhds (by positivity:(0:ℝ)<η/9)))).exists
  set ε:ℝ:=εs j with Zp
  have hε:0<ε:=hεs0 j
  have wW:ε≤1/4:=(LO j).trans (min_le_left _ _)
  obtain ⟨C₂,hC₂,hsm⟩:=Smooth.GC hRH cP nW bC cD
    (κ:=1/2) (by norm_num) (by norm_num) hε wW
  have Zz:Tendsto (fun N:ℝ=>16*(C₁*C₂*N^(-(ε/2)))^2*J₂) atTop (𝓝 0) :=by
    have:=(((tendsto_rpow_neg_atTop (by positivity:0<ε/2)).const_mul (C₁*C₂)).pow 2
      |>.const_mul 16).mul_const J₂
    simpa using this
  have aaR:=Metric.tendsto_nhds.mp (Vv ν bC nW cD hε) ε hε
  obtain ⟨N,hN1,hN2,hN3⟩:=((eventually_ge_atTop (1:ℝ)).and
    ((Zz.eventually (gt_mem_nhds (by positivity:(0:ℝ)<η/9))).and aaR)).exists
  have hN0:0<N:=by linarith
  have hM:0<Mn N:=Nat.ceil_pos.mpr (by linarith)
  have hD1: ‖D ν N (1+ε)‖ ≤2* ε:=by
    rw [dist_eq_norm] at hN3
    have:=JK hε
    calc ‖D ν N (1+ε)‖ ≤ ‖D ν N (1+ε)-(riemannZeta (1+ε))⁻¹‖ +
          ‖(riemannZeta (1+ε))⁻¹‖ :=norm_le_norm_sub_add _ _
      _≤ε+ε:=add_le_add hN3.le this
      _=2* ε:=by ring
  refine ⟨Mn N,cN ν ε N,LJ ν ε N hM,?_⟩
  set g:ℝ→ℂ:=fun x=>1- ∑ k,cN ν ε N k*((Int.fract (θN N k/x) :ℝ) :ℂ) with hg
  have hfm: ∀ k,Measurable (fun x:ℝ=>((Int.fract (θN N k/x) :ℝ) :ℂ)) :=fun k=>
    Complex.measurable_ofReal.comp (measurable_fract.comp (measurable_const.div measurable_id))
  have hgm:Measurable g:=
    measurable_const.sub (Finset.measurable_fun_sum _ fun k _=>measurable_const.mul (hfm k))
  have hgb: ∀ x∈Ioc (0:ℝ) 1, ‖g x‖ ≤1+ ∑ k, ‖cN ν ε N k‖ :=fun x _=>by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]
    refine add_le_add le_rfl ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _=>?_))
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_fract_le _)
  show ∫ x in Ioc (0:ℝ) 1, ‖g x‖ ^2<η
  rw [xT hgm hgb]
  set m:ℝ→ℝ:=fun ξ=>3*(F₁ ε ξ+
    16*(C₁*C₂*N^(-(ε/2)))^2*(1+ |2*π*ξ|)^(-(13/8:ℝ))+
    16*(C₁*(2* ε))^2*(1+ |2*π*ξ|)^(-(15/8:ℝ))) with hm
  have hpt: ∀ ξ:ℝ, ‖∫ x in Ioc (0:ℝ) 1,g x*(x:ℂ)^(aZ ξ-1)‖ ^2≤ m ξ:=by
    intro ξ
    have hre:(aZ ξ).re=1/2:=by simp [aZ]
    rw [Qt (cN ν ε N) (θN N) (XJ N) (LJ ν ε N hM)
      (by rw [hre]; norm_num) (by rw [hre]; norm_num),QX ν bC hN0 hM]
    set s:=aZ ξ
    set z:=riemannZeta s
    set X₁:ℂ:=1-z/riemannZeta (s+ε)
    set X₂:ℂ:=z*(D ν N (s+ε)-(riemannZeta (s+ε))⁻¹)
    set X₃:ℂ:=z*D ν N (1+ε)
    have halg:(1+z*(D ν N (1+ε)-D ν N (s+ε)))/s=X₁/s-X₂/s+X₃/s:=by
      simp only [X₁,X₂,X₃,div_eq_mul_inv]; ring
    have h2: ‖D ν N (s+ε)-(riemannZeta (s+ε))⁻¹‖ ≤
        C₂*N^(-(ε/2))*(1+ |2*π*ξ|)^(1/8:ℝ) :=by
      rw [xB]; exact hsm N hN1 (2*π*ξ)
    have hu:0<1+ |2*π*ξ| :=by positivity
    have hX₂: ‖X₂‖ ≤C₁*C₂*N^(-(ε/2))*(1+ |2*π*ξ|)^(3/16:ℝ) :=by
      rw [norm_mul]
      calc ‖z‖ * ‖D ν N (s+ε)-(riemannZeta (s+ε))⁻¹‖ ≤
            (C₁*(1+ |2*π*ξ|)^(1/16:ℝ))*
              (C₂*N^(-(ε/2))*(1+ |2*π*ξ|)^(1/8:ℝ)) :=
            mul_le_mul (Xc ξ) h2 (norm_nonneg _) (by positivity)
        _=C₁*C₂*N^(-(ε/2))*
              ((1+ |2*π*ξ|)^(1/16:ℝ)*(1+ |2*π*ξ|)^(1/8:ℝ)) :=by ring
        _=_:=by rw [← Real.rpow_add hu]; norm_num
    have hX₃: ‖X₃‖ ≤C₁*(2* ε)*(1+ |2*π*ξ|)^(1/16:ℝ) :=by
      rw [norm_mul]
      calc ‖z‖ * ‖D ν N (1+ε)‖ ≤(C₁*(1+ |2*π*ξ|)^(1/16:ℝ))*(2* ε) :=
            mul_le_mul (Xc ξ) hD1 (norm_nonneg _) (by positivity)
        _=_:=by ring
    have b₂:=Fh (ξ:=ξ) hX₂
    have b₃:=Fh (ξ:=ξ) hX₃
    rw [show 2*(3/16:ℝ)-2= -(13/8) by norm_num] at b₂
    rw [show 2*(1/16:ℝ)-2= -(15/8) by norm_num] at b₃
    rw [halg]
    refine (LL _ _ _).trans ?_
    simp only [hm,hF₁]
    gcongr
  have JL:Integrable (F₁ ε) :=
    ((jC (r:=3/2) (by norm_num)).const_mul (16*4^2)).mono'
      (Qy ε hε wW).aestronglyMeasurable (ae_of_all _ fun ξ=>by
        rw [Real.norm_of_nonneg (by positivity)]; exact NA ε hε (LO j) ξ)
  have hw₂:=(jC (r:=13/8) (by norm_num)).const_mul
    (16*(C₁*C₂*N^(-(ε/2)))^2)
  have hw₃:=(jC (r:=15/8) (by norm_num)).const_mul (16*(C₁*(2* ε))^2)
  have aaS:Integrable m:=((JL.add hw₂).add hw₃).const_mul 3
  have ZA: ∫ ξ,m ξ=3*((∫ ξ,F₁ ε ξ)+16*(C₁*C₂*N^(-(ε/2)))^2*J₂+
      16*(C₁*(2* ε))^2*J₃) :=by
    have e1:=integral_add (JL.add hw₂) hw₃
    have e2:=integral_add JL hw₂
    simp only [Pi.add_apply] at e1 e2
    simp only [hm]
    rw [integral_const_mul,e1,e2,integral_const_mul,integral_const_mul]
  calc (∫ ξ:ℝ, ‖∫ x in Ioc (0:ℝ) 1,g x*(x:ℂ)^(aZ ξ-1)‖ ^2)≤ ∫ ξ,m ξ:=
        integral_mono_of_nonneg (ae_of_all _ fun ξ=>by positivity) aaS (ae_of_all _ hpt)
    _<η:=by rw [ZA]; linarith
theorem tB (hRH:RiemannHypothesis) :
    ∀ η:ℝ,0<η→ ∃ (n:ℕ) (c:Fin n→ℂ) (θ:Fin n→ℝ),
      (∀ k,0<θ k ∧ θ k≤1) ∧ ∑ k,c k*(θ k:ℂ)=0 ∧
      ∫ x in Ioc (0:ℝ) 1, ‖1- ∑ k,c k*((Int.fract (θ k/x) :ℝ) :ℂ)‖ ^2<η:=by
  intro η hη
  obtain ⟨n,c,hsum,hint⟩:=nD hRH η hη
  refine ⟨n,c,fun k=>1/((k:ℝ)+1),fun k=>⟨by positivity,?_⟩,hsum,hint⟩
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg (k:ℕ) :(0:ℝ)≤k)]
end aF.Nyman.Converse
end
end

-- aF.acI
section
open Real MeasureTheory
open scoped ArithmeticFunction.sigma CompactlySupported Convolution ContDiff
noncomputable section
namespace aF.Rr
namespace RiemannHypothesis
section Aux
open Set Filter
abbrev Aw:Measure ℝ:=volume.restrict (Set.Ioc (0:ℝ) 1)
lemma Ie (s:Set ℝ) :Aw s≠ ⊤ :=
  ne_top_of_le_ne_top (measure_Ioc_lt_top (a:=(0:ℝ)) (b:=1)).ne
    (by rw [Measure.restrict_apply' measurableSet_Ioc]; exact measure_mono inter_subset_right)
def ind (θ:ℝ) :Lp ℝ 2 Aw:=indicatorConstLp 2 (measurableSet_Ioc (a:=(0:ℝ)) (b:=θ)) (Ie _) 1
def S:Set (Lp ℝ 2 (volume.restrict (Set.Ioc (0:ℝ) 1))) :=
  { fractScalarInvSumL2 n c θ | (n) (c) (θ)
      (hθ: ∀ ν,θ ν∈Set.Ioc 0 1) (h: ∑ ν,c ν*θ ν=0) }
lemma tD {n m:ℕ} (c θ:Fin n→ℝ) (d φ:Fin m→ℝ) :
    fractScalarInvSumL2 (n+m) (Fin.append c d) (Fin.append θ φ)=
      fractScalarInvSumL2 n c θ+fractScalarInvSumL2 m d φ:=by
  simp only [fractScalarInvSumL2,Fin.sum_univ_add,Fin.append_left,Fin.append_right]
lemma xG {n:ℕ} (a:ℝ) (c θ:Fin n→ℝ) :
    a•fractScalarInvSumL2 n c θ=fractScalarInvSumL2 n (fun ν=>a*c ν) θ:=by
  simp only [fractScalarInvSumL2,Finset.smul_sum,smul_smul]
def M:Submodule ℝ (Lp ℝ 2 Aw) where
  carrier:=S
  zero_mem':=⟨0,Fin.elim0,Fin.elim0,fun ν=>Fin.elim0 ν,by simp,by simp [fractScalarInvSumL2]⟩
  add_mem':=by
    rintro _ _ ⟨n,c,θ,hθ,h,rfl⟩ ⟨m,d,φ,hφ,h',rfl⟩
    refine ⟨n+m,Fin.append c d,Fin.append θ φ,fun ν=>?_,?_,tD c θ d φ⟩
    · refine Fin.addCases (fun i=>?_) (fun i=>?_) ν
      · rw [Fin.append_left]; exact hθ i
      · rw [Fin.append_right]; exact hφ i
    · rw [Fin.sum_univ_add]; simp only [Fin.append_left,Fin.append_right,h,h',add_zero]
  smul_mem':=by
    rintro a _ ⟨n,c,θ,hθ,h,rfl⟩
    refine ⟨n,fun ν=>a*c ν,θ,hθ,?_,(xG a c θ).symm⟩
    simp only [mul_assoc, ← Finset.mul_sum,h,mul_zero]
lemma vT {n:ℕ} (c θ:Fin n→ℝ) :
    ⇑(fractScalarInvSumL2 n c θ) =ᵐ[Aw] fun x=> ∑ ν,c ν* Int.fract (θ ν/x) :=by
  have hk: ∀ᵐ x ∂Aw, ∀ ν:Fin n,
      (c ν•(fractScalarInv_memLp2 (θ ν)).toLp (fractScalarInv (θ ν))) x=
        c ν* Int.fract (θ ν/x) :=
    ae_all_iff.2 fun ν=>by
      filter_upwards [Lp.coeFn_smul (c ν) ((fractScalarInv_memLp2 (θ ν)).toLp (fractScalarInv (θ ν))),
        (fractScalarInv_memLp2 (θ ν)).coeFn_toLp] with x h1 h2
      rw [h1,Pi.smul_apply,smul_eq_mul,h2]
      rfl
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun ν:Fin n=>c ν•(fractScalarInv_memLp2 (θ ν)).toLp (fractScalarInv (θ ν))),hk] with x h1 h2
  simp only [fractScalarInvSumL2]
  rw [h1]
  exact Finset.sum_congr rfl fun ν _=>h2 ν
lemma DQ (F:Lp ℝ 2 Aw) : ‖F‖ ^2= ∫ x in Ioc (0:ℝ) 1,(F x)^2:=by
  rw [← real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x=>?_)
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
lemma zF (θ₀:ℝ) {n:ℕ} (c θ:Fin n→ℝ) :
    ‖ind θ₀-fractScalarInvSumL2 n c θ‖ ^2=
      ∫ x in Ioc (0:ℝ) 1,((Ioc 0 θ₀).indicator (fun _=>(1:ℝ)) x-
        ∑ ν,c ν* Int.fract (θ ν/x))^2:=by
  rw [DQ]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (ind θ₀) (fractScalarInvSumL2 n c θ),vT c θ,
    indicatorConstLp_coeFn (p:=2) (μ:=Aw) (hs:=measurableSet_Ioc (a:=(0:ℝ)) (b:=θ₀))
      (hμs:=Ie _) (c:=(1:ℝ))] with x h1 h2 h3
  rw [h1,Pi.sub_apply,h2,show (ind θ₀) x=_ from h3]
lemma LQ {n:ℕ} (c θ:Fin n→ℝ) (hθ: ∀ ν,θ ν∈Ioc (0:ℝ) 1)
    (h: ∑ ν,c ν*θ ν=0) {θ₀:ℝ} (h0:0<θ₀) (h1:θ₀≤1) :
    ∫ x in Ioc (0:ℝ) 1,((Ioc 0 θ₀).indicator (fun _=>(1:ℝ)) x-
        ∑ ν,c ν* Int.fract ((θ ν*θ₀)/x))^2=
      θ₀* ∫ y in Ioc (0:ℝ) 1,(1- ∑ ν,c ν* Int.fract (θ ν/y))^2:=by
  set G:ℝ→ℝ:=fun y=>(1- ∑ ν,c ν* Int.fract (θ ν/y))^2 with hG
  set F:ℝ→ℝ:=fun x=>((Ioc 0 θ₀).indicator (fun _=>(1:ℝ)) x-
        ∑ ν,c ν* Int.fract ((θ ν*θ₀)/x))^2 with hF
  have key: ∀ x:ℝ,(Ioc (0:ℝ) 1).indicator F x=(Ioc (0:ℝ) 1).indicator G (x/θ₀) :=by
    intro x
    rcases le_or_gt x 0 with hx | hx
    · rw [indicator_of_notMem (fun hm=>by linarith [hm.1]),
        indicator_of_notMem (fun hm=>by
          have:x/θ₀≤0:=div_nonpos_of_nonpos_of_nonneg hx h0.le
          linarith [hm.1])]
    rcases le_or_gt x θ₀ with Qz | Qz
    · have hm:x∈Ioc (0:ℝ) 1:=⟨hx,Qz.trans h1⟩
      have hm':x/θ₀∈Ioc (0:ℝ) 1:=⟨div_pos hx h0,(div_le_one h0).2 Qz⟩
      rw [indicator_of_mem hm,indicator_of_mem hm']
      have e: ∀ ν,θ ν*θ₀/x=θ ν/(x/θ₀) :=fun ν=>by field_simp
      simp only [hF,hG,indicator_of_mem (show x∈Ioc 0 θ₀ from ⟨hx,Qz⟩),e]
    · have hm':x/θ₀∉Ioc (0:ℝ) 1:=fun hm=>by
        have:=hm.2; rw [div_le_one h0] at this; linarith
      rw [indicator_of_notMem hm']
      by_cases hm:x∈Ioc (0:ℝ) 1
      · rw [indicator_of_mem hm]
        simp only [hF,indicator_of_notMem (show x∉Ioc 0 θ₀ from fun h'=>by linarith [h'.2])]
        have hfr: ∀ ν,Int.fract ((θ ν*θ₀)/x)=(θ ν*θ₀)/x:=by
          intro ν
          rw [Int.fract_eq_self]
          refine ⟨div_nonneg (mul_nonneg (hθ ν).1.le h0.le) hx.le,?_⟩
          rw [div_lt_one hx]
          calc θ ν*θ₀≤1*θ₀:=mul_le_mul_of_nonneg_right (hθ ν).2 h0.le
            _=θ₀:=one_mul _
            _<x:=Qz
        simp only [hfr]
        have: ∑ ν,c ν*(θ ν*θ₀/x)=(θ₀/x)* ∑ ν,c ν*θ ν:=by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun ν _=>?_; ring
        rw [this,h]; ring
      · rw [indicator_of_notMem hm]
  rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
  refine (integral_congr_ae (Eventually.of_forall key)).trans ?_
  rw [Measure.integral_comp_div (fun y=>(Ioc (0:ℝ) 1).indicator G y) θ₀,abs_of_pos h0,
    smul_eq_mul]
lemma LV (hRH:_root_.RiemannHypothesis) {θ₀:ℝ} (h0:0<θ₀) (h1:θ₀≤1)
    {ε:ℝ} (hε:0<ε) : ∃ m∈M, ‖ind θ₀-m‖ <ε:=by
  obtain ⟨n,c,θ,hθ,hsum,hint⟩:=Nyman.Converse.tB hRH (ε^2) (by positivity)
  set c':Fin n→ℝ:=fun ν=>(c ν).re with hc'
  have hθ': ∀ ν,θ ν∈Ioc (0:ℝ) 1:=fun ν=>hθ ν
  have hsum': ∑ ν,c' ν*θ ν=0:=by
    have:=congrArg Complex.re hsum
    simp only [Complex.re_sum,Complex.re_mul_ofReal,Complex.zero_re] at this
    exact this
  have hbound: ∀ x:ℝ, ‖1- ∑ ν,c ν*((Int.fract (θ ν/x) :ℝ) :ℂ)‖ ≤1+ ∑ ν, ‖c ν‖ :=by
    intro x
    refine (norm_sub_le _ _).trans (add_le_add (by simp) ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _=>?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (Nyman.norm_fract_le _)
  have ZB:Measurable fun x:ℝ=> ‖1- ∑ ν,c ν*((Int.fract (θ ν/x) :ℝ) :ℂ)‖ ^2:=by
    refine (Measurable.norm (measurable_const.sub (Finset.measurable_fun_sum _ fun ν _=>
      measurable_const.mul (Complex.measurable_ofReal.comp
        (measurable_fract.comp (measurable_const.div measurable_id)))))).pow_const 2
  have aaT:IntegrableOn (fun x:ℝ=> ‖1- ∑ ν,c ν*((Int.fract (θ ν/x) :ℝ) :ℂ)‖ ^2)
      (Ioc (0:ℝ) 1) :=by
    refine Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne ZB.aestronglyMeasurable
      (M:=(1+ ∑ ν, ‖c ν‖)^2) (Eventually.of_forall fun x=>?_)
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2
  have hpt: ∀ x:ℝ,(1- ∑ ν,c' ν* Int.fract (θ ν/x))^2≤
      ‖1- ∑ ν,c ν*((Int.fract (θ ν/x) :ℝ) :ℂ)‖ ^2:=by
    intro x
    have hre:(1- ∑ ν,c ν*((Int.fract (θ ν/x) :ℝ) :ℂ)).re=1- ∑ ν,c' ν* Int.fract (θ ν/x) :=by
      simp only [Complex.sub_re,Complex.one_re,Complex.re_sum,Complex.re_mul_ofReal,hc']
    rw [← hre, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
  have hI: ∫ y in Ioc (0:ℝ) 1,(1- ∑ ν,c' ν* Int.fract (θ ν/y))^2<ε^2:=
    lt_of_le_of_lt (integral_mono_of_nonneg (Eventually.of_forall fun x=>by positivity) aaT
      (Eventually.of_forall hpt)) hint
  have hI0:0≤ ∫ y in Ioc (0:ℝ) 1,(1- ∑ ν,c' ν* Int.fract (θ ν/y))^2:=
    setIntegral_nonneg measurableSet_Ioc fun x _=>by positivity
  refine ⟨fractScalarInvSumL2 n c' (fun ν=>θ ν*θ₀),⟨n,c',fun ν=>θ ν*θ₀,fun ν=>?_,?_,rfl⟩,?_⟩
  · exact ⟨mul_pos (hθ' ν).1 h0,(mul_le_mul (hθ' ν).2 h1 h0.le zero_le_one).trans_eq (one_mul 1)⟩
  · simp only [← mul_assoc, ← Finset.sum_mul,hsum',zero_mul]
  · have hsq: ‖ind θ₀-fractScalarInvSumL2 n c' (fun ν=>θ ν*θ₀)‖ ^2<ε^2:=by
      rw [zF,LQ c' θ hθ' hsum' h0 h1]
      calc θ₀*_≤1*_:=mul_le_mul_of_nonneg_right h1 hI0
        _<ε^2:=by rw [one_mul]; exact hI
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq
lemma yQ {g:ℝ→ℝ} (hg:IntegrableOn g (Ioc 0 1))
    (h: ∀ θ∈Ioc (0:ℝ) 1, ∫ x in Ioc 0 θ,g x=0) :g =ᵐ[Aw] 0:=by
  set k:=(Ioc (0:ℝ) 1).indicator g with aaU
  have hk:Integrable k:=hg.integrable_indicator measurableSet_Ioc
  have hΦ: ∀ t:ℝ, ∫ x in (0:ℝ)..t,k x=0:=by
    intro t
    rcases le_or_gt t 0 with ht | ht
    · rw [intervalIntegral.integral_of_ge ht,neg_eq_zero]
      exact setIntegral_eq_zero_of_forall_eq_zero fun x hx=>
        indicator_of_notMem (fun hm=>by linarith [hm.1,hx.2]) _
    rcases le_or_gt t 1 with ht1 | ht1
    · rw [intervalIntegral.integral_of_le ht.le,
        setIntegral_congr_fun measurableSet_Ioc fun x hx=>indicator_of_mem (show x∈Ioc (0:ℝ) 1 from ⟨hx.1,hx.2.trans ht1⟩) g]
      exact h t ⟨ht,ht1⟩
    · rw [← intervalIntegral.integral_add_adjacent_intervals (b:=1) hk.intervalIntegrable
        hk.intervalIntegrable,intervalIntegral.integral_of_le zero_le_one,
        intervalIntegral.integral_of_le ht1.le,
        setIntegral_congr_fun measurableSet_Ioc fun x hx=>indicator_of_mem hx g,
        h 1 ⟨one_pos,le_rfl⟩,zero_add]
      exact setIntegral_eq_zero_of_forall_eq_zero fun x hx=>
        indicator_of_notMem (fun hm=>by linarith [hm.2,hx.1]) _
  have Pw: ∫ x,k x=0:=by
    rw [aaU,integral_indicator measurableSet_Ioc]
    exact h 1 ⟨one_pos,le_rfl⟩
  have hall: ∀ s,MeasurableSet s→ ∫ x in s,k x=0:=by
    refine MeasurableSpace.induction_on_inter (C:=fun s _=> ∫ x in s,k x=0)
      (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioc ℝ))
      (by simpa using isPiSystem_Ioc (id:ℝ→ℝ) id) (by simp) ?_ ?_ ?_
    · rintro _ ⟨l,u,hlu,rfl⟩
      rw [← intervalIntegral.integral_of_le hlu.le,
        ← intervalIntegral.integral_interval_sub_left (a:=0) hk.intervalIntegrable hk.intervalIntegrable,
        hΦ,hΦ,sub_zero]
    · intro t ht hzero
      rw [setIntegral_compl ht hk,Pw,hzero,sub_zero]
    · intro f hd hfm hf
      rw [integral_iUnion hfm hd hk.integrableOn]
      simp [hf]
  have hk0:k =ᵐ[volume] 0:=hk.ae_eq_zero_of_forall_setIntegral_eq_zero fun s hs _=>hall s hs
  refine (ae_restrict_iff' measurableSet_Ioc).2 (hk0.mono fun x hx hxm=>?_)
  rw [Pi.zero_apply, ← indicator_of_mem hxm g]
  exact hx
lemma GD (hRH:_root_.RiemannHypothesis) :Mᗮ= ⊥ :=by
  rw [Submodule.eq_bot_iff]
  intro g hg
  have hind: ∀ θ∈Ioc (0:ℝ) 1,inner ℝ (ind θ) g=0:=by
    intro θ hθ
    by_contra hne
    set a:= |inner ℝ (ind θ) g| with ha_def
    have ha:0<a:=abs_pos.2 hne
    obtain ⟨m,hm,hd⟩:=LV hRH hθ.1 hθ.2 (ε:=a/(‖g‖ +1)) (by positivity)
    have h0:inner ℝ m g=0:=Submodule.inner_right_of_mem_orthogonal hm hg
    have he:inner ℝ (ind θ) g=inner ℝ (ind θ-m) g:=by rw [inner_sub_left,h0,sub_zero]
    have hle:a≤ ‖ind θ-m‖ * ‖g‖ :=by
      rw [ha_def,he]; exact abs_real_inner_le_norm _ _
    have hlt: ‖ind θ-m‖ * ‖g‖ <a:=by
      calc ‖ind θ-m‖ * ‖g‖ ≤(a/(‖g‖ +1))* ‖g‖ :=mul_le_mul_of_nonneg_right hd.le (norm_nonneg _)
        _<a:=by
          rw [div_mul_eq_mul_div,div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg g]
    linarith
  have hint:Integrable (⇑g) Aw:=(Lp.memLp g).integrable one_le_two
  have hzero: ∀ θ∈Ioc (0:ℝ) 1, ∫ x in Ioc 0 θ,g x=0:=by
    intro θ hθ
    have:=hind θ hθ
    rw [ind,MeasureTheory.L2.inner_indicatorConstLp_one,Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.2 (Ioc_subset_Ioc_right hθ.2)] at this
    exact this
  exact Lp.eq_zero_iff_ae_eq_zero.2 (yQ hint hzero)
lemma tJ (hD:Dense S) :_root_.RiemannHypothesis:=by
  refine Nyman.rS fun ε hε=>?_
  obtain ⟨_,hball,⟨n,c,θ,hθ,h,rfl⟩⟩:=
    Metric.dense_iff.1 hD (ind 1) (Real.sqrt ε) (Real.sqrt_pos.2 hε)
  refine ⟨n,fun ν=>(c ν:ℂ),θ,fun ν=>hθ ν,?_,?_⟩
  · have:=congrArg (fun r:ℝ=>(r:ℂ)) h
    push_cast at this
    exact this
  · have hn: ‖ind 1-fractScalarInvSumL2 n c θ‖ ^2<ε:=by
      rw [Metric.mem_ball,dist_eq_norm,norm_sub_rev] at hball
      calc ‖ind 1-fractScalarInvSumL2 n c θ‖ ^2<Real.sqrt ε^2:=
            pow_lt_pow_left₀ hball (norm_nonneg _) two_ne_zero
        _=ε:=Real.sq_sqrt hε.le
    rw [zF] at hn
    refine lt_of_eq_of_lt ?_ hn
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx=>?_
    simp only
    rw [indicator_of_mem hx]
    have e:(1:ℂ)- ∑ ν,(c ν:ℂ)*((Int.fract (θ ν/x) :ℝ) :ℂ)=
        ((1- ∑ ν,c ν* Int.fract (θ ν/x) :ℝ) :ℂ) :=by push_cast; rfl
    rw [e,Complex.norm_real,Real.norm_eq_abs,sq_abs]
end Aux
theorem beurling_nyman_criterion:RiemannHypothesis↔
    Dense { fractScalarInvSumL2 n c θ | (n) (c) (θ)
      (hθ: ∀ ν,θ ν∈Set.Ioc 0 1) (h: ∑ ν,c ν*θ ν=0) } :=by
  constructor
  · intro hRH
    change Dense (M:Set (Lp ℝ 2 Aw))
    rw [Submodule.dense_iff_topologicalClosure_eq_top,Submodule.topologicalClosure_eq_top_iff]
    exact GD hRH
  · exact tJ
end RiemannHypothesis
end aF.Rr
end
end

theorem OMA.solution:type_of% @RiemannHypothesis.beurling_nyman_criterion:=
  aF.Rr.RiemannHypothesis.beurling_nyman_criterion
