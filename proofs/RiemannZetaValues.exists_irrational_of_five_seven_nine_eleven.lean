import FormalConjectures.Wikipedia.RiemannZetaValues
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Contracting

/-! Proof of Zudilin (2001): at least one of zeta(5), zeta(7), zeta(9), zeta(11) is irrational. -/

namespace Z1
open scoped Real
open Complex Filter Topology MeasureTheory Finset
private noncomputable def Phi (s:ℂ):ℂ:=
 -deriv (DirichletCharacter.LFunctionTrivChar₁ 1) s/DirichletCharacter.LFunctionTrivChar₁ 1 s
private noncomputable def G_fun (z:ℂ):ℂ:=
 (Phi (z+1)-1)/(z+1)
private def U_dom:Set ℂ:=
 {z:ℂ | DirichletCharacter.LFunctionTrivChar₁ 1 (z+1)≠0∧z+1≠0}
private lemma z118:IsOpen U_dom:=by
 have hcont:Continuous (fun z:ℂ=>DirichletCharacter.LFunctionTrivChar₁ 1 (z+1)):=
  (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).continuous.comp
   (continuous_id.add continuous_const)
 exact (isOpen_ne.preimage hcont).inter (isOpen_ne.preimage (continuous_id.add continuous_const))
private lemma z248:{z:ℂ | 0 ≤ z.re} ⊆ U_dom:=by
 intro z hz
 simp only [Set.mem_ofPred_eq] at hz
 have hre:1 ≤ (z+1).re:=by simp [hz]
 have hs0:z+1≠0:=by
  intro h
  have:(z+1).re=0:=by rw [h];simp
  linarith
 refine ⟨?_,hs0⟩
 rcases eq_or_ne (z+1) 1 with h1 | h1
 ·
  rw [h1]
  exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1
 ·
  rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne h1,
   DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq]
  exact mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hre)
private lemma z68:DifferentiableOn ℂ G_fun U_dom:=by
 have hL:Differentiable ℂ (DirichletCharacter.LFunctionTrivChar₁ 1):=
  DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
 have hdL:Differentiable ℂ (deriv (DirichletCharacter.LFunctionTrivChar₁ 1)):=
  hL.deriv
 intro z hz
 refine DifferentiableAt.differentiableWithinAt ?_
 have hadd:DifferentiableAt ℂ (fun w:ℂ=>w+1) z:=differentiableAt_id.add (differentiableAt_const 1)
 have hPhi:DifferentiableAt ℂ (fun w:ℂ=>Phi (w+1)) z:=by
  unfold Phi
  have h1:DifferentiableAt ℂ (fun w:ℂ=>deriv (DirichletCharacter.LFunctionTrivChar₁ 1) (w+1)) z:=
   ((hdL (z+1)).hasDerivAt.comp_add_const z 1).differentiableAt
  have h2:DifferentiableAt ℂ (fun w:ℂ=>DirichletCharacter.LFunctionTrivChar₁ 1 (w+1)) z:=
   ((hL (z+1)).hasDerivAt.comp_add_const z 1).differentiableAt
  exact h1.neg.div h2 hz.1
 exact (hPhi.sub (differentiableAt_const 1)).div hadd hz.2
private lemma z8 {z:ℂ} (hz:0< z.re) :
  G_fun z=LSeries (fun n=>(ArithmeticFunction.vonMangoldt n:ℂ)) (z+1)/(z+1)-1/z:=by
 have hs_re:1< (z+1).re:=by simp [hz]
 have hs1:z+1≠1:=by
  intro h
  have:(z+1).re=1:=by rw [h];simp
  linarith
 have hs0:z+1≠0:=by
  intro h
  have:(z+1).re=0:=by rw [h];simp
  linarith
 have hz0:z≠0:=by
  intro h
  rw [h] at hz
  simp at hz
 have hzeta:riemannZeta (z+1)≠0:=riemannZeta_ne_zero_of_one_le_re hs_re.le
 have hLmod:DirichletCharacter.LFunctionTrivChar 1=riemannZeta:=
  DirichletCharacter.LFunction_modOne_eq
 have hPhi:Phi (z+1)=LSeries (fun n=>(ArithmeticFunction.vonMangoldt n:ℂ)) (z+1)-1/z:=by
  unfold Phi
  rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hs1,
   DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hs1,
   hLmod,ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs_re]
  have hsub:z+1-1=z:=add_sub_cancel_right z 1
  rw [hsub]
  field_simp [hz0,hzeta]
  ring
 unfold G_fun
 rw [hPhi]
 field_simp [hs0,hz0]
 ring
private noncomputable def f_psi (t:ℝ):ℝ:=
 Real.exp (-t)*Chebyshev.psi (Real.exp t)-1
private lemma z79:Measurable f_psi:=by
 unfold f_psi
 exact ((Real.continuous_exp.comp continuous_neg).measurable.mul
  (Chebyshev.psi_mono.measurable.comp Real.continuous_exp.measurable)).sub measurable_const
private lemma z77 {t:ℝ}:|f_psi t| ≤ Real.log 4+4:=by
 unfold f_psi
 have h0:0 ≤ Real.exp (-t)*Chebyshev.psi (Real.exp t):=
  mul_nonneg (Real.exp_nonneg _) (Chebyshev.psi_nonneg _)
 have h1:Real.exp (-t)*Chebyshev.psi (Real.exp t) ≤ Real.log 4+4:=by
  have hpsi:=Chebyshev.psi_le_const_mul_self (Real.exp_nonneg t)
  calc
   Real.exp (-t)*Chebyshev.psi (Real.exp t)
    ≤ Real.exp (-t)*((Real.log 4+4)*Real.exp t):=by
     gcongr
   _=Real.log 4+4:=by
     rw [mul_left_comm,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
 have hlog:0 ≤ Real.log 4:=Real.log_nonneg (by norm_num)
 rw [abs_le]
 constructor <;> linarith
private lemma z104 {z:ℂ} (hz:0< z.re) (a:ℝ) :
  IntegrableOn (fun t:ℝ=>Complex.exp (-z*(t:ℂ))) (Set.Ioi a) volume:=by
 have hmeas:AEStronglyMeasurable (fun t:ℝ=>Complex.exp (-z*(t:ℂ)))
   (volume.restrict (Set.Ioi a)):=
  (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
 have hnorm:∀ t:ℝ,‖Complex.exp (-z*(t:ℂ))‖=Real.exp ((-z.re)*t):=fun t=>by
  rw [Complex.norm_exp]
  simp
 have hint:IntegrableOn (fun t:ℝ=>Real.exp ((-z.re)*t)) (Set.Ioi a) volume:=
  integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hz) a
 exact hint.mono' hmeas (Filter.Eventually.of_forall fun t=>by rw [hnorm])
private lemma z108 {z:ℂ} (hz:0< z.re) (a:ℝ) :
  ∫ t in Set.Ioi a,Complex.exp (-z*(t:ℂ))=Complex.exp (-z*(a:ℂ))/z:=by
 have hz0:z≠0:=by
  intro h
  rw [h] at hz
  simp at hz
 have hderiv:∀ t∈Set.Ici a,
   HasDerivAt (fun x:ℝ=>-Complex.exp (-z*(x:ℂ))/z) (Complex.exp (-z*(t:ℂ))) t:=by
  intro t _
  have h1:HasDerivAt (fun x:ℝ=>-z*(x:ℂ)) (-z) t:=by
   simpa using (Complex.ofRealCLM.hasDerivAt (x:=t)).const_mul (-z)
  have h2:HasDerivAt (fun x:ℝ=>Complex.exp (-z*(x:ℂ)))
    (Complex.exp (-z*(t:ℂ))*(-z)) t:=h1.cexp
  have h3:HasDerivAt (fun x:ℝ=>-Complex.exp (-z*(x:ℂ))/z)
    (-(Complex.exp (-z*(t:ℂ))*(-z))/z) t:=(h2.neg).div_const z
  have h4:-(Complex.exp (-z*(t:ℂ))*(-z))/z=Complex.exp (-z*(t:ℂ)):=by
   rw [mul_neg,neg_neg,mul_div_cancel_right₀ _ hz0]
  exact h4 ▸ h3
 have htend:Tendsto (fun x:ℝ=>-Complex.exp (-z*(x:ℂ))/z) atTop (𝓝 0):=by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm:(fun x:ℝ=>‖-Complex.exp (-z*(x:ℂ))/z‖) =
    fun x:ℝ=>Real.exp ((-z.re)*x) / ‖z‖:=by
   ext x
   rw [norm_div,norm_neg,Complex.norm_exp]
   simp
  rw [hnorm]
  have hexp:Tendsto (fun x:ℝ=>Real.exp ((-z.re)*x)) atTop (𝓝 0):=
   Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hz) tendsto_id)
  simpa using hexp.div_const ‖z‖
 rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (z104 hz a) htend]
 ring
private lemma z114 {s:ℂ} (hs:1< s.re) :
  ∫ t in Set.Ioi (0:ℝ),(Chebyshev.psi (Real.exp t):ℂ)*Complex.exp (-s*(t:ℂ)) =
   LSeries (fun n=>(ArithmeticFunction.vonMangoldt n:ℂ)) s/s:=by
 have hs0:0< s.re:=zero_lt_one.trans hs
 have hs_ne:s≠0:=by
  intro h;rw [h] at hs0;simp at hs0
 let u:ℕ→ ℝ→ ℂ:=fun n t =>
  if 1 ≤ n∧Real.log n ≤ t then (ArithmeticFunction.vonMangoldt n:ℂ)*Complex.exp (-s*(t:ℂ))
  else 0
 have hu_eq:∀ n:ℕ,1 ≤ n →
   ∀ᵐ t ∂(volume.restrict (Set.Ioi (0:ℝ))),
    u n t=(Set.Ioi (Real.log n)).indicator
     (fun t=>(ArithmeticFunction.vonMangoldt n:ℂ)*Complex.exp (-s*(t:ℂ))) t:=by
  intro n hn
  have hlog_nonneg:0 ≤ Real.log (n:ℝ):=Real.log_nonneg (Nat.one_le_cast.mpr hn)
  have hne:∀ᵐ t ∂(volume.restrict (Set.Ioi (0:ℝ))),t≠Real.log n:=by
   refine ae_restrict_of_ae ?_
   rw [ae_iff]
   simp
  filter_upwards [ae_restrict_mem measurableSet_Ioi,hne] with t ht htn
  simp only [u,hn,true_and,Set.indicator,Set.mem_Ioi]
  by_cases hlt:Real.log n< t
  ·
   simp [hlt,hlt.le]
  ·
   have hle:¬ Real.log n ≤ t:=fun h=>hlt (lt_of_le_of_ne h htn.symm)
   simp [hlt,hle]
 have hu_int:∀ n:ℕ,Integrable (u n) (volume.restrict (Set.Ioi (0:ℝ))):=by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
   have hu0:u 0=0:=by ext t;simp [u]
   rw [hu0]
   exact integrable_zero _ _ _
  ·
   have h1:IntegrableOn (fun t:ℝ=>(ArithmeticFunction.vonMangoldt n:ℂ)*Complex.exp (-s*(t:ℂ)))
     (Set.Ioi (Real.log n)) volume:=
    (z104 hs0 (Real.log n)).const_mul _
   have h2:Integrable ((Set.Ioi (Real.log n)).indicator
     (fun t:ℝ=>(ArithmeticFunction.vonMangoldt n:ℂ)*Complex.exp (-s*(t:ℂ))))
     (volume.restrict (Set.Ioi (0:ℝ))):=
    (h1.integrable_indicator measurableSet_Ioi).restrict
   exact h2.congr (Filter.EventuallyEq.symm (hu_eq n hn))
 have hu_integral:∀ n:ℕ,
   ∫ t in Set.Ioi (0:ℝ),u n t =
    LSeries.term (fun n=>(ArithmeticFunction.vonMangoldt n:ℂ)) s n/s:=by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
   simp [u]
  ·
   have hlog_nonneg:0 ≤ Real.log (n:ℝ):=Real.log_nonneg (Nat.one_le_cast.mpr hn)
   have hsub:Set.Ioi (Real.log n) ⊆ Set.Ioi (0:ℝ):=Set.Ioi_subset_Ioi hlog_nonneg
   rw [integral_congr_ae (hu_eq n hn),integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,Set.inter_eq_self_of_subset_left hsub,
    integral_const_mul,z108 hs0 (Real.log n)]
   rw [LSeries.term_of_ne_zero hn.ne']
   have hcpow:Complex.exp (-s*(Real.log (n:ℝ):ℂ))=((n:ℂ)^s)⁻¹:=by
    have hn_pos:(0:ℝ)< (n:ℝ):=Nat.cast_pos.mpr hn
    rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn.ne'),← Complex.exp_neg,
     ← Complex.ofReal_natCast,← Complex.ofReal_log hn_pos.le]
    congr 1
    ring
   rw [hcpow]
   simp [div_eq_mul_inv,mul_assoc,mul_comm]
 have hu_norm_integral:∀ n:ℕ,
   ∫ t in Set.Ioi (0:ℝ),‖u n t‖ =
    ‖LSeries.term (fun n=>(ArithmeticFunction.vonMangoldt n:ℂ)) s n‖ / s.re:=by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
   simp [u]
  ·
   have hlog_nonneg:0 ≤ Real.log (n:ℝ):=Real.log_nonneg (Nat.one_le_cast.mpr hn)
   have hsub:Set.Ioi (Real.log n) ⊆ Set.Ioi (0:ℝ):=Set.Ioi_subset_Ioi hlog_nonneg
   have hnorm_ae:(fun t=>‖u n t‖) =ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
     (Set.Ioi (Real.log n)).indicator
      (fun t=>ArithmeticFunction.vonMangoldt n*Real.exp ((-s.re)*t)):=by
    filter_upwards [hu_eq n hn] with t ht
    rw [ht]
    by_cases hmem:t∈Set.Ioi (Real.log n)
    ·
     simp only [Set.indicator_of_mem hmem,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,Complex.norm_exp]
     simp
    ·
     simp [Set.indicator_of_notMem hmem]
   rw [integral_congr_ae hnorm_ae,integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,Set.inter_eq_self_of_subset_left hsub,
    integral_const_mul]
   have hreal_int:∫ t in Set.Ioi (Real.log (n:ℝ)),Real.exp ((-s.re)*t) =
     Real.exp ((-s.re)*Real.log (n:ℝ))/s.re:=by
    have h:=congrArg Complex.re (z108 (z:=(s.re:ℂ)) (by simpa using hs0) (Real.log n))
    have hre_int:(∫ t in Set.Ioi (Real.log (n:ℝ)),Complex.exp (-(s.re:ℂ)*(t:ℂ))).re =
      ∫ t in Set.Ioi (Real.log (n:ℝ)),Real.exp ((-s.re)*t):=by
     have hc:=Complex.reCLM.integral_comp_comm (z104 (z:=(s.re:ℂ)) (by simpa using hs0) (Real.log n))
     have h1:(∫ t in Set.Ioi (Real.log (n:ℝ)),Complex.reCLM (Complex.exp (-(s.re:ℂ)*(t:ℂ)))) =
       ∫ t in Set.Ioi (Real.log (n:ℝ)),Real.exp ((-s.re)*t):=by
      congr 1 with t
      rw [Complex.reCLM_apply,
       show -(s.re:ℂ)*(t:ℂ)=(((-s.re)*t:ℝ):ℂ) by push_cast;ring,
       ← Complex.ofReal_exp,Complex.ofReal_re]
     rw [← h1,hc,Complex.reCLM_apply]
    rw [hre_int] at h
    rw [h,show -(s.re:ℂ)*(Real.log (n:ℝ):ℂ)=(((-s.re)*Real.log (n:ℝ):ℝ):ℂ) by
     push_cast;ring,← Complex.ofReal_exp,← Complex.ofReal_div,Complex.ofReal_re]
   rw [hreal_int,LSeries.term_of_ne_zero hn.ne',norm_div,Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    Complex.norm_natCast_cpow_of_re_ne_zero n hs0.ne']
   have hn_pos:(0:ℝ)< (n:ℝ):=Nat.cast_pos.mpr hn
   rw [show Real.exp ((-s.re)*Real.log (n:ℝ))=((n:ℝ)^s.re)⁻¹ by
    rw [Real.rpow_def_of_pos hn_pos,← Real.exp_neg];congr 1;ring]
   ring
 have hsum_norm:Summable (fun n:ℕ=>∫ t in Set.Ioi (0:ℝ),‖u n t‖):=by
  simp_rw [hu_norm_integral]
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm.div_const s.re
 have htsum_eq:=integral_tsum_of_summable_integral_norm hu_int hsum_norm
 have hpt:∀ t∈Set.Ioi (0:ℝ),
   ∑' n:ℕ,u n t=(Chebyshev.psi (Real.exp t):ℂ)*Complex.exp (-s*(t:ℂ)):=by
  intro t ht
  have hsupp:∀ n:ℕ,n∉Ioc 0 ⌊Real.exp t⌋₊→ u n t=0:=by
   intro n hn
   simp only [u,ite_eq_right_iff]
   intro ⟨hn1,hlog⟩
   exfalso
   apply hn
   rw [mem_Ioc]
   refine ⟨hn1,Nat.le_floor ?_⟩
   have hnpos:(0:ℝ)< (n:ℝ):=Nat.cast_pos.mpr hn1
   rwa [← Real.log_le_iff_le_exp hnpos]
  rw [tsum_eq_sum hsupp]
  have hsum_eq:∑ n∈Ioc 0 ⌊Real.exp t⌋₊,u n t =
    ∑ n∈Ioc 0 ⌊Real.exp t⌋₊,(ArithmeticFunction.vonMangoldt n:ℂ)*Complex.exp (-s*(t:ℂ)):=by
   refine sum_congr rfl fun n hn=>?_
   rw [mem_Ioc] at hn
   have hlog:Real.log (n:ℝ) ≤ t:=by
    rw [Real.log_le_iff_le_exp (Nat.cast_pos.mpr hn.1)]
    exact (Nat.le_floor_iff (Real.exp_nonneg t)).mp hn.2
   have hcond:1 ≤ n∧Real.log (n:ℝ) ≤ t:=⟨hn.1,hlog⟩
   simp only [u,hcond,and_self,↓reduceIte]
  rw [hsum_eq,← sum_mul,Chebyshev.psi]
  simp
 have hcongr:∫ t in Set.Ioi (0:ℝ),∑' n:ℕ,u n t =
   ∫ t in Set.Ioi (0:ℝ),(Chebyshev.psi (Real.exp t):ℂ)*Complex.exp (-s*(t:ℂ)):=by
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht=>hpt t ht
 rw [← hcongr,← htsum_eq]
 simp_rw [hu_integral,tsum_div_const]
 rfl
private lemma z9 {z:ℂ} (hz:0< z.re) :
  G_fun z=∫ t in Set.Ioi (0:ℝ),(f_psi t:ℂ)*Complex.exp (-z*(t:ℂ)):=by
 have hs:1< (z+1).re:=by simp [hz]
 rw [z8 hz,← z114 hs]
 have h1:IntegrableOn (fun t:ℝ=>(Chebyshev.psi (Real.exp t):ℂ)*Complex.exp (-(z+1)*(t:ℂ)))
   (Set.Ioi (0:ℝ)) volume:=by
  have hmeas:AEStronglyMeasurable
    (fun t:ℝ=>(Chebyshev.psi (Real.exp t):ℂ)*Complex.exp (-(z+1)*(t:ℂ)))
    (volume.restrict (Set.Ioi (0:ℝ))):=
   ((Complex.continuous_ofReal.measurable.comp
    (Chebyshev.psi_mono.measurable.comp Real.continuous_exp.measurable)).mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable).aestronglyMeasurable
  have hdom:IntegrableOn (fun t:ℝ=>(Real.log 4+4)*Real.exp ((-z.re)*t)) (Set.Ioi (0:ℝ)) volume:=
   (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hz) 0).const_mul _
  refine hdom.mono' hmeas (Filter.Eventually.of_forall fun t=>?_)
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Chebyshev.psi_nonneg _),Complex.norm_exp]
  have hre:(-(z+1)*(t:ℂ)).re=(-z.re)*t-t:=by simp;ring
  rw [hre,Real.exp_sub]
  calc
   Chebyshev.psi (Real.exp t)*(Real.exp ((-z.re)*t)/Real.exp t)
    = (Chebyshev.psi (Real.exp t)/Real.exp t)*Real.exp ((-z.re)*t):=by ring
   _ ≤ (Real.log 4+4)*Real.exp ((-z.re)*t):=by
     gcongr
     rw [div_le_iff₀ (Real.exp_pos t)]
     exact Chebyshev.psi_le_const_mul_self (Real.exp_nonneg t)
 have h2:IntegrableOn (fun t:ℝ=>Complex.exp (-z*(t:ℂ))) (Set.Ioi (0:ℝ)) volume:=
  z104 hz 0
 have h2val:∫ t in Set.Ioi (0:ℝ),Complex.exp (-z*(t:ℂ))=1/z:=by
  simpa using z108 hz 0
 rw [← h2val,← integral_sub h1 h2]
 refine setIntegral_congr_fun measurableSet_Ioi fun t _=>?_
 simp only [f_psi,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg,
  Complex.ofReal_one,sub_mul,one_mul]
 congr 1
 rw [mul_comm (Complex.exp (-(t:ℂ))),mul_assoc,← Complex.exp_add]
 congr 2
 ring
private noncomputable def z119 (f:ℝ→ ℝ) (T:ℝ) (z:ℂ):ℂ:=
 ∫ t in (0:ℝ)..T,(f t:ℂ)*Complex.exp (-z*(t:ℂ))
private lemma z69 {f:ℝ→ ℝ} {B:ℝ} (hB:0< B)
  (hf_meas:Measurable f) (hf_bound:∀ t ≥ 0,|f t| ≤ B) {T:ℝ} (hT:0 ≤ T) :
  Differentiable ℂ (z119 f T):=by
 intro z₀
 let F:ℂ→ ℝ→ ℂ:=fun z t=>(f t:ℂ)*Complex.exp (-z*(t:ℂ))
 let F':ℂ→ ℝ→ ℂ:=fun z t=>-(t:ℂ)*(f t:ℂ)*Complex.exp (-z*(t:ℂ))
 let s:Set ℂ:=Metric.ball z₀ 1
 let bound:ℝ→ ℝ:=fun _=>T*B*Real.exp ((‖z₀‖+1)*T)
 have hs:s∈𝓝 z₀:=Metric.ball_mem_nhds z₀ one_pos
 have hF_meas:∀ z:ℂ,AEStronglyMeasurable (F z) (volume.restrict (Set.uIoc 0 T)):=fun z =>
  ((Complex.continuous_ofReal.measurable.comp hf_meas).mul
   (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable).aestronglyMeasurable
 have hF_int:IntervalIntegrable (F z₀) volume 0 T:=by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  have hdom:IntegrableOn (fun _:ℝ=>B*Real.exp (‖z₀‖*T)) (Set.Ioc 0 T) volume:=
   integrableOn_const (by simp)
  refine hdom.mono' (by simpa [Set.uIoc_of_le hT] using hF_meas z₀) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simp only [F,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp]
  have hre:(-z₀*(t:ℂ)).re ≤ ‖z₀‖*T:=by
   have:(-z₀*(t:ℂ)).re=-z₀.re*t:=by simp
   rw [this]
   calc
    -z₀.re*t ≤ |z₀.re| * t:=mul_le_mul_of_nonneg_right (neg_le_abs z₀.re) ht.1.le
    _ ≤ ‖z₀‖*t:=mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z₀) ht.1.le
    _ ≤ ‖z₀‖*T:=mul_le_mul_of_nonneg_left ht.2 (norm_nonneg z₀)
  exact mul_le_mul (hf_bound t ht.1.le) (Real.exp_le_exp.mpr hre) (Real.exp_nonneg _) hB.le
 have hF'_meas:AEStronglyMeasurable (F' z₀) (volume.restrict (Set.uIoc 0 T)):=
  (((Complex.continuous_ofReal.measurable.neg).mul (Complex.continuous_ofReal.measurable.comp hf_meas)).mul
   (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable).aestronglyMeasurable
 have h_bound:∀ᵐ t ∂volume,t∈Set.uIoc 0 T→ ∀ z∈s,‖F' z t‖ ≤ bound t:=by
  refine Filter.Eventually.of_forall fun t ht z hz=>?_
  rw [Set.uIoc_of_le hT] at ht
  have hz_norm:‖z‖ ≤ ‖z₀‖+1:=by
   have:‖z-z₀‖ < 1:=by simpa [Complex.dist_eq] using Metric.mem_ball.mp hz
   have htri:=norm_add_le (z-z₀) z₀
   simp only [sub_add_cancel] at htri
   linarith
  simp only [F',bound,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
   abs_of_pos ht.1,Complex.norm_exp]
  have hre:(-z*(t:ℂ)).re ≤ (‖z₀‖+1)*T:=by
   have:(-z*(t:ℂ)).re=-z.re*t:=by simp
   rw [this]
   calc
    -z.re*t ≤ |z.re| * t:=mul_le_mul_of_nonneg_right (neg_le_abs z.re) ht.1.le
    _ ≤ ‖z‖*t:=mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) ht.1.le
    _ ≤ (‖z₀‖+1)*T:=mul_le_mul hz_norm ht.2 ht.1.le (by positivity)
  have h1:t * |f t| ≤ T*B:=mul_le_mul ht.2 (hf_bound t ht.1.le) (abs_nonneg _) hT
  exact mul_le_mul h1 (Real.exp_le_exp.mpr hre) (Real.exp_nonneg _) (mul_nonneg hT hB.le)
 have h_diff:∀ᵐ t ∂volume,t∈Set.uIoc 0 T→ ∀ z∈s,HasDerivAt (fun w=>F w t) (F' z t) z:=by
  refine Filter.Eventually.of_forall fun t _ z _=>?_
  have h1:HasDerivAt (fun w:ℂ=>-w*(t:ℂ)) (-(t:ℂ)) z:=by
   simpa using (hasDerivAt_id z).neg.mul_const (t:ℂ)
  have h2:HasDerivAt (fun w:ℂ=>(f t:ℂ)*Complex.exp (-w*(t:ℂ)))
    ((f t:ℂ)*(Complex.exp (-z*(t:ℂ))*-(t:ℂ))) z:=h1.cexp.const_mul _
  convert h2 using 1
  simp only [F']
  ring
 exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
  (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas h_bound intervalIntegrable_const h_diff).2.differentiableAt
private lemma z71 {U:Set ℂ} (hU_open:IsOpen U)
  (hU_sub:{z:ℂ | 0 ≤ z.re} ⊆ U) {R:ℝ} (hR:0< R) :
  ∃ δ > 0,(Set.Icc (-δ) R) ×ℂ (Set.Icc (-R) R) ⊆ U:=by
 let K:Set ℂ:=Set.Icc (0:ℝ) R ×ℂ Set.Icc (-R) R
 have hK_compact:IsCompact K:=isCompact_Icc.reProdIm isCompact_Icc
 have hK_sub:K ⊆ U:=fun z hz=>hU_sub hz.1.1
 obtain ⟨δ,hδ_pos,hδ_sub⟩:=hK_compact.exists_thickening_subset_open hU_open hK_sub
 refine ⟨δ / 2,half_pos hδ_pos,fun z hz=>hδ_sub ?_⟩
 rw [Metric.mem_thickening_iff]
 rcases le_or_gt 0 z.re with hre | hre
 ·
  exact ⟨z,⟨⟨hre,hz.1.2⟩,hz.2⟩,by simp [hδ_pos]⟩
 ·
  refine ⟨(z.im:ℂ)*I,?_,?_⟩
  ·
   refine ⟨?_,?_⟩
   ·
    simp [hR.le]
   ·
    simpa using hz.2
  ·
   rw [Complex.dist_eq]
   have hsub:z-(z.im:ℂ)*I=(z.re:ℂ):=by
    apply Complex.ext <;> simp
   rw [hsub,Complex.norm_real,Real.norm_eq_abs,abs_of_neg hre]
   linarith [hz.1.1]
private lemma z46 (R θ : ℝ) (hR:0< R) :
  (I*(R*Complex.exp ((θ : ℂ)*I))) *
   (1/(R*Complex.exp ((θ : ℂ)*I))+(R*Complex.exp ((θ : ℂ)*I))/(R:ℂ)^2) =
  I*Complex.exp ((θ : ℂ)*I)*(2*(Real.cos θ : ℂ)):=by
 have hR0:(R:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hR.ne'
 have hexp0:Complex.exp ((θ : ℂ)*I)≠0:=Complex.exp_ne_zero _
 have hcos:(2:ℂ)*(Real.cos θ : ℂ)=Complex.exp ((θ : ℂ)*I)+Complex.exp (-((θ : ℂ)*I)):=by
  rw [Complex.ofReal_cos,Complex.cos]
  have:-((θ : ℂ)*I)=-(θ : ℂ)*I:=by ring
  rw [this]
  ring
 rw [hcos]
 field_simp [hR0,hexp0]
 rw [mul_add,← sq,← Complex.exp_add,add_neg_cancel,Complex.exp_zero,add_comm]
private lemma z138 (R θ : ℝ) (hR:0< R) :
  ‖(I*(R*Complex.exp ((θ : ℂ)*I))) *
   (1/(R*Complex.exp ((θ : ℂ)*I))+(R*Complex.exp ((θ : ℂ)*I))/(R:ℂ)^2)‖ =
  2 * |Real.cos θ|:=by
 rw [z46 R θ hR,norm_mul,norm_mul,Complex.norm_I,one_mul,
  Complex.norm_exp_ofReal_mul_I,one_mul,norm_mul,Complex.norm_ofNat,
  Complex.norm_real,Real.norm_eq_abs]
private lemma z109 {g:ℝ→ ℂ} {a b:ℝ}
  (hg:ContinuousOn g (Set.uIcc (Real.exp a) (Real.exp b))) :
  (∫ x:ℝ in a..b,g (Real.exp x)*(Real.exp x:ℂ)) =
   ∫ u:ℝ in Real.exp a..Real.exp b,g u:=by
 have hge_cont:ContinuousOn (fun x:ℝ=>g (Real.exp x)*(Real.exp x:ℂ)) (Set.uIcc a b):=by
  refine (hg.comp Real.continuous_exp.continuousOn fun x hx=>?_).mul
   (Complex.continuous_ofReal.comp Real.continuous_exp).continuousOn
  rcases le_total a b with hab | hba
  ·
   rw [Set.uIcc_of_le hab] at hx
   rw [Set.uIcc_of_le (Real.exp_le_exp.mpr hab)]
   exact ⟨Real.exp_le_exp.mpr hx.1,Real.exp_le_exp.mpr hx.2⟩
  ·
   rw [Set.uIcc_of_ge hba] at hx
   rw [Set.uIcc_of_ge (Real.exp_le_exp.mpr hba)]
   exact ⟨Real.exp_le_exp.mpr hx.1,Real.exp_le_exp.mpr hx.2⟩
 have hint1:IntervalIntegrable (fun x:ℝ=>g (Real.exp x)*(Real.exp x:ℂ)) volume a b:=
  hge_cont.intervalIntegrable
 have hint2:IntervalIntegrable g volume (Real.exp a) (Real.exp b):=hg.intervalIntegrable
 have himg:Real.exp '' Set.uIcc a b ⊆ Set.uIcc (Real.exp a) (Real.exp b):=by
  rintro _ ⟨x,hx,rfl⟩
  rcases le_total a b with hab | hba
  ·
   rw [Set.uIcc_of_le hab] at hx
   rw [Set.uIcc_of_le (Real.exp_le_exp.mpr hab)]
   exact ⟨Real.exp_le_exp.mpr hx.1,Real.exp_le_exp.mpr hx.2⟩
  ·
   rw [Set.uIcc_of_ge hba] at hx
   rw [Set.uIcc_of_ge (Real.exp_le_exp.mpr hba)]
   exact ⟨Real.exp_le_exp.mpr hx.1,Real.exp_le_exp.mpr hx.2⟩
 apply Complex.ext
 ·
  have hre1:=Complex.reCLM.intervalIntegral_comp_comm hint1
  have hre2:=Complex.reCLM.intervalIntegral_comp_comm hint2
  simp only [Complex.reCLM_apply] at hre1 hre2
  rw [← hre1,← hre2]
  have hcomp:=intervalIntegral.integral_comp_mul_deriv'
   (f:=Real.exp) (f':=Real.exp) (g:=fun u=>(g u).re)
   (fun x _=>Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn
   ((Complex.continuous_re.comp_continuousOn hg).mono himg)
  refine Eq.trans ?_ hcomp
  refine intervalIntegral.integral_congr fun x _=>?_
  simp [Complex.exp_ofReal_re,mul_comm]
 ·
  have him1:=Complex.imCLM.intervalIntegral_comp_comm hint1
  have him2:=Complex.imCLM.intervalIntegral_comp_comm hint2
  simp only [Complex.imCLM_apply] at him1 him2
  rw [← him1,← him2]
  have hcomp:=intervalIntegral.integral_comp_mul_deriv'
   (f:=Real.exp) (f':=Real.exp) (g:=fun u=>(g u).im)
   (fun x _=>Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn
   ((Complex.continuous_im.comp_continuousOn hg).mono himg)
  refine Eq.trans ?_ hcomp
  refine intervalIntegral.integral_congr fun x _=>?_
  simp [Complex.exp_ofReal_re,mul_comm]
private lemma z117 {R δ : ℝ} (hR:0< R) (hδ : 0 < δ) :
  -(∫ x:ℝ in (-δ)..0,(1:ℂ)/((x:ℂ)+((-R:ℝ):ℂ)*I)) +
   I*(∫ y:ℝ in (-R)..R,(1:ℂ)/(((-δ : ℝ):ℂ)+(y:ℂ)*I)) +
   (∫ x:ℝ in (-δ)..0,(1:ℂ)/((x:ℂ)+(R:ℂ)*I))=-(I*(π : ℂ)):=by
 have hbot:∫ x:ℝ in (-δ)..0,(1:ℂ)/((x:ℂ)+((-R:ℝ):ℂ)*I) =
   Complex.log (-(((0:ℝ):ℂ)+((-R:ℝ):ℂ)*I)) -
   Complex.log (-(((-δ : ℝ):ℂ)+((-R:ℝ):ℂ)*I)):=by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
   (f:=fun x:ℝ=>Complex.log (-((x:ℂ)+((-R:ℝ):ℂ)*I))) (fun x _=>?_) ?_
  ·
   have h1:HasDerivAt (fun t:ℝ=>-((t:ℂ)+((-R:ℝ):ℂ)*I)) (-1:ℂ) x:=
    ((Complex.ofRealCLM.hasDerivAt (x:=x)).add_const (((-R:ℝ):ℂ)*I)).fun_neg
   have hslit:-((x:ℂ)+((-R:ℝ):ℂ)*I)∈Complex.slitPlane:=by
    rw [Complex.mem_slitPlane_iff]
    right
    simp [hR.ne']
   have h2:=h1.clog_real hslit
   have heq:(-1:ℂ) / -((x:ℂ)+((-R:ℝ):ℂ)*I)=(1:ℂ)/((x:ℂ)+((-R:ℝ):ℂ)*I):=by
    rw [div_neg,neg_div,neg_neg]
   exact heq ▸ h2
  ·
   refine ContinuousOn.intervalIntegrable ?_
   intro x _
   refine (continuousAt_const.div ?_ ?_).continuousWithinAt
   ·
    exact (Complex.continuous_ofReal.add continuous_const).continuousAt
   ·
    intro h;have:=congrArg Complex.im h;simp [hR.ne'] at this
 have htop:∫ x:ℝ in (-δ)..0,(1:ℂ)/((x:ℂ)+(R:ℂ)*I) =
   Complex.log (-(((0:ℝ):ℂ)+(R:ℂ)*I)) -
   Complex.log (-(((-δ : ℝ):ℂ)+(R:ℂ)*I)):=by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
   (f:=fun x:ℝ=>Complex.log (-((x:ℂ)+(R:ℂ)*I))) (fun x _=>?_) ?_
  ·
   have h1:HasDerivAt (fun t:ℝ=>-((t:ℂ)+(R:ℂ)*I)) (-1:ℂ) x:=
    ((Complex.ofRealCLM.hasDerivAt (x:=x)).add_const ((R:ℂ)*I)).fun_neg
   have hslit:-((x:ℂ)+(R:ℂ)*I)∈Complex.slitPlane:=by
    rw [Complex.mem_slitPlane_iff]
    right
    simp [hR.ne']
   have h2:=h1.clog_real hslit
   have heq:(-1:ℂ) / -((x:ℂ)+(R:ℂ)*I)=(1:ℂ)/((x:ℂ)+(R:ℂ)*I):=by
    rw [div_neg,neg_div,neg_neg]
   exact heq ▸ h2
  ·
   refine ContinuousOn.intervalIntegrable ?_
   intro x _
   refine (continuousAt_const.div ?_ ?_).continuousWithinAt
   ·
    exact (Complex.continuous_ofReal.add continuous_const).continuousAt
   ·
    intro h;have:=congrArg Complex.im h;simp [hR.ne'] at this
 have hleft:I*(∫ y:ℝ in (-R)..R,(1:ℂ)/(((-δ : ℝ):ℂ)+(y:ℂ)*I)) =
   Complex.log (-(((-δ : ℝ):ℂ)+(R:ℂ)*I)) -
   Complex.log (-(((-δ : ℝ):ℂ)+((-R:ℝ):ℂ)*I)):=by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
   (f:=fun y:ℝ=>Complex.log (-(((-δ : ℝ):ℂ)+(y:ℂ)*I))) (fun y _=>?_) ?_
  ·
   have h0:HasDerivAt (fun t:ℝ=>(t:ℂ)*I) (1*I) y:=
    (Complex.ofRealCLM.hasDerivAt (x:=y)).mul_const I
   have h1:HasDerivAt (fun t:ℝ=>-(((-δ : ℝ):ℂ)+(t:ℂ)*I)) (-I) y:=by
    simpa using (h0.const_add ((-δ : ℝ):ℂ)).fun_neg
   have hslit:-(((-δ : ℝ):ℂ)+(y:ℂ)*I)∈Complex.slitPlane:=by
    rw [Complex.mem_slitPlane_iff]
    left
    simp [hδ]
   have h2:=h1.clog_real hslit
   have heq:(-I) / -(((-δ : ℝ):ℂ)+(y:ℂ)*I) =
     I*((1:ℂ)/(((-δ : ℝ):ℂ)+(y:ℂ)*I)):=by
    rw [div_neg,neg_div,neg_neg,mul_one_div]
   exact heq ▸ h2
  ·
   refine ContinuousOn.intervalIntegrable ?_
   intro y _
   refine (continuousAt_const.mul (continuousAt_const.div ?_ ?_)).continuousWithinAt
   ·
    exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
   ·
    intro h;have:=congrArg Complex.re h;simp [hδ.ne'] at this
 rw [hbot,htop,hleft]
 have htel :
   -(Complex.log (-(((0:ℝ):ℂ)+((-R:ℝ):ℂ)*I)) -
    Complex.log (-(((-δ : ℝ):ℂ)+((-R:ℝ):ℂ)*I))) +
   (Complex.log (-(((-δ : ℝ):ℂ)+(R:ℂ)*I)) -
    Complex.log (-(((-δ : ℝ):ℂ)+((-R:ℝ):ℂ)*I))) +
   (Complex.log (-(((0:ℝ):ℂ)+(R:ℂ)*I)) -
    Complex.log (-(((-δ : ℝ):ℂ)+(R:ℂ)*I))) =
   Complex.log (-((R:ℂ)*I))-Complex.log ((R:ℂ)*I):=by
  simp only [Complex.ofReal_zero,zero_add,Complex.ofReal_neg,neg_mul,neg_neg]
  ring
 rw [htel]
 have hlog_pos:Complex.log ((R:ℂ)*I)=(Real.log R:ℂ)+(π / 2:ℝ)*I:=by
  rw [Complex.log_ofReal_mul hR I_ne_zero,Complex.log_I]
  push_cast
  ring
 have hlog_neg:Complex.log (-((R:ℂ)*I))=(Real.log R:ℂ)-(π / 2:ℝ)*I:=by
  rw [show -((R:ℂ)*I)=(R:ℂ)*(-I) by ring,
   Complex.log_ofReal_mul hR (neg_ne_zero.mpr I_ne_zero),Complex.log_neg_I]
  push_cast
  ring
 rw [hlog_pos,hlog_neg]
 push_cast
 ring
private lemma z51 {G:ℂ→ ℂ} {U:Set ℂ} {R δ T:ℝ}
  (hR:0< R) (hδ : 0 < δ) (hU_open:IsOpen U)
  (hrect:Set.Icc (-δ) R ×ℂ Set.Icc (-R) R ⊆ U)
  (hG_diff:DifferentiableOn ℂ G U) :
  let H_G:ℂ→ ℂ:=fun z=>G z*Complex.exp (z*(T:ℂ))*(1/z+z/(R:ℂ)^2)
  (2*(π : ℂ)*I)*G 0 =
   (∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*H_G (R*Complex.exp ((θ : ℂ)*I))) -
   (-(∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+((-R:ℝ):ℂ)*I)) +
    I*(∫ y:ℝ in (-R)..R,H_G (((-δ : ℝ):ℂ)+(y:ℂ)*I)) +
    (∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+(R:ℂ)*I))):=by
 intro H_G
 have h0_mem:(0:ℂ)∈U:=hrect ⟨⟨by simp;linarith,by simp;exact hR.le⟩,
  ⟨by simp;linarith,by simp;exact hR.le⟩⟩
 let g_exp:ℂ→ ℂ:=fun w=>G w*Complex.exp (w*(T:ℂ))
 have hg_diff:DifferentiableOn ℂ g_exp U:=
  hG_diff.mul ((differentiable_id.mul (differentiable_const (T:ℂ))).cexp.differentiableOn)
 have hg0_diff:DifferentiableAt ℂ g_exp 0:=hg_diff.differentiableAt (hU_open.mem_nhds h0_mem)
 let F:ℂ→ ℂ:=Function.update
  (fun z=>(g_exp z-G 0)/z+g_exp z*z/(R:ℂ)^2) 0 (deriv g_exp 0)
 have hF_of_ne:∀ z:ℂ,z≠0→ F z=H_G z-G 0/z:=by
  intro z hz
  simp only [F,Function.update_of_ne hz,H_G,g_exp]
  field_simp [hz,Complex.ofReal_ne_zero.mpr hR.ne']
  ring
 have hF_cont:ContinuousOn F U:=by
  intro z hz
  rcases eq_or_ne z 0 with rfl | hz0
  ·
   refine ContinuousAt.continuousWithinAt ?_
   have h1:Tendsto (fun w:ℂ=>(g_exp w-g_exp 0)/w) (𝓝[≠] 0) (𝓝 (deriv g_exp 0)):=
    hg0_diff.hasDerivAt.tendsto_slope_zero.congr fun w=>by
     simp [zero_add,smul_eq_mul,inv_mul_eq_div]
   have h2:Tendsto (fun w:ℂ=>g_exp w*w/(R:ℂ)^2) (𝓝[≠] 0) (𝓝 0):=by
    have hc:ContinuousAt (fun w:ℂ=>g_exp w*w/(R:ℂ)^2) 0:=
     (hg0_diff.continuousAt.mul continuousAt_id).div_const _
    have hc':Tendsto (fun w:ℂ=>g_exp w*w/(R:ℂ)^2) (𝓝[≠] 0)
      (𝓝 (g_exp 0*0/(R:ℂ)^2)):=hc.continuousWithinAt
    simpa using hc'
   have h3:Tendsto (fun w:ℂ=>(g_exp w-G 0)/w+g_exp w*w/(R:ℂ)^2)
     (𝓝[≠] 0) (𝓝 (deriv g_exp 0+0)):=by
    have h1':Tendsto (fun w:ℂ=>(g_exp w-G 0)/w) (𝓝[≠] 0) (𝓝 (deriv g_exp 0)):=by
     simpa [g_exp] using h1
    exact h1'.add h2
   rw [add_zero] at h3
   refine continuousWithinAt_compl_self.mp ?_
   have hF0:F 0=deriv g_exp 0:=by simp [F]
   rw [ContinuousWithinAt,hF0]
   refine h3.congr' ?_
   filter_upwards [self_mem_nhdsWithin] with w hw
   simp only [F,Function.update_of_ne hw]
  ·
   refine ContinuousAt.continuousWithinAt ?_
   have hg_at:DifferentiableAt ℂ g_exp z:=hg_diff.differentiableAt (hU_open.mem_nhds hz)
   have hcont_at:ContinuousAt (fun w=>(g_exp w-G 0)/w+g_exp w*w/(R:ℂ)^2) z:=
    ((hg_at.continuousAt.sub continuousAt_const).div continuousAt_id hz0).add
     ((hg_at.continuousAt.mul continuousAt_id).div_const _)
   refine hcont_at.congr ?_
   filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
   simp only [F,Function.update_of_ne hw]
 have hF_diff:∀ z∈U \ {0},DifferentiableAt ℂ F z:=by
  intro z ⟨hzU,hz0⟩
  have hg_at:DifferentiableAt ℂ g_exp z:=hg_diff.differentiableAt (hU_open.mem_nhds hzU)
  have hd:DifferentiableAt ℂ (fun w=>(g_exp w-G 0)/w+g_exp w*w/(R:ℂ)^2) z:=
   ((hg_at.sub (differentiableAt_const _)).div differentiableAt_id hz0).add
    ((hg_at.mul differentiableAt_id).div_const _)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
  simp only [F,Function.update_of_ne hw]
 have hrect_left :
   (∫ x:ℝ in (-δ)..0,F ((x:ℂ)+((-R:ℝ):ℂ)*I)) -
   (∫ x:ℝ in (-δ)..0,F ((x:ℂ)+(R:ℂ)*I)) +
   I*(∫ y:ℝ in (-R)..R,F (((0:ℝ):ℂ)+(y:ℂ)*I)) -
   I*(∫ y:ℝ in (-R)..R,F (((-δ : ℝ):ℂ)+(y:ℂ)*I))=0:=by
  let z₁:ℂ:=⟨-δ,-R⟩
  let w₁:ℂ:=⟨0,R⟩
  have hsub1:Set.uIcc z₁.re w₁.re ×ℂ Set.uIcc z₁.im w₁.im ⊆ U:=by
   intro z hz
   apply hrect
   simp only [z₁,w₁,Set.uIcc_of_le (show -δ ≤ 0 by linarith),
    Set.uIcc_of_le (show -R ≤ R by linarith)] at hz
   exact ⟨⟨hz.1.1,hz.1.2.trans hR.le⟩,hz.2⟩
  have h:=Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable F z₁ w₁ {0}
   (Set.countable_singleton 0) (hF_cont.mono hsub1) (fun z hz=>hF_diff z ⟨hsub1 ⟨?_,?_⟩,hz.2⟩)
  ·
   simpa [z₁,w₁,smul_eq_mul] using h
  ·
   exact Set.Ioo_subset_Icc_self (by simpa [Set.uIcc] using hz.1.1)
  ·
   exact Set.Ioo_subset_Icc_self (by simpa [Set.uIcc] using hz.1.2)
 have hsemi :
   (∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*F (R*Complex.exp ((θ : ℂ)*I))) =
   I*(∫ y:ℝ in (-R)..R,F ((y:ℂ)*I)):=by
  have h_eps:∀ ε : ℝ,0 < ε→ ε < R →
    (∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*F (R*Complex.exp ((θ : ℂ)*I))) -
    (∫ θ : ℝ in (-π / 2)..(π / 2),(I*(ε*Complex.exp ((θ : ℂ)*I)))*F (ε*Complex.exp ((θ : ℂ)*I))) =
    I*(∫ y:ℝ in (-R)..(-ε),F ((y:ℂ)*I))+I*(∫ y:ℝ in ε..R,F ((y:ℂ)*I)):=by
   intro ε hε hεR
   let z₂:ℂ:=⟨Real.log ε,-π / 2⟩
   let w₂:ℂ:=⟨Real.log R,π / 2⟩
   let g_pol:ℂ→ ℂ:=fun w=>F (Complex.exp w)*Complex.exp w
   have hpol_mem:∀ w∈Set.uIcc z₂.re w₂.re ×ℂ Set.uIcc z₂.im w₂.im,Complex.exp w∈U \ {0}:=by
    intro w hw
    have hre_le:Real.log ε ≤ Real.log R:=Real.log_le_log hε hεR.le
    have him_le:-π / 2 ≤ π / 2:=by linarith [Real.pi_pos]
    simp only [z₂,w₂,Set.uIcc_of_le hre_le,Set.uIcc_of_le him_le] at hw
    refine ⟨hrect ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,Complex.exp_ne_zero w⟩
    ·
     have hcos:0 ≤ Real.cos w.im:=Real.cos_nonneg_of_mem_Icc ⟨by linarith [hw.2.1],hw.2.2⟩
     rw [Complex.exp_re]
     linarith [mul_nonneg (Real.exp_nonneg w.re) hcos]
    ·
     rw [Complex.exp_re]
     calc
      Real.exp w.re*Real.cos w.im ≤ Real.exp w.re*1:=
        mul_le_mul_of_nonneg_left (Real.cos_le_one _) (Real.exp_nonneg _)
      _ ≤ Real.exp (Real.log R):=by rw [mul_one];exact Real.exp_le_exp.mpr hw.1.2
      _=R:=Real.exp_log hR
    ·
     rw [Complex.exp_im]
     have h1:-1 ≤ Real.sin w.im:=Real.neg_one_le_sin _
     have h2:Real.exp w.re ≤ R:=(Real.exp_le_exp.mpr hw.1.2).trans_eq (Real.exp_log hR)
     nlinarith [Real.exp_nonneg w.re]
    ·
     rw [Complex.exp_im]
     have h1:Real.sin w.im ≤ 1:=Real.sin_le_one _
     have h2:Real.exp w.re ≤ R:=(Real.exp_le_exp.mpr hw.1.2).trans_eq (Real.exp_log hR)
     nlinarith [Real.exp_nonneg w.re]
   have hpol_diff:DifferentiableOn ℂ g_pol (Set.uIcc z₂.re w₂.re ×ℂ Set.uIcc z₂.im w₂.im):=by
    intro w hw
    have hm:=hpol_mem w hw
    exact ((hF_diff _ hm).comp w (Complex.differentiableAt_exp)).mul
     Complex.differentiableAt_exp |>.differentiableWithinAt
   have hcg:=Complex.integral_boundary_rect_eq_zero_of_differentiableOn g_pol z₂ w₂ hpol_diff
   simp only [z₂,w₂,smul_eq_mul] at hcg
   have hbot:(∫ x:ℝ in Real.log ε..Real.log R,g_pol ((x:ℂ)+((-π / 2:ℝ):ℂ)*I)) =
     -I*(∫ y:ℝ in (-R)..(-ε),F ((y:ℂ)*I)):=by
    have hstep1:(∫ x:ℝ in Real.log ε..Real.log R,g_pol ((x:ℂ)+((-π / 2:ℝ):ℂ)*I)) =
      ∫ x:ℝ in Real.log ε..Real.log R,(-I)*(F ((-Real.exp x:ℝ)*I)*(Real.exp x:ℂ)):=by
     refine intervalIntegral.integral_congr fun x _=>?_
     simp only [g_pol,Complex.exp_add]
     have hpi:Complex.exp (((-π / 2:ℝ):ℂ)*I)=-I:=by
      rw [show (((-π / 2:ℝ):ℂ)*I)=-((π / 2:ℂ)*I) by push_cast;ring,
       Complex.exp_neg,Complex.exp_pi_div_two_mul_I,inv_I]
     rw [hpi,← Complex.ofReal_exp]
     push_cast
     ring
    rw [hstep1,intervalIntegral.integral_const_mul]
    congr 1
    have hsub_exp:(∫ x:ℝ in Real.log ε..Real.log R,F ((-Real.exp x:ℝ)*I)*(Real.exp x:ℂ)) =
      ∫ u:ℝ in ε..R,F ((-u:ℝ)*I):=by
     have hcomp:=z109 (g:=fun u:ℝ=>F ((-u:ℝ)*I))
      (a:=Real.log ε) (b:=Real.log R) (by
       rw [Real.exp_log hε,Real.exp_log hR,Set.uIcc_of_le hεR.le]
       refine hF_cont.comp ((Complex.continuous_ofReal.comp continuous_neg).mul continuous_const).continuousOn
        fun u hu=>hrect ⟨⟨by simp;linarith,by simp;exact hR.le⟩,?_⟩
       exact ⟨by simp;linarith [hu.2],by simp;linarith [hu.1]⟩)
     simpa [Real.exp_log hε,Real.exp_log hR] using hcomp
    rw [hsub_exp]
    have hneg:=intervalIntegral.integral_comp_neg (f:=fun y:ℝ=>F ((y:ℂ)*I)) (a:=ε) (b:=R)
    simpa using hneg
   have htop:(∫ x:ℝ in Real.log ε..Real.log R,g_pol ((x:ℂ)+((π / 2:ℝ):ℂ)*I)) =
     I*(∫ y:ℝ in ε..R,F ((y:ℂ)*I)):=by
    have hstep1:(∫ x:ℝ in Real.log ε..Real.log R,g_pol ((x:ℂ)+((π / 2:ℝ):ℂ)*I)) =
      ∫ x:ℝ in Real.log ε..Real.log R,I*(F ((Real.exp x:ℝ)*I)*(Real.exp x:ℂ)):=by
     refine intervalIntegral.integral_congr fun x _=>?_
     simp only [g_pol,Complex.exp_add]
     have hpi:Complex.exp (((π / 2:ℝ):ℂ)*I)=I:=by
      rw [Complex.exp_mul_I]
      simp
     rw [hpi,← Complex.ofReal_exp]
     ring
    rw [hstep1,intervalIntegral.integral_const_mul]
    congr 1
    have hcomp:=z109 (g:=fun u:ℝ=>F ((u:ℂ)*I))
     (a:=Real.log ε) (b:=Real.log R) (by
      rw [Real.exp_log hε,Real.exp_log hR,Set.uIcc_of_le hεR.le]
      refine hF_cont.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn
       fun u hu=>hrect ⟨⟨by simp;linarith,by simp;exact hR.le⟩,?_⟩
      exact ⟨by simp;linarith [hu.1],by simp;exact hu.2⟩)
    simpa [Real.exp_log hε,Real.exp_log hR] using hcomp
   have hright:I*(∫ θ : ℝ in (-π / 2)..(π / 2),g_pol ((Real.log R:ℂ)+(θ : ℂ)*I)) =
     ∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*F (R*Complex.exp ((θ : ℂ)*I)):=by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _=>?_
    simp only [g_pol,Complex.exp_add,← Complex.ofReal_exp,Real.exp_log hR]
    ring
   have hleft:I*(∫ θ : ℝ in (-π / 2)..(π / 2),g_pol ((Real.log ε : ℂ)+(θ : ℂ)*I)) =
     ∫ θ : ℝ in (-π / 2)..(π / 2),(I*(ε*Complex.exp ((θ : ℂ)*I)))*F (ε*Complex.exp ((θ : ℂ)*I)):=by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _=>?_
    simp only [g_pol,Complex.exp_add,← Complex.ofReal_exp,Real.exp_log hε]
    ring
   rw [hbot,htop,hright,hleft] at hcg
   linear_combination hcg
  have hK_comp:IsCompact (Set.Icc (-δ) R ×ℂ Set.Icc (-R) R):=isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨M,hM⟩:=hK_comp.exists_bound_of_continuousOn (hF_cont.mono hrect)
  have hM_nonneg:0 ≤ M:=by
   have h0:=hM 0 ⟨⟨by simp;linarith,by simp;exact hR.le⟩,
    ⟨by simp;linarith,by simp;exact hR.le⟩⟩
   exact (norm_nonneg _).trans h0
  have hcont_axis:ContinuousOn (fun y:ℝ=>F ((y:ℂ)*I)) (Set.Icc (-R) R):=by
   refine hF_cont.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn fun y hy=>?_
   apply hrect
   exact ⟨⟨by simp;linarith,by simp;exact hR.le⟩,by simpa using hy⟩
  have hint_axis:IntervalIntegrable (fun y:ℝ=>F ((y:ℂ)*I)) volume (-R) R:=
   (hcont_axis.mono (by rw [Set.uIcc_of_le (by linarith)])).intervalIntegrable
  have hdiff_bound:∀ ε : ℝ,0 < ε→ ε < R →
    ‖(∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*F (R*Complex.exp ((θ : ℂ)*I))) -
     I*(∫ y:ℝ in (-R)..R,F ((y:ℂ)*I))‖ ≤ (π+2)*M*ε:=by
   intro ε hε hεR
   have hsplit1:(∫ y:ℝ in (-R)..R,F ((y:ℂ)*I)) =
     (∫ y:ℝ in (-R)..(-ε),F ((y:ℂ)*I)) +
     (∫ y:ℝ in (-ε)..ε,F ((y:ℂ)*I)) +
     (∫ y:ℝ in ε..R,F ((y:ℂ)*I)):=by
    have hint_a:IntervalIntegrable (fun y:ℝ=>F ((y:ℂ)*I)) volume (-R) (-ε):=
     hint_axis.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (by rw [Set.uIcc_of_le (by linarith)];exact ⟨by linarith,by linarith⟩))
    have hint_b:IntervalIntegrable (fun y:ℝ=>F ((y:ℂ)*I)) volume (-ε) ε:=
     hint_axis.mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.uIcc_of_le (by linarith)];exact ⟨by linarith,by linarith⟩)
      (by rw [Set.uIcc_of_le (by linarith)];exact ⟨by linarith,by linarith⟩))
    have hint_c:IntervalIntegrable (fun y:ℝ=>F ((y:ℂ)*I)) volume ε R:=
     hint_axis.mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.uIcc_of_le (by linarith)];exact ⟨by linarith,by linarith⟩)
      Set.right_mem_uIcc)
    have hint_ab:IntervalIntegrable (fun y:ℝ=>F ((y:ℂ)*I)) volume (-R) ε:=
     hint_axis.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (by rw [Set.uIcc_of_le (by linarith)];exact ⟨by linarith,by linarith⟩))
    have h1:=intervalIntegral.integral_add_adjacent_intervals hint_a hint_b
    have h2:=intervalIntegral.integral_add_adjacent_intervals hint_ab hint_c
    rw [← h2,← h1]
   have heq :
     (∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*F (R*Complex.exp ((θ : ℂ)*I))) -
     I*(∫ y:ℝ in (-R)..R,F ((y:ℂ)*I)) =
     (∫ θ : ℝ in (-π / 2)..(π / 2),(I*(ε*Complex.exp ((θ : ℂ)*I)))*F (ε*Complex.exp ((θ : ℂ)*I))) -
     I*(∫ y:ℝ in (-ε)..ε,F ((y:ℂ)*I)):=by
    rw [hsplit1]
    linear_combination h_eps ε hε hεR
   rw [heq]
   have hnorm1:‖∫ θ : ℝ in (-π / 2)..(π / 2),
     (I*(ε*Complex.exp ((θ : ℂ)*I)))*F (ε*Complex.exp ((θ : ℂ)*I))‖ ≤ M*ε*π:=by
    have hb:=intervalIntegral.norm_integral_le_of_norm_le_const (C:=M*ε)
     (a:=-π / 2) (b:=π / 2) (f:=fun θ : ℝ =>
      (I*(ε*Complex.exp ((θ : ℂ)*I)))*F (ε*Complex.exp ((θ : ℂ)*I)))
     (fun θ hθ=>by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hθ
      rw [norm_mul,norm_mul,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,
       Real.norm_of_nonneg hε.le,Complex.norm_exp_ofReal_mul_I,mul_one]
      have hmem:(ε : ℂ)*Complex.exp ((θ : ℂ)*I)∈Set.Icc (-δ) R ×ℂ Set.Icc (-R) R:=by
       refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
       ·
        rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
         Complex.exp_ofReal_mul_I_re]
        have hcos:0 ≤ Real.cos θ:=Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1],hθ.2⟩
        linarith [mul_nonneg hε.le hcos]
       ·
        rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
         Complex.exp_ofReal_mul_I_re]
        nlinarith [Real.cos_le_one θ]
       ·
        rw [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
         Complex.exp_ofReal_mul_I_im]
        nlinarith [Real.neg_one_le_sin θ]
       ·
        rw [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
         Complex.exp_ofReal_mul_I_im]
        nlinarith [Real.sin_le_one θ]
      have hFle:=hM _ hmem
      nlinarith)
    calc
     _ ≤ M*ε * |π / 2 - -π / 2|:=hb
     _=M*ε*π:=by
       rw [show π / 2 - -π / 2=π by ring,abs_of_pos Real.pi_pos]
   have hnorm2:‖I*(∫ y:ℝ in (-ε)..ε,F ((y:ℂ)*I))‖ ≤ 2*M*ε:=by
    rw [norm_mul,Complex.norm_I,one_mul]
    have hb:=intervalIntegral.norm_integral_le_of_norm_le_const (C:=M)
     (a:=-ε) (b:=ε) (f:=fun y:ℝ=>F ((y:ℂ)*I))
     (fun y hy=>by
      rw [Set.uIoc_of_le (by linarith)] at hy
      refine hM _ ⟨⟨?_,?_⟩,?_⟩
      ·
       simp only [Complex.mul_re,Complex.ofReal_re,Complex.I_re,mul_zero,
        Complex.ofReal_im,Complex.I_im,zero_mul,sub_self]
       linarith
      ·
       simp only [Complex.mul_re,Complex.ofReal_re,Complex.I_re,mul_zero,
        Complex.ofReal_im,Complex.I_im,zero_mul,sub_self]
       exact hR.le
      ·
       exact ⟨by simp;linarith [hy.1],by simp;linarith [hy.2]⟩)
    calc
     _ ≤ M * |ε - -ε|:=hb
     _=2*M*ε:=by
       rw [show ε - -ε=2*ε by ring,abs_of_pos (by linarith)]
       ring
   calc
    _ ≤ ‖∫ θ : ℝ in (-π / 2)..(π / 2),
       (I*(ε*Complex.exp ((θ : ℂ)*I)))*F (ε*Complex.exp ((θ : ℂ)*I))‖ +
      ‖I*(∫ y:ℝ in (-ε)..ε,F ((y:ℂ)*I))‖:=norm_sub_le _ _
    _ ≤ M*ε*π+2*M*ε:=add_le_add hnorm1 hnorm2
    _=(π+2)*M*ε:=by ring
  apply sub_eq_zero.mp
  rw [← norm_eq_zero]
  refine le_antisymm ?_ (norm_nonneg _)
  by_contra! hpos
  set c:=‖(∫ θ : ℝ in (-π / 2)..(π / 2),
    (I*(R*Complex.exp ((θ : ℂ)*I)))*F (R*Complex.exp ((θ : ℂ)*I))) -
   I*(∫ y:ℝ in (-R)..R,F ((y:ℂ)*I))‖
  let ε:=min (R/2) (c/(2*((π+2)*M+1)))
  have hε_pos:0 < ε:=by
   refine lt_min (half_pos hR) (div_pos hpos ?_)
   have:0 ≤ (π+2)*M:=mul_nonneg (by linarith [Real.pi_pos]) hM_nonneg
   linarith
  have hεR:ε < R:=(min_le_left _ _).trans_lt (half_lt_self hR)
  have hle:=hdiff_bound ε hε_pos hεR
  have hε_le:ε ≤ c/(2*((π+2)*M+1)):=min_le_right _ _
  have hden_pos:0< 2*((π+2)*M+1):=by
   have:0 ≤ (π+2)*M:=mul_nonneg (by linarith [Real.pi_pos]) hM_nonneg
   linarith
  have hlt:(π+2)*M*ε < c:=by
   calc
    (π+2)*M*ε ≤ (π+2)*M*(c/(2*((π+2)*M+1))):=
      mul_le_mul_of_nonneg_left hε_le (mul_nonneg (by linarith [Real.pi_pos]) hM_nonneg)
    _< ((π+2)*M+1)*(c/(2*((π+2)*M+1))):=
      mul_lt_mul_of_pos_right (by linarith) (div_pos hpos hden_pos)
    _=c/2:=by field_simp [hden_pos.ne']
    _< c:=half_lt_self hpos
  linarith
 have hF_eq :
   (∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*F (R*Complex.exp ((θ : ℂ)*I))) =
   -(∫ x:ℝ in (-δ)..0,F ((x:ℂ)+((-R:ℝ):ℂ)*I)) +
   I*(∫ y:ℝ in (-R)..R,F (((-δ : ℝ):ℂ)+(y:ℂ)*I)) +
   (∫ x:ℝ in (-δ)..0,F ((x:ℂ)+(R:ℂ)*I)):=by
  have h0:I*(∫ y:ℝ in (-R)..R,F (((0:ℝ):ℂ)+(y:ℂ)*I)) =
    I*(∫ y:ℝ in (-R)..R,F ((y:ℂ)*I)):=by simp
  rw [h0] at hrect_left
  linear_combination hsemi+hrect_left
 have hH_cont:ContinuousOn H_G (U \ {0}):=by
  intro z ⟨hzU,hz0⟩
  refine ContinuousAt.continuousWithinAt ?_
  have hG_at:ContinuousAt G z:=(hG_diff.differentiableAt (hU_open.mem_nhds hzU)).continuousAt
  exact (hG_at.mul ((continuous_id.mul continuous_const).cexp.continuousAt)).mul
   ((continuousAt_const.div continuousAt_id hz0).add (continuousAt_id.div_const _))
 have hinv_cont:ContinuousOn (fun z:ℂ=>G 0/z) (U \ {0}):=fun z hz =>
  (continuousAt_const.div continuousAt_id hz.2).continuousWithinAt
 have hsemi_split :
   (∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*F (R*Complex.exp ((θ : ℂ)*I))) =
   (∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*H_G (R*Complex.exp ((θ : ℂ)*I))) -
   I*(π : ℂ)*G 0:=by
  have hcongr:∀ θ∈Set.uIcc (-π / 2) (π / 2),
    (I*(R*Complex.exp ((θ : ℂ)*I)))*F (R*Complex.exp ((θ : ℂ)*I)) =
    (I*(R*Complex.exp ((θ : ℂ)*I)))*H_G (R*Complex.exp ((θ : ℂ)*I))-I*G 0:=by
   intro θ _
   have hz0:(R:ℂ)*Complex.exp ((θ : ℂ)*I)≠0:=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (Complex.exp_ne_zero _)
   rw [hF_of_ne _ hz0,mul_sub]
   congr 1
   have hR0:(R:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hR.ne'
   have hexp0:Complex.exp ((θ : ℂ)*I)≠0:=Complex.exp_ne_zero _
   field_simp [hR0,hexp0]
  rw [intervalIntegral.integral_congr hcongr,intervalIntegral.integral_sub]
  ·
   simp only [intervalIntegral.integral_const,Complex.real_smul]
   have:(π / 2 - -π / 2:ℝ)=π:=by ring
   rw [this]
   ring
  ·
   refine ContinuousOn.intervalIntegrable ?_
   have hmap:Continuous (fun θ : ℝ=>(R:ℂ)*Complex.exp ((θ : ℂ)*I)):=
    continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
   refine (continuous_const.mul hmap).continuousOn.mul (hH_cont.comp hmap.continuousOn fun θ hθ=>?_)
   rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
   refine ⟨hrect ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (Complex.exp_ne_zero _)⟩
   ·
    rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
     Complex.exp_ofReal_mul_I_re]
    linarith [mul_nonneg hR.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1],hθ.2⟩)]
   ·
    rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
     Complex.exp_ofReal_mul_I_re]
    nlinarith [Real.cos_le_one θ]
   ·
    rw [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
     Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.neg_one_le_sin θ]
   ·
    rw [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
     Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.sin_le_one θ]
  ·
   exact intervalIntegrable_const
 have hbot_split :
   (∫ x:ℝ in (-δ)..0,F ((x:ℂ)+((-R:ℝ):ℂ)*I)) =
   (∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+((-R:ℝ):ℂ)*I)) -
   G 0*(∫ x:ℝ in (-δ)..0,(1:ℂ)/((x:ℂ)+((-R:ℝ):ℂ)*I)):=by
  have hne:∀ x:ℝ,(x:ℂ)+((-R:ℝ):ℂ)*I≠0:=fun x h=>by
   have:=congrArg Complex.im h;simp [hR.ne'] at this
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub]
  ·
   refine intervalIntegral.integral_congr fun x _=>?_
   rw [hF_of_ne _ (hne x),mul_one_div]
  ·
   refine ContinuousOn.intervalIntegrable ?_
   refine hH_cont.comp (Complex.continuous_ofReal.add continuous_const).continuousOn fun x hx=>?_
   rw [Set.uIcc_of_le (by linarith)] at hx
   exact ⟨hrect ⟨⟨by simpa using hx.1,by simp;linarith [hx.2]⟩,
    ⟨by simp,by simp;linarith⟩⟩,hne x⟩
  ·
   refine (ContinuousOn.intervalIntegrable ?_).const_mul _
   intro x _
   exact (continuousAt_const.div (Complex.continuous_ofReal.add continuous_const).continuousAt
    (hne x)).continuousWithinAt
 have htop_split :
   (∫ x:ℝ in (-δ)..0,F ((x:ℂ)+(R:ℂ)*I)) =
   (∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+(R:ℂ)*I)) -
   G 0*(∫ x:ℝ in (-δ)..0,(1:ℂ)/((x:ℂ)+(R:ℂ)*I)):=by
  have hne:∀ x:ℝ,(x:ℂ)+(R:ℂ)*I≠0:=fun x h=>by
   have:=congrArg Complex.im h;simp [hR.ne'] at this
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub]
  ·
   refine intervalIntegral.integral_congr fun x _=>?_
   rw [hF_of_ne _ (hne x),mul_one_div]
  ·
   refine ContinuousOn.intervalIntegrable ?_
   refine hH_cont.comp (Complex.continuous_ofReal.add continuous_const).continuousOn fun x hx=>?_
   rw [Set.uIcc_of_le (by linarith)] at hx
   exact ⟨hrect ⟨⟨by simpa using hx.1,by simp;linarith [hx.2]⟩,
    ⟨by simp;linarith,by simp⟩⟩,hne x⟩
  ·
   refine (ContinuousOn.intervalIntegrable ?_).const_mul _
   intro x _
   exact (continuousAt_const.div (Complex.continuous_ofReal.add continuous_const).continuousAt
    (hne x)).continuousWithinAt
 have hleft_split :
   (∫ y:ℝ in (-R)..R,F (((-δ : ℝ):ℂ)+(y:ℂ)*I)) =
   (∫ y:ℝ in (-R)..R,H_G (((-δ : ℝ):ℂ)+(y:ℂ)*I)) -
   G 0*(∫ y:ℝ in (-R)..R,(1:ℂ)/(((-δ : ℝ):ℂ)+(y:ℂ)*I)):=by
  have hne:∀ y:ℝ,((-δ : ℝ):ℂ)+(y:ℂ)*I≠0:=fun y h=>by
   have:=congrArg Complex.re h;simp [hδ.ne'] at this
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub]
  ·
   refine intervalIntegral.integral_congr fun y _=>?_
   rw [hF_of_ne _ (hne y),mul_one_div]
  ·
   refine ContinuousOn.intervalIntegrable ?_
   refine hH_cont.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
    fun y hy=>?_
   rw [Set.uIcc_of_le (by linarith)] at hy
   exact ⟨hrect ⟨⟨by simp,by simp;linarith⟩,by simpa using hy⟩,hne y⟩
  ·
   refine (ContinuousOn.intervalIntegrable ?_).const_mul _
   intro y _
   exact (continuousAt_const.div
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
    (hne y)).continuousWithinAt
 rw [hsemi_split,hbot_split,htop_split,hleft_split] at hF_eq
 have hinv:=z117 hR hδ
 linear_combination -hF_eq+G 0*hinv
private lemma z45 {f:ℝ→ ℝ} {B R T:ℝ}
  (hB:0< B) (hR:0< R) (hT:0 ≤ T)
  (hf_meas:Measurable f) (hf_bound:∀ t ≥ 0,|f t| ≤ B) :
  let H_g:ℂ→ ℂ:=fun z=>z119 f T z*Complex.exp (z*(T:ℂ))*(1/z+z/(R:ℂ)^2)
  (2*(π : ℂ)*I)*z119 f T 0 =
   (∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*H_g (R*Complex.exp ((θ : ℂ)*I))) +
   (∫ θ : ℝ in (π / 2)..(3*π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*H_g (R*Complex.exp ((θ : ℂ)*I))):=by
 intro H_g
 let P:ℂ→ ℂ:=fun z=>z119 f T z*Complex.exp (z*(T:ℂ))*(1+z^2/(R:ℂ)^2)
 have hP_diff:Differentiable ℂ P:=
  ((z69 hB hf_meas hf_bound hT).mul
   ((differentiable_id.mul (differentiable_const (T:ℂ))).cexp)).mul
   ((differentiable_const 1).add ((differentiable_id.pow 2).div_const _))
 have hcauchy:=Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
  (c:=0) (f:=P) hR Set.countable_empty hP_diff.continuous.continuousOn
  (fun z _=>hP_diff z)
 have hP0:P 0=z119 f T 0:=by simp [P]
 rw [hP0] at hcauchy
 simp only [smul_eq_mul,sub_zero] at hcauchy
 let φ : ℝ→ ℂ:=fun θ=>(I*(R*Complex.exp ((θ : ℂ)*I)))*H_g (R*Complex.exp ((θ : ℂ)*I))
 have hcircle_eq:(∮ z in C(0,R),z⁻¹*P z)=∫ θ : ℝ in (0:ℝ)..(2*π),φ θ:=by
  unfold circleIntegral
  refine intervalIntegral.integral_congr fun θ _=>?_
  have hz0:(R:ℂ)*Complex.exp ((θ : ℂ)*I)≠0:=
   mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (Complex.exp_ne_zero _)
  have hmap:circleMap 0 R θ=(R:ℂ)*Complex.exp ((θ : ℂ)*I):=by simp [circleMap]
  have hderiv:deriv (circleMap 0 R) θ=(R:ℂ)*Complex.exp ((θ : ℂ)*I)*I:=by
   simp [deriv_circleMap,circleMap]
  rw [smul_eq_mul,hderiv,hmap]
  simp only [P,φ,H_g]
  field_simp [hz0,Complex.ofReal_ne_zero.mpr hR.ne']
 have hφ_per:Function.Periodic φ (2*π):=by
  intro θ
  simp only [φ]
  have hexp:Complex.exp (((θ+2*π : ℝ):ℂ)*I)=Complex.exp ((θ : ℂ)*I):=by
   rw [Complex.ofReal_add,add_mul,Complex.exp_add]
   have:((2*π : ℝ):ℂ)*I=2*(π : ℂ)*I:=by push_cast;ring
   rw [this,Complex.exp_two_pi_mul_I,mul_one]
  rw [hexp]
 have hφ_cont:Continuous φ:=by
  have hmap:Continuous (fun θ : ℝ=>(R:ℂ)*Complex.exp ((θ : ℂ)*I)):=
   continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
  have hmap_ne:∀ θ : ℝ,(R:ℂ)*Complex.exp ((θ : ℂ)*I)≠0:=fun θ =>
   mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (Complex.exp_ne_zero _)
  have hg_cont:Continuous (z119 f T):=
   (z69 hB hf_meas hf_bound hT).continuous
  refine (continuous_const.mul hmap).mul ?_
  exact ((hg_cont.comp hmap).mul
   (Complex.continuous_exp.comp (hmap.mul continuous_const))).mul
   ((continuous_const.div hmap hmap_ne).add (hmap.div_const _))
 have hshift:(∫ θ : ℝ in (0:ℝ)..(2*π),φ θ)=∫ θ : ℝ in (-π / 2)..(3*π / 2),φ θ:=by
  have h:=hφ_per.intervalIntegral_add_eq (-π / 2) 0
  simpa [show -π / 2+2*π=3*π / 2 by ring] using h.symm
 have hsplit:(∫ θ : ℝ in (-π / 2)..(3*π / 2),φ θ) =
   (∫ θ : ℝ in (-π / 2)..(π / 2),φ θ)+(∫ θ : ℝ in (π / 2)..(3*π / 2),φ θ):=
  (intervalIntegral.integral_add_adjacent_intervals
   (hφ_cont.intervalIntegrable _ _) (hφ_cont.intervalIntegrable _ _)).symm
 rw [← hcauchy,hcircle_eq,hshift,hsplit]
private lemma z133
  {f:ℝ→ ℝ} {B:ℝ} (hB:0< B)
  (hf_meas:Measurable f)
  (hf_bound:∀ t ≥ 0,|f t| ≤ B)
  {G:ℂ→ ℂ} {U:Set ℂ} (hU_open:IsOpen U)
  (hU_sub:{z:ℂ | 0 ≤ z.re} ⊆ U)
  (hG_diff:DifferentiableOn ℂ G U)
  (hG_lap:∀ z:ℂ,0< z.re →
   G z=∫ t in Set.Ioi (0:ℝ),(f t:ℂ)*Complex.exp (-z*(t:ℂ))) :
  Tendsto (fun T:ℝ=>z119 f T 0) atTop (𝓝 (G 0)):=by
 rw [Metric.tendsto_atTop]
 intro η hη
 let R:ℝ:=4*B / η+1
 have hR:0< R:=by positivity
 have hBR:2*B/R < η / 2:=by
  rw [div_lt_iff₀ hR]
  have h1:4*B / η < R:=by simp [R]
  have:2*B=(η / 2)*(4*B / η):=by field_simp [hη.ne'];ring
  rw [this]
  exact mul_lt_mul_of_pos_left h1 (half_pos hη)
 obtain ⟨δ,hδ,hrect⟩:=z71 hU_open hU_sub hR
 let K_base:ℂ→ ℂ:=fun z=>G z*(1/z+z/(R:ℂ)^2)
 have hK_cont:ContinuousOn K_base (U \ {0}):=by
  intro z ⟨hzU,hz0⟩
  exact ((hG_diff.differentiableAt (hU_open.mem_nhds hzU)).continuousAt.mul
   ((continuousAt_const.div continuousAt_id hz0).add (continuousAt_id.div_const _))).continuousWithinAt
 have hbot_cont:ContinuousOn (fun x:ℝ=>K_base ((x:ℂ)+((-R:ℝ):ℂ)*I)) (Set.Icc (-δ) 0):=by
  refine hK_cont.comp (Complex.continuous_ofReal.add continuous_const).continuousOn fun x hx=>?_
  refine ⟨hrect ⟨⟨by simpa using hx.1,by simp;linarith [hx.2]⟩,⟨by simp,by simp;linarith⟩⟩,?_⟩
  intro h;have:=congrArg Complex.im h;simp [hR.ne'] at this
 have htop_cont:ContinuousOn (fun x:ℝ=>K_base ((x:ℂ)+(R:ℂ)*I)) (Set.Icc (-δ) 0):=by
  refine hK_cont.comp (Complex.continuous_ofReal.add continuous_const).continuousOn fun x hx=>?_
  refine ⟨hrect ⟨⟨by simpa using hx.1,by simp;linarith [hx.2]⟩,⟨by simp;linarith,by simp⟩⟩,?_⟩
  intro h;have:=congrArg Complex.im h;simp [hR.ne'] at this
 have hleft_cont:ContinuousOn (fun y:ℝ=>K_base (((-δ : ℝ):ℂ)+(y:ℂ)*I)) (Set.Icc (-R) R):=by
  refine hK_cont.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
   fun y hy=>?_
  refine ⟨hrect ⟨⟨by simp,by simp;linarith⟩,by simpa using hy⟩,?_⟩
  intro h;have:=congrArg Complex.re h;simp [hδ.ne'] at this
 obtain ⟨M₁,hM₁⟩:=isCompact_Icc.exists_bound_of_continuousOn hbot_cont
 obtain ⟨M₂,hM₂⟩:=isCompact_Icc.exists_bound_of_continuousOn htop_cont
 obtain ⟨M₃,hM₃⟩:=isCompact_Icc.exists_bound_of_continuousOn hleft_cont
 let M:ℝ:=max 1 (max M₁ (max M₂ M₃))
 have hM_pos:0< M:=lt_of_lt_of_le one_pos (le_max_left _ _)
 have hM₁_le:∀ x∈Set.Icc (-δ) 0,‖K_base ((x:ℂ)+((-R:ℝ):ℂ)*I)‖ ≤ M:=fun x hx =>
  (hM₁ x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
 have hM₂_le:∀ x∈Set.Icc (-δ) 0,‖K_base ((x:ℂ)+(R:ℂ)*I)‖ ≤ M:=fun x hx =>
  (hM₂ x hx).trans (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
 have hM₃_le:∀ y∈Set.Icc (-R) R,‖K_base (((-δ : ℝ):ℂ)+(y:ℂ)*I)‖ ≤ M:=fun y hy =>
  (hM₃ y hy).trans (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
 have hmain:∀ T:ℝ,0< T →
   ‖G 0-z119 f T 0‖ ≤ 2*B/R+(M / π)*(R*Real.exp (-δ*T)+1/T):=by
  intro T hT
  let H_G:ℂ→ ℂ:=fun z=>G z*Complex.exp (z*(T:ℂ))*(1/z+z/(R:ℂ)^2)
  let H_g:ℂ→ ℂ:=fun z=>z119 f T z*Complex.exp (z*(T:ℂ))*(1/z+z/(R:ℂ)^2)
  have hG_eq:=z51 (T:=T) hR hδ hU_open hrect hG_diff
  have hg_eq:=z45 hB hR hT.le hf_meas hf_bound
  have hsub_eq :
    (2*(π : ℂ)*I)*(G 0-z119 f T 0) =
    ((∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*H_G (R*Complex.exp ((θ : ℂ)*I))) -
     (∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*H_g (R*Complex.exp ((θ : ℂ)*I)))) -
    (∫ θ : ℝ in (π / 2)..(3*π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*H_g (R*Complex.exp ((θ : ℂ)*I))) -
    (-(∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+((-R:ℝ):ℂ)*I)) +
      I*(∫ y:ℝ in (-R)..R,H_G (((-δ : ℝ):ℂ)+(y:ℂ)*I)) +
      (∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+(R:ℂ)*I))):=by
   linear_combination hG_eq-hg_eq
  have hterm1 :
    ‖(∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*H_G (R*Complex.exp ((θ : ℂ)*I))) -
     (∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*H_g (R*Complex.exp ((θ : ℂ)*I)))‖ ≤
    2*π*B/R:=by
   have hmap:Continuous (fun θ : ℝ=>(R:ℂ)*Complex.exp ((θ : ℂ)*I)):=
    continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
   have hmap_ne:∀ θ : ℝ,(R:ℂ)*Complex.exp ((θ : ℂ)*I)≠0:=fun θ =>
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (Complex.exp_ne_zero _)
   have hG_int:IntervalIntegrable
      (fun θ : ℝ=>(I*(R*Complex.exp ((θ : ℂ)*I)))*H_G (R*Complex.exp ((θ : ℂ)*I)))
      volume (-π / 2) (π / 2):=by
    refine ContinuousOn.intervalIntegrable ?_
    have hH_cont:ContinuousOn H_G (U \ {0}):=fun z ⟨hzU,hz0⟩ =>
      (((hG_diff.differentiableAt (hU_open.mem_nhds hzU)).continuousAt.mul
       ((continuous_id.mul continuous_const).cexp.continuousAt)).mul
       ((continuousAt_const.div continuousAt_id hz0).add (continuousAt_id.div_const _))).continuousWithinAt
    refine (continuous_const.mul hmap).continuousOn.mul (hH_cont.comp hmap.continuousOn fun θ hθ=>?_)
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
    refine ⟨hrect ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,hmap_ne θ⟩
    ·
      rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
       Complex.exp_ofReal_mul_I_re]
      linarith [mul_nonneg hR.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1],hθ.2⟩)]
    ·
      rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
       Complex.exp_ofReal_mul_I_re]
      nlinarith [Real.cos_le_one θ]
    ·
      rw [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
       Complex.exp_ofReal_mul_I_im]
      nlinarith [Real.neg_one_le_sin θ]
    ·
      rw [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
       Complex.exp_ofReal_mul_I_im]
      nlinarith [Real.sin_le_one θ]
   have hg_int:IntervalIntegrable
      (fun θ : ℝ=>(I*(R*Complex.exp ((θ : ℂ)*I)))*H_g (R*Complex.exp ((θ : ℂ)*I)))
      volume (-π / 2) (π / 2):=by
    have hcont:Continuous
       (fun θ : ℝ=>(I*(R*Complex.exp ((θ : ℂ)*I)))*H_g (R*Complex.exp ((θ : ℂ)*I))):=
      (continuous_const.mul hmap).mul
       ((((z69 hB hf_meas hf_bound hT.le).continuous.comp hmap).mul
        (Complex.continuous_exp.comp (hmap.mul continuous_const))).mul
        ((continuous_const.div hmap hmap_ne).add (hmap.div_const _)))
    exact hcont.intervalIntegrable _ _
   rw [← intervalIntegral.integral_sub hG_int hg_int]
   have hb:=intervalIntegral.norm_integral_le_of_norm_le_const (C:=2*B/R)
    (a:=-π / 2) (b:=π / 2)
    (f:=fun θ : ℝ =>
      (I*(R*Complex.exp ((θ : ℂ)*I)))*H_G (R*Complex.exp ((θ : ℂ)*I)) -
      (I*(R*Complex.exp ((θ : ℂ)*I)))*H_g (R*Complex.exp ((θ : ℂ)*I)))
    (fun θ hθ=>?_)
   ·
    calc _ ≤ (2*B/R) * |π / 2 - -π / 2|:=hb
      _=2*π*B/R:=by
        rw [show π / 2 - -π / 2=π by ring,abs_of_pos Real.pi_pos]
        ring
   ·
    rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hθ
    set z:ℂ:=(R:ℂ)*Complex.exp ((θ : ℂ)*I)
    have hfact :
       (I*z)*H_G z-(I*z)*H_g z =
       (G z-z119 f T z)*Complex.exp (z*(T:ℂ)) *
        ((I*z)*(1/z+z/(R:ℂ)^2)):=by
      simp only [H_G,H_g];ring
    rw [hfact,norm_mul,norm_mul,z138 R θ hR]
    rcases eq_or_lt_of_le (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1],hθ.2⟩) with hcos0 | hcos_pos
    ·
      rw [← hcos0,abs_zero,mul_zero,mul_zero]
      positivity
    ·
      have hz_re:z.re=R*Real.cos θ:=by
       simp [z,Complex.mul_re,Complex.exp_ofReal_mul_I_re]
      have hz_re_pos:0< z.re:=by rw [hz_re];positivity
      have htail:G z-z119 f T z =
        ∫ t in Set.Ioi T,(f t:ℂ)*Complex.exp (-z*(t:ℂ)):=by
       rw [hG_lap z hz_re_pos,z119,intervalIntegral.integral_of_le hT.le]
       have hunion:Set.Ioi (0:ℝ)=Set.Ioc 0 T ∪ Set.Ioi T:=by
        ext t
        simp only [Set.mem_Ioi,Set.mem_union,Set.mem_Ioc]
        constructor
        ·
         intro ht
         rcases le_or_gt t T with hle | hgt
         ·
          exact Or.inl ⟨ht,hle⟩
         ·
          exact Or.inr hgt
        ·
         rintro (⟨ht,_⟩ | ht)
         ·
          exact ht
         ·
          exact hT.trans ht
       have hdisj:Disjoint (Set.Ioc (0:ℝ) T) (Set.Ioi T):=
        Set.disjoint_left.mpr fun t ht1 ht2=>not_lt_of_ge ht1.2 ht2
       have hint_all:IntegrableOn (fun t:ℝ=>(f t:ℂ)*Complex.exp (-z*(t:ℂ)))
         (Set.Ioi (0:ℝ)) volume:=by
        have hmeas:AEStronglyMeasurable (fun t:ℝ=>(f t:ℂ)*Complex.exp (-z*(t:ℂ)))
          (volume.restrict (Set.Ioi (0:ℝ))):=
         ((Complex.continuous_ofReal.measurable.comp hf_meas).mul
          (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable).aestronglyMeasurable
        have hdom:IntegrableOn (fun t:ℝ=>B*Real.exp ((-z.re)*t)) (Set.Ioi (0:ℝ)) volume:=
         (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hz_re_pos) 0).const_mul B
        refine hdom.mono' hmeas ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp]
        have hre:(-z*(t:ℂ)).re=(-z.re)*t:=by simp
        rw [hre]
        exact mul_le_mul_of_nonneg_right (hf_bound t ht.le) (Real.exp_nonneg _)
       rw [hunion,setIntegral_union hdisj measurableSet_Ioi
        (hint_all.mono_set (by rw [hunion];exact Set.subset_union_left))
        (hint_all.mono_set (by rw [hunion];exact Set.subset_union_right)),
        add_sub_cancel_left]
      have htail_norm:‖G z-z119 f T z‖ ≤ B*Real.exp (-z.re*T)/z.re:=by
       rw [htail]
       have hdom:IntegrableOn (fun t:ℝ=>B*Real.exp ((-z.re)*t)) (Set.Ioi T) volume:=
        (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hz_re_pos) T).const_mul B
       have hle:‖∫ t in Set.Ioi T,(f t:ℂ)*Complex.exp (-z*(t:ℂ))‖ ≤
         ∫ t in Set.Ioi T,B*Real.exp ((-z.re)*t):=by
        refine (norm_integral_le_integral_norm _).trans ?_
        refine setIntegral_mono_on ?_ hdom measurableSet_Ioi fun t ht=>?_
        ·
         have hmeas:AEStronglyMeasurable (fun t:ℝ=>(f t:ℂ)*Complex.exp (-z*(t:ℂ)))
           (volume.restrict (Set.Ioi T)):=
          ((Complex.continuous_ofReal.measurable.comp hf_meas).mul
           (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable).aestronglyMeasurable
         exact (hdom.mono' hmeas (by
           filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
           rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp]
           have:(-z*(u:ℂ)).re=(-z.re)*u:=by simp
           rw [this]
           exact mul_le_mul_of_nonneg_right (hf_bound u (hT.trans hu).le) (Real.exp_nonneg _))).norm
        ·
         rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp]
         have:(-z*(t:ℂ)).re=(-z.re)*t:=by simp
         rw [this]
         exact mul_le_mul_of_nonneg_right (hf_bound t (hT.trans ht).le) (Real.exp_nonneg _)
       have hreal_int:∫ t in Set.Ioi T,B*Real.exp ((-z.re)*t) =
         B*Real.exp (-z.re*T)/z.re:=by
        rw [integral_const_mul]
        have h:=congrArg Complex.re
         (z108 (z:=(z.re:ℂ)) (by simpa using hz_re_pos) T)
        have hre_int:(∫ t in Set.Ioi T,Complex.exp (-(z.re:ℂ)*(t:ℂ))).re =
          ∫ t in Set.Ioi T,Real.exp ((-z.re)*t):=by
         have hc:=Complex.reCLM.integral_comp_comm
          (z104 (z:=(z.re:ℂ)) (by simpa using hz_re_pos) T)
         have h1:(∫ t in Set.Ioi T,Complex.reCLM (Complex.exp (-(z.re:ℂ)*(t:ℂ)))) =
           ∫ t in Set.Ioi T,Real.exp ((-z.re)*t):=by
          congr 1 with t
          rw [Complex.reCLM_apply,
           show -(z.re:ℂ)*(t:ℂ)=(((-z.re)*t:ℝ):ℂ) by push_cast;ring,
           ← Complex.ofReal_exp,Complex.ofReal_re]
         rw [← h1,hc,Complex.reCLM_apply]
        rw [hre_int] at h
        rw [h,show -(z.re:ℂ)*(T:ℂ)=(((-z.re)*T:ℝ):ℂ) by push_cast;ring,
         ← Complex.ofReal_exp,← Complex.ofReal_div,Complex.ofReal_re]
        ring
       exact hle.trans_eq hreal_int
      have hexp_norm:‖Complex.exp (z*(T:ℂ))‖=Real.exp (z.re*T):=by
       rw [Complex.norm_exp];simp
      rw [hexp_norm,abs_of_pos hcos_pos]
      calc
       ‖G z-z119 f T z‖*Real.exp (z.re*T)*(2*Real.cos θ)
        ≤ (B*Real.exp (-z.re*T)/z.re)*Real.exp (z.re*T)*(2*Real.cos θ):=by
         gcongr
       _=2*B/R:=by
         rw [hz_re]
         have hexp_cancel:Real.exp (-(R*Real.cos θ)*T)*Real.exp (R*Real.cos θ*T)=1:=by
          rw [← Real.exp_add];simp
         have:(B*Real.exp (-(R*Real.cos θ)*T)/(R*Real.cos θ)) *
           Real.exp (R*Real.cos θ*T)*(2*Real.cos θ) =
           (B*(Real.exp (-(R*Real.cos θ)*T)*Real.exp (R*Real.cos θ*T)) *
            (2*Real.cos θ))/(R*Real.cos θ):=by ring
         rw [this,hexp_cancel,mul_one]
         field_simp [hR.ne',hcos_pos.ne']
  have hterm2 :
    ‖∫ θ : ℝ in (π / 2)..(3*π / 2),
      (I*(R*Complex.exp ((θ : ℂ)*I)))*H_g (R*Complex.exp ((θ : ℂ)*I))‖ ≤
    2*π*B/R:=by
   have hb:=intervalIntegral.norm_integral_le_of_norm_le_const (C:=2*B/R)
    (a:=π / 2) (b:=3*π / 2)
    (f:=fun θ : ℝ =>
      (I*(R*Complex.exp ((θ : ℂ)*I)))*H_g (R*Complex.exp ((θ : ℂ)*I)))
    (fun θ hθ=>?_)
   ·
    calc _ ≤ (2*B/R) * |3*π / 2 - π / 2|:=hb
      _=2*π*B/R:=by
        rw [show 3*π / 2 - π / 2=π by ring,abs_of_pos Real.pi_pos]
        ring
   ·
    rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hθ
    set z:ℂ:=(R:ℂ)*Complex.exp ((θ : ℂ)*I)
    have hfact :
       (I*z)*H_g z =
       z119 f T z*Complex.exp (z*(T:ℂ)) *
        ((I*z)*(1/z+z/(R:ℂ)^2)):=by
      simp only [H_g];ring
    rw [hfact,norm_mul,norm_mul,z138 R θ hR]
    have hcos_nonpos:Real.cos θ ≤ 0:=by
      have hθ':θ - π∈Set.Icc (-(π / 2)) (π / 2):=⟨by linarith [hθ.1],by linarith [hθ.2]⟩
      have h:=Real.cos_nonneg_of_mem_Icc hθ'
      rw [Real.cos_sub_pi] at h
      linarith
    rcases eq_or_lt_of_le hcos_nonpos with hcos0 | hcos_neg
    ·
      rw [hcos0,abs_zero,mul_zero,mul_zero]
      positivity
    ·
      have hz_re:z.re=R*Real.cos θ:=by
       simp [z,Complex.mul_re,Complex.exp_ofReal_mul_I_re]
      have hz_re_neg:z.re< 0:=by
       rw [hz_re]
       exact mul_neg_of_pos_of_neg hR hcos_neg
      have hpos_a:0 < -z.re:=neg_pos.mpr hz_re_neg
      have hg_norm:‖z119 f T z‖ ≤ B*Real.exp (-z.re*T)/(-z.re):=by
       unfold z119
       have hle:‖∫ t:ℝ in (0:ℝ)..T,(f t:ℂ)*Complex.exp (-z*(t:ℂ))‖ ≤
         ∫ t:ℝ in (0:ℝ)..T,B*Real.exp ((-z.re)*t):=by
        refine intervalIntegral.norm_integral_le_of_norm_le hT.le ?_ ?_
        ·
         refine Filter.Eventually.of_forall fun t ht=>?_
         rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp]
         have:(-z*(t:ℂ)).re=(-z.re)*t:=by simp
         rw [this]
         exact mul_le_mul_of_nonneg_right (hf_bound t ht.1.le) (Real.exp_nonneg _)
        ·
         exact (continuous_const.mul (Real.continuous_exp.comp
          (continuous_const.mul continuous_id))).intervalIntegrable _ _
       have hcalc:∫ t:ℝ in (0:ℝ)..T,B*Real.exp ((-z.re)*t) =
         B*(Real.exp ((-z.re)*T)-1)/(-z.re):=by
        rw [intervalIntegral.integral_const_mul]
        have hftc:∫ t:ℝ in (0:ℝ)..T,Real.exp ((-z.re)*t) =
          Real.exp ((-z.re)*T)/(-z.re)-Real.exp ((-z.re)*0)/(-z.re):=by
         refine intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f:=fun x:ℝ=>Real.exp ((-z.re)*x)/(-z.re)) (fun t _=>?_) ?_
         ·
          have h1:HasDerivAt (fun x:ℝ=>(-z.re)*x) (-z.re) t:=by
           simpa using (hasDerivAt_id t).const_mul (-z.re)
          have h2:=(h1.exp).div_const (-z.re)
          have heq:Real.exp ((-z.re)*t)*(-z.re)/(-z.re)=Real.exp ((-z.re)*t):=
           mul_div_cancel_right₀ _ hpos_a.ne'
          exact heq ▸ h2
         ·
          exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
        rw [hftc,mul_zero,Real.exp_zero]
        ring
       rw [hcalc] at hle
       refine hle.trans ?_
       gcongr
       linarith
      have hexp_norm:‖Complex.exp (z*(T:ℂ))‖=Real.exp (z.re*T):=by
       rw [Complex.norm_exp];simp
      rw [hexp_norm,abs_of_neg hcos_neg]
      calc
       ‖z119 f T z‖*Real.exp (z.re*T)*(2*-Real.cos θ)
        ≤ (B*Real.exp (-z.re*T)/(-z.re))*Real.exp (z.re*T)*(2*-Real.cos θ):=by
         gcongr
         linarith
       _=2*B/R:=by
         rw [hz_re]
         have hexp_cancel:Real.exp (-(R*Real.cos θ)*T)*Real.exp (R*Real.cos θ*T)=1:=by
          rw [← Real.exp_add];simp
         have:(B*Real.exp (-(R*Real.cos θ)*T) / -(R*Real.cos θ)) *
           Real.exp (R*Real.cos θ*T)*(2*-Real.cos θ) =
           (B*(Real.exp (-(R*Real.cos θ)*T)*Real.exp (R*Real.cos θ*T)) *
            (2*-Real.cos θ))/(R*-Real.cos θ):=by ring
         rw [this,hexp_cancel,mul_one]
         field_simp [hR.ne',hcos_neg.ne]
  have hbot_norm:‖∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+((-R:ℝ):ℂ)*I)‖ ≤ M/T:=by
   have hle:‖∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+((-R:ℝ):ℂ)*I)‖ ≤
      ∫ x:ℝ in (-δ)..0,M*Real.exp (x*T):=by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_ ?_
    ·
      refine Filter.Eventually.of_forall fun x hx=>?_
      have hfact:H_G ((x:ℂ)+((-R:ℝ):ℂ)*I) =
        K_base ((x:ℂ)+((-R:ℝ):ℂ)*I) *
         Complex.exp (((x:ℂ)+((-R:ℝ):ℂ)*I)*(T:ℂ)):=by
       simp only [H_G,K_base];ring
      rw [hfact,norm_mul,Complex.norm_exp]
      have hre:(((x:ℂ)+((-R:ℝ):ℂ)*I)*(T:ℂ)).re=x*T:=by simp
      rw [hre]
      exact mul_le_mul_of_nonneg_right (hM₁_le x ⟨hx.1.le,hx.2⟩) (Real.exp_nonneg _)
    ·
      exact (continuous_const.mul (Real.continuous_exp.comp
       (continuous_id.mul continuous_const))).intervalIntegrable _ _
   have hcalc:∫ x:ℝ in (-δ)..0,M*Real.exp (x*T)=M*(1-Real.exp (-δ*T))/T:=by
    rw [intervalIntegral.integral_const_mul]
    have hftc:∫ x:ℝ in (-δ)..0,Real.exp (x*T) =
       Real.exp (0*T)/T-Real.exp ((-δ)*T)/T:=by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
       (f:=fun u:ℝ=>Real.exp (u*T)/T) (fun x _=>?_) ?_
      ·
       have h1:HasDerivAt (fun u:ℝ=>u*T) T x:=by
        simpa using (hasDerivAt_id x).mul_const T
       have h2:=(h1.exp).div_const T
       have heq:Real.exp (x*T)*T/T=Real.exp (x*T):=mul_div_cancel_right₀ _ hT.ne'
       exact heq ▸ h2
      ·
       exact (Real.continuous_exp.comp (continuous_id.mul continuous_const)).intervalIntegrable _ _
    rw [hftc,zero_mul,Real.exp_zero]
    ring
   rw [hcalc] at hle
   refine hle.trans ?_
   have:1-Real.exp (-δ*T) ≤ 1:=by linarith [Real.exp_nonneg (-δ*T)]
   calc
    M*(1-Real.exp (-δ*T))/T ≤ M*1/T:=by gcongr
    _=M/T:=by ring
  have htop_norm:‖∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+(R:ℂ)*I)‖ ≤ M/T:=by
   have hle:‖∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+(R:ℂ)*I)‖ ≤
      ∫ x:ℝ in (-δ)..0,M*Real.exp (x*T):=by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_ ?_
    ·
      refine Filter.Eventually.of_forall fun x hx=>?_
      have hfact:H_G ((x:ℂ)+(R:ℂ)*I) =
        K_base ((x:ℂ)+(R:ℂ)*I) *
         Complex.exp (((x:ℂ)+(R:ℂ)*I)*(T:ℂ)):=by
       simp only [H_G,K_base];ring
      rw [hfact,norm_mul,Complex.norm_exp]
      have hre:(((x:ℂ)+(R:ℂ)*I)*(T:ℂ)).re=x*T:=by simp
      rw [hre]
      exact mul_le_mul_of_nonneg_right (hM₂_le x ⟨hx.1.le,hx.2⟩) (Real.exp_nonneg _)
    ·
      exact (continuous_const.mul (Real.continuous_exp.comp
       (continuous_id.mul continuous_const))).intervalIntegrable _ _
   have hcalc:∫ x:ℝ in (-δ)..0,M*Real.exp (x*T)=M*(1-Real.exp (-δ*T))/T:=by
    rw [intervalIntegral.integral_const_mul]
    have hftc:∫ x:ℝ in (-δ)..0,Real.exp (x*T) =
       Real.exp (0*T)/T-Real.exp ((-δ)*T)/T:=by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
       (f:=fun u:ℝ=>Real.exp (u*T)/T) (fun x _=>?_) ?_
      ·
       have h1:HasDerivAt (fun u:ℝ=>u*T) T x:=by
        simpa using (hasDerivAt_id x).mul_const T
       have h2:=(h1.exp).div_const T
       have heq:Real.exp (x*T)*T/T=Real.exp (x*T):=mul_div_cancel_right₀ _ hT.ne'
       exact heq ▸ h2
      ·
       exact (Real.continuous_exp.comp (continuous_id.mul continuous_const)).intervalIntegrable _ _
    rw [hftc,zero_mul,Real.exp_zero]
    ring
   rw [hcalc] at hle
   refine hle.trans ?_
   have:1-Real.exp (-δ*T) ≤ 1:=by linarith [Real.exp_nonneg (-δ*T)]
   calc
    M*(1-Real.exp (-δ*T))/T ≤ M*1/T:=by gcongr
    _=M/T:=by ring
  have hleft_norm:‖I*(∫ y:ℝ in (-R)..R,H_G (((-δ : ℝ):ℂ)+(y:ℂ)*I))‖ ≤
    2*R*M*Real.exp (-δ*T):=by
   rw [norm_mul,Complex.norm_I,one_mul]
   have hb:=intervalIntegral.norm_integral_le_of_norm_le_const (C:=M*Real.exp (-δ*T))
    (a:=-R) (b:=R) (f:=fun y:ℝ=>H_G (((-δ : ℝ):ℂ)+(y:ℂ)*I)) (fun y hy=>by
      rw [Set.uIoc_of_le (by linarith)] at hy
      have hfact:H_G (((-δ : ℝ):ℂ)+(y:ℂ)*I) =
        K_base (((-δ : ℝ):ℂ)+(y:ℂ)*I) *
         Complex.exp ((((-δ : ℝ):ℂ)+(y:ℂ)*I)*(T:ℂ)):=by
       simp only [H_G,K_base];ring
      rw [hfact,norm_mul,Complex.norm_exp]
      have hre:((((-δ : ℝ):ℂ)+(y:ℂ)*I)*(T:ℂ)).re=-δ*T:=by simp
      rw [hre]
      exact mul_le_mul_of_nonneg_right (hM₃_le y ⟨hy.1.le,hy.2⟩) (Real.exp_nonneg _))
   calc
    _ ≤ M*Real.exp (-δ*T) * |R - -R|:=hb
    _=2*R*M*Real.exp (-δ*T):=by
       rw [show R - -R=2*R by ring,abs_of_pos (by linarith)]
       ring
  have hterm3 :
    ‖-(∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+((-R:ℝ):ℂ)*I)) +
      I*(∫ y:ℝ in (-R)..R,H_G (((-δ : ℝ):ℂ)+(y:ℂ)*I)) +
      (∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+(R:ℂ)*I))‖ ≤
    2*R*M*Real.exp (-δ*T)+2*M/T:=by
   have h1:=norm_add_le
    (-(∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+((-R:ℝ):ℂ)*I)) +
      I*(∫ y:ℝ in (-R)..R,H_G (((-δ : ℝ):ℂ)+(y:ℂ)*I)))
    (∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+(R:ℂ)*I))
   have h2:=norm_add_le
    (-(∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+((-R:ℝ):ℂ)*I)))
    (I*(∫ y:ℝ in (-R)..R,H_G (((-δ : ℝ):ℂ)+(y:ℂ)*I)))
   rw [norm_neg] at h2
   have h2MT:M/T+M/T=2*M/T:=by ring
   linarith
  have htotal:‖(2*(π : ℂ)*I)*(G 0-z119 f T 0)‖ ≤
    4*π*B/R+2*R*M*Real.exp (-δ*T)+2*M/T:=by
   rw [hsub_eq]
   have h1:=norm_sub_le
    (((∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*H_G (R*Complex.exp ((θ : ℂ)*I))) -
     (∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*H_g (R*Complex.exp ((θ : ℂ)*I)))) -
    (∫ θ : ℝ in (π / 2)..(3*π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*H_g (R*Complex.exp ((θ : ℂ)*I))))
    (-(∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+((-R:ℝ):ℂ)*I)) +
      I*(∫ y:ℝ in (-R)..R,H_G (((-δ : ℝ):ℂ)+(y:ℂ)*I)) +
      (∫ x:ℝ in (-δ)..0,H_G ((x:ℂ)+(R:ℂ)*I)))
   have h2:=norm_sub_le
    ((∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*H_G (R*Complex.exp ((θ : ℂ)*I))) -
     (∫ θ : ℝ in (-π / 2)..(π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*H_g (R*Complex.exp ((θ : ℂ)*I))))
    (∫ θ : ℝ in (π / 2)..(3*π / 2),(I*(R*Complex.exp ((θ : ℂ)*I)))*H_g (R*Complex.exp ((θ : ℂ)*I)))
   have h4pi:2*π*B/R+2*π*B/R=4*π*B/R:=by ring
   linarith
  have hnorm_lhs:‖(2*(π : ℂ)*I)*(G 0-z119 f T 0)‖ =
    (2*π)*‖G 0-z119 f T 0‖:=by
   rw [norm_mul,norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_I,mul_one]
  rw [hnorm_lhs] at htotal
  have h2pi:0< 2*π:=by positivity
  rw [← le_div_iff₀' h2pi] at htotal
  refine htotal.trans_eq ?_
  field_simp [Real.pi_pos.ne']
  ring
 have htail_tend:Tendsto (fun T:ℝ=>(M / π)*(R*Real.exp (-δ*T)+1/T)) atTop (𝓝 0):=by
  have h1:Tendsto (fun T:ℝ=>R*Real.exp (-δ*T)) atTop (𝓝 0):=by
   have hexp:=Real.tendsto_exp_atBot.comp
    (Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hδ) tendsto_id)
   simpa using hexp.const_mul R
  have h2:Tendsto (fun T:ℝ=>(1:ℝ)/T) atTop (𝓝 0):=
   tendsto_const_nhds.div_atTop tendsto_id
  simpa using (h1.add h2).const_mul (M / π)
 have hev:=(tendsto_order.mp htail_tend).2 (η / 2) (half_pos hη)
 rw [Filter.eventually_atTop] at hev
 obtain ⟨T₁,hT₁⟩:=hev
 refine ⟨max 1 T₁,fun T hT=>?_⟩
 have hT_pos:0< T:=lt_of_lt_of_le one_pos ((le_max_left 1 T₁).trans hT)
 have hT_ge:T₁ ≤ T:=(le_max_right 1 T₁).trans hT
 rw [dist_comm,dist_eq_norm]
 calc
  ‖G 0-z119 f T 0‖
   ≤ 2*B/R+(M / π)*(R*Real.exp (-δ*T)+1/T):=hmain T hT_pos
  _ < η / 2+η / 2:=add_lt_add hBR (hT₁ T hT_ge)
  _=η:=add_halves η
private lemma z78 (a b:ℝ):IntervalIntegrable f_psi volume a b:=by
 have hmono:Monotone (fun t:ℝ=>Chebyshev.psi (Real.exp t)):=
  Chebyshev.psi_mono.comp Real.exp_monotone
 have h1:IntervalIntegrable (fun t:ℝ=>Chebyshev.psi (Real.exp t)) volume a b:=
  hmono.intervalIntegrable
 have h2:Continuous (fun t:ℝ=>Real.exp (-t)):=
  Real.continuous_exp.comp continuous_neg
 have hprod:IntervalIntegrable (fun t:ℝ=>Real.exp (-t)*Chebyshev.psi (Real.exp t)) volume a b:=by
  simpa only [mul_comm] using h1.continuousOn_mul h2.continuousOn
 exact hprod.sub intervalIntegrable_const
private lemma z268 :
  Tendsto (fun T:ℝ=>∫ t in (0:ℝ)..T,f_psi t) atTop (𝓝 (G_fun 0).re):=by
 have hB:(0:ℝ)< Real.log 4+4:=by
  have:0 ≤ Real.log 4:=Real.log_nonneg (by norm_num)
  linarith
 have htend_c:Tendsto (fun T:ℝ=>z119 f_psi T 0) atTop (𝓝 (G_fun 0)):=
  z133 hB z79 (fun t _=>z77)
   z118 z248 z68 (fun z hz=>z9 hz)
 have hre:=(Complex.continuous_re.tendsto (G_fun 0)).comp htend_c
 refine hre.congr fun T=>?_
 simp only [Function.comp_apply,z119,neg_zero,zero_mul,Complex.exp_zero,mul_one]
 rw [intervalIntegral.integral_ofReal,Complex.ofReal_re]
lemma z246 (ε : ℝ) (hε : 0 < ε) :
  ∀ᶠ x:ℝ in atTop,Chebyshev.psi x ≤ (1+ε)*x:=by
 have htend:=z268
 set δ : ℝ:=Real.log (1+ε / 2)
 have hδ_pos:0 < δ:=Real.log_pos (by linarith)
 have hexp_δ : Real.exp δ=1+ε / 2:=Real.exp_log (by linarith)
 set c:ℝ:=(1+ε)/(1+ε / 2)-1
 have hc_pos:0< c:=by
  have hden:0< 1+ε / 2:=by linarith
  rw [sub_pos,one_lt_div hden]
  linarith
 have hcδ : 0< c*δ / 2:=by positivity
 rw [Metric.tendsto_atTop] at htend
 obtain ⟨T₀,hT₀⟩:=htend (c*δ / 2) hcδ
 have hx_ev:∀ᶠ x:ℝ in atTop,1 ≤ x∧T₀ ≤ Real.log x:=
  (eventually_ge_atTop (1:ℝ)).and
   (Real.tendsto_log_atTop.eventually (eventually_ge_atTop T₀))
 filter_upwards [hx_ev] with x ⟨hx1,hx_log⟩
 by_contra! hgt
 set T:ℝ:=Real.log x
 have hx_pos:(0:ℝ)< x:=by linarith
 have hexp_T:Real.exp T=x:=Real.exp_log hx_pos
 have hint_upper:(∫ t in T..(T+δ),f_psi t)< c*δ:=by
  have hadd:=intervalIntegral.integral_add_adjacent_intervals
   (z78 0 T) (z78 T (T+δ))
  have hdiff:∫ t in T..(T+δ),f_psi t =
    (∫ t in (0:ℝ)..(T+δ),f_psi t)-(∫ t in (0:ℝ)..T,f_psi t):=by linarith
  rw [hdiff]
  have h1:=hT₀ (T+δ) (by linarith)
  have h2:=hT₀ T hx_log
  rw [Real.dist_eq] at h1 h2
  linarith [le_abs_self ((∫ t in (0:ℝ)..(T+δ),f_psi t)-(G_fun 0).re),
   neg_le_abs ((∫ t in (0:ℝ)..T,f_psi t)-(G_fun 0).re)]
 have hint_lower:c*δ ≤ ∫ t in T..(T+δ),f_psi t:=by
  have hconst:∫ _ in T..(T+δ),c=c*δ:=by simp [smul_eq_mul,mul_comm]
  rw [← hconst]
  refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
   (z78 T (T+δ)) fun t ht=>?_
  have hexp_ge:x ≤ Real.exp t:=by rw [← hexp_T];exact Real.exp_le_exp.mpr ht.1
  have hexp_le:Real.exp t ≤ x*(1+ε / 2):=by
   calc
    Real.exp t ≤ Real.exp (T+δ):=Real.exp_le_exp.mpr ht.2
    _=Real.exp T*Real.exp δ:=Real.exp_add T δ
    _=x*(1+ε / 2):=by rw [hexp_T,hexp_δ]
  have hpsi_ge:(1+ε)*x ≤ Chebyshev.psi (Real.exp t):=
   hgt.le.trans (Chebyshev.psi_mono hexp_ge)
  unfold f_psi
  rw [Real.exp_neg,inv_mul_eq_div]
  have hden_pos:0< x*(1+ε / 2):=by positivity
  have h1:(1+ε)/(1+ε / 2)=((1+ε)*x)/(x*(1+ε / 2)):=by
   field_simp [hx_pos.ne']
  have h2:((1+ε)*x)/(x*(1+ε / 2)) ≤ Chebyshev.psi (Real.exp t)/Real.exp t:=by
   calc
    ((1+ε)*x)/(x*(1+ε / 2))
     ≤ ((1+ε)*x)/Real.exp t:=
      div_le_div_of_nonneg_left (by positivity) (Real.exp_pos t) hexp_le
    _ ≤ Chebyshev.psi (Real.exp t)/Real.exp t:=
      div_le_div_of_nonneg_right hpsi_ge (Real.exp_nonneg t)
  linarith [h1,h2]
 linarith
lemma z245 (ε : ℝ) (hε : 0 < ε) :
  ∀ᶠ x:ℝ in atTop,(1 - ε)*x ≤ Chebyshev.psi x:=by
 by_cases hε1:1 ≤ ε
 ·
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  have hnonneg:0 ≤ Chebyshev.psi x:=Chebyshev.psi_nonneg x
  nlinarith
 push Not at hε1
 have htend:=z268
 set δ : ℝ:=-Real.log (1 - ε / 2)
 have h1m:0< 1 - ε / 2:=by linarith
 have hδ_pos:0 < δ:=by
  have:Real.log (1 - ε / 2)< 0:=Real.log_neg h1m (by linarith)
  linarith
 have hexp_neg_δ : Real.exp (-δ)=1 - ε / 2:=by
  simp only [δ,neg_neg]
  exact Real.exp_log h1m
 set c:ℝ:=1-(1 - ε)/(1 - ε / 2)
 have hc_pos:0< c:=by
  rw [sub_pos,div_lt_one h1m]
  linarith
 have hcδ : 0< c*δ / 2:=by positivity
 rw [Metric.tendsto_atTop] at htend
 obtain ⟨T₀,hT₀⟩:=htend (c*δ / 2) hcδ
 have hx_ev:∀ᶠ x:ℝ in atTop,1 ≤ x∧T₀+δ ≤ Real.log x:=
  (eventually_ge_atTop (1:ℝ)).and
   (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (T₀+δ)))
 filter_upwards [hx_ev] with x ⟨hx1,hx_log⟩
 by_contra! hlt
 set T:ℝ:=Real.log x
 have hx_pos:(0:ℝ)< x:=by linarith
 have hexp_T:Real.exp T=x:=Real.exp_log hx_pos
 have hint_lower:-(c*δ) < ∫ t in (T - δ)..T,f_psi t:=by
  have hadd:=intervalIntegral.integral_add_adjacent_intervals
   (z78 0 (T - δ)) (z78 (T - δ) T)
  have hdiff:∫ t in (T - δ)..T,f_psi t =
    (∫ t in (0:ℝ)..T,f_psi t)-(∫ t in (0:ℝ)..(T - δ),f_psi t):=by linarith
  rw [hdiff]
  have h1:=hT₀ T (by linarith)
  have h2:=hT₀ (T - δ) (by linarith)
  rw [Real.dist_eq] at h1 h2
  linarith [neg_le_abs ((∫ t in (0:ℝ)..T,f_psi t)-(G_fun 0).re),
   le_abs_self ((∫ t in (0:ℝ)..(T - δ),f_psi t)-(G_fun 0).re)]
 have hint_upper:∫ t in (T - δ)..T,f_psi t ≤ -(c*δ):=by
  have hconst:∫ _ in (T - δ)..T,(-c)=-(c*δ):=by
   simp [smul_eq_mul];ring
  rw [← hconst]
  refine intervalIntegral.integral_mono_on (by linarith)
   (z78 (T - δ) T) intervalIntegrable_const fun t ht=>?_
  have hexp_le:Real.exp t ≤ x:=by rw [← hexp_T];exact Real.exp_le_exp.mpr ht.2
  have hexp_ge:x*(1 - ε / 2) ≤ Real.exp t:=by
   calc
    x*(1 - ε / 2)=Real.exp T*Real.exp (-δ):=by rw [hexp_T,hexp_neg_δ]
    _=Real.exp (T - δ):=by rw [← Real.exp_add,sub_eq_add_neg]
    _ ≤ Real.exp t:=Real.exp_le_exp.mpr ht.1
  have hpsi_le:Chebyshev.psi (Real.exp t) ≤ (1 - ε)*x:=
   (Chebyshev.psi_mono hexp_le).trans hlt.le
  unfold f_psi
  rw [Real.exp_neg,inv_mul_eq_div]
  have hden_pos:0< x*(1 - ε / 2):=by positivity
  have h1:(1 - ε)/(1 - ε / 2)=((1 - ε)*x)/(x*(1 - ε / 2)):=by
   field_simp [hx_pos.ne']
  have h2:Chebyshev.psi (Real.exp t)/Real.exp t ≤ ((1 - ε)*x)/(x*(1 - ε / 2)):=by
   calc
    Chebyshev.psi (Real.exp t)/Real.exp t
     ≤ ((1 - ε)*x)/Real.exp t:=
      div_le_div_of_nonneg_right hpsi_le (Real.exp_nonneg t)
    _ ≤ ((1 - ε)*x)/(x*(1 - ε / 2)):=
      div_le_div_of_nonneg_left (by nlinarith) hden_pos hexp_ge
  linarith [h1,h2]
 linarith
theorem z244:Tendsto (fun x:ℝ=>Chebyshev.psi x/x) atTop (𝓝 1):=by
 rw [Metric.tendsto_atTop]
 intro ε hε
 have hle:=z246 (ε / 2) (half_pos hε)
 have hge:=z245 (ε / 2) (half_pos hε)
 have hev:=(eventually_ge_atTop (1:ℝ)).and (hle.and hge)
 rw [Filter.eventually_atTop] at hev
 obtain ⟨X,hX⟩:=hev
 refine ⟨X,fun x hx=>?_⟩
 obtain ⟨hx1,h1,h2⟩:=hX x hx
 have hx_pos:0< x:=by linarith
 rw [Real.dist_eq,abs_lt]
 have h1':Chebyshev.psi x/x ≤ 1+ε / 2:=(div_le_iff₀ hx_pos).mpr h1
 have h2':1 - ε / 2 ≤ Chebyshev.psi x/x:=(le_div_iff₀ hx_pos).mpr h2
 constructor <;> linarith
theorem z269:Tendsto (fun x:ℝ=>Chebyshev.theta x/x) atTop (𝓝 1):=by
 obtain ⟨C,hC⟩:=Chebyshev.psi_sub_theta_le_mul_sqrt
 have hsqrt:Tendsto (fun x:ℝ=>C*Real.sqrt x/x) atTop (𝓝 0):=by
  have h1:Tendsto (fun x:ℝ=>C/Real.sqrt x) atTop (𝓝 0):=
   tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop)
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  have hsq:Real.sqrt x≠0:=(Real.sqrt_pos.mpr hx).ne'
  field_simp [hsq,hx.ne']
  rw [Real.sq_sqrt hx.le]
 have hlo:Tendsto (fun x:ℝ=>Chebyshev.psi x/x-C*Real.sqrt x/x) atTop (𝓝 1):=by
  simpa using z244.sub hsqrt
 refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo z244 ?_ ?_
 ·
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  have hdiff:=hC x
  rw [← sub_div]
  exact div_le_div_of_nonneg_right (by linarith) hx.le
 ·
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  exact div_le_div_of_nonneg_right (Chebyshev.theta_le_psi x) hx.le
theorem z124 :
  Tendsto (fun n:ℕ=>Real.log (Nat.lcmUpto n:ℝ)/(n:ℝ)) atTop (𝓝 1):=by
 have h:=z244.comp tendsto_natCast_atTop_atTop
 refine h.congr fun n=>?_
 simp [Chebyshev.psi_eq_log_lcmUpto]
end Z1
namespace Z2
open scoped BigOperators
open Finset Filter Topology
noncomputable def phi0 (x y:ℝ):ℤ:=
 3*(⌊y⌋ - ⌊(27:ℝ)*x⌋ - ⌊y-(27:ℝ)*x⌋) +
 3*(⌊(91:ℝ)*x-y⌋ - ⌊(27:ℝ)*x⌋ - ⌊(64:ℝ)*x-y⌋) +
 ∑ u∈Finset.Icc (1:ℕ) 10,
  (⌊((35-2*u:ℕ):ℝ)*x⌋ - ⌊y-((28+u:ℕ):ℝ)*x⌋ - ⌊((63-u:ℕ):ℝ)*x-y⌋)
def wtL (m:ℕ):ℕ:=
 if m=27 then 3 else if 29 ≤ m∧m ≤ 38 then 1 else 0
def z283 (m:ℕ):ℕ:=
 if m=64 then 3 else if 53 ≤ m∧m ≤ 62 then 1 else 0
def z282 (m:ℕ):ℕ:=
 if m=91 then 3 else 0
def wtR (m:ℕ):ℤ:=(z283 m:ℤ)-(z282 m:ℤ)
def all23:List ℕ:=
 [27,29,30,31,32,33,34,35,36,37,38,53,54,55,56,57,58,59,60,61,62,64,91]
def z81:List ℕ:=
 [15,17,19,21,23,25,27,29,30,31,32,33,34,35,36,37,38,
  53,54,55,56,57,58,59,60,61,62,64,91]
private lemma z83 {a y:ℝ} (hy0:0 ≤ y) (hy1:y< 1) :
  ⌊y-a⌋=-⌊a⌋ - (if y< Int.fract a then 1 else 0):=by
 have hfract:a=⌊a⌋+Int.fract a:=(Int.floor_add_fract a).symm
 have hf0:0 ≤ Int.fract a:=Int.fract_nonneg a
 have hf1:Int.fract a< 1:=Int.fract_lt_one a
 have h1:y-a=(y-Int.fract a)+(-⌊a⌋ : ℤ):=by push_cast;linarith
 rw [h1,Int.floor_add_intCast]
 split_ifs with hlt
 ·
  have hfl:⌊y-Int.fract a⌋=-1:=by
   rw [Int.floor_eq_iff];norm_num;constructor <;> linarith
  omega
 ·
  have hfl:⌊y-Int.fract a⌋=0:=by
   rw [Int.floor_eq_iff];norm_num;constructor <;> linarith
  omega
private lemma z85 {a y:ℝ} (hy0:0 ≤ y) (hy1:y< 1) :
  ⌊a-y⌋=⌊a⌋ - (if Int.fract a< y then 1 else 0):=by
 have hfract:a=⌊a⌋+Int.fract a:=(Int.floor_add_fract a).symm
 have hf0:0 ≤ Int.fract a:=Int.fract_nonneg a
 have hf1:Int.fract a< 1:=Int.fract_lt_one a
 have h1:a-y=(Int.fract a-y)+(⌊a⌋ : ℤ):=by linarith
 rw [h1,Int.floor_add_intCast]
 split_ifs with hlt
 ·
  have hfl:⌊Int.fract a-y⌋=-1:=by
   rw [Int.floor_eq_iff];norm_num;constructor <;> linarith
  omega
 ·
  have hfl:⌊Int.fract a-y⌋=0:=by
   rw [Int.floor_eq_iff];norm_num;constructor <;> linarith
  omega
noncomputable def phiC (x:ℝ):ℤ:=
 3*(⌊(91:ℝ)*x⌋ - ⌊(27:ℝ)*x⌋ - ⌊(64:ℝ)*x⌋) +
 ∑ u∈Finset.Icc (1:ℕ) 10,
  (⌊((35-2*u:ℕ):ℝ)*x⌋+⌊((28+u:ℕ):ℝ)*x⌋ - ⌊((63-u:ℕ):ℝ)*x⌋)
noncomputable def phiW (x y:ℝ):ℤ:=
 (all23.map fun (m:ℕ) =>
  (if y< Int.fract ((m:ℝ)*x) then (wtL m:ℤ) else 0) +
  (if Int.fract ((m:ℝ)*x)< y then wtR m else 0)).sum
lemma z167 {x y:ℝ} (hy0:0 ≤ y) (hy1:y< 1) :
  phi0 x y=phiC x+phiW x y:=by
 have hy_fl:⌊y⌋=0:=by rw [Int.floor_eq_iff];norm_num;exact ⟨hy0,hy1⟩
 have h1:=z83 (a:=(27:ℝ)*x) hy0 hy1
 have h2:=z85 (a:=(91:ℝ)*x) hy0 hy1
 have h3:=z85 (a:=(64:ℝ)*x) hy0 hy1
 have hsum:∑ u∈Finset.Icc (1:ℕ) 10,
   (⌊((35-2*u:ℕ):ℝ)*x⌋ - ⌊y-((28+u:ℕ):ℝ)*x⌋ - ⌊((63-u:ℕ):ℝ)*x-y⌋) =
  (∑ u∈Finset.Icc (1:ℕ) 10,
   (⌊((35-2*u:ℕ):ℝ)*x⌋+⌊((28+u:ℕ):ℝ)*x⌋ - ⌊((63-u:ℕ):ℝ)*x⌋)) +
  ∑ u∈Finset.Icc (1:ℕ) 10,
   ((if y< Int.fract (((28+u:ℕ):ℝ)*x) then (1:ℤ) else 0) +
    (if Int.fract (((63-u:ℕ):ℝ)*x)< y then (1:ℤ) else 0)):=by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _=>?_
  rw [z83 (a:=((28+u:ℕ):ℝ)*x) hy0 hy1,
     z85 (a:=((63-u:ℕ):ℝ)*x) hy0 hy1]
  ring
 unfold phi0 phiC phiW all23 wtL wtR z283 z282
 rw [hy_fl,h1,h2,h3,hsum]
 have hIcc:Finset.Icc (1:ℕ) 10={1,2,3,4,5,6,7,8,9,10}:=by decide
 rw [hIcc]
 simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,Finset.sum_singleton,
  List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
 simp only [show (27:ℕ)=27 from rfl,show ¬(29=27) from by decide,
  show ¬(30=27) from by decide,show ¬(31=27) from by decide,
  show ¬(32=27) from by decide,show ¬(33=27) from by decide,
  show ¬(34=27) from by decide,show ¬(35=27) from by decide,
  show ¬(36=27) from by decide,show ¬(37=27) from by decide,
  show ¬(38=27) from by decide,show ¬(53=27) from by decide,
  show ¬(54=27) from by decide,show ¬(55=27) from by decide,
  show ¬(56=27) from by decide,show ¬(57=27) from by decide,
  show ¬(58=27) from by decide,show ¬(59=27) from by decide,
  show ¬(60=27) from by decide,show ¬(61=27) from by decide,
  show ¬(62=27) from by decide,show ¬(64=27) from by decide,
  show ¬(91=27) from by decide]
 norm_num
 have hmul:∀ (P:Prop) [Decidable P] (c:ℤ),
   (if P then c else 0)=c*(if P then (1:ℤ) else 0):=by
  intro P _ c;split_ifs <;> ring
 rw [hmul (y< Int.fract (27*x)) 3,hmul (Int.fract (64*x)< y) 3,
   hmul (Int.fract (91*x)< y) (-3)]
 ring
structure CertEntry where
 p1:ℕ
 q1:ℕ
 p2:ℕ
 q2:ℕ
 v:ℕ
def z127 (p1 q1 p2 q2 m:ℕ):ℕ:=
 let c:=(m*p1)/q1
 m*(p1*q2+p2*q1)-c*(2*q1*q2)
def z102 (p1 q1 p2 q2:ℕ) (m:ℕ):List ℕ→ List ℕ
 | []=>[m]
 | h :: t =>
  if Nat.ble (z127 p1 q1 p2 q2 m) (z127 p1 q1 p2 q2 h) then m :: h :: t
  else h :: z102 p1 q1 p2 q2 m t
def z258 (p1 q1 p2 q2:ℕ):List ℕ→ List ℕ
 | []=>[]
 | h :: t=>z102 p1 q1 p2 q2 h (z258 p1 q1 p2 q2 t)
def z161 (p1 q1 p2 q2 m1 m2:ℕ):Bool:=
 let c1:=(m1*p1)/q1
 let c2:=(m2*p1)/q1
 let a1:=m1*p1+c2*q1
 let a2:=m2*p1+c1*q1
 let b1:=m1*p2+c2*q2
 let b2:=m2*p2+c1*q2
 Nat.ble a1 a2 && Nat.ble b1 b2 && (Nat.blt a1 a2 || Nat.blt b1 b2)
def z38 (p1 q1 p2 q2:ℕ):List ℕ→ Bool
 | []=>true
 | [_]=>true
 | m1 :: m2 :: t=>z161 p1 q1 p2 q2 m1 m2 && z38 p1 q1 p2 q2 (m2 :: t)
def z43 (v:ℕ) (pos neg accL:ℕ):List ℕ→ Bool
 | []=>Nat.ble (v+neg) (pos+accL)
 | m :: t =>
  let accL':=accL-wtL m
  Nat.ble (v+neg) (pos+accL) &&
  Nat.ble (v+neg) (pos+accL') &&
  z43 v (pos+z283 m) (neg+z282 m) accL' t
def z40 (e:CertEntry):Bool:=
 let p1:=e.p1;let q1:=e.q1;let p2:=e.p2;let q2:=e.q2
 Nat.blt 0 q1 && Nat.blt 0 q2 && Nat.blt (p1*q2) (p2*q1) &&
 Nat.ble q1 (33*p1) && Nat.ble p2 q2 &&
 z81.all (fun m=>Nat.ble (m*p2) (((m*p1)/q1+1)*q2)) &&
 let ord:=z258 p1 q1 p2 q2 all23
 z38 p1 q1 p2 q2 ord &&
 let c (m:ℕ):ℕ:=(m*p1)/q1
 let cPos:ℕ:=
  3*c 91 +
  (c 33+c 29)+(c 31+c 30)+(c 29+c 31)+(c 27+c 32)+(c 25+c 33) +
  (c 23+c 34)+(c 21+c 35)+(c 19+c 36)+(c 17+c 37)+(c 15+c 38)
 let cNeg:ℕ:=
  3*c 27+3*c 64 +
  (c 62+c 61+c 60+c 59+c 58+c 57+c 56+c 55+c 54+c 53)
 z43 e.v cPos cNeg 13 ord
def z39:List CertEntry→ Bool
 | []=>true
 | [_]=>true
 | e1 :: e2 :: t=>Nat.ble (e1.p2*e2.q1) (e2.p1*e1.q2) && z39 (e2 :: t)
def z253 (e:CertEntry):ℕ:=
 (List.range 10).foldl (fun acc k =>
  acc+(100000*e.v*(e.p2*e.q1-e.p1*e.q2))/((k*e.q1+e.p1)*(k*e.q2+e.p2))) 0
def z36:List CertEntry:=
[
 ⟨1,33,1,32,7⟩,⟨1,32,1,31,7⟩,⟨1,31,2,61,8⟩,⟨2,61,3,91,8⟩,⟨3,91,1,30,8⟩,⟨1,30,2,59,8⟩,
 ⟨2,59,1,29,8⟩,⟨1,29,2,57,9⟩,⟨2,57,1,28,9⟩,⟨1,28,2,55,8⟩,⟨2,55,1,27,8⟩,⟨1,27,2,53,4⟩,
 ⟨2,53,1,26,4⟩,⟨1,26,1,25,4⟩,⟨1,25,1,24,5⟩,⟨1,24,1,23,4⟩,⟨1,23,4,91,4⟩,⟨4,91,1,22,4⟩,
 ⟨1,22,3,64,3⟩,⟨3,64,1,21,3⟩,⟨1,21,3,62,3⟩,⟨3,62,3,61,3⟩,⟨3,61,1,20,3⟩,⟨1,20,3,59,2⟩,
 ⟨3,59,3,58,2⟩,⟨3,58,1,19,2⟩,⟨1,19,3,56,2⟩,⟨3,56,2,37,2⟩,⟨2,37,3,55,2⟩,⟨3,55,5,91,2⟩,
 ⟨5,91,1,18,5⟩,⟨1,18,3,53,4⟩,⟨3,53,2,35,4⟩,⟨2,35,1,17,5⟩,⟨1,17,2,33,7⟩,⟨2,33,1,16,7⟩,
 ⟨1,16,2,31,7⟩,⟨2,31,4,61,7⟩,⟨4,61,6,91,7⟩,⟨6,91,1,15,8⟩,⟨1,15,4,59,8⟩,⟨4,59,2,29,8⟩,
 ⟨2,29,4,57,9⟩,⟨4,57,1,14,9⟩,⟨1,14,4,55,8⟩,⟨4,55,2,27,8⟩,⟨2,27,4,53,4⟩,⟨4,53,1,13,4⟩,
 ⟨1,13,5,64,4⟩,⟨5,64,3,38,4⟩,⟨3,38,2,25,5⟩,⟨2,25,5,62,5⟩,⟨5,62,3,37,5⟩,⟨3,37,5,61,5⟩,
 ⟨5,61,1,12,5⟩,⟨1,12,5,59,4⟩,⟨5,59,3,35,4⟩,⟨3,35,5,58,4⟩,⟨5,58,2,23,4⟩,⟨2,23,5,57,4⟩,
 ⟨5,57,8,91,4⟩,⟨8,91,3,34,5⟩,⟨3,34,5,56,4⟩,⟨5,56,1,11,4⟩,⟨1,11,5,54,4⟩,⟨5,54,3,32,4⟩,
 ⟨3,32,5,53,4⟩,⟨5,53,2,21,4⟩,⟨2,21,3,31,5⟩,⟨3,31,6,61,5⟩,⟨6,61,9,91,5⟩,⟨9,91,1,10,8⟩,
 ⟨1,10,6,59,7⟩,⟨6,59,3,29,7⟩,⟨3,29,2,19,8⟩,⟨2,19,3,28,8⟩,⟨3,28,4,37,8⟩,⟨4,37,6,55,5⟩,
 ⟨6,55,7,64,5⟩,⟨7,64,10,91,5⟩,⟨10,91,1,9,8⟩,⟨1,9,7,62,4⟩,⟨7,62,6,53,4⟩,⟨6,53,4,35,4⟩,
 ⟨4,35,7,61,4⟩,⟨7,61,3,26,4⟩,⟨3,26,7,60,3⟩,⟨7,60,2,17,3⟩,⟨2,17,7,59,4⟩,⟨7,59,3,25,4⟩,
 ⟨3,25,7,58,4⟩,⟨7,58,11,91,4⟩,⟨11,91,4,33,4⟩,⟨4,33,7,57,5⟩,⟨7,57,1,8,5⟩,⟨1,8,7,55,3⟩,
 ⟨7,55,4,31,3⟩,⟨4,31,7,54,4⟩,⟨7,54,3,23,4⟩,⟨3,23,8,61,4⟩,⟨8,61,5,38,4⟩,⟨5,38,12,91,5⟩,
 ⟨12,91,7,53,7⟩,⟨7,53,2,15,7⟩,⟨2,15,5,37,8⟩,⟨5,37,8,59,6⟩,⟨8,59,3,22,6⟩,⟨3,22,4,29,6⟩,
 ⟨4,29,5,36,6⟩,⟨5,36,8,57,6⟩,⟨8,57,9,64,6⟩,⟨9,64,1,7,6⟩,⟨1,7,9,62,8⟩,⟨9,62,8,55,8⟩,
 ⟨8,55,5,34,8⟩,⟨5,34,9,61,8⟩,⟨9,61,4,27,8⟩,⟨4,27,3,20,3⟩,⟨3,20,8,53,3⟩,⟨8,53,5,33,3⟩,
 ⟨5,33,9,59,4⟩,⟨9,59,2,13,4⟩,⟨2,13,9,58,4⟩,⟨9,58,5,32,4⟩,⟨5,32,3,19,4⟩,⟨3,19,4,25,5⟩,
 ⟨4,25,9,56,5⟩,⟨9,56,5,31,5⟩,⟨5,31,6,37,5⟩,⟨6,37,9,55,5⟩,⟨9,55,10,61,5⟩,⟨10,61,15,91,5⟩,
 ⟨15,91,1,6,5⟩,⟨1,6,10,59,4⟩,⟨10,59,9,53,4⟩,⟨9,53,6,35,4⟩,⟨6,35,11,64,4⟩,⟨11,64,5,29,4⟩,
 ⟨5,29,4,23,5⟩,⟨4,23,10,57,5⟩,⟨10,57,16,91,5⟩,⟨16,91,3,17,7⟩,⟨3,17,11,62,8⟩,⟨11,62,5,28,8⟩,
 ⟨5,28,11,61,7⟩,⟨11,61,2,11,7⟩,⟨2,11,11,60,7⟩,⟨11,60,7,38,7⟩,⟨7,38,5,27,8⟩,⟨5,27,11,59,4⟩,
 ⟨11,59,17,91,4⟩,⟨17,91,3,16,4⟩,⟨3,16,10,53,4⟩,⟨10,53,7,37,4⟩,⟨7,37,11,58,4⟩,⟨11,58,4,21,4⟩,
 ⟨4,21,5,26,5⟩,⟨5,26,11,57,4⟩,⟨11,57,6,31,4⟩,⟨6,31,7,36,4⟩,⟨7,36,11,56,4⟩,⟨11,56,12,61,4⟩,
 ⟨12,61,18,91,4⟩,⟨18,91,1,5,4⟩,⟨1,5,13,64,4⟩,⟨13,64,12,59,4⟩,⟨12,59,11,54,4⟩,⟨11,54,7,34,4⟩,
 ⟨7,34,6,29,4⟩,⟨6,29,11,53,5⟩,⟨11,53,5,24,5⟩,⟨5,24,19,91,5⟩,⟨19,91,13,62,7⟩,⟨13,62,4,19,7⟩,
 ⟨4,19,7,33,7⟩,⟨7,33,13,61,8⟩,⟨13,61,3,14,8⟩,⟨3,14,8,37,8⟩,⟨8,37,13,60,5⟩,⟨13,60,5,23,5⟩,
 ⟨5,23,12,55,6⟩,⟨12,55,7,32,6⟩,⟨7,32,20,91,6⟩,⟨20,91,13,59,8⟩,⟨13,59,2,9,8⟩,⟨2,9,13,58,4⟩,
 ⟨13,58,7,31,4⟩,⟨7,31,12,53,4⟩,⟨12,53,5,22,4⟩,⟨5,22,13,57,4⟩,⟨13,57,8,35,4⟩,⟨8,35,14,61,4⟩,
 ⟨14,61,3,13,4⟩,⟨3,13,13,56,4⟩,⟨13,56,7,30,4⟩,⟨7,30,15,64,3⟩,⟨15,64,4,17,3⟩,⟨4,17,13,55,4⟩,
 ⟨13,55,9,38,4⟩,⟨9,38,14,59,4⟩,⟨14,59,5,21,4⟩,⟨5,21,6,25,5⟩,⟨6,25,13,54,5⟩,⟨13,54,7,29,5⟩,
 ⟨7,29,22,91,6⟩,⟨22,91,15,62,7⟩,⟨15,62,8,33,7⟩,⟨8,33,9,37,8⟩,⟨9,37,13,53,5⟩,⟨13,53,14,57,5⟩,
 ⟨14,57,15,61,5⟩,⟨15,61,1,4,5⟩,⟨1,4,23,91,5⟩,⟨23,91,15,59,6⟩,⟨15,59,14,55,6⟩,⟨14,55,9,35,6⟩,
 ⟨9,35,8,31,7⟩,⟨8,31,15,58,7⟩,⟨15,58,7,27,7⟩,⟨7,27,6,23,4⟩,⟨6,23,16,61,4⟩,⟨16,61,5,19,4⟩,
 ⟨5,19,24,91,4⟩,⟨24,91,14,53,4⟩,⟨14,53,9,34,4⟩,⟨9,34,17,64,4⟩,⟨17,64,4,15,4⟩,⟨4,15,15,56,5⟩,
 ⟨15,56,7,26,5⟩,⟨7,26,10,37,5⟩,⟨10,37,16,59,4⟩,⟨16,59,3,11,4⟩,⟨3,11,17,62,4⟩,⟨17,62,25,91,4⟩,
 ⟨25,91,8,29,4⟩,⟨8,29,5,18,4⟩,⟨5,18,17,61,4⟩,⟨17,61,7,25,4⟩,⟨7,25,16,57,4⟩,⟨16,57,9,32,4⟩,
 ⟨9,32,15,53,4⟩,⟨15,53,17,60,4⟩,⟨17,60,2,7,4⟩,⟨2,7,17,59,7⟩,⟨17,59,11,38,7⟩,⟨11,38,9,31,7⟩,
 ⟨9,31,16,55,8⟩,⟨16,55,7,24,8⟩,⟨7,24,17,58,7⟩,⟨17,58,5,17,7⟩,⟨5,17,18,61,8⟩,⟨18,61,8,27,8⟩,
 ⟨8,27,27,91,5⟩,⟨27,91,19,64,5⟩,⟨19,64,11,37,5⟩,⟨11,37,17,57,5⟩,⟨17,57,3,10,5⟩,⟨3,10,16,53,4⟩,
 ⟨16,53,10,33,4⟩,⟨10,33,17,56,4⟩,⟨17,56,7,23,4⟩,⟨7,23,18,59,5⟩,⟨18,59,11,36,5⟩,⟨11,36,19,62,5⟩,
 ⟨19,62,4,13,5⟩,⟨4,13,17,55,4⟩,⟨17,55,9,29,4⟩,⟨9,29,19,61,4⟩,⟨19,61,5,16,4⟩,⟨5,16,11,35,4⟩,
 ⟨11,35,17,54,4⟩,⟨17,54,6,19,4⟩,⟨6,19,19,60,5⟩,⟨19,60,7,22,5⟩,⟨7,22,29,91,5⟩,⟨29,91,8,25,7⟩,
 ⟨8,25,17,53,7⟩,⟨17,53,9,28,7⟩,⟨9,28,19,59,6⟩,⟨19,59,10,31,6⟩,⟨10,31,11,34,7⟩,⟨11,34,12,37,6⟩,
 ⟨12,37,18,55,3⟩,⟨18,55,19,58,3⟩,⟨19,58,20,61,3⟩,⟨20,61,21,64,3⟩,⟨21,64,30,91,3⟩,⟨30,91,1,3,6⟩,
 ⟨1,3,21,62,3⟩,⟨21,62,20,59,3⟩,⟨20,59,19,56,3⟩,⟨19,56,18,53,3⟩,⟨18,53,31,91,3⟩,⟨31,91,13,38,4⟩,
 ⟨13,38,12,35,4⟩,⟨12,35,11,32,4⟩,⟨11,32,21,61,4⟩,⟨21,61,10,29,4⟩,⟨10,29,19,55,5⟩,⟨19,55,9,26,5⟩,
 ⟨9,26,8,23,5⟩,⟨8,23,7,20,5⟩,⟨7,20,20,57,4⟩,⟨20,57,13,37,4⟩,⟨13,37,32,91,5⟩,⟨32,91,19,54,5⟩,
 ⟨19,54,6,17,5⟩,⟨6,17,11,31,5⟩,⟨11,31,21,59,5⟩,⟨21,59,5,14,5⟩,⟨5,14,19,53,4⟩,⟨19,53,23,64,4⟩,
 ⟨23,64,9,25,4⟩,⟨9,25,22,61,4⟩,⟨22,61,13,36,4⟩,⟨13,36,21,58,4⟩,⟨21,58,33,91,4⟩,⟨33,91,4,11,7⟩,
 ⟨4,11,11,30,8⟩,⟨11,30,7,19,8⟩,⟨7,19,10,27,9⟩,⟨10,27,23,62,5⟩,⟨23,62,13,35,5⟩,⟨13,35,22,59,5⟩,
 ⟨22,59,34,91,5⟩,⟨34,91,3,8,5⟩,⟨3,8,23,61,3⟩,⟨23,61,20,53,3⟩,⟨20,53,14,37,3⟩,⟨14,37,11,29,4⟩,
 ⟨11,29,8,21,4⟩,⟨8,21,21,55,5⟩,⟨21,55,13,34,5⟩,⟨13,34,23,60,5⟩,⟨23,60,5,13,5⟩,⟨5,13,22,57,4⟩,
 ⟨22,57,12,31,4⟩,⟨12,31,7,18,4⟩,⟨7,18,23,59,4⟩,⟨23,59,25,64,4⟩,⟨25,64,9,23,4⟩,⟨9,23,11,28,4⟩,
 ⟨11,28,24,61,3⟩,⟨24,61,13,33,3⟩,⟨13,33,15,38,5⟩,⟨15,38,36,91,6⟩,⟨36,91,21,53,7⟩,⟨21,53,23,58,7⟩,
 ⟨23,58,2,5,7⟩,⟨2,5,25,62,7⟩,⟨25,62,23,57,7⟩,⟨23,57,15,37,7⟩,⟨15,37,13,32,6⟩,⟨13,32,37,91,6⟩,
 ⟨37,91,24,59,8⟩,⟨24,59,11,27,8⟩,⟨11,27,9,22,4⟩,⟨9,22,25,61,3⟩,⟨25,61,23,56,3⟩,⟨23,56,7,17,3⟩,
 ⟨7,17,12,29,4⟩,⟨12,29,22,53,5⟩,⟨22,53,5,12,5⟩,⟨5,12,38,91,4⟩,⟨38,91,23,55,4⟩,⟨23,55,13,31,4⟩,
 ⟨13,31,8,19,4⟩,⟨8,19,27,64,5⟩,⟨27,64,11,26,5⟩,⟨11,26,25,59,4⟩,⟨25,59,14,33,4⟩,⟨14,33,23,54,5⟩,
 ⟨23,54,26,61,5⟩,⟨26,61,3,7,5⟩,⟨3,7,25,58,7⟩,⟨25,58,16,37,7⟩,⟨16,37,13,30,5⟩,⟨13,30,23,53,4⟩,
 ⟨23,53,10,23,4⟩,⟨10,23,27,62,4⟩,⟨27,62,24,55,4⟩,⟨24,55,7,16,4⟩,⟨7,16,25,57,4⟩,⟨25,57,40,91,4⟩,
 ⟨40,91,11,25,7⟩,⟨11,25,26,59,7⟩,⟨26,59,15,34,7⟩,⟨15,34,27,61,7⟩,⟨27,61,4,9,7⟩,⟨4,9,25,56,4⟩,
 ⟨25,56,17,38,4⟩,⟨17,38,13,29,4⟩,⟨13,29,9,20,4⟩,⟨9,20,41,91,4⟩,⟨41,91,14,31,4⟩,⟨14,31,24,53,4⟩,
 ⟨24,53,29,64,4⟩,⟨29,64,5,11,4⟩,⟨5,11,26,57,5⟩,⟨26,57,16,35,5⟩,⟨16,35,27,59,5⟩,⟨27,59,11,24,5⟩,
 ⟨11,24,28,61,4⟩,⟨28,61,17,37,4⟩,⟨17,37,6,13,5⟩,⟨6,13,25,54,4⟩,⟨25,54,13,28,4⟩,⟨13,28,27,58,3⟩,
 ⟨27,58,7,15,3⟩,⟨7,15,29,62,3⟩,⟨29,62,15,32,3⟩,⟨15,32,8,17,3⟩,⟨8,17,25,53,4⟩,⟨25,53,17,36,4⟩,
 ⟨17,36,43,91,5⟩,⟨43,91,26,55,5⟩,⟨26,55,9,19,5⟩,⟨9,19,28,59,6⟩,⟨28,59,29,61,6⟩,⟨29,61,10,21,6⟩,
 ⟨10,21,11,23,7⟩,⟨11,23,12,25,8⟩,⟨12,25,13,27,9⟩,⟨13,27,27,56,4⟩,⟨27,56,14,29,4⟩,⟨14,29,29,60,4⟩,
 ⟨29,60,44,91,4⟩,⟨44,91,15,31,4⟩,⟨15,31,31,64,4⟩,⟨31,64,16,33,4⟩,⟨16,33,17,35,5⟩,⟨17,35,18,37,5⟩,
 ⟨18,37,26,53,5⟩,⟨26,53,27,55,5⟩,⟨27,55,28,57,5⟩,⟨28,57,29,59,5⟩,⟨29,59,30,61,5⟩,⟨30,61,45,91,5⟩,
 ⟨45,91,1,2,5⟩,⟨1,2,46,91,3⟩,⟨46,91,31,61,3⟩,⟨31,61,30,59,3⟩,⟨30,59,29,57,3⟩,⟨29,57,28,55,3⟩,
 ⟨28,55,27,53,3⟩,⟨27,53,19,37,3⟩,⟨19,37,18,35,4⟩,⟨18,35,17,33,4⟩,⟨17,33,33,64,4⟩,⟨33,64,16,31,4⟩,
 ⟨16,31,47,91,5⟩,⟨47,91,31,60,7⟩,⟨31,60,15,29,7⟩,⟨15,29,29,56,7⟩,⟨29,56,14,27,7⟩,⟨14,27,13,25,4⟩,
 ⟨13,25,12,23,4⟩,⟨12,23,11,21,4⟩,⟨11,21,32,61,4⟩,⟨32,61,31,59,4⟩,⟨31,59,10,19,4⟩,⟨10,19,29,55,4⟩,
 ⟨29,55,48,91,4⟩,⟨48,91,19,36,4⟩,⟨19,36,28,53,4⟩,⟨28,53,9,17,4⟩,⟨9,17,17,32,4⟩,⟨17,32,33,62,4⟩,
 ⟨33,62,8,15,4⟩,⟨8,15,31,58,5⟩,⟨31,58,15,28,5⟩,⟨15,28,29,54,5⟩,⟨29,54,7,13,5⟩,⟨7,13,20,37,8⟩,
 ⟨20,37,33,61,5⟩,⟨33,61,13,24,5⟩,⟨13,24,32,59,5⟩,⟨32,59,19,35,5⟩,⟨19,35,31,57,4⟩,⟨31,57,6,11,4⟩,
 ⟨6,11,35,64,4⟩,⟨35,64,29,53,4⟩,⟨29,53,17,31,4⟩,⟨17,31,50,91,5⟩,⟨50,91,11,20,7⟩,⟨11,20,16,29,7⟩,
 ⟨16,29,21,38,8⟩,⟨21,38,31,56,8⟩,⟨31,56,5,9,8⟩,⟨5,9,34,61,4⟩,⟨34,61,19,34,4⟩,⟨19,34,33,59,4⟩,
 ⟨33,59,14,25,4⟩,⟨14,25,51,91,4⟩,⟨51,91,32,57,4⟩,⟨32,57,9,16,4⟩,⟨9,16,31,55,4⟩,⟨31,55,35,62,4⟩,
 ⟨35,62,13,23,4⟩,⟨13,23,30,53,4⟩,⟨30,53,17,30,4⟩,⟨17,30,21,37,4⟩,⟨21,37,33,58,4⟩,⟨33,58,4,7,4⟩,
 ⟨4,7,35,61,4⟩,⟨35,61,31,54,4⟩,⟨31,54,19,33,4⟩,⟨19,33,34,59,5⟩,⟨34,59,15,26,5⟩,⟨15,26,37,64,4⟩,
 ⟨37,64,11,19,4⟩,⟨11,19,18,31,4⟩,⟨18,31,32,55,5⟩,⟨32,55,53,91,5⟩,⟨53,91,7,12,8⟩,⟨7,12,31,53,7⟩,
 ⟨31,53,17,29,7⟩,⟨17,29,10,17,8⟩,⟨10,17,33,56,8⟩,⟨33,56,36,61,8⟩,⟨36,61,13,22,8⟩,⟨13,22,16,27,8⟩,
 ⟨16,27,35,59,4⟩,⟨35,59,54,91,4⟩,⟨54,91,19,32,4⟩,⟨19,32,22,37,4⟩,⟨22,37,34,57,4⟩,⟨34,57,37,62,4⟩,
 ⟨37,62,3,5,4⟩,⟨3,5,35,58,4⟩,⟨35,58,32,53,4⟩,⟨32,53,55,91,4⟩,⟨55,91,23,38,4⟩,⟨23,38,20,33,4⟩,
 ⟨20,33,37,61,5⟩,⟨37,61,17,28,5⟩,⟨17,28,14,23,4⟩,⟨14,23,39,64,4⟩,⟨39,64,36,59,4⟩,⟨36,59,11,18,4⟩,
 ⟨11,18,19,31,4⟩,⟨19,31,35,57,5⟩,⟨35,57,8,13,5⟩,⟨8,13,37,60,7⟩,⟨37,60,21,34,7⟩,⟨21,34,34,55,7⟩,
 ⟨34,55,13,21,7⟩,⟨13,21,18,29,8⟩,⟨18,29,23,37,8⟩,⟨23,37,33,53,5⟩,⟨33,53,38,61,5⟩,⟨38,61,5,8,5⟩,
 ⟨5,8,57,91,5⟩,⟨57,91,37,59,7⟩,⟨37,59,22,35,7⟩,⟨22,35,39,62,7⟩,⟨39,62,17,27,7⟩,⟨17,27,12,19,4⟩,
 ⟨12,19,19,30,4⟩,⟨19,30,7,11,4⟩,⟨7,11,58,91,4⟩,⟨58,91,37,58,4⟩,⟨37,58,23,36,4⟩,⟨23,36,39,61,4⟩,
 ⟨39,61,16,25,4⟩,⟨16,25,41,64,4⟩,⟨41,64,34,53,4⟩,⟨34,53,9,14,4⟩,⟨9,14,38,59,3⟩,⟨38,59,20,31,3⟩,
 ⟨20,31,11,17,4⟩,⟨11,17,35,54,5⟩,⟨35,54,59,91,5⟩,⟨59,91,24,37,7⟩,⟨24,37,37,57,5⟩,⟨37,57,13,20,5⟩,
 ⟨13,20,15,23,5⟩,⟨15,23,17,26,6⟩,⟨17,26,36,55,5⟩,⟨36,55,19,29,5⟩,⟨19,29,40,61,5⟩,⟨40,61,21,32,5⟩,
 ⟨21,32,23,35,5⟩,⟨23,35,25,38,6⟩,⟨25,38,60,91,6⟩,⟨60,91,35,53,6⟩,⟨35,53,37,56,6⟩,⟨37,56,39,59,6⟩,
 ⟨39,59,41,62,6⟩,⟨41,62,2,3,6⟩,⟨2,3,61,91,3⟩,⟨61,91,43,64,3⟩,⟨43,64,41,61,3⟩,⟨41,61,39,58,3⟩,
 ⟨39,58,37,55,3⟩,⟨37,55,25,37,3⟩,⟨25,37,23,34,3⟩,⟨23,34,21,31,3⟩,⟨21,31,40,59,4⟩,⟨40,59,19,28,4⟩,
 ⟨19,28,36,53,4⟩,⟨36,53,17,25,4⟩,⟨17,25,62,91,5⟩,⟨62,91,15,22,5⟩,⟨15,22,41,60,4⟩,⟨41,60,13,19,4⟩,
 ⟨13,19,37,54,4⟩,⟨37,54,24,35,4⟩,⟨24,35,11,16,4⟩,⟨11,16,42,61,4⟩,⟨42,61,20,29,4⟩,⟨20,29,38,55,5⟩,
 ⟨38,55,9,13,5⟩,⟨9,13,43,62,7⟩,⟨43,62,25,36,7⟩,⟨25,36,41,59,7⟩,⟨41,59,16,23,7⟩,⟨16,23,39,56,7⟩,
 ⟨39,56,23,33,7⟩,⟨23,33,37,53,8⟩,⟨37,53,7,10,8⟩,⟨7,10,40,57,7⟩,⟨40,57,26,37,7⟩,⟨26,37,45,64,5⟩,
 ⟨45,64,64,91,5⟩,⟨64,91,19,27,8⟩,⟨19,27,43,61,4⟩,⟨43,61,12,17,4⟩,⟨12,17,41,58,5⟩,⟨41,58,17,24,5⟩,
 ⟨17,24,39,55,4⟩,⟨39,55,22,31,4⟩,⟨22,31,27,38,4⟩,⟨27,38,42,59,4⟩,⟨42,59,5,7,4⟩,⟨5,7,43,60,4⟩,
 ⟨43,60,38,53,4⟩,⟨38,53,23,32,4⟩,⟨23,32,41,57,4⟩,⟨41,57,18,25,4⟩,⟨18,25,44,61,4⟩,⟨44,61,13,18,4⟩,
 ⟨13,18,21,29,4⟩,⟨21,29,66,91,5⟩,⟨66,91,45,62,7⟩,⟨45,62,8,11,7⟩,⟨8,11,43,59,7⟩,⟨43,59,27,37,7⟩,
 ⟨27,37,19,26,6⟩,⟨19,26,41,56,5⟩,⟨41,56,11,15,5⟩,⟨11,15,47,64,5⟩,⟨47,64,25,34,5⟩,⟨25,34,39,53,5⟩,
 ⟨39,53,67,91,5⟩,⟨67,91,14,19,7⟩,⟨14,19,45,61,8⟩,⟨45,61,17,23,8⟩,⟨17,23,20,27,9⟩,⟨20,27,43,58,4⟩,
 ⟨43,58,23,31,4⟩,⟨23,31,26,35,5⟩,⟨26,35,41,55,5⟩,⟨41,55,44,59,5⟩,⟨44,59,68,91,5⟩,⟨68,91,3,4,5⟩,
 ⟨3,4,46,61,2⟩,⟨46,61,43,57,2⟩,⟨43,57,40,53,2⟩,⟨40,53,28,37,2⟩,⟨28,37,25,33,3⟩,⟨25,33,47,62,4⟩,
 ⟨47,62,69,91,4⟩,⟨69,91,22,29,5⟩,⟨22,29,41,54,5⟩,⟨41,54,19,25,5⟩,⟨19,25,16,21,5⟩,⟨16,21,45,59,5⟩,
 ⟨45,59,29,38,5⟩,⟨29,38,42,55,5⟩,⟨42,55,13,17,5⟩,⟨13,17,49,64,6⟩,⟨49,64,23,30,6⟩,⟨23,30,43,56,6⟩,
 ⟨43,56,10,13,6⟩,⟨10,13,47,61,8⟩,⟨47,61,27,35,8⟩,⟨27,35,44,57,7⟩,⟨44,57,17,22,7⟩,⟨17,22,41,53,7⟩,
 ⟨41,53,24,31,7⟩,⟨24,31,45,58,7⟩,⟨45,58,7,9,7⟩,⟨7,9,46,59,4⟩,⟨46,59,71,91,4⟩,⟨71,91,25,32,4⟩,
 ⟨25,32,43,55,4⟩,⟨43,55,18,23,4⟩,⟨18,23,47,60,4⟩,⟨47,60,29,37,4⟩,⟨29,37,11,14,4⟩,⟨11,14,48,61,3⟩,
 ⟨48,61,26,33,3⟩,⟨26,33,15,19,4⟩,⟨15,19,49,62,5⟩,⟨49,62,72,91,5⟩,⟨72,91,19,24,5⟩,⟨19,24,42,53,4⟩,
 ⟨42,53,23,29,4⟩,⟨23,29,27,34,4⟩,⟨27,34,43,54,4⟩,⟨43,54,47,59,4⟩,⟨47,59,51,64,4⟩,⟨51,64,4,5,4⟩,
 ⟨4,5,73,91,6⟩,⟨73,91,49,61,7⟩,⟨49,61,45,56,7⟩,⟨45,56,29,36,7⟩,⟨29,36,25,31,7⟩,⟨25,31,46,57,8⟩,
 ⟨46,57,21,26,8⟩,⟨21,26,17,21,8⟩,⟨17,21,47,58,8⟩,⟨47,58,30,37,8⟩,⟨30,37,43,53,6⟩,⟨43,53,13,16,6⟩,
 ⟨13,16,74,91,6⟩,⟨74,91,48,59,8⟩,⟨48,59,22,27,8⟩,⟨22,27,31,38,4⟩,⟨31,38,49,60,4⟩,⟨49,60,9,11,4⟩,
 ⟨9,11,50,61,4⟩,⟨50,61,23,28,4⟩,⟨23,28,51,62,3⟩,⟨51,62,14,17,3⟩,⟨14,17,75,91,5⟩,⟨75,91,47,57,5⟩,
 ⟨47,57,19,23,5⟩,⟨19,23,24,29,5⟩,⟨24,29,53,64,5⟩,⟨53,64,29,35,5⟩,⟨29,35,44,53,5⟩,⟨44,53,49,59,5⟩,
 ⟨49,59,5,6,5⟩,⟨5,6,76,91,5⟩,⟨76,91,51,61,6⟩,⟨51,61,46,55,6⟩,⟨46,55,31,37,6⟩,⟨31,37,26,31,5⟩,
 ⟨26,31,47,56,5⟩,⟨47,56,21,25,5⟩,⟨21,25,16,19,5⟩,⟨16,19,27,32,6⟩,⟨27,32,49,58,6⟩,⟨49,58,11,13,6⟩,
 ⟨11,13,50,59,8⟩,⟨50,59,28,33,8⟩,⟨28,33,45,53,8⟩,⟨45,53,17,20,8⟩,⟨17,20,23,27,8⟩,⟨23,27,52,61,3⟩,
 ⟨52,61,29,34,3⟩,⟨29,34,47,55,3⟩,⟨47,55,53,62,3⟩,⟨53,62,6,7,3⟩,⟨6,7,55,64,3⟩,⟨55,64,49,57,3⟩,
 ⟨49,57,31,36,3⟩,⟨31,36,25,29,4⟩,⟨25,29,19,22,5⟩,⟨19,22,51,59,4⟩,⟨51,59,32,37,4⟩,⟨32,37,13,15,4⟩,
 ⟨13,15,46,53,4⟩,⟨46,53,79,91,4⟩,⟨79,91,33,38,4⟩,⟨33,38,53,61,4⟩,⟨53,61,20,23,4⟩,⟨20,23,47,54,4⟩,
 ⟨47,54,27,31,4⟩,⟨27,31,48,55,5⟩,⟨48,55,7,8,5⟩,⟨7,8,50,57,4⟩,⟨50,57,29,33,4⟩,⟨29,33,80,91,6⟩,
 ⟨80,91,51,58,8⟩,⟨51,58,22,25,8⟩,⟨22,25,52,59,8⟩,⟨52,59,15,17,8⟩,⟨15,17,53,60,9⟩,⟨53,60,23,26,9⟩,
 ⟨23,26,54,61,8⟩,⟨54,61,31,35,8⟩,⟨31,35,47,53,7⟩,⟨47,53,55,62,7⟩,⟨55,62,8,9,7⟩,⟨8,9,81,91,4⟩,
 ⟨81,91,57,64,4⟩,⟨57,64,49,55,4⟩,⟨49,55,33,37,4⟩,⟨33,37,25,28,4⟩,⟨25,28,17,19,4⟩,⟨17,19,26,29,4⟩,
 ⟨26,29,53,59,5⟩,⟨53,59,9,10,5⟩,⟨9,10,82,91,4⟩,⟨82,91,55,61,4⟩,⟨55,61,28,31,4⟩,⟨28,31,19,21,5⟩,
 ⟨19,21,48,53,5⟩,⟨48,53,29,32,5⟩,⟨29,32,49,54,5⟩,⟨49,54,10,11,5⟩,⟨10,11,51,56,5⟩,⟨51,56,31,34,5⟩,
 ⟨31,34,83,91,6⟩,⟨83,91,52,57,8⟩,⟨52,57,21,23,8⟩,⟨21,23,53,58,8⟩,⟨53,58,32,35,8⟩,⟨32,35,54,59,8⟩,
 ⟨54,59,11,12,8⟩,⟨11,12,56,61,7⟩,⟨56,61,34,37,7⟩,⟨34,37,57,62,5⟩,⟨57,62,23,25,5⟩,⟨23,25,35,38,6⟩,
 ⟨35,38,59,64,6⟩,⟨59,64,12,13,6⟩,⟨12,13,49,53,8⟩,⟨49,53,25,27,8⟩,⟨25,27,51,55,3⟩,⟨51,55,13,14,3⟩,
 ⟨13,14,53,57,2⟩,⟨53,57,27,29,2⟩,⟨27,29,55,59,2⟩,⟨55,59,14,15,2⟩,⟨14,15,85,91,3⟩,⟨85,91,57,61,4⟩,
 ⟨57,61,29,31,4⟩,⟨29,31,15,16,4⟩,⟨15,16,31,33,4⟩,⟨31,33,16,17,6⟩,⟨16,17,33,35,6⟩,⟨33,35,50,53,5⟩,
 ⟨50,53,17,18,5⟩,⟨17,18,86,91,5⟩,⟨86,91,52,55,5⟩,⟨52,55,35,37,5⟩,⟨35,37,53,56,2⟩,⟨53,56,18,19,2⟩,
 ⟨18,19,55,58,3⟩,⟨55,58,56,59,3⟩,⟨56,59,19,20,3⟩,⟨19,20,58,61,3⟩,⟨58,61,59,62,3⟩,⟨59,62,20,21,3⟩,
 ⟨20,21,61,64,4⟩,⟨61,64,21,22,4⟩,⟨21,22,87,91,4⟩,⟨87,91,22,23,7⟩,⟨22,23,23,24,8⟩,⟨23,24,24,25,8⟩,
 ⟨24,25,25,26,9⟩,⟨25,26,51,53,8⟩,⟨51,53,26,27,8⟩,⟨26,27,53,55,3⟩,⟨53,55,27,28,3⟩,⟨27,28,55,57,2⟩,
 ⟨55,57,28,29,2⟩,⟨28,29,57,59,2⟩,⟨57,59,29,30,2⟩,⟨29,30,88,91,2⟩,⟨88,91,59,61,3⟩,⟨59,61,30,31,3⟩,
 ⟨30,31,31,32,3⟩,⟨31,32,32,33,3⟩,⟨32,33,33,34,5⟩,⟨33,34,34,35,4⟩,⟨34,35,35,36,3⟩,⟨35,36,36,37,3⟩,
 ⟨90,91,1,1,3⟩
]
private lemma z103 (p1 q1 p2 q2 m:ℕ) (l:List ℕ) :
  (z102 p1 q1 p2 q2 m l).Perm (m :: l):=by
 induction l with
 | nil=>exact List.Perm.refl _
 | cons h t ih =>
  unfold z102
  split_ifs
  ·
   exact List.Perm.refl _
  ·
   exact (ih.cons h).trans (List.Perm.swap m h t)
private lemma z259 (p1 q1 p2 q2:ℕ) (l:List ℕ) :
  (z258 p1 q1 p2 q2 l).Perm l:=by
 induction l with
 | nil=>exact List.Perm.refl _
 | cons h t ih =>
  exact (z103 p1 q1 p2 q2 h _).trans (ih.cons h)
private lemma z82 {p1 q1 p2 q2 m:ℕ} {x:ℝ}
  (hq1:0< q1) (hq2:0< q2) (hm:0< m)
  (hlo:(p1:ℝ)/q1< x) (hhi:x< (p2:ℝ)/q2)
  (hbnd:m*p2 ≤ ((m*p1)/q1+1)*q2) :
  ⌊(m:ℝ)*x⌋=(((m*p1)/q1:ℕ):ℤ):=by
 rw [Int.floor_eq_iff]
 have hq1r:(0:ℝ)< q1:=Nat.cast_pos.mpr hq1
 have hq2r:(0:ℝ)< q2:=Nat.cast_pos.mpr hq2
 have hmr:(0:ℝ)< m:=Nat.cast_pos.mpr hm
 constructor
 ·
  have h1:((m*p1)/q1:ℕ)*q1 ≤ m*p1:=Nat.div_mul_le_self (m*p1) q1
  have h1r:(((m*p1)/q1:ℕ):ℝ)*q1 ≤ (m:ℝ)*p1:=by exact_mod_cast h1
  have h2:(((m*p1)/q1:ℕ):ℝ) ≤ (m:ℝ)*((p1:ℝ)/q1):=by
   rw [← mul_div_assoc,le_div_iff₀ hq1r];exact h1r
  have h3:(m:ℝ)*((p1:ℝ)/q1)< (m:ℝ)*x:=mul_lt_mul_of_pos_left hlo hmr
  exact_mod_cast (h2.trans h3.le)
 ·
  have h1r:(m:ℝ)*p2 ≤ ((((m*p1)/q1:ℕ):ℝ)+1)*q2:=by exact_mod_cast hbnd
  have h2:(m:ℝ)*((p2:ℝ)/q2) ≤ (((m*p1)/q1:ℕ):ℝ)+1:=by
   rw [← mul_div_assoc,div_le_iff₀ hq2r];exact h1r
  have h3:(m:ℝ)*x< (m:ℝ)*((p2:ℝ)/q2):=mul_lt_mul_of_pos_left hhi hmr
  exact_mod_cast (h3.trans_le h2)
private lemma z86 {p1 q1 p2 q2 m1 m2:ℕ} {x:ℝ}
  (hq1:0< q1) (hq2:0< q2)
  (hlo:(p1:ℝ)/q1< x) (hhi:x< (p2:ℝ)/q2)
  (hfl1:⌊(m1:ℝ)*x⌋=(((m1*p1)/q1:ℕ):ℤ))
  (hfl2:⌊(m2:ℝ)*x⌋=(((m2*p1)/q1:ℕ):ℤ))
  (hord:z161 p1 q1 p2 q2 m1 m2=true) :
  Int.fract ((m1:ℝ)*x)< Int.fract ((m2:ℝ)*x):=by
 unfold z161 at hord
 simp only [Bool.and_eq_true,Bool.or_eq_true,Nat.ble_eq,Nat.blt_eq] at hord
 rcases hord with ⟨⟨ha_nat,hb_nat⟩,hab⟩
 set c1:ℕ:=(m1*p1)/q1
 set c2:ℕ:=(m2*p1)/q1
 have hq1r:(0:ℝ)< q1:=Nat.cast_pos.mpr hq1
 have hq2r:(0:ℝ)< q2:=Nat.cast_pos.mpr hq2
 have ha':(m1:ℝ)*((p1:ℝ)/q1)-(c1:ℝ) ≤ (m2:ℝ)*((p1:ℝ)/q1)-(c2:ℝ):=by
  have h:(m1:ℝ)*p1+(c2:ℝ)*q1 ≤ (m2:ℝ)*p1+(c1:ℝ)*q1:=by exact_mod_cast ha_nat
  have hsub:(m1:ℝ)*p1-(c1:ℝ)*q1 ≤ (m2:ℝ)*p1-(c2:ℝ)*q1:=by linarith
  have:=div_le_div_of_nonneg_right hsub hq1r.le
  simpa [sub_div,mul_div_assoc,mul_div_cancel_right₀ _ hq1r.ne'] using this
 have hb':(m1:ℝ)*((p2:ℝ)/q2)-(c1:ℝ) ≤ (m2:ℝ)*((p2:ℝ)/q2)-(c2:ℝ):=by
  have h:(m1:ℝ)*p2+(c2:ℝ)*q2 ≤ (m2:ℝ)*p2+(c1:ℝ)*q2:=by exact_mod_cast hb_nat
  have hsub:(m1:ℝ)*p2-(c1:ℝ)*q2 ≤ (m2:ℝ)*p2-(c2:ℝ)*q2:=by linarith
  have:=div_le_div_of_nonneg_right hsub hq2r.le
  simpa [sub_div,mul_div_assoc,mul_div_cancel_right₀ _ hq2r.ne'] using this
 have hstrict:((m1:ℝ)*((p1:ℝ)/q1)-(c1:ℝ)< (m2:ℝ)*((p1:ℝ)/q1)-(c2:ℝ)) ∨
     ((m1:ℝ)*((p2:ℝ)/q2)-(c1:ℝ)< (m2:ℝ)*((p2:ℝ)/q2)-(c2:ℝ)):=by
  rcases hab with hlt | hlt
  ·
   left
   have h:(m1:ℝ)*p1+(c2:ℝ)*q1< (m2:ℝ)*p1+(c1:ℝ)*q1:=by exact_mod_cast hlt
   have hsub:(m1:ℝ)*p1-(c1:ℝ)*q1< (m2:ℝ)*p1-(c2:ℝ)*q1:=by linarith
   have:=div_lt_div_of_pos_right hsub hq1r
   simpa [sub_div,mul_div_assoc,mul_div_cancel_right₀ _ hq1r.ne'] using this
  ·
   right
   have h:(m1:ℝ)*p2+(c2:ℝ)*q2< (m2:ℝ)*p2+(c1:ℝ)*q2:=by exact_mod_cast hlt
   have hsub:(m1:ℝ)*p2-(c1:ℝ)*q2< (m2:ℝ)*p2-(c2:ℝ)*q2:=by linarith
   have:=div_lt_div_of_pos_right hsub hq2r
   simpa [sub_div,mul_div_assoc,mul_div_cancel_right₀ _ hq2r.ne'] using this
 rw [Int.fract,Int.fract,hfl1,hfl2]
 simp only [Int.cast_natCast]
 set a:=(p1:ℝ)/q1
 set b:=(p2:ℝ)/q2
 set d:=b-a
 have hd:0< d:=sub_pos.mpr (hlo.trans hhi)
 set t:=(x-a)/d
 have ht0:0< t:=div_pos (sub_pos.mpr hlo) hd
 have ht1:t< 1:=(div_lt_one hd).mpr (by linarith)
 have hx_eq:x=(1-t)*a+t*b:=by
  have htd:t*d=x-a:=div_mul_cancel₀ (x-a) hd.ne'
  have:d=b-a:=rfl
  nlinarith
 have hlin:((m2:ℝ)*x-(c2:ℝ))-((m1:ℝ)*x-(c1:ℝ)) =
   (1-t)*(((m2:ℝ)*a-(c2:ℝ))-((m1:ℝ)*a-(c1:ℝ))) +
   t*(((m2:ℝ)*b-(c2:ℝ))-((m1:ℝ)*b-(c1:ℝ))):=by
  rw [hx_eq];ring
 have hpos:0< ((m2:ℝ)*x-(c2:ℝ))-((m1:ℝ)*x-(c1:ℝ)):=by
  rw [hlin]
  rcases hstrict with hlt | hlt
  ·
   have h1:0< (1-t)*(((m2:ℝ)*a-(c2:ℝ))-((m1:ℝ)*a-(c1:ℝ))):=
    mul_pos (by linarith) (by linarith)
   have h2:0 ≤ t*(((m2:ℝ)*b-(c2:ℝ))-((m1:ℝ)*b-(c1:ℝ))):=
    mul_nonneg ht0.le (by linarith)
   linarith
  ·
   have h1:0 ≤ (1-t)*(((m2:ℝ)*a-(c2:ℝ))-((m1:ℝ)*a-(c1:ℝ))):=
    mul_nonneg (by linarith) (by linarith)
   have h2:0< t*(((m2:ℝ)*b-(c2:ℝ))-((m1:ℝ)*b-(c1:ℝ))):=
    mul_pos ht0 (by linarith)
   linarith
 linarith
private lemma z162 {p1 q1 p2 q2:ℕ} {x:ℝ}
  (hq1:0< q1) (hq2:0< q2)
  (hlo:(p1:ℝ)/q1< x) (hhi:x< (p2:ℝ)/q2) :
  ∀ (l:List ℕ),
   (∀ m∈l,⌊(m:ℝ)*x⌋=(((m*p1)/q1:ℕ):ℤ)) →
   z38 p1 q1 p2 q2 l=true →
   l.Pairwise (fun (m1 m2:ℕ)=>Int.fract ((m1:ℝ)*x)< Int.fract ((m2:ℝ)*x))
 | [],_,_=>List.Pairwise.nil
 | [_],_,_=>by simp
 | m1 :: m2 :: t,hfl,hchk=>by
  unfold z38 at hchk
  simp only [Bool.and_eq_true] at hchk
  have hlt:=z86 hq1 hq2 hlo hhi
   (hfl m1 (by simp)) (hfl m2 (by simp)) hchk.1
  have hrest:=z162 hq1 hq2 hlo hhi (m2 :: t)
   (fun m hm=>hfl m (by simp [hm])) hchk.2
  rw [List.pairwise_cons] at hrest ⊢
  refine ⟨fun k hk=>?_,List.pairwise_cons.mpr hrest⟩
  rcases List.mem_cons.mp hk with rfl | hkt
  ·
   exact hlt
  ·
   exact hlt.trans (hrest.1 k hkt)
private lemma z44 {x y:ℝ} {v:ℕ} :
  ∀ (l:List ℕ) (pos neg accL:ℕ),
   accL=(l.map wtL).sum →
   l.Pairwise (fun (m1 m2:ℕ)=>Int.fract ((m1:ℝ)*x)< Int.fract ((m2:ℝ)*x)) →
   z43 v pos neg accL l=true →
   (v:ℤ) ≤ ((pos:ℤ)-(neg:ℤ))+(l.map fun (m:ℕ) =>
    (if y< Int.fract ((m:ℝ)*x) then (wtL m:ℤ) else 0) +
    (if Int.fract ((m:ℝ)*x)< y then wtR m else 0)).sum
 | [],pos,neg,accL,hacc,_,hchk=>by
  simp only [List.map_nil,List.sum_nil] at hacc ⊢
  subst hacc
  unfold z43 at hchk
  simp only [Nat.ble_eq,add_zero] at hchk
  omega
 | m :: t,pos,neg,accL,hacc,hpw,hchk=>by
  simp only [List.map_cons,List.sum_cons] at hacc
  unfold z43 at hchk
  simp only [Bool.and_eq_true,Nat.ble_eq] at hchk
  rcases hchk with ⟨⟨h1,h2⟩,h3⟩
  have hpw':=List.pairwise_cons.mp hpw
  have hacc_t:accL-wtL m=(t.map wtL).sum:=by omega
  rcases lt_trichotomy y (Int.fract ((m:ℝ)*x)) with hlt | heq | hgt_y
  ·
   have hmap:((m :: t).map fun (k:ℕ) =>
     (if y< Int.fract ((k:ℝ)*x) then (wtL k:ℤ) else 0) +
     (if Int.fract ((k:ℝ)*x)< y then wtR k else 0)).sum =
     (((m :: t).map wtL).sum:ℕ):=by
    rw [Nat.cast_list_sum,List.map_map]
    congr 1
    refine List.map_congr_left fun k hk=>?_
    have hk_lt:y< Int.fract ((k:ℝ)*x):=by
     rcases List.mem_cons.mp hk with rfl | hkt
     ·
      exact hlt
     ·
      exact hlt.trans (hpw'.1 k hkt)
    simp [if_pos hk_lt,if_neg (not_lt.mpr hk_lt.le)]
   rw [hmap]
   simp only [List.map_cons,List.sum_cons]
   omega
  ·
   have hmap:((m :: t).map fun (k:ℕ) =>
     (if y< Int.fract ((k:ℝ)*x) then (wtL k:ℤ) else 0) +
     (if Int.fract ((k:ℝ)*x)< y then wtR k else 0)).sum =
     ((t.map wtL).sum:ℕ):=by
    rw [List.map_cons,List.sum_cons,heq,if_neg (lt_irrefl _),if_neg (lt_irrefl _),
     add_zero,zero_add,Nat.cast_list_sum,List.map_map]
    congr 1
    refine List.map_congr_left fun k hk=>?_
    have hk_lt:Int.fract ((m:ℝ)*x)< Int.fract ((k:ℝ)*x):=hpw'.1 k hk
    simp [if_pos hk_lt,if_neg (not_lt.mpr hk_lt.le)]
   rw [hmap]
   omega
  ·
   have ih:=z44 t (pos+z283 m) (neg+z282 m) (accL-wtL m)
    hacc_t hpw'.2 h3 (y:=y)
   rw [List.map_cons,List.sum_cons,if_neg (not_lt.mpr hgt_y.le),if_pos hgt_y,zero_add]
   unfold wtR at *
   push_cast at ih ⊢
   linarith
lemma z42 {e:CertEntry} (hchk:z40 e=true)
  {x y:ℝ} (hlo:(e.p1:ℝ)/e.q1< x) (hhi:x< (e.p2:ℝ)/e.q2)
  (hy0:0 ≤ y) (hy1:y< 1) :
  (e.v:ℤ) ≤ phi0 x y:=by
 dsimp only [z40] at hchk
 have h1:=Bool.and_eq_true _ _ |>.mp hchk
 have h2:=Bool.and_eq_true _ _ |>.mp h1.1
 have h3:=Bool.and_eq_true _ _ |>.mp h2.1
 have h4:=Bool.and_eq_true _ _ |>.mp h3.1
 have h5:=Bool.and_eq_true _ _ |>.mp h4.1
 have h6:=Bool.and_eq_true _ _ |>.mp h5.1
 have hcs:=Bool.and_eq_true _ _ |>.mp h1.2
 have hq1:0< e.q1:=Nat.blt_eq.mp h6.1
 have hq2:0< e.q2:=Nat.blt_eq.mp h6.2
 have hfl_all:∀ m∈z81,m*e.p2 ≤ ((m*e.p1)/e.q1+1)*e.q2:=fun m hm =>
  Nat.ble_eq.mp (List.all_eq_true.mp h2.2 m hm)
 have hchain:=hcs.1
 have hsweep:=hcs.2
 have hfl:∀ m∈z81,⌊(m:ℝ)*x⌋=(((m*e.p1)/e.q1:ℕ):ℤ):=by
  intro m hm
  have hm_pos:0< m:=(show ∀ k,k∈z81→ 0< k by decide) m hm
  exact z82 hq1 hq2 hm_pos hlo hhi (hfl_all m hm)
 have hperm:=z259 e.p1 e.q1 e.p2 e.q2 all23
 have hsub:∀ m∈z258 e.p1 e.q1 e.p2 e.q2 all23,m∈z81:=
  fun m hm=>(show ∀ k,k∈all23→ k∈z81 by decide) m (hperm.subset hm)
 have hpw:=z162 hq1 hq2 hlo hhi _ (fun m hm=>hfl m (hsub m hm)) hchain
 have hsumL:(13:ℕ)=((z258 e.p1 e.q1 e.p2 e.q2 all23).map wtL).sum:=by
  rw [(hperm.map wtL).sum_eq]
  decide
 have hsw:=z44 (y:=y) _ _ _ 13 hsumL hpw hsweep
 have hW:phiW x y=((z258 e.p1 e.q1 e.p2 e.q2 all23).map fun (m:ℕ) =>
   (if y< Int.fract ((m:ℝ)*x) then (wtL m:ℤ) else 0) +
   (if Int.fract ((m:ℝ)*x)< y then wtR m else 0)).sum:=
  (hperm.symm.map _).sum_eq
 have hC:phiC x =
   ((3*((91*e.p1)/e.q1) +
    (((33*e.p1)/e.q1)+((29*e.p1)/e.q1))+(((31*e.p1)/e.q1)+((30*e.p1)/e.q1)) +
    (((29*e.p1)/e.q1)+((31*e.p1)/e.q1))+(((27*e.p1)/e.q1)+((32*e.p1)/e.q1)) +
    (((25*e.p1)/e.q1)+((33*e.p1)/e.q1))+(((23*e.p1)/e.q1)+((34*e.p1)/e.q1)) +
    (((21*e.p1)/e.q1)+((35*e.p1)/e.q1))+(((19*e.p1)/e.q1)+((36*e.p1)/e.q1)) +
    (((17*e.p1)/e.q1)+((37*e.p1)/e.q1))+(((15*e.p1)/e.q1)+((38*e.p1)/e.q1)):ℕ):ℤ) -
   ((3*((27*e.p1)/e.q1)+3*((64*e.p1)/e.q1) +
    (((62*e.p1)/e.q1)+((61*e.p1)/e.q1)+((60*e.p1)/e.q1)+((59*e.p1)/e.q1) +
     ((58*e.p1)/e.q1)+((57*e.p1)/e.q1)+((56*e.p1)/e.q1)+((55*e.p1)/e.q1) +
     ((54*e.p1)/e.q1)+((53*e.p1)/e.q1)):ℕ):ℤ):=by
  unfold phiC
  rw [Finset.sum_Icc_succ_top (by omega:1 ≤ 10),Finset.sum_Icc_succ_top (by omega:1 ≤ 9),
   Finset.sum_Icc_succ_top (by omega:1 ≤ 8),Finset.sum_Icc_succ_top (by omega:1 ≤ 7),
   Finset.sum_Icc_succ_top (by omega:1 ≤ 6),Finset.sum_Icc_succ_top (by omega:1 ≤ 5),
   Finset.sum_Icc_succ_top (by omega:1 ≤ 4),Finset.sum_Icc_succ_top (by omega:1 ≤ 3),
   Finset.sum_Icc_succ_top (by omega:1 ≤ 2),Finset.Icc_self,Finset.sum_singleton]
  norm_num
  have hfl':∀ m:ℕ,m∈z81→ ⌊(m:ℝ)*x⌋=(((m*e.p1)/e.q1:ℕ):ℤ):=hfl
  have h91:=hfl' 91 (by unfold z81;decide)
  have h27:=hfl' 27 (by unfold z81;decide)
  have h64:=hfl' 64 (by unfold z81;decide)
  have h33:=hfl' 33 (by unfold z81;decide)
  have h29:=hfl' 29 (by unfold z81;decide)
  have h62:=hfl' 62 (by unfold z81;decide)
  have h31:=hfl' 31 (by unfold z81;decide)
  have h30:=hfl' 30 (by unfold z81;decide)
  have h61:=hfl' 61 (by unfold z81;decide)
  have h60:=hfl' 60 (by unfold z81;decide)
  have h32:=hfl' 32 (by unfold z81;decide)
  have h59:=hfl' 59 (by unfold z81;decide)
  have h25:=hfl' 25 (by unfold z81;decide)
  have h58:=hfl' 58 (by unfold z81;decide)
  have h23:=hfl' 23 (by unfold z81;decide)
  have h34:=hfl' 34 (by unfold z81;decide)
  have h57:=hfl' 57 (by unfold z81;decide)
  have h21:=hfl' 21 (by unfold z81;decide)
  have h35:=hfl' 35 (by unfold z81;decide)
  have h56:=hfl' 56 (by unfold z81;decide)
  have h19:=hfl' 19 (by unfold z81;decide)
  have h36:=hfl' 36 (by unfold z81;decide)
  have h55:=hfl' 55 (by unfold z81;decide)
  have h17:=hfl' 17 (by unfold z81;decide)
  have h37:=hfl' 37 (by unfold z81;decide)
  have h54:=hfl' 54 (by unfold z81;decide)
  have h15:=hfl' 15 (by unfold z81;decide)
  have h38:=hfl' 38 (by unfold z81;decide)
  have h53:=hfl' 53 (by unfold z81;decide)
  norm_num at h91 h27 h64 h33 h29 h62 h31 h30 h61 h60 h32 h59 h25 h58 h23 h34 h57 h21 h35 h56 h19 h36 h55 h17 h37 h54 h15 h38 h53
  rw [h91,h27,h64,h33,h29,h62,h31,h30,h61,h60,h32,h59,h25,h58,h23,h34,h57,h21,h35,h56,h19,h36,h55,h17,h37,h54,h15,h38,h53]
  push_cast
  ring
 rw [z167 hy0 hy1,hW,hC]
 exact hsw
theorem z37 :
  z36.all z40=true ∧
  z39 z36=true ∧
  17610000 ≤ (z36.foldl (fun acc e=>acc+z253 e) 0):=by
 have h1:z36.all z40=true:=by decide +kernel
 have h2:z39 z36=true:=by decide +kernel
 have h3:17610000 ≤ (z36.foldl (fun acc e=>acc+z253 e) 0):=by decide +kernel
 exact ⟨h1,h2,h3⟩
end Z2
namespace Z2
open scoped BigOperators
open Finset Filter Topology
noncomputable def z169 (L:List CertEntry) (n p:ℕ):ℕ:=
 if 91*n< p*p∧p ≤ 33*n then
  ∑ k∈Finset.range 10,
   (L.map fun e =>
    if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
     (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then e.v else 0).sum
 else 0
noncomputable def z168 (n p:ℕ):ℕ:=z169 z36 n p
private lemma z166 (x y:ℝ) (k:ℤ) :
  phi0 (x+k) y=phi0 x y:=by
 unfold phi0
 have hfl:∀ (m:ℕ),⌊(m:ℝ)*(x+k)⌋=⌊(m:ℝ)*x⌋+(m:ℤ)*k:=by
  intro m
  have h:(m:ℝ)*(x+k)=(m:ℝ)*x+(((m:ℤ)*k:ℤ):ℝ):=by push_cast;ring
  rw [h,Int.floor_add_intCast]
 have hsub1:∀ (m:ℕ),⌊y-(m:ℝ)*(x+k)⌋=⌊y-(m:ℝ)*x⌋ - (m:ℤ)*k:=by
  intro m
  have h:y-(m:ℝ)*(x+k)=(y-(m:ℝ)*x)+((-(m:ℤ)*k:ℤ):ℝ):=by
   push_cast;ring
  rw [h,Int.floor_add_intCast];ring
 have hsub2:∀ (m:ℕ),⌊(m:ℝ)*(x+k)-y⌋=⌊(m:ℝ)*x-y⌋+(m:ℤ)*k:=by
  intro m
  have h:(m:ℝ)*(x+k)-y=((m:ℝ)*x-y)+(((m:ℤ)*k:ℤ):ℝ):=by
   push_cast;ring
  rw [h,Int.floor_add_intCast]
 have h27:⌊(27:ℝ)*(x+k)⌋=⌊(27:ℝ)*x⌋+27*k:=by simpa using hfl 27
 have h27s:⌊y-(27:ℝ)*(x+k)⌋=⌊y-(27:ℝ)*x⌋ - 27*k:=by simpa using hsub1 27
 have h91s:⌊(91:ℝ)*(x+k)-y⌋=⌊(91:ℝ)*x-y⌋+91*k:=by simpa using hsub2 91
 have h64s:⌊(64:ℝ)*(x+k)-y⌋=⌊(64:ℝ)*x-y⌋+64*k:=by simpa using hsub2 64
 have hsum:∑ u∈Finset.Icc (1:ℕ) 10,
   (⌊((35-2*u:ℕ):ℝ)*(x+k)⌋ - ⌊y-((28+u:ℕ):ℝ)*(x+k)⌋ -
    ⌊((63-u:ℕ):ℝ)*(x+k)-y⌋) =
   ∑ u∈Finset.Icc (1:ℕ) 10,
   (⌊((35-2*u:ℕ):ℝ)*x⌋ - ⌊y-((28+u:ℕ):ℝ)*x⌋ -
    ⌊((63-u:ℕ):ℝ)*x-y⌋):=by
  refine Finset.sum_congr rfl fun u hu=>?_
  rw [hfl (35-2*u),hsub1 (28+u),hsub2 (63-u)]
  have hu1:1 ≤ u:=(Finset.mem_Icc.mp hu).1
  have hu10:u ≤ 10:=(Finset.mem_Icc.mp hu).2
  have hcoef:((35-2*u:ℕ):ℤ)+((28+u:ℕ):ℤ)-((63-u:ℕ):ℤ)=0:=by omega
  linear_combination k*hcoef
 rw [h27,h27s,h91s,h64s,hsum]
 ring
private lemma z41 {e:CertEntry} (hchk:z40 e=true) :
  0< e.q1∧0< e.q2 ∧
  (e.p1:ℝ)/e.q1< (e.p2:ℝ)/e.q2 ∧
  (1:ℝ)/33 ≤ (e.p1:ℝ)/e.q1 ∧
  (e.p2:ℝ)/e.q2 ≤ 1:=by
 dsimp only [z40] at hchk
 have h1:=Bool.and_eq_true _ _ |>.mp hchk
 have h2:=Bool.and_eq_true _ _ |>.mp h1.1
 have h3:=Bool.and_eq_true _ _ |>.mp h2.1
 have h4:=Bool.and_eq_true _ _ |>.mp h3.1
 have h5:=Bool.and_eq_true _ _ |>.mp h4.1
 have h6:=Bool.and_eq_true _ _ |>.mp h5.1
 have hq1:0< e.q1:=Nat.blt_eq.mp h6.1
 have hq2:0< e.q2:=Nat.blt_eq.mp h6.2
 have hlt_ab:e.p1*e.q2< e.p2*e.q1:=Nat.blt_eq.mp h5.2
 have hge33:e.q1 ≤ 33*e.p1:=Nat.ble_eq.mp h4.2
 have hle1:e.p2 ≤ e.q2:=Nat.ble_eq.mp h3.2
 have hq1r:(0:ℝ)< e.q1:=Nat.cast_pos.mpr hq1
 have hq2r:(0:ℝ)< e.q2:=Nat.cast_pos.mpr hq2
 refine ⟨hq1,hq2,?_,?_,?_⟩
 ·
  rw [div_lt_div_iff₀ hq1r hq2r];exact_mod_cast hlt_ab
 ·
  rw [div_le_div_iff₀ (by positivity:(0:ℝ)< 33) hq1r];norm_num
  exact_mod_cast (show e.q1 ≤ e.p1*33 by omega)
 ·
  rw [div_le_one hq2r];exact_mod_cast hle1
private lemma z70 :
  ∀ (l:List CertEntry) (x:ℝ) (B:ℤ),
   l.all z40=true →
   z39 l=true →
   0 ≤ B →
   (∀ e∈l,(e.p1:ℝ)/e.q1< x→ x< (e.p2:ℝ)/e.q2→ (e.v:ℤ) ≤ B) →
   (((l.map fun e=>if (e.p1:ℝ)/e.q1< x∧x< (e.p2:ℝ)/e.q2 then e.v else 0).sum:ℕ):ℤ) ≤ B
 | [],_,_,_,_,hB0,_=>by simpa using hB0
 | [e],x,B,_,_,hB0,hle=>by
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  split_ifs with h
  ·
   exact hle e (by simp) h.1 h.2
  ·
   simpa using hB0
 | e1 :: e2 :: t,x,B,hall,hdisj,hB0,hle=>by
  simp only [List.all_cons,Bool.and_eq_true] at hall
  unfold z39 at hdisj
  simp only [Bool.and_eq_true,Nat.ble_eq] at hdisj
  have hb1:=z41 hall.1
  have hb2:=z41 hall.2.1
  have he12:(e1.p2:ℝ)/e1.q2 ≤ (e2.p1:ℝ)/e2.q1:=by
   rw [div_le_div_iff₀ (Nat.cast_pos.mpr hb1.2.1) (Nat.cast_pos.mpr hb2.1)]
   exact_mod_cast hdisj.1
  have hall_t:(e2 :: t).all z40=true:=by
   simp only [List.all_cons,Bool.and_eq_true];exact hall.2
  have hle_tail:∀ l':List CertEntry,l'.all z40=true→ z39 l'=true →
    ∀ a0:ℝ,(∀ e0∈l'.head?,a0 ≤ (e0.p1:ℝ)/e0.q1) →
    ∀ e∈l',a0 ≤ (e.p1:ℝ)/e.q1:=by
   intro l'
   induction l' with
   | nil=>intro _ _ _ _ e he;simp at he
   | cons hd tl ih =>
    intro hal hdj a0 ha0 e he
    simp only [List.mem_cons] at he
    rcases he with rfl | htl
    ·
     exact ha0 e (by simp)
    ·
     cases tl with
     | nil=>simp at htl
     | cons hd2 tl2 =>
      simp only [List.all_cons,Bool.and_eq_true] at hal
      unfold z39 at hdj
      simp only [Bool.and_eq_true,Nat.ble_eq] at hdj
      have hba:=z41 hal.1
      have hbb:=z41 hal.2.1
      have h12:(hd.p2:ℝ)/hd.q2 ≤ (hd2.p1:ℝ)/hd2.q1:=by
       rw [div_le_div_iff₀ (Nat.cast_pos.mpr hba.2.1) (Nat.cast_pos.mpr hbb.1)]
       exact_mod_cast hdj.1
      have ha0':a0 ≤ (hd2.p1:ℝ)/hd2.q1:=
       (ha0 hd (by simp)).trans (hba.2.2.1.le.trans h12)
      exact ih (by simp [List.all_cons,hal.2]) hdj.2 a0 (fun e0 he0=>by simp at he0;subst he0;exact ha0') e htl
  by_cases h1:(e1.p1:ℝ)/e1.q1< x∧x< (e1.p2:ℝ)/e1.q2
  ·
   have htail_zero:((e2 :: t).map fun e =>
     if (e.p1:ℝ)/e.q1< x∧x< (e.p2:ℝ)/e.q2 then e.v else 0).sum=0:=by
    rw [List.sum_eq_zero_iff]
    intro val hval
    rcases List.mem_map.mp hval with ⟨e,he,rfl⟩
    have hge:(e1.p2:ℝ)/e1.q2 ≤ (e.p1:ℝ)/e.q1:=
     hle_tail (e2 :: t) hall_t hdisj.2 ((e1.p2:ℝ)/e1.q2)
      (fun e0 he0=>by simp at he0;subst he0;exact he12) e he
    rw [if_neg];intro hlt;linarith [h1.2,hlt.1]
   rw [List.map_cons,List.sum_cons,if_pos h1,htail_zero,add_zero]
   exact hle e1 (by simp) h1.1 h1.2
  ·
   simp only [List.map_cons,List.sum_cons,if_neg h1,zero_add]
   exact z70 (e2 :: t) x B hall_t hdisj.2 hB0
    (fun e he hlo hhi=>hle e (by simp [he]) hlo hhi)
private lemma z170 (L:List CertEntry)
  (hL1:L.all z40=true) (hL2:z39 L=true)
  (n p:ℕ) {y:ℝ} (hy0:0 ≤ y) (hy1:y< 1)
  (hnonneg:0 ≤ phi0 ((n:ℝ)/p) y) :
  (z169 L n p:ℤ) ≤ phi0 ((n:ℝ)/p) y:=by
 unfold z169
 split_ifs with hp
 ·
  rcases eq_or_ne n 0 with rfl | hn0
  ·
   simp only [Nat.cast_zero,zero_div]
   have h0:∑ k∈Finset.range 10,(L.map fun e =>
     if (0:ℝ)< (p:ℝ)∧(p:ℝ)< 0 then e.v else 0).sum=0:=by
    refine Finset.sum_eq_zero fun k _=>?_
    rw [List.sum_eq_zero_iff]
    intro v hv;rcases List.mem_map.mp hv with ⟨e,_,rfl⟩
    rw [if_neg];intro h;linarith
   rw [h0];simpa using hnonneg
  have hnpos:(0:ℝ)< n:=Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hppos:(0:ℝ)< p:=by
   have:0< p*p:=lt_of_le_of_lt (Nat.zero_le _) hp.1
   exact Nat.cast_pos.mpr (Nat.pos_of_mul_pos_left this)
  set x:=(n:ℝ)/p
  set k0:ℕ:=⌊x⌋₊
  have hterm_eq:∀ k∈Finset.range 10,
    (L.map fun e =>
     if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
       (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then e.v else 0).sum =
    if k=k0 then
     (L.map fun e =>
      if (e.p1:ℝ)/e.q1< x-(k0:ℝ)∧x-(k0:ℝ)< (e.p2:ℝ)/e.q2 then e.v else 0).sum
    else 0:=by
   intro k _
   have hall:=hL1
   simp only [List.all_eq_true] at hall
   by_cases hkk0:k=k0
   ·
    subst hkk0
    rw [if_pos rfl]
    congr 1
    refine List.map_congr_left fun e he=>?_
    have hb:=z41 (hall e he)
    have hd1:0< (k0:ℝ)+(e.p1:ℝ)/e.q1:=by linarith [hb.2.2.2.1,Nat.cast_nonneg (α:=ℝ) k0]
    have hd2:0< (k0:ℝ)+(e.p2:ℝ)/e.q2:=by linarith [hb.2.2.1]
    have hiff:((n:ℝ)/((k0:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
      (p:ℝ)< (n:ℝ)/((k0:ℝ)+(e.p1:ℝ)/e.q1)) ↔
      ((e.p1:ℝ)/e.q1< x-(k0:ℝ)∧x-(k0:ℝ)< (e.p2:ℝ)/e.q2):=by
     rw [div_lt_iff₀ hd2,lt_div_iff₀ hd1]
     have hx1:(e.p1:ℝ)/e.q1< x-(k0:ℝ)↔((k0:ℝ)+(e.p1:ℝ)/e.q1)*p< n:=by
      simp only [x];rw [lt_sub_iff_add_lt',lt_div_iff₀ hppos]
     have hx2:x-(k0:ℝ)< (e.p2:ℝ)/e.q2↔(n:ℝ)< ((k0:ℝ)+(e.p2:ℝ)/e.q2)*p:=by
      simp only [x];rw [sub_lt_iff_lt_add',div_lt_iff₀ hppos]
     rw [hx1,hx2];constructor <;> intro ⟨h1,h2⟩ <;> exact ⟨by linarith,by linarith⟩
    simp only [hiff]
   ·
    rw [if_neg hkk0,List.sum_eq_zero_iff]
    intro val hval
    rcases List.mem_map.mp hval with ⟨e,he,rfl⟩
    rw [if_neg]
    intro ⟨h1,h2⟩
    have hb:=z41 (hall e he)
    have hd1:0< (k:ℝ)+(e.p1:ℝ)/e.q1:=by linarith [hb.2.2.2.1,Nat.cast_nonneg (α:=ℝ) k]
    have hd2:0< (k:ℝ)+(e.p2:ℝ)/e.q2:=by linarith [hb.2.2.1]
    rw [div_lt_iff₀ hd2] at h1
    rw [lt_div_iff₀ hd1] at h2
    have hx_lo:(k:ℝ)< x:=by
     have:(k:ℝ)*p< n:=by nlinarith [hb.2.2.2.1]
     exact (lt_div_iff₀ hppos).mpr this
    have hx_hi:x< (k:ℝ)+1:=by
     have:(n:ℝ)< ((k:ℝ)+1)*p:=by nlinarith [hb.2.2.2.2]
     exact (div_lt_iff₀ hppos).mpr this
    have hk_eq:k=k0:=by
     have:⌊x⌋₊=k:=Nat.floor_eq_iff (by positivity:(0:ℝ) ≤ x) |>.mpr ⟨hx_lo.le,hx_hi⟩
     exact this.symm
    exact hkk0 hk_eq
  rw [Finset.sum_congr rfl hterm_eq]
  by_cases hk0:k0∈Finset.range 10
  ·
   rw [Finset.sum_ite_eq' (Finset.range 10) k0,if_pos hk0]
   have hshift:phi0 x y=phi0 (x-(k0:ℝ)) y:=by
    have h:=z166 (x-(k0:ℝ)) y (k0:ℤ)
    have heq:x-(k0:ℝ)+((k0:ℤ):ℝ)=x:=by push_cast;ring
    rw [heq] at h;exact h
   rw [hshift]
   refine z70 L (x-(k0:ℝ)) (phi0 (x-(k0:ℝ)) y)
    hL1 hL2 (by rwa [← hshift]) fun e he hlo hhi=>?_
   have hall:=hL1
   simp only [List.all_eq_true] at hall
   exact z42 (hall e he) hlo hhi hy0 hy1
  ·
   rw [Finset.sum_ite_eq' (Finset.range 10) k0,if_neg hk0]
   simpa using hnonneg
 ·
  simpa using hnonneg
lemma z172 (n p:ℕ) {y:ℝ} (hy0:0 ≤ y) (hy1:y< 1)
  (hnonneg:0 ≤ phi0 ((n:ℝ)/p) y) :
  (z168 n p:ℤ) ≤ phi0 ((n:ℝ)/p) y:=
 z170 z36 z37.1 z37.2.1 n p hy0 hy1 hnonneg
private lemma z171 (L:List CertEntry)
  (hL1:L.all z40=true)
  (n p:ℕ) (hpos:0< z169 L n p) {y:ℝ} (hy0:0 ≤ y) (hy1:y< 1) :
  (91*n< p*p∧p ≤ 33*n)∧0 ≤ phi0 ((n:ℝ)/p) y:=by
 unfold z169 at hpos
 split_ifs at hpos with hp
 ·
  refine ⟨hp,?_⟩
  have hn0:n≠0:=by
   intro h0;subst h0
   simp only [Nat.cast_zero] at hpos
   have:∑ k∈Finset.range 10,(L.map fun e =>
     if (0:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
      (p:ℝ)< (0:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then e.v else 0).sum=0:=by
    refine Finset.sum_eq_zero fun k _=>?_
    rw [List.sum_eq_zero_iff]
    intro v hv;rcases List.mem_map.mp hv with ⟨e,_,rfl⟩
    rw [zero_div,zero_div,if_neg];intro h;linarith
   omega
  have hppos:(0:ℝ)< p:=Nat.cast_pos.mpr (Nat.pos_of_mul_pos_left (lt_of_le_of_lt (Nat.zero_le _) hp.1))
  obtain ⟨k,_,hkpos⟩ : ∃ k∈Finset.range 10,
    0< (L.map fun e =>
     if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
      (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then e.v else 0).sum:=by
   by_contra! hall0
   have:∑ k∈Finset.range 10,(L.map fun e =>
     if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
      (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then e.v else 0).sum=0:=
    Finset.sum_eq_zero fun k hk=>Nat.le_zero.mp (hall0 k hk)
   omega
  obtain ⟨val,hval_mem,hval_pos⟩ : ∃ val∈(L.map fun e =>
     if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
      (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then e.v else 0),0< val:=by
   by_contra! hall0
   have:(L.map fun e =>
     if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
      (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then e.v else 0).sum=0:=
    List.sum_eq_zero_iff.mpr fun v hv=>Nat.le_zero.mp (hall0 v hv)
   omega
  rcases List.mem_map.mp hval_mem with ⟨e,he,rfl⟩
  split_ifs at hval_pos with hlt
  ·
   have hall:=List.all_eq_true.mp hL1
   have hb:=z41 (hall e he)
   have hd1:0< (k:ℝ)+(e.p1:ℝ)/e.q1:=by linarith [hb.2.2.2.1,Nat.cast_nonneg (α:=ℝ) k]
   have hd2:0< (k:ℝ)+(e.p2:ℝ)/e.q2:=by linarith [hb.2.2.1]
   have h1:=(div_lt_iff₀ hd2).mp hlt.1
   have h2:=(lt_div_iff₀ hd1).mp hlt.2
   have hlo:(e.p1:ℝ)/e.q1< (n:ℝ)/p-(k:ℝ):=by
    rw [lt_sub_iff_add_lt',lt_div_iff₀ hppos];linarith
   have hhi:(n:ℝ)/p-(k:ℝ)< (e.p2:ℝ)/e.q2:=by
    rw [sub_lt_iff_lt_add',div_lt_iff₀ hppos];linarith
   have hshift:phi0 ((n:ℝ)/p) y=phi0 ((n:ℝ)/p-(k:ℝ)) y:=by
    have h:=z166 ((n:ℝ)/p-(k:ℝ)) y (k:ℤ)
    have heq:(n:ℝ)/p-(k:ℝ)+((k:ℤ):ℝ)=(n:ℝ)/p:=by push_cast;ring
    rw [heq] at h;exact h
   rw [hshift]
   exact le_trans (Int.natCast_nonneg e.v) (z42 (hall e he) hlo hhi hy0 hy1)
  ·
   omega
 ·
  omega
lemma z173 (n p:ℕ) (hpos:0< z168 n p) {y:ℝ} (hy0:0 ≤ y) (hy1:y< 1) :
  (91*n< p*p∧p ≤ 33*n)∧(z168 n p:ℤ) ≤ phi0 ((n:ℝ)/p) y:=by
 have h:=z171 z36 z37.1 n p hpos hy0 hy1
 exact ⟨h.1,z172 n p hy0 hy1 h.2⟩
private lemma z254 {e:CertEntry} (hchk:z40 e=true) :
  (z253 e:ℝ)/100000 ≤
   (e.v:ℝ)*∑ k∈Finset.range 10,
    (1/((k:ℝ)+(e.p1:ℝ)/e.q1)-1/((k:ℝ)+(e.p2:ℝ)/e.q2)):=by
 have hb:=z41 hchk
 have hq1r:(0:ℝ)< e.q1:=Nat.cast_pos.mpr hb.1
 have hq2r:(0:ℝ)< e.q2:=Nat.cast_pos.mpr hb.2.1
 have hp_lt:e.p1*e.q2< e.p2*e.q1:=by
  have:=hb.2.2.1;rw [div_lt_div_iff₀ hq1r hq2r] at this;exact_mod_cast this
 have hfold:∀ (l:List ℕ) (init:ℕ),
   l.foldl (fun acc k=>acc+(100000*e.v*(e.p2*e.q1-e.p1*e.q2)) /
    ((k*e.q1+e.p1)*(k*e.q2+e.p2))) init =
   init+(l.map fun k=>(100000*e.v*(e.p2*e.q1-e.p1*e.q2)) /
    ((k*e.q1+e.p1)*(k*e.q2+e.p2))).sum:=by
  intro l
  induction l with
  | nil=>intro init;simp
  | cons h t ih =>
   intro init;simp only [List.foldl_cons,List.map_cons,List.sum_cons];rw [ih];omega
 unfold z253
 rw [hfold,zero_add]
 have hlist_sum:(((List.range 10).map fun k=>(100000*e.v*(e.p2*e.q1-e.p1*e.q2)) /
   ((k*e.q1+e.p1)*(k*e.q2+e.p2))).sum:ℕ) =
   ∑ k∈Finset.range 10,(100000*e.v*(e.p2*e.q1-e.p1*e.q2)) /
   ((k*e.q1+e.p1)*(k*e.q2+e.p2)):=by
  have haux:∀ (f:ℕ→ ℕ) (m:ℕ),((List.range m).map f).sum=∑ k∈Finset.range m,f k:=by
   intro f m
   induction m with
   | zero=>simp
   | succ m ih =>
    rw [List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,
     Finset.sum_range_succ,ih]
  exact haux _ 10
 rw [hlist_sum,Nat.cast_sum,Finset.sum_div,Finset.mul_sum]
 refine Finset.sum_le_sum fun k _=>?_
 have hd1:(0:ℝ)< (k:ℝ)*e.q1+e.p1:=by
  have:(0:ℝ)< e.p1:=by
   have h1:=hb.2.2.2.1;have:(0:ℝ)< (e.p1:ℝ)/e.q1:=by linarith
   exact (div_pos_iff_of_pos_right hq1r).mp this
  positivity
 have hd2:(0:ℝ)< (k:ℝ)*e.q2+e.p2:=by
  have:(0:ℝ)< e.p2:=by
   have h1:=hb.2.2.2.1.trans_lt hb.2.2.1;have:(0:ℝ)< (e.p2:ℝ)/e.q2:=by linarith
   exact (div_pos_iff_of_pos_right hq2r).mp this
  positivity
 have hden_pos:(0:ℝ)< ((k:ℝ)*e.q1+e.p1)*((k:ℝ)*e.q2+e.p2):=mul_pos hd1 hd2
 have hnat_le:(((100000*e.v*(e.p2*e.q1-e.p1*e.q2)) /
   ((k*e.q1+e.p1)*(k*e.q2+e.p2)):ℕ):ℝ) *
   (((k:ℝ)*e.q1+e.p1)*((k:ℝ)*e.q2+e.p2)) ≤
   (100000:ℝ)*e.v*((e.p2:ℝ)*e.q1-(e.p1:ℝ)*e.q2):=by
  have h1:=Nat.div_mul_le_self (100000*e.v*(e.p2*e.q1-e.p1*e.q2))
   ((k*e.q1+e.p1)*(k*e.q2+e.p2))
  have h2:(((100000*e.v*(e.p2*e.q1-e.p1*e.q2)) /
    ((k*e.q1+e.p1)*(k*e.q2+e.p2)):ℕ):ℝ) *
    ((((k*e.q1+e.p1)*(k*e.q2+e.p2):ℕ):ℝ)) ≤
    ((100000*e.v*(e.p2*e.q1-e.p1*e.q2):ℕ):ℝ):=by exact_mod_cast h1
  rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_sub hp_lt.le] at h2
  push_cast at h2 ⊢
  exact h2
 have hident:1/((k:ℝ)+(e.p1:ℝ)/e.q1)-1/((k:ℝ)+(e.p2:ℝ)/e.q2) =
   ((e.p2:ℝ)*e.q1-(e.p1:ℝ)*e.q2)/(((k:ℝ)*e.q1+e.p1)*((k:ℝ)*e.q2+e.p2)):=by
  have h1:(k:ℝ)+(e.p1:ℝ)/e.q1=((k:ℝ)*e.q1+e.p1)/e.q1:=by
   field_simp [hq1r.ne']
  have h2:(k:ℝ)+(e.p2:ℝ)/e.q2=((k:ℝ)*e.q2+e.p2)/e.q2:=by
   field_simp [hq2r.ne']
  rw [h1,h2,one_div_div,one_div_div]
  rw [div_sub_div _ _ hd1.ne' hd2.ne']
  congr 1;ring
 rw [hident,div_le_iff₀ (by positivity:(0:ℝ)< 100000)]
 rw [← mul_div_assoc,mul_comm _ (100000:ℝ),← mul_div_assoc,le_div_iff₀ hden_pos]
 linarith
private theorem z122 (L:List CertEntry)
  (hL1:L.all z40=true)
  (hL3:17610000 ≤ (L.foldl (fun acc e=>acc+z253 e) 0))
  (htheta:Tendsto (fun x:ℝ=>Chebyshev.theta x/x) atTop (𝓝 1)) :
  ∀ᶠ n:ℕ in atTop,
   (176:ℝ)*(n:ℝ) ≤
    ∑ p∈(Nat.primesLE (33*n)),(z169 L n p:ℝ)*Real.log (p:ℝ):=by
 have hsum_ge:(176.1:ℝ) ≤
   (L.map fun e=>(e.v:ℝ)*∑ k∈Finset.range 10,
    (1/((k:ℝ)+(e.p1:ℝ)/e.q1)-1/((k:ℝ)+(e.p2:ℝ)/e.q2))).sum:=by
  have hfold:∀ (l:List CertEntry) (init:ℕ),
    l.foldl (fun acc e=>acc+z253 e) init =
    init+(l.map z253).sum:=by
   intro l
   induction l with
   | nil=>intro init;simp
   | cons h t ih=>intro init;simp only [List.foldl_cons,List.map_cons,List.sum_cons];rw [ih];omega
  have hcert:=hL3
  rw [hfold,zero_add] at hcert
  have hcert_r:(176.1:ℝ) ≤ ((L.map z253).sum:ℝ)/100000:=by
   have:(17610000:ℝ) ≤ ((L.map z253).sum:ℝ):=by exact_mod_cast hcert
   linarith
  refine hcert_r.trans ?_
  have hdiv:∀ (l:List CertEntry),
    ((l.map z253).sum:ℝ)/100000 =
    (l.map fun e=>(z253 e:ℝ)/100000).sum:=by
   intro l
   induction l with
   | nil=>simp
   | cons h t ih=>simp only [List.map_cons,List.sum_cons,Nat.cast_add,add_div,ih]
  rw [hdiv L]
  have hall:=hL1
  simp only [List.all_eq_true] at hall
  have hle_list:∀ (l:List CertEntry),(∀ e∈l,z40 e=true) →
    (l.map fun e=>(z253 e:ℝ)/100000).sum ≤
    (l.map fun e=>(e.v:ℝ)*∑ k∈Finset.range 10,
     (1/((k:ℝ)+(e.p1:ℝ)/e.q1)-1/((k:ℝ)+(e.p2:ℝ)/e.q2))).sum:=by
   intro l
   induction l with
   | nil=>intro _;simp
   | cons h t ih =>
    intro hl
    simp only [List.map_cons,List.sum_cons]
    exact add_le_add (z254 (hl h (by simp)))
     (ih fun e he=>hl e (by simp [he]))
  exact hle_list L hall
 have hsingle_tend:∀ (a b:ℝ),(1:ℝ)/33 ≤ a→ a< b→ b ≤ 10 →
   Tendsto (fun n:ℕ =>
    (∑ p∈Nat.primesLE (33*n),
     if (n:ℝ)/b< (p:ℝ)∧(p:ℝ)< (n:ℝ)/a then Real.log (p:ℝ) else 0)/(n:ℝ))
    atTop (𝓝 (1/a-1/b)):=by
  intro a b ha hab hb
  have ha_pos:0< a:=by linarith
  have hb_pos:0< b:=by linarith
  have ht_a:Tendsto (fun n:ℕ=>Chebyshev.theta ((n:ℝ)/a)/(n:ℝ)) atTop (𝓝 (1/a)):=by
   have h1:=htheta.comp (tendsto_natCast_atTop_atTop.atTop_div_const ha_pos)
   have h2:=h1.div_const a
   simpa [one_div] using h2.congr' (by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnr:(0:ℝ)< n:=Nat.cast_pos.mpr hn
    simp only [Function.comp_apply]
    field_simp [ha_pos.ne',hnr.ne'])
  have ht_b:Tendsto (fun n:ℕ=>Chebyshev.theta ((n:ℝ)/b)/(n:ℝ)) atTop (𝓝 (1/b)):=by
   have h1:=htheta.comp (tendsto_natCast_atTop_atTop.atTop_div_const hb_pos)
   have h2:=h1.div_const b
   simpa [one_div] using h2.congr' (by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnr:(0:ℝ)< n:=Nat.cast_pos.mpr hn
    simp only [Function.comp_apply]
    field_simp [hb_pos.ne',hnr.ne'])
  have hlog_zero:Tendsto (fun n:ℕ=>Real.log (33*(n:ℝ))/(n:ℝ)) atTop (𝓝 0):=by
   have h1:Tendsto (fun x:ℝ=>Real.log x/x) atTop (𝓝 0):=by
    simpa [Real.rpow_neg_one,div_eq_mul_inv] using
     Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
   have h2:=h1.comp ((tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity:(0:ℝ)< 33)))
   have h3:=h2.const_mul 33
   simpa using h3.congr' (by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnr:(0:ℝ)< n:=Nat.cast_pos.mpr hn
    simp only [Function.comp_apply]
    field_simp [hnr.ne'])
  have hdiff:=ht_a.sub ht_b
  have hlo:Tendsto (fun n:ℕ =>
    (Chebyshev.theta ((n:ℝ)/a)-Chebyshev.theta ((n:ℝ)/b))/(n:ℝ) -
    Real.log (33*(n:ℝ))/(n:ℝ)) atTop (𝓝 (1/a-1/b)):=by
   have:=hdiff.sub hlog_zero
   simpa [sub_div] using this
  have hhi:Tendsto (fun n:ℕ =>
    (Chebyshev.theta ((n:ℝ)/a)-Chebyshev.theta ((n:ℝ)/b))/(n:ℝ)) atTop (𝓝 (1/a-1/b)):=by
   simpa [sub_div] using hdiff
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  ·
   filter_upwards [eventually_ge_atTop 1] with n hn
   have hnr:(0:ℝ)< n:=Nat.cast_pos.mpr hn
   rw [← sub_div]
   refine div_le_div_of_nonneg_right ?_ hnr.le
   rw [Chebyshev.theta_eq_sum_primesLE,Chebyshev.theta_eq_sum_primesLE]
   have hsub_set:Nat.primesLE ⌊(n:ℝ)/b⌋₊ ⊆ Nat.primesLE ⌊(n:ℝ)/a⌋₊:=by
    intro p hp
    simp only [Nat.mem_primesLE] at hp ⊢
    refine ⟨?_,hp.2⟩
    exact hp.1.trans (Nat.floor_mono (div_le_div_of_nonneg_left hnr.le ha_pos hab.le))
   have hsub_33:Nat.primesLE ⌊(n:ℝ)/a⌋₊ ⊆ Nat.primesLE (33*n):=by
    intro p hp
    simp only [Nat.mem_primesLE] at hp ⊢
    refine ⟨?_,hp.2⟩
    have hle33:(n:ℝ)/a ≤ (33*n:ℕ):=by
     push_cast
     rw [div_le_iff₀ ha_pos];nlinarith
    exact hp.1.trans (Nat.floor_le_of_le hle33)
   rw [← Finset.sum_sdiff hsub_set]
   have hsdiff_split:∑ p∈Nat.primesLE ⌊(n:ℝ)/a⌋₊ \ Nat.primesLE ⌊(n:ℝ)/b⌋₊,Real.log (p:ℝ) ≤
     (∑ p∈Nat.primesLE (33*n),
       if (n:ℝ)/b< (p:ℝ)∧(p:ℝ)< (n:ℝ)/a then Real.log (p:ℝ) else 0) +
     Real.log (33*(n:ℝ)):=by
    set M:=⌊(n:ℝ)/a⌋₊
    have hM_le:(M:ℝ) ≤ 33*(n:ℝ):=by
     calc
       (M:ℝ) ≤ (n:ℝ)/a:=Nat.floor_le (by positivity)
       _ ≤ 33*(n:ℝ):=by rw [div_le_iff₀ ha_pos];nlinarith
    have hrest:∑ p∈(Nat.primesLE M \ Nat.primesLE ⌊(n:ℝ)/b⌋₊).erase M,Real.log (p:ℝ) ≤
       ∑ p∈Nat.primesLE (33*n),
         if (n:ℝ)/b< (p:ℝ)∧(p:ℝ)< (n:ℝ)/a then Real.log (p:ℝ) else 0:=by
     rw [← Finset.sum_filter]
     refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p hp _ =>
       Real.log_nonneg (by
         have:=(Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2.one_lt
         exact_mod_cast this.le))
     intro p hp
     rw [Finset.mem_erase,Finset.mem_sdiff] at hp
     rw [Finset.mem_filter]
     refine ⟨hsub_33 hp.2.1,?_,?_⟩
     ·
       by_contra! hle
       apply hp.2.2
       rw [Nat.mem_primesLE]
       exact ⟨Nat.le_floor hle,(Nat.mem_primesLE.mp hp.2.1).2⟩
     ·
       have hpm:p< M:=lt_of_le_of_ne (Nat.mem_primesLE.mp hp.2.1).1 hp.1
       have hpm_r:(p:ℝ)< M:=by exact_mod_cast hpm
       exact hpm_r.trans_le (Nat.floor_le (by positivity))
    by_cases hM_mem:M∈Nat.primesLE M \ Nat.primesLE ⌊(n:ℝ)/b⌋₊
    ·
     rw [← Finset.add_sum_erase _ _ hM_mem]
     have hM_pos:(0:ℝ)< M:=by
       have:=(Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hM_mem).1).2.pos
       exact Nat.cast_pos.mpr this
     have hlogM:Real.log (M:ℝ) ≤ Real.log (33*(n:ℝ)):=
       Real.log_le_log hM_pos hM_le
     linarith
    ·
     rw [Finset.erase_eq_of_notMem hM_mem] at hrest
     have hn1r:(1:ℝ) ≤ n:=by exact_mod_cast hn
     have hlog_nn:0 ≤ Real.log (33*(n:ℝ)):=Real.log_nonneg (by linarith)
     linarith
   linarith
  ·
   filter_upwards [eventually_ge_atTop 1] with n hn
   have hnr:(0:ℝ)< n:=Nat.cast_pos.mpr hn
   refine div_le_div_of_nonneg_right ?_ hnr.le
   rw [Chebyshev.theta_eq_sum_primesLE,Chebyshev.theta_eq_sum_primesLE]
   have hsub_set:Nat.primesLE ⌊(n:ℝ)/b⌋₊ ⊆ Nat.primesLE ⌊(n:ℝ)/a⌋₊:=by
    intro p hp
    simp only [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans (Nat.floor_mono (div_le_div_of_nonneg_left hnr.le ha_pos hab.le)),hp.2⟩
   rw [← Finset.sum_sdiff hsub_set,add_sub_cancel_right,← Finset.sum_filter]
   refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p hp _ =>
    Real.log_nonneg (by
     have:=(Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2.one_lt
     exact_mod_cast this.le))
   intro p hp
   rw [Finset.mem_filter] at hp
   rw [Finset.mem_sdiff]
   have hpr:=(Nat.mem_primesLE.mp hp.1).2
   refine ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hp.2.2.le,hpr⟩,?_⟩
   intro hmem
   have hle:=(Nat.mem_primesLE.mp hmem).1
   have hle_r:(p:ℝ) ≤ (n:ℝ)/b:=(Nat.cast_le.mpr hle).trans (Nat.floor_le (by positivity))
   linarith [hp.2.1]
 have htotal_tend:Tendsto (fun n:ℕ =>
   ((L.map fun e=>(e.v:ℝ)*∑ k∈Finset.range 10,
    (∑ p∈Nat.primesLE (33*n),
     if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
        (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then Real.log (p:ℝ) else 0)).sum)/(n:ℝ))
   atTop (𝓝 ((L.map fun e=>(e.v:ℝ)*∑ k∈Finset.range 10,
    (1/((k:ℝ)+(e.p1:ℝ)/e.q1)-1/((k:ℝ)+(e.p2:ℝ)/e.q2))).sum)):=by
  have hall:=hL1
  simp only [List.all_eq_true] at hall
  have hlist:∀ (l:List CertEntry),(∀ e∈l,z40 e=true) →
    Tendsto (fun n:ℕ =>
     ((l.map fun e=>(e.v:ℝ)*∑ k∈Finset.range 10,
       (∑ p∈Nat.primesLE (33*n),
         if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
            (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then Real.log (p:ℝ) else 0)).sum)/(n:ℝ))
     atTop (𝓝 ((l.map fun e=>(e.v:ℝ)*∑ k∈Finset.range 10,
       (1/((k:ℝ)+(e.p1:ℝ)/e.q1)-1/((k:ℝ)+(e.p2:ℝ)/e.q2))).sum)):=by
   intro l
   induction l with
   | nil=>intro _;simp [tendsto_const_nhds]
   | cons e t ih =>
    intro hl
    have hb:=z41 (hl e (by simp))
    have he_tend:Tendsto (fun n:ℕ =>
       ((e.v:ℝ)*∑ k∈Finset.range 10,
         (∑ p∈Nat.primesLE (33*n),
           if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
              (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then Real.log (p:ℝ) else 0))/(n:ℝ))
       atTop (𝓝 ((e.v:ℝ)*∑ k∈Finset.range 10,
         (1/((k:ℝ)+(e.p1:ℝ)/e.q1)-1/((k:ℝ)+(e.p2:ℝ)/e.q2)))):=by
     have hk:∀ k∈Finset.range 10,
         Tendsto (fun n:ℕ =>
           (∑ p∈Nat.primesLE (33*n),
             if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
               (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then Real.log (p:ℝ) else 0)/(n:ℝ))
           atTop (𝓝 (1/((k:ℝ)+(e.p1:ℝ)/e.q1)-1/((k:ℝ)+(e.p2:ℝ)/e.q2))):=by
       intro k hk
       have hk9:k ≤ 9:=Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
       have hk9r:(k:ℝ) ≤ 9:=by exact_mod_cast hk9
       exact hsingle_tend ((k:ℝ)+(e.p1:ℝ)/e.q1) ((k:ℝ)+(e.p2:ℝ)/e.q2)
         (by linarith [hb.2.2.2.1]) (by linarith [hb.2.2.1]) (by linarith [hb.2.2.2.2])
     have hfin:=tendsto_finset_sum (Finset.range 10) hk
     have hmul:=hfin.const_mul (e.v:ℝ)
     refine hmul.congr fun n=>?_
     rw [← Finset.sum_div,mul_div_assoc]
    have hadd:=he_tend.add (ih fun e' he'=>hl e' (by simp [he']))
    refine hadd.congr fun n=>?_
    simp only [List.map_cons,List.sum_cons,add_div]
  exact hlist L hall
 have hev_gt:∀ᶠ n:ℕ in atTop,
   (176:ℝ)< ((L.map fun e=>(e.v:ℝ)*∑ k∈Finset.range 10,
    (∑ p∈Nat.primesLE (33*n),
     if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
        (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then Real.log (p:ℝ) else 0)).sum)/(n:ℝ):=
  (tendsto_order.mp htotal_tend).1 176 (by linarith)
 filter_upwards [hev_gt,eventually_ge_atTop 9101] with n hgt hn
 have hnr:(0:ℝ)< n:=Nat.cast_pos.mpr (by omega)
 have hswapped:(L.map fun e=>(e.v:ℝ)*∑ k∈Finset.range 10,
   (∑ p∈Nat.primesLE (33*n),
    if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
      (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then Real.log (p:ℝ) else 0)).sum =
   ∑ p∈Nat.primesLE (33*n),(z169 L n p:ℝ)*Real.log (p:ℝ):=by
  have hall:=hL1
  simp only [List.all_eq_true] at hall
  have hlist_swap:∀ (l:List CertEntry),(∀ e∈l,z40 e=true) →
    (l.map fun e=>(e.v:ℝ)*∑ k∈Finset.range 10,
     (∑ p∈Nat.primesLE (33*n),
       if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
          (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then Real.log (p:ℝ) else 0)).sum =
    ∑ p∈Nat.primesLE (33*n),
     ((∑ k∈Finset.range 10,
       (l.map fun e =>
         if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
            (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then e.v else 0).sum:ℕ):ℝ) *
     Real.log (p:ℝ):=by
   intro l
   induction l with
   | nil=>intro _;simp
   | cons e t ih =>
    intro hl
    simp only [List.map_cons,List.sum_cons]
    rw [ih fun e' he'=>hl e' (by simp [he'])]
    have he_eq:(e.v:ℝ)*∑ k∈Finset.range 10,
       (∑ p∈Nat.primesLE (33*n),
         if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
            (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then Real.log (p:ℝ) else 0) =
       ∑ p∈Nat.primesLE (33*n),
         ((∑ k∈Finset.range 10,
           if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
              (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then e.v else 0:ℕ):ℝ) *
         Real.log (p:ℝ):=by
     rw [Finset.sum_comm,Finset.mul_sum]
     refine Finset.sum_congr rfl fun p _=>?_
     rw [Nat.cast_sum,Finset.sum_mul,Finset.mul_sum]
     refine Finset.sum_congr rfl fun k _=>?_
     split_ifs <;> simp
    rw [he_eq,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _=>?_
    rw [← add_mul,← Nat.cast_add,← Finset.sum_add_distrib]
  rw [hlist_swap L hall]
  refine Finset.sum_congr rfl fun p hp=>?_
  congr 1
  have hp33:p ≤ 33*n:=(Nat.mem_primesLE.mp hp).1
  unfold z169
  by_cases hsq:91*n< p*p
  ·
   rw [if_pos ⟨hsq,hp33⟩]
  ·
   rw [if_neg (by tauto)]
   simp only [Nat.cast_zero]
   suffices h0:∑ k∈Finset.range 10,
     (L.map fun e =>
       if (n:ℝ)/((k:ℝ)+(e.p2:ℝ)/e.q2)< (p:ℝ) ∧
          (p:ℝ)< (n:ℝ)/((k:ℝ)+(e.p1:ℝ)/e.q1) then e.v else 0).sum=0 by
    simp [h0]
   refine Finset.sum_eq_zero fun k hk=>?_
   rw [List.sum_eq_zero_iff]
   intro val hval
   rcases List.mem_map.mp hval with ⟨e,he,rfl⟩
   rw [if_neg]
   intro ⟨h1,_⟩
   have hb:=z41 (hall e he)
   have hk9:(k:ℝ) ≤ 9:=by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
   have hden:(k:ℝ)+(e.p2:ℝ)/e.q2 ≤ 10:=by linarith [hb.2.2.2.2]
   have hden_pos:0< (k:ℝ)+(e.p2:ℝ)/e.q2:=by linarith [hb.2.2.1,hb.2.2.2.1]
   have hp_gt:(n:ℝ)/10< (p:ℝ):=
    (div_le_div_of_nonneg_left hnr.le hden_pos hden).trans_lt h1
   have hp2_gt:91*(n:ℝ)< (p:ℝ)*(p:ℝ):=by nlinarith [show (9101:ℝ) ≤ n by exact_mod_cast hn]
   have:91*n< p*p:=by exact_mod_cast hp2_gt
   exact hsq this
 rw [← hswapped]
 exact ((lt_div_iff₀ hnr).mp hgt).le
theorem z121
  (htheta:Tendsto (fun x:ℝ=>Chebyshev.theta x/x) atTop (𝓝 1)) :
  ∀ᶠ n:ℕ in atTop,
   (176:ℝ)*(n:ℝ) ≤
    ∑ p∈(Nat.primesLE (33*n)),(z168 n p:ℝ)*Real.log (p:ℝ):=
 z122 z36 z37.1 z37.2.2 htheta
end Z2
namespace Z3
open scoped Real BigOperators
open Complex Filter Topology MeasureTheory
private lemma z99 {z:ℂ} (hsin:Complex.sin (π*z)≠0) :
  HasDerivAt (fun x:ℂ=>(π : ℂ)*Complex.cot ((π : ℂ)*x))
   (-((π : ℂ)^2)/Complex.sin ((π : ℂ)*z)^2) z:=by
 have h1:HasDerivAt (fun x:ℂ=>(π : ℂ)*x) (π : ℂ) z:=by
  simpa using (hasDerivAt_id z).const_mul (π : ℂ)
 have hcos:HasDerivAt (fun x:ℂ=>Complex.cos ((π : ℂ)*x))
   (-Complex.sin ((π : ℂ)*z)*(π : ℂ)) z:=
  (Complex.hasDerivAt_cos ((π : ℂ)*z)).comp z h1
 have hsin_d:HasDerivAt (fun x:ℂ=>Complex.sin ((π : ℂ)*x))
   (Complex.cos ((π : ℂ)*z)*(π : ℂ)) z:=
  (Complex.hasDerivAt_sin ((π : ℂ)*z)).comp z h1
 have hdiv:HasDerivAt (fun x:ℂ=>(π : ℂ)*(Complex.cos ((π : ℂ)*x)/Complex.sin ((π : ℂ)*x)))
   ((π : ℂ)*((-Complex.sin ((π : ℂ)*z)*(π : ℂ)*Complex.sin ((π : ℂ)*z) -
    Complex.cos ((π : ℂ)*z)*(Complex.cos ((π : ℂ)*z)*(π : ℂ))) /
    Complex.sin ((π : ℂ)*z)^2)) z:=
  (hcos.fun_div hsin_d hsin).const_mul (π : ℂ)
 have hfun:(fun x:ℂ=>(π : ℂ)*(Complex.cos ((π : ℂ)*x)/Complex.sin ((π : ℂ)*x))) =
   (fun x:ℂ=>(π : ℂ)*Complex.cot ((π : ℂ)*x)):=by
  funext x;rw [Complex.cot_eq_cos_div_sin]
 rw [hfun] at hdiv
 refine hdiv.congr_deriv ?_
 have hpyth:=Complex.sin_sq_add_cos_sq ((π : ℂ)*z)
 have hnum:-Complex.sin ((π : ℂ)*z)*(π : ℂ)*Complex.sin ((π : ℂ)*z) -
   Complex.cos ((π : ℂ)*z)*(Complex.cos ((π : ℂ)*z)*(π : ℂ))=-(π : ℂ):=by
  linear_combination -(π : ℂ)*hpyth
 rw [hnum]
 ring
private lemma z98 {z:ℂ} (hsin:Complex.sin (π*z)≠0) :
  HasDerivAt (fun x:ℂ=>-((π : ℂ)^2)/Complex.sin ((π : ℂ)*x)^2)
   (2*(π : ℂ)^3*Complex.cos ((π : ℂ)*z)/Complex.sin ((π : ℂ)*z)^3) z:=by
 have h1:HasDerivAt (fun x:ℂ=>(π : ℂ)*x) (π : ℂ) z:=by
  simpa using (hasDerivAt_id z).const_mul (π : ℂ)
 have hsin_d:HasDerivAt (fun x:ℂ=>Complex.sin ((π : ℂ)*x))
   (Complex.cos ((π : ℂ)*z)*(π : ℂ)) z:=
  (Complex.hasDerivAt_sin ((π : ℂ)*z)).comp z h1
 have hsq:HasDerivAt (fun x:ℂ=>Complex.sin ((π : ℂ)*x)^2)
   (2*Complex.sin ((π : ℂ)*z)*(Complex.cos ((π : ℂ)*z)*(π : ℂ))) z:=by
  simpa [pow_one] using hsin_d.fun_pow 2
 have hdiv:HasDerivAt (fun x:ℂ=>-((π : ℂ)^2)/Complex.sin ((π : ℂ)*x)^2)
   ((0*Complex.sin ((π : ℂ)*z)^2 -
    (-((π : ℂ)^2))*(2*Complex.sin ((π : ℂ)*z)*(Complex.cos ((π : ℂ)*z)*(π : ℂ)))) /
    (Complex.sin ((π : ℂ)*z)^2)^2) z:=
  (hasDerivAt_const z (-((π : ℂ)^2))).fun_div hsq (pow_ne_zero 2 hsin)
 convert hdiv using 1
 field_simp [hsin]
 ring
private lemma z256 {z:ℂ} (hz:z.im≠0) :
  Complex.sin ((π : ℂ)*z)≠0:=by
 intro h
 rw [Complex.sin_eq_zero_iff] at h
 obtain ⟨k,hk⟩:=h
 have hpi:(π : ℂ)≠0:=Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
 have hz_eq:z=k:=mul_left_cancel₀ hpi (by rw [hk];ring)
 have:z.im=0:=by rw [hz_eq];simp
 exact hz this
lemma z281 {z:ℂ} (hz:z.im≠0) :
  2*(π : ℂ)^3*Complex.cos ((π : ℂ)*z)/Complex.sin ((π : ℂ)*z)^3 =
   2*∑' m:ℤ,(1:ℂ)/(z-(m:ℂ))^3:=by
 have hpos_case:∀ w:ℂ,0< w.im →
   2*(π : ℂ)^3*Complex.cos ((π : ℂ)*w)/Complex.sin ((π : ℂ)*w)^3 =
    2*∑' m:ℤ,(1:ℂ)/(w-(m:ℂ))^3:=by
  intro w hw
  have hw_mem:w∈UpperHalfPlane.upperHalfPlaneSet:=hw
  have hcot:=iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow (k:=2) (by omega) hw_mem
  have hopen:IsOpen UpperHalfPlane.upperHalfPlaneSet:=UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hderiv1:∀ x∈UpperHalfPlane.upperHalfPlaneSet,
    derivWithin (fun u:ℂ=>(π : ℂ)*Complex.cot ((π : ℂ)*u))
     UpperHalfPlane.upperHalfPlaneSet x =
    -((π : ℂ)^2)/Complex.sin ((π : ℂ)*x)^2:=by
   intro x hx
   rw [derivWithin_of_isOpen hopen hx]
   exact (z99 (z256 (ne_of_gt hx))).deriv
  have hderiv2:iteratedDerivWithin 2 (fun u:ℂ=>(π : ℂ)*Complex.cot ((π : ℂ)*u))
    UpperHalfPlane.upperHalfPlaneSet w =
    2*(π : ℂ)^3*Complex.cos ((π : ℂ)*w)/Complex.sin ((π : ℂ)*w)^3:=by
   rw [iteratedDerivWithin_succ,iteratedDerivWithin_one]
   rw [derivWithin_congr hderiv1 (hderiv1 w hw_mem),derivWithin_of_isOpen hopen hw_mem]
   exact (z98 (z256 (ne_of_gt hw))).deriv
  rw [hderiv2] at hcot
  have hreindex:(∑' m:ℤ,(1:ℂ)/(w+(m:ℂ))^3) =
    ∑' m:ℤ,(1:ℂ)/(w-(m:ℂ))^3:=by
   rw [← (Equiv.neg ℤ).tsum_eq]
   congr 1;ext m;simp [sub_eq_add_neg]
  rw [hreindex] at hcot
  simpa [Nat.factorial] using hcot
 rcases lt_or_gt_of_ne hz with hneg | hpos
 ·
  have hconj_pos:0< ((starRingEnd ℂ) z).im:=by simp [hneg]
  have h:=hpos_case ((starRingEnd ℂ) z) hconj_pos
  have h2:=congrArg (starRingEnd ℂ) h
  have hsin_conj:(starRingEnd ℂ) (Complex.sin ((π : ℂ)*(starRingEnd ℂ) z)) =
    Complex.sin ((π : ℂ)*z):=by
   rw [← Complex.sin_conj]
   simp
  have hcos_conj:(starRingEnd ℂ) (Complex.cos ((π : ℂ)*(starRingEnd ℂ) z)) =
    Complex.cos ((π : ℂ)*z):=by
   rw [← Complex.cos_conj]
   simp
  have htsum_conj:(starRingEnd ℂ) (∑' m:ℤ,(1:ℂ)/((starRingEnd ℂ) z-(m:ℂ))^3) =
    ∑' m:ℤ,(1:ℂ)/(z-(m:ℂ))^3:=by
   rw [Complex.conj_tsum]
   congr 1;ext m
   simp
  simp only [map_div₀,map_mul,map_pow,map_ofNat,Complex.conj_ofReal,
   hcos_conj,hsin_conj,htsum_conj] at h2
  exact h2
 ·
  exact hpos_case z hpos
private lemma z135 (A y:ℝ) :
  ‖(A:ℂ)+(y:ℂ)*I‖=Real.sqrt (A^2+y^2):=by
 rw [Complex.norm_def,Complex.normSq_apply]
 simp [sq]
private lemma z28 {A:ℝ} (hA:A≠0) (y:ℝ) :
  (A:ℂ)+(y:ℂ)*I≠0:=by
 intro h
 have:=congrArg Complex.re h
 simp at this
 exact hA this
private lemma z105 {A:ℝ} (hA:A≠0) {m:ℕ} (hm:2 ≤ m) :
  Integrable (fun y:ℝ=>((A:ℂ)+(y:ℂ)*I)⁻¹^m):=by
 have hcont:Continuous (fun y:ℝ=>((A:ℂ)+(y:ℂ)*I)⁻¹^m):=by
  refine Continuous.pow (Continuous.inv₀ ?_ (fun y=>z28 hA y)) m
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
 have hint_sq:Integrable (fun y:ℝ=>(1+(y / |A|)^2)⁻¹):=by
  have h1:=integrable_inv_one_add_sq
  simpa [div_eq_mul_inv] using h1.comp_mul_right' (inv_ne_zero (abs_ne_zero.mpr hA))
 refine (hint_sq.const_mul (|A|⁻¹^m)).mono' hcont.aestronglyMeasurable
  (Filter.Eventually.of_forall fun y=>?_)
 rw [norm_pow,norm_inv,z135]
 have hsq:A^2+y^2=|A|^2*(1+(y / |A|)^2):=by
  have ha:|A|≠0:=abs_ne_zero.mpr hA
  field_simp [ha]
  rw [sq_abs]
 have h1p:1 ≤ 1+(y / |A|)^2:=by nlinarith [sq_nonneg (y / |A|)]
 have hsqrt:Real.sqrt (A^2+y^2)=|A| * Real.sqrt (1+(y / |A|)^2):=by
  rw [hsq,Real.sqrt_mul (sq_nonneg |A|),Real.sqrt_sq (abs_nonneg A)]
 rw [hsqrt,mul_inv,mul_pow]
 have hle:(Real.sqrt (1+(y / |A|)^2))⁻¹^m ≤ (Real.sqrt (1+(y / |A|)^2))⁻¹^2:=
  pow_le_pow_of_le_one (inv_nonneg.mpr (Real.sqrt_nonneg _))
   (inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr h1p)) hm
 have hsq2:(Real.sqrt (1+(y / |A|)^2))⁻¹^2=(1+(y / |A|)^2)⁻¹:=by
  rw [inv_pow,Real.sq_sqrt (by linarith)]
 rw [hsq2] at hle
 exact mul_le_mul_of_nonneg_left hle (pow_nonneg (inv_nonneg.mpr (abs_nonneg A)) m)
lemma z110 {A:ℝ} (hA:A≠0) {m:ℕ} (hm:2 ≤ m) :
  ∫ y:ℝ,((A:ℂ)+(y:ℂ)*I)⁻¹^m=0:=by
 set k:ℕ:=m-1
 have hk:1 ≤ k:=by omega
 have hkm:k+1=m:=by omega
 set F:ℝ→ ℂ:=fun y=>-((1:ℂ)/((k:ℂ)*I))*((A:ℂ)+(y:ℂ)*I)⁻¹^k
 have hderiv:∀ y:ℝ,HasDerivAt F (((A:ℂ)+(y:ℂ)*I)⁻¹^m) y:=by
  intro y
  have h1:HasDerivAt (fun t:ℝ=>(t:ℂ)) 1 y:=Complex.ofRealCLM.hasDerivAt
  have hlin:HasDerivAt (fun t:ℝ=>(A:ℂ)+(t:ℂ)*I) I y:=by
   have h2:=h1.mul_const I
   have h3:=(hasDerivAt_const y (A:ℂ)).fun_add h2
   simpa using h3
  have hne:(A:ℂ)+(y:ℂ)*I≠0:=z28 hA y
  have hinv:HasDerivAt (fun t:ℝ=>((A:ℂ)+(t:ℂ)*I)⁻¹)
    (-I/((A:ℂ)+(y:ℂ)*I)^2) y:=hlin.fun_inv hne
  have hpow:HasDerivAt (fun t:ℝ=>((A:ℂ)+(t:ℂ)*I)⁻¹^k)
    ((k:ℂ)*((A:ℂ)+(y:ℂ)*I)⁻¹^(k-1)*(-I/((A:ℂ)+(y:ℂ)*I)^2)) y:=
   hinv.fun_pow k
  have hmul:=hpow.const_mul (-((1:ℂ)/((k:ℂ)*I)))
  refine hmul.congr_deriv ?_
  have hk_ne:(k:ℂ)≠0:=Nat.cast_ne_zero.mpr (by omega)
  rw [← hkm]
  have hk1:k=(k-1)+1:=by omega
  rw [pow_succ,inv_pow,inv_pow]
  conv_rhs=>rw [hk1,pow_succ]
  field_simp [hne,hk_ne,Complex.I_ne_zero]
  ring
 have htend:∀ (l:Filter ℝ),Tendsto (fun y:ℝ=>|y|) l atTop→ Tendsto F l (𝓝 0):=by
  intro l hl
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hle:∀ᶠ y:ℝ in l,‖F y‖ ≤ (1/(k:ℝ))*(|y|⁻¹^k):=by
   filter_upwards [hl.eventually (eventually_ge_atTop (1:ℝ))] with y hy1
   simp only [F,norm_mul,norm_neg,norm_div,norm_one,norm_pow,norm_inv,
    Complex.norm_natCast,Complex.norm_I,mul_one,z135]
   have hyle:|y| ≤ Real.sqrt (A^2+y^2):=by
    calc
     |y|=Real.sqrt (y^2):=(Real.sqrt_sq_eq_abs y).symm
     _ ≤ Real.sqrt (A^2+y^2):=Real.sqrt_le_sqrt (by nlinarith [sq_nonneg A])
   have hinv_le:(Real.sqrt (A^2+y^2))⁻¹ ≤ |y|⁻¹:=
    inv_anti₀ (by linarith) hyle
   exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hinv_le k) (by positivity)
  have ht0:Tendsto (fun y:ℝ=>(1/(k:ℝ))*(|y|⁻¹^k)) l (𝓝 0):=by
   have h1:Tendsto (fun y:ℝ=>|y|⁻¹) l (𝓝 0):=tendsto_inv_atTop_zero.comp hl
   have h2:Tendsto (fun y:ℝ=>|y|⁻¹^k) l (𝓝 (0^k)):=h1.pow k
   rw [zero_pow (by omega)] at h2
   simpa using h2.const_mul (1/(k:ℝ))
  exact squeeze_zero' (Filter.Eventually.of_forall fun y=>norm_nonneg _) hle ht0
 have htop:Tendsto F atTop (𝓝 0):=
  htend atTop tendsto_abs_atTop_atTop
 have hbot:Tendsto F atBot (𝓝 0):=
  htend atBot tendsto_abs_atBot_atTop
 simpa using integral_of_hasDerivAt_of_tendsto hderiv (z105 hA hm) hbot htop
private lemma z113 {A:ℝ} (hA:0< A) :
  ∫ y:ℝ,A/(A^2+y^2)=π:=by
 have hfun:(fun y:ℝ=>A/(A^2+y^2))=(fun y:ℝ=>A⁻¹*(1+(A⁻¹*y)^2)⁻¹):=by
  funext y;field_simp [hA.ne']
 rw [hfun,integral_const_mul,Measure.integral_comp_mul_left (fun u=>(1+u^2)⁻¹) A⁻¹]
 rw [integral_univ_inv_one_add_sq,smul_eq_mul,inv_inv,abs_of_pos hA]
 field_simp [hA.ne']
private lemma z107 {A:ℝ} (hA:0< A) :
  Integrable (fun y:ℝ=>A/(A^2+y^2)):=by
 have hfun:(fun y:ℝ=>A/(A^2+y^2))=(fun y:ℝ=>A⁻¹*(1+(A⁻¹*y)^2)⁻¹):=by
  funext y;field_simp [hA.ne']
 rw [hfun]
 exact (integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hA.ne')).const_mul A⁻¹
private lemma z111 {A B:ℝ} (hA:A≠0) (hB:B≠0) :
  ∫ y:ℝ,(((A:ℂ)+(y:ℂ)*I)⁻¹ - ((B:ℂ)+(y:ℂ)*I)⁻¹) =
   (((if 0< A then π else -π)-(if 0< B then π else -π):ℝ):ℂ):=by
 have hre_fn:∀ C:ℝ,C≠0→ ∀ y:ℝ,
   (((C:ℂ)+(y:ℂ)*I)⁻¹) =
    ((C/(C^2+y^2):ℝ):ℂ)+(((-y)/(C^2+y^2):ℝ):ℂ)*I:=by
  intro C hC y
  have hden:(C^2+y^2:ℝ)≠0:=by positivity
  have hne:(C:ℂ)+(y:ℂ)*I≠0:=z28 hC y
  apply mul_left_cancel₀ hne
  rw [mul_inv_cancel₀ hne]
  push_cast
  have hdenC:((C:ℂ)^2+(y:ℂ)^2)≠0:=by exact_mod_cast hden
  field_simp [hdenC]
  ring_nf
  simp [Complex.I_sq]
 have hsplit:(fun y:ℝ=>((A:ℂ)+(y:ℂ)*I)⁻¹ - ((B:ℂ)+(y:ℂ)*I)⁻¹) =
   (fun y:ℝ =>
    (((A/(A^2+y^2):ℝ):ℂ)-((B/(B^2+y^2):ℝ):ℂ)) +
    (((y*(A^2-B^2)/((A^2+y^2)*(B^2+y^2)):ℝ):ℂ)*I)):=by
  funext y
  rw [hre_fn A hA y,hre_fn B hB y]
  have hA2:(A^2+y^2:ℝ)≠0:=by positivity
  have hB2:(B^2+y^2:ℝ)≠0:=by positivity
  have him:(-y)/(A^2+y^2)-(-y)/(B^2+y^2) =
    y*(A^2-B^2)/((A^2+y^2)*(B^2+y^2)):=by
   field_simp [hA2,hB2];ring
  have himC:(((-y)/(A^2+y^2):ℝ):ℂ)-(((-y)/(B^2+y^2):ℝ):ℂ) =
    ((y*(A^2-B^2)/((A^2+y^2)*(B^2+y^2)):ℝ):ℂ):=by
   rw [← Complex.ofReal_sub,him]
  linear_combination himC*I
 have hint_re_C:∀ C:ℝ,C≠0→ Integrable (fun y:ℝ=>C/(C^2+y^2)):=by
  intro C hC
  rcases lt_or_gt_of_ne hC with hneg | hpos
  ·
   have h:=(z107 (neg_pos.mpr hneg)).neg
   refine h.congr (Filter.Eventually.of_forall fun y=>?_)
   simp [neg_div]
  ·
   exact z107 hpos
 have hint_re_val:∀ C:ℝ,C≠0→ ∫ y:ℝ,C/(C^2+y^2)=if 0< C then π else -π:=by
  intro C hC
  rcases lt_or_gt_of_ne hC with hneg | hpos
  ·
   rw [if_neg (not_lt.mpr hneg.le)]
   have h:(fun y:ℝ=>C/(C^2+y^2))=fun y=>-((-C)/((-C)^2+y^2)):=by
    funext y;simp [neg_div]
   rw [h,integral_neg,z113 (neg_pos.mpr hneg)]
  ·
   rw [if_pos hpos]
   exact z113 hpos
 have hint_im:Integrable (fun y:ℝ=>y*(A^2-B^2)/((A^2+y^2)*(B^2+y^2))):=by
  have hcont:Continuous (fun y:ℝ=>y*(A^2-B^2)/((A^2+y^2)*(B^2+y^2))):=by
   refine Continuous.div (continuous_id.mul continuous_const)
    ((continuous_const.add (continuous_pow 2)).mul (continuous_const.add (continuous_pow 2)))
    (fun y=>by positivity)
  have hdom:Integrable (fun y:ℝ=>(|A^2-B^2| / (2 * |A|))*(1/(B^2+y^2))):=by
   have hb:Integrable (fun y:ℝ=>1/(B^2+y^2)):=by
    have:=(z107 (abs_pos.mpr hB)).div_const |B|
    refine this.congr (Filter.Eventually.of_forall fun y=>?_)
    rw [sq_abs];field_simp [abs_ne_zero.mpr hB]
   exact hb.const_mul _
  refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y=>?_)
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos (by positivity:0< (A^2+y^2)*(B^2+y^2))]
  have ham:2 * |A| * |y| ≤ A^2+y^2:=by
   have:0 ≤ (|A| - |y|)^2:=sq_nonneg _
   nlinarith [sq_abs A,sq_abs y]
  have h1:|y| / (A^2+y^2) ≤ 1/(2 * |A|):=by
   rw [div_le_div_iff₀ (by positivity) (by positivity)]
   linarith
  have hA2p:(A^2+y^2:ℝ)≠0:=by positivity
  have hB2p:(B^2+y^2:ℝ)≠0:=by positivity
  calc
   |y| * |A^2-B^2| / ((A^2+y^2)*(B^2+y^2))
    = (|y| / (A^2+y^2)) * |A^2-B^2| * (1/(B^2+y^2)):=by
     field_simp [hA2p,hB2p]
   _ ≤ (1/(2 * |A|)) * |A^2-B^2| * (1/(B^2+y^2)):=by
     gcongr
   _=|A^2-B^2| / (2 * |A|)*(1/(B^2+y^2)):=by ring
 have hint_im_zero:∫ y:ℝ,y*(A^2-B^2)/((A^2+y^2)*(B^2+y^2))=0:=by
  have hneg:=Measure.integral_comp_mul_left
   (fun y:ℝ=>y*(A^2-B^2)/((A^2+y^2)*(B^2+y^2))) (-1)
  have hodd:(fun y:ℝ=>(-1*y)*(A^2-B^2)/((A^2+(-1*y)^2)*(B^2+(-1*y)^2))) =
    fun y=>-(y*(A^2-B^2)/((A^2+y^2)*(B^2+y^2))):=by
   funext y;simp [neg_div]
  rw [hodd,integral_neg,smul_eq_mul] at hneg
  norm_num at hneg
  linarith
 rw [hsplit]
 have hA':Integrable (fun y:ℝ=>((A/(A^2+y^2):ℝ):ℂ)):=
  Complex.ofRealCLM.integrable_comp (hint_re_C A hA)
 have hB':Integrable (fun y:ℝ=>((B/(B^2+y^2):ℝ):ℂ)):=
  Complex.ofRealCLM.integrable_comp (hint_re_C B hB)
 have h1:Integrable (fun y:ℝ =>
   (((A/(A^2+y^2):ℝ):ℂ)-((B/(B^2+y^2):ℝ):ℂ))):=hA'.sub hB'
 have h2:Integrable (fun y:ℝ =>
   ((y*(A^2-B^2)/((A^2+y^2)*(B^2+y^2)):ℝ):ℂ)*I):=
  (Complex.ofRealCLM.integrable_comp hint_im).mul_const I
 rw [integral_add h1 h2,integral_mul_const]
 have h_im_c:(∫ y:ℝ,((y*(A^2-B^2)/((A^2+y^2)*(B^2+y^2)):ℝ):ℂ))=0:=by
  have:=Complex.ofRealCLM.integral_comp_comm hint_im
  simpa [hint_im_zero] using this
 have h_re_A:(∫ y:ℝ,((A/(A^2+y^2):ℝ):ℂ))=((if 0< A then π else -π : ℝ):ℂ):=by
  have:=Complex.ofRealCLM.integral_comp_comm (hint_re_C A hA)
  simpa [hint_re_val A hA] using this
 have h_re_B:(∫ y:ℝ,((B/(B^2+y^2):ℝ):ℂ))=((if 0< B then π else -π : ℝ):ℂ):=by
  have:=Complex.ofRealCLM.integral_comp_comm (hint_re_C B hB)
  simpa [hint_re_val B hB] using this
 rw [h_im_c,zero_mul,add_zero,integral_sub hA' hB',h_re_A,h_re_B]
 push_cast
 ring
private lemma z163 (i:ℕ) (hi:1 ≤ i) {a t:ℂ} (hat:a+t≠0) :
  ∃ c:ℕ→ ℂ,
   c 1=-((i*(i+1):ℕ):ℂ)/(2*(a+t)^(i+2)) ∧
   ∀ u:ℂ,u+a≠0→ u-t≠0 →
    1/((u+a)^i*(u-t)^3) =
     1/((a+t)^i*(u-t)^3) -
     (i:ℂ)/((a+t)^(i+1)*(u-t)^2) +
     ((i*(i+1):ℕ):ℂ)/(2*(a+t)^(i+2)*(u-t)) +
     ∑ m∈Finset.Icc 1 i,c m/(u+a)^m:=by
 induction i with
 | zero=>omega
 | succ k ih =>
  cases k with
  | zero =>
   refine ⟨fun m=>if m=1 then -(1:ℂ)/(a+t)^3 else 0,by
    simp only [↓reduceIte,zero_add,mul_two,Nat.cast_add,Nat.cast_one]
    field_simp [hat];ring,fun u hua hut=>?_⟩
   simp only [Finset.Icc_self,Finset.sum_singleton,↓reduceIte,pow_one]
   field_simp [hat,hua,hut]
   ring
  | succ j =>
   obtain ⟨c,hc1,hpf⟩:=ih (by omega)
   set c':ℕ→ ℂ:=fun m =>
    if m=1 then -(((j+2)*(j+3):ℕ):ℂ)/(2*(a+t)^(j+4))
    else c (m-1)
   refine ⟨c',by simp only [c',↓reduceIte],fun u hua hut=>?_⟩
   have hprev:=hpf u hua hut
   have hmul:1/((u+a)^(j+2)*(u-t)^3) =
     (1/((u+a)^(j+1)*(u-t)^3))*(1/(u+a)):=by
    rw [pow_succ];field_simp [hua,hut]
   rw [hmul,hprev]
   have hsum_split:∑ m∈Finset.Icc 1 (j+2),c' m/(u+a)^m =
     c' 1/(u+a)+∑ m∈Finset.Icc 1 (j+1),c m/(u+a)^(m+1):=by
    have h1:Finset.Icc 1 (j+2)=insert 1 (Finset.Icc 2 (j+2)):=by
     ext m;simp only [Finset.mem_Icc,Finset.mem_insert];omega
    rw [h1,Finset.sum_insert (by simp),pow_one]
    congr 1
    refine Finset.sum_bij (fun m _=>m-1) ?_ ?_ ?_ ?_
    ·
     intro m hm;simp only [Finset.mem_Icc] at hm ⊢;omega
    ·
     intro m1 hm1 m2 hm2 heq;simp only [Finset.mem_Icc] at hm1 hm2;omega
    ·
     intro m hm;refine ⟨m+1,?_,by omega⟩;simp only [Finset.mem_Icc] at hm ⊢;omega
    ·
     intro m hm
     simp only [Finset.mem_Icc] at hm
     have hm1:m≠1:=by omega
     have hm2:m-1+1=m:=by omega
     simp [c',hm1,hm2]
   rw [hsum_split]
   have hsum_mul:(∑ m∈Finset.Icc 1 (j+1),c m/(u+a)^m)*(1/(u+a)) =
     ∑ m∈Finset.Icc 1 (j+1),c m/(u+a)^(m+1):=by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _=>?_
    rw [pow_succ];field_simp [hua]
   simp only [add_mul,sub_mul,hsum_mul]
   simp only [c',↓reduceIte]
   have hstep:1/((a+t)^(j+1)*(u-t)^3)*(1/(u+a)) -
     ((j+1:ℕ):ℂ)/((a+t)^(j+2)*(u-t)^2)*(1/(u+a)) +
     (((j+1)*(j+2):ℕ):ℂ)/(2*(a+t)^(j+3)*(u-t))*(1/(u+a)) =
     1/((a+t)^(j+2)*(u-t)^3) -
     ((j+2:ℕ):ℂ)/((a+t)^(j+3)*(u-t)^2) +
     (((j+2)*(j+3):ℕ):ℂ)/(2*(a+t)^(j+4)*(u-t)) +
     -(((j+2)*(j+3):ℕ):ℂ)/(2*(a+t)^(j+4))/(u+a):=by
    push_cast
    field_simp [hat,hua,hut]
    ring
   have hnat3:j+1+2=j+3:=by omega
   have hnat4:j+1+1+2=j+4:=by omega
   have hnat5:j+1+1=j+2:=by omega
   rw [hnat3,hnat4,hnat5]
   push_cast at hstep ⊢
   linear_combination hstep
private lemma z116 (i:ℕ) (hi:1 ≤ i) {a:ℝ} (ha:0< a) (t:ℤ) :
  ∫ y:ℝ,(1:ℂ)/((((1/2+a:ℝ):ℂ)+(y:ℂ)*I)^i *
   ((((1/2-(t:ℝ):ℝ):ℂ)+(y:ℂ)*I)^3)) =
  if 1 ≤ t then -((π : ℂ)*((i*(i+1):ℕ):ℂ)/(((t:ℂ)+a)^(i+2))) else 0:=by
 set A:ℝ:=1/2+a
 set B:ℝ:=1/2-(t:ℝ)
 have hA_pos:0< A:=by simp only [A];linarith
 have hA_ne:A≠0:=hA_pos.ne'
 have hB_ne:B≠0:=by
  intro h
  have h1:(2:ℝ)*(t:ℝ)=1:=by simp only [B] at h;linarith
  have h2t:(2*t:ℤ)=1:=by exact_mod_cast h1
  omega
 by_cases hat:(a:ℝ)+(t:ℝ)=0
 ·
  have ht_neg:¬ (1 ≤ t):=by
   intro h1
   have:(1:ℝ) ≤ (t:ℝ):=by exact_mod_cast h1
   linarith
  rw [if_neg ht_neg]
  have hAB:B=A:=by simp only [A,B];linarith
  have hfun:(fun y:ℝ=>(1:ℂ)/(((A:ℂ)+(y:ℂ)*I)^i*((B:ℂ)+(y:ℂ)*I)^3)) =
    fun y:ℝ=>((A:ℂ)+(y:ℂ)*I)⁻¹^(i+3):=by
   funext y;rw [hAB,← pow_add,one_div,inv_pow]
  rw [hfun]
  exact z110 hA_ne (by omega)
 ·
  have hatC:((a:ℂ)+(t:ℂ))≠0:=by exact_mod_cast hat
  obtain ⟨c,hc1,hpf⟩:=z163 i hi hatC
  set K:ℂ:=((i*(i+1):ℕ):ℂ)/(2*((a:ℂ)+(t:ℂ))^(i+2))
  have hsplit:(fun y:ℝ=>(1:ℂ)/(((A:ℂ)+(y:ℂ)*I)^i*((B:ℂ)+(y:ℂ)*I)^3)) =
    fun y:ℝ =>
     ((1/((a:ℂ)+(t:ℂ))^i)*((B:ℂ)+(y:ℂ)*I)⁻¹^3) -
     (((i:ℂ)/((a:ℂ)+(t:ℂ))^(i+1))*((B:ℂ)+(y:ℂ)*I)⁻¹^2) +
     (K*(((B:ℂ)+(y:ℂ)*I)⁻¹ - ((A:ℂ)+(y:ℂ)*I)⁻¹)) +
     ∑ m∈Finset.Icc 2 i,c m*((A:ℂ)+(y:ℂ)*I)⁻¹^m:=by
   funext y
   set u:ℂ:=(1/2:ℂ)+(y:ℂ)*I
   have huA:u+(a:ℂ)=(A:ℂ)+(y:ℂ)*I:=by simp only [u,A];push_cast;ring
   have huB:u-(t:ℂ)=(B:ℂ)+(y:ℂ)*I:=by simp only [u,B];push_cast;ring
   have hneA:u+(a:ℂ)≠0:=by rw [huA];exact z28 hA_ne y
   have hneB:u-(t:ℂ)≠0:=by rw [huB];exact z28 hB_ne y
   have hp:=hpf u hneA hneB
   rw [huA,huB] at hp
   rw [hp]
   have hIcc:Finset.Icc 1 i=insert 1 (Finset.Icc 2 i):=by
    ext m;simp only [Finset.mem_Icc,Finset.mem_insert];omega
   rw [hIcc,Finset.sum_insert (by simp),pow_one,hc1]
   have hsum_eq:∑ m∈Finset.Icc 2 i,c m/((A:ℂ)+(y:ℂ)*I)^m =
     ∑ m∈Finset.Icc 2 i,c m*((A:ℂ)+(y:ℂ)*I)⁻¹^m:=by
    refine Finset.sum_congr rfl fun m _=>?_
    rw [div_eq_mul_inv,inv_pow]
   rw [hsum_eq]
   simp only [K,div_eq_mul_inv,mul_inv,inv_pow]
   ring
  have hint1:Integrable (fun y:ℝ=>(1/((a:ℂ)+(t:ℂ))^i)*((B:ℂ)+(y:ℂ)*I)⁻¹^3):=
   (z105 hB_ne (by omega)).const_mul _
  have hint2:Integrable (fun y:ℝ=>((i:ℂ)/((a:ℂ)+(t:ℂ))^(i+1))*((B:ℂ)+(y:ℂ)*I)⁻¹^2):=
   (z105 hB_ne (by omega)).const_mul _
  have hint3:Integrable (fun y:ℝ=>K*(((B:ℂ)+(y:ℂ)*I)⁻¹ - ((A:ℂ)+(y:ℂ)*I)⁻¹)):=by
   have hdiff:Integrable (fun y:ℝ=>((B:ℂ)+(y:ℂ)*I)⁻¹ - ((A:ℂ)+(y:ℂ)*I)⁻¹):=by
    have hcont:Continuous (fun y:ℝ=>((B:ℂ)+(y:ℂ)*I)⁻¹ - ((A:ℂ)+(y:ℂ)*I)⁻¹):=
     (Continuous.inv₀ (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
      (z28 hB_ne)).sub
     (Continuous.inv₀ (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
      (z28 hA_ne))
    set m:ℝ:=min |A| |B|
    have hm_pos:0< m:=lt_min (abs_pos.mpr hA_ne) (abs_pos.mpr hB_ne)
    have hdom2:Integrable (fun y:ℝ=>(|A-B| / m)*(m/(m^2+y^2))):=
     (z107 hm_pos).const_mul _
    refine hdom2.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y=>?_)
    have hneA:=z28 hA_ne y
    have hneB:=z28 hB_ne y
    have hsub:((B:ℂ)+(y:ℂ)*I)⁻¹ - ((A:ℂ)+(y:ℂ)*I)⁻¹ =
      ((A-B:ℝ):ℂ)/(((B:ℂ)+(y:ℂ)*I)*((A:ℂ)+(y:ℂ)*I)):=by
     push_cast;field_simp [hneA,hneB];ring
    rw [hsub,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,z135,z135]
    have hmA:m^2+y^2 ≤ A^2+y^2:=by
     have:m^2 ≤ |A|^2:=pow_le_pow_left₀ hm_pos.le (min_le_left _ _) 2
     rw [sq_abs] at this;linarith
    have hmB:m^2+y^2 ≤ B^2+y^2:=by
     have:m^2 ≤ |B|^2:=pow_le_pow_left₀ hm_pos.le (min_le_right _ _) 2
     rw [sq_abs] at this;linarith
    have hmul_ge:m^2+y^2 ≤ Real.sqrt (B^2+y^2)*Real.sqrt (A^2+y^2):=by
     calc
      m^2+y^2
       = Real.sqrt (m^2+y^2)*Real.sqrt (m^2+y^2):=
        (Real.mul_self_sqrt (by positivity)).symm
      _ ≤ Real.sqrt (B^2+y^2)*Real.sqrt (A^2+y^2):=
        mul_le_mul (Real.sqrt_le_sqrt hmB) (Real.sqrt_le_sqrt hmA)
         (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hrhs:|A-B| / m*(m/(m^2+y^2))=|A-B| / (m^2+y^2):=by
     field_simp [hm_pos.ne']
    rw [hrhs]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hmul_ge
   exact hdiff.const_mul K
  have hint4:∀ m∈Finset.Icc 2 i,Integrable (fun y:ℝ=>c m*((A:ℂ)+(y:ℂ)*I)⁻¹^m):=by
   intro m hm
   exact (z105 hA_ne (Finset.mem_Icc.mp hm).1).const_mul _
  have hint_sum:Integrable (fun y:ℝ=>∑ m∈Finset.Icc 2 i,c m*((A:ℂ)+(y:ℂ)*I)⁻¹^m):=
   integrable_finset_sum _ hint4
  have hint12:Integrable (fun y:ℝ =>
    ((1/((a:ℂ)+(t:ℂ))^i)*((B:ℂ)+(y:ℂ)*I)⁻¹^3) -
    (((i:ℂ)/((a:ℂ)+(t:ℂ))^(i+1))*((B:ℂ)+(y:ℂ)*I)⁻¹^2)):=
   hint1.sub hint2
  have hint123:Integrable (fun y:ℝ =>
    ((1/((a:ℂ)+(t:ℂ))^i)*((B:ℂ)+(y:ℂ)*I)⁻¹^3) -
    (((i:ℂ)/((a:ℂ)+(t:ℂ))^(i+1))*((B:ℂ)+(y:ℂ)*I)⁻¹^2) +
    (K*(((B:ℂ)+(y:ℂ)*I)⁻¹ - ((A:ℂ)+(y:ℂ)*I)⁻¹))):=
   hint12.add hint3
  rw [hsplit]
  rw [integral_add hint123 hint_sum]
  rw [integral_add hint12 hint3,integral_sub hint1 hint2]
  rw [integral_const_mul,integral_const_mul,integral_const_mul]
  rw [z110 hB_ne (by omega),
    z110 hB_ne (by omega)]
  rw [integral_finset_sum _ hint4]
  have hsum0:∑ m∈Finset.Icc 2 i,∫ y:ℝ,c m*((A:ℂ)+(y:ℂ)*I)⁻¹^m=0:=by
   refine Finset.sum_eq_zero fun m hm=>?_
   rw [integral_const_mul,z110 hA_ne (Finset.mem_Icc.mp hm).1,mul_zero]
  rw [hsum0,z111 hB_ne hA_ne]
  simp only [mul_zero,sub_zero,zero_add,add_zero,if_pos hA_pos]
  by_cases ht1:1 ≤ t
  ·
   rw [if_pos ht1]
   have hB_neg:¬ (0< B):=by
    have:(1:ℝ) ≤ (t:ℝ):=by exact_mod_cast ht1
    simp only [B];linarith
   rw [if_neg hB_neg]
   simp only [K]
   have hcomm:(t:ℂ)+(a:ℂ)=(a:ℂ)+(t:ℂ):=add_comm _ _
   rw [hcomm]
   push_cast
   field_simp [hatC]
   ring
  ·
   rw [if_neg ht1]
   have hB_pos:0< B:=by
    have:t ≤ 0:=by omega
    have:(t:ℝ) ≤ 0:=by exact_mod_cast this
    simp only [B];linarith
   rw [if_pos hB_pos]
   simp
lemma z112 (i:ℕ) (hi:1 ≤ i) {a:ℝ} (ha:0< a) :
  ∫ y:ℝ,(((1/2+a:ℝ):ℂ)+(y:ℂ)*I)⁻¹^i *
   (2*(π : ℂ)^3*Complex.cos ((π : ℂ)*((1/2:ℂ)+(y:ℂ)*I)) /
    Complex.sin ((π : ℂ)*((1/2:ℂ)+(y:ℂ)*I))^3) =
  -2*(π : ℂ)*∑' t:ℕ,((i*(i+1):ℕ):ℂ)/((((t+1:ℕ):ℂ)+(a:ℂ))^(i+2)):=by
 set F:ℤ→ ℝ→ ℂ:=fun t y =>
  2*((1:ℂ)/((((1/2+a:ℝ):ℂ)+(y:ℂ)*I)^i *
   ((((1/2-(t:ℝ):ℝ):ℂ)+(y:ℂ)*I)^3)))
 have hae:(fun y:ℝ=>(((1/2+a:ℝ):ℂ)+(y:ℂ)*I)⁻¹^i *
   (2*(π : ℂ)^3*Complex.cos ((π : ℂ)*((1/2:ℂ)+(y:ℂ)*I)) /
    Complex.sin ((π : ℂ)*((1/2:ℂ)+(y:ℂ)*I))^3)) =ᵐ[volume]
   fun y:ℝ=>∑' t:ℤ,F t y:=by
  have hne0:∀ᵐ y:ℝ ∂volume,y≠0:=by
   rw [ae_iff];simp
  filter_upwards [hne0] with y hy
  have him:((1/2:ℂ)+(y:ℂ)*I).im≠0:=by simp [hy]
  rw [z281 him,← mul_assoc,mul_comm _ (2:ℂ),mul_assoc,
   ← tsum_mul_left,← tsum_mul_left]
  congr 1;ext t
  have hsub:(1/2:ℂ)+(y:ℂ)*I-(t:ℂ)=(((1/2-(t:ℝ):ℝ):ℂ)+(y:ℂ)*I):=by
   push_cast;ring
  simp only [F]
  rw [hsub]
  simp only [one_div,inv_pow,mul_inv]
 rw [integral_congr_ae hae]
 set A:ℝ:=1/2+a
 have hA_pos:0< A:=by simp only [A];linarith
 have hB_ne:∀ t:ℤ,(1/2-(t:ℝ))≠0:=by
  intro t h
  have:(2*t:ℤ)=1:=by exact_mod_cast (show (2:ℝ)*(t:ℝ)=1 by linarith)
  omega
 have hB_abs_pos:∀ t:ℤ,0 < |1/2-(t:ℝ)|:=fun t=>abs_pos.mpr (hB_ne t)
 have hF_norm_le:∀ (t:ℤ) (y:ℝ),
   ‖F t y‖ ≤ (2/(A^i * |1/2-(t:ℝ)|))*(1/((1/2-(t:ℝ))^2+y^2)):=by
  intro t y
  simp only [F,norm_mul,norm_div,norm_one,norm_pow,norm_ofNat,z135]
  have hA_le:A ≤ Real.sqrt (A^2+y^2):=by
   calc
    A=Real.sqrt (A^2):=(Real.sqrt_sq hA_pos.le).symm
    _ ≤ Real.sqrt (A^2+y^2):=Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
  have hAi:A^i ≤ Real.sqrt (A^2+y^2)^i:=pow_le_pow_left₀ hA_pos.le hA_le i
  have hB_le:|1/2-(t:ℝ)| ≤ Real.sqrt ((1/2-(t:ℝ))^2+y^2):=by
   calc
    |1/2-(t:ℝ)|=Real.sqrt ((1/2-(t:ℝ))^2):=(Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((1/2-(t:ℝ))^2+y^2):=Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
  have hB3:|1/2-(t:ℝ)| * ((1/2-(t:ℝ))^2+y^2) ≤
    Real.sqrt ((1/2-(t:ℝ))^2+y^2)^3:=by
   have hsq:Real.sqrt ((1/2-(t:ℝ))^2+y^2)^2=(1/2-(t:ℝ))^2+y^2:=
    Real.sq_sqrt (by positivity)
   calc
    |1/2-(t:ℝ)| * ((1/2-(t:ℝ))^2+y^2)
     ≤ Real.sqrt ((1/2-(t:ℝ))^2+y^2)*((1/2-(t:ℝ))^2+y^2):=
      mul_le_mul_of_nonneg_right hB_le (by positivity)
    _=Real.sqrt ((1/2-(t:ℝ))^2+y^2)*Real.sqrt ((1/2-(t:ℝ))^2+y^2)^2:=by
      rw [hsq]
    _=Real.sqrt ((1/2-(t:ℝ))^2+y^2)^3:=by ring
  have hprod:A^i * |1/2-(t:ℝ)| * ((1/2-(t:ℝ))^2+y^2) ≤
    Real.sqrt (A^2+y^2)^i*Real.sqrt ((1/2-(t:ℝ))^2+y^2)^3:=by
   rw [mul_assoc]
   exact mul_le_mul hAi hB3 (by positivity) (by positivity)
  have hden_pos:0< A^i * |1/2-(t:ℝ)| * ((1/2-(t:ℝ))^2+y^2):=by
   have h1:0< (1/2-(t:ℝ))^2+y^2:=by
    have:=sq_pos_of_ne_zero (hB_ne t);linarith [sq_nonneg y]
   have h2:=hB_abs_pos t
   positivity
  have hrhs:2/(A^i * |1/2-(t:ℝ)|)*(1/((1/2-(t:ℝ))^2+y^2)) =
    2*(1/(A^i * |1/2-(t:ℝ)| * ((1/2-(t:ℝ))^2+y^2))):=by
   rw [div_mul_div_comm,mul_one,mul_one_div]
  rw [hrhs]
  exact mul_le_mul_of_nonneg_left
   (one_div_le_one_div_of_le hden_pos hprod) (by norm_num)
 have hinv_int:∀ t:ℤ,Integrable (fun y:ℝ=>1/((1/2-(t:ℝ))^2+y^2)):=by
  intro t
  have hb:=hB_abs_pos t
  have h1:=(z107 hb).div_const |1/2-(t:ℝ)|
  refine h1.congr (Filter.Eventually.of_forall fun y=>?_)
  dsimp only
  rw [sq_abs,div_div,mul_comm,← div_div,div_self hb.ne']
 have hF_int:∀ t:ℤ,Integrable (F t):=by
  intro t
  have hcont:Continuous (F t):=by
   refine continuous_const.mul (continuous_const.div ?_ fun y =>
    mul_ne_zero (pow_ne_zero i (z28 hA_pos.ne' y))
     (pow_ne_zero 3 (z28 (hB_ne t) y)))
   exact ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).pow i).mul
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).pow 3)
  exact ((hinv_int t).const_mul _).mono' hcont.aestronglyMeasurable
   (Filter.Eventually.of_forall (hF_norm_le t))
 have hF_sum:Summable (fun t:ℤ=>∫ y:ℝ,‖F t y‖):=by
  have hbound:∀ t:ℤ,∫ y:ℝ,‖F t y‖ ≤ (2*π / A^i)*(1/(1/2-(t:ℝ))^2):=by
   intro t
   have hb:=hB_abs_pos t
   have hle:=integral_mono (hF_int t).norm ((hinv_int t).const_mul _) (hF_norm_le t)
   have hint_val:∫ y:ℝ,(1/((1/2-(t:ℝ))^2+y^2))=π / |1/2-(t:ℝ)|:=by
    have h1:=z113 hb
    have h2:(fun y:ℝ=>1/((1/2-(t:ℝ))^2+y^2)) =
      fun y=>(|1/2-(t:ℝ)| / (|1/2-(t:ℝ)|^2+y^2)) / |1/2-(t:ℝ)|:=by
     funext y
     rw [sq_abs,div_div,mul_comm,← div_div,div_self hb.ne']
    rw [h2,integral_div,h1]
   rw [integral_const_mul,hint_val] at hle
   refine hle.trans_eq ?_
   have hsq:|1/2-(t:ℝ)|^2=(1/2-(t:ℝ))^2:=sq_abs _
   rw [← hsq]
   field_simp [hA_pos.ne',hb.ne']
  have hsum_inv:Summable (fun t:ℤ=>(1:ℝ)/(1/2-(t:ℝ))^2):=by
   have hnat:Summable (fun n:ℕ=>(16:ℝ)/((n:ℝ)+1)^2):=by
    have h:=Real.summable_one_div_nat_pow.mpr (show 1< 2 by omega)
    have hshift:=(summable_nat_add_iff 1).mpr h
    simpa [Nat.cast_add,Nat.cast_one,div_eq_mul_inv] using hshift.mul_left (16:ℝ)
   rw [summable_int_iff_summable_nat_and_neg]
   constructor
   ·
    refine Summable.of_nonneg_of_le (fun n=>by positivity) (fun n=>?_) hnat
    have hge:((n:ℝ)+1)/4 ≤ |1/2-(n:ℝ)|:=by
     rcases n with _ | m
     ·
      norm_num
     ·
      push_cast;rw [abs_of_neg (by linarith)];linarith
    have hsq:((n:ℝ)+1)^2/16 ≤ (1/2-(n:ℝ))^2:=by
     have:=pow_le_pow_left₀ (by positivity) hge 2
     rw [sq_abs] at this;linarith
    have hdiv:(1:ℝ)/(1/2-(n:ℝ))^2 ≤ 1/(((n:ℝ)+1)^2/16):=
     one_div_le_one_div_of_le (by positivity) hsq
    rw [one_div_div] at hdiv
    simpa using hdiv
   ·
    refine Summable.of_nonneg_of_le (fun n=>by positivity) (fun n=>?_) hnat
    have hge:((n:ℝ)+1)/4 ≤ 1/2-((-(n:ℤ):ℤ):ℝ):=by push_cast;linarith
    have hsq:((n:ℝ)+1)^2/16 ≤ (1/2-((-(n:ℤ):ℤ):ℝ))^2:=by
     have:=pow_le_pow_left₀ (by positivity) hge 2;linarith
    have hdiv:(1:ℝ)/(1/2-((-(n:ℤ):ℤ):ℝ))^2 ≤ 1/(((n:ℝ)+1)^2/16):=
     one_div_le_one_div_of_le (by positivity) hsq
    rw [one_div_div] at hdiv
    exact hdiv
  exact Summable.of_nonneg_of_le (fun t=>integral_nonneg fun y=>norm_nonneg _)
   hbound (hsum_inv.mul_left _)
 rw [← integral_tsum_of_summable_integral_norm hF_int hF_sum]
 have hterm:∀ t:ℤ,∫ y:ℝ,F t y =
   if 1 ≤ t then -2*(π : ℂ)*(((i*(i+1):ℕ):ℂ)/(((t:ℂ)+a)^(i+2))) else 0:=by
  intro t
  simp only [F]
  rw [integral_const_mul,z116 i hi ha t]
  split_ifs <;> ring
 simp_rw [hterm]
 rw [← tsum_mul_left]
 set g:ℤ→ ℂ:=fun t=>-2*(π : ℂ)*(((i*(i+1):ℕ):ℂ)/(((t:ℂ)+a)^(i+2)))
 have heq_tsum:(∑' t:ℤ,if 1 ≤ t then g t else 0)=∑' k:ℕ,g ((k+1:ℕ):ℤ):=by
  have hinj:Function.Injective (fun k:ℕ=>((k+1:ℕ):ℤ)):=by
   intro k1 k2 h
   dsimp only at h
   exact Nat.succ.inj (Int.ofNat.inj h)
  have hsupp:Function.support (fun t:ℤ=>if 1 ≤ t then g t else 0) ⊆
    Set.range (fun k:ℕ=>((k+1:ℕ):ℤ)):=by
   intro t ht
   rw [Function.mem_support] at ht
   have ht1:1 ≤ t:=by by_contra h;rw [if_neg h] at ht;exact ht rfl
   refine ⟨(t-1).toNat,?_⟩
   dsimp only
   omega
  rw [← tsum_subtype_eq_of_support_subset hsupp,tsum_range (fun t:ℤ=>if 1 ≤ t then g t else 0) hinj]
  congr 1;ext k
  rw [if_pos (by omega)]
 rw [heq_tsum]
 congr 1
private lemma z52 (z:ℂ) (M:ℕ) :
  Complex.cos (z+(M:ℂ)*(π : ℂ))=(-1:ℂ)^M*Complex.cos z:=by
 induction M with
 | zero=>simp
 | succ k ih =>
  rw [Nat.cast_succ,add_mul,one_mul,← add_assoc,Complex.cos_add_pi,ih,pow_succ]
  ring
private lemma z255 (z:ℂ) (M:ℕ) :
  Complex.sin (z+(M:ℂ)*(π : ℂ))=(-1:ℂ)^M*Complex.sin z:=by
 induction M with
 | zero=>simp
 | succ k ih =>
  rw [Nat.cast_succ,add_mul,one_mul,← add_assoc,Complex.sin_add_pi,ih,pow_succ]
  ring
theorem z115 (i:ℕ) (hi:1 ≤ i) (M m:ℕ) (hm:0< m) :
  Integrable (fun y:ℝ =>
   ((((M:ℂ)+1/2+(y:ℂ)*I)+(m:ℂ))⁻¹^i) *
    (2*(π : ℂ)^3*Complex.cos ((π : ℂ)*((M:ℂ)+1/2+(y:ℂ)*I)) /
     Complex.sin ((π : ℂ)*((M:ℂ)+1/2+(y:ℂ)*I))^3)) ∧
  ∫ y:ℝ,((((M:ℂ)+1/2+(y:ℂ)*I)+(m:ℂ))⁻¹^i) *
   (2*(π : ℂ)^3*Complex.cos ((π : ℂ)*((M:ℂ)+1/2+(y:ℂ)*I)) /
    Complex.sin ((π : ℂ)*((M:ℂ)+1/2+(y:ℂ)*I))^3) =
  -2*(π : ℂ)*∑' t:ℕ,((i*(i+1):ℕ):ℂ)/((((M+t+1:ℕ):ℂ)+(m:ℂ))^(i+2)):=by
 have ha:(0:ℝ)< (M+m:ℕ):=Nat.cast_pos.mpr (by omega)
 have h0:=z112 i hi ha
 have hsin_half:∀ y:ℝ,
   Complex.sin ((π : ℂ)*((1/2:ℂ)+(y:ℂ)*I))=(Real.cosh (π*y):ℂ):=by
  intro y
  rw [show (π : ℂ)*((1/2:ℂ)+(y:ℂ)*I)=(π : ℂ)/2+((π*y:ℝ):ℂ)*I by
   push_cast;ring]
  rw [Complex.sin_add,Complex.sin_pi_div_two,Complex.cos_pi_div_two,one_mul,zero_mul,add_zero,
   Complex.cos_mul_I,Complex.ofReal_cosh]
 have hcos_half:∀ y:ℝ,
   Complex.cos ((π : ℂ)*((1/2:ℂ)+(y:ℂ)*I))=-((Real.sinh (π*y):ℂ)*I):=by
  intro y
  rw [show (π : ℂ)*((1/2:ℂ)+(y:ℂ)*I)=(π : ℂ)/2+((π*y:ℝ):ℂ)*I by
   push_cast;ring]
  rw [Complex.cos_add,Complex.sin_pi_div_two,Complex.cos_pi_div_two,one_mul,zero_mul,zero_sub,
   Complex.sin_mul_I,Complex.ofReal_sinh]
 have htrig:∀ y:ℝ,
   Complex.cos ((π : ℂ)*((M:ℂ)+1/2+(y:ℂ)*I)) /
    Complex.sin ((π : ℂ)*((M:ℂ)+1/2+(y:ℂ)*I))^3 =
   Complex.cos ((π : ℂ)*((1/2:ℂ)+(y:ℂ)*I)) /
    Complex.sin ((π : ℂ)*((1/2:ℂ)+(y:ℂ)*I))^3:=by
  intro y
  have harg:(π : ℂ)*((M:ℂ)+1/2+(y:ℂ)*I) =
    (π : ℂ)*((1/2:ℂ)+(y:ℂ)*I)+(M:ℂ)*(π : ℂ):=by ring
  rw [harg,z52,z255]
  rw [mul_pow,← pow_mul]
  have hsign:(-1:ℂ)^(M*3)=(-1:ℂ)^M:=by
   have h2:(-1:ℂ)^(2*M)=1:=by rw [pow_mul];norm_num
   calc
    (-1:ℂ)^(M*3)=(-1:ℂ)^(2*M+M):=by congr 1;omega
    _=(-1:ℂ)^(2*M)*(-1:ℂ)^M:=pow_add _ _ _
    _=(-1:ℂ)^M:=by rw [h2,one_mul]
  rw [hsign]
  have hne:(-1:ℂ)^M≠0:=pow_ne_zero M (by norm_num)
  field_simp [hne]
 constructor
 ·
  have hcont:Continuous (fun y:ℝ =>
    ((((M:ℂ)+1/2+(y:ℂ)*I)+(m:ℂ))⁻¹^i) *
     (2*(π : ℂ)^3*Complex.cos ((π : ℂ)*((M:ℂ)+1/2+(y:ℂ)*I)) /
      Complex.sin ((π : ℂ)*((M:ℂ)+1/2+(y:ℂ)*I))^3)):=by
   refine Continuous.mul ?_ ?_
   ·
    refine Continuous.pow (Continuous.inv₀ (by fun_prop) fun y=>?_) i
    intro h0';have hre:=congr_arg Complex.re h0'
    simp only [Complex.add_re,Complex.natCast_re,Complex.div_ofNat_re,Complex.one_re,
     Complex.mul_re,Complex.ofReal_re,Complex.I_re,mul_zero,Complex.ofReal_im,Complex.I_im,
     mul_one,sub_self,add_zero,Complex.zero_re] at hre
    have:(1:ℝ) ≤ m:=by exact_mod_cast hm
    linarith [Nat.cast_nonneg (α:=ℝ) M]
   ·
    refine Continuous.div (by fun_prop) (by fun_prop) fun y=>?_
    have harg:(π : ℂ)*((M:ℂ)+1/2+(y:ℂ)*I) =
      (π : ℂ)*((1/2:ℂ)+(y:ℂ)*I)+(M:ℂ)*(π : ℂ):=by ring
    rw [harg,z255,hsin_half]
    exact pow_ne_zero 3 (mul_ne_zero (pow_ne_zero M (by norm_num))
     (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'))
  refine (integrable_inv_one_add_sq.const_mul (8*π^3)).mono' hcont.aestronglyMeasurable
   (Filter.Eventually.of_forall fun y=>?_)
  rw [mul_div_assoc,htrig y,hcos_half y,hsin_half y]
  simp only [norm_mul,norm_pow,norm_inv,norm_div,norm_neg,Complex.norm_I,mul_one,
   norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
   abs_of_pos (Real.cosh_pos _)]
  have hinv_le:‖((M:ℂ)+1/2+(y:ℂ)*I)+(m:ℂ)‖⁻¹ ≤ 1:=by
   refine inv_le_one_of_one_le₀ ?_
   have hre:(1:ℝ) ≤ (((M:ℂ)+1/2+(y:ℂ)*I)+(m:ℂ)).re:=by
    simp only [Complex.add_re,Complex.natCast_re,Complex.div_ofNat_re,Complex.one_re,
     Complex.mul_re,Complex.ofReal_re,Complex.I_re,mul_zero,Complex.ofReal_im,Complex.I_im,
     mul_one,sub_self,add_zero]
    have:(1:ℝ) ≤ m:=by exact_mod_cast hm
    linarith [Nat.cast_nonneg (α:=ℝ) M]
   exact hre.trans (Complex.re_le_norm _)
  have hpow_le:(‖((M:ℂ)+1/2+(y:ℂ)*I)+(m:ℂ)‖⁻¹)^i ≤ 1:=
   pow_le_one₀ (inv_nonneg.mpr (norm_nonneg _)) hinv_le
  have hsinh_le:|Real.sinh (π*y)| ≤ Real.cosh (π*y):=by
   rw [Real.sinh_eq,Real.cosh_eq,abs_div]
   rw [show |(2:ℝ)|=2 by norm_num]
   refine div_le_div_of_nonneg_right ?_ two_pos.le
   rw [abs_le];constructor <;> linarith [Real.exp_pos (π*y),Real.exp_pos (-(π*y))]
  have hcosh_ge:(1+|y|)/2 ≤ Real.cosh (π*y):=by
   rw [← Real.cosh_abs,Real.cosh_eq]
   have h1:1+|π*y| ≤ Real.exp |π*y|:=by linarith [Real.add_one_le_exp |π*y|]
   have h2:|y| ≤ |π*y|:=by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    nlinarith [Real.two_le_pi,abs_nonneg y]
   linarith [Real.exp_pos (-|π*y|)]
  have hcosh_sq:1+y^2 ≤ 4*Real.cosh (π*y)^2:=by
   have hsq:((1+|y|)/2)^2 ≤ Real.cosh (π*y)^2:=
    pow_le_pow_left₀ (by positivity) hcosh_ge 2
   have habs2:|y|^2=y^2:=sq_abs y
   nlinarith [abs_nonneg y,hsq,habs2]
  have htrig_le:|Real.sinh (π*y)| / Real.cosh (π*y)^3 ≤ 4*(1+y^2)⁻¹:=by
   have hcpos:=Real.cosh_pos (π*y)
   calc
    |Real.sinh (π*y)| / Real.cosh (π*y)^3
     ≤ Real.cosh (π*y)/Real.cosh (π*y)^3:=
      div_le_div_of_nonneg_right hsinh_le (by positivity)
    _=1/Real.cosh (π*y)^2:=by field_simp [hcpos.ne']
    _ ≤ 1/((1+y^2)/4):=one_div_le_one_div_of_le (by positivity) (by linarith)
    _=4*(1+y^2)⁻¹:=by field_simp
  calc
   ‖((M:ℂ)+1/2+(y:ℂ)*I)+(m:ℂ)‖⁻¹^i *
      (2*π^3*(|Real.sinh (π*y)| / Real.cosh (π*y)^3))
    ≤ 1*(2*π^3*(4*(1+y^2)⁻¹)):=
     mul_le_mul hpow_le (mul_le_mul_of_nonneg_left htrig_le (by positivity))
      (by positivity) zero_le_one
   _=8*π^3*(1+y^2)⁻¹:=by ring
 ·
  convert h0 using 2
  ·
   ext y
   rw [mul_div_assoc,htrig y,← mul_div_assoc]
   congr 2
   push_cast;ring
  ·
   congr 1;ext t
   congr 2
   push_cast;ring
end Z3
namespace Z4
open scoped BigOperators
open Finset Polynomial Complex MeasureTheory
abbrev PS:=ℕ→ ℚ
def psOne:PS:=fun d=>if d=0 then 1 else 0
def z238 (c:ℚ) (f:PS):PS:=fun d=>c*f d
def psMul (f g:PS):PS:=fun d =>
 ∑ r∈Finset.range (d+1),f r*g (d-r)
def psPow (f:PS):ℕ→ PS
 | 0=>psOne
 | k+1=>psMul f (psPow f k)
private lemma z212 (f g:PS):psMul f g=psMul g f:=by
 funext d
 unfold psMul
 refine Finset.sum_bij (fun r _=>d-r) ?_ ?_ ?_ ?_
 ·
  intro r hr;simp only [Finset.mem_range] at hr ⊢;omega
 ·
  intro r1 hr1 r2 hr2 h;simp only [Finset.mem_range] at hr1 hr2;omega
 ·
  intro r hr;simp only [Finset.mem_range] at hr
  exact ⟨d-r,Finset.mem_range.mpr (by omega),by omega⟩
 ·
  intro r hr
  simp only [Finset.mem_range] at hr
  have hsub:d-(d-r)=r:=by omega
  rw [mul_comm,hsub]
private lemma z211 (f g h:PS):psMul (psMul f g) h=psMul f (psMul g h):=by
 funext d
 unfold psMul
 simp_rw [Finset.sum_mul,Finset.mul_sum]
 have hL:(∑ x∈Finset.range (d+1),∑ i∈Finset.range (x+1),f i*g (x-i)*h (d-x)) =
   ∑ p∈(Finset.range (d+1)).sigma (fun x=>Finset.range (x+1)),
    f p.2*g (p.1-p.2)*h (d-p.1):=
  (Finset.sum_sigma (Finset.range (d+1)) (fun x=>Finset.range (x+1))
   (fun p=>f p.2*g (p.1-p.2)*h (d-p.1))).symm
 have hR:(∑ x∈Finset.range (d+1),∑ i∈Finset.range (d-x+1),f x*(g i*h (d-x-i))) =
   ∑ p∈(Finset.range (d+1)).sigma (fun x=>Finset.range (d-x+1)),
    f p.1*(g p.2*h (d-p.1-p.2)):=
  (Finset.sum_sigma (Finset.range (d+1)) (fun x=>Finset.range (d-x+1))
   (fun p=>f p.1*(g p.2*h (d-p.1-p.2)))).symm
 rw [hL,hR]
 refine Finset.sum_bij (fun p _=>(⟨p.2,p.1-p.2⟩ : Σ _:ℕ,ℕ)) ?_ ?_ ?_ ?_
 ·
  intro ⟨r,a⟩ hp
  simp only [Finset.mem_sigma,Finset.mem_range] at hp ⊢
  omega
 ·
  intro ⟨r1,a1⟩ hp1 ⟨r2,a2⟩ hp2 heq
  simp only [Finset.mem_sigma,Finset.mem_range] at hp1 hp2
  simp only [Sigma.mk.inj_iff,heq_eq_eq] at heq
  have ha:a1=a2:=heq.1
  have hr:r1=r2:=by omega
  subst ha;subst hr;rfl
 ·
  intro ⟨a,b⟩ hp
  simp only [Finset.mem_sigma,Finset.mem_range] at hp
  refine ⟨⟨a+b,a⟩,?_,?_⟩
  ·
   simp only [Finset.mem_sigma,Finset.mem_range];omega
  ·
   simp
 ·
  intro ⟨r,a⟩ hp
  simp only [Finset.mem_sigma,Finset.mem_range] at hp
  rw [mul_assoc,show d-a-(r-a)=d-r by omega]
instance:Std.Commutative psMul:=⟨z212⟩
instance:Std.Associative psMul:=⟨z211⟩
def z230 {ι : Type*} (s:Finset ι) (f:ι→ PS):PS:=
 s.fold psMul psOne f
private lemma z213 (f:PS):psMul f psOne=f:=by
 funext d
 unfold psMul psOne
 rw [Finset.sum_eq_single d]
 ·
  simp
 ·
  intro r hr hne
  have:d-r≠0:=by simp only [Finset.mem_range] at hr;omega
  simp [this]
 ·
  intro h;exfalso;exact h (Finset.mem_range.mpr (by omega))
private lemma z220 (f:PS):psMul psOne f=f:=by
 rw [z212,z213]
private lemma z240 (c:ℚ) (f g:PS) :
  psMul (z238 c f) g=z238 c (psMul f g):=by
 funext d;unfold psMul z238
 rw [Finset.mul_sum]
 refine Finset.sum_congr rfl fun r _=>by ring
private lemma z241 (c:ℚ) (f g:PS) :
  psMul f (z238 c g)=z238 c (psMul f g):=by
 rw [z212,z240,z212]
private lemma z239 (c1 c2:ℚ) (f:PS) :
  z238 c1 (z238 c2 f)=z238 (c1*c2) f:=by
 funext d;unfold z238;ring
private lemma z242 (f:PS):z238 1 f=f:=by
 funext d;simp [z238]
private lemma z210 (f g h:PS) :
  psMul f (fun d=>g d+h d)=(fun d=>psMul f g d+psMul f h d):=by
 funext d;unfold psMul
 rw [← Finset.sum_add_distrib]
 refine Finset.sum_congr rfl fun r _=>by ring
private lemma z214 {ι : Type*} (s:Finset ι) (f:PS) (g:ι→ PS) :
  psMul f (fun d=>∑ i∈s,g i d)=(fun d=>∑ i∈s,psMul f (g i) d):=by
 classical
 induction s using Finset.induction with
 | empty=>funext d;simp [psMul]
 | insert a s ha ih =>
  funext d
  simp only [Finset.sum_insert ha]
  have h1:=congr_fun (z210 f (g a) (fun d=>∑ i∈s,g i d)) d
  rw [h1,congr_fun ih d]
private lemma z232 {ι : Type*} (f:ι→ PS) :
  z230 (∅ : Finset ι) f=psOne:=by
 simp [z230]
private lemma z233 {ι : Type*} [DecidableEq ι] {a:ι} {s:Finset ι} (ha:a∉s)
  (f:ι→ PS) :
  z230 (insert a s) f=psMul (f a) (z230 s f):=by
 simp [z230,Finset.fold_insert ha]
private lemma z231 {ι : Type*} {s t:Finset ι} (h:s=t) (f g:ι→ PS)
  (hfg:∀ i∈t,f i=g i):z230 s f=z230 t g:=by
 subst h
 classical
 induction s using Finset.induction with
 | empty=>simp [z230]
 | insert a s ha ih =>
  rw [z233 ha,z233 ha,hfg a (Finset.mem_insert_self a s),
   ih (fun i hi=>hfg i (Finset.mem_insert_of_mem hi))]
private lemma z234 {ι : Type*} (s:Finset ι) (f g:ι→ PS) :
  z230 s (fun i=>psMul (f i) (g i))=psMul (z230 s f) (z230 s g):=by
 classical
 induction s using Finset.induction with
 | empty=>simp [z230,z213]
 | insert a s ha ih =>
  rw [z233 ha,z233 ha,z233 ha,ih]
  rw [z211,← z211 (g a),z212 (g a) (z230 s f),
   z211 (z230 s f),← z211]
private lemma z236 {ι : Type*} (s:Finset ι) (c:ι→ ℚ) (f:ι→ PS) :
  z230 s (fun i=>z238 (c i) (f i))=z238 (∏ i∈s,c i) (z230 s f):=by
 classical
 induction s using Finset.induction with
 | empty=>simp [z230,z242]
 | insert a s ha ih =>
  rw [z233 ha,ih,z240,z241,z239,
   Finset.prod_insert ha,z233 ha]
private lemma z237 {ι : Type*} [DecidableEq ι] {s t:Finset ι} (hd:Disjoint s t)
  (f:ι→ PS) :
  z230 (s ∪ t) f=psMul (z230 s f) (z230 t f):=by
 induction s using Finset.induction with
 | empty=>simp [z230,z220]
 | insert a s ha ih =>
  have ha_t:a∉t:=fun h=>Finset.disjoint_left.mp hd (Finset.mem_insert_self a s) h
  have hd':Disjoint s t:=Finset.disjoint_of_subset_left (Finset.subset_insert a s) hd
  rw [Finset.insert_union,z233 (by simp [ha,ha_t]),z233 ha,ih hd',z211]
private lemma z235 {ι : Type*} (s:Finset ι) :
  z230 s (fun _=>psOne)=psOne:=by
 classical
 induction s using Finset.induction with
 | empty=>simp [z230]
 | insert a s ha ih=>rw [z233 ha,ih,z213]
def toPS (p:Polynomial ℚ):PS:=fun d=>p.coeff d
private lemma z276:toPS 1=psOne:=by
 funext d;simp [toPS,psOne,Polynomial.coeff_one]
private lemma z272 (c:ℚ):toPS (C c)=z238 c psOne:=by
 funext d;simp [toPS,z238,psOne,Polynomial.coeff_C]
private lemma z273 (c:ℚ) (p:Polynomial ℚ) :
  toPS (C c*p)=z238 c (toPS p):=by
 funext d;simp [toPS,z238]
private lemma z274 (p q:Polynomial ℚ) :
  toPS (p+q)=fun d=>toPS p d+toPS q d:=by
 funext d;simp [toPS]
private lemma z279 {ι : Type*} (s:Finset ι) (f:ι→ Polynomial ℚ) :
  toPS (∑ i∈s,f i)=fun d=>∑ i∈s,toPS (f i) d:=by
 funext d;simp [toPS,Polynomial.finsetSum_coeff]
private lemma z275 (p q:Polynomial ℚ):toPS (p*q)=psMul (toPS p) (toPS q):=by
 funext d
 unfold toPS psMul
 rw [Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b=>p.coeff a*q.coeff b)]
private lemma z277 (p:Polynomial ℚ) (k:ℕ):toPS (p^k)=psPow (toPS p) k:=by
 induction k with
 | zero=>simp [psPow,z276]
 | succ k ih=>rw [pow_succ',z275,ih,psPow]
private lemma z278 {ι : Type*} (s:Finset ι) (f:ι→ Polynomial ℚ) :
  toPS (∏ i∈s,f i)=z230 s (fun i=>toPS (f i)):=by
 classical
 induction s using Finset.induction with
 | empty=>simp [z230,z276]
 | insert a s ha ih=>rw [Finset.prod_insert ha,z275,ih,z233 ha]
def z208 (a:ℚ):PS:=fun d=>(-1:ℚ)^d/a^(d+1)
private lemma z215 {a:ℚ} (ha:a≠0) :
  psMul (toPS (X+C a)) (z208 a)=psOne:=by
 funext d
 unfold psMul toPS z208 psOne
 cases d with
 | zero=>simp [ha]
 | succ d =>
  rw [if_neg (Nat.succ_ne_zero d)]
  have hcoeff:∀ r:ℕ,(X+C a:Polynomial ℚ).coeff r =
    (if r=1 then 1 else 0)+(if r=0 then a else 0):=by
   intro r;simp [Polynomial.coeff_X,Polynomial.coeff_C,eq_comm]
  rw [Finset.sum_range_succ']
  simp only [hcoeff,zero_ne_one,↓reduceIte,zero_add,Nat.sub_zero]
  rw [Finset.sum_eq_single 0]
  ·
   simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,↓reduceIte,add_zero,one_mul,
    Nat.succ_sub_one,zero_add]
   have h1:a*((-1:ℚ)^(d+1)/a^(d+1+1))=-((-1:ℚ)^d/a^(d+1)):=by
    have hp:a^(d+1+1)=a*a^(d+1):=by ring
    rw [hp,pow_succ]
    field_simp [ha,pow_ne_zero (d+1) ha]
   linarith
  ·
   intro b hb hne
   simp only [Finset.mem_range] at hb
   have hb1:b+1≠1:=by omega
   have hb0:b+1≠0:=by omega
   rw [if_neg hb1,if_neg hb0,add_zero,zero_mul]
  ·
   intro h;exfalso;exact h (Finset.mem_range.mpr (by omega))
def z216 (f:PS):PS:=fun d=>(-1:ℚ)^d*f d
private lemma z217 (f g:PS) :
  z216 (psMul f g)=psMul (z216 f) (z216 g):=by
 funext d
 unfold z216 psMul
 rw [Finset.mul_sum]
 refine Finset.sum_congr rfl fun r hr=>?_
 have hrd:r ≤ d:=Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
 have hpow:(-1:ℚ)^d=(-1:ℚ)^r*(-1:ℚ)^(d-r):=by
  rw [← pow_add,Nat.add_sub_of_le hrd]
 rw [hpow];ring
private lemma z218 (c:ℚ) (f:PS) :
  z216 (z238 c f)=z238 c (z216 f):=by
 funext d;unfold z216 z238;ring
private lemma z219 (p:Polynomial ℚ) :
  z216 (toPS p)=toPS (p.comp (-X)):=by
 funext d
 unfold z216 toPS
 induction p using Polynomial.induction_on' with
 | add p q ihp ihq =>
  rw [Polynomial.add_comp,Polynomial.coeff_add,Polynomial.coeff_add,mul_add,ihp,ihq]
 | monomial n a =>
  rw [Polynomial.monomial_comp,Polynomial.coeff_monomial]
  have hpow:(-X:Polynomial ℚ)^n=C ((-1:ℚ)^n)*X^n:=by
   rw [show (-X:Polynomial ℚ)=C (-1:ℚ)*X by simp,mul_pow,← C_pow]
  rw [hpow,← mul_assoc,← C_mul,Polynomial.coeff_C_mul_X_pow]
  by_cases h:d=n
  ·
   subst h;simp;ring
  ·
   simp [h,Ne.symm h]
private lemma z26 {p:Polynomial ℚ} {k:ℕ}
  (h:∀ d< k,p.coeff d=0):X^k ∣ p:=by
 rw [Polynomial.X_pow_dvd_iff]
 exact h
def z56 (D:ℕ) (q:ℚ):Prop:=
 ∃ z:ℤ,(z:ℚ)=(D:ℚ)*q
private lemma z67 (D:ℕ):z56 D 0:=⟨0,by simp⟩
private lemma z59 (z:ℤ):z56 1 (z:ℚ):=⟨z,by simp⟩
private lemma z62 (n:ℕ):z56 1 (n:ℚ):=⟨n,by simp⟩
private lemma z58 {D1 D2:ℕ} {q:ℚ} (hd:D1 ∣ D2) (h:z56 D1 q) :
  z56 D2 q:=by
 rcases hd with ⟨k,rfl⟩
 rcases h with ⟨z,hz⟩
 refine ⟨z*k,?_⟩
 push_cast
 linear_combination (k:ℚ)*hz
private lemma z57 {D:ℕ} {q1 q2:ℚ} (h1:z56 D q1) (h2:z56 D q2) :
  z56 D (q1+q2):=by
 rcases h1 with ⟨z1,hz1⟩;rcases h2 with ⟨z2,hz2⟩
 refine ⟨z1+z2,?_⟩;push_cast;linear_combination hz1+hz2
private lemma z63 {D:ℕ} {q:ℚ} (h:z56 D q):z56 D (-q):=by
 rcases h with ⟨z,hz⟩
 refine ⟨-z,?_⟩;push_cast;linear_combination -hz
private lemma z66 {ι : Type*} {D:ℕ} {s:Finset ι} {f:ι→ ℚ}
  (h:∀ i∈s,z56 D (f i)):z56 D (∑ i∈s,f i):=by
 classical
 induction s using Finset.induction with
 | empty=>simpa using z67 D
 | insert a s ha ih =>
  rw [Finset.sum_insert ha]
  exact z57 (h a (Finset.mem_insert_self a s))
   (ih fun i hi=>h i (Finset.mem_insert_of_mem hi))
private lemma z61 {D1 D2:ℕ} {q1 q2:ℚ} (h1:z56 D1 q1) (h2:z56 D2 q2) :
  z56 (D1*D2) (q1*q2):=by
 rcases h1 with ⟨z1,hz1⟩;rcases h2 with ⟨z2,hz2⟩
 refine ⟨z1*z2,?_⟩
 push_cast;rw [hz1,hz2];ring
private lemma z60 {D:ℕ} (c:ℤ) {q:ℚ} (h:z56 D q) :
  z56 D ((c:ℚ)*q):=by
 simpa using z61 (z59 c) h
private lemma z65 {D m:ℕ} (hm:0< m) (hd:m ∣ D) :
  z56 D (1/(m:ℚ)):=by
 rcases hd with ⟨k,rfl⟩
 refine ⟨k,?_⟩
 have hmq:(m:ℚ)≠0:=Nat.cast_ne_zero.mpr hm.ne'
 push_cast;field_simp [hmq]
private lemma z64 {D:ℕ} {a:ℤ} (ha:a≠0) (hd:a.natAbs ∣ D) :
  z56 D (1/(a:ℚ)):=by
 have hm:0< a.natAbs:=Int.natAbs_pos.mpr ha
 have h1:=z65 hm hd
 rcases Int.natAbs_eq a with hpos | hneg
 ·
  have:(a:ℚ)=(a.natAbs:ℚ):=by conv_lhs=>rw [hpos];rw [Int.cast_natCast]
  rwa [this]
 ·
  have:(a:ℚ)=-(a.natAbs:ℚ):=by conv_lhs=>rw [hneg];rw [Int.cast_neg,Int.cast_natCast]
  rw [this,div_neg]
  exact z63 h1
private lemma z130 {m N:ℕ} (hm:0< m) (hle:m ≤ N) :
  m ∣ Nat.lcmUpto N:=by
 unfold Nat.lcmUpto
 exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hm,hle⟩)
private lemma z120 {M N:ℕ} (hle:M ≤ N) :
  Nat.lcmUpto M ∣ Nat.lcmUpto N:=by
 unfold Nat.lcmUpto
 exact Finset.lcm_dvd fun k hk =>
  Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,(Finset.mem_Icc.mp hk).2.trans hle⟩)
def z199 (D a:ℕ) (f:PS):Prop:=
 ∀ d:ℕ,z56 (D^(d+a)) (f d)
private lemma z205 (D:ℕ):z199 D 0 psOne:=by
 intro d
 unfold psOne
 split_ifs with h
 ·
  subst h;simpa using z62 1
 ·
  exact z67 _
private lemma z200 {D1 D2 a:ℕ} {f:PS} (hd:D1 ∣ D2) (h:z199 D1 a f) :
 z199 D2 a f:=fun d=>z58 (pow_dvd_pow_of_dvd hd _) (h d)
private lemma z201 {D a:ℕ} (c:ℤ) {f:PS} (h:z199 D a f) :
 z199 D a (z238 (c:ℚ) f):=fun d=>z60 c (h d)
private lemma z204 {D a:ℕ} {f:PS} (h:z199 D a f) :
  z199 D a (z216 f):=by
 intro d
 unfold z216
 have:((-1:ℚ)^d)=(((-1:ℤ)^d:ℤ):ℚ):=by push_cast;rfl
 rw [this]
 exact z60 ((-1:ℤ)^d) (h d)
private lemma z203 {D a b:ℕ} {f g:PS}
  (hf:z199 D a f) (hg:z199 D b g) :
  z199 D (a+b) (psMul f g):=by
 intro d
 unfold psMul
 refine z66 fun r hr=>?_
 have hrd:r ≤ d:=Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
 have hmul:=z61 (hf r) (hg (d-r))
 have hexp:D^(r+a)*D^(d-r+b)=D^(d+(a+b)):=by
  rw [← pow_add];congr 1;omega
 rwa [hexp] at hmul
private lemma z206 {D a:ℕ} {f:PS} (hf:z199 D a f) (k:ℕ) :
  z199 D (k*a) (psPow f k):=by
 induction k with
 | zero=>simpa [psPow] using z205 D
 | succ k ih =>
  rw [psPow,show (k+1)*a=a+k*a by ring]
  exact z203 hf ih
private lemma z207 {ι : Type*} {D:ℕ} (s:Finset ι) (a:ι→ ℕ) (f:ι→ PS)
  (hf:∀ i∈s,z199 D (a i) (f i)) :
  z199 D (∑ i∈s,a i) (z230 s f):=by
 classical
 induction s using Finset.induction with
 | empty=>simpa [z230] using z205 D
 | insert x s hx ih =>
  rw [Finset.sum_insert hx,z233 hx]
  exact z203 (hf x (Finset.mem_insert_self x s))
   (ih fun i hi=>hf i (Finset.mem_insert_of_mem hi))
private lemma z202 {D:ℕ} {a:ℤ} (ha:a≠0) (hd:a.natAbs ∣ D) :
  z199 D 1 (z208 (a:ℚ)):=by
 intro d
 unfold z208
 have h1:((-1:ℚ)^d)/(a:ℚ)^(d+1) =
   (((-1:ℤ)^d:ℤ):ℚ)*(1/(a:ℚ))^(d+1):=by
  push_cast;rw [one_div_pow];ring
 rw [h1]
 refine z60 ((-1:ℤ)^d) ?_
 have hbase:=z64 ha hd
 have hpow:∀ k:ℕ,z56 (D^k) ((1/(a:ℚ))^k):=by
  intro k;induction k with
  | zero=>simpa using z62 1
  | succ k ih=>rw [pow_succ,pow_succ];exact z61 ih hbase
 exact hpow (d+1)
def z147 (p:ℕ) (b:ℤ) (q:ℚ):Prop:=
 q=0∨b ≤ padicValRat p q
private lemma z158 (p:ℕ) (b:ℤ):z147 p b 0:=Or.inl rfl
private lemma z151 {p:ℕ} {b1 b2:ℤ} {q:ℚ} (hle:b1 ≤ b2)
  (h:z147 p b2 q):z147 p b1 q:=
 h.imp_right fun hv=>hle.trans hv
private lemma z149 (p:ℕ) [Fact p.Prime] (z:ℤ):z147 p 0 (z:ℚ):=by
 rcases eq_or_ne z 0 with rfl | hz
 ·
  exact Or.inl (by simp)
 ·
  right
  rw [padicValRat.of_int]
  exact Int.natCast_nonneg _
private lemma z153 (p:ℕ) [Fact p.Prime] (n:ℕ):z147 p 0 (n:ℚ):=by
 simpa using z149 p (n:ℤ)
private lemma z154 {p:ℕ} {b:ℤ} {q:ℚ} (h:z147 p b q) :
  z147 p b (-q):=by
 rcases h with rfl | hv
 ·
  exact Or.inl (by simp)
 ·
  right;rwa [padicValRat.neg]
private lemma z148 {p:ℕ} [Fact p.Prime] {b:ℤ} {q1 q2:ℚ}
  (h1:z147 p b q1) (h2:z147 p b q2):z147 p b (q1+q2):=by
 by_cases hsum:q1+q2=0
 ·
  exact Or.inl hsum
 ·
  rcases h1 with rfl | hv1
  ·
   rw [zero_add];exact h2
  ·
   rcases h2 with rfl | hv2
   ·
    rw [add_zero];exact Or.inr hv1
   ·
    right
    exact (le_min hv1 hv2).trans (padicValRat.min_le_padicValRat_add hsum)
private lemma z157 {ι : Type*} {p:ℕ} [Fact p.Prime] {b:ℤ} {s:Finset ι} {f:ι→ ℚ}
  (h:∀ i∈s,z147 p b (f i)):z147 p b (∑ i∈s,f i):=by
 classical
 induction s using Finset.induction with
 | empty=>simpa using z158 p b
 | insert a s ha ih =>
  rw [Finset.sum_insert ha]
  exact z148 (h a (Finset.mem_insert_self a s))
   (ih fun i hi=>h i (Finset.mem_insert_of_mem hi))
private lemma z152 {p:ℕ} [Fact p.Prime] {b1 b2:ℤ} {q1 q2:ℚ}
  (h1:z147 p b1 q1) (h2:z147 p b2 q2):z147 p (b1+b2) (q1*q2):=by
 rcases h1 with rfl | hv1
 ·
  exact Or.inl (by simp)
 ·
  rcases h2 with rfl | hv2
  ·
   exact Or.inl (by simp)
  ·
   by_cases hq1:q1=0
   ·
    exact Or.inl (by simp [hq1])
   ·
    by_cases hq2:q2=0
    ·
     exact Or.inl (by simp [hq2])
    ·
     right;rw [padicValRat.mul hq1 hq2];linarith
private lemma z156 {p:ℕ} [Fact p.Prime] {b:ℤ} {q:ℚ}
  (h:z147 p b q) (k:ℕ):z147 p ((k:ℤ)*b) (q^k):=by
 induction k with
 | zero =>
  right;simp
 | succ k ih =>
  rw [pow_succ,show ((k+1:ℕ):ℤ)*b=(k:ℤ)*b+b by push_cast;ring]
  exact z152 ih h
private lemma z150 {p:ℕ} [Fact p.Prime] (z:ℤ) (e:ℕ) :
  z147 p (e:ℤ) (z:ℚ)↔((p^e:ℕ):ℤ) ∣ z:=by
 rcases eq_or_ne z 0 with rfl | hz
 ·
  simp [z147]
 ·
  have hzq:(z:ℚ)≠0:=Int.cast_ne_zero.mpr hz
  simp only [z147,hzq,false_or,padicValRat.of_int]
  unfold padicValInt
  rw [Int.ofNat_le,← padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hz),
   Int.natCast_dvd]
private lemma z160 {p m:ℕ} [Fact p.Prime] (hm:0< m)
  (hlt:m< p*p):padicValNat p m ≤ 1:=by
 by_contra! hgt
 have h2:2 ≤ padicValNat p m:=hgt
 have hdvd:p^2 ∣ m:=(padicValNat_dvd_iff_le hm.ne').mpr h2
 have hle:p^2 ≤ m:=Nat.le_of_dvd hm hdvd
 nlinarith
private lemma z159 {p m:ℕ} [hp:Fact p.Prime]
  (hlt:m< p*p):padicValNat p m.factorial=m/p:=by
 rcases eq_or_ne m 0 with rfl | hm0
 ·
  simp
 ·
  have hlog:Nat.log p m< 2:=by
   rw [Nat.log_lt_iff_lt_pow hp.out.one_lt hm0]
   simpa [sq] using hlt
  rw [padicValNat_factorial hlog]
  have hIco:Finset.Ico 1 2={1}:=by decide
  rw [hIco,Finset.sum_singleton,pow_one]
private lemma z129 (m p:ℕ) :
  ((m/p:ℕ):ℤ)=⌊(m:ℝ)/(p:ℝ)⌋:=by
 rcases eq_or_ne p 0 with rfl | hp0
 ·
  simp
 ·
  symm
  rw [Int.floor_eq_iff]
  have hppos:(0:ℝ)< p:=Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp0)
  have hdiv:=Nat.div_add_mod m p
  have hmod:=Nat.mod_lt m (Nat.pos_of_ne_zero hp0)
  have hdivr:(p:ℝ)*((m/p:ℕ):ℝ)+((m % p:ℕ):ℝ)=m:=by exact_mod_cast hdiv
  have hmodr:((m % p:ℕ):ℝ)< p:=by exact_mod_cast hmod
  have hmodnn:(0:ℝ) ≤ (m % p:ℕ):=Nat.cast_nonneg _
  rw [Int.cast_natCast]
  constructor
  ·
   rw [le_div_iff₀ hppos];linarith
  ·
   rw [div_lt_iff₀ hppos];linarith
private lemma z84 {A p:ℕ} (hA:1 ≤ A) (hp:1 ≤ p) :
  (((A-1)/p:ℕ):ℤ)=-⌊(-(A:ℝ))/(p:ℝ)⌋ - 1:=by
 have hppos:(0:ℝ)< p:=Nat.cast_pos.mpr hp
 have hdiv:=Nat.div_add_mod (A-1) p
 have hmod:=Nat.mod_lt (A-1) hp
 set q:=(A-1)/p
 set r:=(A-1) % p
 have hAr:(A:ℝ)=(p:ℝ)*(q:ℝ)+(r:ℝ)+1:=by
  have:A=p*q+r+1:=by omega
  exact_mod_cast this
 have hr1:(r:ℝ)+1 ≤ p:=by exact_mod_cast (show r+1 ≤ p by omega)
 have hrnn:(0:ℝ) ≤ r:=Nat.cast_nonneg r
 have hfl:⌊(-(A:ℝ))/(p:ℝ)⌋=-((q:ℤ)+1):=by
  rw [Int.floor_eq_iff,Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one]
  have hdist1:-((q:ℝ)+1)*(p:ℝ)=-(p:ℝ)*(q:ℝ)-(p:ℝ):=by ring
  have hdist2:(-((q:ℝ)+1)+1)*(p:ℝ)=-(p:ℝ)*(q:ℝ):=by ring
  constructor
  ·
   rw [le_div_iff₀ hppos,hdist1];linarith
  ·
   rw [div_lt_iff₀ hppos,hdist2];linarith
 omega
def z221 (p:ℕ) (B:ℤ) (f:PS):Prop:=
 ∀ d:ℕ,z147 p (B-(d:ℤ)) (f d)
private lemma z226 (p:ℕ) [Fact p.Prime]:z221 p 0 psOne:=by
 intro d
 unfold psOne
 split_ifs with h
 ·
  subst h;simpa using z153 p 1
 ·
  exact z158 p _
private lemma z222 {p:ℕ} {B1 B2:ℤ} {f:PS} (hle:B1 ≤ B2)
  (h:z221 p B2 f):z221 p B1 f:=
 fun d=>z151 (by linarith) (h d)
private lemma z229 {p:ℕ} [Fact p.Prime] {B1 B2:ℤ} {c:ℚ} {f:PS}
  (hc:z147 p B1 c) (hf:z221 p B2 f) :
  z221 p (B1+B2) (z238 c f):=by
 intro d
 unfold z238
 exact z151 (by omega) (z152 hc (hf d))
private lemma z224 {p:ℕ} {B:ℤ} {f:PS} (h:z221 p B f) :
  z221 p B (z216 f):=by
 intro d
 unfold z216
 rcases Nat.even_or_odd d with ⟨k,hk⟩ | ⟨k,hk⟩
 ·
  have:(-1:ℚ)^d=1:=by rw [hk,← two_mul,pow_mul];norm_num
  rw [this,one_mul];exact h d
 ·
  have:(-1:ℚ)^d=-1:=by rw [hk,pow_succ,pow_mul];norm_num
  rw [this,neg_one_mul];exact z154 (h d)
private lemma z223 {p:ℕ} [Fact p.Prime] {B1 B2:ℤ} {f g:PS}
  (hf:z221 p B1 f) (hg:z221 p B2 g) :
  z221 p (B1+B2) (psMul f g):=by
 intro d
 unfold psMul
 refine z157 fun r hr=>?_
 have hrd:r ≤ d:=Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
 have h1:=z152 (hf r) (hg (d-r))
 refine z151 ?_ h1
 have:((d-r:ℕ):ℤ)=(d:ℤ)-(r:ℤ):=Int.ofNat_sub hrd
 omega
private lemma z227 {p:ℕ} [Fact p.Prime] {B:ℤ} {f:PS}
  (hf:z221 p B f) (k:ℕ) :
  z221 p ((k:ℤ)*B) (psPow f k):=by
 induction k with
 | zero=>simpa [psPow] using z226 p
 | succ k ih =>
  rw [psPow,show ((k+1:ℕ):ℤ)*B=B+(k:ℤ)*B by push_cast;ring]
  exact z223 hf ih
private lemma z228 {ι : Type*} {p:ℕ} [Fact p.Prime] (s:Finset ι)
  (B:ι→ ℤ) (f:ι→ PS) (hf:∀ i∈s,z221 p (B i) (f i)) :
  z221 p (∑ i∈s,B i) (z230 s f):=by
 classical
 induction s using Finset.induction with
 | empty=>simpa [z230] using z226 p
 | insert x s hx ih =>
  rw [Finset.sum_insert hx,z233 hx]
  exact z223 (hf x (Finset.mem_insert_self x s))
   (ih fun i hi=>hf i (Finset.mem_insert_of_mem hi))
private lemma z155 {p:ℕ} [Fact p.Prime] {a:ℤ}
  (ha:a≠0) (hlt:a.natAbs< p*p) :
  z147 p (-1) (1/(a:ℚ)):=by
 have haq:(a:ℚ)≠0:=Int.cast_ne_zero.mpr ha
 right
 rw [one_div,padicValRat.inv,padicValRat.of_int]
 unfold padicValInt
 have hle:=z160 (Int.natAbs_pos.mpr ha) hlt
 omega
private lemma z225 {p:ℕ} [Fact p.Prime] {a:ℤ}
  (ha:a≠0) (hlt:a.natAbs< p*p) :
  z221 p 0 (z238 (a:ℚ) (z208 (a:ℚ))):=by
 intro d
 unfold z238 z208
 have haq:(a:ℚ)≠0:=Int.cast_ne_zero.mpr ha
 have h1:(a:ℚ)*((-1:ℚ)^d/(a:ℚ)^(d+1)) =
   ((-1:ℚ)^d)*(1/(a:ℚ))^d:=by
  rw [pow_succ,one_div_pow];field_simp [haq,pow_ne_zero d haq]
 rw [h1]
 have hsign:z147 p 0 ((-1:ℚ)^d):=by
  have:((-1:ℚ)^d)=(((-1:ℤ)^d:ℤ):ℚ):=by push_cast;rfl
  rw [this];exact z149 p _
 have hpow:=z156 (z155 ha hlt) d
 have hmul:=z152 hsign hpow
 exact z151 (by omega) hmul
private lemma z185 (M L:ℕ) :
  (∏ r∈Finset.Icc 1 L,((M+r:ℕ):ℚ)) =
   (L.factorial:ℚ)*(Nat.choose (M+L) L:ℚ):=by
 induction L with
 | zero=>simp
 | succ L ih =>
  rw [Finset.prod_Icc_succ_top (by omega:1 ≤ L+1),ih]
  have hch:(L+1)*Nat.choose (M+L+1) (L+1)=(M+L+1)*Nat.choose (M+L) L:=by
   have:=Nat.add_one_mul_choose_eq (M+L) L
   linarith
  have hchr:((L+1:ℕ):ℚ)*(Nat.choose (M+L+1) (L+1):ℚ) =
    ((M+L+1:ℕ):ℚ)*(Nat.choose (M+L) L:ℚ):=by exact_mod_cast hch
  rw [Nat.factorial_succ,Nat.cast_mul,show M+(L+1)=M+L+1 by omega]
  linear_combination (L.factorial:ℚ)*hchr.symm
private lemma z187 (w s:ℕ) :
  (∏ j∈Finset.range s,((w:ℚ)-(j:ℚ))) =
   (s.factorial:ℚ)*(Nat.choose w s:ℚ):=by
 induction s with
 | zero=>simp
 | succ s ih =>
  rw [Finset.prod_range_succ,ih]
  by_cases hsw:s ≤ w
  ·
   have hch:(s+1)*Nat.choose w (s+1)=(w-s)*Nat.choose w s:=by
    have:=Nat.choose_succ_right_eq w s
    linarith
   have hchr:((s+1:ℕ):ℚ)*(Nat.choose w (s+1):ℚ) =
     ((w:ℚ)-(s:ℚ))*(Nat.choose w s:ℚ):=by
    have h1:((w-s:ℕ):ℚ)=(w:ℚ)-(s:ℚ):=Nat.cast_sub hsw
    rw [← h1];exact_mod_cast hch
   rw [Nat.factorial_succ,Nat.cast_mul]
   linear_combination (s.factorial:ℚ)*hchr.symm
  ·
   have h1:Nat.choose w (s+1)=0:=Nat.choose_eq_zero_of_lt (by omega)
   have h2:Nat.choose w s=0:=by
    rcases eq_or_lt_of_le (show w ≤ s by omega) with rfl | hlt
    ·
     exfalso;omega
    ·
     exact Nat.choose_eq_zero_of_lt hlt
   by_cases hws:w=s
   ·
    subst hws;simp [h1]
   ·
    have hlt:w< s:=by omega
    rw [Nat.choose_eq_zero_of_lt hlt,h1];simp
private lemma z188 (M L:ℕ) :
  C ((L.factorial:ℚ)⁻¹)*(∏ r∈Finset.Icc 1 L,(X+C ((M+r:ℕ):ℚ))) =
  ∑ s∈Finset.range (L+1),
   C ((Nat.choose (M+L) (L-s):ℚ)*(s.factorial:ℚ)⁻¹) *
    (∏ j∈Finset.range s,(X-C (j:ℚ))):=by
 set p1:Polynomial ℚ:=C ((L.factorial:ℚ)⁻¹)*(∏ r∈Finset.Icc 1 L,(X+C ((M+r:ℕ):ℚ)))
 set p2:Polynomial ℚ:=∑ s∈Finset.range (L+1),
   C ((Nat.choose (M+L) (L-s):ℚ)*(s.factorial:ℚ)⁻¹) *
    (∏ j∈Finset.range s,(X-C (j:ℚ)))
 have heval:∀ w:ℕ,p1.eval (w:ℚ)=p2.eval (w:ℚ):=by
  intro w
  simp only [p1,p2,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_prod,
   Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_finset_sum]
  have hL:(L.factorial:ℚ)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero L)
  have hLHS:(∏ r∈Finset.Icc 1 L,((w:ℚ)+((M+r:ℕ):ℚ))) =
    (L.factorial:ℚ)*(Nat.choose (w+M+L) L:ℚ):=by
   have hcongr:(∏ r∈Finset.Icc 1 L,((w:ℚ)+((M+r:ℕ):ℚ))) =
     ∏ r∈Finset.Icc 1 L,(((w+M+r:ℕ):ℚ)):=by
    refine Finset.prod_congr rfl fun r _=>by push_cast;ring
   rw [hcongr,z185 (w+M) L]
  rw [hLHS,inv_mul_cancel_left₀ hL]
  have hRHS:∑ s∈Finset.range (L+1),
    (Nat.choose (M+L) (L-s):ℚ)*(s.factorial:ℚ)⁻¹ *
     ∏ j∈Finset.range s,((w:ℚ)-(j:ℚ)) =
    ∑ s∈Finset.range (L+1),
     (Nat.choose w s:ℚ)*(Nat.choose (M+L) (L-s):ℚ):=by
   refine Finset.sum_congr rfl fun s _=>?_
   have hs:(s.factorial:ℚ)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s)
   rw [z187 w s]
   field_simp [hs]
  rw [hRHS]
  have hv:=Nat.add_choose_eq w (M+L) L
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  have hvr:(Nat.choose (w+(M+L)) L:ℚ) =
    ∑ s∈Finset.range (L+1),(Nat.choose w s:ℚ)*(Nat.choose (M+L) (L-s):ℚ):=by
   exact_mod_cast hv
  rw [show w+M+L=w+(M+L) by omega,hvr]
 by_contra hne
 have hsub:p1-p2≠0:=sub_ne_zero.mpr hne
 have hcard:=Polynomial.card_roots' (p1-p2)
 set N:=(p1-p2).natDegree+1
 have hsub_roots:(Finset.range N).val.map (fun w:ℕ=>(w:ℚ)) ⊆ (p1-p2).roots:=by
  intro x hx
  rcases Multiset.mem_map.mp hx with ⟨w,_,rfl⟩
  rw [Polynomial.mem_roots hsub,Polynomial.IsRoot,Polynomial.eval_sub,heval w,sub_self]
 have hnd:((Finset.range N).val.map (fun w:ℕ=>(w:ℚ))).Nodup:=
  (Finset.range N).nodup.map (fun _ _ h=>Nat.cast_injective h)
 have hle:Multiset.card ((Finset.range N).val.map (fun w:ℕ=>(w:ℚ))) ≤
   Multiset.card (p1-p2).roots:=
  Multiset.card_le_card (Multiset.le_iff_subset hnd |>.mpr hsub_roots)
 simp only [Multiset.card_map,Finset.card_val,Finset.card_range] at hle
 omega
private lemma z80 {L s:ℕ} (hs:s ≤ L) :
  z199 (Nat.lcmUpto L) 0
   (toPS (C ((s.factorial:ℚ)⁻¹)*(∏ j∈Finset.range s,(X-C (j:ℚ))))):=by
 cases s with
 | zero =>
  simpa [z276] using z205 (Nat.lcmUpto L)
 | succ s =>
  have hsplit:(∏ j∈Finset.range (s+1),(X-C (j:ℚ))) =
    X*∏ j∈Finset.Icc 1 s,(X-C (j:ℚ)):=by
   rw [Finset.prod_range_succ']
   simp only [Nat.cast_zero,map_zero,sub_zero,mul_comm _ X]
   congr 1
   refine Finset.prod_bij (fun j _=>j+1) ?_ ?_ ?_ ?_
   ·
    intro j hj;simp only [Finset.mem_range] at hj;simp only [Finset.mem_Icc];omega
   ·
    intro j1 _ j2 _ h;omega
   ·
    intro j hj;simp only [Finset.mem_Icc] at hj
    exact ⟨j-1,Finset.mem_range.mpr (by omega),by omega⟩
   ·
    intro j _;push_cast;rfl
  have hfac:(∏ j∈Finset.Icc 1 s,(j:ℚ))=(s.factorial:ℚ):=by
   clear hs hsplit
   induction s with
   | zero=>simp
   | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega:1 ≤ k+1),ih,Nat.factorial_succ,Nat.cast_mul]
    ring
  have hpoly:C (((s+1).factorial:ℚ)⁻¹)*(∏ j∈Finset.range (s+1),(X-C (j:ℚ))) =
    (C (1/((s+1:ℕ):ℚ))*X) *
     (∏ j∈Finset.Icc 1 s,(C (1/(j:ℚ))*X-1)):=by
   rw [hsplit]
   have hprod_eq:(∏ j∈Finset.Icc 1 s,(C (1/(j:ℚ))*X-1)) =
     C ((s.factorial:ℚ)⁻¹)*(∏ j∈Finset.Icc 1 s,(X-C (j:ℚ))):=by
    have hstep:∀ j∈Finset.Icc 1 s,
      (C (1/(j:ℚ))*X-1:Polynomial ℚ) =
       C ((j:ℚ)⁻¹)*(X-C (j:ℚ)):=by
     intro j hj
     have hj0:(j:ℚ)≠0:=Nat.cast_ne_zero.mpr (by have:=(Finset.mem_Icc.mp hj).1;omega)
     rw [mul_sub,← C_mul,inv_mul_cancel₀ hj0,map_one,one_div]
    rw [Finset.prod_congr rfl hstep,Finset.prod_mul_distrib,← map_prod,
     Finset.prod_inv_distrib,hfac]
   rw [hprod_eq,Nat.factorial_succ,Nat.cast_mul,mul_inv,one_div]
   rw [← mul_assoc,← mul_assoc]
   have hcomm:C ((s+1:ℕ):ℚ)⁻¹*X*C (s.factorial:ℚ)⁻¹ =
     C (((s+1:ℕ):ℚ)⁻¹*(s.factorial:ℚ)⁻¹)*X:=by
    rw [C_mul];ring
   rw [hcomm]
  rw [hpoly,z275,z278]
  have hX:z199 (Nat.lcmUpto L) 0 (toPS (C (1/((s+1:ℕ):ℚ))*X)):=by
   intro d
   unfold toPS
   rw [Polynomial.coeff_C_mul,Polynomial.coeff_X]
   by_cases hd1:d=1
   ·
    subst hd1
    simp only [↓reduceIte,mul_one,add_zero,pow_one]
    exact z65 (by omega) (z130 (by omega) hs)
   ·
    simp only [if_neg (Ne.symm hd1),mul_zero]
    exact z67 _
  have hprod:z199 (Nat.lcmUpto L) 0
    (z230 (Finset.Icc 1 s) fun j=>toPS (C (1/(j:ℚ))*X-1)):=by
   have h0:∑ _j∈Finset.Icc 1 s,(0:ℕ)=0:=by simp
   rw [← h0]
   refine z207 _ (fun _=>0) _ fun j hj=>?_
   intro d
   unfold toPS
   rw [Polynomial.coeff_sub,Polynomial.coeff_C_mul,Polynomial.coeff_X,Polynomial.coeff_one]
   rcases d with _ | _ | d
   ·
    simp only [one_ne_zero,↓reduceIte,mul_zero,zero_sub,zero_add,pow_zero]
    simpa using z63 (z62 1)
   ·
    simp only [zero_add,pow_one,↓reduceIte,mul_one,one_ne_zero,sub_zero,add_zero]
    exact z65 (Finset.mem_Icc.mp hj).1
     (z130 (Finset.mem_Icc.mp hj).1 (le_trans (Finset.mem_Icc.mp hj).2 (by omega:s ≤ L)))
   ·
    simp only [show ¬(1=d+2) by omega,show ¬(d+2=0) by omega,
     ↓reduceIte,mul_zero,sub_zero]
    exact z67 _
  simpa using z203 hX hprod
private lemma z189 (M L:ℕ) :
  z199 (Nat.lcmUpto L) 0
   (toPS (C ((L.factorial:ℚ)⁻¹)*(∏ r∈Finset.Icc 1 L,(X+C ((M+r:ℕ):ℚ))))):=by
 rw [z188,z279]
 intro d
 refine z66 fun s hs=>?_
 have hsL:s ≤ L:=Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
 have h1:C ((Nat.choose (M+L) (L-s):ℚ)*(s.factorial:ℚ)⁻¹) *
   ∏ j∈Finset.range s,(X-C (j:ℚ)) =
   C ((Nat.choose (M+L) (L-s):ℚ)) *
    (C ((s.factorial:ℚ)⁻¹)*∏ j∈Finset.range s,(X-C (j:ℚ))):=by
  rw [C_mul,mul_assoc]
 rw [h1,z273]
 unfold z238
 exact z60 (Nat.choose (M+L) (L-s):ℤ) (z80 hsL d)
private lemma z190 {p:ℕ} [Fact p.Prime] {M L:ℕ}
  (hlt:M+L< p*p) :
  z221 p (⌊((M+L:ℕ):ℝ)/p⌋ - ⌊(M:ℝ)/p⌋ - ⌊(L:ℝ)/p⌋)
   (toPS (C ((L.factorial:ℚ)⁻¹)*(∏ r∈Finset.Icc 1 L,(X+C ((M+r:ℕ):ℚ))))):=by
 have hpoly:C ((L.factorial:ℚ)⁻¹)*(∏ r∈Finset.Icc 1 L,(X+C ((M+r:ℕ):ℚ))) =
   C (Nat.choose (M+L) L:ℚ) *
    (∏ r∈Finset.Icc 1 L,(C (1/((M+r:ℕ):ℚ))*X+1)):=by
  have hstep:∀ r∈Finset.Icc 1 L,
    (C (1/((M+r:ℕ):ℚ))*X+1:Polynomial ℚ) =
     C (((M+r:ℕ):ℚ)⁻¹)*(X+C ((M+r:ℕ):ℚ)):=by
   intro r hr
   have hr0:((M+r:ℕ):ℚ)≠0:=Nat.cast_ne_zero.mpr (by have:=(Finset.mem_Icc.mp hr).1;omega)
   rw [mul_add,← C_mul,inv_mul_cancel₀ hr0,map_one,one_div]
  rw [Finset.prod_congr rfl hstep,Finset.prod_mul_distrib,← map_prod,
   Finset.prod_inv_distrib,z185 M L,mul_inv,
   ← mul_assoc,← C_mul]
  have hch0:(Nat.choose (M+L) L:ℚ)≠0:=
   Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have hcancel:(Nat.choose (M+L) L:ℚ)*((L.factorial:ℚ)⁻¹*(Nat.choose (M+L) L:ℚ)⁻¹) =
    (L.factorial:ℚ)⁻¹:=by
   field_simp [hch0]
  rw [hcancel]
 rw [hpoly,z273,z278]
 have hch_val:z147 p (⌊((M+L:ℕ):ℝ)/p⌋ - ⌊(M:ℝ)/p⌋ - ⌊(L:ℝ)/p⌋)
   (Nat.choose (M+L) L:ℚ):=by
  have hch_pos:0< Nat.choose (M+L) L:=Nat.choose_pos (by omega)
  have hch_eq:(Nat.choose (M+L) L:ℚ) =
    ((M+L).factorial:ℚ)/((M.factorial:ℚ)*(L.factorial:ℚ)):=by
   have h:=Nat.choose_mul_factorial_mul_factorial (show L ≤ M+L by omega)
   rw [Nat.add_sub_cancel] at h
   have hr:(Nat.choose (M+L) L:ℚ)*(L.factorial:ℚ)*(M.factorial:ℚ) =
     ((M+L).factorial:ℚ):=by exact_mod_cast h
   have hLf:(L.factorial:ℚ)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero L)
   have hMf:(M.factorial:ℚ)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero M)
   field_simp [hLf,hMf];linarith
  right
  rw [hch_eq,padicValRat.div (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
   (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))),
   padicValRat.mul (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
   padicValRat.of_nat,padicValRat.of_nat,padicValRat.of_nat,
   z159 hlt,
   z159 (by omega),
   z159 (by omega),
   z129,z129,z129]
  omega
 have hprod:z221 p 0
   (z230 (Finset.Icc 1 L) fun r=>toPS (C (1/((M+r:ℕ):ℚ))*X+1)):=by
  have h0:∑ _r∈Finset.Icc 1 L,(0:ℤ)=0:=by simp
  rw [← h0]
  refine z228 _ (fun _=>0) _ fun r hr=>?_
  intro d
  unfold toPS
  rw [Polynomial.coeff_add,Polynomial.coeff_C_mul,Polynomial.coeff_X,Polynomial.coeff_one]
  rcases d with _ | _ | d
  ·
   simp only [one_ne_zero,↓reduceIte,mul_zero,zero_add,CharP.cast_eq_zero,sub_zero]
   simpa using z153 p 1
  ·
   simp only [↓reduceIte,mul_one,one_ne_zero,add_zero,Nat.cast_one,zero_sub]
   have hr1:1 ≤ r:=(Finset.mem_Icc.mp hr).1
   have hrL:r ≤ L:=(Finset.mem_Icc.mp hr).2
   simpa using z155 (a:=((M+r:ℕ):ℤ)) (by omega) (by
    rw [Int.natAbs_natCast];omega)
  ·
   simp only [show ¬(1=d+2) by omega,show ¬(d+2=0) by omega,
    ↓reduceIte,mul_zero,add_zero]
   exact z158 p _
 simpa using z229 hch_val hprod
def z195 (a b m:ℕ):PS:=
 z238 (((b-a).factorial:ℚ))
  (z230 ((Finset.Icc a b).erase m) (fun r=>z208 ((r:ℚ)-(m:ℚ))))
def z191 (a b m:ℕ):PS:=
 z238 (((b-a).factorial:ℚ))
  (z230 (Finset.Icc a b) (fun r=>z208 ((r:ℚ)-(m:ℚ))))
private lemma z186 {a b m:ℕ} (ham:a ≤ m) (hmb:m ≤ b) :
  (∏ r∈(Finset.Icc a b).erase m,((r:ℚ)-(m:ℚ))) =
   (-1:ℚ)^(m-a)*(((m-a).factorial:ℚ)*((b-m).factorial:ℚ)):=by
 have hsplit:(Finset.Icc a b).erase m=Finset.Ico a m ∪ Finset.Ioc m b:=by
  ext r;simp only [Finset.mem_erase,Finset.mem_Icc,Finset.mem_union,Finset.mem_Ico,
   Finset.mem_Ioc];omega
 have hdisj:Disjoint (Finset.Ico a m) (Finset.Ioc m b):=by
  rw [Finset.disjoint_left];intro r h1 h2
  simp only [Finset.mem_Ico,Finset.mem_Ioc] at h1 h2;omega
 rw [hsplit,Finset.prod_union hdisj]
 have hleft:(∏ r∈Finset.Ico a m,((r:ℚ)-(m:ℚ))) =
   (-1:ℚ)^(m-a)*((m-a).factorial:ℚ):=by
  have hbij:(∏ r∈Finset.Ico a m,((r:ℚ)-(m:ℚ))) =
    ∏ j∈Finset.Icc 1 (m-a),(-(j:ℚ)):=by
   refine Finset.prod_bij (fun r _=>m-r) ?_ ?_ ?_ ?_
   ·
    intro r hr;simp only [Finset.mem_Ico] at hr;simp only [Finset.mem_Icc];omega
   ·
    intro r1 hr1 r2 hr2 h;simp only [Finset.mem_Ico] at hr1 hr2;omega
   ·
    intro j hj;simp only [Finset.mem_Icc] at hj
    exact ⟨m-j,Finset.mem_Ico.mpr (by omega),by omega⟩
   ·
    intro r hr
    have hrm:r ≤ m:=(Finset.mem_Ico.mp hr).2.le
    rw [Nat.cast_sub hrm];ring
  have hneg_eq:(∏ j∈Finset.Icc 1 (m-a),-(j:ℚ)) =
    ∏ j∈Finset.Icc 1 (m-a),((-1:ℚ)*(j:ℚ)):=
   Finset.prod_congr rfl fun j _=>by ring
  rw [hbij,hneg_eq,Finset.prod_mul_distrib,Finset.prod_const,Nat.card_Icc,
   show m-a+1-1=m-a by omega]
  congr 1
  clear hbij hsplit hdisj
  induction (m-a) with
  | zero=>simp
  | succ k ih =>
   rw [Finset.prod_Icc_succ_top (by omega:1 ≤ k+1),ih,Nat.factorial_succ,Nat.cast_mul]
   ring
 have hright:(∏ r∈Finset.Ioc m b,((r:ℚ)-(m:ℚ)))=((b-m).factorial:ℚ):=by
  have hbij:(∏ r∈Finset.Ioc m b,((r:ℚ)-(m:ℚ))) =
    ∏ j∈Finset.Icc 1 (b-m),(j:ℚ):=by
   refine Finset.prod_bij (fun r _=>r-m) ?_ ?_ ?_ ?_
   ·
    intro r hr;simp only [Finset.mem_Ioc] at hr;simp only [Finset.mem_Icc];omega
   ·
    intro r1 hr1 r2 hr2 h;simp only [Finset.mem_Ioc] at hr1 hr2;omega
   ·
    intro j hj;simp only [Finset.mem_Icc] at hj
    exact ⟨m+j,Finset.mem_Ioc.mpr (by omega),by omega⟩
   ·
    intro r hr
    have hmr:m ≤ r:=(Finset.mem_Ioc.mp hr).1.le
    rw [Nat.cast_sub hmr]
  rw [hbij]
  clear hbij hleft hsplit hdisj
  induction (b-m) with
  | zero=>simp
  | succ k ih =>
   rw [Finset.prod_Icc_succ_top (by omega:1 ≤ k+1),ih,Nat.factorial_succ,Nat.cast_mul]
   ring
 rw [hleft,hright];ring
private lemma z196 {a b m:ℕ} (ham:a ≤ m) (hmb:m ≤ b) :
  z195 a b m =
   z238 ((-1:ℚ)^(m-a)*(Nat.choose (b-a) (m-a):ℚ))
    (z230 ((Finset.Icc a b).erase m)
     (fun r=>z238 ((r:ℚ)-(m:ℚ)) (z208 ((r:ℚ)-(m:ℚ))))):=by
 unfold z195
 rw [z236,z239,z186 ham hmb]
 congr 1
 have hch:=Nat.choose_mul_factorial_mul_factorial (show m-a ≤ b-a by omega)
 rw [show b-a-(m-a)=b-m by omega] at hch
 have hchr:(Nat.choose (b-a) (m-a):ℚ)*(((m-a).factorial:ℚ)*((b-m).factorial:ℚ)) =
   ((b-a).factorial:ℚ):=by
  have:(Nat.choose (b-a) (m-a):ℚ)*((m-a).factorial:ℚ)*((b-m).factorial:ℚ) =
    ((b-a).factorial:ℚ):=by exact_mod_cast hch
  linarith
 have hsign:(-1:ℚ)^(m-a)*(-1:ℚ)^(m-a)=1:=by
  rw [← pow_add,← two_mul,pow_mul];norm_num
 calc
  ((b-a).factorial:ℚ)
   = (Nat.choose (b-a) (m-a):ℚ)*(((m-a).factorial:ℚ)*((b-m).factorial:ℚ)):=hchr.symm
  _=((-1:ℚ)^(m-a)*(-1:ℚ)^(m-a)) *
    ((Nat.choose (b-a) (m-a):ℚ)*(((m-a).factorial:ℚ)*((b-m).factorial:ℚ))):=by
    rw [hsign,one_mul]
  _=(-1:ℚ)^(m-a)*(Nat.choose (b-a) (m-a):ℚ) *
    ((-1:ℚ)^(m-a)*(((m-a).factorial:ℚ)*((b-m).factorial:ℚ))):=by ring
private lemma z197 {a b m D:ℕ} (ham:a ≤ m) (hmb:m ≤ b)
  (hba:b-a ≤ D) :
  z199 (Nat.lcmUpto D) 0 (z195 a b m):=by
 rw [z196 ham hmb]
 have hscale:((-1:ℚ)^(m-a)*(Nat.choose (b-a) (m-a):ℚ)) =
   ((((-1:ℤ)^(m-a)*(Nat.choose (b-a) (m-a):ℤ)):ℤ):ℚ):=by push_cast;rfl
 rw [hscale]
 refine z201 _ ?_
 have h0:∑ _r∈(Finset.Icc a b).erase m,(0:ℕ)=0:=by simp
 rw [← h0]
 refine z207 _ (fun _=>0) _ fun r hr=>?_
 rcases Finset.mem_erase.mp hr with ⟨hne,hrIcc⟩
 rcases Finset.mem_Icc.mp hrIcc with ⟨hra,hrb⟩
 intro d
 unfold z238 z208
 have hrm_ne:((r:ℤ)-(m:ℤ))≠0:=by omega
 have hrm_abs_pos:0< ((r:ℤ)-(m:ℤ)).natAbs:=Int.natAbs_pos.mpr hrm_ne
 have hrm_abs_le:((r:ℤ)-(m:ℤ)).natAbs ≤ D:=by omega
 have hrmq:(r:ℚ)-(m:ℚ)=(((r:ℤ)-(m:ℤ):ℤ):ℚ):=by push_cast;rfl
 have hrmq_ne:(r:ℚ)-(m:ℚ)≠0:=by rw [hrmq];exact Int.cast_ne_zero.mpr hrm_ne
 have hsimp:((r:ℚ)-(m:ℚ))*((-1:ℚ)^d/((r:ℚ)-(m:ℚ))^(d+1)) =
   (((-1:ℤ)^d:ℤ):ℚ)*(1/(((r:ℤ)-(m:ℤ):ℤ):ℚ))^d:=by
  rw [pow_succ,one_div_pow,hrmq];push_cast
  field_simp [show (((r:ℤ)-(m:ℤ):ℤ):ℚ)≠0 from Int.cast_ne_zero.mpr hrm_ne]
 rw [hsimp,add_zero]
 refine z60 ((-1:ℤ)^d) ?_
 have hbase:=z64 hrm_ne (z130 hrm_abs_pos hrm_abs_le)
 have hpow:∀ k:ℕ,z56 ((Nat.lcmUpto D)^k) ((1/(((r:ℤ)-(m:ℤ):ℤ):ℚ))^k):=by
  intro k;induction k with
  | zero=>simpa using z62 1
  | succ k ih=>rw [pow_succ,pow_succ];exact z61 ih hbase
 exact hpow d
private lemma z198 {p a b m:ℕ} [Fact p.Prime] (ham:a ≤ m) (hmb:m ≤ b)
  (hlt:b-a< p*p) :
  z221 p (⌊((b-a:ℕ):ℝ)/p⌋ - ⌊((m:ℝ)-(a:ℝ))/p⌋ - ⌊((b:ℝ)-(m:ℝ))/p⌋)
   (z195 a b m):=by
 rw [z196 ham hmb]
 have hch_val:z147 p
   (⌊((b-a:ℕ):ℝ)/p⌋ - ⌊((m:ℝ)-(a:ℝ))/p⌋ - ⌊((b:ℝ)-(m:ℝ))/p⌋)
   ((-1:ℚ)^(m-a)*(Nat.choose (b-a) (m-a):ℚ)):=by
  have hsign:z147 p 0 ((-1:ℚ)^(m-a)):=by
   have:((-1:ℚ)^(m-a))=(((-1:ℤ)^(m-a):ℤ):ℚ):=by push_cast;rfl
   rw [this];exact z149 p _
  have hch:z147 p
    (⌊((b-a:ℕ):ℝ)/p⌋ - ⌊((m-a:ℕ):ℝ)/p⌋ - ⌊((b-m:ℕ):ℝ)/p⌋)
    (Nat.choose (b-a) (m-a):ℚ):=by
   have hch_eq:(Nat.choose (b-a) (m-a):ℚ) =
     ((b-a).factorial:ℚ)/(((m-a).factorial:ℚ)*((b-m).factorial:ℚ)):=by
    have h:=Nat.choose_mul_factorial_mul_factorial (show m-a ≤ b-a by omega)
    rw [show b-a-(m-a)=b-m by omega] at h
    have hr:(Nat.choose (b-a) (m-a):ℚ)*((m-a).factorial:ℚ)*((b-m).factorial:ℚ) =
      ((b-a).factorial:ℚ):=by exact_mod_cast h
    have hf1:((m-a).factorial:ℚ)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hf2:((b-m).factorial:ℚ)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hf1,hf2];linarith
   right
   rw [hch_eq,padicValRat.div (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
     (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))),
    padicValRat.mul (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
     (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
    padicValRat.of_nat,padicValRat.of_nat,padicValRat.of_nat,
    z159 hlt,
    z159 (by omega),
    z159 (by omega),
    z129,z129,z129]
   omega
  have hmul:=z152 hsign hch
  rw [zero_add,Nat.cast_sub ham,Nat.cast_sub hmb] at hmul
  exact hmul
 have hprod:z221 p 0
   (z230 ((Finset.Icc a b).erase m)
    (fun r=>z238 ((r:ℚ)-(m:ℚ)) (z208 ((r:ℚ)-(m:ℚ))))):=by
  have h0:∑ _r∈(Finset.Icc a b).erase m,(0:ℤ)=0:=by simp
  rw [← h0]
  refine z228 _ (fun _=>0) _ fun r hr=>?_
  rcases Finset.mem_erase.mp hr with ⟨hne,hrIcc⟩
  rcases Finset.mem_Icc.mp hrIcc with ⟨hra,hrb⟩
  have hrmq:(r:ℚ)-(m:ℚ)=(((r:ℤ)-(m:ℤ):ℤ):ℚ):=by push_cast;rfl
  rw [hrmq]
  exact z225 (by omega) (by omega)
 simpa using z229 hch_val hprod
private lemma z192 {a b m:ℕ} (hab:a ≤ b) (hm:m∉Finset.Icc a b) :
  z191 a b m=fun d =>
   ∑ r∈Finset.Icc a b,
    (-1:ℚ)^(r-a)*(Nat.choose (b-a) (r-a):ℚ)*z208 ((r:ℚ)-(m:ℚ)) d:=by
 let Q:Polynomial ℚ:=∏ r∈Finset.Icc a b,(X+C ((r:ℚ)-(m:ℚ)))
 let Qinv:PS:=z230 (Finset.Icc a b) (fun r=>z208 ((r:ℚ)-(m:ℚ)))
 have hQQinv:psMul (toPS Q) Qinv=psOne:=by
  rw [z278,← z234]
  have h1:∀ r∈Finset.Icc a b,
    psMul (toPS (X+C ((r:ℚ)-(m:ℚ)))) (z208 ((r:ℚ)-(m:ℚ)))=psOne:=by
   intro r hr
   have hne:(r:ℚ)-(m:ℚ)≠0:=by
    intro heq
    have:r=m:=by exact_mod_cast sub_eq_zero.mp heq
    exact hm (this ▸ hr)
   exact z215 hne
  rw [z231 rfl _ _ h1,z235]
 let RHS_poly:Polynomial ℚ:=
  ∑ r∈Finset.Icc a b,
   C ((-1:ℚ)^(r-a)*(Nat.choose (b-a) (r-a):ℚ)) *
    (∏ j∈(Finset.Icc a b).erase r,(X+C ((j:ℚ)-(m:ℚ))))
 have hpoly_eq:C (((b-a).factorial:ℚ))=RHS_poly:=by
  have hdeg_rhs:RHS_poly.natDegree ≤ b-a:=by
   have hsum_le:∀ (s:Finset ℕ) (f:ℕ→ Polynomial ℚ) (N:ℕ),
     (∀ r∈s,(f r).natDegree ≤ N)→ (∑ r∈s,f r).natDegree ≤ N:=by
    intro s f N hf
    induction s using Finset.induction with
    | empty=>simp
    | insert x s hx ih =>
     rw [Finset.sum_insert hx]
     exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (hf x (Finset.mem_insert_self x s)) (ih fun r hr=>hf r (Finset.mem_insert_of_mem hr)))
   refine hsum_le (Finset.Icc a b)
    (fun r=>C ((-1:ℚ)^(r-a)*(Nat.choose (b-a) (r-a):ℚ)) *
     ∏ j∈(Finset.Icc a b).erase r,(X+C ((j:ℚ)-(m:ℚ)))) (b-a) fun r hr=>?_
   refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
   refine (Polynomial.natDegree_prod_le _ _).trans ?_
   calc
    ∑ j∈(Finset.Icc a b).erase r,(X+C ((j:ℚ)-(m:ℚ))).natDegree
     = ∑ _j∈(Finset.Icc a b).erase r,1:=Finset.sum_congr rfl fun j _ =>
      Polynomial.natDegree_X_add_C _
    _=((Finset.Icc a b).erase r).card:=by simp
    _ ≤ b-a:=by rw [Finset.card_erase_of_mem hr,Nat.card_Icc];omega
  have heval:∀ r0∈Finset.Icc a b,
    RHS_poly.eval ((m:ℚ)-(r0:ℚ))=((b-a).factorial:ℚ):=by
   intro r0 hr0
   simp only [RHS_poly,Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_prod,Polynomial.eval_add,Polynomial.eval_X]
   rw [Finset.sum_eq_single r0]
   ·
    have hprod:(∏ j∈(Finset.Icc a b).erase r0,((m:ℚ)-(r0:ℚ)+((j:ℚ)-(m:ℚ)))) =
      ∏ j∈(Finset.Icc a b).erase r0,((j:ℚ)-(r0:ℚ)):=
     Finset.prod_congr rfl fun j _=>by ring
    rw [hprod,z186 (Finset.mem_Icc.mp hr0).1 (Finset.mem_Icc.mp hr0).2]
    have hch:=Nat.choose_mul_factorial_mul_factorial
     (show r0-a ≤ b-a by have:=Finset.mem_Icc.mp hr0;omega)
    rw [show b-a-(r0-a)=b-r0 by have:=Finset.mem_Icc.mp hr0;omega] at hch
    have hchr:(Nat.choose (b-a) (r0-a):ℚ) *
      (((r0-a).factorial:ℚ)*((b-r0).factorial:ℚ))=((b-a).factorial:ℚ):=by
     have:(Nat.choose (b-a) (r0-a):ℚ)*((r0-a).factorial:ℚ)*((b-r0).factorial:ℚ) =
       ((b-a).factorial:ℚ):=by exact_mod_cast hch
     linarith
    have hsign:(-1:ℚ)^(r0-a)*(-1:ℚ)^(r0-a)=1:=by
     rw [← pow_add,← two_mul,pow_mul];norm_num
    calc
     (-1:ℚ)^(r0-a)*(Nat.choose (b-a) (r0-a):ℚ) *
       ((-1:ℚ)^(r0-a)*(((r0-a).factorial:ℚ)*((b-r0).factorial:ℚ)))
      = ((-1:ℚ)^(r0-a)*(-1:ℚ)^(r0-a)) *
       ((Nat.choose (b-a) (r0-a):ℚ) *
        (((r0-a).factorial:ℚ)*((b-r0).factorial:ℚ))):=by ring
     _=((b-a).factorial:ℚ):=by rw [hsign,one_mul,hchr]
   ·
    intro r hr hne
    have hr0_mem:r0∈(Finset.Icc a b).erase r:=Finset.mem_erase.mpr ⟨Ne.symm hne,hr0⟩
    have hzero:(∏ j∈(Finset.Icc a b).erase r,((m:ℚ)-(r0:ℚ)+((j:ℚ)-(m:ℚ))))=0:=
     Finset.prod_eq_zero hr0_mem (by ring)
    rw [hzero,mul_zero]
   ·
    intro h;exact (h hr0).elim
  by_contra hne
  have hdiff:C (((b-a).factorial:ℚ))-RHS_poly≠0:=sub_ne_zero.mpr hne
  have hdeg_diff:(C (((b-a).factorial:ℚ))-RHS_poly).natDegree ≤ b-a:=
   (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) hdeg_rhs)
  have hroots:((Finset.Icc a b).val.map (fun r:ℕ=>(m:ℚ)-(r:ℚ))) ⊆
    (C (((b-a).factorial:ℚ))-RHS_poly).roots:=by
   intro x hx
   rcases Multiset.mem_map.mp hx with ⟨r,hr,rfl⟩
   rw [Polynomial.mem_roots hdiff,Polynomial.IsRoot,Polynomial.eval_sub,Polynomial.eval_C,
    heval r hr,sub_self]
  have hnd:((Finset.Icc a b).val.map (fun r:ℕ=>(m:ℚ)-(r:ℚ))).Nodup:=
   (Finset.Icc a b).nodup.map (fun r1 r2 h=>by
    have:(r1:ℚ)=(r2:ℚ):=by linarith
    exact Nat.cast_injective this)
  have hle:=Multiset.card_le_card (Multiset.le_iff_subset hnd |>.mpr hroots)
  have hcard:=Polynomial.card_roots' (C (((b-a).factorial:ℚ))-RHS_poly)
  simp only [Multiset.card_map,Finset.card_val,Nat.card_Icc] at hle
  omega
 have hps:=congr_arg (fun p=>psMul Qinv (toPS p)) hpoly_eq
 have hLHS:psMul Qinv (toPS (C (((b-a).factorial:ℚ))))=z191 a b m:=by
  rw [z272,z241,z213];rfl
 rw [hLHS] at hps
 rw [hps]
 rw [z279,z214]
 funext d
 refine Finset.sum_congr rfl fun r hr=>?_
 rw [z273,z241]
 unfold z238
 congr 1
 have hQinv_split:Qinv=psMul (z208 ((r:ℚ)-(m:ℚ)))
   (z230 ((Finset.Icc a b).erase r) (fun j=>z208 ((j:ℚ)-(m:ℚ)))):=by
  unfold Qinv
  conv_lhs=>rw [← Finset.insert_erase hr]
  rw [z233 (Finset.notMem_erase r _)]
 have hcancel:psMul (z230 ((Finset.Icc a b).erase r) (fun j=>z208 ((j:ℚ)-(m:ℚ))))
   (toPS (∏ j∈(Finset.Icc a b).erase r,(X+C ((j:ℚ)-(m:ℚ)))))=psOne:=by
  rw [z278,z212,← z234]
  have h1:∀ j∈(Finset.Icc a b).erase r,
    psMul (toPS (X+C ((j:ℚ)-(m:ℚ)))) (z208 ((j:ℚ)-(m:ℚ)))=psOne:=by
   intro j hj
   have hj_mem:j∈Finset.Icc a b:=(Finset.mem_erase.mp hj).2
   have hne:(j:ℚ)-(m:ℚ)≠0:=by
    intro heq
    have:j=m:=by exact_mod_cast sub_eq_zero.mp heq
    exact hm (this ▸ hj_mem)
   exact z215 hne
  rw [z231 rfl _ _ h1,z235]
 rw [hQinv_split,z211,hcancel,z213]
private lemma z193 {a b m D:ℕ} (hab:a ≤ b) (hm:m∉Finset.Icc a b)
  (hdist:∀ r∈Finset.Icc a b,((r:ℤ)-(m:ℤ)).natAbs ≤ D) :
  z199 (Nat.lcmUpto D) 1 (z191 a b m):=by
 rw [z192 hab hm]
 intro d
 refine z66 fun r hr=>?_
 have hne:((r:ℤ)-(m:ℤ))≠0:=by
  intro heq
  have:r=m:=by omega
  exact hm (this ▸ hr)
 have hscale:((-1:ℚ)^(r-a)*(Nat.choose (b-a) (r-a):ℚ)) =
   ((((-1:ℤ)^(r-a)*(Nat.choose (b-a) (r-a):ℤ)):ℤ):ℚ):=by push_cast;rfl
 have hrmq:(r:ℚ)-(m:ℚ)=(((r:ℤ)-(m:ℤ):ℤ):ℚ):=by push_cast;rfl
 rw [hscale,hrmq]
 exact z60 _ (z202 hne
  (z130 (Int.natAbs_pos.mpr hne) (hdist r hr)) d)
private lemma z194 {p a b m:ℕ} [hp:Fact p.Prime] (hab:a ≤ b)
  (hm:m∉Finset.Icc a b) (hlt_L:b-a< p*p)
  (hlt_dist:∀ r∈Finset.Icc a b,((r:ℤ)-(m:ℤ)).natAbs< p*p) :
  z221 p
   (⌊((b-a:ℕ):ℝ)/p⌋ - ⌊((m:ℝ)-(a:ℝ))/p⌋ - ⌊((b:ℝ)-(m:ℝ))/p⌋ - 1)
   (z191 a b m):=by
 have hfactor:z191 a b m =
   z238 (((b-a).factorial:ℚ)/(∏ r∈Finset.Icc a b,((r:ℚ)-(m:ℚ))))
    (z230 (Finset.Icc a b)
     (fun r=>z238 ((r:ℚ)-(m:ℚ)) (z208 ((r:ℚ)-(m:ℚ))))):=by
  unfold z191
  rw [z236,z239]
  congr 1
  have hprod_ne:(∏ r∈Finset.Icc a b,((r:ℚ)-(m:ℚ)))≠0:=by
   refine Finset.prod_ne_zero_iff.mpr fun r hr=>?_
   intro heq
   have:r=m:=by exact_mod_cast sub_eq_zero.mp heq
   exact hm (this ▸ hr)
  field_simp [hprod_ne]
 rw [hfactor]
 have hprod:z221 p 0
   (z230 (Finset.Icc a b)
    (fun r=>z238 ((r:ℚ)-(m:ℚ)) (z208 ((r:ℚ)-(m:ℚ))))):=by
  have h0:∑ _r∈Finset.Icc a b,(0:ℤ)=0:=by simp
  rw [← h0]
  refine z228 _ (fun _=>0) _ fun r hr=>?_
  have hne:((r:ℤ)-(m:ℤ))≠0:=by
   intro heq
   have hrm:r=m:=by omega
   subst hrm;exact hm hr
  have hrmq:(r:ℚ)-(m:ℚ)=(((r:ℤ)-(m:ℤ):ℤ):ℚ):=by push_cast;rfl
  rw [hrmq]
  exact z225 hne (hlt_dist r hr)
 have hscalar:z147 p
   (⌊((b-a:ℕ):ℝ)/p⌋ - ⌊((m:ℝ)-(a:ℝ))/p⌋ - ⌊((b:ℝ)-(m:ℝ))/p⌋ - 1)
   (((b-a).factorial:ℚ)/(∏ r∈Finset.Icc a b,((r:ℚ)-(m:ℚ)))):=by
  have hcases:m< a∨b< m:=by
   simp only [Finset.mem_Icc,not_and_or,not_le] at hm
   exact hm
  rcases hcases with hlt_m | hgt_m
  ·
   have hprod_eq:(∏ r∈Finset.Icc a b,((r:ℚ)-(m:ℚ))) =
     ((b-m).factorial:ℚ)/((a-1-m).factorial:ℚ):=by
    have hbij:(∏ r∈Finset.Icc a b,((r:ℚ)-(m:ℚ))) =
      ∏ j∈Finset.Icc (a-m) (b-m),(j:ℚ):=by
     refine Finset.prod_bij (fun r _=>r-m) ?_ ?_ ?_ ?_
     ·
      intro r hr;simp only [Finset.mem_Icc] at hr ⊢;omega
     ·
      intro r1 hr1 r2 hr2 h;simp only [Finset.mem_Icc] at hr1 hr2;omega
     ·
      intro j hj;simp only [Finset.mem_Icc] at hj
      exact ⟨j+m,Finset.mem_Icc.mpr (by omega),by omega⟩
     ·
      intro r hr;rw [Nat.cast_sub (by have:=(Finset.mem_Icc.mp hr).1;omega)]
    rw [hbij]
    have hmul:(∏ j∈Finset.Icc 1 (a-1-m),(j:ℚ)) *
      (∏ j∈Finset.Icc (a-m) (b-m),(j:ℚ)) =
      ∏ j∈Finset.Icc 1 (b-m),(j:ℚ):=by
     rw [← Finset.prod_union]
     ·
      congr 1;ext j;simp only [Finset.mem_union,Finset.mem_Icc];omega
     ·
      rw [Finset.disjoint_left];intro j h1 h2;simp only [Finset.mem_Icc] at h1 h2;omega
    have hfac:∀ N:ℕ,(∏ j∈Finset.Icc 1 N,(j:ℚ))=(N.factorial:ℚ):=by
     intro N;induction N with
     | zero=>simp
     | succ k ih =>
      rw [Finset.prod_Icc_succ_top (by omega:1 ≤ k+1),ih,Nat.factorial_succ,Nat.cast_mul]
      ring
    rw [hfac,hfac] at hmul
    have hne:((a-1-m).factorial:ℚ)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hne];linarith
   have hbm_lt:b-m< p*p:=by
    have hb:=hlt_dist b (Finset.mem_Icc.mpr ⟨hab,le_rfl⟩)
    omega
   rw [hprod_eq,div_div_eq_mul_div]
   right
   rw [padicValRat.div
     (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
     (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
    padicValRat.mul (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
     (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
    padicValRat.of_nat,padicValRat.of_nat,padicValRat.of_nat,
    z159 hlt_L,
    z159 (by omega:a-1-m< p*p),
    z159 hbm_lt,
    z129 (b-a) p,
    z129 (b-m) p,
    Nat.cast_sub (by omega:m ≤ b)]
   have hsub1:=z84 (A:=a-m) (p:=p) (by omega) hp.out.pos
   rw [show a-m-1=a-1-m by omega,Nat.cast_sub (by omega:m ≤ a)] at hsub1
   have hneg:-((a:ℝ)-(m:ℝ))=(m:ℝ)-(a:ℝ):=by ring
   rw [hneg] at hsub1
   omega
  ·
   have hprod_eq:(∏ r∈Finset.Icc a b,((r:ℚ)-(m:ℚ))) =
     (-1:ℚ)^(b-a+1)*(((m-a).factorial:ℚ)/((m-1-b).factorial:ℚ)):=by
    have hbij:(∏ r∈Finset.Icc a b,((r:ℚ)-(m:ℚ))) =
      ∏ j∈Finset.Icc (m-b) (m-a),(-(j:ℚ)):=by
     refine Finset.prod_bij (fun r _=>m-r) ?_ ?_ ?_ ?_
     ·
      intro r hr;simp only [Finset.mem_Icc] at hr ⊢;omega
     ·
      intro r1 hr1 r2 hr2 h;simp only [Finset.mem_Icc] at hr1 hr2;omega
     ·
      intro j hj;simp only [Finset.mem_Icc] at hj
      exact ⟨m-j,Finset.mem_Icc.mpr (by omega),by omega⟩
     ·
      intro r hr
      rw [Nat.cast_sub (by have:=(Finset.mem_Icc.mp hr).2;omega)];ring
    have hneg_eq:(∏ j∈Finset.Icc (m-b) (m-a),-(j:ℚ)) =
      ∏ j∈Finset.Icc (m-b) (m-a),((-1:ℚ)*(j:ℚ)):=
     Finset.prod_congr rfl fun j _=>by ring
    rw [hbij,hneg_eq,Finset.prod_mul_distrib,Finset.prod_const,Nat.card_Icc,
     show m-a+1-(m-b)=b-a+1 by omega]
    congr 1
    have hmul:(∏ j∈Finset.Icc 1 (m-1-b),(j:ℚ)) *
      (∏ j∈Finset.Icc (m-b) (m-a),(j:ℚ)) =
      ∏ j∈Finset.Icc 1 (m-a),(j:ℚ):=by
     rw [← Finset.prod_union]
     ·
      congr 1;ext j;simp only [Finset.mem_union,Finset.mem_Icc];omega
     ·
      rw [Finset.disjoint_left];intro j h1 h2;simp only [Finset.mem_Icc] at h1 h2;omega
    have hfac:∀ N:ℕ,(∏ j∈Finset.Icc 1 N,(j:ℚ))=(N.factorial:ℚ):=by
     intro N;induction N with
     | zero=>simp
     | succ k ih =>
      rw [Finset.prod_Icc_succ_top (by omega:1 ≤ k+1),ih,Nat.factorial_succ,Nat.cast_mul]
      ring
    rw [hfac,hfac] at hmul
    have hne:((m-1-b).factorial:ℚ)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hne];linarith
   have hma_lt:m-a< p*p:=by
    have ha:=hlt_dist a (Finset.mem_Icc.mpr ⟨le_rfl,hab⟩)
    omega
   rw [hprod_eq]
   have hsign_eq:((b-a).factorial:ℚ) /
     ((-1:ℚ)^(b-a+1)*(((m-a).factorial:ℚ)/((m-1-b).factorial:ℚ))) =
     (-1:ℚ)^(b-a+1)*(((b-a).factorial:ℚ)*((m-1-b).factorial:ℚ) /
      ((m-a).factorial:ℚ)):=by
    have hs2:(-1:ℚ)^(b-a+1)*(-1:ℚ)^(b-a+1)=1:=by
     rw [← pow_add,← two_mul,pow_mul];norm_num
    have hsne:(-1:ℚ)^(b-a+1)≠0:=pow_ne_zero _ (by norm_num)
    have hf1:((m-a).factorial:ℚ)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hf2:((m-1-b).factorial:ℚ)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hinv:((-1:ℚ)^(b-a+1))⁻¹=(-1:ℚ)^(b-a+1):=
     inv_eq_of_mul_eq_one_right hs2
    rw [div_mul_eq_div_div,div_div_eq_mul_div,
     div_eq_mul_inv ((b-a).factorial:ℚ) ((-1:ℚ)^(b-a+1)),hinv]
    ring
   rw [hsign_eq]
   have hsign:z147 p 0 ((-1:ℚ)^(b-a+1)):=by
    have:((-1:ℚ)^(b-a+1))=(((-1:ℤ)^(b-a+1):ℤ):ℚ):=by push_cast;rfl
    rw [this];exact z149 p _
   have hval:z147 p
     (⌊((b-a:ℕ):ℝ)/p⌋ - ⌊((m:ℝ)-(a:ℝ))/p⌋ - ⌊((b:ℝ)-(m:ℝ))/p⌋ - 1)
     (((b-a).factorial:ℚ)*((m-1-b).factorial:ℚ)/((m-a).factorial:ℚ)):=by
    right
    rw [padicValRat.div
      (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
       (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
     padicValRat.mul (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
     padicValRat.of_nat,padicValRat.of_nat,padicValRat.of_nat,
     z159 hlt_L,
     z159 (by omega:m-1-b< p*p),
     z159 hma_lt,
     z129 (b-a) p,
     z129 (m-a) p,
     Nat.cast_sub (by omega:a ≤ m)]
    have hsub1:=z84 (A:=m-b) (p:=p) (by omega) hp.out.pos
    rw [show m-b-1=m-1-b by omega,Nat.cast_sub (by omega:b ≤ m)] at hsub1
    have hneg:-((m:ℝ)-(b:ℝ))=(b:ℝ)-(m:ℝ):=by ring
    rw [hneg] at hsub1
    omega
   simpa using z152 hsign hval
 simpa using z229 hscalar hprod
def z174 (n m:ℕ):ℕ:=
 ((Finset.Icc 1 10).filter fun u=>(1+u)*n ≤ m∧m ≤ (36-u)*n).card
private lemma z177 (n m:ℕ):z174 n m ≤ 10:=by
 unfold z174
 calc
  ((Finset.Icc 1 10).filter _).card ≤ (Finset.Icc 1 10).card:=Finset.card_filter_le _ _
  _=10:=by decide
private lemma z178 {n m:ℕ} (hlo:2*n ≤ m) (hhi:m ≤ 35*n) :
  1 ≤ z174 n m:=by
 unfold z174
 refine Finset.card_pos.mpr ⟨1,Finset.mem_filter.mpr ⟨by decide,by omega⟩⟩
private lemma z179 {n m:ℕ} (hm:m ≤ 37*n) :
  z174 n (37*n-m)=z174 n m:=by
 unfold z174
 congr 1;ext u
 simp only [Finset.mem_filter,Finset.mem_Icc]
 constructor
 ·
  intro ⟨hu,h1,h2⟩
  have hsum:(1+u)*n+(36-u)*n=37*n:=by rw [← add_mul];congr 1;omega
  exact ⟨hu,by omega,by omega⟩
 ·
  intro ⟨hu,h1,h2⟩
  have hsum:(1+u)*n+(36-u)*n=37*n:=by rw [← add_mul];congr 1;omega
  exact ⟨hu,by omega,by omega⟩
private lemma z176 {n m:ℕ} (h:2 ≤ z174 n m):m ≤ 34*n:=by
 unfold z174 at h
 by_contra! hgt
 have hsub:((Finset.Icc 1 10).filter fun u=>(1+u)*n ≤ m∧m ≤ (36-u)*n) ⊆ {1}:=by
  intro u hu
  rcases Finset.mem_filter.mp hu with ⟨huIcc,_,h2⟩
  rcases Finset.mem_Icc.mp huIcc with ⟨hu1,hu10⟩
  rw [Finset.mem_singleton]
  by_contra hu_ne1
  have hu2:2 ≤ u:=by omega
  have hle:(36-u)*n ≤ 34*n:=Nat.mul_le_mul_right n (by omega)
  omega
 have hle:=Finset.card_le_card hsub
 simp only [Finset.card_singleton] at hle
 omega
private lemma z175 {n m:ℕ} (h:3 ≤ z174 n m):m ≤ 33*n:=by
 unfold z174 at h
 by_contra! hgt
 have hsub:((Finset.Icc 1 10).filter fun u=>(1+u)*n ≤ m∧m ≤ (36-u)*n) ⊆ {1,2}:=by
  intro u hu
  rcases Finset.mem_filter.mp hu with ⟨huIcc,_,h2⟩
  rcases Finset.mem_Icc.mp huIcc with ⟨hu1,hu10⟩
  simp only [Finset.mem_insert,Finset.mem_singleton]
  by_contra hu_ne
  have hu3:3 ≤ u:=by omega
  have hle:(36-u)*n ≤ 33*n:=Nat.mul_le_mul_right n (by omega)
  omega
 have hle:=Finset.card_le_card hsub
 have hcard2:({1,2}:Finset ℕ).card ≤ 2:=by decide
 omega
def z286 (n:ℕ):ℚ:=
 (∏ u∈Finset.Icc 1 10,(((35-2*u)*n).factorial:ℚ)) /
  (((27*n).factorial:ℚ)^6)
noncomputable def z10 (n:ℕ):Polynomial ℚ:=
 C (z286 n) *
  (C ((37*n:ℕ):ℚ)+C 2*X) *
  (∏ m∈Finset.Icc 1 (27*n),(X-C (m:ℚ)))^3 *
  (∏ m∈Finset.Icc (37*n+1) (64*n),(X+C (m:ℚ)))^3
noncomputable def z13 (n:ℕ):Polynomial ℚ:=
 ∏ u∈Finset.Icc 1 10,∏ r∈Finset.Icc ((1+u)*n) ((36-u)*n),(X+C (r:ℚ))
noncomputable def z18 (n m:ℕ):Polynomial ℚ:=
 ∏ u∈Finset.Icc 1 10,∏ r∈(Finset.Icc ((1+u)*n) ((36-u)*n)).erase m,(X+C (r:ℚ))
noncomputable def z243 (n m:ℕ):PS:=
 let psL:PS:=toPS (C (((37*n:ℤ)-2*(m:ℤ):ℤ):ℚ)+C 2*X)
 let psA:PS:=z238 ((-1:ℚ)^(27*n))
  (z216 (toPS (C (((27*n).factorial:ℚ)⁻¹) *
   ∏ r∈Finset.Icc 1 (27*n),(X+C ((m+r:ℕ):ℚ)))))
 let psB:PS:=toPS (C (((27*n).factorial:ℚ)⁻¹) *
  ∏ r∈Finset.Icc 1 (27*n),(X+C ((37*n-m+r:ℕ):ℚ)))
 let psC:PS:=z230 (Finset.Icc 1 10) fun u =>
  if (1+u)*n ≤ m∧m ≤ (36-u)*n then
   z195 ((1+u)*n) ((36-u)*n) m
  else
   z191 ((1+u)*n) ((36-u)*n) m
 psMul psL (psMul (psPow psA 3) (psMul (psPow psB 3) psC))
noncomputable def z32 (n i m:ℕ):ℚ:=
 if 1 ≤ i∧i ≤ z174 n m then
  z243 n m (z174 n m-i)
 else 0
private lemma z14 (n m:ℕ) :
  z13 n=(X+C (m:ℚ))^(z174 n m)*z18 n m:=by
 unfold z13 z18 z174
 have hterm:∀ u∈Finset.Icc 1 10,
   (∏ r∈Finset.Icc ((1+u)*n) ((36-u)*n),(X+C (r:ℚ))) =
   (if (1+u)*n ≤ m∧m ≤ (36-u)*n then (X+C (m:ℚ)) else 1) *
    (∏ r∈(Finset.Icc ((1+u)*n) ((36-u)*n)).erase m,(X+C (r:ℚ))):=by
  intro u _
  split_ifs with hm
  ·
   have hmem:m∈Finset.Icc ((1+u)*n) ((36-u)*n):=Finset.mem_Icc.mpr hm
   rw [← Finset.mul_prod_erase _ _ hmem]
  ·
   have hnot:m∉Finset.Icc ((1+u)*n) ((36-u)*n):=by
    simpa [Finset.mem_Icc] using hm
   rw [Finset.erase_eq_of_notMem hnot,one_mul]
 rw [Finset.prod_congr rfl hterm,Finset.prod_mul_distrib]
 congr 1
 rw [Finset.prod_ite,Finset.prod_const_one,mul_one,Finset.prod_const]
private lemma z15 (n:ℕ) (hn:1 ≤ n) :
  z13 n=∏ m∈Finset.Icc (2*n) (35*n),(X+C (m:ℚ))^(z174 n m):=by
 unfold z13 z174
 have hsub:∀ u∈Finset.Icc 1 10,
   Finset.Icc ((1+u)*n) ((36-u)*n) ⊆ Finset.Icc (2*n) (35*n):=by
  intro u hu r hr
  rcases Finset.mem_Icc.mp hu with ⟨hu1,hu10⟩
  rcases Finset.mem_Icc.mp hr with ⟨hr1,hr2⟩
  refine Finset.mem_Icc.mpr ⟨?_,?_⟩
  ·
   exact le_trans (Nat.mul_le_mul_right n (by omega)) hr1
  ·
   exact le_trans hr2 (Nat.mul_le_mul_right n (by omega))
 have h1:∀ u∈Finset.Icc 1 10,
   (∏ r∈Finset.Icc ((1+u)*n) ((36-u)*n),(X+C (r:ℚ))) =
   ∏ m∈Finset.Icc (2*n) (35*n),
    if (1+u)*n ≤ m∧m ≤ (36-u)*n then (X+C (m:ℚ)) else 1:=by
  intro u hu
  rw [Finset.prod_ite,Finset.prod_const_one,mul_one]
  congr 1;ext m
  simp only [Finset.mem_filter,Finset.mem_Icc]
  constructor
  ·
   intro hm;exact ⟨⟨le_trans (Nat.mul_le_mul_right n (by have:=(Finset.mem_Icc.mp hu).1;omega)) hm.1,
    le_trans hm.2 (Nat.mul_le_mul_right n (by have:=(Finset.mem_Icc.mp hu).1;omega))⟩,hm⟩
  ·
   intro ⟨_,hm⟩;exact hm
 rw [Finset.prod_congr rfl h1,Finset.prod_comm]
 refine Finset.prod_congr rfl fun m _=>?_
 rw [Finset.prod_ite,Finset.prod_const_one,mul_one,Finset.prod_const]
private lemma z16 (n:ℕ):(z13 n).Monic:=by
 unfold z13
 exact Polynomial.monic_prod_of_monic _ _ fun u _ =>
  Polynomial.monic_prod_of_monic _ _ fun r _=>Polynomial.monic_X_add_C _
private lemma z19 (n m:ℕ):(z18 n m).Monic:=by
 unfold z18
 exact Polynomial.monic_prod_of_monic _ _ fun u _ =>
  Polynomial.monic_prod_of_monic _ _ fun r _=>Polynomial.monic_X_add_C _
private lemma z17 (n:ℕ) (hn:1 ≤ n) :
  (z13 n).natDegree=240*n+10:=by
 unfold z13
 rw [Polynomial.natDegree_prod_of_monic _ _ (fun u _ =>
  Polynomial.monic_prod_of_monic _ _ fun r _=>Polynomial.monic_X_add_C _)]
 have hinner:∀ u∈Finset.Icc 1 10,
   (∏ r∈Finset.Icc ((1+u)*n) ((36-u)*n),(X+C (r:ℚ))).natDegree =
    (35-2*u)*n+1:=by
  intro u hu
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun r _=>Polynomial.monic_X_add_C _)]
  simp only [Polynomial.natDegree_X_add_C,Finset.sum_const,smul_eq_mul,mul_one,Nat.card_Icc]
  have hu1:=(Finset.mem_Icc.mp hu).1
  have hu10:=(Finset.mem_Icc.mp hu).2
  have h1:(1+u)*n ≤ (36-u)*n:=Nat.mul_le_mul_right n (by omega)
  have h2:(36-u)*n-(1+u)*n=(35-2*u)*n:=by
   rw [← Nat.sub_mul];congr 1;omega
  omega
 rw [Finset.sum_congr rfl hinner]
 rw [Finset.sum_Icc_succ_top (by omega:1 ≤ 10),Finset.sum_Icc_succ_top (by omega:1 ≤ 9),
  Finset.sum_Icc_succ_top (by omega:1 ≤ 8),Finset.sum_Icc_succ_top (by omega:1 ≤ 7),
  Finset.sum_Icc_succ_top (by omega:1 ≤ 6),Finset.sum_Icc_succ_top (by omega:1 ≤ 5),
  Finset.sum_Icc_succ_top (by omega:1 ≤ 4),Finset.sum_Icc_succ_top (by omega:1 ≤ 3),
  Finset.sum_Icc_succ_top (by omega:1 ≤ 2),Finset.Icc_self,Finset.sum_singleton]
 ring
private lemma z20 (n m:ℕ) (hn:1 ≤ n) :
  (z18 n m).natDegree=240*n+10-z174 n m:=by
 have h:=z14 n m
 have h1:(z13 n).natDegree =
   ((X+C (m:ℚ))^(z174 n m)).natDegree+(z18 n m).natDegree:=by
  rw [h,Polynomial.natDegree_mul]
  ·
   exact ((Polynomial.monic_X_add_C _).pow _).ne_zero
  ·
   exact (z19 n m).ne_zero
 rw [z17 n hn,((Polynomial.monic_X_add_C _).natDegree_pow),
  Polynomial.natDegree_X_add_C,mul_one] at h1
 omega
private lemma z12 (n:ℕ) :
  (z10 n).natDegree ≤ 162*n+1:=by
 unfold z10
 refine (Polynomial.natDegree_mul_le).trans ?_
 have hA:((∏ m∈Finset.Icc 1 (27*n),(X-C (m:ℚ)))^3).natDegree ≤ 81*n:=by
  refine (Polynomial.natDegree_pow_le).trans ?_
  have hp:(∏ m∈Finset.Icc 1 (27*n),(X-C (m:ℚ))).natDegree ≤ 27*n:=by
   refine (Polynomial.natDegree_prod_le _ _).trans ?_
   calc
    ∑ m∈Finset.Icc 1 (27*n),(X-C (m:ℚ)).natDegree
     = ∑ _m∈Finset.Icc 1 (27*n),1:=Finset.sum_congr rfl fun m _=>Polynomial.natDegree_X_sub_C _
    _ ≤ 27*n:=by simp
  omega
 have hB:((∏ m∈Finset.Icc (37*n+1) (64*n),(X+C (m:ℚ)))^3).natDegree ≤ 81*n:=by
  refine (Polynomial.natDegree_pow_le).trans ?_
  have hp:(∏ m∈Finset.Icc (37*n+1) (64*n),(X+C (m:ℚ))).natDegree ≤ 27*n:=by
   refine (Polynomial.natDegree_prod_le _ _).trans ?_
   calc
    ∑ m∈Finset.Icc (37*n+1) (64*n),(X+C (m:ℚ)).natDegree
     = ∑ _m∈Finset.Icc (37*n+1) (64*n),1:=Finset.sum_congr rfl fun m _=>Polynomial.natDegree_X_add_C _
    _ ≤ 27*n:=by simp;omega
  omega
 have hL:(C (z286 n)*(C ((37*n:ℕ):ℚ)+C 2*X)).natDegree ≤ 1:=by
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  ·
   rw [Polynomial.natDegree_C];omega
  ·
   exact (Polynomial.natDegree_C_mul_le _ _).trans (by rw [Polynomial.natDegree_X])
 have h12:(C (z286 n)*(C ((37*n:ℕ):ℚ)+C 2*X) *
   (∏ m∈Finset.Icc 1 (27*n),(X-C (m:ℚ)))^3).natDegree ≤ 81*n+1:=
  (Polynomial.natDegree_mul_le).trans (by omega)
 omega
private lemma z209 {n m:ℕ} (hm:m ≤ 35*n) :
  psMul (toPS ((z18 n m).comp (X-C (m:ℚ)))) (z243 n m) =
   toPS ((z10 n).comp (X-C (m:ℚ))):=by
 have hQ_comp:(z18 n m).comp (X-C (m:ℚ)) =
   ∏ u∈Finset.Icc 1 10,
    ∏ r∈(Finset.Icc ((1+u)*n) ((36-u)*n)).erase m,
     (X+C ((r:ℚ)-(m:ℚ))):=by
  unfold z18
  rw [Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun u _=>?_
  rw [Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun r _=>?_
  simp only [Polynomial.add_comp,Polynomial.X_comp,Polynomial.C_comp,map_sub]
  ring
 have hQ_psC:psMul (toPS ((z18 n m).comp (X-C (m:ℚ))))
   (z230 (Finset.Icc 1 10) fun u =>
    if (1+u)*n ≤ m∧m ≤ (36-u)*n then
     z195 ((1+u)*n) ((36-u)*n) m
    else
     z191 ((1+u)*n) ((36-u)*n) m) =
   toPS (C (∏ u∈Finset.Icc 1 10,(((35-2*u)*n).factorial:ℚ))):=by
  rw [hQ_comp,z278,← z234]
  have hu:∀ u∈Finset.Icc 1 10,
    psMul (toPS (∏ r∈(Finset.Icc ((1+u)*n) ((36-u)*n)).erase m,
      (X+C ((r:ℚ)-(m:ℚ)))))
     (if (1+u)*n ≤ m∧m ≤ (36-u)*n then
      z195 ((1+u)*n) ((36-u)*n) m
     else
      z191 ((1+u)*n) ((36-u)*n) m) =
    z238 ((((35-2*u)*n).factorial:ℚ)) psOne:=by
   intro u hu
   have hdiff:(36-u)*n-(1+u)*n=(35-2*u)*n:=by
    rw [← Nat.sub_mul];congr 1;have:=Finset.mem_Icc.mp hu;omega
   split_ifs with hmem
   ·
    unfold z195
    rw [hdiff,z241,z278,← z234]
    have h1:∀ r∈(Finset.Icc ((1+u)*n) ((36-u)*n)).erase m,
      psMul (toPS (X+C ((r:ℚ)-(m:ℚ)))) (z208 ((r:ℚ)-(m:ℚ)))=psOne:=by
     intro r hr
     have hne:(r:ℚ)-(m:ℚ)≠0:=
      sub_ne_zero.mpr (Nat.cast_injective.ne (Finset.mem_erase.mp hr).1)
     exact z215 hne
    rw [z231 rfl _ _ h1,z235]
   ·
    unfold z191
    have hnot:m∉Finset.Icc ((1+u)*n) ((36-u)*n):=by
     simpa [Finset.mem_Icc] using hmem
    rw [Finset.erase_eq_of_notMem hnot,hdiff,z241,z278,← z234]
    have h1:∀ r∈Finset.Icc ((1+u)*n) ((36-u)*n),
      psMul (toPS (X+C ((r:ℚ)-(m:ℚ)))) (z208 ((r:ℚ)-(m:ℚ)))=psOne:=by
     intro r hr
     have hne:(r:ℚ)-(m:ℚ)≠0:=by
      intro heq;have:r=m:=by exact_mod_cast sub_eq_zero.mp heq
      exact hnot (this ▸ hr)
     exact z215 hne
    rw [z231 rfl _ _ h1,z235]
  rw [z231 rfl _ _ hu,z236,z235,z272]
 have hP_comp:(z10 n).comp (X-C (m:ℚ)) =
   C (∏ u∈Finset.Icc 1 10,(((35-2*u)*n).factorial:ℚ)) *
   (C (((37*n:ℤ)-2*(m:ℤ):ℤ):ℚ)+C 2*X) *
   (C ((-1:ℚ)^(27*n)) *
    (C (((27*n).factorial:ℚ)⁻¹) *
     ∏ r∈Finset.Icc 1 (27*n),(X+C ((m+r:ℕ):ℚ))).comp (-X))^3 *
   (C (((27*n).factorial:ℚ)⁻¹) *
    ∏ r∈Finset.Icc 1 (27*n),(X+C ((37*n-m+r:ℕ):ℚ)))^3:=by
  unfold z10 z286
  simp only [Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.add_comp,Polynomial.C_comp,
   Polynomial.X_comp,Polynomial.prod_comp,Polynomial.sub_comp]
  have hL:C ((37*n:ℕ):ℚ)+C 2*(X-C (m:ℚ)) =
    C (((37*n:ℤ)-2*(m:ℤ):ℤ):ℚ)+C 2*X:=by
   rw [Nat.cast_mul,Nat.cast_ofNat,C_mul]
   simp only [Int.cast_sub,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat,map_sub,map_mul]
   ring
  have hA:(∏ r∈Finset.Icc 1 (27*n),(X-C (m:ℚ)-C (r:ℚ))) =
    C ((-1:ℚ)^(27*n)) *
     (∏ r∈Finset.Icc 1 (27*n),(X+C ((m+r:ℕ):ℚ))).comp (-X):=by
   rw [Polynomial.prod_comp]
   have hstep:∀ r∈Finset.Icc 1 (27*n),
     (X-C (m:ℚ)-C (r:ℚ):Polynomial ℚ) =
      C (-1:ℚ)*((X+C ((m+r:ℕ):ℚ)).comp (-X)):=by
    intro r _
    simp only [Polynomial.add_comp,Polynomial.X_comp,Polynomial.C_comp,Nat.cast_add,map_add,
     map_neg,map_one]
    ring
   rw [Finset.prod_congr rfl hstep,Finset.prod_mul_distrib,Finset.prod_const,
    Nat.card_Icc,show 27*n+1-1=27*n by omega,← C_pow]
  have hB:(∏ r∈Finset.Icc (37*n+1) (64*n),(X-C (m:ℚ)+C (r:ℚ))) =
    ∏ r∈Finset.Icc 1 (27*n),(X+C ((37*n-m+r:ℕ):ℚ)):=by
   refine Finset.prod_bij (fun r _=>r-37*n) ?_ ?_ ?_ ?_
   ·
    intro r hr;simp only [Finset.mem_Icc] at hr ⊢;omega
   ·
    intro r1 hr1 r2 hr2 h;simp only [Finset.mem_Icc] at hr1 hr2;omega
   ·
    intro r hr;simp only [Finset.mem_Icc] at hr
    exact ⟨37*n+r,Finset.mem_Icc.mpr (by omega),by omega⟩
   ·
    intro r hr
    have hr1:37*n+1 ≤ r:=(Finset.mem_Icc.mp hr).1
    have hcast:((37*n-m+(r-37*n):ℕ):ℚ)=(r:ℚ)-(m:ℚ):=by
     have h1:37*n-m+(r-37*n)=r-m:=by omega
     rw [h1,Nat.cast_sub (by omega)]
    rw [hcast,map_sub];ring
  rw [hL,hA,hB]
  have hApoly_comp:(∏ r∈Finset.Icc 1 (27*n),(X+C ((m+r:ℕ):ℚ))).comp (-X) =
    ∏ r∈Finset.Icc 1 (27*n),(-X+C ((m+r:ℕ):ℚ)):=by
   rw [Polynomial.prod_comp]
   refine Finset.prod_congr rfl fun r _=>by simp
  rw [hApoly_comp]
  set F1:=∏ u∈Finset.Icc 1 10,(((35-2*u)*n).factorial:ℚ)
  set F2:=((27*n).factorial:ℚ)
  have hdiv:C (F1/F2^6)=C F1*(C (F2⁻¹))^3*(C (F2⁻¹))^3:=by
   rw [div_eq_mul_inv,← inv_pow,← C_pow,← C_mul,← C_mul]
   congr 1;ring
  rw [hdiv]
  simp only [mul_pow,← C_pow]
  ring
 set qW:=toPS ((z18 n m).comp (X-C (m:ℚ)))
 set pL:=toPS (C (((37*n:ℤ)-2*(m:ℤ):ℤ):ℚ)+C 2*X)
 set pA:=z238 ((-1:ℚ)^(27*n))
  (z216 (toPS (C (((27*n).factorial:ℚ)⁻¹) *
   ∏ r∈Finset.Icc 1 (27*n),(X+C ((m+r:ℕ):ℚ)))))
 set pB:=toPS (C (((27*n).factorial:ℚ)⁻¹) *
  ∏ r∈Finset.Icc 1 (27*n),(X+C ((37*n-m+r:ℕ):ℚ)))
 set pC:=z230 (Finset.Icc 1 10) fun u =>
  if (1+u)*n ≤ m∧m ≤ (36-u)*n then
   z195 ((1+u)*n) ((36-u)*n) m
  else
   z191 ((1+u)*n) ((36-u)*n) m
 set pF:=toPS (C (∏ u∈Finset.Icc 1 10,(((35-2*u)*n).factorial:ℚ)))
 change psMul qW (psMul pL (psMul (psPow pA 3) (psMul (psPow pB 3) pC)))=_
 have hLHS:psMul qW (psMul pL (psMul (psPow pA 3) (psMul (psPow pB 3) pC))) =
   psMul (psMul (psMul pF pL) (psPow pA 3)) (psPow pB 3):=by
  calc
   psMul qW (psMul pL (psMul (psPow pA 3) (psMul (psPow pB 3) pC)))
    = psMul pL (psMul (psPow pA 3) (psMul (psPow pB 3) (psMul qW pC))):=by
     rw [← z211,z212 qW pL,z211,
      ← z211 qW,z212 qW (psPow pA 3),z211,
      ← z211 qW,z212 qW (psPow pB 3),z211]
   _=psMul pL (psMul (psPow pA 3) (psMul (psPow pB 3) pF)):=by rw [hQ_psC]
   _=psMul (psMul (psMul pF pL) (psPow pA 3)) (psPow pB 3):=by
     rw [z212 (psPow pB 3) pF,← z211 (psPow pA 3) pF,
      z212 (psPow pA 3) pF,← z211 pL,← z211 pL,
      z212 pL pF]
 rw [hLHS,hP_comp,z275,z275,z275,z277,z277,z273,
  ← z219]
private lemma z128 {ι : Type*} (s:Finset ι) (f:ι→ Polynomial ℚ) {N:ℕ}
  (hN:0< N) (h:∀ i∈s,(f i).natDegree< N) :
  (∑ i∈s,f i).natDegree< N:=by
 classical
 induction s using Finset.induction with
 | empty=>simpa using hN
 | insert a s ha ih =>
  rw [Finset.sum_insert ha]
  exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
   (max_lt (h a (Finset.mem_insert_self a s)) (ih fun i hi=>h i (Finset.mem_insert_of_mem hi)))
theorem z11 {n:ℕ} (hn:1 ≤ n) :
  z10 n =
   ∑ m∈Finset.Icc (2*n) (35*n),
    ∑ i∈Finset.Icc 1 (z174 n m),
     C (z32 n i m)*(X+C (m:ℚ))^(z174 n m-i)*z18 n m:=by
 let H:Polynomial ℚ:=z10 n -
  ∑ m∈Finset.Icc (2*n) (35*n),
   ∑ i∈Finset.Icc 1 (z174 n m),
    C (z32 n i m)*(X+C (m:ℚ))^(z174 n m-i)*z18 n m
 suffices hH:H=0 by exact sub_eq_zero.mp hH
 have hdeg_H:H.natDegree< (z13 n).natDegree:=by
  rw [z17 n hn]
  have hdeg_P:(z10 n).natDegree< 240*n+10:=by
   have:=z12 n;omega
  have hdeg_sum:(∑ m∈Finset.Icc (2*n) (35*n),
    ∑ i∈Finset.Icc 1 (z174 n m),
     C (z32 n i m)*(X+C (m:ℚ))^(z174 n m-i)*z18 n m).natDegree <
    240*n+10:=by
   refine z128 _ _ (by omega) fun m _=>?_
   refine z128 _ _ (by omega) fun i hi=>?_
   rcases Finset.mem_Icc.mp hi with ⟨hi1,himk⟩
   have h1:(C (z32 n i m)*(X+C (m:ℚ))^(z174 n m-i)*z18 n m).natDegree ≤
     (z174 n m-i)+(z18 n m).natDegree:=by
    refine (Polynomial.natDegree_mul_le).trans ?_
    have h2:(C (z32 n i m)*(X+C (m:ℚ))^(z174 n m-i)).natDegree ≤
      z174 n m-i:=
     (Polynomial.natDegree_C_mul_le _ _).trans (by
      rw [(Polynomial.monic_X_add_C _).natDegree_pow,Polynomial.natDegree_X_add_C,mul_one])
    omega
   rw [z20 n m hn] at h1
   have hmk10:=z177 n m
   omega
  exact lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hdeg_P hdeg_sum)
 have hdvd_Q:z13 n ∣ H:=by
  rw [z15 n hn]
  refine Finset.prod_dvd_of_coprime ?_ ?_
  ·
   intro m1 _ m2 _ hne
   refine IsCoprime.pow ?_
   have hsub:((m1:ℚ)-(m2:ℚ))≠0:=
    sub_ne_zero.mpr (by exact_mod_cast hne)
   refine ⟨C (((m1:ℚ)-(m2:ℚ))⁻¹),-C (((m1:ℚ)-(m2:ℚ))⁻¹),?_⟩
   have h1:C (((m1:ℚ)-(m2:ℚ))⁻¹)*(X+C (m1:ℚ)) +
     -C (((m1:ℚ)-(m2:ℚ))⁻¹)*(X+C (m2:ℚ)) =
     C (((m1:ℚ)-(m2:ℚ))⁻¹*((m1:ℚ)-(m2:ℚ))):=by
    rw [C_mul,map_sub];ring
   rw [h1,inv_mul_cancel₀ hsub,map_one]
  ·
   intro m hm
   have hmlo:=(Finset.mem_Icc.mp hm).1
   have hmhi:=(Finset.mem_Icc.mp hm).2
   have hother:∀ m'∈(Finset.Icc (2*n) (35*n)).erase m,
     (X+C (m:ℚ))^(z174 n m) ∣
      (∑ i∈Finset.Icc 1 (z174 n m'),
       C (z32 n i m')*(X+C (m':ℚ))^(z174 n m'-i)*z18 n m'):=by
    intro m' hm'
    refine Finset.dvd_sum fun i _=>?_
    refine dvd_mul_of_dvd_right ?_ _
    have hne:m≠m':=Ne.symm (Finset.mem_erase.mp hm').1
    have hmul:(X+C (m':ℚ))^(z174 n m')*z18 n m'=z13 n:=
     (z14 n m').symm
    have hdvd_prod:(X+C (m:ℚ))^(z174 n m) ∣ z13 n:=by
     rw [z14 n m];exact dvd_mul_right _ _
    rw [← hmul] at hdvd_prod
    have hcop:IsCoprime ((X+C (m:ℚ))^(z174 n m)) ((X+C (m':ℚ))^(z174 n m')):=by
     refine IsCoprime.pow ?_
     have hsub:((m:ℚ)-(m':ℚ))≠0:=sub_ne_zero.mpr (by exact_mod_cast hne)
     refine ⟨C (((m:ℚ)-(m':ℚ))⁻¹),-C (((m:ℚ)-(m':ℚ))⁻¹),?_⟩
     have h1:C (((m:ℚ)-(m':ℚ))⁻¹)*(X+C (m:ℚ)) +
       -C (((m:ℚ)-(m':ℚ))⁻¹)*(X+C (m':ℚ)) =
       C (((m:ℚ)-(m':ℚ))⁻¹*((m:ℚ)-(m':ℚ))):=by
      rw [C_mul,map_sub];ring
     rw [h1,inv_mul_cancel₀ hsub,map_one]
    exact hcop.dvd_of_dvd_mul_left hdvd_prod
   have hH_split:H=(z10 n -
     (∑ i∈Finset.Icc 1 (z174 n m),
      C (z32 n i m)*(X+C (m:ℚ))^(z174 n m-i)*z18 n m)) -
     ∑ m'∈(Finset.Icc (2*n) (35*n)).erase m,
      ∑ i∈Finset.Icc 1 (z174 n m'),
       C (z32 n i m')*(X+C (m':ℚ))^(z174 n m'-i)*z18 n m':=by
    dsimp only [H]
    rw [← Finset.add_sum_erase _ _ hm]
    ring
   rw [hH_split]
   refine dvd_sub ?_ (Finset.dvd_sum hother)
   set Dpoly:Polynomial ℚ:=z10 n -
    ∑ i∈Finset.Icc 1 (z174 n m),
     C (z32 n i m)*(X+C (m:ℚ))^(z174 n m-i)*z18 n m
   have hX_dvd:X^(z174 n m) ∣ Dpoly.comp (X-C (m:ℚ)):=by
    refine z26 fun d hd=>?_
    have hcomp:Dpoly.comp (X-C (m:ℚ)) =
      (z10 n).comp (X-C (m:ℚ)) -
       (z18 n m).comp (X-C (m:ℚ)) *
        (∑ r∈Finset.range (z174 n m),
         C (z243 n m r)*X^r):=by
     dsimp only [Dpoly]
     rw [Polynomial.sub_comp,Polynomial.sum_comp]
     congr 1
     rw [Finset.mul_sum]
     refine Finset.sum_bij (fun i _=>z174 n m-i) ?_ ?_ ?_ ?_
     ·
      intro i hi;simp only [Finset.mem_Icc] at hi;simp only [Finset.mem_range];omega
     ·
      intro i1 hi1 i2 hi2 h;simp only [Finset.mem_Icc] at hi1 hi2;omega
     ·
      intro r hr;simp only [Finset.mem_range] at hr
      exact ⟨z174 n m-r,Finset.mem_Icc.mpr (by omega),by omega⟩
     ·
      intro i hi
      rcases Finset.mem_Icc.mp hi with ⟨hi1,himk⟩
      simp only [Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.add_comp,
       Polynomial.C_comp,Polynomial.X_comp,sub_add_cancel]
      unfold z32
      rw [if_pos ⟨hi1,himk⟩]
      ring
    rw [hcomp,Polynomial.coeff_sub]
    have hP_coeff:((z10 n).comp (X-C (m:ℚ))).coeff d =
      toPS ((z10 n).comp (X-C (m:ℚ))) d:=rfl
    rw [hP_coeff,← z209 hmhi]
    have hQ_coeff:((z18 n m).comp (X-C (m:ℚ)) *
      ∑ r∈Finset.range (z174 n m),
       C (z243 n m r)*X^r).coeff d =
      psMul (toPS ((z18 n m).comp (X-C (m:ℚ)))) (z243 n m) d:=by
     change toPS ((z18 n m).comp (X-C (m:ℚ)) *
      ∑ r∈Finset.range (z174 n m),C (z243 n m r)*X^r) d=_
     rw [z275]
     unfold psMul toPS
     refine Finset.sum_congr rfl fun r hr=>?_
     have hrd:r ≤ d:=Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
     congr 1
     rw [Polynomial.finsetSum_coeff]
     rw [Finset.sum_eq_single (d-r)]
     ·
      simp [Polynomial.coeff_C_mul_X_pow]
     ·
      intro s hs hne
      simp [Polynomial.coeff_C_mul_X_pow,Ne.symm hne]
     ·
      intro hnot
      exfalso;exact hnot (Finset.mem_range.mpr (by omega))
    rw [hQ_coeff,sub_self]
   rcases hX_dvd with ⟨R,hR⟩
   refine ⟨R.comp (X+C (m:ℚ)),?_⟩
   have hcomp_back:=congr_arg (fun p=>p.comp (X+C (m:ℚ))) hR
   simp only [Polynomial.comp_assoc,Polynomial.sub_comp,Polynomial.X_comp,Polynomial.C_comp,
    add_sub_cancel_right,Polynomial.comp_X,Polynomial.mul_comp,Polynomial.pow_comp] at hcomp_back
   exact hcomp_back
 rcases hdvd_Q with ⟨K,hK⟩
 by_contra hH0
 have hK0:K≠0:=by intro h0;subst h0;simp at hK;exact hH0 hK
 have hQ0:z13 n≠0:=(z16 n).ne_zero
 have hdeg_mul:H.natDegree=(z13 n).natDegree+K.natDegree:=by
  rw [hK,Polynomial.natDegree_mul hQ0 hK0]
 omega
theorem z265 {n:ℕ} (hn:1 ≤ n) :
  ∑ m∈Finset.Icc (2*n) (35*n),z32 n 1 m=0:=by
 have hpf:=z11 hn
 have hcoeff:=congr_arg (fun p=>p.coeff (240*n+9)) hpf
 have hLHS:(z10 n).coeff (240*n+9)=0:=
  Polynomial.coeff_eq_zero_of_natDegree_lt (by have:=z12 n;omega)
 rw [hLHS,Polynomial.finset_sum_coeff] at hcoeff
 have hterm:∀ m∈Finset.Icc (2*n) (35*n),
   (∑ i∈Finset.Icc 1 (z174 n m),
    C (z32 n i m)*(X+C (m:ℚ))^(z174 n m-i)*z18 n m).coeff
     (240*n+9)=z32 n 1 m:=by
  intro m hm
  rw [Polynomial.finset_sum_coeff]
  have hmk_pos:=z178 (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2
  have hmk10:=z177 n m
  rw [Finset.sum_eq_single 1]
  ·
   have hmon:((X+C (m:ℚ))^(z174 n m-1)*z18 n m).Monic:=
    ((Polynomial.monic_X_add_C _).pow _).mul (z19 n m)
   have hdeg:((X+C (m:ℚ))^(z174 n m-1)*z18 n m).natDegree=240*n+9:=by
    rw [Polynomial.natDegree_mul (((Polynomial.monic_X_add_C _).pow _).ne_zero)
     (z19 n m).ne_zero,(Polynomial.monic_X_add_C _).natDegree_pow,
     Polynomial.natDegree_X_add_C,mul_one,z20 n m hn]
    omega
   rw [mul_assoc,Polynomial.coeff_C_mul,← hdeg,Polynomial.coeff_natDegree,hmon.leadingCoeff,
    mul_one]
  ·
   intro i hi hne
   rcases Finset.mem_Icc.mp hi with ⟨hi1,himk⟩
   have hi2:2 ≤ i:=by omega
   refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
   have h1:(C (z32 n i m)*(X+C (m:ℚ))^(z174 n m-i)*z18 n m).natDegree ≤
     (z174 n m-i)+(z18 n m).natDegree:=by
    refine (Polynomial.natDegree_mul_le).trans ?_
    have h2:(C (z32 n i m)*(X+C (m:ℚ))^(z174 n m-i)).natDegree ≤
      z174 n m-i:=
     (Polynomial.natDegree_C_mul_le _ _).trans (by
      rw [(Polynomial.monic_X_add_C _).natDegree_pow,Polynomial.natDegree_X_add_C,mul_one])
    omega
   rw [z20 n m hn] at h1
   omega
  ·
   intro hnot;exfalso;exact hnot (Finset.mem_Icc.mpr ⟨le_rfl,hmk_pos⟩)
 rw [Finset.sum_congr rfl hterm] at hcoeff
 exact hcoeff.symm
theorem z35 {n i m:ℕ} (hlo:2*n ≤ m) (hhi:m ≤ 35*n) :
  z32 n i (37*n-m)=(-1:ℚ)^(i+1)*z32 n i m:=by
 have hm37:m ≤ 37*n:=by omega
 have hmk:z174 n (37*n-m)=z174 n m:=z179 hm37
 unfold z32
 rw [hmk]
 split_ifs with h
 ·
  set m':=37*n-m
  have hP_symm:(z10 n).comp (C (-(37*n:ℕ):ℚ)-X)=-z10 n:=by
   unfold z10
   simp only [Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.add_comp,Polynomial.C_comp,
    Polynomial.X_comp,Polynomial.prod_comp,Polynomial.sub_comp]
   have hL:C ((37*n:ℕ):ℚ)+C 2*(C (-(37*n:ℕ):ℚ)-X) =
     -(C ((37*n:ℕ):ℚ)+C 2*X):=by
    simp only [map_neg,map_ofNat];ring
   have hA:(∏ r∈Finset.Icc 1 (27*n),(C (-(37*n:ℕ):ℚ)-X-C (r:ℚ))) =
     C ((-1:ℚ)^(27*n)) *
      ∏ r∈Finset.Icc (37*n+1) (64*n),(X+C (r:ℚ)):=by
    have hbij:(∏ r∈Finset.Icc 1 (27*n),(C (-(37*n:ℕ):ℚ)-X-C (r:ℚ))) =
      ∏ r∈Finset.Icc (37*n+1) (64*n),(C (-1:ℚ)*(X+C (r:ℚ))):=by
     refine Finset.prod_bij (fun r _=>37*n+r) ?_ ?_ ?_ ?_
     ·
      intro r hr;simp only [Finset.mem_Icc] at hr ⊢;omega
     ·
      intro r1 _ r2 _ h;omega
     ·
      intro r hr;simp only [Finset.mem_Icc] at hr
      exact ⟨r-37*n,Finset.mem_Icc.mpr (by omega),by omega⟩
     ·
      intro r _
      simp only [Nat.cast_add,map_add,map_neg,map_one];ring
    rw [hbij,Finset.prod_mul_distrib,Finset.prod_const,Nat.card_Icc,
     show 64*n+1-(37*n+1)=27*n by omega,← C_pow]
   have hB:(∏ r∈Finset.Icc (37*n+1) (64*n),(C (-(37*n:ℕ):ℚ)-X+C (r:ℚ))) =
     C ((-1:ℚ)^(27*n)) *
      ∏ r∈Finset.Icc 1 (27*n),(X-C (r:ℚ)):=by
    have hbij:(∏ r∈Finset.Icc (37*n+1) (64*n),(C (-(37*n:ℕ):ℚ)-X+C (r:ℚ))) =
      ∏ r∈Finset.Icc 1 (27*n),(C (-1:ℚ)*(X-C (r:ℚ))):=by
     refine Finset.prod_bij (fun r _=>r-37*n) ?_ ?_ ?_ ?_
     ·
      intro r hr;simp only [Finset.mem_Icc] at hr ⊢;omega
     ·
      intro r1 hr1 r2 hr2 h;simp only [Finset.mem_Icc] at hr1 hr2;omega
     ·
      intro r hr;simp only [Finset.mem_Icc] at hr
      exact ⟨37*n+r,Finset.mem_Icc.mpr (by omega),by omega⟩
     ·
      intro r hr
      have hr1:37*n ≤ r:=by have:=(Finset.mem_Icc.mp hr).1;omega
      rw [Nat.cast_sub hr1];simp only [map_sub,map_neg,map_one];ring
    rw [hbij,Finset.prod_mul_distrib,Finset.prod_const,Nat.card_Icc,
     show 27*n+1-1=27*n by omega,← C_pow]
   rw [hL,hA,hB,mul_pow,mul_pow,← C_pow]
   have hsign:((-1:ℚ)^(27*n))^3*((-1:ℚ)^(27*n))^3=1:=by
    rw [← mul_pow,← pow_add,← two_mul,pow_mul];norm_num
   have hC:C (((-1:ℚ)^(27*n))^3)*C (((-1:ℚ)^(27*n))^3)=1:=by
    rw [← C_mul,hsign,map_one]
   linear_combination (C (z286 n)*-(C ((37*n:ℕ):ℚ)+C 2*X) *
    (∏ r∈Finset.Icc 1 (27*n),(X-C (r:ℚ)))^3 *
    (∏ r∈Finset.Icc (37*n+1) (64*n),(X+C (r:ℚ)))^3)*(hC-1)
  have hQ_wo_symm:(z18 n m).comp (C (-(37*n:ℕ):ℚ)-X) =
    C ((-1:ℚ)^(z174 n m))*z18 n m':=by
   unfold z18
   rw [Polynomial.prod_comp]
   have hterm:∀ u∈Finset.Icc 1 10,
     (∏ r∈(Finset.Icc ((1+u)*n) ((36-u)*n)).erase m,(X+C (r:ℚ))).comp
      (C (-(37*n:ℕ):ℚ)-X) =
     C ((-1:ℚ)^((35-2*u)*n+1 -
       (if (1+u)*n ≤ m∧m ≤ (36-u)*n then 1 else 0))) *
      ∏ r∈(Finset.Icc ((1+u)*n) ((36-u)*n)).erase m',(X+C (r:ℚ)):=by
    intro u hu
    have hu1:=(Finset.mem_Icc.mp hu).1
    have hu10:=(Finset.mem_Icc.mp hu).2
    have hsum_u:(1+u)*n+(36-u)*n=37*n:=by
     rw [← add_mul];congr 1;omega
    have hdiff_u:(36-u)*n-(1+u)*n=(35-2*u)*n:=by
     rw [← Nat.sub_mul];congr 1;omega
    have hle_u:(1+u)*n ≤ (36-u)*n:=Nat.mul_le_mul_right n (by omega)
    have hle37_u:(36-u)*n ≤ 37*n:=Nat.mul_le_mul_right n (by omega)
    rw [Polynomial.prod_comp]
    have hbij:(∏ r∈(Finset.Icc ((1+u)*n) ((36-u)*n)).erase m,
       (C (-(37*n:ℕ):ℚ)-X+C (r:ℚ))) =
      ∏ r∈(Finset.Icc ((1+u)*n) ((36-u)*n)).erase m',
       (C (-1:ℚ)*(X+C (r:ℚ))):=by
     refine Finset.prod_bij (fun r _=>37*n-r) ?_ ?_ ?_ ?_
     ·
      intro r hr
      rcases Finset.mem_erase.mp hr with ⟨hne,hrI⟩
      rcases Finset.mem_Icc.mp hrI with ⟨h1,h2⟩
      refine Finset.mem_erase.mpr ⟨by dsimp only [m'];omega,
       Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩
     ·
      intro r1 hr1 r2 hr2 h
      have h1:=(Finset.mem_Icc.mp (Finset.mem_erase.mp hr1).2).2
      have h2:=(Finset.mem_Icc.mp (Finset.mem_erase.mp hr2).2).2
      omega
     ·
      intro r hr
      rcases Finset.mem_erase.mp hr with ⟨hne,hrI⟩
      rcases Finset.mem_Icc.mp hrI with ⟨h1,h2⟩
      refine ⟨37*n-r,Finset.mem_erase.mpr ⟨by dsimp only [m'] at hne;omega,
       Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩,by omega⟩
     ·
      intro r hr
      have hr2:=(Finset.mem_Icc.mp (Finset.mem_erase.mp hr).2).2
      have hle37:r ≤ 37*n:=hr2.trans hle37_u
      rw [Nat.cast_sub hle37];simp only [map_sub,map_neg,map_one];ring
    have hcomp_simp:(∏ r∈(Finset.Icc ((1+u)*n) ((36-u)*n)).erase m,
       (X+C (r:ℚ)).comp (C (-(37*n:ℕ):ℚ)-X)) =
      ∏ r∈(Finset.Icc ((1+u)*n) ((36-u)*n)).erase m,
       (C (-(37*n:ℕ):ℚ)-X+C (r:ℚ)):=
     Finset.prod_congr rfl fun r _=>by simp
    rw [hcomp_simp,hbij,Finset.prod_mul_distrib,Finset.prod_const,← C_pow]
    congr 2
    split_ifs with hcond
    ·
     have hm':m'∈Finset.Icc ((1+u)*n) ((36-u)*n):=
      Finset.mem_Icc.mpr ⟨by dsimp only [m'];omega,by dsimp only [m'];omega⟩
     rw [Finset.card_erase_of_mem hm',Nat.card_Icc,Nat.sub_add_comm hle_u,hdiff_u]
    ·
     have hm':m'∉Finset.Icc ((1+u)*n) ((36-u)*n):=by
      simp only [Finset.mem_Icc];dsimp only [m'];omega
     rw [Finset.erase_eq_of_notMem hm',Nat.card_Icc,Nat.sub_add_comm hle_u,hdiff_u,Nat.sub_zero]
   rw [Finset.prod_congr rfl hterm,Finset.prod_mul_distrib,← map_prod]
   congr 2
   rw [Finset.prod_pow_eq_pow_sum]
   have htot:(∑ u∈Finset.Icc 1 10,((35-2*u)*n+1 -
     (if (1+u)*n ≤ m∧m ≤ (36-u)*n then 1 else 0))) =
     240*n+10-z174 n m:=by
    have h1:∀ u∈Finset.Icc 1 10,
      ((35-2*u)*n+1-(if (1+u)*n ≤ m∧m ≤ (36-u)*n then 1 else 0)) +
       (if (1+u)*n ≤ m∧m ≤ (36-u)*n then 1 else 0) =
      (35-2*u)*n+1:=by
     intro u _;split_ifs <;> omega
    have hadd:=Finset.sum_congr rfl h1
    rw [Finset.sum_add_distrib] at hadd
    have hsum1:∑ u∈Finset.Icc 1 10,((35-2*u)*n+1)=240*n+10:=by
     rw [Finset.sum_Icc_succ_top (by omega:1 ≤ 10),Finset.sum_Icc_succ_top (by omega:1 ≤ 9),
      Finset.sum_Icc_succ_top (by omega:1 ≤ 8),Finset.sum_Icc_succ_top (by omega:1 ≤ 7),
      Finset.sum_Icc_succ_top (by omega:1 ≤ 6),Finset.sum_Icc_succ_top (by omega:1 ≤ 5),
      Finset.sum_Icc_succ_top (by omega:1 ≤ 4),Finset.sum_Icc_succ_top (by omega:1 ≤ 3),
      Finset.sum_Icc_succ_top (by omega:1 ≤ 2),Finset.Icc_self,Finset.sum_singleton]
     ring
    have hsum2:∑ u∈Finset.Icc 1 10,
      (if (1+u)*n ≤ m∧m ≤ (36-u)*n then 1 else 0)=z174 n m:=by
     unfold z174
     rw [Finset.sum_boole,Nat.cast_id]
    omega
   rw [htot]
   have hmk10:=z177 n m
   have heven:Even (240*n+10):=⟨120*n+5,by omega⟩
   have hsub_eq:(-1:ℚ)^(240*n+10-z174 n m)*(-1:ℚ)^(z174 n m)=1:=by
    rw [← pow_add,Nat.sub_add_cancel (by omega:z174 n m ≤ 240*n+10)]
    rcases heven with ⟨k,hk⟩
    rw [hk,← two_mul,pow_mul];norm_num
   have hpow2:(-1:ℚ)^(z174 n m)*(-1:ℚ)^(z174 n m)=1:=by
    rw [← pow_add,← two_mul,pow_mul];norm_num
   linear_combination ((-1:ℚ)^(z174 n m))*hsub_eq -
    ((-1:ℚ)^(240*n+10-z174 n m))*hpow2
  have hps_m:=congr_arg z216 (z209 hhi)
  rw [z217,z219,z219,Polynomial.comp_assoc,Polynomial.comp_assoc] at hps_m
  have hshift:(X-C (m:ℚ)).comp (-X)=(C (-(37*n:ℕ):ℚ)-X).comp (X-C (m':ℚ)):=by
   simp only [Polynomial.sub_comp,Polynomial.X_comp,Polynomial.C_comp,m']
   rw [Nat.cast_sub hm37];simp only [map_sub,map_neg];ring
  rw [hshift,← Polynomial.comp_assoc,← Polynomial.comp_assoc,hP_symm,hQ_wo_symm,
   Polynomial.neg_comp,Polynomial.mul_comp,Polynomial.C_comp,z273,z240] at hps_m
  have hm'_le:m' ≤ 35*n:=by dsimp only [m'];omega
  have hps_m':=z209 hm'_le
  have hneg_toPS:toPS (-(z10 n).comp (X-C (m':ℚ))) =
    z238 (-1:ℚ) (toPS ((z10 n).comp (X-C (m':ℚ)))):=by
   rw [show -(z10 n).comp (X-C (m':ℚ)) =
     C (-1:ℚ)*(z10 n).comp (X-C (m':ℚ)) by simp,z273]
  rw [hneg_toPS,← hps_m'] at hps_m
  let Qinv':PS:=z230 (Finset.Icc 1 10) fun u =>
   z230 ((Finset.Icc ((1+u)*n) ((36-u)*n)).erase m')
    (fun r=>z208 ((r:ℚ)-(m':ℚ)))
  have hQinv'_mul:psMul Qinv' (toPS ((z18 n m').comp (X-C (m':ℚ))))=psOne:=by
   unfold Qinv' z18
   rw [Polynomial.prod_comp,z278,z212,← z234]
   have hu:∀ u∈Finset.Icc 1 10,
     psMul (toPS ((∏ r∈(Finset.Icc ((1+u)*n) ((36-u)*n)).erase m',
       (X+C (r:ℚ))).comp (X-C (m':ℚ))))
      (z230 ((Finset.Icc ((1+u)*n) ((36-u)*n)).erase m')
       (fun r=>z208 ((r:ℚ)-(m':ℚ))))=psOne:=by
    intro u _
    rw [Polynomial.prod_comp,z278,← z234]
    have hr:∀ r∈(Finset.Icc ((1+u)*n) ((36-u)*n)).erase m',
      psMul (toPS ((X+C (r:ℚ)).comp (X-C (m':ℚ))))
       (z208 ((r:ℚ)-(m':ℚ)))=psOne:=by
     intro r hr
     have h1:(X+C (r:ℚ)).comp (X-C (m':ℚ))=X+C ((r:ℚ)-(m':ℚ)):=by
      simp [map_sub];ring
     rw [h1]
     have hne:(r:ℚ)-(m':ℚ)≠0:=by
      have:=(Finset.mem_erase.mp hr).1
      exact sub_ne_zero.mpr (by exact_mod_cast this)
     exact z215 hne
    rw [z231 rfl _ _ hr,z235]
   rw [z231 rfl _ _ hu,z235]
  have hcancel:=congr_arg (fun x=>psMul Qinv' x) hps_m
  rw [z241,z241,← z211,← z211,
   hQinv'_mul,z220,z220] at hcancel
  have hpt:=congr_fun hcancel (z174 n m-i)
  unfold z238 z216 at hpt
  have hexp:(-1:ℚ)^(z174 n m)*(-1:ℚ)^(z174 n m-i)=-((-1:ℚ)^(i+1)):=by
   rw [← pow_add,show z174 n m+(z174 n m-i)=2*(z174 n m-i)+i by omega,
    pow_add,pow_mul,show (-1:ℚ)^2=1 by norm_num,one_pow,one_mul,pow_succ]
   ring
  rw [← mul_assoc,hexp] at hpt
  linarith
 ·
  simp
theorem z264 {n i:ℕ} (heven:Even i) :
  ∑ m∈Finset.Icc (2*n) (35*n),z32 n i m=0:=by
 have hsum:∑ m∈Finset.Icc (2*n) (35*n),z32 n i m =
   ∑ m∈Finset.Icc (2*n) (35*n),z32 n i (37*n-m):=by
  refine Finset.sum_bij (fun m _=>37*n-m) ?_ ?_ ?_ ?_
  ·
   intro m hm;simp only [Finset.mem_Icc] at hm ⊢;omega
  ·
   intro m1 hm1 m2 hm2 h;simp only [Finset.mem_Icc] at hm1 hm2;omega
  ·
   intro m hm;simp only [Finset.mem_Icc] at hm
   exact ⟨37*n-m,Finset.mem_Icc.mpr (by omega),by omega⟩
  ·
   intro m hm
   have hmhi:=(Finset.mem_Icc.mp hm).2
   congr 1;omega
 have hneg:∑ m∈Finset.Icc (2*n) (35*n),z32 n i (37*n-m) =
   -∑ m∈Finset.Icc (2*n) (35*n),z32 n i m:=by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m hm=>?_
  rw [z35 (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2]
  rcases heven with ⟨k,rfl⟩
  have hpow:(-1:ℚ)^(k+k+1)=-1:=by
   rw [pow_succ,← two_mul,pow_mul];norm_num
  rw [hpow];ring
 linarith
noncomputable def z23 (n:ℕ) (z:ℂ):ℂ:=
 ((z286 n:ℚ):ℂ) *
  (((37*n:ℕ):ℂ)+2*z) *
  (∏ m∈Finset.Icc 1 (27*n),(z-(m:ℂ)))^3 *
  (∏ m∈Finset.Icc (37*n+1) (64*n),(z+(m:ℂ)))^3 /
  (∏ u∈Finset.Icc 1 10,∏ r∈Finset.Icc ((1+u)*n) ((36-u)*n),(z+(r:ℂ)))
lemma z24 {n:ℕ} (hn:1 ≤ n) {z:ℂ}
  (hz:∀ m∈Finset.Icc (2*n) (35*n),z+(m:ℂ)≠0) :
  z23 n z =
   ∑ m∈Finset.Icc (2*n) (35*n),∑ i∈Finset.Icc 1 10,
    ((z32 n i m:ℚ):ℂ)*(z+(m:ℂ))⁻¹^i:=by
 have hQne:Polynomial.aeval z (z13 n)≠0:=by
  rw [z15 n hn,map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun m hm=>?_
  rw [map_pow,map_add,Polynomial.aeval_X,Polynomial.aeval_C]
  simpa using pow_ne_zero _ (hz m hm)
 have hP_eval:Polynomial.aeval z (z10 n) =
   ((z286 n:ℚ):ℂ) *
    (((37*n:ℕ):ℂ)+2*z) *
    (∏ m∈Finset.Icc 1 (27*n),(z-(m:ℂ)))^3 *
    (∏ m∈Finset.Icc (37*n+1) (64*n),(z+(m:ℂ)))^3:=by
  unfold z10
  simp [map_mul,map_pow,map_add,map_sub,map_prod]
 have hQ_eval:Polynomial.aeval z (z13 n) =
   ∏ u∈Finset.Icc 1 10,∏ r∈Finset.Icc ((1+u)*n) ((36-u)*n),(z+(r:ℂ)):=by
  unfold z13
  simp [map_prod,map_add]
 unfold z23
 rw [← hP_eval,← hQ_eval,div_eq_iff hQne]
 have hpf:=congr_arg (Polynomial.aeval z) (z11 hn)
 rw [hpf,map_sum,Finset.sum_mul]
 refine Finset.sum_congr rfl fun m hm=>?_
 rw [map_sum,Finset.sum_mul]
 have hmk10:=z177 n m
 have hsplit:∑ i∈Finset.Icc 1 10,
   ((z32 n i m:ℚ):ℂ)*(z+(m:ℂ))⁻¹^i*Polynomial.aeval z (z13 n) =
   ∑ i∈Finset.Icc 1 (z174 n m),
    ((z32 n i m:ℚ):ℂ)*(z+(m:ℂ))⁻¹^i*Polynomial.aeval z (z13 n):=by
  symm
  refine Finset.sum_subset (Finset.Icc_subset_Icc_right hmk10) fun i hi hnot=>?_
  have hci:z32 n i m=0:=by
   unfold z32;rw [if_neg];intro ⟨h1,h2⟩;exact hnot (Finset.mem_Icc.mpr ⟨h1,h2⟩)
  simp [hci]
 rw [hsplit]
 refine Finset.sum_congr rfl fun i hi=>?_
 have himk:=(Finset.mem_Icc.mp hi).2
 have hQ_wo:=congr_arg (Polynomial.aeval z) (z14 n m)
 simp only [map_mul,map_pow,map_add,Polynomial.aeval_X,Polynomial.aeval_C,eq_ratCast,
  Rat.cast_natCast] at hQ_wo ⊢
 rw [hQ_wo]
 have hzm:z+(m:ℂ)≠0:=hz m hm
 have hpow:(z+(m:ℂ))⁻¹^i*(z+(m:ℂ))^(z174 n m) =
   (z+(m:ℂ))^(z174 n m-i):=by
  rw [inv_pow]
  conv_lhs=>rw [← Nat.sub_add_cancel himk]
  rw [pow_add]
  field_simp [pow_ne_zero i hzm]
 linear_combination ((z32 n i m:ℚ):ℂ)*Polynomial.aeval z (z18 n m)*hpow.symm
noncomputable def z21 (n:ℕ) (t:ℝ):ℝ:=
 ∑ m∈Finset.Icc (2*n) (35*n),∑ i∈Finset.Icc (1:ℕ) 10,
  ((i*(i+1):ℕ):ℝ)*((z32 n i m:ℚ):ℝ)/(t+(m:ℝ))^(i+2)
theorem z22 {n k:ℕ} (hn:1 ≤ n) (hk1:1 ≤ k) (hk27:k ≤ 27*n) :
  z21 n (k:ℝ)=0:=by
 let f:ℝ→ ℝ:=fun t =>
  Polynomial.aeval t (z10 n)/Polynomial.aeval t (z13 n)
 let g1:ℝ→ ℝ:=fun t =>
  ∑ m∈Finset.Icc (2*n) (35*n),∑ i∈Finset.Icc (1:ℕ) 10,
   ((z32 n i m:ℚ):ℝ)/(t+(m:ℝ))^i
 let g1':ℝ→ ℝ:=fun t =>
  ∑ m∈Finset.Icc (2*n) (35*n),∑ i∈Finset.Icc (1:ℕ) 10,
   -((i:ℝ)*((z32 n i m:ℚ):ℝ))/(t+(m:ℝ))^(i+1)
 have hQpos:∀ t:ℝ,0< t→ Polynomial.aeval t (z13 n)≠0:=by
  intro t ht
  rw [z15 n hn,map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun m _=>?_
  rw [map_pow,map_add,Polynomial.aeval_X,Polynomial.aeval_C]
  exact pow_ne_zero _ (by simp;positivity)
 have hfg:∀ t:ℝ,0< t→ f t=g1 t:=by
  intro t ht
  have hQne:=hQpos t ht
  dsimp only [f,g1]
  rw [div_eq_iff hQne]
  have hpf:=congr_arg (Polynomial.aeval t) (z11 hn)
  rw [hpf,map_sum,Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm=>?_
  rw [map_sum,Finset.sum_mul]
  have hmk10:=z177 n m
  have hsplit:∑ i∈Finset.Icc (1:ℕ) 10,
    ((z32 n i m:ℚ):ℝ)/(t+(m:ℝ))^i*Polynomial.aeval t (z13 n) =
    ∑ i∈Finset.Icc 1 (z174 n m),
     ((z32 n i m:ℚ):ℝ)/(t+(m:ℝ))^i*Polynomial.aeval t (z13 n):=by
   symm
   refine Finset.sum_subset (Finset.Icc_subset_Icc_right hmk10) fun i hi hnot=>?_
   have hci:z32 n i m=0:=by
    unfold z32;rw [if_neg];intro ⟨h1,h2⟩;exact hnot (Finset.mem_Icc.mpr ⟨h1,h2⟩)
   simp [hci]
  rw [hsplit]
  refine Finset.sum_congr rfl fun i hi=>?_
  have himk:=(Finset.mem_Icc.mp hi).2
  have hQ_wo:=congr_arg (Polynomial.aeval t) (z14 n m)
  simp only [map_mul,map_pow,map_add,Polynomial.aeval_X,Polynomial.aeval_C,eq_ratCast,
   Rat.cast_natCast] at hQ_wo ⊢
  rw [hQ_wo]
  have htm:t+(m:ℝ)≠0:=by positivity
  have hpow:(t+(m:ℝ))^(z174 n m) =
    (t+(m:ℝ))^(z174 n m-i)*(t+(m:ℝ))^i:=by
   rw [← pow_add,Nat.sub_add_cancel himk]
  rw [hpow]
  field_simp [pow_ne_zero i htm]
 have hg1_deriv:∀ t:ℝ,0< t→ HasDerivAt g1 (g1' t) t:=by
  intro t ht
  refine HasDerivAt.fun_sum fun m _=>HasDerivAt.fun_sum fun i _=>?_
  have htm:t+(m:ℝ)≠0:=by positivity
  have h1:HasDerivAt (fun x:ℝ=>(x+(m:ℝ))^i) ((i:ℝ)*(t+(m:ℝ))^(i-1)) t:=by
   have:=((hasDerivAt_id t).add_const (m:ℝ)).fun_pow i
   simpa using this
  have h2:HasDerivAt (fun x:ℝ=>((z32 n i m:ℚ):ℝ)/(x+(m:ℝ))^i)
    (-(((z32 n i m:ℚ):ℝ)*((i:ℝ)*(t+(m:ℝ))^(i-1))) /
     ((t+(m:ℝ))^i)^2) t:=by
   have:=(hasDerivAt_const t ((z32 n i m:ℚ):ℝ)).fun_div h1 (pow_ne_zero i htm)
   simpa using this
  have hval:-((i:ℝ)*((z32 n i m:ℚ):ℝ))/(t+(m:ℝ))^(i+1) =
    -(((z32 n i m:ℚ):ℝ)*((i:ℝ)*(t+(m:ℝ))^(i-1))) /
     ((t+(m:ℝ))^i)^2:=by
   rcases i with _ | i
   ·
    simp
   ·
    simp only [Nat.add_sub_cancel]
    field_simp [htm,pow_ne_zero (i+1) htm]
    ring
  rw [hval]
  exact h2
 have hg1'_deriv:HasDerivAt g1' (z21 n (k:ℝ)) (k:ℝ):=by
  have hkpos:(0:ℝ)< k:=Nat.cast_pos.mpr hk1
  refine HasDerivAt.fun_sum fun m _=>HasDerivAt.fun_sum fun i _=>?_
  have hkm:(k:ℝ)+(m:ℝ)≠0:=by positivity
  have h1:HasDerivAt (fun x:ℝ=>(x+(m:ℝ))^(i+1))
    (((i+1:ℕ):ℝ)*((k:ℝ)+(m:ℝ))^i) (k:ℝ):=by
   have:=((hasDerivAt_id (k:ℝ)).add_const (m:ℝ)).fun_pow (i+1)
   simpa using this
  have h2:HasDerivAt (fun x:ℝ=>-((i:ℝ)*((z32 n i m:ℚ):ℝ))/(x+(m:ℝ))^(i+1))
    (-(-((i:ℝ)*((z32 n i m:ℚ):ℝ))*(((i+1:ℕ):ℝ)*((k:ℝ)+(m:ℝ))^i)) /
     (((k:ℝ)+(m:ℝ))^(i+1))^2) (k:ℝ):=by
   have:=(hasDerivAt_const (k:ℝ) (-((i:ℝ)*((z32 n i m:ℚ):ℝ)))).fun_div h1
    (pow_ne_zero (i+1) hkm)
   simpa using this
  have hval:((i*(i+1):ℕ):ℝ)*((z32 n i m:ℚ):ℝ)/((k:ℝ)+(m:ℝ))^(i+2) =
    -(-((i:ℝ)*((z32 n i m:ℚ):ℝ))*(((i+1:ℕ):ℝ)*((k:ℝ)+(m:ℝ))^i)) /
     (((k:ℝ)+(m:ℝ))^(i+1))^2:=by
   push_cast
   have hpow:(((k:ℝ)+(m:ℝ))^(i+1))^2 =
     ((k:ℝ)+(m:ℝ))^(i+2)*((k:ℝ)+(m:ℝ))^i:=by
    rw [← pow_mul,← pow_add];congr 1;omega
   rw [hpow]
   field_simp [hkm,pow_ne_zero i hkm,pow_ne_zero (i+2) hkm]
  rw [hval]
  exact h2
 have hdvd3:(X-C (k:ℚ))^3 ∣ z10 n:=by
  unfold z10
  refine dvd_mul_of_dvd_left ?_ _
  refine dvd_mul_of_dvd_right ?_ _
  have hkmem:k∈Finset.Icc 1 (27*n):=Finset.mem_Icc.mpr ⟨hk1,hk27⟩
  rw [← Finset.mul_prod_erase _ _ hkmem,mul_pow]
  exact dvd_mul_right _ _
 rcases hdvd3 with ⟨S,hS⟩
 let h:ℝ→ ℝ:=fun t=>Polynomial.aeval t S/Polynomial.aeval t (z13 n)
 have hf_eq_cube:∀ t:ℝ,0< t→ f t=(t-(k:ℝ))^3*h t:=by
  intro t _
  dsimp only [f,h]
  have hSev:=congr_arg (Polynomial.aeval t) hS
  simp only [map_mul,map_pow,map_sub,Polynomial.aeval_X,Polynomial.aeval_C,eq_ratCast,
   Rat.cast_natCast] at hSev
  rw [hSev,mul_div_assoc]
 let SR:Polynomial ℝ:=S.map (algebraMap ℚ ℝ)
 let QR:Polynomial ℝ:=(z13 n).map (algebraMap ℚ ℝ)
 have hh_eq:∀ t:ℝ,h t=SR.eval t/QR.eval t:=by
  intro t;simp [h,SR,QR,Polynomial.aeval_def,Polynomial.eval_map]
 have hh_deriv:∀ t:ℝ,0< t →
   HasDerivAt h ((SR.derivative.eval t*QR.eval t-SR.eval t*QR.derivative.eval t) /
    (QR.eval t)^2) t:=by
  intro t ht
  have hQne:QR.eval t≠0:=by
   have:=hQpos t ht;simpa [QR,Polynomial.aeval_def,Polynomial.eval_map] using this
  rw [show h=fun x=>SR.eval x/QR.eval x from funext hh_eq]
  exact (SR.hasDerivAt t).fun_div (QR.hasDerivAt t) hQne
 let h':ℝ→ ℝ:=fun t =>
  (SR.derivative.eval t*QR.eval t-SR.eval t*QR.derivative.eval t)/(QR.eval t)^2
 have hh'_diff:DifferentiableAt ℝ h' (k:ℝ):=by
  have hkpos:(0:ℝ)< k:=Nat.cast_pos.mpr hk1
  have hQne:QR.eval (k:ℝ)≠0:=by
   have:=hQpos (k:ℝ) hkpos;simpa [QR,Polynomial.aeval_def,Polynomial.eval_map] using this
  have hnum:DifferentiableAt ℝ (fun t=>SR.derivative.eval t*QR.eval t -
    SR.eval t*QR.derivative.eval t) (k:ℝ):=
   ((SR.derivative.hasDerivAt _).differentiableAt.fun_mul (QR.hasDerivAt _).differentiableAt).fun_sub
    ((SR.hasDerivAt _).differentiableAt.fun_mul (QR.derivative.hasDerivAt _).differentiableAt)
  have hden:DifferentiableAt ℝ (fun t=>(QR.eval t)^2) (k:ℝ):=
   (QR.hasDerivAt _).differentiableAt.fun_pow 2
  exact hnum.fun_div hden (pow_ne_zero 2 hQne)
 have hg1'_eq:∀ t:ℝ,0< t →
   g1' t=3*(t-(k:ℝ))^2*h t+(t-(k:ℝ))^3*h' t:=by
  intro t ht
  have hcube_d:HasDerivAt (fun x=>(x-(k:ℝ))^3*h x)
    (3*(t-(k:ℝ))^2*h t+(t-(k:ℝ))^3*h' t) t:=by
   have h1:HasDerivAt (fun x:ℝ=>(x-(k:ℝ))^3) (3*(t-(k:ℝ))^2) t:=by
    have:=((hasDerivAt_id t).sub_const (k:ℝ)).fun_pow 3
    simpa using this
   exact h1.fun_mul (hh_deriv t ht)
  have hev:g1 =ᶠ[nhds t] (fun x=>(x-(k:ℝ))^3*h x):=by
   filter_upwards [eventually_gt_nhds ht] with x hx
   rw [← hfg x hx,hf_eq_cube x hx]
  exact (hg1_deriv t ht).unique (hcube_d.congr_of_eventuallyEq hev)
 have hkpos:(0:ℝ)< k:=Nat.cast_pos.mpr hk1
 have hRHS_d:HasDerivAt (fun x=>3*(x-(k:ℝ))^2*h x+(x-(k:ℝ))^3*h' x)
   0 (k:ℝ):=by
  have hA:HasDerivAt (fun x=>3*(x-(k:ℝ))^2*h x) 0 (k:ℝ):=by
   have h1:HasDerivAt (fun x:ℝ=>3*(x-(k:ℝ))^2) 0 (k:ℝ):=by
    have:=(((hasDerivAt_id (k:ℝ)).sub_const (k:ℝ)).fun_pow 2).const_mul 3
    simpa using this
   have h2:=h1.fun_mul (hh_deriv (k:ℝ) hkpos)
   simpa using h2
  have hB:HasDerivAt (fun x=>(x-(k:ℝ))^3*h' x) 0 (k:ℝ):=by
   have h1:HasDerivAt (fun x:ℝ=>(x-(k:ℝ))^3) 0 (k:ℝ):=by
    have:=((hasDerivAt_id (k:ℝ)).sub_const (k:ℝ)).fun_pow 3
    simpa using this
   have h2:=h1.fun_mul hh'_diff.hasDerivAt
   simpa using h2
  simpa using hA.fun_add hB
 have hev':g1' =ᶠ[nhds (k:ℝ)]
   (fun x=>3*(x-(k:ℝ))^2*h x+(x-(k:ℝ))^3*h' x):=by
  filter_upwards [eventually_gt_nhds hkpos] with x hx
  exact hg1'_eq x hx
 exact hg1'_deriv.unique (hRHS_d.congr_of_eventuallyEq hev')
noncomputable def z285 (j:ℕ):ℝ:=
 ∑' m:ℕ,(1:ℝ)/((m:ℝ)+1)^j
lemma z251 {j:ℕ} (hj:2 ≤ j) :
  riemannZeta (j:ℂ)=(z285 j:ℂ):=by
 have hj1:1< ((j:ℂ)).re:=by
  simp only [Complex.natCast_re]
  exact_mod_cast (show 1< j by omega)
 rw [zeta_eq_tsum_one_div_nat_add_one_cpow hj1]
 unfold z285
 rw [Complex.ofReal_tsum]
 congr 1;ext m
 push_cast
 rw [Complex.cpow_natCast]
private lemma z266 {j:ℕ} (hj:2 ≤ j) (k:ℕ) :
  Summable (fun m:ℕ=>(1:ℝ)/((m:ℝ)+1+(k:ℝ))^j):=by
 have hbase:Summable (fun n:ℕ=>((n:ℝ)^j)⁻¹):=
  Real.summable_nat_pow_inv.mpr (by omega)
 have hshift:=(summable_nat_add_iff (k+1)).mpr hbase
 refine hshift.congr fun m=>?_
 rw [one_div];congr 1;push_cast;ring
private lemma z101 {j:ℕ} (hj:2 ≤ j) (k:ℕ) :
  HasSum (fun m:ℕ=>(1:ℝ)/((m:ℝ)+1+(k:ℝ))^j)
   (z285 j - ∑ i∈Finset.Icc 1 k,(1:ℝ)/(i:ℝ)^j):=by
 have hsum0:Summable (fun m:ℕ=>(1:ℝ)/((m:ℝ)+1)^j):=by
  simpa using z266 hj 0
 have hshift:=hsum0.sum_add_tsum_nat_add k
 have hfin:∑ i∈Finset.range k,(1:ℝ)/((i:ℝ)+1)^j =
   ∑ i∈Finset.Icc 1 k,(1:ℝ)/(i:ℝ)^j:=by
  refine Finset.sum_bij (fun i _=>i+1) ?_ ?_ ?_ ?_
  ·
   intro i hi;simp only [Finset.mem_range] at hi;simp only [Finset.mem_Icc];omega
  ·
   intro i1 _ i2 _ h;omega
  ·
   intro i hi;simp only [Finset.mem_Icc] at hi
   exact ⟨i-1,by simp only [Finset.mem_range];omega,by omega⟩
  ·
   intro i _;push_cast;rfl
 have htsum:∑' m:ℕ,(1:ℝ)/((m:ℝ)+1+(k:ℝ))^j =
   z285 j - ∑ i∈Finset.Icc 1 k,(1:ℝ)/(i:ℝ)^j:=by
  have heq:(fun m:ℕ=>(1:ℝ)/((m:ℝ)+1+(k:ℝ))^j) =
    (fun m:ℕ=>(1:ℝ)/(((m+k:ℕ):ℝ)+1)^j):=by
   ext m;push_cast;ring_nf
  rw [heq]
  unfold z285
  linarith
 rw [← htsum]
 exact (z266 hj k).hasSum
noncomputable def z3 (n:ℕ):ℝ:=
 (1/2:ℝ)*∑' k:ℕ,z21 n ((k:ℝ)+1)
noncomputable def z48 (n i:ℕ):ℚ:=
 ((i*(i+1)/2:ℕ):ℚ)*∑ m∈Finset.Icc (2*n) (35*n),z32 n i m
noncomputable def z47 (n:ℕ):ℚ:=
 ∑ i∈Finset.Icc 1 10,
  ((i*(i+1)/2:ℕ):ℚ) *
   ∑ m∈Finset.Icc (2*n) (35*n),
    z32 n i m*∑ j∈Finset.Icc 1 m,(1:ℚ)/(j:ℚ)^(i+2)
private lemma z280 (i:ℕ):2 ∣ i*(i+1):=by
 rcases Nat.even_or_odd i with ⟨k,rfl⟩ | ⟨k,rfl⟩
 ·
  exact ⟨k*(2*k+1),by ring⟩
 ·
  exact ⟨(2*k+1)*(k+1),by ring⟩
private lemma z93 (i:ℕ) :
  (1/2:ℝ)*((i*(i+1):ℕ):ℝ)=((i*(i+1)/2:ℕ):ℝ):=by
 have hdvd:=z280 i
 have h:2*(i*(i+1)/2)=i*(i+1):=Nat.mul_div_cancel' hdvd
 have hr:(2:ℝ)*((i*(i+1)/2:ℕ):ℝ)=((i*(i+1):ℕ):ℝ):=by exact_mod_cast h
 linarith
theorem z6 {n:ℕ} (hn:1 ≤ n) :
  z3 n =
   ((z48 n 3:ℚ):ℝ)*z285 5 +
   ((z48 n 5:ℚ):ℝ)*z285 7 +
   ((z48 n 7:ℚ):ℝ)*z285 9 +
   ((z48 n 9:ℚ):ℝ)*z285 11 -
   ((z47 n:ℚ):ℝ):=by
 have hhasSum_term:∀ m∈Finset.Icc (2*n) (35*n),∀ i∈Finset.Icc 1 10,
   HasSum (fun k:ℕ=>((i*(i+1):ℕ):ℝ)*((z32 n i m:ℚ):ℝ) /
     (((k:ℝ)+1)+(m:ℝ))^(i+2))
    (((i*(i+1):ℕ):ℝ)*((z32 n i m:ℚ):ℝ) *
     (z285 (i+2) - ∑ j∈Finset.Icc 1 m,(1:ℝ)/(j:ℝ)^(i+2))):=by
  intro m _ i hi
  have h:=(z101 (j:=i+2) (by omega) m).mul_left
   (((i*(i+1):ℕ):ℝ)*((z32 n i m:ℚ):ℝ))
  refine h.congr_fun fun k=>by ring
 have hhasSum_tot:HasSum (fun k:ℕ=>z21 n ((k:ℝ)+1))
   (∑ m∈Finset.Icc (2*n) (35*n),∑ i∈Finset.Icc 1 10,
    ((i*(i+1):ℕ):ℝ)*((z32 n i m:ℚ):ℝ) *
     (z285 (i+2) - ∑ j∈Finset.Icc 1 m,(1:ℝ)/(j:ℝ)^(i+2))):=by
  unfold z21
  exact hasSum_sum fun m hm=>hasSum_sum fun i hi=>hhasSum_term m hm i hi
 unfold z3
 rw [hhasSum_tot.tsum_eq,Finset.sum_comm,Finset.mul_sum]
 have hsplit:∑ i∈Finset.Icc 1 10,
   (1/2:ℝ)*∑ m∈Finset.Icc (2*n) (35*n),
    ((i*(i+1):ℕ):ℝ)*((z32 n i m:ℚ):ℝ) *
     (z285 (i+2) - ∑ j∈Finset.Icc 1 m,(1:ℝ)/(j:ℝ)^(i+2)) =
   (∑ i∈Finset.Icc 1 10,((z48 n i:ℚ):ℝ)*z285 (i+2)) -
    ((z47 n:ℚ):ℝ):=by
  unfold z48 z47
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _=>?_
  rw [← z93 i]
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  rw [mul_sub]
  congr 1
  ·
   rw [Finset.mul_sum,Finset.mul_sum,Finset.sum_mul]
   refine Finset.sum_congr rfl fun m _=>by push_cast;ring
  ·
   rw [Finset.mul_sum,Finset.mul_sum]
   refine Finset.sum_congr rfl fun m _=>by push_cast;ring
 rw [hsplit]
 congr 1
 have h1:z48 n 1=0:=by unfold z48;rw [z265 hn,mul_zero]
 have h2:z48 n 2=0:=by unfold z48;rw [z264 (by decide),mul_zero]
 have h4:z48 n 4=0:=by unfold z48;rw [z264 (by decide),mul_zero]
 have h6:z48 n 6=0:=by unfold z48;rw [z264 (by decide),mul_zero]
 have h8:z48 n 8=0:=by unfold z48;rw [z264 (by decide),mul_zero]
 have h10:z48 n 10=0:=by unfold z48;rw [z264 (by decide),mul_zero]
 rw [Finset.sum_Icc_succ_top (by omega:1 ≤ 10),Finset.sum_Icc_succ_top (by omega:1 ≤ 9),
  Finset.sum_Icc_succ_top (by omega:1 ≤ 8),Finset.sum_Icc_succ_top (by omega:1 ≤ 7),
  Finset.sum_Icc_succ_top (by omega:1 ≤ 6),Finset.sum_Icc_succ_top (by omega:1 ≤ 5),
  Finset.sum_Icc_succ_top (by omega:1 ≤ 4),Finset.sum_Icc_succ_top (by omega:1 ≤ 3),
  Finset.sum_Icc_succ_top (by omega:1 ≤ 2),Finset.Icc_self,Finset.sum_singleton]
 simp only [h1,h2,h4,h6,h8,h10,Rat.cast_zero,zero_mul,add_zero,zero_add]
def D_B (n:ℕ):ℕ:=
 (Nat.lcmUpto (35*n))^3*Nat.lcmUpto (34*n)*(Nat.lcmUpto (33*n))^8
lemma z2 (n:ℕ):0< D_B n:=by
 unfold D_B
 have h1:=Nat.lcmUpto_pos (35*n)
 have h2:=Nat.lcmUpto_pos (34*n)
 have h3:=Nat.lcmUpto_pos (33*n)
 positivity
private lemma z33 {n i m:ℕ} (hlo:2*n ≤ m) (hhi:m ≤ 35*n)
  (hi1:1 ≤ i) (himk:i ≤ z174 n m) :
  z56 ((Nat.lcmUpto (33*n))^(10-i)) (z32 n i m):=by
 unfold z32
 rw [if_pos ⟨hi1,himk⟩]
 unfold z243
 have hL:z199 (Nat.lcmUpto (33*n)) 0
   (toPS (C (((37*n:ℤ)-2*(m:ℤ):ℤ):ℚ)+C 2*X)):=by
  intro d
  unfold toPS
  rw [Polynomial.coeff_add,Polynomial.coeff_C,Polynomial.coeff_C_mul,Polynomial.coeff_X]
  rcases d with _ | _ | d
  ·
   simp only [↓reduceIte,one_ne_zero,mul_zero,add_zero,pow_zero]
   exact z59 _
  ·
   simp only [Nat.one_ne_zero,↓reduceIte,mul_one,zero_add,add_zero,pow_one]
   exact z58 (one_dvd _) (z62 2)
  ·
   simp only [show ¬(d+2=0) by omega,show ¬(1=d+2) by omega,
    ↓reduceIte,mul_zero,add_zero]
   exact z67 _
 have hA:z199 (Nat.lcmUpto (33*n)) 0
   (psPow (z238 ((-1:ℚ)^(27*n))
    (z216 (toPS (C (((27*n).factorial:ℚ)⁻¹) *
     ∏ r∈Finset.Icc 1 (27*n),(X+C ((m+r:ℕ):ℚ)))))) 3):=by
  have h1:=z189 m (27*n)
  have h2:=z200 (z120 (by omega:27*n ≤ 33*n)) h1
  have h3:=z204 h2
  have hscale:((-1:ℚ)^(27*n))=(((-1:ℤ)^(27*n):ℤ):ℚ):=by push_cast;rfl
  rw [hscale]
  simpa using z206 (z201 ((-1:ℤ)^(27*n)) h3) 3
 have hB:z199 (Nat.lcmUpto (33*n)) 0
   (psPow (toPS (C (((27*n).factorial:ℚ)⁻¹) *
    ∏ r∈Finset.Icc 1 (27*n),(X+C ((37*n-m+r:ℕ):ℚ)))) 3):=by
  have h1:=z189 (37*n-m) (27*n)
  have h2:=z200 (z120 (by omega:27*n ≤ 33*n)) h1
  simpa using z206 h2 3
 have hC:z199 (Nat.lcmUpto (33*n)) (10-z174 n m)
   (z230 (Finset.Icc 1 10) fun u =>
    if (1+u)*n ≤ m∧m ≤ (36-u)*n then
     z195 ((1+u)*n) ((36-u)*n) m
    else
     z191 ((1+u)*n) ((36-u)*n) m):=by
  have hsum:(∑ u∈Finset.Icc 1 10,
    if (1+u)*n ≤ m∧m ≤ (36-u)*n then (0:ℕ) else 1)=10-z174 n m:=by
   have h1:∀ u∈Finset.Icc 1 10,
     (if (1+u)*n ≤ m∧m ≤ (36-u)*n then (0:ℕ) else 1) +
     (if (1+u)*n ≤ m∧m ≤ (36-u)*n then (1:ℕ) else 0)=1:=by
    intro u _;split_ifs <;> omega
   have hadd:=Finset.sum_congr rfl h1
   rw [Finset.sum_add_distrib] at hadd
   have hcard10:(∑ _u∈Finset.Icc 1 10,(1:ℕ))=10:=by decide
   have hpm:(∑ u∈Finset.Icc 1 10,
     if (1+u)*n ≤ m∧m ≤ (36-u)*n then (1:ℕ) else 0)=z174 n m:=by
    unfold z174;rw [Finset.sum_boole,Nat.cast_id]
   omega
  rw [← hsum]
  refine z207 _ _ _ fun u hu=>?_
  rcases Finset.mem_Icc.mp hu with ⟨hu1,hu10⟩
  split_ifs with hcond
  ·
   refine z197 hcond.1 hcond.2 ?_
   have:(36-u)*n-(1+u)*n=(35-2*u)*n:=by
    rw [← Nat.sub_mul];congr 1;omega
   rw [this];exact Nat.mul_le_mul_right n (by omega)
  ·
   have hu2:2 ≤ u:=by
    by_contra! hlt
    have hu_eq:u=1:=by omega
    subst hu_eq
    exact hcond ⟨by omega,by omega⟩
   have hab:(1+u)*n ≤ (36-u)*n:=Nat.mul_le_mul_right n (by omega)
   have hnot:m∉Finset.Icc ((1+u)*n) ((36-u)*n):=by
    simpa [Finset.mem_Icc] using hcond
   refine z193 hab hnot fun r hr=>?_
   rcases Finset.mem_Icc.mp hr with ⟨hr1,hr2⟩
   have h34:(36-u)*n ≤ 34*n:=Nat.mul_le_mul_right n (by omega)
   have h3:3*n ≤ (1+u)*n:=Nat.mul_le_mul_right n (by omega)
   omega
 have htot:=z203 hL (z203 hA (z203 hB hC))
 have hval:=htot (z174 n m-i)
 have hexp:z174 n m-i+(0+(0+(0+(10-z174 n m))))=10-i:=by
  have:=z177 n m;omega
 rwa [hexp] at hval
theorem z1 {n i:ℕ} (hi1:1 ≤ i) (hi10:i ≤ 10) :
  z56 (D_B n) (z48 n i):=by
 unfold z48
 refine z60 ((i*(i+1)/2:ℕ):ℤ) ?_
 refine z66 fun m hm=>?_
 by_cases himk:i ≤ z174 n m
 ·
  have h:=z33 (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2 hi1 himk
  refine z58 ?_ h
  unfold D_B
  have hd1:Nat.lcmUpto (33*n) ∣ Nat.lcmUpto (35*n):=z120 (by omega)
  have hd2:Nat.lcmUpto (33*n) ∣ Nat.lcmUpto (34*n):=z120 (by omega)
  have h12:(Nat.lcmUpto (33*n))^12 ∣
    (Nat.lcmUpto (35*n))^3*Nat.lcmUpto (34*n)*(Nat.lcmUpto (33*n))^8:=by
   have:(Nat.lcmUpto (33*n))^12 =
     (Nat.lcmUpto (33*n))^3*Nat.lcmUpto (33*n)*(Nat.lcmUpto (33*n))^8:=by ring
   rw [this]
   exact mul_dvd_mul (mul_dvd_mul (pow_dvd_pow_of_dvd hd1 3) hd2) dvd_rfl
  exact (pow_dvd_pow _ (by omega:10-i ≤ 12)).trans h12
 ·
  have h0:z32 n i m=0:=by
   unfold z32;rw [if_neg];intro h;exact himk h.2
  rw [h0];exact z67 _
theorem z0 (n:ℕ) :
  z56 (D_B n) (z47 n):=by
 unfold z47
 refine z66 fun i hi=>?_
 rcases Finset.mem_Icc.mp hi with ⟨hi1,hi10⟩
 refine z60 ((i*(i+1)/2:ℕ):ℤ) ?_
 refine z66 fun m hm=>?_
 rcases Finset.mem_Icc.mp hm with ⟨hmlo,hmhi⟩
 rw [Finset.mul_sum]
 refine z66 fun j hj=>?_
 rcases Finset.mem_Icc.mp hj with ⟨hj1,hjm⟩
 by_cases himk:i ≤ z174 n m
 ·
  have hc:=z33 hmlo hmhi hi1 himk
  have hmk_cases:z174 n m=1∨z174 n m=2∨3 ≤ z174 n m:=by omega
  rcases hmk_cases with hmk1 | hmk2 | hmk3
  ·
   have hi_eq:i=1:=by omega
   subst hi_eq
   have hj_dvd:j ∣ Nat.lcmUpto (35*n):=z130 hj1 (hjm.trans hmhi)
   have hj3:z56 ((Nat.lcmUpto (35*n))^3) ((1:ℚ)/(j:ℚ)^3):=by
    have hbase:=z65 hj1 hj_dvd
    have h3:=z61 (z61 hbase hbase) hbase
    have hD:Nat.lcmUpto (35*n)*Nat.lcmUpto (35*n)*Nat.lcmUpto (35*n) =
      (Nat.lcmUpto (35*n))^3:=by ring
    have hq:(1/(j:ℚ))*(1/(j:ℚ))*(1/(j:ℚ))=1/(j:ℚ)^3:=by ring
    rwa [hD,hq] at h3
   have hprod:=z61 hc hj3
   refine z58 ?_ hprod
   unfold D_B
   have hd2:Nat.lcmUpto (33*n) ∣ Nat.lcmUpto (34*n):=z120 (by omega)
   have h9:(Nat.lcmUpto (33*n))^(10-1)*(Nat.lcmUpto (35*n))^3 =
     (Nat.lcmUpto (35*n))^3*Nat.lcmUpto (33*n)*(Nat.lcmUpto (33*n))^8:=by
    rw [show 10-1=9 by norm_num];ring
   rw [h9]
   exact mul_dvd_mul_right (mul_dvd_mul_left _ hd2) _
  ·
   have hm34:m ≤ 34*n:=z176 (by omega)
   have hj_dvd34:j ∣ Nat.lcmUpto (34*n):=z130 hj1 (hjm.trans hm34)
   have hj_dvd35:j ∣ Nat.lcmUpto (35*n):=hj_dvd34.trans (z120 (by omega))
   have hi_cases:i=1∨i=2:=by omega
   rcases hi_cases with rfl | rfl
   ·
    have hbase35:=z65 hj1 hj_dvd35
    have hj3:z56 ((Nat.lcmUpto (35*n))^3) ((1:ℚ)/(j:ℚ)^3):=by
     have h3:=z61 (z61 hbase35 hbase35) hbase35
     have hD:Nat.lcmUpto (35*n)*Nat.lcmUpto (35*n)*Nat.lcmUpto (35*n) =
       (Nat.lcmUpto (35*n))^3:=by ring
     have hq:(1/(j:ℚ))*(1/(j:ℚ))*(1/(j:ℚ))=1/(j:ℚ)^3:=by ring
     rwa [hD,hq] at h3
    have hprod:=z61 hc hj3
    refine z58 ?_ hprod
    unfold D_B
    have hd2:Nat.lcmUpto (33*n) ∣ Nat.lcmUpto (34*n):=z120 (by omega)
    have h9:(Nat.lcmUpto (33*n))^(10-1)*(Nat.lcmUpto (35*n))^3 =
      (Nat.lcmUpto (35*n))^3*Nat.lcmUpto (33*n)*(Nat.lcmUpto (33*n))^8:=by
     rw [show 10-1=9 by norm_num];ring
    rw [h9]
    exact mul_dvd_mul_right (mul_dvd_mul_left _ hd2) _
   ·
    have hbase35:=z65 hj1 hj_dvd35
    have hbase34:=z65 hj1 hj_dvd34
    have hj4:z56 ((Nat.lcmUpto (35*n))^3*Nat.lcmUpto (34*n)) ((1:ℚ)/(j:ℚ)^4):=by
     have h4:=z61 (z61 (z61 hbase35 hbase35) hbase35) hbase34
     have hpow4:(1/(j:ℚ))*(1/(j:ℚ))*(1/(j:ℚ))*(1/(j:ℚ)) =
       1/(j:ℚ)^4:=by ring
     have hD:Nat.lcmUpto (35*n)*Nat.lcmUpto (35*n)*Nat.lcmUpto (35*n) *
       Nat.lcmUpto (34*n)=(Nat.lcmUpto (35*n))^3*Nat.lcmUpto (34*n):=by ring
     rwa [hpow4,hD] at h4
    have hprod:=z61 hc hj4
    refine z58 ?_ hprod
    unfold D_B
    rw [show 10-2=8 by norm_num,mul_comm]
  ·
   have hm33:m ≤ 33*n:=z175 hmk3
   have hj_dvd33:j ∣ Nat.lcmUpto (33*n):=z130 hj1 (hjm.trans hm33)
   have hjpow:z56 ((Nat.lcmUpto (33*n))^(i+2)) ((1:ℚ)/(j:ℚ)^(i+2)):=by
    have hbase:=z65 hj1 hj_dvd33
    have hpow:∀ k:ℕ,z56 ((Nat.lcmUpto (33*n))^k) ((1:ℚ)/(j:ℚ)^k):=by
     intro k;induction k with
     | zero=>simpa using z62 1
     | succ k ih =>
      have hm:=z61 ih hbase
      have heq:(1:ℚ)/(j:ℚ)^k*(1/(j:ℚ))=1/(j:ℚ)^(k+1):=by
       rw [pow_succ];ring
      rwa [heq,← pow_succ] at hm
    exact hpow (i+2)
   have hprod:=z61 hc hjpow
   rw [← pow_add,show 10-i+(i+2)=12 by omega] at hprod
   refine z58 ?_ hprod
   unfold D_B
   have hd1:Nat.lcmUpto (33*n) ∣ Nat.lcmUpto (35*n):=z120 (by omega)
   have hd2:Nat.lcmUpto (33*n) ∣ Nat.lcmUpto (34*n):=z120 (by omega)
   have:(Nat.lcmUpto (33*n))^12 =
     (Nat.lcmUpto (33*n))^3*Nat.lcmUpto (33*n)*(Nat.lcmUpto (33*n))^8:=by ring
   rw [this]
   exact mul_dvd_mul (mul_dvd_mul (pow_dvd_pow_of_dvd hd1 3) hd2) dvd_rfl
 ·
  have h0:z32 n i m=0:=by
   unfold z32;rw [if_neg];intro h;exact himk h.2
  rw [h0,zero_mul];exact z67 _
noncomputable def z164 (x y:ℝ):ℤ:=
 3*(⌊y⌋ - ⌊(27:ℝ)*x⌋ - ⌊y-(27:ℝ)*x⌋) +
 3*(⌊(91:ℝ)*x-y⌋ - ⌊(27:ℝ)*x⌋ - ⌊(64:ℝ)*x-y⌋) +
 ∑ u∈Finset.Icc (1:ℕ) 10,
  (⌊((35-2*u:ℕ):ℝ)*x⌋ - ⌊y-((28+u:ℕ):ℝ)*x⌋ - ⌊((63-u:ℕ):ℝ)*x-y⌋)
private lemma z165 (x y:ℝ) (k:ℤ) :
  z164 x (y+k)=z164 x y:=by
 unfold z164
 have h1:⌊y+k⌋=⌊y⌋+k:=Int.floor_add_intCast y k
 have h2:⌊y+k-(27:ℝ)*x⌋=⌊y-(27:ℝ)*x⌋+k:=by
  rw [show y+k-(27:ℝ)*x=(y-(27:ℝ)*x)+k by ring,Int.floor_add_intCast]
 have h3:⌊(91:ℝ)*x-(y+k)⌋=⌊(91:ℝ)*x-y⌋ - k:=by
  rw [show (91:ℝ)*x-(y+k)=((91:ℝ)*x-y)+((-k:ℤ):ℝ) by push_cast;ring,
   Int.floor_add_intCast];ring
 have h4:⌊(64:ℝ)*x-(y+k)⌋=⌊(64:ℝ)*x-y⌋ - k:=by
  rw [show (64:ℝ)*x-(y+k)=((64:ℝ)*x-y)+((-k:ℤ):ℝ) by push_cast;ring,
   Int.floor_add_intCast];ring
 have h5:∀ u∈Finset.Icc (1:ℕ) 10,
   ⌊((35-2*u:ℕ):ℝ)*x⌋ - ⌊y+k-((28+u:ℕ):ℝ)*x⌋ -
    ⌊((63-u:ℕ):ℝ)*x-(y+k)⌋ =
   ⌊((35-2*u:ℕ):ℝ)*x⌋ - ⌊y-((28+u:ℕ):ℝ)*x⌋ -
    ⌊((63-u:ℕ):ℝ)*x-y⌋:=by
  intro u _
  have ha:⌊y+k-((28+u:ℕ):ℝ)*x⌋=⌊y-((28+u:ℕ):ℝ)*x⌋+k:=by
   rw [show y+k-((28+u:ℕ):ℝ)*x=(y-((28+u:ℕ):ℝ)*x)+k by ring,
    Int.floor_add_intCast]
  have hb:⌊((63-u:ℕ):ℝ)*x-(y+k)⌋=⌊((63-u:ℕ):ℝ)*x-y⌋ - k:=by
   rw [show ((63-u:ℕ):ℝ)*x-(y+k) =
     (((63-u:ℕ):ℝ)*x-y)+((-k:ℤ):ℝ) by push_cast;ring,
    Int.floor_add_intCast];ring
  omega
 rw [h1,h2,h3,h4,Finset.sum_congr rfl h5]
 ring
private lemma z34 {p n i m:ℕ} [Fact p.Prime]
  (hlo:2*n ≤ m) (hhi:m ≤ 35*n) (hsq:91*n< p*p)
  (hi1:1 ≤ i) (himk:i ≤ z174 n m) :
  z147 p
   (z164 ((n:ℝ)/p) (Int.fract (((m+27*n:ℕ):ℝ)/p))-10+(i:ℤ))
   (z32 n i m):=by
 have hphi_eq:z164 ((n:ℝ)/p) (Int.fract (((m+27*n:ℕ):ℝ)/p)) =
   z164 ((n:ℝ)/p) (((m+27*n:ℕ):ℝ)/p):=by
  have h:=z165 ((n:ℝ)/p) (Int.fract (((m+27*n:ℕ):ℝ)/p))
   ⌊((m+27*n:ℕ):ℝ)/p⌋
  rw [show Int.fract (((m+27*n:ℕ):ℝ)/p)+(⌊((m+27*n:ℕ):ℝ)/p⌋ : ℝ) =
   ((m+27*n:ℕ):ℝ)/p by linarith [Int.floor_add_fract (((m+27*n:ℕ):ℝ)/p)]] at h
  exact h.symm
 rw [hphi_eq]
 unfold z32
 rw [if_pos ⟨hi1,himk⟩]
 unfold z243
 have hL:z221 p 0
   (toPS (C (((37*n:ℤ)-2*(m:ℤ):ℤ):ℚ)+C 2*X)):=by
  intro d
  unfold toPS
  rw [Polynomial.coeff_add,Polynomial.coeff_C,Polynomial.coeff_C_mul,Polynomial.coeff_X]
  rcases d with _ | _ | d
  ·
   simp only [↓reduceIte,one_ne_zero,mul_zero,add_zero,CharP.cast_eq_zero,sub_zero]
   exact z149 p _
  ·
   simp only [Nat.one_ne_zero,↓reduceIte,mul_one,zero_add,Nat.cast_one,zero_sub]
   exact z151 (by omega) (z153 p 2)
  ·
   simp only [show ¬(d+2=0) by omega,show ¬(1=d+2) by omega,
    ↓reduceIte,mul_zero,add_zero]
   exact z158 p _
 have hA:z221 p
   (3*(⌊((m+27*n:ℕ):ℝ)/p⌋ - ⌊(27:ℝ)*((n:ℝ)/p)⌋ -
    ⌊((m+27*n:ℕ):ℝ)/p-(27:ℝ)*((n:ℝ)/p)⌋))
   (psPow (z238 ((-1:ℚ)^(27*n))
    (z216 (toPS (C (((27*n).factorial:ℚ)⁻¹) *
     ∏ r∈Finset.Icc 1 (27*n),(X+C ((m+r:ℕ):ℚ)))))) 3):=by
  have h1:=z190 (p:=p) (M:=m) (L:=27*n) (by omega)
  have h2:=z224 h1
  have hsign:z147 p 0 ((-1:ℚ)^(27*n)):=by
   have:((-1:ℚ)^(27*n))=(((-1:ℤ)^(27*n):ℤ):ℚ):=by push_cast;rfl
   rw [this];exact z149 p _
  have h3:=z227
   (z222 (B1:=⌊((m+27*n:ℕ):ℝ)/p⌋ - ⌊(m:ℝ)/p⌋ - ⌊((27*n:ℕ):ℝ)/p⌋)
    (by omega) (z229 hsign h2)) 3
  refine z222 ?_ h3
  have heq1:(27:ℝ)*((n:ℝ)/p)=((27*n:ℕ):ℝ)/p:=by push_cast;ring
  have heq2:((m+27*n:ℕ):ℝ)/p-(27:ℝ)*((n:ℝ)/p)=(m:ℝ)/p:=by
   push_cast;ring
  rw [heq2,heq1];norm_num;linarith
 have hB:z221 p
   (3*(⌊(91:ℝ)*((n:ℝ)/p)-((m+27*n:ℕ):ℝ)/p⌋ -
    ⌊(27:ℝ)*((n:ℝ)/p)⌋ -
    ⌊(64:ℝ)*((n:ℝ)/p)-((m+27*n:ℕ):ℝ)/p⌋))
   (psPow (toPS (C (((27*n).factorial:ℚ)⁻¹) *
    ∏ r∈Finset.Icc 1 (27*n),(X+C ((37*n-m+r:ℕ):ℚ)))) 3):=by
  have h1:=z190 (p:=p) (M:=37*n-m) (L:=27*n) (by omega)
  have h2:=z227 h1 3
  refine z222 ?_ h2
  have heq1:(91:ℝ)*((n:ℝ)/p)-((m+27*n:ℕ):ℝ)/p =
    ((37*n-m+27*n:ℕ):ℝ)/p:=by
   rw [show 37*n-m+27*n=64*n-m by omega,Nat.cast_sub (by omega)]
   push_cast;ring
  have heq2:(27:ℝ)*((n:ℝ)/p)=((27*n:ℕ):ℝ)/p:=by push_cast;ring
  have heq3:(64:ℝ)*((n:ℝ)/p)-((m+27*n:ℕ):ℝ)/p =
    ((37*n-m:ℕ):ℝ)/p:=by
   rw [Nat.cast_sub (by omega)];push_cast;ring
  rw [heq1,heq2,heq3];norm_num;linarith
 have hC:z221 p
   ((∑ u∈Finset.Icc (1:ℕ) 10,
    (⌊((35-2*u:ℕ):ℝ)*((n:ℝ)/p)⌋ -
     ⌊((m+27*n:ℕ):ℝ)/p-((28+u:ℕ):ℝ)*((n:ℝ)/p)⌋ -
     ⌊((63-u:ℕ):ℝ)*((n:ℝ)/p)-((m+27*n:ℕ):ℝ)/p⌋)) -
    ((10-z174 n m:ℕ):ℤ))
   (z230 (Finset.Icc 1 10) fun u =>
    if (1+u)*n ≤ m∧m ≤ (36-u)*n then
     z195 ((1+u)*n) ((36-u)*n) m
    else
     z191 ((1+u)*n) ((36-u)*n) m):=by
  have hsum_eq:(∑ u∈Finset.Icc (1:ℕ) 10,
    ((⌊((35-2*u:ℕ):ℝ)*((n:ℝ)/p)⌋ -
     ⌊((m+27*n:ℕ):ℝ)/p-((28+u:ℕ):ℝ)*((n:ℝ)/p)⌋ -
     ⌊((63-u:ℕ):ℝ)*((n:ℝ)/p)-((m+27*n:ℕ):ℝ)/p⌋) -
     (if (1+u)*n ≤ m∧m ≤ (36-u)*n then (0:ℤ) else 1))) =
    (∑ u∈Finset.Icc (1:ℕ) 10,
     (⌊((35-2*u:ℕ):ℝ)*((n:ℝ)/p)⌋ -
      ⌊((m+27*n:ℕ):ℝ)/p-((28+u:ℕ):ℝ)*((n:ℝ)/p)⌋ -
      ⌊((63-u:ℕ):ℝ)*((n:ℝ)/p)-((m+27*n:ℕ):ℝ)/p⌋)) -
    ((10-z174 n m:ℕ):ℤ):=by
   rw [Finset.sum_sub_distrib]
   congr 1
   have h1:∀ u∈Finset.Icc (1:ℕ) 10,
     (if (1+u)*n ≤ m∧m ≤ (36-u)*n then (0:ℤ) else 1) +
     (if (1+u)*n ≤ m∧m ≤ (36-u)*n then (1:ℤ) else 0)=1:=by
    intro u _;split_ifs <;> omega
   have hadd:=Finset.sum_congr rfl h1
   rw [Finset.sum_add_distrib] at hadd
   have hcard10:(∑ _u∈Finset.Icc (1:ℕ) 10,(1:ℤ))=10:=by decide
   have hpm:(∑ u∈Finset.Icc (1:ℕ) 10,
     if (1+u)*n ≤ m∧m ≤ (36-u)*n then (1:ℤ) else 0)=(z174 n m:ℤ):=by
    unfold z174;rw [Finset.sum_boole]
   have hmk10:=z177 n m
   omega
  rw [← hsum_eq]
  refine z228 _ _ _ fun u hu=>?_
  rcases Finset.mem_Icc.mp hu with ⟨hu1,hu10⟩
  have hdiff:(36-u)*n-(1+u)*n=(35-2*u)*n:=by
   rw [← Nat.sub_mul];congr 1;omega
  have heq1:((35-2*u:ℕ):ℝ)*((n:ℝ)/p) =
    (((36-u)*n-(1+u)*n:ℕ):ℝ)/p:=by
   rw [hdiff];push_cast;ring
  have heq2:((m+27*n:ℕ):ℝ)/p-((28+u:ℕ):ℝ)*((n:ℝ)/p) =
    ((m:ℝ)-(((1+u)*n:ℕ):ℝ))/p:=by
   push_cast;ring
  have heq3:((63-u:ℕ):ℝ)*((n:ℝ)/p)-((m+27*n:ℕ):ℝ)/p =
    ((((36-u)*n:ℕ):ℝ)-(m:ℝ))/p:=by
   have h63:((63-u:ℕ):ℝ)=63-(u:ℝ):=Nat.cast_sub (by omega)
   have h36:((36-u:ℕ):ℝ)=36-(u:ℝ):=Nat.cast_sub (by omega)
   push_cast [h63,h36];ring
  rw [heq1,heq2,heq3]
  split_ifs with hcond
  ·
   rw [sub_zero]
   refine z198 hcond.1 hcond.2 ?_
   rw [hdiff]
   have:(35-2*u)*n ≤ 33*n:=Nat.mul_le_mul_right n (by omega)
   omega
  ·
   have hab:(1+u)*n ≤ (36-u)*n:=Nat.mul_le_mul_right n (by omega)
   have hnot:m∉Finset.Icc ((1+u)*n) ((36-u)*n):=by
    simpa [Finset.mem_Icc] using hcond
   refine z194 hab hnot ?_ ?_
   ·
    rw [hdiff]
    have:(35-2*u)*n ≤ 33*n:=Nat.mul_le_mul_right n (by omega)
    omega
   ·
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨hr1,hr2⟩
    have h35:(36-u)*n ≤ 35*n:=Nat.mul_le_mul_right n (by omega)
    omega
 have htot:=z223 hL (z223 hA (z223 hB hC))
 have hval:=htot (z174 n m-i)
 refine z151 ?_ hval
 unfold z164
 have hmk10:=z177 n m
 have:((10-z174 n m:ℕ):ℤ)=10-(z174 n m:ℤ):=Int.ofNat_sub hmk10
 have:((z174 n m-i:ℕ):ℤ)=(z174 n m:ℤ)-(i:ℤ):=Int.ofNat_sub himk
 omega
theorem z72
  (z168:ℕ→ ℕ→ ℕ)
  (hphi_le:∀ n p,0< z168 n p→ ∀ y:ℝ,0 ≤ y→ y< 1 →
   (91*n< p*p∧p ≤ 33*n)∧(z168 n p:ℤ) ≤ z164 ((n:ℝ)/p) y)
  {n:ℕ} (hn:1 ≤ n) :
  ∃ a0 a5 a7 a9 a11:ℤ,
   ((D_B n:ℝ)/((∏ p∈Nat.primesLE (33*n),p^(z168 n p):ℕ):ℝ))*z3 n =
    (a5:ℝ)*z285 5+(a7:ℝ)*z285 7 +
    (a9:ℝ)*z285 9+(a11:ℝ)*z285 11-(a0:ℝ):=by
 set Phi:ℕ:=∏ p∈Nat.primesLE (33*n),p^(z168 n p)
 have hPhi_pos:0< Phi:=by
  refine Finset.prod_pos fun p hp=>pow_pos (Nat.mem_primesLE.mp hp).2.pos _
 have hDB_val:∀ p:ℕ,[Fact p.Prime]→ p ≤ 33*n→ z147 p 12 (D_B n:ℚ):=by
  intro p hp hp33
  have hdiv33:p ∣ Nat.lcmUpto (33*n):=z130 hp.out.pos hp33
  have hdiv34:p ∣ Nat.lcmUpto (34*n):=z130 hp.out.pos (by omega)
  have hdiv35:p ∣ Nat.lcmUpto (35*n):=z130 hp.out.pos (by omega)
  have h12:p^12 ∣ D_B n:=by
   unfold D_B
   have:p^12=p^3*p*p^8:=by ring
   rw [this]
   exact mul_dvd_mul (mul_dvd_mul (pow_dvd_pow_of_dvd hdiv35 3) hdiv34)
    (pow_dvd_pow_of_dvd hdiv33 8)
  have h12z:((p^12:ℕ):ℤ) ∣ (D_B n:ℤ):=Int.ofNat_dvd.mpr h12
  simpa using (z150 (p:=p) (D_B n:ℤ) 12).mpr h12z
 have hdiv_Phi:∀ (q:ℚ) (hq_int:z56 (D_B n) q)
   (hq_padic:∀ p:ℕ,∀ (_hp:p∈Nat.primesLE (33*n)),0< z168 n p →
    z147 p (z168 n p:ℤ) ((D_B n:ℚ)*q)),
   ∃ a:ℤ,(a:ℝ)=((D_B n:ℝ)/(Phi:ℝ))*(q:ℝ):=by
  intro q hq_int hq_padic
  rcases hq_int with ⟨z,hz⟩
  have hPhi_dvd:(Phi:ℤ) ∣ z:=by
   rw [show (Phi:ℤ)=∏ p∈Nat.primesLE (33*n),((p^(z168 n p):ℕ):ℤ) by
    simp [Phi,Nat.cast_prod]]
   refine Finset.prod_dvd_of_coprime ?_ ?_
   ·
    intro p1 hp1 p2 hp2 hne
    have hpr1:=(Nat.mem_primesLE.mp hp1).2
    have hpr2:=(Nat.mem_primesLE.mp hp2).2
    have hcop:Nat.Coprime (p1^z168 n p1) (p2^z168 n p2):=
     ((Nat.coprime_primes hpr1 hpr2).mpr hne).pow _ _
    exact hcop.isCoprime
   ·
    intro p hp
    rcases eq_or_ne (z168 n p) 0 with h0 | hpos
    ·
     simp [h0]
    ·
     have:Fact p.Prime:=⟨(Nat.mem_primesLE.mp hp).2⟩
     have hv:=hq_padic p hp (Nat.pos_of_ne_zero hpos)
     rw [← hz] at hv
     exact (z150 z (z168 n p)).mp hv
  rcases hPhi_dvd with ⟨a,ha⟩
  refine ⟨a,?_⟩
  have hPhir:(Phi:ℝ)≠0:=Nat.cast_ne_zero.mpr hPhi_pos.ne'
  have hzr:(z:ℝ)=(D_B n:ℝ)*(q:ℝ):=by exact_mod_cast hz
  have har:(z:ℝ)=(Phi:ℝ)*(a:ℝ):=by exact_mod_cast ha
  field_simp [hPhir];linarith
 have hzeta_int:∀ i:ℕ,1 ≤ i→ i ≤ 10 →
   ∃ a:ℤ,(a:ℝ)=((D_B n:ℝ)/(Phi:ℝ))*(z48 n i:ℝ):=by
  intro i hi1 hi10
  refine hdiv_Phi (z48 n i) (z1 hi1 hi10) ?_
  intro p hp hpos
  have:Fact p.Prime:=⟨(Nat.mem_primesLE.mp hp).2⟩
  unfold z48
  rw [mul_left_comm,Finset.mul_sum]
  refine z152 (b1:=0) (b2:=(z168 n p:ℤ)) (z153 p _) ?_ |>
   fun h=>by simpa using h
  refine z157 fun m hm=>?_
  rcases Finset.mem_Icc.mp hm with ⟨hmlo,hmhi⟩
  by_cases himk:i ≤ z174 n m
  ·
   have hphi:=hphi_le n p hpos (Int.fract (((m+27*n:ℕ):ℝ)/p))
    (Int.fract_nonneg _) (Int.fract_lt_one _)
   have hDB:=hDB_val p hphi.1.2
   have hc:=z34 (p:=p) hmlo hmhi hphi.1.1 hi1 himk
   have hmul:=z152 hDB hc
   refine z151 ?_ hmul
   omega
  ·
   have h0:z32 n i m=0:=by
    unfold z32;rw [if_neg];intro h;exact himk h.2
   rw [h0,mul_zero];exact z158 p _
 have hconst_int:∃ a:ℤ,(a:ℝ)=((D_B n:ℝ)/(Phi:ℝ))*(z47 n:ℝ):=by
  refine hdiv_Phi (z47 n) (z0 n) ?_
  intro p hp hpos
  have:Fact p.Prime:=⟨(Nat.mem_primesLE.mp hp).2⟩
  unfold z47
  rw [Finset.mul_sum]
  refine z157 fun i hi=>?_
  rcases Finset.mem_Icc.mp hi with ⟨hi1,hi10⟩
  rw [mul_left_comm,Finset.mul_sum]
  refine z152 (b1:=0) (b2:=(z168 n p:ℤ)) (z153 p _) ?_ |>
   fun h=>by simpa using h
  refine z157 fun m hm=>?_
  rcases Finset.mem_Icc.mp hm with ⟨hmlo,hmhi⟩
  rw [← mul_assoc,Finset.mul_sum]
  refine z157 fun j hj=>?_
  rcases Finset.mem_Icc.mp hj with ⟨hj1,hjm⟩
  by_cases himk:i ≤ z174 n m
  ·
   have hphi:=hphi_le n p hpos (Int.fract (((m+27*n:ℕ):ℝ)/p))
    (Int.fract_nonneg _) (Int.fract_lt_one _)
   have hDB:=hDB_val p hphi.1.2
   have hc:=z34 (p:=p) hmlo hmhi hphi.1.1 hi1 himk
   have hj_val:z147 p (-((i+2:ℕ):ℤ)) ((1:ℚ)/(j:ℚ)^(i+2)):=by
    have h1:z147 p (-1) (1/((j:ℤ):ℚ)):=
     z155 (by omega) (by rw [Int.natAbs_natCast];omega)
    have hpow:=z156 h1 (i+2)
    have heq:(1/((j:ℤ):ℚ))^(i+2)=(1:ℚ)/(j:ℚ)^(i+2):=by
     push_cast;rw [one_div_pow]
    rw [heq] at hpow
    exact z151 (by omega) hpow
   have hmul:=z152 (z152 hDB hc) hj_val
   rw [← one_div]
   refine z151 ?_ hmul
   omega
  ·
   have h0:z32 n i m=0:=by
    unfold z32;rw [if_neg];intro h;exact himk h.2
   rw [h0,mul_zero,zero_mul];exact z158 p _
 rcases hconst_int with ⟨a0,ha0⟩
 rcases hzeta_int 3 (by omega) (by omega) with ⟨a5,ha5⟩
 rcases hzeta_int 5 (by omega) (by omega) with ⟨a7,ha7⟩
 rcases hzeta_int 7 (by omega) (by omega) with ⟨a9,ha9⟩
 rcases hzeta_int 9 (by omega) (by omega) with ⟨a11,ha11⟩
 refine ⟨a0,a5,a7,a9,a11,?_⟩
 rw [z6 hn]
 rw [ha0,ha5,ha7,ha9,ha11]
 ring
noncomputable def z88 (n:ℕ) (z:ℂ):ℂ:=
 ((-1:ℂ)^n)*Complex.cos ((Real.pi:ℂ)*z) *
  ((z286 n:ℚ):ℂ) *
  (((37*n:ℕ):ℂ)+2*z) *
  (Complex.Gamma z^3*Complex.Gamma ((27*n+1:ℕ)-z)^3 *
   (Complex.Gamma (z+(64*n+1:ℕ))/Complex.Gamma (z+(37*n+1:ℕ)))^3) *
  ∏ u∈Finset.Icc 1 10,
   (Complex.Gamma (z+((1+u)*n:ℕ))/Complex.Gamma (z+((36-u)*n+1:ℕ)))
private lemma z92 {z:ℂ} (hz:∀ k:ℕ,z≠(k:ℂ)) (N:ℕ) :
  Complex.Gamma ((N+1:ℕ)-z) =
   ((-1:ℂ)^N)*(∏ m∈Finset.Icc 1 N,(z-(m:ℂ)))*Complex.Gamma (1-z):=by
 induction N with
 | zero=>simp
 | succ N ih =>
  have harg:(((N+1+1:ℕ):ℂ)-z)=(((N+1:ℕ):ℂ)-z)+1:=by push_cast;ring
  have hne:(((N+1:ℕ):ℂ)-z)≠0:=by
   intro heq;exact hz (N+1) (sub_eq_zero.mp heq).symm
  rw [harg,Complex.Gamma_add_one _ hne,ih,Finset.prod_Icc_succ_top (by omega:1 ≤ N+1)]
  rw [pow_succ];push_cast;ring
private lemma z91 {z:ℂ} (hz:0< z.re) (a b:ℕ) (hab:a ≤ b) :
  (∏ m∈Finset.Icc a b,(z+(m:ℂ)))*Complex.Gamma (z+(a:ℂ)) =
   Complex.Gamma (z+((b+1:ℕ):ℂ)):=by
 induction b,hab using Nat.le_induction with
 | base =>
  simp only [Finset.Icc_self,Finset.prod_singleton]
  have harg:z+((a+1:ℕ):ℂ)=(z+(a:ℂ))+1:=by push_cast;ring
  have hne:z+(a:ℂ)≠0:=by
   intro h;have hre:=congr_arg Complex.re h;simp at hre;linarith
  rw [harg,Complex.Gamma_add_one _ hne]
 | succ k hle ih =>
  rw [Finset.prod_Icc_succ_top (by omega:a ≤ k+1),mul_right_comm,ih]
  have harg:z+((k+1+1:ℕ):ℂ)=(z+((k+1:ℕ):ℂ))+1:=by push_cast;ring
  have hne:z+((k+1:ℕ):ℂ)≠0:=by
   intro h;have hre:=congr_arg Complex.re h;simp at hre;linarith
  rw [harg,Complex.Gamma_add_one _ hne,mul_comm]
theorem z25 {n:ℕ} {z:ℂ}
  (hz_re:0< z.re) (hz_not_int:∀ k:ℤ,z≠(k:ℂ)) :
  z23 n z *
   ((Real.pi:ℂ)^3*Complex.cos ((Real.pi:ℂ)*z) /
    Complex.sin ((Real.pi:ℂ)*z)^3) =
  z88 n z:=by
 have hz_nat:∀ k:ℕ,z≠(k:ℂ):=fun k=>by simpa using hz_not_int (k:ℤ)
 have hGamma_pos_ne:∀ a:ℕ,Complex.Gamma (z+(a:ℂ))≠0:=fun a =>
  Complex.Gamma_ne_zero_of_re_pos (by simp;linarith)
 have hrefl:Complex.Gamma z*Complex.Gamma (1-z) =
   (Real.pi:ℂ)/Complex.sin ((Real.pi:ℂ)*z):=Complex.Gamma_mul_Gamma_one_sub z
 have hA_refl:(∏ m∈Finset.Icc 1 (27*n),(z-(m:ℂ))) *
   ((Real.pi:ℂ)/Complex.sin ((Real.pi:ℂ)*z)) =
   ((-1:ℂ)^(27*n))*(Complex.Gamma z*Complex.Gamma ((27*n+1:ℕ)-z)):=by
  rw [z92 hz_nat (27*n),← hrefl]
  have hs2:((-1:ℂ)^(27*n))*((-1:ℂ)^(27*n))=1:=by
   rw [← pow_add,← two_mul,pow_mul];norm_num
  linear_combination -(Complex.Gamma z*Complex.Gamma (1-z) *
   ∏ m∈Finset.Icc 1 (27*n),(z-(m:ℂ)))*hs2
 have hA3:(∏ m∈Finset.Icc 1 (27*n),(z-(m:ℂ)))^3 *
   ((Real.pi:ℂ)^3/Complex.sin ((Real.pi:ℂ)*z)^3) =
   ((-1:ℂ)^n)*(Complex.Gamma z^3*Complex.Gamma ((27*n+1:ℕ)-z)^3):=by
  have hcube:=congr_arg (fun w:ℂ=>w^3) hA_refl
  rw [mul_pow,div_pow,mul_pow,mul_pow,← pow_mul] at hcube
  have hpow81:((-1:ℂ)^(27*n*3))=(-1:ℂ)^n:=by
   rw [show 27*n*3=2*(40*n)+n by omega,pow_add,pow_mul]
   norm_num
  rwa [hpow81] at hcube
 have hB:(∏ m∈Finset.Icc (37*n+1) (64*n),(z+(m:ℂ))) =
   Complex.Gamma (z+(64*n+1:ℕ))/Complex.Gamma (z+(37*n+1:ℕ)):=by
  rcases eq_or_ne n 0 with rfl | hn0
  ·
   have hne1:Complex.Gamma (z+1)≠0:=by simpa using hGamma_pos_ne 1
   simp [hne1]
  ·
   rw [eq_div_iff (hGamma_pos_ne (37*n+1))]
   exact z91 hz_re (37*n+1) (64*n) (by omega)
 have hC:(∏ u∈Finset.Icc 1 10,∏ r∈Finset.Icc ((1+u)*n) ((36-u)*n),(z+(r:ℂ)))⁻¹ =
   ∏ u∈Finset.Icc 1 10,
    (Complex.Gamma (z+((1+u)*n:ℕ))/Complex.Gamma (z+((36-u)*n+1:ℕ))):=by
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun u hu=>?_
  have hab:(1+u)*n ≤ (36-u)*n:=Nat.mul_le_mul_right n (by have:=Finset.mem_Icc.mp hu;omega)
  have hprod:=z91 hz_re ((1+u)*n) ((36-u)*n) hab
  have hne2:=hGamma_pos_ne ((36-u)*n+1)
  have hprod_ne:(∏ r∈Finset.Icc ((1+u)*n) ((36-u)*n),(z+(r:ℂ)))≠0:=by
   intro h0;rw [h0,zero_mul] at hprod;exact hne2 hprod.symm
  rw [eq_div_iff hne2,inv_mul_eq_iff_eq_mul₀ hprod_ne]
  exact hprod.symm
 unfold z23 z88
 rw [div_eq_mul_inv,hC,hB]
 have hstep:(Real.pi:ℂ)^3*Complex.cos ((Real.pi:ℂ)*z)/Complex.sin ((Real.pi:ℂ)*z)^3 =
   ((Real.pi:ℂ)^3/Complex.sin ((Real.pi:ℂ)*z)^3)*Complex.cos ((Real.pi:ℂ)*z):=by ring
 rw [hstep]
 linear_combination ((z286 n:ℚ):ℂ)*(((37*n:ℕ):ℂ)+2*z) *
  (Complex.Gamma (z+(64*n+1:ℕ))/Complex.Gamma (z+(37*n+1:ℕ)))^3 *
  (∏ u∈Finset.Icc 1 10,
   (Complex.Gamma (z+((1+u)*n:ℕ))/Complex.Gamma (z+((36-u)*n+1:ℕ)))) *
  Complex.cos ((Real.pi:ℂ)*z)*hA3
theorem z7
  (hInt1:∀ (i:ℕ),1 ≤ i→ ∀ (M m:ℕ),0< m →
   Integrable (fun y:ℝ =>
    ((((M:ℂ)+1/2+(y:ℂ)*I)+(m:ℂ))⁻¹^i) *
     (2*(Real.pi:ℂ)^3*Complex.cos ((Real.pi:ℂ)*((M:ℂ)+1/2+(y:ℂ)*I)) /
      Complex.sin ((Real.pi:ℂ)*((M:ℂ)+1/2+(y:ℂ)*I))^3)) ∧
   ∫ y:ℝ,((((M:ℂ)+1/2+(y:ℂ)*I)+(m:ℂ))⁻¹^i) *
     (2*(Real.pi:ℂ)^3*Complex.cos ((Real.pi:ℂ)*((M:ℂ)+1/2+(y:ℂ)*I)) /
      Complex.sin ((Real.pi:ℂ)*((M:ℂ)+1/2+(y:ℂ)*I))^3) =
    -2*(Real.pi:ℂ) *
     ∑' t:ℕ,((i*(i+1):ℕ):ℂ)/((((M+t+1:ℕ):ℂ)+(m:ℂ))^(i+2)))
  {n M:ℕ} (hn:1 ≤ n) (hM:M ≤ 27*n) :
  Integrable (fun y:ℝ=>z88 n ((M:ℂ)+1/2+(y:ℂ)*I)) ∧
  ((z3 n:ℂ)) =
   -(1/(2*(Real.pi:ℂ))) *
    ∫ y:ℝ,z88 n ((M:ℂ)+1/2+(y:ℂ)*I):=by
 let z:ℝ→ ℂ:=fun y=>(M:ℂ)+1/2+(y:ℂ)*I
 let K:ℝ→ ℂ:=fun y =>
  2*(Real.pi:ℂ)^3*Complex.cos ((Real.pi:ℂ)*z y) /
   Complex.sin ((Real.pi:ℂ)*z y)^3
 have hz_re:∀ y:ℝ,0< (z y).re:=fun y=>by
  simp only [z,Complex.add_re,Complex.natCast_re,Complex.div_ofNat_re,Complex.one_re,
   Complex.mul_re,Complex.ofReal_re,Complex.I_re,mul_zero,Complex.ofReal_im,Complex.I_im,
   mul_one,sub_self,add_zero]
  positivity
 have hz_not_int:∀ (y:ℝ) (k:ℤ),z y≠(k:ℂ):=by
  intro y k heq
  have hre:=congr_arg Complex.re heq
  simp only [z,Complex.add_re,Complex.natCast_re,Complex.div_ofNat_re,Complex.one_re,
   Complex.mul_re,Complex.ofReal_re,Complex.I_re,mul_zero,Complex.ofReal_im,Complex.I_im,
   mul_one,sub_self,add_zero,Complex.intCast_re] at hre
  have h2:2*(M:ℤ)+1=2*k:=by
   have:(2*(M:ℝ)+1)=2*(k:ℝ):=by linarith
   exact_mod_cast this
  omega
 have hz_ne_neg:∀ (y:ℝ),∀ m∈Finset.Icc (2*n) (35*n),z y+(m:ℂ)≠0:=by
  intro y m _ heq
  have hre:=congr_arg Complex.re heq
  simp only [Complex.add_re,Complex.natCast_re,Complex.zero_re] at hre
  have:=hz_re y;linarith [Nat.cast_nonneg (α:=ℝ) m]
 have hpt:∀ y:ℝ,
   2*z88 n (z y) =
    ∑ m∈Finset.Icc (2*n) (35*n),∑ i∈Finset.Icc 1 10,
     ((z32 n i m:ℚ):ℂ)*(((z y+(m:ℂ))⁻¹^i)*K y):=by
  intro y
  rw [← z25 (hz_re y) (hz_not_int y)]
  rw [z24 hn (hz_ne_neg y)]
  have hK:2*(z23 n (z y) *
    ((Real.pi:ℂ)^3*Complex.cos ((Real.pi:ℂ)*z y) /
     Complex.sin ((Real.pi:ℂ)*z y)^3)) =
    z23 n (z y)*K y:=by
   dsimp only [K];ring
  rw [← z24 hn (hz_ne_neg y),hK,z24 hn (hz_ne_neg y)]
  simp_rw [Finset.sum_mul,mul_assoc]
 have hint_term:∀ m∈Finset.Icc (2*n) (35*n),∀ i∈Finset.Icc 1 10,
   Integrable (fun y:ℝ=>((z32 n i m:ℚ):ℂ)*(((z y+(m:ℂ))⁻¹^i)*K y)):=by
  intro m hm i hi
  have hm_pos:0< m:=by have:=(Finset.mem_Icc.mp hm).1;omega
  exact ((hInt1 i (Finset.mem_Icc.mp hi).1 M m hm_pos).1).const_mul _
 have hint_two:Integrable (fun y:ℝ=>2*z88 n (z y)):=by
  rw [show (fun y:ℝ=>2*z88 n (z y)) =
    (fun y:ℝ=>∑ m∈Finset.Icc (2*n) (35*n),∑ i∈Finset.Icc 1 10,
     ((z32 n i m:ℚ):ℂ)*(((z y+(m:ℂ))⁻¹^i)*K y)) from funext hpt]
  exact integrable_finset_sum _ fun m hm=>integrable_finset_sum _ fun i hi=>hint_term m hm i hi
 have hint_gamma:Integrable (fun y:ℝ=>z88 n (z y)):=by
  have:=hint_two.const_mul (1/2:ℂ)
  refine this.congr (Filter.Eventually.of_forall fun y=>by ring)
 refine ⟨hint_gamma,?_⟩
 have hint_eq:∫ y:ℝ,2*z88 n (z y) =
   -2*(Real.pi:ℂ) *
    ∑ m∈Finset.Icc (2*n) (35*n),∑ i∈Finset.Icc 1 10,
     ((z32 n i m:ℚ):ℂ) *
      ∑' t:ℕ,((i*(i+1):ℕ):ℂ)/((((M+t+1:ℕ):ℂ)+(m:ℂ))^(i+2)):=by
  rw [show (fun y:ℝ=>2*z88 n (z y)) =
    (fun y:ℝ=>∑ m∈Finset.Icc (2*n) (35*n),∑ i∈Finset.Icc 1 10,
     ((z32 n i m:ℚ):ℂ)*(((z y+(m:ℂ))⁻¹^i)*K y)) from funext hpt]
  rw [integral_finset_sum _ (fun m hm=>integrable_finset_sum _ fun i hi=>hint_term m hm i hi)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm=>?_
  rw [integral_finset_sum _ (fun i hi=>hint_term m hm i hi),Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi=>?_
  have hm_pos:0< m:=by have:=(Finset.mem_Icc.mp hm).1;omega
  rw [integral_const_mul,(hInt1 i (Finset.mem_Icc.mp hi).1 M m hm_pos).2]
  ring
 have htsum_eq:(∑ m∈Finset.Icc (2*n) (35*n),∑ i∈Finset.Icc 1 10,
   ((z32 n i m:ℚ):ℂ) *
    ∑' t:ℕ,((i*(i+1):ℕ):ℂ)/((((M+t+1:ℕ):ℂ)+(m:ℂ))^(i+2))) =
   ((2*z3 n:ℝ):ℂ):=by
  have hreal_term:∀ m∈Finset.Icc (2*n) (35*n),∀ i∈Finset.Icc 1 10,
    ((z32 n i m:ℚ):ℂ) *
     (∑' t:ℕ,((i*(i+1):ℕ):ℂ)/((((M+t+1:ℕ):ℂ)+(m:ℂ))^(i+2))) =
    (((∑' t:ℕ,((i*(i+1):ℕ):ℝ)*((z32 n i m:ℚ):ℝ) /
      ((((M+t:ℕ):ℝ)+1)+(m:ℝ))^(i+2)):ℝ):ℂ):=by
   intro m _ i _
   rw [Complex.ofReal_tsum,← tsum_mul_left]
   congr 1;ext t
   push_cast;ring
  rw [Finset.sum_congr rfl fun m hm=>Finset.sum_congr rfl fun i hi=>hreal_term m hm i hi]
  simp_rw [← Complex.ofReal_sum]
  congr 1
  have hsumm:∀ m∈Finset.Icc (2*n) (35*n),∀ i∈Finset.Icc 1 10,
    Summable (fun t:ℕ=>((i*(i+1):ℕ):ℝ)*((z32 n i m:ℚ):ℝ) /
     ((((M+t:ℕ):ℝ)+1)+(m:ℝ))^(i+2)):=by
   intro m _ i hi
   have h1:=(z266 (j:=i+2) (by omega) (M+m)).mul_left
    (((i*(i+1):ℕ):ℝ)*((z32 n i m:ℚ):ℝ))
   refine h1.congr fun t=>?_
   push_cast;ring
  have hswap:(∑ m∈Finset.Icc (2*n) (35*n),∑ i∈Finset.Icc 1 10,
    ∑' t:ℕ,((i*(i+1):ℕ):ℝ)*((z32 n i m:ℚ):ℝ) /
     ((((M+t:ℕ):ℝ)+1)+(m:ℝ))^(i+2)) =
    ∑' t:ℕ,z21 n (((M+t:ℕ):ℝ)+1):=by
   unfold z21
   have hhas:HasSum (fun t:ℕ=>∑ m∈Finset.Icc (2*n) (35*n),∑ i∈Finset.Icc 1 10,
     ((i*(i+1):ℕ):ℝ)*((z32 n i m:ℚ):ℝ) /
      ((((M+t:ℕ):ℝ)+1)+(m:ℝ))^(i+2))
     (∑ m∈Finset.Icc (2*n) (35*n),∑ i∈Finset.Icc 1 10,
      ∑' t:ℕ,((i*(i+1):ℕ):ℝ)*((z32 n i m:ℚ):ℝ) /
       ((((M+t:ℕ):ℝ)+1)+(m:ℝ))^(i+2)):=
    hasSum_sum fun m hm=>hasSum_sum fun i hi=>(hsumm m hm i hi).hasSum
   exact hhas.tsum_eq.symm
  rw [hswap]
  have hsumm_all:Summable (fun k:ℕ=>z21 n ((k:ℝ)+1)):=by
   unfold z21
   refine summable_sum fun m hm=>summable_sum fun i hi=>?_
   have h1:=(z266 (j:=i+2) (by omega) m).mul_left
    (((i*(i+1):ℕ):ℝ)*((z32 n i m:ℚ):ℝ))
   refine h1.congr fun k=>by ring
  have hsplit:=hsumm_all.sum_add_tsum_nat_add M
  have hhead:∑ k∈Finset.range M,z21 n ((k:ℝ)+1)=0:=by
   refine Finset.sum_eq_zero fun k hk=>?_
   have hkM:k< M:=Finset.mem_range.mp hk
   have hcast:(k:ℝ)+1=((k+1:ℕ):ℝ):=by push_cast;rfl
   rw [hcast]
   exact z22 hn (by omega) (by omega)
  rw [hhead,zero_add] at hsplit
  have hcomm:(fun t:ℕ=>z21 n (((M+t:ℕ):ℝ)+1)) =
    (fun t:ℕ=>z21 n (((t+M:ℕ):ℝ)+1)):=by
   ext t;rw [add_comm M t]
  rw [hcomm,hsplit]
  unfold z3;ring
 rw [integral_const_mul,htsum_eq] at hint_eq
 have hpi:(Real.pi:ℂ)≠0:=Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
 have h2pi:(2:ℂ)*(Real.pi:ℂ)≠0:=mul_ne_zero two_ne_zero hpi
 push_cast at hint_eq
 change ((z3 n:ℂ))=-(1/(2*(Real.pi:ℂ)))*∫ y:ℝ,z88 n (z y)
 have hmul:(2*(Real.pi:ℂ))*((z3 n:ℂ)) =
   (2*(Real.pi:ℂ))*(-(1/(2*(Real.pi:ℂ)))*∫ y:ℝ,z88 n (z y)):=by
  have hcancel:(2*(Real.pi:ℂ))*(-(1/(2*(Real.pi:ℂ)))*∫ y:ℝ,z88 n (z y)) =
    -(∫ y:ℝ,z88 n (z y)):=by
   rw [← mul_assoc,mul_neg,mul_one_div_cancel h2pi];ring
  rw [hcancel]
  linear_combination hint_eq/2
 exact mul_left_cancel₀ h2pi hmul
end Z4
namespace Z5
open scoped BigOperators Real Topology
open Complex Filter Finset MeasureTheory Set
lemma z257 {z:ℂ} (hz:0< z.re):z∈Complex.slitPlane:=
 Or.inl hz
lemma z31 {z:ℂ} (hz:0< z.re) :
  -(Real.pi/2)< Complex.arg z∧Complex.arg z< Real.pi/2:=by
 have hz0:z≠0:=by intro h;simp [h] at hz
 have hcos:0< Real.cos (Complex.arg z):=by
  rw [Complex.cos_arg hz0]
  exact div_pos hz (norm_pos_iff.mpr hz0)
 have hlt1:=Complex.neg_pi_lt_arg z
 have hle2:=Complex.arg_le_pi z
 constructor
 ·
  by_contra! hle
  have hcos_le:Real.cos (Complex.arg z) ≤ 0:=by
   rw [← Real.cos_neg]
   exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
  linarith
 ·
  by_contra! hge
  have hcos_le:Real.cos (Complex.arg z) ≤ 0:=
   Real.cos_nonpos_of_pi_div_two_le_of_le hge (by linarith [Real.pi_pos])
  linarith
lemma z30 {z:ℂ} (hz:0< z.re) :
  Complex.arg z=Real.arctan (z.im/z.re):=by
 have hz0:z≠0:=by intro h;simp [h] at hz
 have hbd:=z31 hz
 have htan:Real.tan (Complex.arg z)=z.im/z.re:=by
  rw [Real.tan_eq_sin_div_cos,Complex.sin_arg,Complex.cos_arg hz0]
  field_simp [(norm_pos_iff.mpr hz0).ne',hz.ne']
 rw [← htan,Real.arctan_tan hbd.1 hbd.2]
lemma z125 {a b:ℂ} (ha:0< a.re) (hb:0< b.re) :
  Complex.log (a*b)=Complex.log a+Complex.log b:=by
 have ha0:a≠0:=by intro h;simp [h] at ha
 have hb0:b≠0:=by intro h;simp [h] at hb
 have hba:=z31 ha
 have hbb:=z31 hb
 have hexp:Complex.exp (Complex.log a+Complex.log b)=a*b:=by
  rw [Complex.exp_add,Complex.exp_log ha0,Complex.exp_log hb0]
 rw [← hexp,Complex.log_exp]
 ·
  simp only [Complex.add_im,Complex.log_im];linarith
 ·
  simp only [Complex.add_im,Complex.log_im];linarith
lemma z123 {a b:ℂ} (ha:0< a.re) (hb:0< b.re) :
  Complex.log (a/b)=Complex.log a-Complex.log b:=by
 have hb0:b≠0:=by intro h;simp [h] at hb
 have hinv_re:0< b⁻¹.re:=by
  rw [Complex.inv_re]
  exact div_pos hb (Complex.normSq_pos.mpr hb0)
 rw [div_eq_mul_inv,z125 ha hinv_re]
 have h1:Complex.log b+Complex.log b⁻¹=0:=by
  rw [← z125 hb hinv_re,mul_inv_cancel₀ hb0,Complex.log_one]
 linear_combination h1
lemma z126 {u:ℂ} (hu:‖u‖ ≤ 1/2) :
  Complex.log (1+u)=∫ t in (0:ℝ)..1,u/(1+(t:ℂ)*u):=by
 have hre:∀ t∈Set.uIcc (0:ℝ) 1,(1/2:ℝ) ≤ (1+(t:ℂ)*u).re:=by
  intro t ht
  rw [Set.uIcc_of_le (by norm_num:(0:ℝ) ≤ 1)] at ht
  have h1:‖(t:ℂ)*u‖ ≤ 1/2:=by
   rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ht.1]
   nlinarith [ht.2,norm_nonneg u]
  have hre_le:|(t*u:ℂ).re| ≤ 1/2:=(Complex.abs_re_le_norm _).trans h1
  simp only [Complex.add_re,Complex.one_re]
  linarith [abs_le.mp hre_le]
 have hderiv:∀ t∈Set.uIcc (0:ℝ) 1,
   HasDerivAt (fun x:ℝ=>Complex.log (1+(x:ℂ)*u))
    (u/(1+(t:ℂ)*u)) t:=by
  intro t ht
  have hslit:1+(t:ℂ)*u∈Complex.slitPlane:=
   z257 (by linarith [hre t ht])
  have hlin:HasDerivAt (fun x:ℝ=>1+(x:ℂ)*u) u t:=by
   have h1:HasDerivAt (fun x:ℝ=>(x:ℂ)) 1 t:=Complex.ofRealCLM.hasDerivAt
   have h2:=(h1.mul_const u).const_add (1:ℂ)
   rw [one_mul] at h2
   exact h2
  have hcomp:=(Complex.hasDerivAt_log hslit).comp t hlin
  rw [div_eq_mul_inv,mul_comm]
  exact hcomp
 have hint:IntervalIntegrable (fun t:ℝ=>u/(1+(t:ℂ)*u)) volume 0 1:=by
  refine ContinuousOn.intervalIntegrable ?_
  refine continuousOn_const.div (continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)) ?_
  intro t ht heq
  have h1:=congr_arg Complex.re heq
  have h2:=hre t ht
  rw [Complex.zero_re] at h1
  linarith
 have hftc:=intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
 simp only [Complex.ofReal_one,one_mul,Complex.ofReal_zero,zero_mul,add_zero,
  Complex.log_one,sub_zero] at hftc
 exact hftc.symm
lemma z140 {u:ℂ} (hu:‖u‖ ≤ 1/2) :
  ‖Complex.log (1+u)‖ ≤ 2*‖u‖:=by
 rw [z126 hu]
 have hbd:∀ t∈Set.uIoc (0:ℝ) 1,‖u/(1+(t:ℂ)*u)‖ ≤ 2*‖u‖:=by
  intro t ht
  rw [Set.uIoc_of_le (by norm_num:(0:ℝ) ≤ 1)] at ht
  have hnorm_den:(1/2:ℝ) ≤ ‖1+(t:ℂ)*u‖:=by
   have h1:‖(t:ℂ)*u‖ ≤ 1/2:=by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ht.1.le]
    nlinarith [ht.2,norm_nonneg u]
   have h2:=norm_sub_norm_le (1:ℂ) (-(t:ℂ)*u)
   simp only [sub_neg_eq_add,norm_one,neg_mul,norm_neg] at h2
   linarith
  rw [norm_div]
  calc
   ‖u‖ / ‖1+(t:ℂ)*u‖ ≤ ‖u‖ / (1/2):=
     div_le_div_of_nonneg_left (norm_nonneg u) (by norm_num) hnorm_den
   _=2*‖u‖:=by ring
 have h:=intervalIntegral.norm_integral_le_of_norm_le_const hbd
 simpa using h
lemma z141 {u:ℂ} (hu:‖u‖ ≤ 1/2) :
  ‖Complex.log (1+u)-u‖ ≤ 2*‖u‖^2:=by
 rw [z126 hu]
 have hint1:IntervalIntegrable (fun t:ℝ=>u/(1+(t:ℂ)*u)) volume 0 1:=by
  refine ContinuousOn.intervalIntegrable ?_
  refine continuousOn_const.div
   (continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)) ?_
  intro t ht heq
  rw [Set.uIcc_of_le (by norm_num:(0:ℝ) ≤ 1)] at ht
  have h1:‖(t:ℂ)*u‖ ≤ 1/2:=by
   rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ht.1]
   nlinarith [ht.2,norm_nonneg u]
  have:=congr_arg Complex.re heq
  have hre_le:|(t*u:ℂ).re| ≤ 1/2:=(Complex.abs_re_le_norm _).trans h1
  simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at this
  linarith [abs_le.mp hre_le]
 have hsub_int:(∫ t in (0:ℝ)..1,u/(1+(t:ℂ)*u))-u =
   ∫ t in (0:ℝ)..1,(u/(1+(t:ℂ)*u)-u):=by
  rw [intervalIntegral.integral_sub hint1 intervalIntegrable_const]
  simp
 rw [hsub_int]
 have hbd:∀ t∈Set.uIoc (0:ℝ) 1,‖u/(1+(t:ℂ)*u)-u‖ ≤ 2*‖u‖^2:=by
  intro t ht
  rw [Set.uIoc_of_le (by norm_num:(0:ℝ) ≤ 1)] at ht
  have hnorm_den:(1/2:ℝ) ≤ ‖1+(t:ℂ)*u‖:=by
   have h1:‖(t:ℂ)*u‖ ≤ 1/2:=by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ht.1.le]
    nlinarith [ht.2,norm_nonneg u]
   have h2:=norm_sub_norm_le (1:ℂ) (-(t:ℂ)*u)
   simp only [sub_neg_eq_add,norm_one,neg_mul,norm_neg] at h2
   linarith
  have hden_ne:1+(t:ℂ)*u≠0:=norm_pos_iff.mp (by linarith)
  have hsub:u/(1+(t:ℂ)*u)-u=-((t:ℂ)*u^2)/(1+(t:ℂ)*u):=by
   rw [eq_div_iff hden_ne,sub_mul,div_mul_cancel₀ _ hden_ne];ring
  rw [hsub,norm_div,norm_neg,norm_mul,Complex.norm_real,Real.norm_of_nonneg ht.1.le,norm_pow]
  calc
   t*‖u‖^2 / ‖1+(t:ℂ)*u‖
    ≤ 1*‖u‖^2/(1/2):=by
     refine div_le_div₀ (by positivity) (by nlinarith [ht.2,sq_nonneg ‖u‖]) (by norm_num) hnorm_den
   _=2*‖u‖^2:=by ring
 have h:=intervalIntegral.norm_integral_le_of_norm_le_const hbd
 simpa using h
noncomputable def z261 (z:ℂ):ℂ:=
 (z+1/2)*Complex.log (1+1/z)-1
lemma z144 {z:ℂ} (hz:2 ≤ ‖z‖) :
  ‖z261 z‖ ≤ 1 / ‖z‖^2:=by
 have hz0:z≠0:=norm_pos_iff.mp (by linarith)
 set u:ℂ:=1/z
 have hu:‖u‖ ≤ 1/2:=by
  simp only [u,one_div,norm_inv]
  exact inv_le_of_inv_le₀ (by norm_num) (by norm_num;exact hz)
 have hden_ge:∀ t∈Set.uIcc (0:ℝ) 1,(1/2:ℝ) ≤ ‖1+(t:ℂ)*u‖:=by
  intro t ht
  rw [Set.uIcc_of_le (by norm_num:(0:ℝ) ≤ 1)] at ht
  have h1:‖(t:ℂ)*u‖ ≤ 1/2:=by
   rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ht.1]
   nlinarith [ht.2,norm_nonneg u]
  have h2:=norm_sub_norm_le (1:ℂ) (-(t:ℂ)*u)
  simp only [sub_neg_eq_add,norm_one,neg_mul,norm_neg] at h2
  linarith
 have hden_ne:∀ t∈Set.uIcc (0:ℝ) 1,1+(t:ℂ)*u≠0:=fun t ht =>
  norm_pos_iff.mp (by linarith [hden_ge t ht])
 have hint_f:IntervalIntegrable (fun t:ℝ=>(1/2-(t:ℂ))*u/(1+(t:ℂ)*u)) volume 0 1:=by
  refine ContinuousOn.intervalIntegrable ?_
  refine ((continuousOn_const.sub Complex.continuous_ofReal.continuousOn).mul continuousOn_const).div
   (continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const))
   (fun t ht=>hden_ne t ht)
 have hint_f':IntervalIntegrable (fun t:ℝ=>(1/2-((1-t:ℝ):ℂ))*u/(1+((1-t:ℝ):ℂ)*u)) volume 0 1:=by
  refine ContinuousOn.intervalIntegrable ?_
  have hc:Continuous (fun t:ℝ=>((1-t:ℝ):ℂ)):=
   Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)
  refine ((continuousOn_const.sub hc.continuousOn).mul continuousOn_const).div
   (continuousOn_const.add (hc.continuousOn.mul continuousOn_const)) ?_
  intro t ht
  rw [Set.uIcc_of_le (by norm_num:(0:ℝ) ≤ 1)] at ht
  exact hden_ne (1-t) (by rw [Set.uIcc_of_le (by norm_num:(0:ℝ) ≤ 1)];constructor <;> linarith [ht.1,ht.2])
 have hg_int:z261 z=∫ t in (0:ℝ)..1,(1/2-(t:ℂ))*u/(1+(t:ℂ)*u):=by
  unfold z261
  rw [show (1:ℂ)/z=u from rfl,z126 hu,
   ← intervalIntegral.integral_const_mul]
  have hint1:IntervalIntegrable (fun t:ℝ=>(z+1/2)*(u/(1+(t:ℂ)*u))) volume 0 1:=by
   refine ContinuousOn.intervalIntegrable ?_
   refine continuousOn_const.mul (continuousOn_const.div
    (continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const))
    (fun t ht=>hden_ne t ht))
  have hsub1:(∫ t in (0:ℝ)..1,(z+1/2)*(u/(1+(t:ℂ)*u)))-1 =
    ∫ t in (0:ℝ)..1,((z+1/2)*(u/(1+(t:ℂ)*u))-1):=by
   rw [intervalIntegral.integral_sub hint1 intervalIntegrable_const]
   simp
  rw [hsub1]
  refine intervalIntegral.integral_congr fun t ht=>?_
  have hne:=hden_ne t ht
  have hzu:z*u=1:=mul_one_div_cancel hz0
  rw [eq_div_iff hne,sub_mul,mul_assoc,div_mul_cancel₀ _ hne]
  calc
   (z+1/2)*u-1*(1+(t:ℂ)*u)
    = z*u+(1/2-(t:ℂ))*u-1:=by ring
   _=(1/2-(t:ℂ))*u:=by rw [hzu];ring
 have hsymm:(∫ t in (0:ℝ)..1,(1/2-(t:ℂ))*u/(1+(t:ℂ)*u)) =
   ∫ t in (0:ℝ)..1,(1/2-((1-t:ℝ):ℂ))*u/(1+((1-t:ℝ):ℂ)*u):=by
  have h:=intervalIntegral.integral_comp_sub_left
   (f:=fun t:ℝ=>(1/2-(t:ℂ))*u/(1+(t:ℂ)*u)) (a:=0) (b:=1) (1:ℝ)
  simpa using h.symm
 have havg:z261 z =
   ∫ t in (0:ℝ)..1,
    ((1/2-(t:ℂ))^2*u^2)/((1+(t:ℂ)*u)*(1+((1-t:ℝ):ℂ)*u)):=by
  have h2:2*z261 z =
    ∫ t in (0:ℝ)..1,
     ((1/2-(t:ℂ))*u/(1+(t:ℂ)*u) +
      (1/2-((1-t:ℝ):ℂ))*u/(1+((1-t:ℝ):ℂ)*u)):=by
   rw [intervalIntegral.integral_add hint_f hint_f',← hsymm,← hg_int];ring
  have hcongr:(∫ t in (0:ℝ)..1,
     ((1/2-(t:ℂ))*u/(1+(t:ℂ)*u) +
      (1/2-((1-t:ℝ):ℂ))*u/(1+((1-t:ℝ):ℂ)*u))) =
    ∫ t in (0:ℝ)..1,
     2*(((1/2-(t:ℂ))^2*u^2)/((1+(t:ℂ)*u)*(1+((1-t:ℝ):ℂ)*u))):=by
   refine intervalIntegral.integral_congr fun t ht=>?_
   have hne1:=hden_ne t ht
   rw [Set.uIcc_of_le (by norm_num:(0:ℝ) ≤ 1)] at ht
   have hne2:=hden_ne (1-t) (by rw [Set.uIcc_of_le (by norm_num:(0:ℝ) ≤ 1)];constructor <;> linarith [ht.1,ht.2])
   rw [div_add_div _ _ hne1 hne2,← mul_div_assoc]
   push_cast;ring
  rw [hcongr,intervalIntegral.integral_const_mul] at h2
  exact mul_left_cancel₀ (two_ne_zero) h2
 rw [havg]
 have hbd:∀ t∈Set.uIoc (0:ℝ) 1,
   ‖((1/2-(t:ℂ))^2*u^2)/((1+(t:ℂ)*u)*(1+((1-t:ℝ):ℂ)*u))‖ ≤
    1 / ‖z‖^2:=by
  intro t ht
  rw [Set.uIoc_of_le (by norm_num:(0:ℝ) ≤ 1)] at ht
  have h1:=hden_ge t (by rw [Set.uIcc_of_le (by norm_num:(0:ℝ) ≤ 1)];exact ⟨ht.1.le,ht.2⟩)
  have h2:=hden_ge (1-t) (by rw [Set.uIcc_of_le (by norm_num:(0:ℝ) ≤ 1)];constructor <;> linarith [ht.1,ht.2])
  have hnum:‖(1/2-(t:ℂ))^2‖ ≤ 1/4:=by
   have hreal:(1/2-(t:ℂ))=(((1/2-t:ℝ):ℂ)):=by push_cast;rfl
   rw [hreal,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
   nlinarith [ht.1,ht.2]
  have hu2:‖u^2‖=1 / ‖z‖^2:=by simp [u,norm_pow,one_div]
  rw [norm_div,norm_mul,norm_mul,hu2]
  calc
   ‖(1/2-(t:ℂ))^2‖*(1 / ‖z‖^2)/(‖1+(t:ℂ)*u‖*‖1+((1-t:ℝ):ℂ)*u‖)
    ≤ (1/4)*(1 / ‖z‖^2)/((1/2)*(1/2)):=by
     refine div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_right hnum (by positivity)) (by norm_num)
      (mul_le_mul h1 h2 (by norm_num) (by linarith))
   _=1 / ‖z‖^2:=by ring
 have h:=intervalIntegral.norm_integral_le_of_norm_le_const hbd
 simpa using h
noncomputable def z260 (s:ℂ):ℂ:=
 ∑' k:ℕ,z261 (s+(k:ℂ))
private lemma z137 {s:ℂ} (hre:0< s.re) (k:ℕ) :
  (‖s‖+(k:ℝ))^2/2 ≤ ‖s+(k:ℂ)‖^2:=by
 have hsq:‖s+(k:ℂ)‖^2=‖s‖^2+2*(k:ℝ)*s.re+(k:ℝ)^2:=by
  rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
  simp only [Complex.add_re,Complex.natCast_re,Complex.add_im,Complex.natCast_im,add_zero]
  ring
 rw [hsq]
 nlinarith [sq_nonneg (‖s‖ - (k:ℝ)),Nat.cast_nonneg (α:=ℝ) k]
private lemma z136 {s:ℂ} (hre:0< s.re) (k:ℕ) :
  ‖s‖ ≤ ‖s+(k:ℂ)‖:=by
 have hsq:‖s+(k:ℂ)‖^2=‖s‖^2+2*(k:ℝ)*s.re+(k:ℝ)^2:=by
  rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
  simp only [Complex.add_re,Complex.natCast_re,Complex.add_im,Complex.natCast_im,add_zero]
  ring
 nlinarith [norm_nonneg s,norm_nonneg (s+(k:ℂ)),Nat.cast_nonneg (α:=ℝ) k]
private lemma z267 {s:ℂ} (hre:0< s.re) (hnorm:2 ≤ ‖s‖) :
  Summable (fun k:ℕ=>z261 (s+(k:ℂ))):=by
 refine Summable.of_norm_bounded (g:=fun k:ℕ=>2/((k:ℝ)+1)^2) ?_ ?_
 ·
  have h:=(Real.summable_nat_pow_inv.mpr (show 1< 2 by norm_num)).mul_left 2
  have hshift:=(summable_nat_add_iff 1).mpr h
  refine hshift.congr fun k=>by push_cast;rw [div_eq_mul_inv]
 ·
  intro k
  have hge:=z137 hre k
  have hnorm_k:2 ≤ ‖s+(k:ℂ)‖:=hnorm.trans (z136 hre k)
  calc
   ‖z261 (s+(k:ℂ))‖ ≤ 1 / ‖s+(k:ℂ)‖^2:=z144 hnorm_k
   _ ≤ 1/((‖s‖+(k:ℝ))^2/2):=
    div_le_div_of_nonneg_left zero_le_one (by positivity) hge
   _=2/(‖s‖+(k:ℝ))^2:=by rw [div_div_eq_mul_div,one_mul]
   _ ≤ 2/((k:ℝ)+1)^2:=by
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    nlinarith [Nat.cast_nonneg (α:=ℝ) k]
lemma z143 {s:ℂ} (hre:0< s.re) (hnorm:2 ≤ ‖s‖) :
  ‖z260 s‖ ≤ 6 / ‖s‖:=by
 have hsumm:=z267 hre hnorm
 have hshift:=hsumm.norm.sum_add_tsum_nat_add 1
 have htel:HasSum (fun k:ℕ=>2*(1/(‖s‖+(k:ℝ))-1/(‖s‖+((k+1:ℕ):ℝ))))
   (2 / ‖s‖):=by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  ·
   have hpart:∀ N:ℕ,
     ∑ k∈Finset.range N,2*(1/(‖s‖+(k:ℝ))-1/(‖s‖+((k+1:ℕ):ℝ))) =
     2 / ‖s‖ - 2/(‖s‖+(N:ℝ)):=by
    intro N;induction N with
    | zero=>simp
    | succ N ih =>
     rw [Finset.sum_range_succ,ih];ring
   simp_rw [hpart]
   have h0:Tendsto (fun N:ℕ=>2/(‖s‖+(N:ℝ))) atTop (𝓝 0):=by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=(2:ℝ))).mul
     (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ ‖s‖ tendsto_natCast_atTop_atTop))
   simpa using tendsto_const_nhds.sub h0
  ·
   intro k
   have hk:(0:ℝ) ≤ k:=Nat.cast_nonneg k
   have h1:1/(‖s‖+((k+1:ℕ):ℝ)) ≤ 1/(‖s‖+(k:ℝ)):=
    div_le_div_of_nonneg_left zero_le_one (by linarith) (by push_cast;linarith)
   linarith
 have htail_le:∑' k:ℕ,‖z261 (s+((k+1:ℕ):ℂ))‖ ≤ 2 / ‖s‖:=by
  rw [← htel.tsum_eq]
  refine Summable.tsum_le_tsum (fun k=>?_) ((summable_nat_add_iff 1).mpr hsumm.norm) htel.summable
  have hge:=z137 hre (k+1)
  have hnorm_k:2 ≤ ‖s+((k+1:ℕ):ℂ)‖:=hnorm.trans (z136 hre (k+1))
  have hd1:0 < ‖s‖+(k:ℝ):=by linarith [Nat.cast_nonneg (α:=ℝ) k]
  have hd2:0 < ‖s‖+((k+1:ℕ):ℝ):=by push_cast;linarith [Nat.cast_nonneg (α:=ℝ) k]
  have hdiff:2*(1/(‖s‖+(k:ℝ))-1/(‖s‖+((k+1:ℕ):ℝ))) =
    2/((‖s‖+(k:ℝ))*(‖s‖+((k+1:ℕ):ℝ))):=by
   field_simp [hd1.ne',hd2.ne'];push_cast;ring
  rw [hdiff]
  calc
   ‖z261 (s+((k+1:ℕ):ℂ))‖
    ≤ 1 / ‖s+((k+1:ℕ):ℂ)‖^2:=z144 hnorm_k
   _ ≤ 2/(‖s‖+((k+1:ℕ):ℝ))^2:=by
     have:1/((‖s‖+((k+1:ℕ):ℝ))^2/2)=2/(‖s‖+((k+1:ℕ):ℝ))^2:=by
      rw [div_div_eq_mul_div,one_mul]
     rw [← this]
     exact div_le_div_of_nonneg_left zero_le_one (by positivity) hge
   _ ≤ 2/((‖s‖+(k:ℝ))*(‖s‖+((k+1:ℕ):ℝ))):=by
     refine div_le_div_of_nonneg_left (by norm_num) (mul_pos hd1 hd2) ?_
     push_cast;nlinarith [hd2]
 have h0_le:‖z261 s‖ ≤ 1 / ‖s‖:=by
  calc
   ‖z261 s‖ ≤ 1 / ‖s‖^2:=z144 hnorm
   _ ≤ 1 / ‖s‖:=div_le_div_of_nonneg_left zero_le_one (by linarith) (by nlinarith)
 calc
  ‖z260 s‖
   ≤ ∑' k:ℕ,‖z261 (s+(k:ℂ))‖:=norm_tsum_le_tsum_norm hsumm.norm
  _=‖z261 s‖+∑' k:ℕ,‖z261 (s+((k+1:ℕ):ℂ))‖:=by
    simpa using hshift.symm
  _ ≤ 1 / ‖s‖+2 / ‖s‖:=add_le_add h0_le htail_le
  _ ≤ 6 / ‖s‖:=by
    have:(0:ℝ) < ‖s‖:=by linarith
    rw [← add_div];exact div_le_div_of_nonneg_right (by norm_num) this.le
theorem z49 {s:ℂ} (hre:0< s.re) (hnorm:2 ≤ ‖s‖) :
  Complex.Gamma s =
   ((Real.sqrt (2*Real.pi):ℝ):ℂ) *
    Complex.exp ((s-1/2)*Complex.log s-s+z260 s):=by
 let F:ℂ→ ℂ:=fun z =>
  Complex.Gamma z*Complex.exp (-((z-1/2)*Complex.log z-z+z260 z))
 have hper:∀ z:ℂ,0< z.re→ 2 ≤ ‖z‖→ F (z+1)=F z:=by
  intro z hz_re hz_norm
  have hz0:z≠0:=norm_pos_iff.mp (by linarith)
  have h1_re:0< (1+1/z).re:=by
   simp only [Complex.add_re,Complex.one_re,one_div,Complex.inv_re]
   have:0< z.re/Complex.normSq z:=div_pos hz_re (Complex.normSq_pos.mpr hz0)
   linarith
  have hlog_add:Complex.log (z+1)=Complex.log z+Complex.log (1+1/z):=by
   have hmul:z+1=z*(1+1/z):=by field_simp [hz0]
   rw [hmul,z125 hz_re h1_re]
  have hrem:z260 z=z261 z+z260 (z+1):=by
   unfold z260
   have h:=(z267 hz_re hz_norm).sum_add_tsum_nat_add 1
   simp only [Finset.sum_range_one,Nat.cast_zero,add_zero] at h
   rw [← h];congr 1
   exact tsum_congr fun k=>by congr 1;push_cast;ring
  dsimp only [F]
  rw [Complex.Gamma_add_one z hz0,mul_comm z,mul_assoc]
  congr 1
  calc
   z*Complex.exp (-((z+1-1/2)*Complex.log (z+1)-(z+1)+z260 (z+1)))
    = Complex.exp (Complex.log z) *
      Complex.exp (-((z+1-1/2)*Complex.log (z+1)-(z+1)+z260 (z+1))):=by
     rw [Complex.exp_log hz0]
   _=Complex.exp (Complex.log z +
      -((z+1-1/2)*Complex.log (z+1)-(z+1)+z260 (z+1))):=
     (Complex.exp_add _ _).symm
   _=Complex.exp (-((z-1/2)*Complex.log z-z+z260 z)):=by
     congr 1;rw [hlog_add,hrem];unfold z261;ring
 have hshift:∀ N:ℕ,F (s+(N:ℂ))=F s:=by
  intro N;induction N with
  | zero=>simp
  | succ N ih =>
   rw [Nat.cast_succ,← add_assoc,hper (s+(N:ℂ)) (by simp;linarith [Nat.cast_nonneg (α:=ℝ) N])
    (hnorm.trans (z136 hre N)),ih]
 have htend:Tendsto (fun N:ℕ=>F (s+((N+1:ℕ):ℂ))) atTop
   (𝓝 ((Real.sqrt (2*Real.pi):ℝ):ℂ)):=by
  have hG_ne:Complex.Gamma s≠0:=Complex.Gamma_ne_zero_of_re_pos hre
  have hratio1:Tendsto (fun N:ℕ =>
    Complex.Gamma (s+((N+1:ℕ):ℂ)) /
     (Complex.exp (s*Complex.log (N:ℂ))*(N.factorial:ℂ))) atTop (𝓝 1):=by
   have hgs:=(Complex.GammaSeq_tendsto_Gamma s).inv₀ hG_ne
   have hmul:=hgs.const_mul (Complex.Gamma s)
   rw [mul_inv_cancel₀ hG_ne] at hmul
   refine hmul.congr' ?_
   filter_upwards [eventually_ge_atTop 1] with N hN
   have hNpos:(0:ℝ)< N:=Nat.cast_pos.mpr hN
   have hNne:(N:ℂ)≠0:=Nat.cast_ne_zero.mpr (by omega)
   have hfac_ne:(N.factorial:ℂ)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
   have hprod_gamma:Complex.Gamma (s+((N+1:ℕ):ℂ)) =
     (∏ k∈Finset.range (N+1),(s+(k:ℂ)))*Complex.Gamma s:=by
    clear hgs hmul hN hNpos hNne hfac_ne
    induction N with
    | zero=>simp [Complex.Gamma_add_one s (by intro h;simp [h] at hre)]
    | succ k ih =>
     rw [Finset.prod_range_succ,mul_right_comm,← ih,mul_comm (Complex.Gamma _)]
     have harg:s+((k+1+1:ℕ):ℂ)=(s+((k+1:ℕ):ℂ))+1:=by push_cast;ring
     have hne:s+((k+1:ℕ):ℂ)≠0:=by
      intro h;have:=congr_arg Complex.re h;simp at this;linarith
     rw [harg,Complex.Gamma_add_one _ hne]
   unfold Complex.GammaSeq
   have hcpow:((N:ℂ)^s)=Complex.exp (s*Complex.log (N:ℂ)):=by
    rw [Complex.cpow_def_of_ne_zero hNne,mul_comm]
   rw [hprod_gamma,hcpow]
   have hprod_ne:(∏ k∈Finset.range (N+1),(s+(k:ℂ)))≠0:=by
    refine Finset.prod_ne_zero_iff.mpr fun k _ heq=>?_
    have:=congr_arg Complex.re heq;simp at this;linarith
   field_simp [hprod_ne,hfac_ne,Complex.exp_ne_zero]
  have hratio2:Tendsto (fun N:ℕ =>
    (N.factorial:ℂ) /
     (((Real.sqrt (2*Real.pi):ℝ):ℂ) *
      Complex.exp (((N:ℂ)+1/2)*Complex.log (N:ℂ)-(N:ℂ)))) atTop (𝓝 1):=by
   have hst_real:Tendsto (fun N:ℕ =>
     (N.factorial:ℝ)/(Real.sqrt (2*(N:ℝ)*Real.pi)*((N:ℝ)/Real.exp 1)^N))
     atTop (𝓝 1):=by
    have hsq:Real.sqrt Real.pi≠0:=by positivity
    have h:=Stirling.tendsto_stirlingSeq_sqrt_pi.div_const (Real.sqrt Real.pi)
    rw [div_self hsq] at h
    refine h.congr fun N=>?_
    unfold Stirling.stirlingSeq
    rw [Real.sqrt_mul (by positivity:0 ≤ 2*(N:ℝ)),
     Real.sqrt_mul (by positivity:(0:ℝ) ≤ 2)]
    ring
   have hst_c:=(Complex.continuous_ofReal.tendsto 1).comp hst_real
   simp only [Complex.ofReal_one] at hst_c
   refine hst_c.congr' ?_
   filter_upwards [eventually_ge_atTop 1] with N hN
   have hNpos:(0:ℝ)< N:=Nat.cast_pos.mpr hN
   simp only [Function.comp_apply,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_mul]
   congr 1
   have hsqrt:Real.sqrt (2*(N:ℝ)*Real.pi)=Real.sqrt (2*Real.pi)*Real.sqrt (N:ℝ):=by
    rw [show 2*(N:ℝ)*Real.pi=(2*Real.pi)*(N:ℝ) by ring,
     Real.sqrt_mul (by positivity)]
   have hexp_real:Real.sqrt (N:ℝ)*((N:ℝ)/Real.exp 1)^N =
     Real.exp (((N:ℝ)+1/2)*Real.log (N:ℝ)-(N:ℝ)):=by
    rw [div_pow,← Real.exp_nat_mul,mul_one,Real.sqrt_eq_rpow,
     Real.rpow_def_of_pos hNpos,show ((N:ℝ)^N)=Real.exp ((N:ℝ)*Real.log (N:ℝ)) by
      rw [← Real.rpow_natCast,Real.rpow_def_of_pos hNpos,mul_comm]]
    rw [← mul_div_assoc,← Real.exp_add,← Real.exp_sub]
    congr 1;ring
   rw [← Complex.ofReal_mul,hsqrt,mul_assoc,hexp_real,Complex.ofReal_mul,Complex.ofReal_exp]
   congr 2
   push_cast;rfl
  have hratio3:Tendsto (fun N:ℕ =>
    Complex.exp ((s+(N:ℂ)+1/2)*Complex.log (N:ℂ)-(N:ℂ) -
     ((s+((N+1:ℕ):ℂ)-1/2)*Complex.log (s+((N+1:ℕ):ℂ)) -
      (s+((N+1:ℕ):ℂ))+z260 (s+((N+1:ℕ):ℂ)))))
    atTop (𝓝 1):=by
   suffices h:Tendsto (fun N:ℕ =>
     (s+(N:ℂ)+1/2)*Complex.log (N:ℂ)-(N:ℂ) -
      ((s+((N+1:ℕ):ℂ)-1/2)*Complex.log (s+((N+1:ℕ):ℂ)) -
       (s+((N+1:ℕ):ℂ))+z260 (s+((N+1:ℕ):ℂ)))) atTop (𝓝 0) by
    simpa only [Function.comp_def,Complex.exp_zero] using (Complex.continuous_exp.tendsto 0).comp h
   have hterm1:Tendsto (fun N:ℕ =>
     (s+1)-(s+(N:ℂ)+1/2)*Complex.log (1+(s+1)/(N:ℂ))) atTop (𝓝 0):=by
    refine Metric.tendsto_atTop.mpr fun ε hε=>?_
    obtain ⟨N0,hN0⟩:=exists_nat_gt (max (2*(‖s+1‖+1))
     ((2*‖s+1‖^2+2*‖s+1/2‖*‖s+1‖+1) / ε))
    refine ⟨max N0 1,fun N hN=>?_⟩
    have hNpos:(0:ℝ)< N:=Nat.cast_pos.mpr (by omega)
    have hNge:2*(‖s+1‖+1)< (N:ℝ):=
     lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hN0 (Nat.cast_le.mpr (le_trans (le_max_left _ _) hN)))
    set u:ℂ:=(s+1)/(N:ℂ)
    have hu:‖u‖ ≤ 1/2:=by
     simp only [u,norm_div,Complex.norm_natCast]
     rw [div_le_iff₀ hNpos];linarith
    have hdiff_eq:(s+1)-(s+(N:ℂ)+1/2)*Complex.log (1+u) =
      -((N:ℂ)*(Complex.log (1+u)-u))-(s+1/2)*Complex.log (1+u):=by
     have hNu:(N:ℂ)*u=s+1:=by
      simp only [u];field_simp [Nat.cast_ne_zero.mpr (by omega:N≠0)]
     calc
      (s+1)-(s+(N:ℂ)+1/2)*Complex.log (1+u)
       = (N:ℂ)*u-(s+(N:ℂ)+1/2)*Complex.log (1+u):=by rw [hNu]
      _=-((N:ℂ)*(Complex.log (1+u)-u))-(s+1/2)*Complex.log (1+u):=by ring
    rw [dist_zero_right,hdiff_eq]
    have hbd1:‖(N:ℂ)*(Complex.log (1+u)-u)‖ ≤ 2*‖s+1‖^2/(N:ℝ):=by
     rw [norm_mul,Complex.norm_natCast]
     have h:=z141 hu
     have hu2:‖u‖^2=‖s+1‖^2/(N:ℝ)^2:=by simp [u,div_pow]
     rw [hu2] at h
     calc
      (N:ℝ)*‖Complex.log (1+u)-u‖ ≤ (N:ℝ)*(2*(‖s+1‖^2/(N:ℝ)^2)):=
        mul_le_mul_of_nonneg_left h hNpos.le
      _=2*‖s+1‖^2/(N:ℝ):=by field_simp [hNpos.ne']
    have hbd2:‖(s+1/2)*Complex.log (1+u)‖ ≤ 2*‖s+1/2‖*‖s+1‖ / (N:ℝ):=by
     rw [norm_mul]
     have h:=z140 hu
     simp only [u,norm_div,Complex.norm_natCast] at h
     calc
      ‖s+1/2‖*‖Complex.log (1+u)‖ ≤ ‖s+1/2‖*(2*(‖s+1‖ / (N:ℝ))):=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _=2*‖s+1/2‖*‖s+1‖ / (N:ℝ):=by ring
    have htot:‖-((N:ℂ)*(Complex.log (1+u)-u))-(s+1/2)*Complex.log (1+u)‖ ≤
      (2*‖s+1‖^2+2*‖s+1/2‖*‖s+1‖)/(N:ℝ):=by
     calc
      ‖-((N:ℂ)*(Complex.log (1+u)-u))-(s+1/2)*Complex.log (1+u)‖
       ≤ ‖-((N:ℂ)*(Complex.log (1+u)-u))‖+‖(s+1/2)*Complex.log (1+u)‖:=
        norm_sub_le _ _
      _=‖(N:ℂ)*(Complex.log (1+u)-u)‖+‖(s+1/2)*Complex.log (1+u)‖:=by rw [norm_neg]
      _ ≤ 2*‖s+1‖^2/(N:ℝ)+2*‖s+1/2‖*‖s+1‖ / (N:ℝ):=add_le_add hbd1 hbd2
      _=_:=by rw [add_div]
    refine lt_of_le_of_lt htot ?_
    rw [div_lt_iff₀ hNpos]
    have hNge2:(2*‖s+1‖^2+2*‖s+1/2‖*‖s+1‖+1) / ε < (N:ℝ):=
     lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hN0 (Nat.cast_le.mpr (le_trans (le_max_left _ _) hN)))
    have hNε:=(div_lt_iff₀ hε).mp hNge2
    linarith
   have hterm2:Tendsto (fun N:ℕ=>z260 (s+((N+1:ℕ):ℂ))) atTop (𝓝 0):=by
    refine squeeze_zero_norm' (a:=fun N:ℕ=>6/((N:ℝ)+1)) ?_ ?_
    ·
     filter_upwards [eventually_ge_atTop 2] with N hN
     have hreN:0< (s+((N+1:ℕ):ℂ)).re:=by simp;linarith
     have hnormN:((N:ℝ)+1) ≤ ‖s+((N+1:ℕ):ℂ)‖:=by
      have:=Complex.re_le_norm (s+((N+1:ℕ):ℂ))
      simp only [Complex.add_re,Complex.natCast_re,Complex.one_re,Nat.cast_add,Nat.cast_one] at this
      rw [Nat.cast_add,Nat.cast_one]
      linarith
     have h2N:2 ≤ ‖s+((N+1:ℕ):ℂ)‖:=by
      have:(2:ℝ) ≤ N:=by exact_mod_cast hN
      linarith
     exact (z143 hreN h2N).trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) hnormN)
    ·
     simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=(6:ℝ))).mul
      (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
   have hsub:=hterm1.sub hterm2
   rw [sub_zero] at hsub
   refine hsub.congr' ?_
   filter_upwards [eventually_ge_atTop 1] with N hN
   have hNpos:(0:ℝ)< N:=Nat.cast_pos.mpr hN
   have hNre:0< (N:ℂ).re:=by simpa using hNpos
   have h1re:0< (1+(s+1)/(N:ℂ)).re:=by
    rw [show (N:ℂ)=((N:ℝ):ℂ) by norm_cast]
    simp only [Complex.add_re,Complex.one_re,Complex.div_ofReal_re]
    have:0< (s.re+1)/(N:ℝ):=div_pos (by linarith) hNpos
    linarith
   have hlog_eq:Complex.log (s+((N+1:ℕ):ℂ)) =
     Complex.log (N:ℂ)+Complex.log (1+(s+1)/(N:ℂ)):=by
    have hmul:s+((N+1:ℕ):ℂ)=(N:ℂ)*(1+(s+1)/(N:ℂ)):=by
     have hNne:(N:ℂ)≠0:=Nat.cast_ne_zero.mpr (by omega)
     push_cast;field_simp [hNne];ring
    rw [hmul,z125 hNre h1re]
   rw [hlog_eq]
   push_cast;ring
  have hprod:=((hratio1.mul hratio2).mul hratio3).const_mul ((Real.sqrt (2*Real.pi):ℝ):ℂ)
  simp only [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hfac_ne:(N.factorial:ℂ)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hsq_ne:((Real.sqrt (2*Real.pi):ℝ):ℂ)≠0:=
   Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  dsimp only [F]
  have hcomb:Complex.exp (s*Complex.log (N:ℂ)) *
    Complex.exp (((N:ℂ)+1/2)*Complex.log (N:ℂ)-(N:ℂ)) =
    Complex.exp ((s+(N:ℂ)+1/2)*Complex.log (N:ℂ)-(N:ℂ)):=by
   rw [← Complex.exp_add];congr 1;ring
  have hexp_cancel:Complex.exp ((s+(N:ℂ)+1/2)*Complex.log (N:ℂ)-(N:ℂ)) *
    Complex.exp (-((s+((N+1:ℕ):ℂ)-1/2)*Complex.log (s+((N+1:ℕ):ℂ)) -
     (s+((N+1:ℕ):ℂ))+z260 (s+((N+1:ℕ):ℂ)))) =
    Complex.exp ((s+(N:ℂ)+1/2)*Complex.log (N:ℂ)-(N:ℂ) -
     ((s+((N+1:ℕ):ℂ)-1/2)*Complex.log (s+((N+1:ℕ):ℂ)) -
      (s+((N+1:ℕ):ℂ))+z260 (s+((N+1:ℕ):ℂ)))):=by
   rw [← Complex.exp_add];congr 1
  rw [← hexp_cancel,← hcomb]
  field_simp [hfac_ne,hsq_ne,Complex.exp_ne_zero]
 have hconst:F s=((Real.sqrt (2*Real.pi):ℝ):ℂ):=by
  have htend':Tendsto (fun _:ℕ=>F s) atTop (𝓝 ((Real.sqrt (2*Real.pi):ℝ):ℂ)):=
   htend.congr (fun N=>hshift (N+1))
  exact tendsto_nhds_unique tendsto_const_nhds htend'
 dsimp only [F] at hconst
 calc
  Complex.Gamma s
   = Complex.Gamma s*Complex.exp (-((s-1/2)*Complex.log s-s+z260 s)) *
     Complex.exp ((s-1/2)*Complex.log s-s+z260 s):=by
    rw [mul_assoc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero,mul_one]
  _=((Real.sqrt (2*Real.pi):ℝ):ℂ) *
     Complex.exp ((s-1/2)*Complex.log s-s+z260 s):=by rw [hconst]
lemma z131 {m:ℕ} (hm:2 ≤ m) :
  (m.factorial:ℂ) =
   ((Real.sqrt (2*Real.pi):ℝ):ℂ) *
    Complex.exp (((m:ℂ)+1/2)*Complex.log (m:ℂ)-(m:ℂ)+z260 (m:ℂ)):=by
 have hm_pos:(0:ℝ)< m:=Nat.cast_pos.mpr (by omega)
 have hm_re:0< (m:ℂ).re:=by simpa using hm_pos
 have hm_norm:2 ≤ ‖(m:ℂ)‖:=by rw [Complex.norm_natCast];exact_mod_cast hm
 have hm_ne:(m:ℂ)≠0:=Nat.cast_ne_zero.mpr (by omega)
 have h1:(m.factorial:ℂ)=(m:ℂ)*Complex.Gamma (m:ℂ):=by
  rw [← Complex.Gamma_nat_eq_factorial,Complex.Gamma_add_one _ hm_ne]
 rw [h1,z49 hm_re hm_norm]
 calc
  (m:ℂ)*(((Real.sqrt (2*Real.pi):ℝ):ℂ) *
     Complex.exp (((m:ℂ)-1/2)*Complex.log (m:ℂ)-(m:ℂ)+z260 (m:ℂ)))
   = ((Real.sqrt (2*Real.pi):ℝ):ℂ) *
     (Complex.exp (Complex.log (m:ℂ)) *
      Complex.exp (((m:ℂ)-1/2)*Complex.log (m:ℂ)-(m:ℂ)+z260 (m:ℂ))):=by
    rw [Complex.exp_log hm_ne];ring
  _=((Real.sqrt (2*Real.pi):ℝ):ℂ) *
     Complex.exp (((m:ℂ)+1/2)*Complex.log (m:ℂ)-(m:ℂ)+z260 (m:ℂ)):=by
    rw [← Complex.exp_add];congr 2;ring
noncomputable def wPot (z:ℂ):ℂ:=
 I*(Real.pi:ℂ)*(z+1) +
  (∑ u∈Finset.Icc (1:ℕ) 10,(((35-2*u:ℕ):ℂ)*Complex.log ((35-2*u:ℕ):ℂ))) -
  162*Complex.log 27 +
  3*z*Complex.log z +
  3*(27-z)*Complex.log (27-z) +
  3*(z+64)*Complex.log (z+64) -
  3*(z+37)*Complex.log (z+37) +
  ∑ u∈Finset.Icc (1:ℕ) 10,
   ((z+((1+u:ℕ):ℂ))*Complex.log (z+((1+u:ℕ):ℂ)) -
    (z+((36-u:ℕ):ℂ))*Complex.log (z+((36-u:ℕ):ℂ)))
noncomputable def dwPot (z:ℂ):ℂ:=
 I*(Real.pi:ℂ) +
  3*Complex.log z -
  3*Complex.log (27-z) +
  3*Complex.log (z+64) -
  3*Complex.log (z+37) +
  ∑ u∈Finset.Icc (1:ℕ) 10,
   (Complex.log (z+((1+u:ℕ):ℂ))-Complex.log (z+((36-u:ℕ):ℂ)))
noncomputable def z53 (z:ℂ):ℂ:=
 3/z+3/(27-z)+3/(z+64)-3/(z+37) +
  ∑ u∈Finset.Icc (1:ℕ) 10,
   (1/(z+((1+u:ℕ):ℂ))-1/(z+((36-u:ℕ):ℂ)))
noncomputable def z55 (z:ℂ):ℂ:=
 -3/z^2+3/(27-z)^2-3/(z+64)^2+3/(z+37)^2 +
  ∑ u∈Finset.Icc (1:ℕ) 10,
   (-1/(z+((1+u:ℕ):ℂ))^2+1/(z+((36-u:ℕ):ℂ))^2)
private lemma z96 (c:ℂ) {z:ℂ} (hre:0< (z+c).re) :
  HasDerivAt (fun w:ℂ=>(w+c)*Complex.log (w+c)) (Complex.log (z+c)+1) z:=by
 have hslit:z+c∈Complex.slitPlane:=z257 hre
 have hne:z+c≠0:=Complex.slitPlane_ne_zero hslit
 have hlin:HasDerivAt (fun w:ℂ=>w+c) 1 z:=(hasDerivAt_id z).add_const c
 have hlog:HasDerivAt (fun w:ℂ=>Complex.log (w+c)) (z+c)⁻¹ z:=by
  rw [← mul_one (z+c)⁻¹]
  exact (Complex.hasDerivAt_log hslit).comp z hlin
 have hmul:=hlin.fun_mul hlog
 rw [show Complex.log (z+c)+1=1*Complex.log (z+c)+(z+c)*(z+c)⁻¹ by
  rw [one_mul,mul_inv_cancel₀ hne]]
 exact hmul
private lemma z97 (c:ℂ) {z:ℂ} (hre:0< (c-z).re) :
  HasDerivAt (fun w:ℂ=>(c-w)*Complex.log (c-w)) (-(Complex.log (c-z)+1)) z:=by
 have hslit:c-z∈Complex.slitPlane:=z257 hre
 have hne:c-z≠0:=Complex.slitPlane_ne_zero hslit
 have hlin:HasDerivAt (fun w:ℂ=>c-w) (-1) z:=by
  rw [show (-1:ℂ)=0-1 by ring]
  exact (hasDerivAt_const z c).fun_sub (hasDerivAt_id z)
 have hlog:HasDerivAt (fun w:ℂ=>Complex.log (c-w)) (-(c-z)⁻¹) z:=by
  rw [show -(c-z)⁻¹=(c-z)⁻¹*(-1) by ring]
  exact (Complex.hasDerivAt_log hslit).comp z hlin
 have hmul:=hlin.fun_mul hlog
 rw [show -(Complex.log (c-z)+1)=(-1)*Complex.log (c-z)+(c-z)*-(c-z)⁻¹ by
  rw [neg_one_mul,mul_neg,mul_inv_cancel₀ hne];ring]
 exact hmul
lemma z100 {z:ℂ} (h0:0< z.re) (h27:z.re< 27) :
  HasDerivAt wPot (dwPot z) z:=by
 have h1:HasDerivAt (fun w:ℂ=>I*(Real.pi:ℂ)*(w+1)) (I*(Real.pi:ℂ)) z:=by
  have h:=((hasDerivAt_id z).add_const (1:ℂ)).const_mul (I*(Real.pi:ℂ))
  rw [mul_one] at h
  exact h
 have h2:HasDerivAt (fun w:ℂ=>3*w*Complex.log w) (3*(Complex.log z+1)) z:=by
  have h:=(z96 0 (by simpa using h0)).const_mul (3:ℂ)
  rw [add_zero] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w=>by simp [mul_assoc])
 have h3:HasDerivAt (fun w:ℂ=>3*(27-w)*Complex.log (27-w))
   (3*(-(Complex.log (27-z)+1))) z:=by
  have h:=(z97 27 (by simp;linarith)).const_mul (3:ℂ)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w=>by ring)
 have h4:HasDerivAt (fun w:ℂ=>3*(w+64)*Complex.log (w+64))
   (3*(Complex.log (z+64)+1)) z:=by
  have h:=(z96 64 (by simp;linarith)).const_mul (3:ℂ)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w=>by ring)
 have h5:HasDerivAt (fun w:ℂ=>3*(w+37)*Complex.log (w+37))
   (3*(Complex.log (z+37)+1)) z:=by
  have h:=(z96 37 (by simp;linarith)).const_mul (3:ℂ)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w=>by ring)
 have h6:HasDerivAt (fun w:ℂ=>∑ u∈Finset.Icc (1:ℕ) 10,
   ((w+((1+u:ℕ):ℂ))*Complex.log (w+((1+u:ℕ):ℂ)) -
    (w+((36-u:ℕ):ℂ))*Complex.log (w+((36-u:ℕ):ℂ))))
   (∑ u∈Finset.Icc (1:ℕ) 10,
    (Complex.log (z+((1+u:ℕ):ℂ))-Complex.log (z+((36-u:ℕ):ℂ)))) z:=by
  refine HasDerivAt.fun_sum fun u _=>?_
  have ha:=z96 ((1+u:ℕ):ℂ) (z:=z) (by simp;positivity)
  have hb:=z96 ((36-u:ℕ):ℂ) (z:=z) (by simp;positivity)
  have hsub:=ha.fun_sub hb
  rw [add_sub_add_right_eq_sub] at hsub
  exact hsub
 have htot:=((((((h1.add_const
   (∑ u∈Finset.Icc (1:ℕ) 10,(((35-2*u:ℕ):ℂ)*Complex.log ((35-2*u:ℕ):ℂ)))).sub_const
   (162*Complex.log 27)).fun_add h2).fun_add h3).fun_add h4).fun_sub h5).fun_add h6
 have hval:I*(Real.pi:ℂ)+3*(Complex.log z+1)+3*-(Complex.log (27-z)+1) +
   3*(Complex.log (z+64)+1)-3*(Complex.log (z+37)+1) +
   ∑ u∈Finset.Icc (1:ℕ) 10,(Complex.log (z+((1+u:ℕ):ℂ))-Complex.log (z+((36-u:ℕ):ℂ))) =
   dwPot z:=by
  unfold dwPot;ring
 rw [← hval]
 exact htot
lemma z95 {z:ℂ} (h0:0< z.re) (h27:z.re< 27) :
  HasDerivAt dwPot (z53 z) z:=by
 have hlog_add:∀ c:ℂ,0< (z+c).re →
   HasDerivAt (fun w:ℂ=>Complex.log (w+c)) (1/(z+c)) z:=by
  intro c hc
  rw [one_div,← mul_one (z+c)⁻¹]
  exact (Complex.hasDerivAt_log (z257 hc)).comp z ((hasDerivAt_id z).add_const c)
 have hlog_sub:HasDerivAt (fun w:ℂ=>Complex.log (27-w)) (-(1/(27-z))) z:=by
  have hlin:HasDerivAt (fun w:ℂ=>(27:ℂ)-w) (-1) z:=by
   rw [show (-1:ℂ)=0-1 by ring]
   exact (hasDerivAt_const z (27:ℂ)).fun_sub (hasDerivAt_id z)
  rw [show -(1/(27-z))=(27-z)⁻¹*(-1) by ring]
  exact (Complex.hasDerivAt_log (z257 (by simp;linarith))).comp z hlin
 have h1:HasDerivAt (fun w:ℂ=>3*Complex.log w) (3/z) z:=by
  rw [div_eq_mul_inv]
  exact (Complex.hasDerivAt_log (z257 h0)).const_mul (3:ℂ)
 have h2:HasDerivAt (fun w:ℂ=>3*Complex.log (27-w)) (-(3/(27-z))) z:=by
  have h:=hlog_sub.const_mul (3:ℂ)
  have heq:(3:ℂ)*-(1/(27-z))=-(3/(27-z)):=by ring
  rwa [heq] at h
 have h3:HasDerivAt (fun w:ℂ=>3*Complex.log (w+64)) (3/(z+64)) z:=by
  have h:=(hlog_add 64 (by simp;linarith)).const_mul (3:ℂ)
  have heq:(3:ℂ)*(1/(z+64))=3/(z+64):=by ring
  rwa [heq] at h
 have h4:HasDerivAt (fun w:ℂ=>3*Complex.log (w+37)) (3/(z+37)) z:=by
  have h:=(hlog_add 37 (by simp;linarith)).const_mul (3:ℂ)
  have heq:(3:ℂ)*(1/(z+37))=3/(z+37):=by ring
  rwa [heq] at h
 have h5:HasDerivAt (fun w:ℂ=>∑ u∈Finset.Icc (1:ℕ) 10,
   (Complex.log (w+((1+u:ℕ):ℂ))-Complex.log (w+((36-u:ℕ):ℂ))))
   (∑ u∈Finset.Icc (1:ℕ) 10,
    (1/(z+((1+u:ℕ):ℂ))-1/(z+((36-u:ℕ):ℂ)))) z:=
  HasDerivAt.fun_sum fun u _ =>
   (hlog_add ((1+u:ℕ):ℂ) (by simp;positivity)).fun_sub
    (hlog_add ((36-u:ℕ):ℂ) (by simp;positivity))
 have htot:=((((hasDerivAt_const z (I*(Real.pi:ℂ))).fun_add h1).fun_sub h2).fun_add h3).fun_sub h4 |>.fun_add h5
 have hval:0+3/z - -(3/(27-z))+3/(z+64)-3/(z+37) +
   ∑ u∈Finset.Icc (1:ℕ) 10,(1/(z+((1+u:ℕ):ℂ))-1/(z+((36-u:ℕ):ℂ))) =
   z53 z:=by
  unfold z53;ring
 rw [← hval]
 exact htot
lemma z94 {z:ℂ} (h0:0< z.re) (h27:z.re< 27) :
  HasDerivAt z53 (z55 z) z:=by
 have hinv_add:∀ (a c:ℂ),0< (z+c).re →
   HasDerivAt (fun w:ℂ=>a/(w+c)) (-a/(z+c)^2) z:=by
  intro a c hc
  have hne:z+c≠0:=by intro h;simp [h] at hc
  have h:=(hasDerivAt_const z a).fun_div ((hasDerivAt_id z).add_const c) hne
  rw [show -a/(z+c)^2=(0*(z+c)-a*1)/(z+c)^2 by ring]
  exact h
 have hinv_sub:HasDerivAt (fun w:ℂ=>(3:ℂ)/(27-w)) (3/(27-z)^2) z:=by
  have hne:(27:ℂ)-z≠0:=by
   intro h;have:=congr_arg Complex.re h;simp at this;linarith
  have hlin:HasDerivAt (fun w:ℂ=>(27:ℂ)-w) (-1) z:=by
   rw [show (-1:ℂ)=0-1 by ring]
   exact (hasDerivAt_const z (27:ℂ)).fun_sub (hasDerivAt_id z)
  have h:=(hasDerivAt_const z (3:ℂ)).fun_div hlin hne
  rw [show (3:ℂ)/(27-z)^2=(0*(27-z)-3*(-1))/(27-z)^2 by ring]
  exact h
 have h1:HasDerivAt (fun w:ℂ=>(3:ℂ)/w) (-3/z^2) z:=by
  have h:=hinv_add 3 0 (by simpa using h0)
  rw [add_zero] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w=>by simp)
 have h3:=hinv_add 3 64 (by simp;linarith)
 have h4:=hinv_add 3 37 (by simp;linarith)
 have h5:HasDerivAt (fun w:ℂ=>∑ u∈Finset.Icc (1:ℕ) 10,
   (1/(w+((1+u:ℕ):ℂ))-1/(w+((36-u:ℕ):ℂ))))
   (∑ u∈Finset.Icc (1:ℕ) 10,
    (-1/(z+((1+u:ℕ):ℂ))^2+1/(z+((36-u:ℕ):ℂ))^2)) z:=by
  refine HasDerivAt.fun_sum fun u _=>?_
  have ha:=hinv_add 1 ((1+u:ℕ):ℂ) (by simp;positivity)
  have hb:=hinv_add 1 ((36-u:ℕ):ℂ) (by simp;positivity)
  have hs:=ha.fun_sub hb
  have heq:-1/(z+((1+u:ℕ):ℂ))^2 - -1/(z+((36-u:ℕ):ℂ))^2 =
    -1/(z+((1+u:ℕ):ℂ))^2+1/(z+((36-u:ℕ):ℂ))^2:=by ring
  rwa [heq] at hs
 have htot:=(((h1.fun_add hinv_sub).fun_add h3).fun_sub h4).fun_add h5
 have hval:-3/z^2+3/(27-z)^2+-3/(z+64)^2 - -3/(z+37)^2 +
   ∑ u∈Finset.Icc (1:ℕ) 10,(-1/(z+((1+u:ℕ):ℂ))^2+1/(z+((36-u:ℕ):ℂ))^2) =
   z55 z:=by
  unfold z55;ring
 rw [← hval]
 exact htot
private def gMul:ℤ × ℤ→ ℤ × ℤ→ ℤ × ℤ
 | (a1,a2),(b1,b2)=>(a1*b1-a2*b2,a1*b2+a2*b1)
private def gPow (a:ℤ × ℤ):ℕ→ ℤ × ℤ
 | 0=>(1,0)
 | n+1 =>
  let half:=gPow a ((n+1)/2)
  let sq:=gMul half half
  if (n+1) % 2=0 then sq else gMul a sq
private def z87:ℤ × ℤ→ ℤ
 | (a1,a2)=>a1*a1+a2*a2
private def toC (a:ℤ × ℤ):ℂ:=(a.1:ℂ)+(a.2:ℂ)*I
private lemma z270 (a b:ℤ × ℤ):toC (gMul a b)=toC a*toC b:=by
 rcases a with ⟨a1,a2⟩;rcases b with ⟨b1,b2⟩
 unfold gMul toC;push_cast;ring_nf;rw [Complex.I_sq];ring
private lemma z271 (a:ℤ × ℤ) (n:ℕ):toC (gPow a n)=(toC a)^n:=by
 induction n using Nat.strong_induction_on with
 | h n ih =>
  cases n with
  | zero=>simp [gPow,toC]
  | succ m =>
   rw [gPow]
   have hlt:(m+1)/2< m+1:=Nat.div_lt_self (Nat.succ_pos m) (by norm_num)
   have hih:=ih ((m+1)/2) hlt
   split_ifs with hmod
   ·
    rw [z270,hih,← pow_add]
    congr 1;omega
   ·
    rw [z270,z270,hih,← pow_add,← pow_succ']
    congr 1;omega
private lemma z134 (a:ℤ × ℤ):Complex.normSq (toC a)=(z87 a:ℝ):=by
 rcases a with ⟨a1,a2⟩
 unfold toC z87
 rw [Complex.normSq_apply]
 simp only [Complex.add_re,Complex.intCast_re,Complex.mul_re,Complex.I_re,mul_zero,
  Complex.intCast_im,Complex.I_im,mul_one,sub_self,add_zero,Complex.add_im,zero_add,
  Complex.mul_im]
 push_cast;ring
noncomputable def z284:ℂ:=(234790:ℂ)/10000-((33282:ℂ)/10000)*I
private def zNumG:ℤ × ℤ:=
 let xr:ℤ:=234790;let yr:ℤ:=-33282;let D:ℤ:=10000
 let p0:=gMul (-1,0) (gMul (gPow (xr,yr) 3) (gPow (xr+64*D,yr) 3))
 (List.range 10).foldl (fun acc (k:ℕ)=>gMul acc (xr+(2+(k:ℤ))*D,yr)) p0
private def zDenG:ℤ × ℤ:=
 let xr:ℤ:=234790;let yr:ℤ:=-33282;let D:ℤ:=10000
 let p0:=gMul (gPow (27*D-xr,-yr) 3) (gPow (xr+37*D,yr) 3)
 (List.range 10).foldl (fun acc (k:ℕ)=>gMul acc (xr+(35-(k:ℤ))*D,yr)) p0
private def wNumG:ℤ × ℤ:=
 let xr:ℤ:=234790;let yr:ℤ:=-33282;let D:ℤ:=10000
 let cnum:ℤ:=(List.range 10).foldl (fun acc (k:ℕ)=>acc*((33-2*k:ℕ):ℤ)^(33-2*k)) 1
 let p0:=gMul (-cnum*D^78,0) (gMul (gPow (27*D-xr,-yr) 81) (gPow (xr+64*D,yr) 192))
 (List.range 10).foldl (fun acc (k:ℕ)=>gMul acc (gPow (xr+(2+(k:ℤ))*D,yr) (2+k))) p0
private def wDenG:ℤ × ℤ:=
 let xr:ℤ:=234790;let yr:ℤ:=-33282;let D:ℤ:=10000
 let p0:=gMul ((27:ℤ)^162,0) (gPow (xr+37*D,yr) 111)
 (List.range 10).foldl (fun acc (k:ℕ)=>gMul acc (gPow (xr+(35-(k:ℤ))*D,yr) (35-k))) p0
private theorem z252 :
  (z87 (zNumG.1-zDenG.1,zNumG.2-zDenG.2)*(100000:ℤ)^2< z87 zDenG ∧
   0< z87 zDenG) ∧
  (z87 wNumG*(68*(10:ℤ)^97)^2< z87 wDenG∧0< z87 wDenG) ∧
  ((2718281829:ℕ)^455< (10:ℕ)^(9*455)*(68*(10:ℕ)^97)^2) ∧
  (9*z87 wNumG*z87 wDenG <
   (gMul wNumG (wDenG.1,-wDenG.2)).2^2*100):=by
 have h1:z87 (zNumG.1-zDenG.1,zNumG.2-zDenG.2)*(100000:ℤ)^2< z87 zDenG:=by
  decide +kernel
 have h2:0< z87 zDenG:=by decide +kernel
 have h3:z87 wNumG*(68*(10:ℤ)^97)^2< z87 wDenG:=by decide +kernel
 have h4:0< z87 wDenG:=by decide +kernel
 have h5:(2718281829:ℕ)^455< (10:ℕ)^(9*455)*(68*(10:ℕ)^97)^2:=by
  decide +kernel
 have h6:9*z87 wNumG*z87 wDenG <
   (gMul wNumG (wDenG.1,-wDenG.2)).2^2*100:=by decide +kernel
 exact ⟨⟨h1,h2⟩,⟨h3,h4⟩,h5,h6⟩
private lemma z29 {t:ℝ} (ht:0 ≤ t) :
  t/(1+t^2) ≤ Real.arctan t∧Real.arctan t ≤ t:=by
 constructor
 ·
  have h1:(0:ℝ) ≤ Real.arctan t-t/(1+t^2):=by
   have hderiv:∀ x∈Set.Icc (0:ℝ) t,
     HasDerivAt (fun y=>Real.arctan y-y/(1+t^2))
      (1/(1+x^2)-1/(1+t^2)) x:=by
    intro x _
    have h1:=Real.hasDerivAt_arctan x
    have h2:HasDerivAt (fun y:ℝ=>y/(1+t^2)) (1/(1+t^2)) x:=
     (hasDerivAt_id x).div_const (1+t^2)
    exact h1.fun_sub h2
   have hmono:MonotoneOn (fun y=>Real.arctan y-y/(1+t^2)) (Set.Icc 0 t):=by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t) ?_ ?_ ?_
    ·
     exact (Real.continuous_arctan.sub (continuous_id.div_const _)).continuousOn
    ·
     intro x hx;exact (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    ·
     intro x hx
     have hmem:=interior_subset hx
     rw [(hderiv x hmem).deriv]
     have hle:1/(1+t^2) ≤ 1/(1+x^2):=
      div_le_div_of_nonneg_left zero_le_one (by positivity) (by nlinarith [hmem.1,hmem.2])
     linarith
   have:=hmono (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht) ht
   simpa using this
  linarith
 ·
  have hmono:MonotoneOn (fun y=>y-Real.arctan y) (Set.Icc 0 t):=by
   refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t) ?_ ?_ ?_
   ·
    exact (continuous_id.sub Real.continuous_arctan).continuousOn
   ·
    intro x _;exact ((hasDerivAt_id x).fun_sub (Real.hasDerivAt_arctan x)).differentiableAt.differentiableWithinAt
   ·
    intro x _
    have hd:HasDerivAt (fun y=>y-Real.arctan y) (1-1/(1+x^2)) x:=
     (hasDerivAt_id x).fun_sub (Real.hasDerivAt_arctan x)
    rw [hd.deriv,one_div]
    have hle:(1+x^2)⁻¹ ≤ 1:=inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
    linarith
  have:=hmono (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht) ht
  simp only [Real.arctan_zero,sub_zero] at this
  linarith
private lemma z184 {α : Type*} [CommMonoid α] (f:ℕ→ α) :
  ∏ u∈Finset.Icc (1:ℕ) 10,f u =
   f 1*f 2*f 3*f 4*f 5*f 6*f 7*f 8*f 9*f 10:=by
 simp only [Finset.prod_Icc_succ_top (by norm_num:1 ≤ _),Finset.Icc_self,Finset.prod_singleton]
private lemma z263 {α : Type*} [AddCommMonoid α] (f:ℕ→ α) :
  ∑ u∈Finset.Icc (1:ℕ) 10,f u =
   f 1+f 2+f 3+f 4+f 5+f 6+f 7+f 8+f 9+f 10:=by
 simp only [Finset.sum_Icc_succ_top (by norm_num:1 ≤ _),Finset.Icc_self,Finset.sum_singleton]
private lemma z74 :
  Complex.exp (dwPot z284)=toC zNumG/toC zDenG:=by
 have hz_re:(0:ℝ)< z284.re:=by unfold z284;simp
 have h27_re:z284.re< 27:=by unfold z284;simp;norm_num
 have hne:∀ c:ℂ,0< c.re→ c≠0:=fun c hc h0=>by simp [h0] at hc
 have hexp_sum:Complex.exp (dwPot z284) =
   (-1:ℂ)*(z284^3*(z284+64)^3*∏ u∈Finset.Icc (1:ℕ) 10,(z284+((1+u:ℕ):ℂ))) /
    ((27-z284)^3*(z284+37)^3*∏ u∈Finset.Icc (1:ℕ) 10,(z284+((36-u:ℕ):ℂ))):=by
  unfold dwPot
  simp only [Complex.exp_add,Complex.exp_sub,Complex.exp_sum]
  rw [show I*(Real.pi:ℂ)=(Real.pi:ℂ)*I by ring,Complex.exp_pi_mul_I]
  have h1:=Complex.exp_log (hne z284 hz_re)
  have h2:=Complex.exp_log (hne (27-z284) (by simp;linarith))
  have h3:=Complex.exp_log (hne (z284+64) (by simp;linarith))
  have h4:=Complex.exp_log (hne (z284+37) (by simp;linarith))
  have h5:∀ u∈Finset.Icc (1:ℕ) 10,
    Complex.exp (Complex.log (z284+((1+u:ℕ):ℂ)))=z284+((1+u:ℕ):ℂ):=
   fun u _=>Complex.exp_log (hne _ (by simp;positivity))
  have h6:∀ u∈Finset.Icc (1:ℕ) 10,
    Complex.exp (Complex.log (z284+((36-u:ℕ):ℂ)))=z284+((36-u:ℕ):ℂ):=
   fun u _=>Complex.exp_log (hne _ (by simp;positivity))
  have h3log:∀ c:ℂ,Complex.exp (3*Complex.log c)=(Complex.exp (Complex.log c))^3:=by
   intro c;simpa using Complex.exp_nat_mul (Complex.log c) 3
  rw [h3log,h3log,h3log,h3log,h1,h2,h3,h4]
  have hprod_div:(∏ u∈Finset.Icc (1:ℕ) 10,
    Complex.exp (Complex.log (z284+((1+u:ℕ):ℂ))) /
     Complex.exp (Complex.log (z284+((36-u:ℕ):ℂ)))) =
    (∏ u∈Finset.Icc (1:ℕ) 10,(z284+((1+u:ℕ):ℂ))) /
    (∏ u∈Finset.Icc (1:ℕ) 10,(z284+((36-u:ℕ):ℂ))):=by
   rw [← Finset.prod_div_distrib]
   refine Finset.prod_congr rfl fun u hu=>by rw [h5 u hu,h6 u hu]
  rw [hprod_div]
  simp only [div_eq_mul_inv,mul_inv]
  ring
 rw [hexp_sum]
 have h10z:∀ a:ℤ,(10000:ℂ)*(z284+(a:ℂ))=toC (234790+a*10000,-33282):=by
  intro a;unfold z284 toC;push_cast;ring
 have h10z_add:∀ k:ℕ,toC (234790+(2+(k:ℤ))*10000,-33282) =
   (10000:ℂ)*(z284+((1+(k+1):ℕ):ℂ)):=by
  intro k;unfold z284 toC;push_cast;ring
 have h10z_sub:∀ k:ℕ,k ≤ 9→ toC (234790+(35-(k:ℤ))*10000,-33282) =
   (10000:ℂ)*(z284+((36-(k+1):ℕ):ℂ)):=by
  intro k hk
  have hnat:((36-(k+1):ℕ):ℂ)=35-(k:ℂ):=by
   have:36-(k+1)=35-k:=by omega
   rw [this,Nat.cast_sub (by omega)];push_cast;rfl
  rw [hnat];unfold z284 toC;push_cast;ring
 have h10z0:(10000:ℂ)*z284=toC (234790,-33282):=by
  unfold z284 toC;push_cast;ring
 have h10z27:(10000:ℂ)*(27-z284)=toC (27*10000-234790,-(-33282)):=by
  unfold z284 toC;push_cast;ring
 have hrange10:List.range 10=[0,1,2,3,4,5,6,7,8,9]:=rfl
 have hnum_eq:toC zNumG =
   (10000:ℂ)^16*((-1:ℂ)*(z284^3*(z284+64)^3 *
    ∏ u∈Finset.Icc (1:ℕ) 10,(z284+((1+u:ℕ):ℂ)))):=by
  rw [z184]
  unfold zNumG
  rw [hrange10]
  simp only [List.foldl_cons,List.foldl_nil,z270,z271]
  have hm1:toC (-1,0)=(-1:ℂ):=by unfold toC;simp
  rw [hm1,← h10z0,← h10z 64,h10z_add 0,h10z_add 1,h10z_add 2,h10z_add 3,h10z_add 4,
   h10z_add 5,h10z_add 6,h10z_add 7,h10z_add 8,h10z_add 9]
  push_cast;ring
 have hden_eq:toC zDenG =
   (10000:ℂ)^16*((27-z284)^3*(z284+37)^3 *
    ∏ u∈Finset.Icc (1:ℕ) 10,(z284+((36-u:ℕ):ℂ))):=by
  rw [z184]
  unfold zDenG
  rw [hrange10]
  simp only [List.foldl_cons,List.foldl_nil,z270,z271]
  rw [← h10z27,← h10z 37,h10z_sub 0 (by omega),h10z_sub 1 (by omega),h10z_sub 2 (by omega),
   h10z_sub 3 (by omega),h10z_sub 4 (by omega),h10z_sub 5 (by omega),h10z_sub 6 (by omega),
   h10z_sub 7 (by omega),h10z_sub 8 (by omega),h10z_sub 9 (by omega)]
  push_cast;ring
 rw [hnum_eq,hden_eq,mul_div_mul_left _ _ (pow_ne_zero 16 (by norm_num))]
private lemma z139:‖dwPot z284‖ ≤ 2/100000:=by
 have him_bounds:-Real.pi< (dwPot z284).im∧(dwPot z284).im ≤ Real.pi:=by
  have hre_z:z284.re=23479/1000:=by unfold z284;simp;norm_num
  have him_z:z284.im=-33282/10000:=by unfold z284;simp;norm_num
  have harg_pos:∀ (a:ℝ),0< a →
    (Complex.log (z284+(a:ℂ))).im=-Real.arctan ((33282/10000)/(23479/1000+a)):=by
   intro a ha
   rw [Complex.log_im,z30 (by simp [hre_z];linarith)]
   simp only [Complex.add_im,Complex.ofReal_im,add_zero,him_z,Complex.add_re,
    Complex.ofReal_re,hre_z]
   rw [show (-33282/10000:ℝ)/(23479/1000+a)=-((33282/10000)/(23479/1000+a)) by ring,
    Real.arctan_neg]
  have harg0:(Complex.log z284).im=-Real.arctan ((33282/10000)/(23479/1000)):=by
   rw [Complex.log_im,z30 (by rw [hre_z];norm_num),hre_z,him_z]
   rw [show (-33282/10000:ℝ)/(23479/1000)=-((33282/10000)/(23479/1000)) by ring,
    Real.arctan_neg]
  have harg27:(Complex.log (27-z284)).im=Real.arctan ((33282/10000)/(27-23479/1000)):=by
   rw [Complex.log_im,z30 (by simp [hre_z];norm_num)]
   simp only [Complex.sub_im,Complex.im_ofNat,zero_sub,him_z,Complex.sub_re,Complex.re_ofNat,hre_z]
   congr 1;ring
  have ha0:=z29 (show (0:ℝ) ≤ (33282/10000)/(23479/1000) by norm_num)
  have ha27:=z29 (show (0:ℝ) ≤ (33282/10000)/(27-23479/1000) by norm_num)
  have ha37:=z29 (show (0:ℝ) ≤ (33282/10000)/(23479/1000+37) by norm_num)
  have ha64:=z29 (show (0:ℝ) ≤ (33282/10000)/(23479/1000+64) by norm_num)
  have hsum_bd:-2 ≤ (∑ u∈Finset.Icc (1:ℕ) 10,
    (Complex.log (z284+((1+u:ℕ):ℂ))-Complex.log (z284+((36-u:ℕ):ℂ)))).im ∧
    (∑ u∈Finset.Icc (1:ℕ) 10,
     (Complex.log (z284+((1+u:ℕ):ℂ))-Complex.log (z284+((36-u:ℕ):ℂ)))).im ≤ 0:=by
   rw [Complex.im_sum]
   constructor
   ·
    calc (-2:ℝ)=∑ _u∈Finset.Icc (1:ℕ) 10,(-1/5:ℝ):=by norm_num
     _ ≤ _:=Finset.sum_le_sum fun u hu=>by
      have hu1:=(Finset.mem_Icc.mp hu).1
      have hu10:=(Finset.mem_Icc.mp hu).2
      have h36pos:(0:ℝ)< ((36-u:ℕ):ℝ):=Nat.cast_pos.mpr (by omega)
      rw [Complex.sub_im,
       show ((1+u:ℕ):ℂ)=(((1+u:ℕ):ℝ):ℂ) by push_cast;rfl,
       show ((36-u:ℕ):ℂ)=(((36-u:ℕ):ℝ):ℂ) by push_cast;rfl,
       harg_pos ((1+u:ℕ):ℝ) (by positivity),
       harg_pos ((36-u:ℕ):ℝ) h36pos]
      have hb1:=z29 (show (0:ℝ) ≤ (33282/10000)/(23479/1000+((1+u:ℕ):ℝ)) by positivity)
      have hb2:=z29 (show (0:ℝ) ≤ (33282/10000)/(23479/1000+((36-u:ℕ):ℝ)) by positivity)
      have hle1:(33282/10000:ℝ)/(23479/1000+((1+u:ℕ):ℝ)) ≤ 1/5:=by
       rw [div_le_iff₀ (by positivity)]
       have:(1:ℝ) ≤ u:=by exact_mod_cast hu1
       push_cast;linarith
      linarith [hb1.2,hb2.1,show (0:ℝ) ≤ (33282/10000)/(23479/1000+((36-u:ℕ):ℝ)) /
       (1+((33282/10000)/(23479/1000+((36-u:ℕ):ℝ)))^2) by positivity]
   ·
    refine Finset.sum_nonpos fun u hu=>?_
    have hu1:=(Finset.mem_Icc.mp hu).1
    have hu10:=(Finset.mem_Icc.mp hu).2
    have h36pos:(0:ℝ)< ((36-u:ℕ):ℝ):=Nat.cast_pos.mpr (by omega)
    rw [Complex.sub_im,
     show ((1+u:ℕ):ℂ)=(((1+u:ℕ):ℝ):ℂ) by push_cast;rfl,
     show ((36-u:ℕ):ℂ)=(((36-u:ℕ):ℝ):ℂ) by push_cast;rfl,
     harg_pos ((1+u:ℕ):ℝ) (by positivity),
     harg_pos ((36-u:ℕ):ℝ) h36pos]
    have hlt:((1+u:ℕ):ℝ) ≤ ((36-u:ℕ):ℝ):=by exact_mod_cast (show 1+u ≤ 36-u by omega)
    have hdiv:(33282/10000:ℝ)/(23479/1000+((36-u:ℕ):ℝ)) ≤
      (33282/10000:ℝ)/(23479/1000+((1+u:ℕ):ℝ)):=
     div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    have hmono:=Real.arctan_mono hdiv
    linarith
  have hdw_im:(dwPot z284).im =
    Real.pi+3*(Complex.log z284).im-3*(Complex.log (27-z284)).im +
     3*(Complex.log (z284+64)).im-3*(Complex.log (z284+37)).im +
     (∑ u∈Finset.Icc (1:ℕ) 10,
      (Complex.log (z284+((1+u:ℕ):ℂ))-Complex.log (z284+((36-u:ℕ):ℂ)))).im:=by
   unfold dwPot
   simp only [Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.I_re,Complex.ofReal_im,
    Complex.I_im,Complex.ofReal_re,Complex.re_ofNat,Complex.im_ofNat]
   ring
  rw [hdw_im,harg0,harg27,
   show (64:ℂ)=((64:ℝ):ℂ) by norm_num,harg_pos 64 (by norm_num),
   show (37:ℂ)=((37:ℝ):ℂ) by norm_num,harg_pos 37 (by norm_num)]
  have hpi3:=Real.pi_gt_three
  constructor <;> nlinarith [ha0.1,ha0.2,ha27.1,ha27.2,ha37.1,ha37.2,ha64.1,ha64.2,
   hsum_bd.1,hsum_bd.2]
 have hdw_eq:dwPot z284=Complex.log (toC zNumG/toC zDenG):=by
  rw [← z74,Complex.log_exp him_bounds.1 him_bounds.2]
 rw [hdw_eq]
 have hden_pos:(0:ℝ)< Complex.normSq (toC zDenG):=by
  rw [z134];exact_mod_cast z252.1.2
 have hden_ne:toC zDenG≠0:=Complex.normSq_pos.mp hden_pos
 set u:ℂ:=toC zNumG/toC zDenG-1
 have hu_le:‖u‖ ≤ 1/100000:=by
  have hu_eq:u=toC (zNumG.1-zDenG.1,zNumG.2-zDenG.2)/toC zDenG:=by
   have hsub:toC (zNumG.1-zDenG.1,zNumG.2-zDenG.2)=toC zNumG-toC zDenG:=by
    unfold toC;push_cast;ring
   rw [hsub,sub_div,div_self hden_ne]
  rw [hu_eq,norm_div,div_le_iff₀ (norm_pos_iff.mpr hden_ne)]
  have hsq:‖toC (zNumG.1-zDenG.1,zNumG.2-zDenG.2)‖^2*100000^2 < ‖toC zDenG‖^2:=by
   rw [Complex.sq_norm,Complex.sq_norm,z134,z134]
   exact_mod_cast z252.1.1
  nlinarith [norm_nonneg (toC (zNumG.1-zDenG.1,zNumG.2-zDenG.2)),norm_nonneg (toC zDenG)]
 have h1u:toC zNumG/toC zDenG=1+u:=by simp [u]
 rw [h1u]
 exact (z140 (hu_le.trans (by norm_num))).trans (by linarith)
private lemma z76 :
  Complex.exp (wPot z284-z284*dwPot z284)=toC wNumG/toC wDenG:=by
 have hz_re:(0:ℝ)< z284.re:=by unfold z284;simp
 have h27_re:z284.re< 27:=by unfold z284;simp;norm_num
 have hne:∀ c:ℂ,0< c.re→ c≠0:=fun c hc h0=>by simp [h0] at hc
 have hsub:wPot z284-z284*dwPot z284 =
   I*(Real.pi:ℂ) +
    (∑ u∈Finset.Icc (1:ℕ) 10,(((35-2*u:ℕ):ℂ)*Complex.log ((35-2*u:ℕ):ℂ))) -
    162*Complex.log 27 +
    81*Complex.log (27-z284) +
    192*Complex.log (z284+64) -
    111*Complex.log (z284+37) +
    ∑ u∈Finset.Icc (1:ℕ) 10,
     ((((1+u:ℕ):ℂ)*Complex.log (z284+((1+u:ℕ):ℂ))) -
      (((36-u:ℕ):ℂ)*Complex.log (z284+((36-u:ℕ):ℂ)))):=by
  unfold wPot dwPot
  simp only [mul_add,mul_sub,Finset.mul_sum]
  have hsum_sub:(∑ u∈Finset.Icc (1:ℕ) 10,
    ((z284+((1+u:ℕ):ℂ))*Complex.log (z284+((1+u:ℕ):ℂ)) -
     (z284+((36-u:ℕ):ℂ))*Complex.log (z284+((36-u:ℕ):ℂ)))) -
    (∑ u∈Finset.Icc (1:ℕ) 10,
     (z284*Complex.log (z284+((1+u:ℕ):ℂ))-z284*Complex.log (z284+((36-u:ℕ):ℂ)))) =
    ∑ u∈Finset.Icc (1:ℕ) 10,
     ((((1+u:ℕ):ℂ)*Complex.log (z284+((1+u:ℕ):ℂ))) -
      (((36-u:ℕ):ℂ)*Complex.log (z284+((36-u:ℕ):ℂ)))):=by
   rw [← Finset.sum_sub_distrib]
   refine Finset.sum_congr rfl fun u _=>by ring
  linear_combination hsum_sub
 rw [hsub]
 simp only [Complex.exp_add,Complex.exp_sub,Complex.exp_sum]
 rw [show I*(Real.pi:ℂ)=(Real.pi:ℂ)*I by ring,Complex.exp_pi_mul_I]
 have hlog_pow:∀ (k:ℕ) (c:ℂ),0< c.re →
   Complex.exp ((k:ℂ)*Complex.log c)=c^k:=by
  intro k c hc
  rw [Complex.exp_nat_mul,Complex.exp_log (hne c hc)]
 have h162:Complex.exp (162*Complex.log (27:ℂ))=(27:ℂ)^162:=by
  simpa using hlog_pow 162 27 (by norm_num)
 have h81:Complex.exp (81*Complex.log (27-z284))=(27-z284)^81:=by
  simpa using hlog_pow 81 (27-z284) (by simp;linarith)
 have h192:Complex.exp (192*Complex.log (z284+64))=(z284+64)^192:=by
  simpa using hlog_pow 192 (z284+64) (by simp;linarith)
 have h111:Complex.exp (111*Complex.log (z284+37))=(z284+37)^111:=by
  simpa using hlog_pow 111 (z284+37) (by simp;linarith)
 have hcprod:(∏ u∈Finset.Icc (1:ℕ) 10,
   Complex.exp (((35-2*u:ℕ):ℂ)*Complex.log ((35-2*u:ℕ):ℂ))) =
   ∏ u∈Finset.Icc (1:ℕ) 10,((35-2*u:ℕ):ℂ)^(35-2*u):=
  Finset.prod_congr rfl fun u hu=>hlog_pow _ _ (by
   have:=(Finset.mem_Icc.mp hu).2;simp;omega)
 have huprod:(∏ u∈Finset.Icc (1:ℕ) 10,
   Complex.exp (((1+u:ℕ):ℂ)*Complex.log (z284+((1+u:ℕ):ℂ))) /
    Complex.exp (((36-u:ℕ):ℂ)*Complex.log (z284+((36-u:ℕ):ℂ)))) =
   (∏ u∈Finset.Icc (1:ℕ) 10,(z284+((1+u:ℕ):ℂ))^(1+u)) /
   (∏ u∈Finset.Icc (1:ℕ) 10,(z284+((36-u:ℕ):ℂ))^(36-u)):=by
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun u _=>by
   rw [hlog_pow _ _ (by simp;positivity),hlog_pow _ _ (by simp;positivity)]
 rw [h162,h81,h192,h111,hcprod,huprod]
 have h10z:∀ (a:ℤ) (k:ℕ),toC (234790+a*10000,-33282)^k =
   (10000:ℂ)^k*(z284+(a:ℂ))^k:=by
  intro a k
  rw [← mul_pow];congr 1;unfold z284 toC;push_cast;ring
 have h10z_add:∀ k:ℕ,toC (234790+(2+(k:ℤ))*10000,-33282)^(2+k) =
   (10000:ℂ)^(2+k)*(z284+((1+(k+1):ℕ):ℂ))^(1+(k+1)):=by
  intro k
  rw [show (2+k:ℕ)=1+(k+1) by omega,← mul_pow]
  congr 1;unfold z284 toC;push_cast;ring
 have h10z_sub:∀ k:ℕ,k ≤ 9→ toC (234790+(35-(k:ℤ))*10000,-33282)^(35-k) =
   (10000:ℂ)^(35-k)*(z284+((36-(k+1):ℕ):ℂ))^(36-(k+1)):=by
  intro k hk
  have hnat:36-(k+1)=35-k:=by omega
  rw [hnat,← mul_pow]
  congr 1
  rw [Nat.cast_sub (by omega)];unfold z284 toC;push_cast;ring
 have h10z27:toC (27*10000-234790,-(-33282))^81 =
   (10000:ℂ)^81*(27-z284)^81:=by
  rw [← mul_pow];congr 1;unfold z284 toC;push_cast;ring
 have hrange10:List.range 10=[0,1,2,3,4,5,6,7,8,9]:=rfl
 have hnum_eq:toC wNumG =
   (10000:ℂ)^416*((-1:ℂ) *
    (∏ u∈Finset.Icc (1:ℕ) 10,((35-2*u:ℕ):ℂ)^(35-2*u)) *
    (27-z284)^81*(z284+64)^192 *
    (∏ u∈Finset.Icc (1:ℕ) 10,(z284+((1+u:ℕ):ℂ))^(1+u))):=by
  have hfold_prod:∀ (init:ℤ × ℤ),
    toC ((List.range 10).foldl (fun acc (k:ℕ)=>gMul acc (gPow (234790+(2+(k:ℤ))*10000,-33282) (2+k))) init) =
    toC init*(10000:ℂ)^65*∏ u∈Finset.Icc (1:ℕ) 10,(z284+((1+u:ℕ):ℂ))^(1+u):=by
   intro init
   rw [hrange10,z184]
   simp only [List.foldl_cons,List.foldl_nil,z270,z271]
   rw [h10z_add 0,h10z_add 1,h10z_add 2,h10z_add 3,h10z_add 4,
    h10z_add 5,h10z_add 6,h10z_add 7,h10z_add 8,h10z_add 9]
   have h65:∀ x:ℂ,x^65 =
     x^(2+0)*x^(2+1)*x^(2+2) *
     x^(2+3)*x^(2+4)*x^(2+5) *
     x^(2+6)*x^(2+7)*x^(2+8) *
     x^(2+9):=fun x=>by simp only [← pow_add]
   rw [h65 (10000:ℂ)]
   generalize toC init=I0
   generalize (10000:ℂ)^(2+0)=a0;generalize (10000:ℂ)^(2+1)=a1
   generalize (10000:ℂ)^(2+2)=a2;generalize (10000:ℂ)^(2+3)=a3
   generalize (10000:ℂ)^(2+4)=a4;generalize (10000:ℂ)^(2+5)=a5
   generalize (10000:ℂ)^(2+6)=a6;generalize (10000:ℂ)^(2+7)=a7
   generalize (10000:ℂ)^(2+8)=a8;generalize (10000:ℂ)^(2+9)=a9
   generalize (z284+((1+1:ℕ):ℂ))^(1+1)=b0
   generalize (z284+((1+2:ℕ):ℂ))^(1+2)=b1
   generalize (z284+((1+3:ℕ):ℂ))^(1+3)=b2
   generalize (z284+((1+4:ℕ):ℂ))^(1+4)=b3
   generalize (z284+((1+5:ℕ):ℂ))^(1+5)=b4
   generalize (z284+((1+6:ℕ):ℂ))^(1+6)=b5
   generalize (z284+((1+7:ℕ):ℂ))^(1+7)=b6
   generalize (z284+((1+8:ℕ):ℂ))^(1+8)=b7
   generalize (z284+((1+9:ℕ):ℂ))^(1+9)=b8
   generalize (z284+((1+10:ℕ):ℂ))^(1+10)=b9
   ring
  have hcnum_eq:(((List.range 10).foldl (fun acc (k:ℕ)=>acc*((33-2*k:ℕ):ℤ)^(33-2*k)) 1:ℤ):ℂ) =
    ∏ u∈Finset.Icc (1:ℕ) 10,((35-2*u:ℕ):ℂ)^(35-2*u):=by
   rw [hrange10,z184]
   simp only [List.foldl_cons,List.foldl_nil,Int.cast_mul,Int.cast_pow,Int.cast_natCast,one_mul]
  unfold wNumG
  dsimp only
  rw [hfold_prod,z270,z270,z271,z271,h10z27,h10z 64 192]
  have htoC0:∀ x:ℤ,toC (x,0)=(x:ℂ):=fun x=>by unfold toC;simp
  rw [htoC0,Int.cast_mul,Int.cast_neg,Int.cast_pow,Int.cast_ofNat,hcnum_eq]
  have h64:((64:ℤ):ℂ)=(64:ℂ):=by norm_num
  rw [h64]
  have h416:∀ x:ℂ,x^416=x^78*x^81*x^192*x^65:=fun x=>by
   simp only [← pow_add]
  rw [h416 (10000:ℂ)]
  generalize (10000:ℂ)^78=d1;generalize (10000:ℂ)^81=d2
  generalize (10000:ℂ)^192=d3;generalize (10000:ℂ)^65=d4
  generalize (27-z284)^81=A;generalize (z284+64)^192=B
  ring
 have hden_eq:toC wDenG =
   (10000:ℂ)^416*((27:ℂ)^162*(z284+37)^111 *
    (∏ u∈Finset.Icc (1:ℕ) 10,(z284+((36-u:ℕ):ℂ))^(36-u))):=by
  have hfold_prod:∀ (init:ℤ × ℤ),
    toC ((List.range 10).foldl (fun acc (k:ℕ)=>gMul acc (gPow (234790+(35-(k:ℤ))*10000,-33282) (35-k))) init) =
    toC init*(10000:ℂ)^305*∏ u∈Finset.Icc (1:ℕ) 10,(z284+((36-u:ℕ):ℂ))^(36-u):=by
   intro init
   rw [hrange10,z184]
   simp only [List.foldl_cons,List.foldl_nil,z270,z271]
   rw [h10z_sub 0 (by omega),h10z_sub 1 (by omega),h10z_sub 2 (by omega),
    h10z_sub 3 (by omega),h10z_sub 4 (by omega),h10z_sub 5 (by omega),
    h10z_sub 6 (by omega),h10z_sub 7 (by omega),h10z_sub 8 (by omega),
    h10z_sub 9 (by omega)]
   have h305:∀ x:ℂ,x^305 =
     x^(35-0)*x^(35-1)*x^(35-2) *
     x^(35-3)*x^(35-4)*x^(35-5) *
     x^(35-6)*x^(35-7)*x^(35-8) *
     x^(35-9):=fun x=>by simp only [← pow_add]
   rw [h305 (10000:ℂ)]
   generalize toC init=I0
   generalize (10000:ℂ)^(35-0)=a0;generalize (10000:ℂ)^(35-1)=a1
   generalize (10000:ℂ)^(35-2)=a2;generalize (10000:ℂ)^(35-3)=a3
   generalize (10000:ℂ)^(35-4)=a4;generalize (10000:ℂ)^(35-5)=a5
   generalize (10000:ℂ)^(35-6)=a6;generalize (10000:ℂ)^(35-7)=a7
   generalize (10000:ℂ)^(35-8)=a8;generalize (10000:ℂ)^(35-9)=a9
   generalize (z284+((36-1:ℕ):ℂ))^(36-1)=b0
   generalize (z284+((36-2:ℕ):ℂ))^(36-2)=b1
   generalize (z284+((36-3:ℕ):ℂ))^(36-3)=b2
   generalize (z284+((36-4:ℕ):ℂ))^(36-4)=b3
   generalize (z284+((36-5:ℕ):ℂ))^(36-5)=b4
   generalize (z284+((36-6:ℕ):ℂ))^(36-6)=b5
   generalize (z284+((36-7:ℕ):ℂ))^(36-7)=b6
   generalize (z284+((36-8:ℕ):ℂ))^(36-8)=b7
   generalize (z284+((36-9:ℕ):ℂ))^(36-9)=b8
   generalize (z284+((36-10:ℕ):ℂ))^(36-10)=b9
   ring
  unfold wDenG
  dsimp only
  rw [hfold_prod,z270,z271,h10z 37 111]
  have htoC0:toC ((27:ℤ)^162,0)=(27:ℂ)^162:=by
   unfold toC;simp only [Int.cast_zero,zero_mul,add_zero,Int.cast_pow,Int.cast_ofNat]
  rw [htoC0]
  have h37:((37:ℤ):ℂ)=(37:ℂ):=by norm_num
  rw [h37]
  have h416:∀ x:ℂ,x^416=x^111*x^305:=fun x=>by
   simp only [← pow_add]
  rw [h416 (10000:ℂ)]
  generalize (10000:ℂ)^111=d1;generalize (10000:ℂ)^305=d2
  generalize (27:ℂ)^162=A;generalize (z284+37)^111=B
  ring
 have hrewrite :
   (-1:ℂ)*(∏ u∈Finset.Icc (1:ℕ) 10,((35-2*u:ℕ):ℂ)^(35-2*u)) /
    (27:ℂ)^162*(27-z284)^81*(z284+64)^192/(z284+37)^111 *
    ((∏ u∈Finset.Icc (1:ℕ) 10,(z284+((1+u:ℕ):ℂ))^(1+u)) /
     (∏ u∈Finset.Icc (1:ℕ) 10,(z284+((36-u:ℕ):ℂ))^(36-u))) =
   ((-1:ℂ)*(∏ u∈Finset.Icc (1:ℕ) 10,((35-2*u:ℕ):ℂ)^(35-2*u)) *
    (27-z284)^81*(z284+64)^192 *
    (∏ u∈Finset.Icc (1:ℕ) 10,(z284+((1+u:ℕ):ℂ))^(1+u))) /
   ((27:ℂ)^162*(z284+37)^111 *
    (∏ u∈Finset.Icc (1:ℕ) 10,(z284+((36-u:ℕ):ℂ))^(36-u))):=by
  have hgen:∀ (x1 x2 x3 x4 x5 x6 x7:ℂ),
    (-1:ℂ)*x1/x2*x3*x4/x5*(x6/x7) =
    ((-1:ℂ)*x1*x3*x4*x6)/(x2*x5*x7):=fun _ _ _ _ _ _ _=>by
   simp only [div_eq_mul_inv,mul_inv];ring
  exact hgen _ _ _ _ _ _ _
 rw [hrewrite,hnum_eq,hden_eq,mul_div_mul_left _ _ (pow_ne_zero 416 (by norm_num))]
private lemma z54 :
  (z53 z284).re∈Set.Icc (707/1000:ℝ) (708/1000) ∧
  (z53 z284).im∈Set.Icc (-384/1000:ℝ) (-382/1000):=by
 unfold z53 z284
 rw [z263]
 simp only [Complex.add_re,Complex.sub_re,Complex.div_re,Complex.add_im,Complex.sub_im,
  Complex.div_im,Complex.normSq_apply,Complex.re_ofNat,Complex.im_ofNat,Complex.one_re,
  Complex.one_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
  Complex.natCast_re,Complex.natCast_im]
 constructor <;> constructor <;> norm_num
theorem z73 :
  ∃ z₀:ℂ,
   ‖z₀-z284‖ ≤ 1/1000 ∧
   dwPot z₀=0 ∧
   (wPot z₀).re ≤ -227.4 ∧
   (1/4:ℝ) ≤ |Real.sin (wPot z₀).im| ∧
   (1/2:ℝ) ≤ (z53 z₀).re ∧
   ‖z53 z₀‖ ≤ 1:=by
 let A:ℂ:=(109:ℂ)/100+((59:ℂ)/100)*I
 let s:Set ℂ:=Metric.closedBall z284 (1/1000)
 let f:ℂ→ ℂ:=fun z=>z-A*dwPot z
 have hA_norm:‖A‖ ≤ 5/4:=by
  have hsq:‖A‖^2 ≤ (5/4:ℝ)^2:=by
   rw [Complex.sq_norm,Complex.normSq_apply]
   simp only [A,Complex.add_re,Complex.div_ofNat_re,Complex.re_ofNat,Complex.mul_re,
    Complex.I_re,mul_zero,Complex.div_ofNat_im,Complex.im_ofNat,Complex.I_im,mul_one,
    sub_self,add_zero,Complex.add_im,zero_add,Complex.mul_im]
   norm_num
  nlinarith [norm_nonneg A]
 have hs_re:∀ z∈s,(234/10:ℝ) ≤ z.re∧z.re ≤ (236/10:ℝ):=by
  intro z hz
  have hd:‖z-z284‖ ≤ 1/1000:=by simpa [s,dist_eq_norm] using hz
  have hre:=(Complex.abs_re_le_norm (z-z284)).trans hd
  have hzt:z284.re=23479/1000:=by unfold z284;simp;norm_num
  simp only [Complex.sub_re,hzt] at hre
  constructor <;> linarith [abs_le.mp hre]
 have hd3_le:∀ z∈s,‖z55 z‖ ≤ 1:=by
  intro z hz
  have hre:=hs_re z hz
  have hinv_le:∀ (c:ℂ) (r:ℝ),0< r→ r ≤ c.re→ ‖1/c^2‖ ≤ 1/r^2:=by
   intro c r hr hcr
   rw [one_div,norm_inv,norm_pow,← one_div]
   refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
   have:=hcr.trans (Complex.re_le_norm c)
   nlinarith
  have hinv3_le:∀ (c:ℂ) (r:ℝ),0< r→ r ≤ c.re→ ‖(3:ℂ)/c^2‖ ≤ 3/r^2:=by
   intro c r hr hcr
   rw [show (3:ℂ)/c^2=3*(1/c^2) by ring,norm_mul,Complex.norm_ofNat,
    show (3:ℝ)/r^2=3*(1/r^2) by ring]
   have:=hinv_le c r hr hcr;linarith
  unfold z55
  have h1:‖(-3:ℂ)/z^2‖ ≤ 3/(23:ℝ)^2:=by
   rw [neg_div,norm_neg];exact hinv3_le z 23 (by norm_num) (by linarith [hre.1])
  have h2:‖(3:ℂ)/(27-z)^2‖ ≤ 3/(3:ℝ)^2:=
   hinv3_le (27-z) 3 (by norm_num) (by simp;linarith [hre.2])
  have h3:‖(3:ℂ)/(z+64)^2‖ ≤ 3/(80:ℝ)^2:=
   hinv3_le (z+64) 80 (by norm_num) (by simp;linarith [hre.1])
  have h4:‖(3:ℂ)/(z+37)^2‖ ≤ 3/(60:ℝ)^2:=
   hinv3_le (z+37) 60 (by norm_num) (by simp;linarith [hre.1])
  have h5:‖∑ u∈Finset.Icc (1:ℕ) 10,
    (-1/(z+((1+u:ℕ):ℂ))^2+1/(z+((36-u:ℕ):ℂ))^2)‖ ≤
    10*(2/(20:ℝ)^2):=by
   refine (norm_sum_le _ _).trans ?_
   calc
    ∑ u∈Finset.Icc (1:ℕ) 10,
      ‖-1/(z+((1+u:ℕ):ℂ))^2+1/(z+((36-u:ℕ):ℂ))^2‖
     ≤ ∑ _u∈Finset.Icc (1:ℕ) 10,(2/(20:ℝ)^2):=by
      refine Finset.sum_le_sum fun u _=>?_
      refine (norm_add_le _ _).trans ?_
      rw [neg_div,norm_neg]
      have ha:=hinv_le (z+((1+u:ℕ):ℂ)) 20 (by norm_num) (by simp;linarith [hre.1,Nat.cast_nonneg (α:=ℝ) u])
      have hb:=hinv_le (z+((36-u:ℕ):ℂ)) 20 (by norm_num) (by simp;linarith [hre.1,Nat.cast_nonneg (α:=ℝ) (36-u)])
      linarith
    _=10*(2/(20:ℝ)^2):=by norm_num
  have htri:‖(-3:ℂ)/z^2+3/(27-z)^2-3/(z+64)^2+3/(z+37)^2 +
    ∑ u∈Finset.Icc (1:ℕ) 10,
     (-1/(z+((1+u:ℕ):ℂ))^2+1/(z+((36-u:ℕ):ℂ))^2)‖ ≤
    ‖(-3:ℂ)/z^2‖+‖(3:ℂ)/(27-z)^2‖+‖(3:ℂ)/(z+64)^2‖ +
     ‖(3:ℂ)/(z+37)^2‖ +
     ‖∑ u∈Finset.Icc (1:ℕ) 10,
      (-1/(z+((1+u:ℕ):ℂ))^2+1/(z+((36-u:ℕ):ℂ))^2)‖:=by
   have t1:=norm_add_le (-3/z^2+3/(27-z)^2-3/(z+64)^2+3/(z+37)^2)
    (∑ u∈Finset.Icc (1:ℕ) 10,(-1/(z+((1+u:ℕ):ℂ))^2+1/(z+((36-u:ℕ):ℂ))^2))
   have t2:=norm_add_le (-3/z^2+3/(27-z)^2-3/(z+64)^2) (3/(z+37)^2)
   have t3:=norm_sub_le (-3/z^2+3/(27-z)^2) (3/(z+64)^2)
   have t4:=norm_add_le (-3/z^2) (3/(27-z)^2)
   linarith
  linarith
 have hd2_zt:‖1-A*z53 z284‖ ≤ 1/100 ∧
   (6/10:ℝ) ≤ (z53 z284).re∧‖z53 z284‖ ≤ 9/10:=by
  have hd2_re_im:=z54
  set a:=(z53 z284).re
  set b:=(z53 z284).im
  have hre1:(1-A*z53 z284).re=1-(109/100*a-59/100*b):=by
   simp only [A,a,b,Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.add_re,
    Complex.div_ofNat_re,Complex.re_ofNat,Complex.I_re,mul_zero,Complex.div_ofNat_im,
    Complex.im_ofNat,Complex.I_im,mul_one,sub_self,add_zero,Complex.add_im,zero_add,
    Complex.mul_im]
   ring
  have him1:(1-A*z53 z284).im=-(109/100*b+59/100*a):=by
   simp only [A,a,b,Complex.sub_im,Complex.one_im,Complex.mul_im,Complex.add_re,
    Complex.div_ofNat_re,Complex.re_ofNat,Complex.I_re,mul_zero,Complex.div_ofNat_im,
    Complex.im_ofNat,Complex.I_im,mul_one,sub_self,add_zero,Complex.add_im,zero_add,
    Complex.mul_re]
   ring
  refine ⟨?_,by linarith [hd2_re_im.1.1],?_⟩
  ·
   have hsq:‖1-A*z53 z284‖^2 ≤ (1/100:ℝ)^2:=by
    rw [Complex.sq_norm,Complex.normSq_apply,hre1,him1]
    nlinarith [hd2_re_im.1.1,hd2_re_im.1.2,hd2_re_im.2.1,hd2_re_im.2.2]
   nlinarith [norm_nonneg (1-A*z53 z284)]
  ·
   have hsq:‖z53 z284‖^2 ≤ (9/10:ℝ)^2:=by
    rw [Complex.sq_norm,Complex.normSq_apply]
    change a*a+b*b ≤ (9/10:ℝ)^2
    nlinarith [hd2_re_im.1.1,hd2_re_im.1.2,hd2_re_im.2.1,hd2_re_im.2.2]
   nlinarith [norm_nonneg (z53 z284)]
 have hf_deriv:∀ z∈s,HasDerivAt f (1-A*z53 z) z:=by
  intro z hz
  have hre:=hs_re z hz
  have hd:=(z95 (by linarith [hre.1]) (by linarith [hre.2])).const_mul A
  exact (hasDerivAt_id z).fun_sub hd
 have hf_deriv_le:∀ z∈s,‖deriv f z‖ ≤ 1/10:=by
  intro z hz
  rw [(hf_deriv z hz).deriv]
  have hd2_diff:‖z53 z-z53 z284‖ ≤ 1/1000:=by
   have hmvt:=Convex.norm_image_sub_le_of_norm_deriv_le (f:=z53) (s:=s) (C:=1)
    (fun w hw=>(z94 (by linarith [(hs_re w hw).1]) (by linarith [(hs_re w hw).2])).differentiableAt)
    (fun w hw=>by
     rw [(z94 (by linarith [(hs_re w hw).1]) (by linarith [(hs_re w hw).2])).deriv]
     exact hd3_le w hw)
    (convex_closedBall z284 _)
    (Metric.mem_closedBall_self (by norm_num)) hz
   have hdist:‖z-z284‖ ≤ 1/1000:=by simpa [s,dist_eq_norm] using hz
   linarith
  have hsplit:1-A*z53 z=(1-A*z53 z284)-A*(z53 z-z53 z284):=by ring
  rw [hsplit]
  calc
   ‖(1-A*z53 z284)-A*(z53 z-z53 z284)‖
    ≤ ‖1-A*z53 z284‖+‖A*(z53 z-z53 z284)‖:=norm_sub_le _ _
   _=‖1-A*z53 z284‖+‖A‖*‖z53 z-z53 z284‖:=by rw [norm_mul]
   _ ≤ 1/100+(5/4)*(1/1000):=add_le_add hd2_zt.1
     (mul_le_mul hA_norm hd2_diff (norm_nonneg _) (by norm_num))
   _ ≤ 1/10:=by norm_num
 have hf_lip:∀ x∈s,∀ y∈s,‖f x-f y‖ ≤ (1/10:ℝ)*‖x-y‖:=by
  intro x hx y hy
  exact Convex.norm_image_sub_le_of_norm_deriv_le
   (fun w hw=>(hf_deriv w hw).differentiableAt) hf_deriv_le (convex_closedBall z284 _) hy hx
 have hf_maps:Set.MapsTo f s s:=by
  intro z hz
  have hz_mem:z∈s:=hz
  simp only [s,Metric.mem_closedBall,dist_eq_norm] at hz ⊢
  have hfz:‖f z-f z284‖ ≤ (1/10:ℝ)*‖z-z284‖:=
   hf_lip z hz_mem z284 (Metric.mem_closedBall_self (by norm_num))
  have h0:‖f z284-z284‖ ≤ 5/4*(2/100000):=by
   have:f z284-z284=-(A*dwPot z284):=by simp [f]
   rw [this,norm_neg,norm_mul]
   exact mul_le_mul hA_norm z139 (norm_nonneg _) (by norm_num)
  calc
   ‖f z-z284‖=‖(f z-f z284)+(f z284-z284)‖:=by ring_nf
   _ ≤ ‖f z-f z284‖+‖f z284-z284‖:=norm_add_le _ _
   _ ≤ (1/10)*(1/1000)+5/4*(2/100000):=by linarith [hfz,h0,hz]
   _ ≤ 1/1000:=by norm_num
 let K:NNReal:=⟨1/10,by norm_num⟩
 have hcontr:ContractingWith K (hf_maps.restrict f s s):=by
  refine ⟨?_,?_⟩
  ·
   change (1/10:ℝ)< 1;norm_num
  ·
   refine LipschitzWith.of_dist_le_mul fun ⟨x,hx⟩ ⟨y,hy⟩=>?_
   rw [Subtype.dist_eq,Subtype.dist_eq,dist_eq_norm,dist_eq_norm]
   exact hf_lip x hx y hy
 obtain ⟨z₀,hz₀_mem,hz₀_fix,_,_⟩:=ContractingWith.exists_fixedPoint'
  (Metric.isClosed_closedBall.isComplete) hf_maps hcontr (Metric.mem_closedBall_self (by norm_num))
  (edist_ne_top _ _)
 have hz₀_dist:‖z₀-z284‖ ≤ 1/1000:=by simpa [s,dist_eq_norm] using hz₀_mem
 have hA_ne:A≠0:=by
  intro h;have:=congr_arg Complex.re h
  simp only [A,Complex.add_re,Complex.div_ofNat_re,Complex.re_ofNat,Complex.mul_re,
   Complex.I_re,mul_zero,Complex.div_ofNat_im,Complex.im_ofNat,Complex.I_im,mul_one,
   sub_self,add_zero,Complex.zero_re] at this
  norm_num at this
 have hdw0:dwPot z₀=0:=by
  have hfix:z₀-A*dwPot z₀=z₀:=hz₀_fix
  have hmul0:A*dwPot z₀=0:=by linear_combination -hfix
  exact (mul_eq_zero.mp hmul0).resolve_left hA_ne
 have hd2_diff0:‖z53 z₀-z53 z284‖ ≤ 1/1000:=by
  have hmvt:=Convex.norm_image_sub_le_of_norm_deriv_le (f:=z53) (s:=s) (C:=1)
   (fun w hw=>(z94 (by linarith [(hs_re w hw).1]) (by linarith [(hs_re w hw).2])).differentiableAt)
   (fun w hw=>by
    rw [(z94 (by linarith [(hs_re w hw).1]) (by linarith [(hs_re w hw).2])).deriv]
    exact hd3_le w hw)
   (convex_closedBall z284 _) (Metric.mem_closedBall_self (by norm_num)) hz₀_mem
  linarith
 have hd2_re0:(1/2:ℝ) ≤ (z53 z₀).re:=by
  have hre:=(Complex.abs_re_le_norm (z53 z₀-z53 z284)).trans hd2_diff0
  simp only [Complex.sub_re] at hre
  linarith [abs_le.mp hre,hd2_zt.2.1]
 have hd2_norm0:‖z53 z₀‖ ≤ 1:=by
  calc
   ‖z53 z₀‖=‖z53 z284+(z53 z₀-z53 z284)‖:=by ring_nf
   _ ≤ ‖z53 z284‖+‖z53 z₀-z53 z284‖:=norm_add_le _ _
   _ ≤ 9/10+1/1000:=add_le_add hd2_zt.2.2 hd2_diff0
   _ ≤ 1:=by norm_num
 have hdw_on_s:∀ z∈s,‖dwPot z‖ ≤ 2/1000:=by
  intro z hz
  have hd2_on_s:∀ w∈s,‖z53 w‖ ≤ 1:=by
   intro w hw
   have hmvt:=Convex.norm_image_sub_le_of_norm_deriv_le (f:=z53) (s:=s) (C:=1)
    (fun u hu=>(z94 (by linarith [(hs_re u hu).1]) (by linarith [(hs_re u hu).2])).differentiableAt)
    (fun u hu=>by
     rw [(z94 (by linarith [(hs_re u hu).1]) (by linarith [(hs_re u hu).2])).deriv]
     exact hd3_le u hu)
    (convex_closedBall z284 _) (Metric.mem_closedBall_self (by norm_num)) hw
   have hw_d:‖w-z284‖ ≤ 1/1000:=by simpa [s,dist_eq_norm] using hw
   calc
    ‖z53 w‖=‖z53 z284+(z53 w-z53 z284)‖:=by ring_nf
    _ ≤ ‖z53 z284‖+‖z53 w-z53 z284‖:=norm_add_le _ _
    _ ≤ 9/10+1/1000:=by linarith [hd2_zt.2.2]
    _ ≤ 1:=by norm_num
  have hmvt:=Convex.norm_image_sub_le_of_norm_deriv_le (f:=dwPot) (s:=s) (C:=1)
   (fun w hw=>(z95 (by linarith [(hs_re w hw).1]) (by linarith [(hs_re w hw).2])).differentiableAt)
   (fun w hw=>by
    rw [(z95 (by linarith [(hs_re w hw).1]) (by linarith [(hs_re w hw).2])).deriv]
    exact hd2_on_s w hw)
   (convex_closedBall z284 _) (Metric.mem_closedBall_self (by norm_num)) hz
  have hz_d:‖z-z284‖ ≤ 1/1000:=by simpa [s,dist_eq_norm] using hz
  calc
   ‖dwPot z‖=‖dwPot z284+(dwPot z-dwPot z284)‖:=by ring_nf
   _ ≤ ‖dwPot z284‖+‖dwPot z-dwPot z284‖:=norm_add_le _ _
   _ ≤ 2/100000+1/1000:=by linarith [z139]
   _ ≤ 2/1000:=by norm_num
 have hw_diff:‖wPot z₀-(wPot z284-z284*dwPot z284)‖ ≤ 1/1000:=by
  have hmvt:=Convex.norm_image_sub_le_of_norm_deriv_le (f:=wPot) (s:=s) (C:=2/1000)
   (fun w hw=>(z100 (by linarith [(hs_re w hw).1]) (by linarith [(hs_re w hw).2])).differentiableAt)
   (fun w hw=>by
    rw [(z100 (by linarith [(hs_re w hw).1]) (by linarith [(hs_re w hw).2])).deriv]
    exact hdw_on_s w hw)
   (convex_closedBall z284 _) (Metric.mem_closedBall_self (by norm_num)) hz₀_mem
  have hzt_norm:‖z284‖ ≤ 25:=by
   have hsq:‖z284‖^2 ≤ 25^2:=by
    rw [Complex.sq_norm,Complex.normSq_apply]
    unfold z284
    simp only [Complex.sub_re,Complex.div_ofNat_re,Complex.re_ofNat,Complex.mul_re,
     Complex.I_re,mul_zero,Complex.div_ofNat_im,Complex.im_ofNat,Complex.I_im,mul_one,
     sub_self,sub_zero,Complex.sub_im,zero_sub,Complex.mul_im]
    norm_num
   nlinarith [norm_nonneg z284]
  calc
   ‖wPot z₀-(wPot z284-z284*dwPot z284)‖
    = ‖(wPot z₀-wPot z284)+z284*dwPot z284‖:=by ring_nf
   _ ≤ ‖wPot z₀-wPot z284‖+‖z284*dwPot z284‖:=norm_add_le _ _
   _=‖wPot z₀-wPot z284‖+‖z284‖*‖dwPot z284‖:=by rw [norm_mul]
   _ ≤ (2/1000)*(1/1000)+25*(2/100000):=by
     have:=mul_le_mul hzt_norm z139 (norm_nonneg _) (by norm_num)
     nlinarith [hmvt,hz₀_dist]
   _ ≤ 1/1000:=by norm_num
 set W:=wPot z284-z284*dwPot z284
 have hW_exp:Complex.exp W=toC wNumG/toC wDenG:=z76
 have hW_den_pos:(0:ℝ)< Complex.normSq (toC wDenG):=by
  rw [z134];exact_mod_cast z252.2.1.2
 have hW_den_ne:toC wDenG≠0:=Complex.normSq_pos.mp hW_den_pos
 have hW_re:W.re ≤ -227.5:=by
  have hnormW:Real.exp W.re=‖toC wNumG‖ / ‖toC wDenG‖:=by
   rw [← Complex.norm_exp,hW_exp,norm_div]
  have hW_lt:‖toC wNumG‖ / ‖toC wDenG‖ < 1/(68*(10:ℝ)^97):=by
   rw [div_lt_div_iff₀ (norm_pos_iff.mpr hW_den_ne) (by positivity),one_mul]
   have hsq:‖toC wNumG‖^2*(68*(10:ℝ)^97)^2 < ‖toC wDenG‖^2:=by
    rw [Complex.sq_norm,Complex.sq_norm,z134,z134]
    exact_mod_cast z252.2.1.1
   nlinarith [norm_nonneg (toC wNumG),norm_nonneg (toC wDenG)]
  have hexp_lt:Real.exp 455< (68*(10:ℝ)^97)^2:=by
   have he:Real.exp 1< (2718281829:ℝ)/(10:ℝ)^9:=by
    have:=Real.exp_one_lt_d9;linarith
   have hpow:(Real.exp 1)^455< ((2718281829:ℝ)/(10:ℝ)^9)^455:=
    pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
   rw [← Real.exp_nat_mul,mul_one] at hpow
   refine hpow.trans ?_
   rw [div_pow,div_lt_iff₀ (by positivity),← pow_mul]
   have h5:((2718281829:ℝ)^455)< ((10:ℝ)^(9*455))*(68*(10:ℝ)^97)^2:=by
    exact_mod_cast z252.2.2.1
   linarith
  have hexp_227:Real.exp 227.5< 68*(10:ℝ)^97:=by
   have hsq:(Real.exp 227.5)^2=Real.exp 455:=by
    rw [sq,← Real.exp_add];norm_num
   nlinarith [Real.exp_pos 227.5,hexp_lt]
  have hlt_exp:Real.exp W.re< Real.exp (-227.5):=by
   rw [hnormW,Real.exp_neg,← one_div]
   exact hW_lt.trans (one_div_lt_one_div_of_lt (Real.exp_pos _) hexp_227)
  exact (Real.exp_lt_exp.mp hlt_exp).le
 have hW_sin:(3/10:ℝ) ≤ |Real.sin W.im|:=by
  have hsin_eq:Real.sin W.im=(Complex.exp W).im / ‖Complex.exp W‖:=by
   rw [Complex.exp_im,Complex.norm_exp,mul_div_cancel_left₀ _ (Real.exp_pos _).ne']
  rw [hsin_eq,hW_exp,abs_div,abs_norm]
  have hnum_ne:toC wNumG≠0:=by
   intro h0
   have hexp0:Complex.exp W=0:=by rw [hW_exp,h0,zero_div]
   exact Complex.exp_ne_zero W hexp0
  have him_div:(toC wNumG/toC wDenG).im =
    ((gMul wNumG (wDenG.1,-wDenG.2)).2:ℝ)/Complex.normSq (toC wDenG):=by
   rw [Complex.div_im]
   unfold gMul toC
   simp only [Complex.add_re,Complex.intCast_re,Complex.mul_re,Complex.I_re,mul_zero,
    Complex.intCast_im,Complex.I_im,mul_one,sub_self,add_zero,Complex.add_im,zero_add,
    Complex.mul_im]
   push_cast;ring
  rw [him_div,abs_div,abs_of_pos hW_den_pos,norm_div]
  have hsq_pos:0 < ‖toC wNumG‖*‖toC wDenG‖:=
   mul_pos (norm_pos_iff.mpr hnum_ne) (norm_pos_iff.mpr hW_den_ne)
  have hsimp:|((gMul wNumG (wDenG.1,-wDenG.2)).2:ℝ)| / Complex.normSq (toC wDenG) /
    (‖toC wNumG‖ / ‖toC wDenG‖) =
    |((gMul wNumG (wDenG.1,-wDenG.2)).2:ℝ)| / (‖toC wNumG‖*‖toC wDenG‖):=by
   rw [← Complex.sq_norm]
   field_simp [(norm_pos_iff.mpr hnum_ne).ne',(norm_pos_iff.mpr hW_den_ne).ne']
  rw [hsimp,le_div_iff₀ hsq_pos]
  have hsq:9*(‖toC wNumG‖^2*‖toC wDenG‖^2) <
    ((gMul wNumG (wDenG.1,-wDenG.2)).2:ℝ)^2*100:=by
   rw [Complex.sq_norm,Complex.sq_norm,z134,z134]
   have h6:(9:ℝ)*(z87 wNumG:ℝ)*(z87 wDenG:ℝ) <
     ((gMul wNumG (wDenG.1,-wDenG.2)).2:ℝ)^2*100:=by
    exact_mod_cast z252.2.2.2
   linarith
  have habs_sq:|((gMul wNumG (wDenG.1,-wDenG.2)).2:ℝ)|^2 =
    ((gMul wNumG (wDenG.1,-wDenG.2)).2:ℝ)^2:=sq_abs _
  nlinarith [abs_nonneg ((gMul wNumG (wDenG.1,-wDenG.2)).2:ℝ),hsq_pos]
 have hw0_re:(wPot z₀).re ≤ -227.4:=by
  have h:=(Complex.abs_re_le_norm (wPot z₀-W)).trans hw_diff
  simp only [Complex.sub_re] at h
  linarith [abs_le.mp h,hW_re]
 have hw0_sin:(1/4:ℝ) ≤ |Real.sin (wPot z₀).im|:=by
  have him:=(Complex.abs_im_le_norm (wPot z₀-W)).trans hw_diff
  simp only [Complex.sub_im] at him
  have hlip:|Real.sin (wPot z₀).im-Real.sin W.im| ≤ |(wPot z₀).im-W.im|:=by
   simpa [Real.dist_eq] using Real.lipschitzWith_sin.dist_le_mul (wPot z₀).im W.im
  have htri:=abs_sub_abs_le_abs_sub (Real.sin W.im) (Real.sin (wPot z₀).im)
  rw [abs_sub_comm] at htri
  linarith
 exact ⟨z₀,hz₀_dist,hdw0,hw0_re,hw0_sin,hd2_re0,hd2_norm0⟩
lemma z247 {x y:ℝ} (hx1:(234/10:ℝ) ≤ x) (hx2:x ≤ (236/10:ℝ))
  (hy1:-37 ≤ y) (hy2:y ≤ 0) :
  (1/140:ℝ) ≤ (z53 ((x:ℂ)+(y:ℂ)*I)).re:=by
 have hinv_re:∀ (a:ℝ),(1/((a:ℂ)+(y:ℂ)*I)).re=a/(a^2+y^2):=by
  intro a
  rw [one_div,Complex.inv_re,Complex.normSq_apply]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,mul_zero,
   Complex.ofReal_im,Complex.I_im,mul_one,sub_self,add_zero,Complex.add_im,zero_add,
   Complex.mul_im]
  ring
 have hpair_pos:∀ (a b:ℝ),0< a→ a< b→ 37^2 ≤ a*b →
   0 ≤ (1/((a:ℂ)+(y:ℂ)*I)-1/((b:ℂ)+(y:ℂ)*I)).re:=by
  intro a b ha hab hab_sq
  rw [Complex.sub_re,hinv_re a,hinv_re b]
  have hda:0< a^2+y^2:=by positivity
  have hdb:0< b^2+y^2:=by nlinarith
  rw [div_sub_div _ _ hda.ne' hdb.ne']
  refine div_nonneg ?_ (mul_pos hda hdb).le
  have hnum:a*(b^2+y^2)-(a^2+y^2)*b=(b-a)*(a*b-y^2):=by ring
  rw [hnum]
  exact mul_nonneg (by linarith) (by nlinarith)
 have hmain:(1/140:ℝ) ≤ ((3:ℂ)/(27-((x:ℂ)+(y:ℂ)*I))).re:=by
  have h1:(27:ℂ)-((x:ℂ)+(y:ℂ)*I)=(((27-x:ℝ):ℂ)+((-y:ℝ):ℂ)*I):=by
   push_cast;ring
  rw [h1,div_eq_mul_one_div (3:ℂ),Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
   zero_mul,sub_zero,one_div (((27-x:ℝ):ℂ)+((-y:ℝ):ℂ)*I),
   Complex.inv_re,Complex.normSq_apply]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,mul_zero,
   Complex.ofReal_im,Complex.I_im,mul_one,sub_self,add_zero,Complex.add_im,zero_add,
   Complex.mul_im]
  have hden_pos:0< (27-x)*(27-x)+-y*-y:=by nlinarith
  rw [← mul_div_assoc,le_div_iff₀ hden_pos]
  nlinarith
 have h64:0 ≤ ((3:ℂ)/(((x:ℂ)+(y:ℂ)*I)+64)).re:=by
  have h1:((x:ℂ)+(y:ℂ)*I)+64=(((x+64:ℝ):ℂ)+(y:ℂ)*I):=by push_cast;ring
  rw [h1,div_eq_mul_one_div (3:ℂ),Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
   zero_mul,sub_zero,hinv_re]
  positivity
 have h037:0 ≤ ((3:ℂ)/((x:ℂ)+(y:ℂ)*I)-3/(((x:ℂ)+(y:ℂ)*I)+37)).re:=by
  have h1:(3:ℂ)/((x:ℂ)+(y:ℂ)*I)-3/(((x:ℂ)+(y:ℂ)*I)+37) =
    3*(1/((x:ℂ)+(y:ℂ)*I)-1/(((x+37:ℝ):ℂ)+(y:ℂ)*I)):=by
   push_cast;ring
  rw [h1,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  have hp:=hpair_pos x (x+37) (by linarith) (by linarith) (by nlinarith)
  linarith
 have hsum:0 ≤ (∑ u∈Finset.Icc (1:ℕ) 10,
   (1/(((x:ℂ)+(y:ℂ)*I)+((1+u:ℕ):ℂ)) -
    1/(((x:ℂ)+(y:ℂ)*I)+((36-u:ℕ):ℂ)))).re:=by
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun u hu=>?_
  have hu1:=(Finset.mem_Icc.mp hu).1
  have hu10:=(Finset.mem_Icc.mp hu).2
  have h1:((x:ℂ)+(y:ℂ)*I)+((1+u:ℕ):ℂ) =
    (((x+((1+u:ℕ):ℝ):ℝ):ℂ)+(y:ℂ)*I):=by push_cast;ring
  have h2:((x:ℂ)+(y:ℂ)*I)+((36-u:ℕ):ℂ) =
    (((x+((36-u:ℕ):ℝ):ℝ):ℂ)+(y:ℂ)*I):=by push_cast;ring
  rw [h1,h2]
  have hu1r:(1:ℝ) ≤ u:=by exact_mod_cast hu1
  have hu10r:(u:ℝ) ≤ 10:=by exact_mod_cast hu10
  have h1u:((1+u:ℕ):ℝ)=1+(u:ℝ):=by push_cast;rfl
  have h36u:((36-u:ℕ):ℝ)=36-(u:ℝ):=Nat.cast_sub (by omega)
  refine hpair_pos _ _ (by linarith) (by linarith) ?_
  rw [h1u,h36u]
  nlinarith
 have hsplit:z53 ((x:ℂ)+(y:ℂ)*I) =
   3/(27-((x:ℂ)+(y:ℂ)*I))+3/(((x:ℂ)+(y:ℂ)*I)+64) +
   (3/((x:ℂ)+(y:ℂ)*I)-3/(((x:ℂ)+(y:ℂ)*I)+37)) +
   ∑ u∈Finset.Icc (1:ℕ) 10,
    (1/(((x:ℂ)+(y:ℂ)*I)+((1+u:ℕ):ℂ)) -
     1/(((x:ℂ)+(y:ℂ)*I)+((36-u:ℕ):ℂ))):=by
  unfold z53;ring
 rw [hsplit]
 simp only [Complex.add_re]
 linarith
lemma z132 {x y:ℝ} (hx1:(234/10:ℝ) ≤ x) (hx2:x ≤ (236/10:ℝ))
  (hy:y ≤ -37) :
  (1:ℝ) ≤ -(dwPot ((x:ℂ)+(y:ℂ)*I)).im:=by
 set Y:ℝ:=-y
 have hY:37 ≤ Y:=by linarith
 have harg_add:∀ a:ℝ,0< x+a →
   (Complex.log (((x:ℂ)+(y:ℂ)*I)+(a:ℂ))).im=-Real.arctan (Y/(x+a)):=by
  intro a ha
  rw [Complex.log_im,z30 (by simp;linarith)]
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,mul_zero,
   Complex.ofReal_re,Complex.I_im,mul_one,zero_add,add_zero,Complex.add_re,Complex.mul_re,
   sub_self]
  rw [show y/(x+a)=-(Y/(x+a)) by simp [Y,neg_div],Real.arctan_neg]
 have harg27:(Complex.log (27-((x:ℂ)+(y:ℂ)*I))).im=Real.arctan (Y/(27-x)):=by
  rw [Complex.log_im,z30 (by simp;linarith)]
  simp only [Complex.sub_im,Complex.im_ofNat,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
   Complex.I_re,mul_zero,Complex.ofReal_re,Complex.I_im,mul_one,zero_add,zero_sub,
   Complex.sub_re,Complex.re_ofNat,Complex.add_re,Complex.mul_re,sub_self,add_zero,Y]
 have hdw_im:-(dwPot ((x:ℂ)+(y:ℂ)*I)).im =
   -Real.pi+3*Real.arctan (Y/(27-x)) +
   3*(Real.arctan (Y/x)-Real.arctan (Y/(x+37))) +
   3*Real.arctan (Y/(x+64)) +
   ∑ u∈Finset.Icc (1:ℕ) 10,
    (Real.arctan (Y/(x+((1+u:ℕ):ℝ)))-Real.arctan (Y/(x+((36-u:ℕ):ℝ)))):=by
  unfold dwPot
  simp only [Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.I_re,Complex.ofReal_im,
   Complex.I_im,Complex.ofReal_re,Complex.re_ofNat,Complex.im_ofNat,Complex.im_sum]
  have h0:(Complex.log ((x:ℂ)+(y:ℂ)*I)).im=-Real.arctan (Y/x):=by
   simpa using harg_add 0 (by linarith)
  have h64:(Complex.log (((x:ℂ)+(y:ℂ)*I)+64)).im=-Real.arctan (Y/(x+64)):=by
   simpa using harg_add 64 (by linarith)
  have h37:(Complex.log (((x:ℂ)+(y:ℂ)*I)+37)).im=-Real.arctan (Y/(x+37)):=by
   simpa using harg_add 37 (by linarith)
  have hsum:∑ u∈Finset.Icc (1:ℕ) 10,
    ((Complex.log (((x:ℂ)+(y:ℂ)*I)+((1+u:ℕ):ℂ))).im -
     (Complex.log (((x:ℂ)+(y:ℂ)*I)+((36-u:ℕ):ℂ))).im) =
    -∑ u∈Finset.Icc (1:ℕ) 10,
     (Real.arctan (Y/(x+((1+u:ℕ):ℝ)))-Real.arctan (Y/(x+((36-u:ℕ):ℝ)))):=by
   rw [← Finset.sum_neg_distrib]
   refine Finset.sum_congr rfl fun u _=>?_
   rw [show ((1+u:ℕ):ℂ)=(((1+u:ℕ):ℝ):ℂ) by push_cast;rfl,
    show ((36-u:ℕ):ℂ)=(((36-u:ℕ):ℝ):ℂ) by push_cast;rfl,
    harg_add _ (by positivity),harg_add _ (by positivity)]
   ring
  rw [h0,harg27,h64,h37,hsum];ring
 rw [hdw_im]
 have h1:(1:ℝ) ≤ -Real.pi+3*Real.arctan (Y/(27-x)):=by
  have hdiv:(10:ℝ) ≤ Y/(27-x):=by
   rw [le_div_iff₀ (by linarith)];linarith
  have hmono:=Real.arctan_mono hdiv
  have hinv:Real.arctan 10=Real.pi/2-Real.arctan (1/10):=by
   have h:=Real.arctan_inv_of_pos (by norm_num:(0:ℝ)< 10)
   linarith
  have hsmall:=(z29 (by norm_num:(0:ℝ) ≤ 1/10)).2
  have hpi3:=Real.pi_gt_three
  linarith
 have h2:0 ≤ Real.arctan (Y/x)-Real.arctan (Y/(x+37)):=by
  have hle:Y/(x+37) ≤ Y/x:=div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  linarith [Real.arctan_mono hle]
 have h3:0 ≤ Real.arctan (Y/(x+64)):=by
  rw [← Real.arctan_zero];exact Real.arctan_mono (by positivity)
 have h4:0 ≤ ∑ u∈Finset.Icc (1:ℕ) 10,
   (Real.arctan (Y/(x+((1+u:ℕ):ℝ)))-Real.arctan (Y/(x+((36-u:ℕ):ℝ)))):=by
  refine Finset.sum_nonneg fun u hu=>?_
  have hu1:=(Finset.mem_Icc.mp hu).1
  have hu10:=(Finset.mem_Icc.mp hu).2
  have hle:((1+u:ℕ):ℝ) ≤ ((36-u:ℕ):ℝ):=by exact_mod_cast (show 1+u ≤ 36-u by omega)
  have hdiv:Y/(x+((36-u:ℕ):ℝ)) ≤ Y/(x+((1+u:ℕ):ℝ)):=
   div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
  linarith [Real.arctan_mono hdiv]
 linarith
lemma z249 {z₀:ℂ} (hz₀_re1:(234/10:ℝ) ≤ z₀.re) (hz₀_re2:z₀.re ≤ (236/10:ℝ))
  (hz₀_im1:-4 ≤ z₀.im) (hz₀_im2:z₀.im ≤ -3) (hdw0:dwPot z₀=0)
  {y:ℝ} (hy:y ≤ 0) :
  (wPot ((z₀.re:ℂ)+(y:ℂ)*I)).re-(wPot z₀).re ≤
   if -37 ≤ y then -(y-z₀.im)^2/280 else -|y-z₀.im| / 10:=by
 let φ : ℝ→ ℝ:=fun t=>(wPot ((z₀.re:ℂ)+(t:ℂ)*I)).re
 let φ':ℝ→ ℝ:=fun t=>-(dwPot ((z₀.re:ℂ)+(t:ℂ)*I)).im
 let φ'':ℝ→ ℝ:=fun t=>-(z53 ((z₀.re:ℂ)+(t:ℂ)*I)).re
 have hφ_d:∀ t:ℝ,HasDerivAt φ (φ' t) t:=by
  intro t
  have hlin:HasDerivAt (fun u:ℝ=>(z₀.re:ℂ)+(u:ℂ)*I) I t:=by
   have h:=(Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const I
   rw [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] at h
   exact h.const_add (z₀.re:ℂ)
  have hcomp:=(z100 (z:=(z₀.re:ℂ)+(t:ℂ)*I) (by simp;linarith) (by simp;linarith)).comp t hlin
  have hre:=Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomp
  have hval:Complex.reCLM (dwPot ((z₀.re:ℂ)+(t:ℂ)*I)*I)=φ' t:=by
   simp [φ']
  rwa [hval] at hre
 have hφ'_d:∀ t:ℝ,HasDerivAt φ' (φ'' t) t:=by
  intro t
  have hlin:HasDerivAt (fun u:ℝ=>(z₀.re:ℂ)+(u:ℂ)*I) I t:=by
   have h:=(Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const I
   rw [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] at h
   exact h.const_add (z₀.re:ℂ)
  have hcomp:=(z95 (z:=(z₀.re:ℂ)+(t:ℂ)*I) (by simp;linarith) (by simp;linarith)).comp t hlin
  have him:=(Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hcomp).neg
  have hval:-(Complex.imCLM (z53 ((z₀.re:ℂ)+(t:ℂ)*I)*I))=φ'' t:=by
   simp [φ'']
  rwa [hval] at him
 have hφ'_0:φ' z₀.im=0:=by
  have hz:(z₀.re:ℂ)+(z₀.im:ℂ)*I=z₀:=Complex.re_add_im z₀
  simp [φ',hz,hdw0]
 have hquad:∀ t:ℝ,-37 ≤ t→ t ≤ 0 →
   φ t - φ z₀.im ≤ -(t-z₀.im)^2/280:=by
  intro t ht1 ht2
  let ψ : ℝ→ ℝ:=fun u=>φ u+(u-z₀.im)^2/280
  let ψ':ℝ→ ℝ:=fun u=>φ' u+(u-z₀.im)/140
  have hψ_d:∀ u:ℝ,HasDerivAt ψ (ψ' u) u:=by
   intro u
   have h1:HasDerivAt (fun v:ℝ=>(v-z₀.im)^2/280) ((u-z₀.im)/140) u:=by
    have h:=(((hasDerivAt_id u).sub_const z₀.im).pow 2).div_const 280
    dsimp only [id] at h
    rw [show ((2:ℕ):ℝ)*(u-z₀.im)^(2-1)*1/280=(u-z₀.im)/140 by
     push_cast;ring] at h
    exact h
   exact (hφ_d u).add h1
  have hψ'_d:∀ u:ℝ,HasDerivAt ψ' (φ'' u+1/140) u:=by
   intro u
   have h1:HasDerivAt (fun v:ℝ=>(v-z₀.im)/140) (1/140) u:=by
    simpa using ((hasDerivAt_id u).sub_const z₀.im).div_const 140
   exact (hφ'_d u).add h1
  have hψ'_anti:AntitoneOn ψ' (Set.Icc (-37) 0):=by
   refine antitoneOn_of_deriv_nonpos (convex_Icc (-37) 0) ?_ ?_ ?_
   ·
    exact (fun u _=>(hψ'_d u).continuousAt.continuousWithinAt)
   ·
    intro u _;exact (hψ'_d u).differentiableAt.differentiableWithinAt
   ·
    intro u hu
    have hmem:=interior_subset hu
    rw [(hψ'_d u).deriv]
    have h:=z247 hz₀_re1 hz₀_re2 hmem.1 hmem.2
    simp only [φ''];linarith
  have hψ'_z0:ψ' z₀.im=0:=by simp [ψ',hφ'_0]
  rcases le_or_gt t z₀.im with hle | hgt
  ·
   have hmono:MonotoneOn ψ (Set.Icc t z₀.im):=by
    refine monotoneOn_of_deriv_nonneg (convex_Icc t z₀.im) ?_ ?_ ?_
    ·
     exact fun u _=>(hψ_d u).continuousAt.continuousWithinAt
    ·
     intro u _;exact (hψ_d u).differentiableAt.differentiableWithinAt
    ·
     intro u hu
     have hmem:=interior_subset hu
     rw [(hψ_d u).deriv]
     have h1:=hψ'_anti ⟨by linarith [hmem.1],by linarith [hmem.2]⟩ ⟨by linarith,by linarith⟩ hmem.2
     linarith
   have:=hmono (Set.left_mem_Icc.mpr hle) (Set.right_mem_Icc.mpr hle) hle
   simp only [ψ,sub_self,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_div,add_zero] at this
   linarith
  ·
   have hanti:AntitoneOn ψ (Set.Icc z₀.im t):=by
    refine antitoneOn_of_deriv_nonpos (convex_Icc z₀.im t) ?_ ?_ ?_
    ·
     exact fun u _=>(hψ_d u).continuousAt.continuousWithinAt
    ·
     intro u _;exact (hψ_d u).differentiableAt.differentiableWithinAt
    ·
     intro u hu
     have hmem:=interior_subset hu
     rw [(hψ_d u).deriv]
     have h1:=hψ'_anti ⟨by linarith,by linarith⟩ ⟨by linarith [hmem.1],by linarith [hmem.2]⟩ hmem.1
     linarith
   have:=hanti (Set.left_mem_Icc.mpr hgt.le) (Set.right_mem_Icc.mpr hgt.le) hgt.le
   simp only [ψ,sub_self,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_div,add_zero] at this
   linarith
 have hz0_eq:φ z₀.im=(wPot z₀).re:=by simp [φ,Complex.re_add_im]
 change φ y-(wPot z₀).re ≤ _
 rw [← hz0_eq]
 split_ifs with hy37
 ·
  exact hquad y hy37 hy
 ·
  push Not at hy37
  have h37:=hquad (-37) le_rfl (by norm_num)
  have hlin:φ y ≤ φ (-37)+(y+37):=by
   let χ : ℝ→ ℝ:=fun u=>φ u-u
   have hχ_d:∀ u:ℝ,HasDerivAt χ (φ' u-1) u:=fun u=>(hφ_d u).sub (hasDerivAt_id u)
   have hmono:MonotoneOn χ (Set.Icc y (-37)):=by
    refine monotoneOn_of_deriv_nonneg (convex_Icc y (-37)) ?_ ?_ ?_
    ·
     exact fun u _=>(hχ_d u).continuousAt.continuousWithinAt
    ·
     intro u _;exact (hχ_d u).differentiableAt.differentiableWithinAt
    ·
     intro u hu
     have hmem:=interior_subset hu
     rw [(hχ_d u).deriv]
     have:=z132 hz₀_re1 hz₀_re2 hmem.2
     linarith
   have:=hmono (Set.left_mem_Icc.mpr hy37.le) (Set.right_mem_Icc.mpr hy37.le) hy37.le
   simp only [χ] at this;linarith
  have habs:|y-z₀.im|=z₀.im-y:=by
   rw [abs_of_neg (by linarith)];ring
  rw [habs]
  nlinarith [h37,hlin]
lemma z27 {x y:ℝ} (hx1:(234/10:ℝ) ≤ x) (hx2:x ≤ (236/10:ℝ)) :
  |(dwPot ((x:ℂ)+(y:ℂ)*I)).re| ≤ 120:=by
 have hratio_log:∀ (a b:ℝ),3 ≤ a→ a ≤ 90→ 3 ≤ b→ b ≤ 90 →
   |Real.log ‖((a:ℂ)+(y:ℂ)*I)‖ - Real.log ‖((b:ℂ)+(y:ℂ)*I)‖| ≤ 4:=by
  intro a b ha1 ha2 hb1 hb2
  have hna:0 < ‖(a:ℂ)+(y:ℂ)*I‖:=norm_pos_iff.mpr (by
   intro h;have:=congr_arg Complex.re h;simp at this;linarith)
  have hnb:0 < ‖(b:ℂ)+(y:ℂ)*I‖:=norm_pos_iff.mpr (by
   intro h;have:=congr_arg Complex.re h;simp at this;linarith)
  rw [← Real.log_div hna.ne' hnb.ne']
  have hle:‖(a:ℂ)+(y:ℂ)*I‖ / ‖(b:ℂ)+(y:ℂ)*I‖ ≤ 30:=by
   rw [div_le_iff₀ hnb]
   have hsq:‖(a:ℂ)+(y:ℂ)*I‖^2 ≤ (30*‖(b:ℂ)+(y:ℂ)*I‖)^2:=by
    rw [mul_pow,Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,mul_zero,
     Complex.ofReal_im,Complex.I_im,mul_one,sub_self,add_zero,Complex.add_im,zero_add,
     Complex.mul_im]
    nlinarith [sq_nonneg y]
   nlinarith [hna,hnb]
  have hge:(1/30:ℝ) ≤ ‖(a:ℂ)+(y:ℂ)*I‖ / ‖(b:ℂ)+(y:ℂ)*I‖:=by
   rw [div_le_div_iff₀ (by norm_num) hnb,one_mul]
   have hsq:‖(b:ℂ)+(y:ℂ)*I‖^2 ≤ (30*‖(a:ℂ)+(y:ℂ)*I‖)^2:=by
    rw [mul_pow,Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,mul_zero,
     Complex.ofReal_im,Complex.I_im,mul_one,sub_self,add_zero,Complex.add_im,zero_add,
     Complex.mul_im]
    nlinarith [sq_nonneg y]
   nlinarith [hna,hnb]
  have hlog30:Real.log 30 ≤ 4:=by
   rw [Real.log_le_iff_le_exp (by norm_num)]
   have he:(2.7:ℝ) ≤ Real.exp 1:=by linarith [Real.exp_one_gt_d9]
   have h4:(2.7:ℝ)^4 ≤ Real.exp 4:=by
    have:=pow_le_pow_left₀ (by norm_num) he 4
    rwa [← Real.exp_nat_mul,mul_one] at this
   linarith [show (30:ℝ) ≤ (2.7:ℝ)^4 by norm_num]
  rw [abs_le]
  constructor
  ·
   have h1:=Real.log_le_log (by norm_num) hge
   rw [one_div,Real.log_inv] at h1;linarith
  ·
   exact (Real.log_le_log (div_pos hna hnb) hle).trans hlog30
 have h27norm:‖(27:ℂ)-((x:ℂ)+(y:ℂ)*I)‖=‖(((27-x:ℝ):ℂ)+(y:ℂ)*I)‖:=by
  have hsq:‖(27:ℂ)-((x:ℂ)+(y:ℂ)*I)‖^2=‖(((27-x:ℝ):ℂ)+(y:ℂ)*I)‖^2:=by
   rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
   simp only [Complex.sub_re,Complex.re_ofNat,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.I_re,mul_zero,Complex.ofReal_im,Complex.I_im,mul_one,sub_self,add_zero,
    Complex.sub_im,Complex.im_ofNat,Complex.add_im,Complex.mul_im,zero_add,zero_sub]
   ring
  nlinarith [norm_nonneg ((27:ℂ)-((x:ℂ)+(y:ℂ)*I)),
   norm_nonneg (((27-x:ℝ):ℂ)+(y:ℂ)*I)]
 have hre_eq:(dwPot ((x:ℂ)+(y:ℂ)*I)).re =
   3*(Real.log ‖(x:ℂ)+(y:ℂ)*I‖ - Real.log ‖(((27-x:ℝ):ℂ)+(y:ℂ)*I)‖) +
   3*(Real.log ‖(((x+64:ℝ):ℂ)+(y:ℂ)*I)‖ - Real.log ‖(((x+37:ℝ):ℂ)+(y:ℂ)*I)‖) +
   ∑ u∈Finset.Icc (1:ℕ) 10,
    (Real.log ‖(((x+((1+u:ℕ):ℝ):ℝ):ℂ)+(y:ℂ)*I)‖ -
     Real.log ‖(((x+((36-u:ℕ):ℝ):ℝ):ℂ)+(y:ℂ)*I)‖):=by
  unfold dwPot
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.I_re,Complex.ofReal_re,
   Complex.I_im,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,Complex.log_re,
   Complex.re_sum,h27norm]
  have h64:((x:ℂ)+(y:ℂ)*I)+64=(((x+64:ℝ):ℂ)+(y:ℂ)*I):=by push_cast;ring
  have h37:((x:ℂ)+(y:ℂ)*I)+37=(((x+37:ℝ):ℂ)+(y:ℂ)*I):=by push_cast;ring
  rw [h64,h37]
  have hsum:∑ u∈Finset.Icc (1:ℕ) 10,
    (Real.log ‖((x:ℂ)+(y:ℂ)*I)+((1+u:ℕ):ℂ)‖ -
     Real.log ‖((x:ℂ)+(y:ℂ)*I)+((36-u:ℕ):ℂ)‖) =
    ∑ u∈Finset.Icc (1:ℕ) 10,
     (Real.log ‖(((x+((1+u:ℕ):ℝ):ℝ):ℂ)+(y:ℂ)*I)‖ -
      Real.log ‖(((x+((36-u:ℕ):ℝ):ℝ):ℂ)+(y:ℂ)*I)‖):=by
   refine Finset.sum_congr rfl fun u _=>by
    congr 2 <;> (push_cast;ring)
  rw [hsum];ring
 rw [hre_eq]
 have h1:=hratio_log x (27-x) (by linarith) (by linarith) (by linarith) (by linarith)
 have h2:=hratio_log (x+64) (x+37) (by linarith) (by linarith) (by linarith) (by linarith)
 have h3:|∑ u∈Finset.Icc (1:ℕ) 10,
   (Real.log ‖(((x+((1+u:ℕ):ℝ):ℝ):ℂ)+(y:ℂ)*I)‖ -
    Real.log ‖(((x+((36-u:ℕ):ℝ):ℝ):ℂ)+(y:ℂ)*I)‖)| ≤ 40:=by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
   ∑ u∈Finset.Icc (1:ℕ) 10,
     |Real.log ‖(((x+((1+u:ℕ):ℝ):ℝ):ℂ)+(y:ℂ)*I)‖ -
      Real.log ‖(((x+((36-u:ℕ):ℝ):ℝ):ℂ)+(y:ℂ)*I)‖|
    ≤ ∑ _u∈Finset.Icc (1:ℕ) 10,(4:ℝ):=by
     refine Finset.sum_le_sum fun u hu=>?_
     have hu1:=(Finset.mem_Icc.mp hu).1
     have hu10:=(Finset.mem_Icc.mp hu).2
     have hu1r:(1:ℝ) ≤ u:=by exact_mod_cast hu1
     have hu10r:(u:ℝ) ≤ 10:=by exact_mod_cast hu10
     have h1u:((1+u:ℕ):ℝ)=1+(u:ℝ):=by push_cast;rfl
     have h36u:((36-u:ℕ):ℝ)=36-(u:ℝ):=Nat.cast_sub (by omega)
     exact hratio_log _ _ (by linarith) (by linarith) (by linarith) (by linarith)
   _=40:=by norm_num
 have htri1:=abs_add_le
  (3*(Real.log ‖(x:ℂ)+(y:ℂ)*I‖ - Real.log ‖(((27-x:ℝ):ℂ)+(y:ℂ)*I)‖) +
   3*(Real.log ‖(((x+64:ℝ):ℂ)+(y:ℂ)*I)‖ - Real.log ‖(((x+37:ℝ):ℂ)+(y:ℂ)*I)‖))
  (∑ u∈Finset.Icc (1:ℕ) 10,
   (Real.log ‖(((x+((1+u:ℕ):ℝ):ℝ):ℂ)+(y:ℂ)*I)‖ -
    Real.log ‖(((x+((36-u:ℕ):ℝ):ℝ):ℂ)+(y:ℂ)*I)‖))
 have htri2:=abs_add_le
  (3*(Real.log ‖(x:ℂ)+(y:ℂ)*I‖ - Real.log ‖(((27-x:ℝ):ℂ)+(y:ℂ)*I)‖))
  (3*(Real.log ‖(((x+64:ℝ):ℂ)+(y:ℂ)*I)‖ - Real.log ‖(((x+37:ℝ):ℂ)+(y:ℂ)*I)‖))
 simp only [abs_mul,abs_of_pos (by norm_num:(0:ℝ)< 3)] at htri2
 linarith
lemma z250 {x x₀ y:ℝ}
  (hx1:(234/10:ℝ) ≤ x) (hx2:x ≤ (236/10:ℝ))
  (hx01:(234/10:ℝ) ≤ x₀) (hx02:x₀ ≤ (236/10:ℝ)) :
  |(wPot ((x:ℂ)+(y:ℂ)*I)).re-(wPot ((x₀:ℂ)+(y:ℂ)*I)).re| ≤
   120 * |x-x₀|:=by
 let g:ℝ→ ℝ:=fun t=>(wPot ((t:ℂ)+(y:ℂ)*I)).re
 have hg_d:∀ t∈Set.Icc (234/10:ℝ) (236/10),
   HasDerivAt g (dwPot ((t:ℂ)+(y:ℂ)*I)).re t:=by
  intro t ht
  have hlin:HasDerivAt (fun u:ℝ=>(u:ℂ)+(y:ℂ)*I) 1 t:=
   (Complex.ofRealCLM.hasDerivAt (x:=t)).add_const ((y:ℂ)*I)
  have hcomp:=(z100 (z:=(t:ℂ)+(y:ℂ)*I)
   (by simp;linarith [ht.1]) (by simp;linarith [ht.2])).comp t hlin
  have hre:=Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomp
  have hval:Complex.reCLM (dwPot ((t:ℂ)+(y:ℂ)*I)*1)=(dwPot ((t:ℂ)+(y:ℂ)*I)).re:=by
   simp
  rwa [hval] at hre
 have hmvt:=Convex.norm_image_sub_le_of_norm_deriv_le (f:=g) (s:=Set.Icc (234/10) (236/10))
  (C:=120) (fun t ht=>(hg_d t ht).differentiableAt)
  (fun t ht=>by
   rw [(hg_d t ht).deriv,Real.norm_eq_abs]
   exact z27 ht.1 ht.2)
  (convex_Icc _ _) ⟨hx01,hx02⟩ ⟨hx1,hx2⟩
 simpa [g,Real.norm_eq_abs] using hmvt
noncomputable def z180:ℂ:=
 (1/2:ℂ)*((2*Real.pi:ℝ):ℂ)^5 *
  (∏ u∈Finset.Icc (1:ℕ) 10,((Real.sqrt ((35-2*u:ℕ):ℝ):ℝ):ℂ)) /
  ((27:ℂ)^3)
noncomputable def z182 (ζ : ℂ):ℂ:=
 z180*(37+2*ζ) *
  Complex.exp (-(3/2:ℂ)*Complex.log ζ+(3/2:ℂ)*Complex.log (27 - ζ) +
   (3/2:ℂ)*Complex.log (ζ+64)-(3/2:ℂ)*Complex.log (ζ+37) -
   (1/2:ℂ)*∑ u∈Finset.Icc (1:ℕ) 10,
    (Complex.log (ζ+((1+u:ℕ):ℂ))+Complex.log (ζ+((36-u:ℕ):ℂ))))
noncomputable def z262 (n:ℕ) (ζ : ℂ):ℂ:=
 (∑ u∈Finset.Icc (1:ℕ) 10,z260 (((35-2*u)*n:ℕ):ℂ)) -
  6*z260 ((27*n:ℕ):ℂ) +
  3*z260 ((n:ℂ)*ζ) +
  3*z260 ((n:ℂ)*(27 - ζ)) +
  3*z260 ((n:ℂ)*(ζ+64)) -
  3*z260 ((n:ℂ)*(ζ+37)) +
  ∑ u∈Finset.Icc (1:ℕ) 10,
   (z260 ((n:ℂ)*(ζ+((1+u:ℕ):ℂ))) -
    z260 ((n:ℂ)*(ζ+((36-u:ℕ):ℂ))))
section Laplace
lemma z181:z180≠0:=by
 unfold z180
 refine div_ne_zero ?_ (pow_ne_zero 3 (by norm_num))
 refine mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 5 (Complex.ofReal_ne_zero.mpr (by positivity)))) ?_
 refine Finset.prod_ne_zero_iff.mpr fun u hu=>?_
 have hu2:=(Finset.mem_Icc.mp hu).2
 exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (by omega)))
lemma z183 {ζ : ℂ} (h0:0 < ζ.re):z182 ζ≠0:=by
 unfold z182
 refine mul_ne_zero (mul_ne_zero z181 ?_) (Complex.exp_ne_zero _)
 intro h0'
 have:=congr_arg Complex.re h0'
 simp only [Complex.add_re,Complex.re_ofNat,Complex.mul_re,Complex.im_ofNat,zero_mul,sub_zero,
  Complex.zero_re] at this
 linarith
lemma z50 {ζ : ℂ} (h0:0 < ζ.re) (h27:ζ.re< 27) :
  ContinuousAt z182 ζ:=by
 unfold z182
 have hc_log_add:∀ c:ℂ,0< (ζ+c).re →
   ContinuousAt (fun w:ℂ=>Complex.log (w+c)) ζ:=fun c hc =>
  ContinuousAt.comp (f:=fun w:ℂ=>w+c)
   (Complex.hasDerivAt_log (Or.inl hc)).continuousAt
   (continuousAt_id.add continuousAt_const)
 have hc_log_sub:ContinuousAt (fun w:ℂ=>Complex.log (27-w)) ζ:=by
  have h0:=(Complex.hasDerivAt_log (Or.inl (show (0:ℝ)< (27 - ζ).re by simp;linarith))).continuousAt
  exact h0.comp (continuousAt_const.sub continuousAt_id)
 have hc_sum:ContinuousAt (fun w:ℂ=>∑ u∈Finset.Icc (1:ℕ) 10,
   (Complex.log (w+((1+u:ℕ):ℂ))+Complex.log (w+((36-u:ℕ):ℂ)))) ζ:=
  tendsto_finsetSum _ fun u _ =>
   (hc_log_add _ (by simp;positivity)).add (hc_log_add _ (by simp;positivity))
 have hc_exp:ContinuousAt (fun w:ℂ =>
   Complex.exp (-(3/2:ℂ)*Complex.log w+(3/2:ℂ)*Complex.log (27-w) +
    (3/2:ℂ)*Complex.log (w+64)-(3/2:ℂ)*Complex.log (w+37) -
    (1/2:ℂ)*∑ u∈Finset.Icc (1:ℕ) 10,
     (Complex.log (w+((1+u:ℕ):ℂ))+Complex.log (w+((36-u:ℕ):ℂ))))) ζ:=by
  refine Complex.continuous_exp.continuousAt.comp ?_
  refine ((((continuousAt_const.mul (Complex.hasDerivAt_log (Or.inl h0)).continuousAt).add
   (continuousAt_const.mul hc_log_sub)).add
   (continuousAt_const.mul (hc_log_add 64 (by simp;linarith)))).sub
   (continuousAt_const.mul (hc_log_add 37 (by simp;linarith)))).sub
   (continuousAt_const.mul hc_sum)
 exact (continuousAt_const.mul (continuousAt_const.add (continuousAt_const.mul continuousAt_id))).mul hc_exp
lemma z142 {ζ : ℂ} (h1:(234/10:ℝ) ≤ ζ.re) (h2:ζ.re ≤ (236/10:ℝ)) :
  ‖z182 ζ‖ ≤ ‖z180‖*12:=by
 have hnorm_pos:∀ c:ℂ,0< c.re→ 0 < ‖c‖:=fun c hc =>
  norm_pos_iff.mpr (fun h=>by simp [h] at hc)
 have hnorm_ge1:∀ c:ℂ,1 ≤ c.re→ 1 ≤ ‖c‖:=fun c hc =>
  hc.trans (Complex.re_le_norm c)
 have hexp_norm:∀ (r:ℝ) (c:ℂ),‖Complex.exp ((r:ℂ)*Complex.log c)‖=Real.exp (r*Real.log ‖c‖):=by
  intro r c
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.log_re]
 have hlog_bd :
   (-(3/2:ℝ)*Real.log ‖ζ‖+(3/2:ℝ)*Real.log ‖27 - ζ‖ +
    (3/2:ℝ)*Real.log ‖ζ+64‖ - (3/2:ℝ)*Real.log ‖ζ+37‖ -
    (1/2:ℝ)*∑ u∈Finset.Icc (1:ℕ) 10,
     (Real.log ‖ζ+((1+u:ℕ):ℂ)‖+Real.log ‖ζ+((36-u:ℕ):ℂ)‖)) ≤
   Real.log 3-(1/2:ℝ)*(Real.log ‖ζ+((2:ℕ):ℂ)‖+Real.log ‖ζ+((35:ℕ):ℂ)‖):=by
  have h27_le:‖27 - ζ‖ ≤ ‖ζ‖:=by
   have hsq:‖27 - ζ‖^2 ≤ ‖ζ‖^2:=by
    rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.re_ofNat,Complex.sub_im,Complex.im_ofNat,zero_sub]
    nlinarith [sq_nonneg ζ.im]
   nlinarith [norm_nonneg (27 - ζ),norm_nonneg ζ]
  have hlog27:Real.log ‖27 - ζ‖ ≤ Real.log ‖ζ‖:=
   Real.log_le_log (hnorm_pos _ (by simp;linarith)) h27_le
  have h64_le:‖ζ+64‖ ≤ 2*‖ζ+37‖:=by
   have hsq:‖ζ+64‖^2 ≤ (2*‖ζ+37‖)^2:=by
    rw [mul_pow,Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
    simp only [Complex.add_re,Complex.re_ofNat,Complex.add_im,Complex.im_ofNat,add_zero]
    nlinarith [sq_nonneg ζ.im]
   nlinarith [norm_nonneg (ζ+64),norm_nonneg (ζ+37)]
  have hlog64:(3/2:ℝ)*(Real.log ‖ζ+64‖ - Real.log ‖ζ+37‖) ≤ Real.log 3:=by
   have h1':Real.log ‖ζ+64‖ ≤ Real.log (2*‖ζ+37‖):=
    Real.log_le_log (hnorm_pos _ (by simp;linarith)) h64_le
   rw [Real.log_mul (by norm_num) (hnorm_pos _ (by simp;linarith)).ne'] at h1'
   have h32:(3/2:ℝ)*Real.log 2 ≤ Real.log 3:=by
    have h23:Real.log ((2:ℝ)^3) ≤ Real.log ((3:ℝ)^2):=
     Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow,Real.log_pow] at h23
    push_cast at h23;linarith
   linarith
  have hsum_ge:Real.log ‖ζ+((2:ℕ):ℂ)‖+Real.log ‖ζ+((35:ℕ):ℂ)‖ ≤
    ∑ u∈Finset.Icc (1:ℕ) 10,
     (Real.log ‖ζ+((1+u:ℕ):ℂ)‖+Real.log ‖ζ+((36-u:ℕ):ℂ)‖):=by
   have hmem:(1:ℕ)∈Finset.Icc (1:ℕ) 10:=by decide
   have hle:=Finset.single_le_sum (f:=fun u:ℕ =>
     Real.log ‖ζ+((1+u:ℕ):ℂ)‖+Real.log ‖ζ+((36-u:ℕ):ℂ)‖)
    (fun u _=>add_nonneg
     (Real.log_nonneg (hnorm_ge1 _ (by simp;linarith [Nat.cast_nonneg (α:=ℝ) u])))
     (Real.log_nonneg (hnorm_ge1 _ (by simp;linarith [Nat.cast_nonneg (α:=ℝ) (36-u)]))))
    hmem
   exact hle
  have hp1:-(3/2:ℝ)*Real.log ‖ζ‖+(3/2:ℝ)*Real.log ‖27 - ζ‖ ≤ 0:=by linarith
  have hp2:(3/2:ℝ)*Real.log ‖ζ+64‖ - (3/2:ℝ)*Real.log ‖ζ+37‖ ≤ Real.log 3:=by
   rw [← mul_sub];exact hlog64
  have hp3:-(1/2:ℝ)*∑ u∈Finset.Icc (1:ℕ) 10,
     (Real.log ‖ζ+((1+u:ℕ):ℂ)‖+Real.log ‖ζ+((36-u:ℕ):ℂ)‖) ≤
    -(1/2:ℝ)*(Real.log ‖ζ+((2:ℕ):ℂ)‖+Real.log ‖ζ+((35:ℕ):ℂ)‖):=
   mul_le_mul_of_nonpos_left hsum_ge (by norm_num)
  linarith
 have hlin_bd:‖37+2*ζ‖ ≤ 4*Real.sqrt (‖ζ+((2:ℕ):ℂ)‖*‖ζ+((35:ℕ):ℂ)‖):=by
  have hsq1:‖37+2*ζ‖^2 ≤ 16*‖ζ+((2:ℕ):ℂ)‖^2:=by
   rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
   simp only [Complex.add_re,Complex.re_ofNat,Complex.mul_re,Complex.im_ofNat,zero_mul,sub_zero,
    Complex.add_im,Complex.mul_im,add_zero,zero_add,Nat.cast_ofNat]
   nlinarith [sq_nonneg ζ.im]
  have hsq2:‖37+2*ζ‖^2 ≤ 16*‖ζ+((35:ℕ):ℂ)‖^2:=by
   rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
   simp only [Complex.add_re,Complex.re_ofNat,Complex.mul_re,Complex.im_ofNat,zero_mul,sub_zero,
    Complex.add_im,Complex.mul_im,add_zero,zero_add,Nat.cast_ofNat]
   nlinarith [sq_nonneg ζ.im]
  have h1':‖37+2*ζ‖ ≤ 4*‖ζ+((2:ℕ):ℂ)‖:=by nlinarith [norm_nonneg (37+2*ζ),norm_nonneg (ζ+((2:ℕ):ℂ))]
  have h2':‖37+2*ζ‖ ≤ 4*‖ζ+((35:ℕ):ℂ)‖:=by nlinarith [norm_nonneg (37+2*ζ),norm_nonneg (ζ+((35:ℕ):ℂ))]
  have hmul:‖37+2*ζ‖^2 ≤ (4*Real.sqrt (‖ζ+((2:ℕ):ℂ)‖*‖ζ+((35:ℕ):ℂ)‖))^2:=by
   rw [mul_pow,Real.sq_sqrt (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
   nlinarith [norm_nonneg (37+2*ζ),norm_nonneg (ζ+((2:ℕ):ℂ)),norm_nonneg (ζ+((35:ℕ):ℂ))]
  nlinarith [norm_nonneg (37+2*ζ),Real.sqrt_nonneg (‖ζ+((2:ℕ):ℂ)‖*‖ζ+((35:ℕ):ℂ)‖)]
 unfold z182
 rw [norm_mul,norm_mul,Complex.norm_exp]
 have hre_exp:(-(3/2:ℂ)*Complex.log ζ+(3/2:ℂ)*Complex.log (27 - ζ) +
    (3/2:ℂ)*Complex.log (ζ+64)-(3/2:ℂ)*Complex.log (ζ+37) -
    (1/2:ℂ)*∑ u∈Finset.Icc (1:ℕ) 10,
     (Complex.log (ζ+((1+u:ℕ):ℂ))+Complex.log (ζ+((36-u:ℕ):ℂ)))).re =
   -(3/2:ℝ)*Real.log ‖ζ‖+(3/2:ℝ)*Real.log ‖27 - ζ‖ +
    (3/2:ℝ)*Real.log ‖ζ+64‖ - (3/2:ℝ)*Real.log ‖ζ+37‖ -
    (1/2:ℝ)*∑ u∈Finset.Icc (1:ℕ) 10,
     (Real.log ‖ζ+((1+u:ℕ):ℂ)‖+Real.log ‖ζ+((36-u:ℕ):ℂ)‖):=by
  simp only [Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.neg_re,Complex.div_ofNat_re,
   Complex.re_ofNat,Complex.one_re,Complex.neg_im,Complex.div_ofNat_im,Complex.im_ofNat,
   Complex.one_im,zero_div,neg_zero,zero_mul,sub_zero,Complex.log_re,Complex.re_sum]
 rw [hre_exp]
 have hexp_le:Real.exp (-(3/2:ℝ)*Real.log ‖ζ‖+(3/2:ℝ)*Real.log ‖27 - ζ‖ +
    (3/2:ℝ)*Real.log ‖ζ+64‖ - (3/2:ℝ)*Real.log ‖ζ+37‖ -
    (1/2:ℝ)*∑ u∈Finset.Icc (1:ℕ) 10,
     (Real.log ‖ζ+((1+u:ℕ):ℂ)‖+Real.log ‖ζ+((36-u:ℕ):ℂ)‖)) ≤
   3/Real.sqrt (‖ζ+((2:ℕ):ℂ)‖*‖ζ+((35:ℕ):ℂ)‖):=by
  have h2p:0 < ‖ζ+((2:ℕ):ℂ)‖:=hnorm_pos _ (by simp;linarith)
  have h35p:0 < ‖ζ+((35:ℕ):ℂ)‖:=hnorm_pos _ (by simp;linarith)
  have hsq_eq:Real.exp (Real.log 3-(1/2:ℝ)*(Real.log ‖ζ+((2:ℕ):ℂ)‖+Real.log ‖ζ+((35:ℕ):ℂ)‖)) =
    3/Real.sqrt (‖ζ+((2:ℕ):ℂ)‖*‖ζ+((35:ℕ):ℂ)‖):=by
   rw [Real.exp_sub,Real.exp_log (by norm_num),← Real.log_mul h2p.ne' h35p.ne',
    mul_comm (1/2:ℝ),← Real.rpow_def_of_pos (mul_pos h2p h35p),← Real.sqrt_eq_rpow]
  rw [← hsq_eq]
  exact Real.exp_le_exp.mpr hlog_bd
 have hsq_pos:0< Real.sqrt (‖ζ+((2:ℕ):ℂ)‖*‖ζ+((35:ℕ):ℂ)‖):=
  Real.sqrt_pos.mpr (mul_pos (hnorm_pos _ (by simp;linarith)) (hnorm_pos _ (by simp;linarith)))
 have hprod_le:‖37+2*ζ‖*Real.exp (-(3/2:ℝ)*Real.log ‖ζ‖+(3/2:ℝ)*Real.log ‖27 - ζ‖ +
    (3/2:ℝ)*Real.log ‖ζ+64‖ - (3/2:ℝ)*Real.log ‖ζ+37‖ -
    (1/2:ℝ)*∑ u∈Finset.Icc (1:ℕ) 10,
     (Real.log ‖ζ+((1+u:ℕ):ℂ)‖+Real.log ‖ζ+((36-u:ℕ):ℂ)‖)) ≤ 12:=by
  calc
   ‖37+2*ζ‖*Real.exp _
    ≤ (4*Real.sqrt (‖ζ+((2:ℕ):ℂ)‖*‖ζ+((35:ℕ):ℂ)‖)) *
      (3/Real.sqrt (‖ζ+((2:ℕ):ℂ)‖*‖ζ+((35:ℕ):ℂ)‖)):=
     mul_le_mul hlin_bd hexp_le (Real.exp_pos _).le (by positivity)
   _=12:=by field_simp [hsq_pos.ne'];ring
 rw [mul_assoc]
 exact mul_le_mul_of_nonneg_left hprod_le (norm_nonneg _)
lemma z145
  (hrem_le:∀ {s:ℂ},0< s.re→ 2 ≤ ‖s‖→ ‖z260 s‖ ≤ 6 / ‖s‖)
  {n:ℕ} (hn:1 ≤ n) {ζ : ℂ} (h1:(234/10:ℝ) ≤ ζ.re) (h2:ζ.re ≤ (236/10:ℝ)) :
  ‖z262 n ζ‖ ≤ 200/(n:ℝ):=by
 have hn_pos:(0:ℝ)< n:=Nat.cast_pos.mpr hn
 have hbd_c:∀ c:ℂ,3 ≤ c.re→ ‖z260 ((n:ℂ)*c)‖ ≤ 2/(n:ℝ):=by
  intro c hc
  have hre:0< ((n:ℂ)*c).re:=by
   simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
   nlinarith
  have hnorm3:3*(n:ℝ) ≤ ‖(n:ℂ)*c‖:=by
   have:=Complex.re_le_norm ((n:ℂ)*c)
   simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] at this
   nlinarith
  have hnorm2:2 ≤ ‖(n:ℂ)*c‖:=by
   have:(1:ℝ) ≤ n:=by exact_mod_cast hn
   linarith
  calc
   ‖z260 ((n:ℂ)*c)‖ ≤ 6 / ‖(n:ℂ)*c‖:=hrem_le hre hnorm2
   _ ≤ 6/(3*(n:ℝ)):=div_le_div_of_nonneg_left (by norm_num) (by positivity) hnorm3
   _=2/(n:ℝ):=by ring
 have hbd_nat:∀ a:ℕ,3 ≤ a→ ‖z260 ((a*n:ℕ):ℂ)‖ ≤ 2/(n:ℝ):=by
  intro a ha
  have hcast:((a*n:ℕ):ℂ)=(n:ℂ)*(a:ℂ):=by push_cast;ring
  rw [hcast]
  exact hbd_c (a:ℂ) (by simp;exact_mod_cast ha)
 unfold z262
 have h1':‖∑ u∈Finset.Icc (1:ℕ) 10,z260 (((35-2*u)*n:ℕ):ℂ)‖ ≤ 20/(n:ℝ):=by
  refine (norm_sum_le _ _).trans ?_
  calc
   ∑ u∈Finset.Icc (1:ℕ) 10,‖z260 (((35-2*u)*n:ℕ):ℂ)‖
    ≤ ∑ _u∈Finset.Icc (1:ℕ) 10,(2/(n:ℝ)):=
     Finset.sum_le_sum fun u hu=>hbd_nat (35-2*u) (by have:=(Finset.mem_Icc.mp hu).2;omega)
   _=20/(n:ℝ):=by simp;ring
 have h2':‖(6:ℂ)*z260 ((27*n:ℕ):ℂ)‖ ≤ 12/(n:ℝ):=by
  rw [norm_mul,Complex.norm_ofNat]
  calc
   (6:ℝ)*‖z260 ((27*n:ℕ):ℂ)‖ ≤ 6*(2/(n:ℝ)):=
     mul_le_mul_of_nonneg_left (hbd_nat 27 (by omega)) (by norm_num)
   _=12/(n:ℝ):=by ring
 have h3':‖(3:ℂ)*z260 ((n:ℂ)*ζ)‖ ≤ 6/(n:ℝ):=by
  rw [norm_mul,Complex.norm_ofNat]
  calc
   (3:ℝ)*‖z260 ((n:ℂ)*ζ)‖ ≤ 3*(2/(n:ℝ)):=
     mul_le_mul_of_nonneg_left (hbd_c ζ (by linarith)) (by norm_num)
   _=6/(n:ℝ):=by ring
 have h4':‖(3:ℂ)*z260 ((n:ℂ)*(27 - ζ))‖ ≤ 6/(n:ℝ):=by
  rw [norm_mul,Complex.norm_ofNat]
  calc
   (3:ℝ)*‖z260 ((n:ℂ)*(27 - ζ))‖ ≤ 3*(2/(n:ℝ)):=
     mul_le_mul_of_nonneg_left (hbd_c (27 - ζ) (by simp;linarith)) (by norm_num)
   _=6/(n:ℝ):=by ring
 have h5':‖(3:ℂ)*z260 ((n:ℂ)*(ζ+64))‖ ≤ 6/(n:ℝ):=by
  rw [norm_mul,Complex.norm_ofNat]
  calc
   (3:ℝ)*‖z260 ((n:ℂ)*(ζ+64))‖ ≤ 3*(2/(n:ℝ)):=
     mul_le_mul_of_nonneg_left (hbd_c (ζ+64) (by simp;linarith)) (by norm_num)
   _=6/(n:ℝ):=by ring
 have h6':‖(3:ℂ)*z260 ((n:ℂ)*(ζ+37))‖ ≤ 6/(n:ℝ):=by
  rw [norm_mul,Complex.norm_ofNat]
  calc
   (3:ℝ)*‖z260 ((n:ℂ)*(ζ+37))‖ ≤ 3*(2/(n:ℝ)):=
     mul_le_mul_of_nonneg_left (hbd_c (ζ+37) (by simp;linarith)) (by norm_num)
   _=6/(n:ℝ):=by ring
 have h7':‖∑ u∈Finset.Icc (1:ℕ) 10,
   (z260 ((n:ℂ)*(ζ+((1+u:ℕ):ℂ))) -
    z260 ((n:ℂ)*(ζ+((36-u:ℕ):ℂ))))‖ ≤ 40/(n:ℝ):=by
  refine (norm_sum_le _ _).trans ?_
  calc
   ∑ u∈Finset.Icc (1:ℕ) 10,
     ‖z260 ((n:ℂ)*(ζ+((1+u:ℕ):ℂ))) -
      z260 ((n:ℂ)*(ζ+((36-u:ℕ):ℂ)))‖
    ≤ ∑ _u∈Finset.Icc (1:ℕ) 10,(4/(n:ℝ)):=by
     refine Finset.sum_le_sum fun u _=>(norm_sub_le _ _).trans ?_
     have ha:=hbd_c (ζ+((1+u:ℕ):ℂ)) (by simp;linarith [Nat.cast_nonneg (α:=ℝ) u])
     have hb:=hbd_c (ζ+((36-u:ℕ):ℂ)) (by simp;linarith [Nat.cast_nonneg (α:=ℝ) (36-u)])
     rw [show (4:ℝ)/(n:ℝ)=2/(n:ℝ)+2/(n:ℝ) by ring];linarith
   _=40/(n:ℝ):=by simp;ring
 have ht1:=norm_add_le
  ((∑ u∈Finset.Icc (1:ℕ) 10,z260 (((35-2*u)*n:ℕ):ℂ)) -
   6*z260 ((27*n:ℕ):ℂ) +
   3*z260 ((n:ℂ)*ζ) +
   3*z260 ((n:ℂ)*(27 - ζ)) +
   3*z260 ((n:ℂ)*(ζ+64)) -
   3*z260 ((n:ℂ)*(ζ+37)))
  (∑ u∈Finset.Icc (1:ℕ) 10,
   (z260 ((n:ℂ)*(ζ+((1+u:ℕ):ℂ))) -
    z260 ((n:ℂ)*(ζ+((36-u:ℕ):ℂ)))))
 have ht2:=norm_sub_le
  ((∑ u∈Finset.Icc (1:ℕ) 10,z260 (((35-2*u)*n:ℕ):ℂ)) -
   6*z260 ((27*n:ℕ):ℂ) +
   3*z260 ((n:ℂ)*ζ) +
   3*z260 ((n:ℂ)*(27 - ζ)) +
   3*z260 ((n:ℂ)*(ζ+64)))
  (3*z260 ((n:ℂ)*(ζ+37)))
 have ht3:=norm_add_le
  ((∑ u∈Finset.Icc (1:ℕ) 10,z260 (((35-2*u)*n:ℕ):ℂ)) -
   6*z260 ((27*n:ℕ):ℂ) +
   3*z260 ((n:ℂ)*ζ) +
   3*z260 ((n:ℂ)*(27 - ζ)))
  (3*z260 ((n:ℂ)*(ζ+64)))
 have ht4:=norm_add_le
  ((∑ u∈Finset.Icc (1:ℕ) 10,z260 (((35-2*u)*n:ℕ):ℂ)) -
   6*z260 ((27*n:ℕ):ℂ) +
   3*z260 ((n:ℂ)*ζ))
  (3*z260 ((n:ℂ)*(27 - ζ)))
 have ht5:=norm_add_le
  ((∑ u∈Finset.Icc (1:ℕ) 10,z260 (((35-2*u)*n:ℕ):ℂ)) -
   6*z260 ((27*n:ℕ):ℂ))
  (3*z260 ((n:ℂ)*ζ))
 have ht6:=norm_sub_le
  (∑ u∈Finset.Icc (1:ℕ) 10,z260 (((35-2*u)*n:ℕ):ℂ))
  (6*z260 ((27*n:ℕ):ℂ))
 have hsum:(20:ℝ)/n+12/n+6/n+6/n+6/n+6/n+40/n ≤ 200/n:=by
  have:(20:ℝ)/n+12/n+6/n+6/n+6/n+6/n+40/n=96/n:=by ring
  rw [this];exact div_le_div_of_nonneg_right (by norm_num) hn_pos.le
 linarith
private lemma z75 {x:ℝ} (hx:0< x) :
  Complex.exp ((1/2:ℂ)*Complex.log (x:ℂ))=((Real.sqrt x:ℝ):ℂ):=by
 rw [← Complex.ofReal_log hx.le,show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,
  ← Complex.ofReal_mul,← Complex.ofReal_exp]
 congr 1
 rw [mul_comm,← Real.rpow_def_of_pos hx,← Real.sqrt_eq_rpow]
lemma z90
  (hlog_mul:∀ {a b:ℂ},0< a.re→ 0< b.re→ Complex.log (a*b)=Complex.log a+Complex.log b)
  (hstirling:∀ {s:ℂ},0< s.re→ 2 ≤ ‖s‖ →
   Complex.Gamma s=((Real.sqrt (2*Real.pi):ℝ):ℂ) *
    Complex.exp ((s-1/2)*Complex.log s-s+z260 s))
  (hfac_stirling:∀ {m:ℕ},2 ≤ m →
   (m.factorial:ℂ)=((Real.sqrt (2*Real.pi):ℝ):ℂ) *
    Complex.exp (((m:ℂ)+1/2)*Complex.log (m:ℂ)-(m:ℂ)+z260 (m:ℂ)))
  {n:ℕ} (hn:1 ≤ n) {ζ : ℂ} (h1:(234/10:ℝ) ≤ ζ.re) (h2:ζ.re ≤ (236/10:ℝ)) :
  Z4.z88 n ((n:ℂ)*ζ) =
   ((n:ℂ)^7)⁻¹*z182 ζ *
    (1+Complex.exp (-2*I*(Real.pi:ℂ)*(n:ℂ)*ζ)) *
    Complex.exp ((n:ℂ)*wPot ζ+z262 n ζ):=by
 have hn_pos:(0:ℝ)< n:=Nat.cast_pos.mpr hn
 have hn_re:0< (n:ℂ).re:=by simpa using hn_pos
 have hn_ne:(n:ℂ)≠0:=Nat.cast_ne_zero.mpr (by omega)
 have hsq2pi_ne:((Real.sqrt (2*Real.pi):ℝ):ℂ)≠0:=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
 have hsq2pi_sq:(((Real.sqrt (2*Real.pi):ℝ):ℂ))^2=((2*Real.pi:ℝ):ℂ):=by
  rw [← Complex.ofReal_pow,Real.sq_sqrt (by positivity)]
 have hG:∀ c:ℂ,3 ≤ c.re →
   Complex.Gamma ((n:ℂ)*c)=((Real.sqrt (2*Real.pi):ℝ):ℂ) *
    Complex.exp (((n:ℂ)*c-1/2)*Complex.log (n:ℂ) +
     ((n:ℂ)*c-1/2)*Complex.log c-(n:ℂ)*c+z260 ((n:ℂ)*c)):=by
  intro c hc
  have hre_c:0< c.re:=by linarith
  have hre_nc:0< ((n:ℂ)*c).re:=by
   simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
   nlinarith
  have hnorm_nc:2 ≤ ‖(n:ℂ)*c‖:=by
   have:=Complex.re_le_norm ((n:ℂ)*c)
   simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] at this
   have hn1:(1:ℝ) ≤ n:=by exact_mod_cast hn
   nlinarith
  rw [hstirling hre_nc hnorm_nc,hlog_mul hn_re hre_c]
  congr 2;ring
 have hG1:∀ c:ℂ,3 ≤ c.re →
   Complex.Gamma ((n:ℂ)*c+1)=((Real.sqrt (2*Real.pi):ℝ):ℂ) *
    Complex.exp (((n:ℂ)*c+1/2)*Complex.log (n:ℂ) +
     ((n:ℂ)*c+1/2)*Complex.log c-(n:ℂ)*c+z260 ((n:ℂ)*c)):=by
  intro c hc
  have hc_ne:c≠0:=by intro h;simp [h] at hc;linarith
  have hnc_ne:(n:ℂ)*c≠0:=mul_ne_zero hn_ne hc_ne
  rw [Complex.Gamma_add_one _ hnc_ne,hG c hc]
  set E:=((n:ℂ)*c-1/2)*Complex.log (n:ℂ) +
   ((n:ℂ)*c-1/2)*Complex.log c-(n:ℂ)*c+z260 ((n:ℂ)*c)
  calc
   (n:ℂ)*c*(((Real.sqrt (2*Real.pi):ℝ):ℂ)*Complex.exp E)
    = ((Real.sqrt (2*Real.pi):ℝ):ℂ) *
      (Complex.exp (Complex.log (n:ℂ))*Complex.exp (Complex.log c)*Complex.exp E):=by
     rw [Complex.exp_log hn_ne,Complex.exp_log hc_ne];ring
   _=((Real.sqrt (2*Real.pi):ℝ):ℂ) *
      Complex.exp (((n:ℂ)*c+1/2)*Complex.log (n:ℂ) +
       ((n:ℂ)*c+1/2)*Complex.log c-(n:ℂ)*c+z260 ((n:ℂ)*c)):=by
     rw [← Complex.exp_add,← Complex.exp_add]
     congr 2;dsimp only [E];ring
 have hFac:∀ a:ℕ,3 ≤ a →
   (((a*n).factorial:ℕ):ℂ)=((Real.sqrt (2*Real.pi):ℝ):ℂ) *
    ((Real.sqrt (a:ℝ):ℝ):ℂ) *
    Complex.exp ((((a:ℂ)*(n:ℂ)+1/2)*Complex.log (n:ℂ) +
     (a:ℂ)*(n:ℂ)*Complex.log (a:ℂ)-(a:ℂ)*(n:ℂ) +
     z260 ((a*n:ℕ):ℂ))):=by
  intro a ha
  have ha_pos:(0:ℝ)< a:=Nat.cast_pos.mpr (by omega)
  have ha_re:0< (a:ℂ).re:=by simpa using ha_pos
  rw [hfac_stirling (by nlinarith:2 ≤ a*n)]
  have hcast:((a*n:ℕ):ℂ)=(a:ℂ)*(n:ℂ):=by push_cast;rfl
  rw [hcast,hlog_mul ha_re hn_re,← hcast,← z75 ha_pos]
  rw [mul_assoc,← Complex.exp_add]
  congr 2;push_cast;ring
 have hcos:((-1:ℂ)^n)*Complex.cos ((Real.pi:ℂ)*((n:ℂ)*ζ)) =
   (1/2:ℂ)*(1+Complex.exp (-2*I*(Real.pi:ℂ)*(n:ℂ)*ζ)) *
    Complex.exp ((n:ℂ)*(I*(Real.pi:ℂ)*(ζ+1))):=by
  have hm1:(-1:ℂ)^n=Complex.exp ((n:ℂ)*(I*(Real.pi:ℂ))):=by
   rw [show (n:ℂ)*(I*(Real.pi:ℂ))=(n:ℂ)*((Real.pi:ℂ)*I) by ring,
    Complex.exp_nat_mul,Complex.exp_pi_mul_I]
  rw [hm1,Complex.cos,neg_mul]
  have hsplit:Complex.exp ((Real.pi:ℂ)*((n:ℂ)*ζ)*I) +
     Complex.exp (-((Real.pi:ℂ)*((n:ℂ)*ζ)*I)) =
    Complex.exp ((Real.pi:ℂ)*((n:ℂ)*ζ)*I) *
     (1+Complex.exp (-2*I*(Real.pi:ℂ)*(n:ℂ)*ζ)):=by
   rw [mul_add,mul_one,← Complex.exp_add]
   congr 2;ring
  rw [hsplit]
  calc
   Complex.exp ((n:ℂ)*(I*(Real.pi:ℂ))) *
     (Complex.exp ((Real.pi:ℂ)*((n:ℂ)*ζ)*I) *
      (1+Complex.exp (-2*I*(Real.pi:ℂ)*(n:ℂ)*ζ))/2)
    = (1/2:ℂ)*(1+Complex.exp (-2*I*(Real.pi:ℂ)*(n:ℂ)*ζ)) *
      (Complex.exp ((n:ℂ)*(I*(Real.pi:ℂ))) *
       Complex.exp ((Real.pi:ℂ)*((n:ℂ)*ζ)*I)):=by ring
   _=_:=by rw [← Complex.exp_add];congr 2;ring
 have hscale:((Z4.z286 n:ℚ):ℂ) =
   ((2*Real.pi:ℝ):ℂ)^2 *
    (∏ u∈Finset.Icc (1:ℕ) 10,((Real.sqrt ((35-2*u:ℕ):ℝ):ℝ):ℂ)) /
    ((27:ℂ)^3) *
    Complex.exp ((78*(n:ℂ)+2)*Complex.log (n:ℂ) +
     (n:ℂ)*(∑ u∈Finset.Icc (1:ℕ) 10,
       (((35-2*u:ℕ):ℂ)*Complex.log ((35-2*u:ℕ):ℂ)) -
      162*Complex.log 27) -
     78*(n:ℂ) +
     (∑ u∈Finset.Icc (1:ℕ) 10,z260 (((35-2*u)*n:ℕ):ℂ)) -
     6*z260 ((27*n:ℕ):ℂ)):=by
  simp only [Z4.z286,Rat.cast_div,Rat.cast_prod,Rat.cast_pow,Rat.cast_natCast]
  have hnum_fac:(∏ u∈Finset.Icc (1:ℕ) 10,((((35-2*u)*n).factorial:ℕ):ℂ)) =
    (((Real.sqrt (2*Real.pi):ℝ):ℂ))^10 *
     (∏ u∈Finset.Icc (1:ℕ) 10,((Real.sqrt ((35-2*u:ℕ):ℝ):ℝ):ℂ)) *
     Complex.exp (∑ u∈Finset.Icc (1:ℕ) 10,
      ((((35-2*u:ℕ):ℂ)*(n:ℂ)+1/2)*Complex.log (n:ℂ) +
       ((35-2*u:ℕ):ℂ)*(n:ℂ)*Complex.log ((35-2*u:ℕ):ℂ) -
       ((35-2*u:ℕ):ℂ)*(n:ℂ) +
       z260 (((35-2*u)*n:ℕ):ℂ))):=by
   have hcongr:(∏ u∈Finset.Icc (1:ℕ) 10,((((35-2*u)*n).factorial:ℕ):ℂ)) =
     ∏ u∈Finset.Icc (1:ℕ) 10,
      (((Real.sqrt (2*Real.pi):ℝ):ℂ)*((Real.sqrt ((35-2*u:ℕ):ℝ):ℝ):ℂ) *
       Complex.exp ((((35-2*u:ℕ):ℂ)*(n:ℂ)+1/2)*Complex.log (n:ℂ) +
        ((35-2*u:ℕ):ℂ)*(n:ℂ)*Complex.log ((35-2*u:ℕ):ℂ) -
        ((35-2*u:ℕ):ℂ)*(n:ℂ) +
        z260 (((35-2*u)*n:ℕ):ℂ))):=
    Finset.prod_congr rfl fun u hu=>hFac (35-2*u) (by have:=(Finset.mem_Icc.mp hu).2;omega)
   rw [hcongr,Finset.prod_mul_distrib,Finset.prod_mul_distrib,Finset.prod_const,
    ← Complex.exp_sum]
   simp
  have hden_fac:((((27*n).factorial:ℕ):ℂ))^6 =
    (((Real.sqrt (2*Real.pi):ℝ):ℂ))^6*(27:ℂ)^3 *
     Complex.exp (6*((27*(n:ℂ)+1/2)*Complex.log (n:ℂ) +
      27*(n:ℂ)*Complex.log 27-27*(n:ℂ) +
      z260 ((27*n:ℕ):ℂ))):=by
   rw [hFac 27 (by omega),mul_pow,mul_pow,← Complex.exp_nat_mul]
   have hsq27:(((Real.sqrt (27:ℝ):ℝ):ℂ))^6=(27:ℂ)^3:=by
    rw [show (6:ℕ)=2*3 by norm_num,pow_mul,← Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]
    norm_num
   simp only [Nat.cast_ofNat]
   rw [hsq27]
  rw [hnum_fac,hden_fac]
  have hsum35:∑ u∈Finset.Icc (1:ℕ) 10,((35-2*u:ℕ):ℂ)=240:=by
   have:∑ u∈Finset.Icc (1:ℕ) 10,(35-2*u)=240:=by decide
   exact_mod_cast this
  have hexp_simpl :
    (∑ u∈Finset.Icc (1:ℕ) 10,
      ((((35-2*u:ℕ):ℂ)*(n:ℂ)+1/2)*Complex.log (n:ℂ) +
       ((35-2*u:ℕ):ℂ)*(n:ℂ)*Complex.log ((35-2*u:ℕ):ℂ) -
       ((35-2*u:ℕ):ℂ)*(n:ℂ) +
       z260 (((35-2*u)*n:ℕ):ℂ))) -
     6*((27*(n:ℂ)+1/2)*Complex.log (n:ℂ) +
      27*(n:ℂ)*Complex.log 27-27*(n:ℂ) +
      z260 ((27*n:ℕ):ℂ)) =
    (78*(n:ℂ)+2)*Complex.log (n:ℂ) +
     (n:ℂ)*(∑ u∈Finset.Icc (1:ℕ) 10,
       (((35-2*u:ℕ):ℂ)*Complex.log ((35-2*u:ℕ):ℂ)) -
      162*Complex.log 27) -
     78*(n:ℂ) +
     (∑ u∈Finset.Icc (1:ℕ) 10,z260 (((35-2*u)*n:ℕ):ℂ)) -
     6*z260 ((27*n:ℕ):ℂ):=by
   have hsplit1:∑ u∈Finset.Icc (1:ℕ) 10,
     ((((35-2*u:ℕ):ℂ)*(n:ℂ)+1/2)*Complex.log (n:ℂ) +
      ((35-2*u:ℕ):ℂ)*(n:ℂ)*Complex.log ((35-2*u:ℕ):ℂ) -
      ((35-2*u:ℕ):ℂ)*(n:ℂ) +
      z260 (((35-2*u)*n:ℕ):ℂ)) =
     ((∑ u∈Finset.Icc (1:ℕ) 10,((35-2*u:ℕ):ℂ))*(n:ℂ)+5)*Complex.log (n:ℂ) +
     (n:ℂ)*(∑ u∈Finset.Icc (1:ℕ) 10,
      (((35-2*u:ℕ):ℂ)*Complex.log ((35-2*u:ℕ):ℂ))) -
     (∑ u∈Finset.Icc (1:ℕ) 10,((35-2*u:ℕ):ℂ))*(n:ℂ) +
     (∑ u∈Finset.Icc (1:ℕ) 10,z260 (((35-2*u)*n:ℕ):ℂ)):=by
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,Finset.mul_sum]
    have hhalf:∑ _u∈Finset.Icc (1:ℕ) 10,(1/2:ℂ)=5:=by norm_num
    have hrew:∑ u∈Finset.Icc (1:ℕ) 10,
      (n:ℂ)*(((35-2*u:ℕ):ℂ)*Complex.log ((35-2*u:ℕ):ℂ)) =
      ∑ u∈Finset.Icc (1:ℕ) 10,
       ((35-2*u:ℕ):ℂ)*(n:ℂ)*Complex.log ((35-2*u:ℕ):ℂ):=
     Finset.sum_congr rfl fun u _=>by ring
    rw [hrew,hhalf]
   rw [hsplit1,hsum35];ring
  have hpow4:(((Real.sqrt (2*Real.pi):ℝ):ℂ))^10/(((Real.sqrt (2*Real.pi):ℝ):ℂ))^6 =
    ((2*Real.pi:ℝ):ℂ)^2:=by
   rw [show (10:ℕ)=4+6 by norm_num,pow_add,mul_div_cancel_right₀ _ (pow_ne_zero 6 hsq2pi_ne),
    show (4:ℕ)=2*2 by norm_num,pow_mul,hsq2pi_sq]
  rw [← hexp_simpl,Complex.exp_sub]
  set En:=∑ u∈Finset.Icc (1:ℕ) 10,
   ((((35-2*u:ℕ):ℂ)*(n:ℂ)+1/2)*Complex.log (n:ℂ) +
    ((35-2*u:ℕ):ℂ)*(n:ℂ)*Complex.log ((35-2*u:ℕ):ℂ) -
    ((35-2*u:ℕ):ℂ)*(n:ℂ) +
    z260 (((35-2*u)*n:ℕ):ℂ))
  set Ed:=6*((27*(n:ℂ)+1/2)*Complex.log (n:ℂ) +
   27*(n:ℂ)*Complex.log 27-27*(n:ℂ) +
   z260 ((27*n:ℕ):ℂ))
  calc
   (((Real.sqrt (2*Real.pi):ℝ):ℂ))^10 *
     (∏ u∈Finset.Icc (1:ℕ) 10,((Real.sqrt ((35-2*u:ℕ):ℝ):ℝ):ℂ))*Complex.exp En /
     ((((Real.sqrt (2*Real.pi):ℝ):ℂ))^6*27^3*Complex.exp Ed)
    = ((((Real.sqrt (2*Real.pi):ℝ):ℂ))^10/(((Real.sqrt (2*Real.pi):ℝ):ℂ))^6) *
      (∏ u∈Finset.Icc (1:ℕ) 10,((Real.sqrt ((35-2*u:ℕ):ℝ):ℝ):ℂ))/27^3 *
      (Complex.exp En/Complex.exp Ed):=by ring
   _=_:=by rw [hpow4]
 have hG_part1 :
   Complex.Gamma ((n:ℂ)*ζ)^3*Complex.Gamma ((27*n+1:ℕ)-(n:ℂ)*ζ)^3 *
    (Complex.Gamma ((n:ℂ)*ζ+(64*n+1:ℕ)) /
     Complex.Gamma ((n:ℂ)*ζ+(37*n+1:ℕ)))^3 =
   ((2*Real.pi:ℝ):ℂ)^3 *
    Complex.exp ((162*(n:ℂ))*Complex.log (n:ℂ) +
     (n:ℂ)*(3*ζ*Complex.log ζ+3*(27 - ζ)*Complex.log (27 - ζ) +
      3*(ζ+64)*Complex.log (ζ+64)-3*(ζ+37)*Complex.log (ζ+37)) +
     (-(3/2:ℂ)*Complex.log ζ+(3/2:ℂ)*Complex.log (27 - ζ) +
      (3/2:ℂ)*Complex.log (ζ+64)-(3/2:ℂ)*Complex.log (ζ+37)) -
     162*(n:ℂ) +
     3*z260 ((n:ℂ)*ζ)+3*z260 ((n:ℂ)*(27 - ζ)) +
     3*z260 ((n:ℂ)*(ζ+64))-3*z260 ((n:ℂ)*(ζ+37))):=by
  rw [show (((27*n+1:ℕ):ℂ)-(n:ℂ)*ζ)=(n:ℂ)*(27 - ζ)+1 by push_cast;ring,
   show ((n:ℂ)*ζ+((64*n+1:ℕ):ℂ))=(n:ℂ)*(ζ+64)+1 by push_cast;ring,
   show ((n:ℂ)*ζ+((37*n+1:ℕ):ℂ))=(n:ℂ)*(ζ+37)+1 by push_cast;ring]
  rw [hG ζ (by linarith),hG1 (27 - ζ) (by simp;linarith),
   hG1 (ζ+64) (by simp;linarith),hG1 (ζ+37) (by simp;linarith)]
  rw [mul_div_mul_left _ _ hsq2pi_ne,← Complex.exp_sub,mul_pow,mul_pow,
   ← Complex.exp_nat_mul,← Complex.exp_nat_mul,← Complex.exp_nat_mul]
  have hpow6:(((Real.sqrt (2*Real.pi):ℝ):ℂ))^3*(((Real.sqrt (2*Real.pi):ℝ):ℂ))^3 =
    ((2*Real.pi:ℝ):ℂ)^3:=by
   rw [← pow_add,show (3+3:ℕ)=2*3 by norm_num,pow_mul,hsq2pi_sq]
  set E1:=(3:ℕ)*(((n:ℂ)*ζ - 1/2)*Complex.log (n:ℂ) +
   ((n:ℂ)*ζ - 1/2)*Complex.log ζ - (n:ℂ)*ζ+z260 ((n:ℂ)*ζ))
  set E2:=(3:ℕ)*(((n:ℂ)*(27 - ζ)+1/2)*Complex.log (n:ℂ) +
   ((n:ℂ)*(27 - ζ)+1/2)*Complex.log (27 - ζ)-(n:ℂ)*(27 - ζ) +
   z260 ((n:ℂ)*(27 - ζ)))
  set E3:=(3:ℕ)*((((n:ℂ)*(ζ+64)+1/2)*Complex.log (n:ℂ) +
   ((n:ℂ)*(ζ+64)+1/2)*Complex.log (ζ+64)-(n:ℂ)*(ζ+64) +
   z260 ((n:ℂ)*(ζ+64))) -
   (((n:ℂ)*(ζ+37)+1/2)*Complex.log (n:ℂ) +
    ((n:ℂ)*(ζ+37)+1/2)*Complex.log (ζ+37)-(n:ℂ)*(ζ+37) +
    z260 ((n:ℂ)*(ζ+37))))
  calc
   (((Real.sqrt (2*Real.pi):ℝ):ℂ))^3*Complex.exp E1 *
      ((((Real.sqrt (2*Real.pi):ℝ):ℂ))^3*Complex.exp E2)*Complex.exp E3
    = ((((Real.sqrt (2*Real.pi):ℝ):ℂ))^3*(((Real.sqrt (2*Real.pi):ℝ):ℂ))^3) *
      (Complex.exp E1*Complex.exp E2*Complex.exp E3):=by ring
   _=((2*Real.pi:ℝ):ℂ)^3*Complex.exp _:=by
     rw [hpow6,← Complex.exp_add,← Complex.exp_add]
     congr 2;dsimp only [E1,E2,E3];push_cast;ring
 have hG_part2 :
   (∏ u∈Finset.Icc (1:ℕ) 10,
    (Complex.Gamma ((n:ℂ)*ζ+((1+u)*n:ℕ)) /
     Complex.Gamma ((n:ℂ)*ζ+((36-u)*n+1:ℕ)))) =
   Complex.exp ((-240*(n:ℂ)-10)*Complex.log (n:ℂ) +
    (n:ℂ)*(∑ u∈Finset.Icc (1:ℕ) 10,
     ((ζ+((1+u:ℕ):ℂ))*Complex.log (ζ+((1+u:ℕ):ℂ)) -
      (ζ+((36-u:ℕ):ℂ))*Complex.log (ζ+((36-u:ℕ):ℂ)))) -
    (1/2:ℂ)*(∑ u∈Finset.Icc (1:ℕ) 10,
     (Complex.log (ζ+((1+u:ℕ):ℂ))+Complex.log (ζ+((36-u:ℕ):ℂ)))) +
    240*(n:ℂ) +
    ∑ u∈Finset.Icc (1:ℕ) 10,
     (z260 ((n:ℂ)*(ζ+((1+u:ℕ):ℂ))) -
      z260 ((n:ℂ)*(ζ+((36-u:ℕ):ℂ))))):=by
  have hcongr:(∏ u∈Finset.Icc (1:ℕ) 10,
    (Complex.Gamma ((n:ℂ)*ζ+((1+u)*n:ℕ)) /
     Complex.Gamma ((n:ℂ)*ζ+((36-u)*n+1:ℕ)))) =
    ∏ u∈Finset.Icc (1:ℕ) 10,
     Complex.exp (((-((35-2*u:ℕ):ℂ)*(n:ℂ)-1)*Complex.log (n:ℂ)) +
      (n:ℂ)*((ζ+((1+u:ℕ):ℂ))*Complex.log (ζ+((1+u:ℕ):ℂ)) -
       (ζ+((36-u:ℕ):ℂ))*Complex.log (ζ+((36-u:ℕ):ℂ))) -
      (1/2:ℂ)*(Complex.log (ζ+((1+u:ℕ):ℂ))+Complex.log (ζ+((36-u:ℕ):ℂ))) +
      ((35-2*u:ℕ):ℂ)*(n:ℂ) +
      (z260 ((n:ℂ)*(ζ+((1+u:ℕ):ℂ))) -
       z260 ((n:ℂ)*(ζ+((36-u:ℕ):ℂ))))):=by
   refine Finset.prod_congr rfl fun u hu=>?_
   have hu10:=(Finset.mem_Icc.mp hu).2
   rw [show ((n:ℂ)*ζ+(((1+u)*n:ℕ):ℂ))=(n:ℂ)*(ζ+((1+u:ℕ):ℂ)) by push_cast;ring,
    show ((n:ℂ)*ζ+(((36-u)*n+1:ℕ):ℂ))=(n:ℂ)*(ζ+((36-u:ℕ):ℂ))+1 by push_cast;ring]
   rw [hG _ (by simp;linarith [Nat.cast_nonneg (α:=ℝ) u]),
    hG1 _ (by simp;linarith [Nat.cast_nonneg (α:=ℝ) (36-u)]),
    mul_div_mul_left _ _ hsq2pi_ne,← Complex.exp_sub]
   congr 1
   have hdiff:((36-u:ℕ):ℂ)-((1+u:ℕ):ℂ)=((35-2*u:ℕ):ℂ):=by
    have hnat:(36-u)=(1+u)+(35-2*u):=by omega
    have hc:((36-u:ℕ):ℂ)=((1+u:ℕ):ℂ)+((35-2*u:ℕ):ℂ):=by exact_mod_cast hnat
    linear_combination hc
   linear_combination ((n:ℂ)-(n:ℂ)*Complex.log (n:ℂ))*hdiff
  rw [hcongr,← Complex.exp_sum]
  congr 1
  have hsum35:∑ u∈Finset.Icc (1:ℕ) 10,((35-2*u:ℕ):ℂ)=240:=by
   have:∑ u∈Finset.Icc (1:ℕ) 10,(35-2*u)=240:=by decide
   exact_mod_cast this
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.mul_sum,
   Finset.sum_neg_distrib]
  have h10:∑ _u∈Finset.Icc (1:ℕ) 10,(1:ℂ)=10:=by norm_num
  rw [hsum35,h10]
 unfold Z4.z88
 rw [hcos,hscale,hG_part1,hG_part2]
 have hlin37:(((37*n:ℕ):ℂ)+2*((n:ℂ)*ζ))=(n:ℂ)*(37+2*ζ):=by
  push_cast;ring
 rw [hlin37]
 have hn_log:((n:ℂ)^7)⁻¹=(n:ℂ)*Complex.exp ((-8:ℂ)*Complex.log (n:ℂ)):=by
  have h8:Complex.exp ((-8:ℂ)*Complex.log (n:ℂ))=((n:ℂ)^8)⁻¹:=by
   rw [show (-8:ℂ)*Complex.log (n:ℂ)=-((8:ℕ)*Complex.log (n:ℂ)) by push_cast;ring,
    Complex.exp_neg,Complex.exp_nat_mul,Complex.exp_log hn_ne]
  rw [h8]
  field_simp [hn_ne]
 unfold z182 z180 wPot z262
 rw [hn_log]
 set C0:=((1/2:ℂ)*((2*Real.pi:ℝ):ℂ)^5 *
  (∏ u∈Finset.Icc (1:ℕ) 10,((Real.sqrt ((35-2*u:ℕ):ℝ):ℝ):ℂ))/(27:ℂ)^3)
 set P1:=(1+Complex.exp (-2*I*(Real.pi:ℂ)*(n:ℂ)*ζ))
 set A1:=(n:ℂ)*(I*(Real.pi:ℂ)*(ζ+1))
 set A2:=(78*(n:ℂ)+2)*Complex.log (n:ℂ) +
  (n:ℂ)*(∑ u∈Finset.Icc (1:ℕ) 10,
   (((35-2*u:ℕ):ℂ)*Complex.log ((35-2*u:ℕ):ℂ))-162*Complex.log 27) -
  78*(n:ℂ) +
  (∑ u∈Finset.Icc (1:ℕ) 10,z260 (((35-2*u)*n:ℕ):ℂ)) -
  6*z260 ((27*n:ℕ):ℂ)
 set A3:=(162*(n:ℂ))*Complex.log (n:ℂ) +
  (n:ℂ)*(3*ζ*Complex.log ζ+3*(27 - ζ)*Complex.log (27 - ζ) +
   3*(ζ+64)*Complex.log (ζ+64)-3*(ζ+37)*Complex.log (ζ+37)) +
  (-(3/2:ℂ)*Complex.log ζ+(3/2:ℂ)*Complex.log (27 - ζ) +
   (3/2:ℂ)*Complex.log (ζ+64)-(3/2:ℂ)*Complex.log (ζ+37)) -
  162*(n:ℂ) +
  3*z260 ((n:ℂ)*ζ)+3*z260 ((n:ℂ)*(27 - ζ)) +
  3*z260 ((n:ℂ)*(ζ+64))-3*z260 ((n:ℂ)*(ζ+37))
 set A4:=(-240*(n:ℂ)-10)*Complex.log (n:ℂ) +
  (n:ℂ)*(∑ u∈Finset.Icc (1:ℕ) 10,
   ((ζ+((1+u:ℕ):ℂ))*Complex.log (ζ+((1+u:ℕ):ℂ)) -
    (ζ+((36-u:ℕ):ℂ))*Complex.log (ζ+((36-u:ℕ):ℂ)))) -
  (1/2:ℂ)*(∑ u∈Finset.Icc (1:ℕ) 10,
   (Complex.log (ζ+((1+u:ℕ):ℂ))+Complex.log (ζ+((36-u:ℕ):ℂ)))) +
  240*(n:ℂ) +
  ∑ u∈Finset.Icc (1:ℕ) 10,
   (z260 ((n:ℂ)*(ζ+((1+u:ℕ):ℂ))) -
    z260 ((n:ℂ)*(ζ+((36-u:ℕ):ℂ))))
 set B2:=-(3/2:ℂ)*Complex.log ζ+(3/2:ℂ)*Complex.log (27 - ζ) +
  (3/2:ℂ)*Complex.log (ζ+64)-(3/2:ℂ)*Complex.log (ζ+37) -
  (1/2:ℂ)*∑ u∈Finset.Icc (1:ℕ) 10,
   (Complex.log (ζ+((1+u:ℕ):ℂ))+Complex.log (ζ+((36-u:ℕ):ℂ)))
 set B3:=(n:ℂ)*(I*(Real.pi:ℂ)*(ζ+1) +
   (∑ u∈Finset.Icc (1:ℕ) 10,(((35-2*u:ℕ):ℂ)*Complex.log ((35-2*u:ℕ):ℂ))) -
   162*Complex.log 27+3*ζ*Complex.log ζ+3*(27 - ζ)*Complex.log (27 - ζ) +
   3*(ζ+64)*Complex.log (ζ+64)-3*(ζ+37)*Complex.log (ζ+37) +
   ∑ u∈Finset.Icc (1:ℕ) 10,
    ((ζ+((1+u:ℕ):ℂ))*Complex.log (ζ+((1+u:ℕ):ℂ)) -
     (ζ+((36-u:ℕ):ℂ))*Complex.log (ζ+((36-u:ℕ):ℂ)))) +
  ((∑ u∈Finset.Icc (1:ℕ) 10,z260 (((35-2*u)*n:ℕ):ℂ)) -
   6*z260 ((27*n:ℕ):ℂ)+3*z260 ((n:ℂ)*ζ) +
   3*z260 ((n:ℂ)*(27 - ζ))+3*z260 ((n:ℂ)*(ζ+64)) -
   3*z260 ((n:ℂ)*(ζ+37)) +
   ∑ u∈Finset.Icc (1:ℕ) 10,
    (z260 ((n:ℂ)*(ζ+((1+u:ℕ):ℂ))) -
     z260 ((n:ℂ)*(ζ+((36-u:ℕ):ℂ)))))
 have hlhs_group :
   (1/2:ℂ)*P1*Complex.exp A1 *
    (((2*Real.pi:ℝ):ℂ)^2 *
     (∏ u∈Finset.Icc (1:ℕ) 10,((Real.sqrt ((35-2*u:ℕ):ℝ):ℝ):ℂ))/27^3 *
     Complex.exp A2) *
    ((n:ℂ)*(37+2*ζ)) *
    (((2*Real.pi:ℝ):ℂ)^3*Complex.exp A3) *
    Complex.exp A4 =
   (n:ℂ)*(C0*(37+2*ζ))*P1 *
    (Complex.exp A1*Complex.exp A2*Complex.exp A3*Complex.exp A4):=by
  dsimp only [C0];ring
 have hrhs_group :
   (n:ℂ)*Complex.exp ((-8:ℂ)*Complex.log (n:ℂ)) *
    (C0*(37+2*ζ)*Complex.exp B2)*P1*Complex.exp B3 =
   (n:ℂ)*(C0*(37+2*ζ))*P1 *
    (Complex.exp ((-8:ℂ)*Complex.log (n:ℂ))*Complex.exp B2*Complex.exp B3):=by ring
 rw [hlhs_group,hrhs_group]
 congr 1
 simp only [← Complex.exp_add]
 congr 1
 dsimp only [A1,A2,A3,A4,B2,B3]
 ring
lemma z146
  (hdw:∀ {z:ℂ},0< z.re→ z.re< 27→ HasDerivAt wPot (dwPot z) z)
  (hd2w:∀ {z:ℂ},0< z.re→ z.re< 27→ HasDerivAt dwPot (z53 z) z)
  (hd3w:∀ {z:ℂ},0< z.re→ z.re< 27→ HasDerivAt z53 (z55 z) z)
  {z₀:ℂ} (h1:(234/10:ℝ) ≤ z₀.re) (h2:z₀.re ≤ (236/10:ℝ))
  (hdw0:dwPot z₀=0) {h:ℂ} (hh:‖h‖ ≤ 1/10) :
  ‖wPot (z₀+h)-wPot z₀-(1/2:ℂ)*z53 z₀*h^2‖ ≤ 2*‖h‖^3:=by
 let B:Set ℂ:=Metric.closedBall z₀ (1/10)
 have hB_re:∀ w∈B,(23:ℝ) ≤ w.re∧w.re ≤ (24:ℝ):=by
  intro w hw
  have hd:‖w-z₀‖ ≤ 1/10:=by simpa [B,dist_eq_norm] using hw
  have hre:=(Complex.abs_re_le_norm (w-z₀)).trans hd
  simp only [Complex.sub_re] at hre
  constructor <;> linarith [abs_le.mp hre]
 have hd3_le:∀ w∈B,‖z55 w‖ ≤ 2:=by
  intro w hw
  have hre:=hB_re w hw
  have hinv_le:∀ (c:ℂ) (r:ℝ),0< r→ r ≤ c.re→ ‖1/c^2‖ ≤ 1/r^2:=by
   intro c r hr hcr
   rw [one_div,norm_inv,norm_pow,← one_div]
   refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
   have:=hcr.trans (Complex.re_le_norm c);nlinarith
  have hinv3_le:∀ (c:ℂ) (r:ℝ),0< r→ r ≤ c.re→ ‖(3:ℂ)/c^2‖ ≤ 3/r^2:=by
   intro c r hr hcr
   rw [show (3:ℂ)/c^2=3*(1/c^2) by ring,norm_mul,Complex.norm_ofNat,
    show (3:ℝ)/r^2=3*(1/r^2) by ring]
   linarith [hinv_le c r hr hcr]
  unfold z55
  have b1:‖(-3:ℂ)/w^2‖ ≤ 3/(23:ℝ)^2:=by
   rw [neg_div,norm_neg];exact hinv3_le w 23 (by norm_num) (by linarith [hre.1])
  have b2:‖(3:ℂ)/(27-w)^2‖ ≤ 3/(3:ℝ)^2:=
   hinv3_le (27-w) 3 (by norm_num) (by simp;linarith [hre.2])
  have b3:‖(3:ℂ)/(w+64)^2‖ ≤ 3/(80:ℝ)^2:=
   hinv3_le (w+64) 80 (by norm_num) (by simp;linarith [hre.1])
  have b4:‖(3:ℂ)/(w+37)^2‖ ≤ 3/(60:ℝ)^2:=
   hinv3_le (w+37) 60 (by norm_num) (by simp;linarith [hre.1])
  have b5:‖∑ u∈Finset.Icc (1:ℕ) 10,
    (-1/(w+((1+u:ℕ):ℂ))^2+1/(w+((36-u:ℕ):ℂ))^2)‖ ≤ 10*(2/(20:ℝ)^2):=by
   refine (norm_sum_le _ _).trans ?_
   calc
    ∑ u∈Finset.Icc (1:ℕ) 10,
      ‖-1/(w+((1+u:ℕ):ℂ))^2+1/(w+((36-u:ℕ):ℂ))^2‖
     ≤ ∑ _u∈Finset.Icc (1:ℕ) 10,(2/(20:ℝ)^2):=by
      refine Finset.sum_le_sum fun u _=>(norm_add_le _ _).trans ?_
      rw [neg_div,norm_neg]
      have ha:=hinv_le (w+((1+u:ℕ):ℂ)) 20 (by norm_num) (by simp;linarith [hre.1,Nat.cast_nonneg (α:=ℝ) u])
      have hb:=hinv_le (w+((36-u:ℕ):ℂ)) 20 (by norm_num) (by simp;linarith [hre.1,Nat.cast_nonneg (α:=ℝ) (36-u)])
      linarith
    _=10*(2/(20:ℝ)^2):=by norm_num
  have t1:=norm_add_le (-3/w^2+3/(27-w)^2-3/(w+64)^2+3/(w+37)^2)
   (∑ u∈Finset.Icc (1:ℕ) 10,(-1/(w+((1+u:ℕ):ℂ))^2+1/(w+((36-u:ℕ):ℂ))^2))
  have t2:=norm_add_le (-3/w^2+3/(27-w)^2-3/(w+64)^2) (3/(w+37)^2)
  have t3:=norm_sub_le (-3/w^2+3/(27-w)^2) (3/(w+64)^2)
  have t4:=norm_add_le (-3/w^2) (3/(27-w)^2)
  linarith
 have hd2_lip:∀ w∈B,‖z53 w-z53 z₀‖ ≤ 2*‖w-z₀‖:=by
  intro w hw
  exact Convex.norm_image_sub_le_of_norm_deriv_le (f:=z53) (s:=B) (C:=2)
   (fun u hu=>(hd3w (by linarith [(hB_re u hu).1]) (by linarith [(hB_re u hu).2])).differentiableAt)
   (fun u hu=>by
    rw [(hd3w (by linarith [(hB_re u hu).1]) (by linarith [(hB_re u hu).2])).deriv]
    exact hd3_le u hu)
   (convex_closedBall z₀ _) (Metric.mem_closedBall_self (by norm_num)) hw
 have hmem_t:∀ t∈Set.Icc (0:ℝ) 1,z₀+(t:ℂ)*h∈B:=by
  intro t ht
  simp only [B,Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_mul,
   Complex.norm_real,Real.norm_of_nonneg ht.1]
  nlinarith [ht.2,norm_nonneg h]
 let k:ℝ→ ℂ:=fun t=>dwPot (z₀+(t:ℂ)*h)-z53 z₀*((t:ℂ)*h)
 have hk_d:∀ t∈Set.Icc (0:ℝ) 1,
   HasDerivAt k ((z53 (z₀+(t:ℂ)*h)-z53 z₀)*h) t:=by
  intro t ht
  have hre:=hB_re _ (hmem_t t ht)
  have hlin:HasDerivAt (fun u:ℝ=>z₀+(u:ℂ)*h) h t:=by
   have h1':=(Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const h
   rw [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] at h1'
   exact h1'.const_add z₀
  have hc1:=(hd2w (by linarith [hre.1]) (by linarith [hre.2])).comp t hlin
  have hc2:HasDerivAt (fun u:ℝ=>z53 z₀*((u:ℂ)*h)) (z53 z₀*h) t:=by
   have h1':=(Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const h
   rw [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] at h1'
   exact h1'.const_mul (z53 z₀)
  have hsub:=hc1.fun_sub hc2
  rw [show z53 (z₀+(t:ℂ)*h)*h-z53 z₀*h =
    (z53 (z₀+(t:ℂ)*h)-z53 z₀)*h by ring] at hsub
  exact hsub
 have hk_bd:∀ t∈Set.Icc (0:ℝ) 1,‖k t‖ ≤ 2*‖h‖^2:=by
  intro t ht
  have hmvt:=Convex.norm_image_sub_le_of_norm_deriv_le (f:=k) (s:=Set.Icc 0 1) (C:=2*‖h‖^2)
   (fun u hu=>(hk_d u hu).differentiableAt)
   (fun u hu=>by
    rw [(hk_d u hu).deriv,norm_mul]
    have h1':=hd2_lip _ (hmem_t u hu)
    rw [add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_of_nonneg hu.1] at h1'
    nlinarith [hu.2,norm_nonneg h,sq_nonneg ‖h‖])
   (convex_Icc 0 1) (Set.left_mem_Icc.mpr zero_le_one) ht
  have hk0:k 0=0:=by simp [k,hdw0]
  rw [hk0,sub_zero,Real.norm_eq_abs,sub_zero,abs_of_nonneg ht.1] at hmvt
  nlinarith [ht.2,sq_nonneg ‖h‖]
 let g:ℝ→ ℂ:=fun t=>wPot (z₀+(t:ℂ)*h)-wPot z₀ -
  (1/2:ℂ)*z53 z₀*((t:ℂ)*h)^2
 have hg_d:∀ t∈Set.Icc (0:ℝ) 1,HasDerivAt g (k t*h) t:=by
  intro t ht
  have hre:=hB_re _ (hmem_t t ht)
  have hlin:HasDerivAt (fun u:ℝ=>z₀+(u:ℂ)*h) h t:=by
   have h1':=(Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const h
   rw [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] at h1'
   exact h1'.const_add z₀
  have hc1:=((hdw (by linarith [hre.1]) (by linarith [hre.2])).comp t hlin).sub_const (wPot z₀)
  have hc2:HasDerivAt (fun u:ℝ=>(1/2:ℂ)*z53 z₀*((u:ℂ)*h)^2)
    (z53 z₀*((t:ℂ)*h)*h) t:=by
   have h1':=(Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const h
   rw [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] at h1'
   have h2':=(h1'.pow 2).const_mul ((1/2:ℂ)*z53 z₀)
   simp only [Complex.ofRealCLM_apply] at h2'
   rw [show (1/2:ℂ)*z53 z₀*(((2:ℕ):ℂ)*((t:ℂ)*h)^(2-1)*h) =
     z53 z₀*((t:ℂ)*h)*h by push_cast;ring] at h2'
   exact h2'
  have hsub:=hc1.fun_sub hc2
  rw [show dwPot (z₀+(t:ℂ)*h)*h-z53 z₀*((t:ℂ)*h)*h=k t*h by
   dsimp only [k];ring] at hsub
  exact hsub
 have hmvt_g:=Convex.norm_image_sub_le_of_norm_deriv_le (f:=g) (s:=Set.Icc 0 1) (C:=2*‖h‖^3)
  (fun u hu=>(hg_d u hu).differentiableAt)
  (fun u hu=>by
   rw [(hg_d u hu).deriv,norm_mul]
   calc
    ‖k u‖*‖h‖ ≤ (2*‖h‖^2)*‖h‖:=mul_le_mul_of_nonneg_right (hk_bd u hu) (norm_nonneg h)
    _=2*‖h‖^3:=by ring)
  (convex_Icc 0 1) (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
 have hg0:g 0=0:=by simp [g]
 have hg1:g 1=wPot (z₀+h)-wPot z₀-(1/2:ℂ)*z53 z₀*h^2:=by
  simp [g]
 rw [hg1,hg0,sub_zero,sub_zero,norm_one,mul_one] at hmvt_g
 exact hmvt_g
lemma z89 (n M:ℕ) (y:ℝ) :
  Z4.z88 n ((M:ℂ)+1/2+((-y:ℝ):ℂ)*I) =
   starRingEnd ℂ (Z4.z88 n ((M:ℂ)+1/2+(y:ℂ)*I)):=by
 set z:ℂ:=(M:ℂ)+1/2+(y:ℂ)*I
 have hz_conj:starRingEnd ℂ z=(M:ℂ)+1/2+((-y:ℝ):ℂ)*I:=by
  simp only [z,map_add,map_div₀,map_one,map_ofNat,map_natCast,map_mul,Complex.conj_I,
   Complex.conj_ofReal]
  push_cast;ring
 rw [← hz_conj]
 unfold Z4.z88
 have hrat:starRingEnd ℂ ((Z4.z286 n:ℚ):ℂ)=((Z4.z286 n:ℚ):ℂ):=by
  rw [show ((Z4.z286 n:ℚ):ℂ)=(((Z4.z286 n:ℚ):ℝ):ℂ) by norm_cast,
   Complex.conj_ofReal]
 have hpi:starRingEnd ℂ ((Real.pi:ℂ)*z)=(Real.pi:ℂ)*starRingEnd ℂ z:=by
  rw [map_mul,Complex.conj_ofReal]
 have hsub27:starRingEnd ℂ (((27*n+1:ℕ):ℂ)-z)=((27*n+1:ℕ):ℂ)-starRingEnd ℂ z:=by
  rw [map_sub,map_natCast]
 have hadd:∀ m:ℕ,starRingEnd ℂ (z+(m:ℂ))=starRingEnd ℂ z+(m:ℂ):=fun m=>by
  rw [map_add,map_natCast]
 simp only [map_mul,map_pow,map_div₀,map_prod,map_add,map_neg,map_one,map_ofNat,
  map_natCast,hrat,← Complex.cos_conj,← Complex.Gamma_conj,hpi,hsub27,hadd]
lemma z5
  {z3:ℕ→ ℝ}
  (hF_vert:∀ {n M:ℕ},1 ≤ n→ M ≤ 27*n →
   Integrable (fun y:ℝ=>Z4.z88 n ((M:ℂ)+1/2+(y:ℂ)*I)) ∧
   ((z3 n:ℂ))=-(1/(2*(Real.pi:ℂ))) *
    ∫ y:ℝ,Z4.z88 n ((M:ℂ)+1/2+(y:ℂ)*I))
  {n M:ℕ} (hn:1 ≤ n) (hM:M ≤ 27*n) :
  z3 n=-(1/Real.pi) *
   (∫ y in Set.Iic (0:ℝ),Z4.z88 n ((M:ℂ)+1/2+(y:ℂ)*I)).re:=by
 obtain ⟨hint,hF⟩:=hF_vert hn hM
 let g:ℝ→ ℂ:=fun y=>Z4.z88 n ((M:ℂ)+1/2+(y:ℂ)*I)
 have hsplit:∫ y:ℝ,g y=(∫ y in Set.Iic (0:ℝ),g y)+∫ y in Set.Ioi (0:ℝ),g y:=by
  rw [← Set.compl_Iic]
  exact (integral_add_compl measurableSet_Iic hint).symm
 have hpos_eq:∫ y in Set.Ioi (0:ℝ),g y=starRingEnd ℂ (∫ y in Set.Iic (0:ℝ),g y):=by
  have hcomp:=integral_comp_neg_Iic (c:=(0:ℝ)) (f:=g)
  rw [neg_zero] at hcomp
  rw [← hcomp]
  have hconj:(fun y:ℝ=>g (-y))=(fun y:ℝ=>starRingEnd ℂ (g y)):=
   funext fun y=>z89 n M y
  rw [hconj,integral_conj]
 have hsum_re:(∫ y:ℝ,g y)=(2:ℂ)*(((∫ y in Set.Iic (0:ℝ),g y).re:ℝ):ℂ):=by
  rw [hsplit,hpos_eq,Complex.add_conj]
  push_cast;ring
 have hF_re:=congr_arg Complex.re hF
 rw [hsum_re] at hF_re
 have hcancel:(-(1/(2*(Real.pi:ℂ)))*((2:ℂ)*(((∫ y in Set.Iic (0:ℝ),g y).re:ℝ):ℂ))) =
   (((-(1/Real.pi)*(∫ y in Set.Iic (0:ℝ),g y).re:ℝ):ℂ)):=by
  push_cast;ring
 rw [hcancel,Complex.ofReal_re,Complex.ofReal_re] at hF_re
 exact hF_re
private lemma z106 (C:ℝ) :
  Integrable (fun s:ℝ=>C*(Real.exp (-(s^2)/280)+Real.exp (-|s| / 10))):=by
 have h1:Integrable (fun s:ℝ=>Real.exp (-(s^2)/280)):=by
  have h:=integrable_exp_neg_mul_sq (show (0:ℝ)< 1/280 by norm_num)
  refine h.congr (Filter.Eventually.of_forall fun s=>by ring_nf)
 have h2:Integrable (fun s:ℝ=>Real.exp (-|s| / 10)):=by
  rw [← integrableOn_univ,← Set.Iic_union_Ioi (a:=(0:ℝ)),integrableOn_union]
  constructor
  ·
   have h:=integrableOn_exp_mul_Iic (show (0:ℝ)< 1/10 by norm_num) (0:ℝ)
   refine h.congr_fun (fun s hs=>?_) measurableSet_Iic
   have hs0:s ≤ 0:=hs
   rw [abs_of_nonpos hs0];ring_nf
  ·
   have h:=integrableOn_exp_mul_Ioi (show (-1/10:ℝ)< 0 by norm_num) (0:ℝ)
   refine h.congr_fun (fun s hs=>?_) measurableSet_Ioi
   have hs0:0 ≤ s:=hs.le
   rw [abs_of_nonneg hs0];ring_nf
 exact (h1.add h2).const_mul C
set_option maxHeartbeats 800000 in
theorem z4
  (hlog_mul:∀ {a b:ℂ},0< a.re→ 0< b.re→ Complex.log (a*b)=Complex.log a+Complex.log b)
  (hrem_le:∀ {s:ℂ},0< s.re→ 2 ≤ ‖s‖→ ‖z260 s‖ ≤ 6 / ‖s‖)
  (hstirling:∀ {s:ℂ},0< s.re→ 2 ≤ ‖s‖ →
   Complex.Gamma s=((Real.sqrt (2*Real.pi):ℝ):ℂ) *
    Complex.exp ((s-1/2)*Complex.log s-s+z260 s))
  (hfac_stirling:∀ {m:ℕ},2 ≤ m →
   (m.factorial:ℂ)=((Real.sqrt (2*Real.pi):ℝ):ℂ) *
    Complex.exp (((m:ℂ)+1/2)*Complex.log (m:ℂ)-(m:ℂ)+z260 (m:ℂ)))
  (hdw:∀ {z:ℂ},0< z.re→ z.re< 27→ HasDerivAt wPot (dwPot z) z)
  (hd2w:∀ {z:ℂ},0< z.re→ z.re< 27→ HasDerivAt dwPot (z53 z) z)
  (hd3w:∀ {z:ℂ},0< z.re→ z.re< 27→ HasDerivAt z53 (z55 z) z)
  (hsaddle:∃ z₀:ℂ,
   ‖z₀-z284‖ ≤ 1/1000 ∧
   dwPot z₀=0 ∧
   (wPot z₀).re ≤ -227.4 ∧
   (1/4:ℝ) ≤ |Real.sin (wPot z₀).im| ∧
   (1/2:ℝ) ≤ (z53 z₀).re ∧
   ‖z53 z₀‖ ≤ 1)
  (hglobal:∀ {z₀:ℂ},(234/10:ℝ) ≤ z₀.re→ z₀.re ≤ (236/10:ℝ) →
   -4 ≤ z₀.im→ z₀.im ≤ -3→ dwPot z₀=0→ ∀ {y:ℝ},y ≤ 0 →
   (wPot ((z₀.re:ℂ)+(y:ℂ)*I)).re-(wPot z₀).re ≤
    if -37 ≤ y then -(y-z₀.im)^2/280 else -|y-z₀.im| / 10)
  (hhoriz:∀ {x x₀ y:ℝ},
   (234/10:ℝ) ≤ x→ x ≤ (236/10:ℝ) →
   (234/10:ℝ) ≤ x₀→ x₀ ≤ (236/10:ℝ) →
   |(wPot ((x:ℂ)+(y:ℂ)*I)).re-(wPot ((x₀:ℂ)+(y:ℂ)*I)).re| ≤
    120 * |x-x₀|)
  {z3:ℕ→ ℝ}
  (hF_vert:∀ {n M:ℕ},1 ≤ n→ M ≤ 27*n →
   Integrable (fun y:ℝ=>Z4.z88 n ((M:ℂ)+1/2+(y:ℂ)*I)) ∧
   ((z3 n:ℂ))=-(1/(2*(Real.pi:ℂ))) *
    ∫ y:ℝ,Z4.z88 n ((M:ℂ)+1/2+(y:ℂ)*I)) :
  (∃ C:ℝ,0< C∧∀ᶠ n:ℕ in atTop,|z3 n| ≤ C*Real.exp (-227.4*(n:ℝ))) ∧
  (∀ᶠ n:ℕ in atTop,z3 n≠0∨z3 (n+1)≠0):=by
 obtain ⟨z₀,hz₀_dist,hdw0,hw0_re,hw0_sin,hd2_re,hd2_norm⟩:=hsaddle
 have hz₀_re_bd:(2347/100:ℝ) ≤ z₀.re∧z₀.re ≤ (2349/100:ℝ):=by
  have hre:=(Complex.abs_re_le_norm (z₀-z284)).trans hz₀_dist
  have hzt:z284.re=23479/1000:=by unfold z284;simp;norm_num
  simp only [Complex.sub_re,hzt] at hre
  constructor <;> linarith [abs_le.mp hre]
 have hz₀_im_bd:(-34/10:ℝ) ≤ z₀.im∧z₀.im ≤ (-32/10:ℝ):=by
  have him:=(Complex.abs_im_le_norm (z₀-z284)).trans hz₀_dist
  have hzt:z284.im=-33282/10000:=by unfold z284;simp;norm_num
  simp only [Complex.sub_im,hzt] at him
  constructor <;> linarith [abs_le.mp him]
 let M:ℕ→ ℕ:=fun n=>Nat.floor (z₀.re*(n:ℝ))
 let x:ℕ→ ℝ:=fun n=>((M n:ℝ)+1/2)/(n:ℝ)
 have hM_le:∀ n:ℕ,M n ≤ 27*n:=fun n=>by
  have h1:(M n:ℝ) ≤ z₀.re*(n:ℝ):=Nat.floor_le (by nlinarith [Nat.cast_nonneg (α:=ℝ) n])
  have h2:(M n:ℝ)< ((27*n+1:ℕ):ℝ):=by push_cast;nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have h3:M n< 27*n+1:=by exact_mod_cast h2
  omega
 have hx_diff:∀ n:ℕ,1 ≤ n→ |x n-z₀.re| ≤ 1/(2*(n:ℝ)):=by
  intro n hn
  have hn_pos:(0:ℝ)< n:=Nat.cast_pos.mpr hn
  have hfl_le:(M n:ℝ) ≤ z₀.re*(n:ℝ):=Nat.floor_le (by nlinarith)
  have hfl_lt:z₀.re*(n:ℝ)< (M n:ℝ)+1:=Nat.lt_floor_add_one _
  rw [abs_le]
  have hx_sub:x n-z₀.re=((M n:ℝ)+1/2-z₀.re*(n:ℝ))/(n:ℝ):=by
   dsimp only [x];field_simp [hn_pos.ne']
  rw [hx_sub]
  constructor
  ·
   rw [show -(1/(2*(n:ℝ)))=(-1/2)/(n:ℝ) by ring,div_le_div_iff_of_pos_right hn_pos];linarith
  ·
   rw [show 1/(2*(n:ℝ))=(1/2)/(n:ℝ) by ring,div_le_div_iff_of_pos_right hn_pos];linarith
 have hx_strip:∀ n:ℕ,50 ≤ n→ (234/10:ℝ) ≤ x n∧x n ≤ (236/10:ℝ):=by
  intro n hn
  have hn50:(50:ℝ) ≤ n:=by exact_mod_cast hn
  have hd:=(hx_diff n (by omega)).trans (show 1/(2*(n:ℝ)) ≤ 1/100 by
   exact div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith))
  constructor <;> linarith [abs_le.mp hd,hz₀_re_bd.1,hz₀_re_bd.2]
 let ζn:ℕ→ ℝ→ ℂ:=fun n s=>(x n:ℂ)+((z₀.im+s/Real.sqrt (n:ℝ):ℝ):ℂ)*I
 let fn:ℕ→ ℝ→ ℂ:=fun n s =>
  Set.indicator (Set.Iic (-Real.sqrt (n:ℝ)*z₀.im)) (fun s =>
   z182 (ζn n s) *
    (1+Complex.exp (-2*I*(Real.pi:ℂ)*(n:ℂ)*ζn n s)) *
    Complex.exp ((n:ℂ)*(wPot (ζn n s)-wPot z₀)+z262 n (ζn n s))) s
 let J:ℕ→ ℂ:=fun n=>∫ s:ℝ,fn n s
 have hF_eq_J:∀ n:ℕ,50 ≤ n →
   z3 n =
    -(Real.sqrt (n:ℝ)/(Real.pi*(n:ℝ)^7)) *
     Real.exp ((n:ℝ)*(wPot z₀).re) *
     (Complex.exp (I*(((n:ℝ)*(wPot z₀).im:ℝ):ℂ))*J n).re:=by
  intro n hn
  have hn1:1 ≤ n:=by omega
  have hn_pos:(0:ℝ)< n:=Nat.cast_pos.mpr hn1
  have hsqn_pos:0< Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr hn_pos
  have hxs:=hx_strip n hn
  rw [z5 hF_vert hn1 (hM_le n)]
  have hchg:∫ y in Set.Iic (0:ℝ),Z4.z88 n ((M n:ℂ)+1/2+(y:ℂ)*I) =
    ((Real.sqrt (n:ℝ):ℝ):ℂ)*(((n:ℂ)^7)⁻¹*Complex.exp ((n:ℂ)*wPot z₀))*J n:=by
   let g0:ℝ→ ℂ:=fun y =>
    Set.indicator (Set.Iic (0:ℝ)) (fun y=>Z4.z88 n ((M n:ℂ)+1/2+(y:ℂ)*I)) y
   have h1:∫ y in Set.Iic (0:ℝ),Z4.z88 n ((M n:ℂ)+1/2+(y:ℂ)*I) =
     ∫ y:ℝ,g0 y:=(integral_indicator measurableSet_Iic).symm
   rw [h1]
   have h2:∫ y:ℝ,g0 y=∫ y:ℝ,g0 ((n:ℝ)*z₀.im+y):=
    (integral_add_left_eq_self g0 ((n:ℝ)*z₀.im)).symm
   rw [h2]
   have h3:=(Measure.integral_comp_mul_left (fun y=>g0 ((n:ℝ)*z₀.im+y)) (Real.sqrt (n:ℝ))).symm
   rw [abs_of_pos (inv_pos.mpr hsqn_pos),inv_smul_eq_iff₀ hsqn_pos.ne'] at h3
   rw [h3,Complex.real_smul,← integral_const_mul,← integral_const_mul]
   congr 1;ext s
   dsimp only [g0,fn]
   have hiff:(n:ℝ)*z₀.im+Real.sqrt (n:ℝ)*s ≤ 0↔s ≤ -Real.sqrt (n:ℝ)*z₀.im:=by
    have hsq:Real.sqrt (n:ℝ)*Real.sqrt (n:ℝ)=(n:ℝ):=Real.mul_self_sqrt hn_pos.le
    constructor <;> intro hle
    ·
     have:Real.sqrt (n:ℝ)*s ≤ Real.sqrt (n:ℝ)*(-Real.sqrt (n:ℝ)*z₀.im):=by
      nlinarith [hsq]
     exact le_of_mul_le_mul_left this hsqn_pos
    ·
     have:=mul_le_mul_of_nonneg_left hle hsqn_pos.le
     nlinarith [hsq]
   by_cases hs:s ≤ -Real.sqrt (n:ℝ)*z₀.im
   ·
    have hy0:(n:ℝ)*z₀.im+Real.sqrt (n:ℝ)*s ≤ 0:=hiff.mpr hs
    rw [Set.indicator_of_mem (Set.mem_Iic.mpr hs),Set.indicator_of_mem (Set.mem_Iic.mpr hy0)]
    have harg:(M n:ℂ)+1/2+(((n:ℝ)*z₀.im+Real.sqrt (n:ℝ)*s:ℝ):ℂ)*I =
      (n:ℂ)*ζn n s:=by
     dsimp only [ζn,x]
     have hsq_eq:(n:ℂ)*(((s/Real.sqrt (n:ℝ):ℝ):ℂ))=((Real.sqrt (n:ℝ)*s:ℝ):ℂ):=by
      rw [show (n:ℂ)=((n:ℝ):ℂ) by norm_cast,← Complex.ofReal_mul]
      congr 1
      calc
       (n:ℝ)*(s/Real.sqrt (n:ℝ))
        = (Real.sqrt (n:ℝ)*Real.sqrt (n:ℝ))*(s/Real.sqrt (n:ℝ)):=by
         rw [Real.mul_self_sqrt hn_pos.le]
       _=Real.sqrt (n:ℝ)*s:=by field_simp [hsqn_pos.ne']
     have hx_eq:(n:ℂ)*((((M n:ℝ)+1/2)/(n:ℝ):ℝ):ℂ)=(M n:ℂ)+1/2:=by
      rw [show (n:ℂ)=((n:ℝ):ℂ) by norm_cast,← Complex.ofReal_mul,
       mul_div_cancel₀ _ hn_pos.ne']
      push_cast;rfl
     calc
      (M n:ℂ)+1/2+(((n:ℝ)*z₀.im+Real.sqrt (n:ℝ)*s:ℝ):ℂ)*I
       = (n:ℂ)*((((M n:ℝ)+1/2)/(n:ℝ):ℝ):ℂ) +
         ((n:ℂ)*(z₀.im:ℂ)+(n:ℂ)*((s/Real.sqrt (n:ℝ):ℝ):ℂ))*I:=by
        rw [hx_eq,hsq_eq];push_cast;ring
      _=(n:ℂ)*(((((M n:ℝ)+1/2)/(n:ℝ):ℝ):ℂ) +
         ((z₀.im+s/Real.sqrt (n:ℝ):ℝ):ℂ)*I):=by push_cast;ring
    rw [harg,z90 hlog_mul hstirling hfac_stirling hn1
     (by simp [ζn];exact hxs.1) (by simp [ζn];exact hxs.2)]
    have hexp_split:Complex.exp ((n:ℂ)*wPot (ζn n s)+z262 n (ζn n s)) =
      Complex.exp ((n:ℂ)*wPot z₀) *
       Complex.exp ((n:ℂ)*(wPot (ζn n s)-wPot z₀)+z262 n (ζn n s)):=by
     rw [← Complex.exp_add];congr 1;ring
    rw [hexp_split];ring
   ·
    have hy0:¬ ((n:ℝ)*z₀.im+Real.sqrt (n:ℝ)*s ≤ 0):=mt hiff.mp hs
    rw [Set.indicator_of_notMem (Set.mem_Iic.not.mpr hs),
     Set.indicator_of_notMem (Set.mem_Iic.not.mpr hy0),mul_zero,mul_zero]
  rw [hchg]
  have hexp_split:Complex.exp ((n:ℂ)*wPot z₀) =
    ((Real.exp ((n:ℝ)*(wPot z₀).re):ℝ):ℂ) *
     Complex.exp (I*(((n:ℝ)*(wPot z₀).im:ℝ):ℂ)):=by
   rw [Complex.ofReal_exp,← Complex.exp_add]
   congr 1
   have hdecomp:wPot z₀=((wPot z₀).re:ℂ)+((wPot z₀).im:ℂ)*I:=
    (Complex.re_add_im _).symm
   conv_lhs=>rw [hdecomp]
   push_cast;ring
  rw [hexp_split]
  have hreal_factor :
    ((Real.sqrt (n:ℝ):ℝ):ℂ) *
     (((n:ℂ)^7)⁻¹*(((Real.exp ((n:ℝ)*(wPot z₀).re):ℝ):ℂ) *
      Complex.exp (I*(((n:ℝ)*(wPot z₀).im:ℝ):ℂ))))*J n =
    (((Real.sqrt (n:ℝ)/(n:ℝ)^7*Real.exp ((n:ℝ)*(wPot z₀).re):ℝ):ℂ)) *
     (Complex.exp (I*(((n:ℝ)*(wPot z₀).im:ℝ):ℂ))*J n):=by
   push_cast;ring
  rw [hreal_factor,Complex.re_ofReal_mul]
  ring
 let Cdom:ℝ:=‖z180‖*24*Real.exp 64
 have hdom_bd:∀ n:ℕ,50 ≤ n→ ∀ s:ℝ,
   ‖fn n s‖ ≤ Cdom*(Real.exp (-(s^2)/280)+Real.exp (-|s| / 10)):=by
  intro n hn s
  have hxs:=hx_strip n hn
  have hn_pos:(0:ℝ)< n:=Nat.cast_pos.mpr (by omega)
  have hsqn_pos:0< Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr hn_pos
  by_cases hs:s ≤ -Real.sqrt (n:ℝ)*z₀.im
  ·
   simp only [fn,Set.indicator_of_mem (show s∈Set.Iic _ from hs)]
   set y:ℝ:=z₀.im+s/Real.sqrt (n:ℝ)
   have hy0:y ≤ 0:=by
    dsimp only [y]
    have:s/Real.sqrt (n:ℝ) ≤ -z₀.im:=by
     rw [div_le_iff₀ hsqn_pos];nlinarith
    linarith
   have hζ_re:(ζn n s).re=x n:=by simp [ζn]
   have hζ_im:(ζn n s).im=y:=by simp [ζn,y]
   have hp_bd:‖z182 (ζn n s)‖ ≤ ‖z180‖*12:=
    z142 (by rw [hζ_re];exact hxs.1) (by rw [hζ_re];exact hxs.2)
   have hcos_bd:‖1+Complex.exp (-2*I*(Real.pi:ℂ)*(n:ℂ)*ζn n s)‖ ≤ 2:=by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one,Complex.norm_exp]
    have hre_e:(-2*I*(Real.pi:ℂ)*(n:ℂ)*ζn n s).re=2*Real.pi*(n:ℝ)*y:=by
     rw [show -2*I*(Real.pi:ℂ)*(n:ℂ)*ζn n s =
       (((2*Real.pi*(n:ℝ):ℝ):ℂ))*(-I*ζn n s) by push_cast;ring,
      Complex.re_ofReal_mul]
     simp [hζ_im]
    rw [hre_e]
    have hle1:Real.exp (2*Real.pi*(n:ℝ)*y) ≤ 1:=
     Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) hy0)
    linarith
   have hrem_bd:(z262 n (ζn n s)).re ≤ 4:=by
    have h1':=(Complex.re_le_norm _).trans
     (z145 hrem_le (n:=n) (by omega) (by rw [hζ_re];exact hxs.1) (by rw [hζ_re];exact hxs.2))
    have hn50:(50:ℝ) ≤ n:=by exact_mod_cast hn
    have h2':200/(n:ℝ) ≤ 4:=by rw [div_le_iff₀ hn_pos];linarith
    linarith
   have hhor_bd:(n:ℝ)*((wPot (ζn n s)).re-(wPot ((z₀.re:ℂ)+(y:ℂ)*I)).re) ≤ 60:=by
    have h1':=(le_abs_self _).trans (hhoriz (x:=x n) (x₀:=z₀.re) (y:=y)
     hxs.1 hxs.2 (by linarith [hz₀_re_bd.1]) (by linarith [hz₀_re_bd.2]))
    have h2':=hx_diff n (by omega)
    have h3':(n:ℝ)*(120 * |x n-z₀.re|) ≤ 60:=by
     calc
      (n:ℝ)*(120 * |x n-z₀.re|) ≤ (n:ℝ)*(120*(1/(2*(n:ℝ)))):=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2' (by norm_num)) hn_pos.le
      _=60:=by field_simp [hn_pos.ne'];ring
    have hζ_eq:ζn n s=(x n:ℂ)+(y:ℂ)*I:=rfl
    rw [hζ_eq];nlinarith
   have hglob_bd:=hglobal (by linarith [hz₀_re_bd.1]) (by linarith [hz₀_re_bd.2])
    (by linarith [hz₀_im_bd.1]) (by linarith [hz₀_im_bd.2]) hdw0 hy0
   have hexp_main:Real.exp (((n:ℂ)*(wPot (ζn n s)-wPot z₀)+z262 n (ζn n s)).re) ≤
     Real.exp 64*(Real.exp (-(s^2)/280)+Real.exp (-|s| / 10)):=by
    have hre_tot:((n:ℂ)*(wPot (ζn n s)-wPot z₀)+z262 n (ζn n s)).re =
      (n:ℝ)*((wPot (ζn n s)).re-(wPot ((z₀.re:ℂ)+(y:ℂ)*I)).re) +
      (n:ℝ)*((wPot ((z₀.re:ℂ)+(y:ℂ)*I)).re-(wPot z₀).re) +
      (z262 n (ζn n s)).re:=by
     simp only [Complex.add_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
      zero_mul,sub_zero,Complex.sub_re]
     ring
    rw [hre_tot]
    split_ifs at hglob_bd with hy37
    ·
     have hysq:(n:ℝ)*(-(y-z₀.im)^2/280)=-(s^2)/280:=by
      have hy_sub:y-z₀.im=s/Real.sqrt (n:ℝ):=by dsimp only [y];ring
      rw [hy_sub,div_pow,Real.sq_sqrt hn_pos.le]
      field_simp [hn_pos.ne']
     have hle_exp:Real.exp ((n:ℝ)*((wPot (ζn n s)).re-(wPot ((z₀.re:ℂ)+(y:ℂ)*I)).re) +
        (n:ℝ)*((wPot ((z₀.re:ℂ)+(y:ℂ)*I)).re-(wPot z₀).re) +
        (z262 n (ζn n s)).re) ≤ Real.exp (64+-(s^2)/280):=by
      refine Real.exp_le_exp.mpr ?_
      have:=mul_le_mul_of_nonneg_left hglob_bd hn_pos.le
      linarith
     rw [Real.exp_add 64] at hle_exp
     nlinarith [Real.exp_pos 64,Real.exp_pos (-|s| / 10)]
    ·
     have hyabs:(n:ℝ)*(-|y-z₀.im| / 10) ≤ -|s| / 10:=by
      have hy_sub:y-z₀.im=s/Real.sqrt (n:ℝ):=by dsimp only [y];ring
      rw [hy_sub,abs_div,abs_of_pos hsqn_pos]
      have h1':(n:ℝ)*(-(|s| / Real.sqrt (n:ℝ))/10)=-(Real.sqrt (n:ℝ) * |s|)/10:=by
       calc
        (n:ℝ)*(-(|s| / Real.sqrt (n:ℝ))/10)
         = (Real.sqrt (n:ℝ)*Real.sqrt (n:ℝ))*(-(|s| / Real.sqrt (n:ℝ))/10):=by
          rw [Real.mul_self_sqrt hn_pos.le]
        _=-(Real.sqrt (n:ℝ) * |s|)/10:=by field_simp [hsqn_pos.ne']
      rw [h1']
      have hsq1:1 ≤ Real.sqrt (n:ℝ):=by
       rw [Real.one_le_sqrt];exact_mod_cast (show 1 ≤ n by omega)
      nlinarith [abs_nonneg s]
     have hle_exp:Real.exp ((n:ℝ)*((wPot (ζn n s)).re-(wPot ((z₀.re:ℂ)+(y:ℂ)*I)).re) +
        (n:ℝ)*((wPot ((z₀.re:ℂ)+(y:ℂ)*I)).re-(wPot z₀).re) +
        (z262 n (ζn n s)).re) ≤ Real.exp (64+-|s| / 10):=by
      refine Real.exp_le_exp.mpr ?_
      have:=mul_le_mul_of_nonneg_left hglob_bd hn_pos.le
      linarith
     rw [Real.exp_add 64] at hle_exp
     nlinarith [Real.exp_pos 64,Real.exp_pos (-(s^2)/280)]
   rw [norm_mul,norm_mul,Complex.norm_exp]
   have h12:=mul_le_mul hp_bd hcos_bd (norm_nonneg _) (by positivity)
   calc
    ‖z182 (ζn n s)‖*‖1+Complex.exp (-2*I*(Real.pi:ℂ)*(n:ℂ)*ζn n s)‖ *
      Real.exp (((n:ℂ)*(wPot (ζn n s)-wPot z₀)+z262 n (ζn n s)).re)
     ≤ (‖z180‖*12*2)*(Real.exp 64*(Real.exp (-(s^2)/280)+Real.exp (-|s| / 10))):=
      mul_le_mul h12 hexp_main (Real.exp_pos _).le (by positivity)
    _=Cdom*(Real.exp (-(s^2)/280)+Real.exp (-|s| / 10)):=by dsimp only [Cdom];ring
  ·
   simp only [fn,Set.indicator_of_notMem (show s∉Set.Iic _ from hs),norm_zero]
   have:0 ≤ Cdom:=by dsimp only [Cdom];positivity
   exact mul_nonneg this (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
 let fLim:ℝ→ ℂ:=fun s=>z182 z₀*Complex.exp (-(z53 z₀/2)*(s:ℂ)^2)
 have hpt_lim:∀ s:ℝ,Tendsto (fun n:ℕ=>fn n s) atTop (𝓝 (fLim s)):=by
  intro s
  have hinv_sq:Tendsto (fun n:ℕ=>(1:ℝ)/Real.sqrt (n:ℝ)) atTop (𝓝 0):=by
   have h:=tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
   exact h.congr fun n=>by simp [Function.comp_def,one_div]
  have hζ_lim:Tendsto (fun n:ℕ=>ζn n s) atTop (𝓝 z₀):=by
   have hx_lim:Tendsto x atTop (𝓝 z₀.re):=by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm' (a:=fun n:ℕ=>1/(2*(n:ℝ))) ?_ ?_
    ·
     filter_upwards [eventually_ge_atTop 1] with n hn
     simpa [Real.norm_eq_abs] using hx_diff n hn
    ·
     have h:=(tendsto_const_nhds (x:=(1/2:ℝ))).mul
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
     rw [mul_zero] at h
     exact h.congr fun n=>by simp only [Function.comp_def];ring
   have hy_lim:Tendsto (fun n:ℕ=>z₀.im+s/Real.sqrt (n:ℝ)) atTop (𝓝 z₀.im):=by
    have hs0:Tendsto (fun n:ℕ=>s/Real.sqrt (n:ℝ)) atTop (𝓝 0):=by
     have h:=hinv_sq.const_mul s
     rw [mul_zero] at h
     exact h.congr fun n=>by ring
    simpa using tendsto_const_nhds.add hs0
   have hcomb:=((Complex.continuous_ofReal.tendsto _).comp hx_lim).add
    (((Complex.continuous_ofReal.tendsto _).comp hy_lim).mul_const I)
   simpa [ζn,Function.comp_def,Complex.re_add_im] using hcomb
  have hp_lim:Tendsto (fun n:ℕ=>z182 (ζn n s)) atTop (𝓝 (z182 z₀)):=
   (z50 (by linarith [hz₀_re_bd.1]) (by linarith [hz₀_re_bd.2])).tendsto.comp hζ_lim
  have hcos_lim:Tendsto (fun n:ℕ=>1+Complex.exp (-2*I*(Real.pi:ℂ)*(n:ℂ)*ζn n s))
    atTop (𝓝 1):=by
   have hexp0:Tendsto (fun n:ℕ=>Complex.exp (-2*I*(Real.pi:ℂ)*(n:ℂ)*ζn n s))
     atTop (𝓝 0):=by
    refine squeeze_zero_norm' (a:=fun n:ℕ=>Real.exp (-(n:ℝ))) ?_ ?_
    ·
     obtain ⟨N0,hN0⟩:=exists_nat_gt (|s|^2)
     filter_upwards [eventually_ge_atTop (max N0 1)] with n hn
     have hn1:1 ≤ n:=le_trans (le_max_right _ _) hn
     have hsqn_pos:0< Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn1)
     have hs_div:|s| / Real.sqrt (n:ℝ) ≤ 1:=by
      rw [div_le_one hsqn_pos]
      have h1':|s|^2< (n:ℝ):=lt_of_lt_of_le hN0 (Nat.cast_le.mpr (le_trans (le_max_left _ _) hn))
      have hsq:|s|^2 ≤ (Real.sqrt (n:ℝ))^2:=by rw [Real.sq_sqrt (Nat.cast_nonneg n)];exact h1'.le
      nlinarith [abs_nonneg s,Real.sqrt_nonneg (n:ℝ)]
     have hy_le:z₀.im+s/Real.sqrt (n:ℝ) ≤ -1:=by
      have:=(le_abs_self (s/Real.sqrt (n:ℝ)))
      rw [abs_div,abs_of_pos hsqn_pos] at this
      linarith [hz₀_im_bd.2]
     rw [Complex.norm_exp]
     have hre_e:(-2*I*(Real.pi:ℂ)*(n:ℂ)*ζn n s).re =
       2*Real.pi*(n:ℝ)*(z₀.im+s/Real.sqrt (n:ℝ)):=by
      rw [show -2*I*(Real.pi:ℂ)*(n:ℂ)*ζn n s =
        (((2*Real.pi*(n:ℝ):ℝ):ℂ))*(-I*ζn n s) by push_cast;ring,
       Complex.re_ofReal_mul]
      simp [ζn]
     rw [hre_e]
     refine Real.exp_le_exp.mpr ?_
     calc
      2*Real.pi*(n:ℝ)*(z₀.im+s/Real.sqrt (n:ℝ))
       ≤ 2*Real.pi*(n:ℝ)*(-1):=mul_le_mul_of_nonneg_left hy_le (by positivity)
      _ ≤ -(n:ℝ):=by nlinarith [Real.two_le_pi,Nat.cast_nonneg (α:=ℝ) n]
    ·
     exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
   simpa using tendsto_const_nhds.add hexp0
  have hrem_lim:Tendsto (fun n:ℕ=>z262 n (ζn n s)) atTop (𝓝 0):=by
   refine squeeze_zero_norm' (a:=fun n:ℕ=>200/(n:ℝ)) ?_ ?_
   ·
    filter_upwards [eventually_ge_atTop 50] with n hn
    have hxs:=hx_strip n hn
    exact z145 hrem_le (n:=n) (by omega) (by simp [ζn];exact hxs.1) (by simp [ζn];exact hxs.2)
   ·
    have h:=(tendsto_const_nhds (x:=(200:ℝ))).mul
     (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    rw [mul_zero] at h
    exact h.congr fun n=>by simp only [Function.comp_def];ring
  have hquad_lim:Tendsto (fun n:ℕ=>(n:ℂ)*(wPot (ζn n s)-wPot z₀)) atTop
    (𝓝 (-(z53 z₀/2)*(s:ℂ)^2)):=by
   rw [tendsto_iff_norm_sub_tendsto_zero]
   refine squeeze_zero_norm' (a:=fun n:ℕ=>(1+2 * |s|+2*(1+|s|)^3)/Real.sqrt (n:ℝ)) ?_ ?_
   ·
    obtain ⟨N0,hN0⟩:=exists_nat_gt ((20*(1+|s|))^2)
    filter_upwards [eventually_ge_atTop (max N0 50)] with n hn
    have hn50:50 ≤ n:=le_trans (le_max_right _ _) hn
    have hn_pos:(0:ℝ)< n:=Nat.cast_pos.mpr (by omega)
    have hsqn_pos:0< Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr hn_pos
    have hsqn_ge:20*(1+|s|) ≤ Real.sqrt (n:ℝ):=by
     have h1':(20*(1+|s|))^2< (n:ℝ):=
      lt_of_lt_of_le hN0 (Nat.cast_le.mpr (le_trans (le_max_left _ _) hn))
     have h2':(20*(1+|s|))^2 ≤ (Real.sqrt (n:ℝ))^2:=by
      rw [Real.sq_sqrt hn_pos.le];exact h1'.le
     nlinarith [abs_nonneg s,Real.sqrt_nonneg (n:ℝ)]
    have hsqn_ge1:1 ≤ Real.sqrt (n:ℝ):=by linarith [abs_nonneg s]
    set dx:ℝ:=x n-z₀.re
    set dy:ℝ:=s/Real.sqrt (n:ℝ)
    set h:ℂ:=(dx:ℂ)+(dy:ℂ)*I
    have hζ_eq:ζn n s=z₀+h:=by
     calc
      ζn n s=(x n:ℂ)+((z₀.im+s/Real.sqrt (n:ℝ):ℝ):ℂ)*I:=rfl
      _=((z₀.re:ℂ)+(z₀.im:ℂ)*I)+h:=by dsimp only [h,dx,dy];push_cast;ring
      _=z₀+h:=by rw [Complex.re_add_im]
    have hdx:|dx| ≤ 1/(2*(n:ℝ)):=hx_diff n (by omega)
    have hh_bd:‖h‖ ≤ (1+|s|)/Real.sqrt (n:ℝ):=by
     have h1':‖h‖ ≤ |dx|+|dy|:=by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,
       Real.norm_eq_abs,Real.norm_eq_abs]
     have hdx_sq:|dx| ≤ 1/Real.sqrt (n:ℝ):=by
      refine hdx.trans ?_
      have hle:Real.sqrt (n:ℝ) ≤ 2*(n:ℝ):=by
       have:(n:ℝ)=Real.sqrt (n:ℝ)*Real.sqrt (n:ℝ):=(Real.mul_self_sqrt hn_pos.le).symm
       nlinarith
      exact div_le_div_of_nonneg_left zero_le_one hsqn_pos hle
     have hdy_eq:|dy|=|s| / Real.sqrt (n:ℝ):=by
      dsimp only [dy];rw [abs_div,abs_of_pos hsqn_pos]
     rw [add_div];linarith
    have hh10:‖h‖ ≤ 1/10:=by
     refine hh_bd.trans ?_
     rw [div_le_iff₀ hsqn_pos];linarith [abs_nonneg s]
    have htay:=z146 hdw hd2w hd3w (by linarith [hz₀_re_bd.1])
     (by linarith [hz₀_re_bd.2]) hdw0 hh10
    rw [← hζ_eq] at htay
    have hsplit:(n:ℂ)*(wPot (ζn n s)-wPot z₀)-(-(z53 z₀/2)*(s:ℂ)^2) =
      (n:ℂ)*(wPot (ζn n s)-wPot z₀-(1/2:ℂ)*z53 z₀*h^2) +
      (1/2:ℂ)*z53 z₀*((n:ℂ)*h^2+(s:ℂ)^2):=by ring
    rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),hsplit]
    have hterm1:‖(n:ℂ)*(wPot (ζn n s)-wPot z₀-(1/2:ℂ)*z53 z₀*h^2)‖ ≤
      2*(1+|s|)^3/Real.sqrt (n:ℝ):=by
     rw [norm_mul,Complex.norm_natCast]
     calc
      (n:ℝ)*‖wPot (ζn n s)-wPot z₀-(1/2:ℂ)*z53 z₀*h^2‖
       ≤ (n:ℝ)*(2*‖h‖^3):=mul_le_mul_of_nonneg_left htay hn_pos.le
      _ ≤ (n:ℝ)*(2*((1+|s|)/Real.sqrt (n:ℝ))^3):=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
         (pow_le_pow_left₀ (norm_nonneg h) hh_bd 3) (by norm_num)) hn_pos.le
      _=2*(1+|s|)^3/Real.sqrt (n:ℝ):=by
        rw [div_pow,show (Real.sqrt (n:ℝ))^3=(Real.sqrt (n:ℝ))^2*Real.sqrt (n:ℝ) by ring,
         Real.sq_sqrt hn_pos.le]
        field_simp [hn_pos.ne',hsqn_pos.ne']
    have hterm2:‖(1/2:ℂ)*z53 z₀*((n:ℂ)*h^2+(s:ℂ)^2)‖ ≤
      (1+2 * |s|)/Real.sqrt (n:ℝ):=by
     have hnh2:(n:ℂ)*h^2+(s:ℂ)^2 =
       (((n:ℝ)*dx^2:ℝ):ℂ)+(((2*(n:ℝ)*dx*dy:ℝ):ℂ))*I:=by
      have hndy2:(n:ℂ)*(dy:ℂ)^2=(s:ℂ)^2:=by
       dsimp only [dy]
       rw [show (n:ℂ)=((n:ℝ):ℂ) by norm_cast,← Complex.ofReal_pow,← Complex.ofReal_mul,
        div_pow,Real.sq_sqrt hn_pos.le,mul_div_cancel₀ _ hn_pos.ne']
       push_cast;rfl
      dsimp only [h]
      calc
       (n:ℂ)*((dx:ℂ)+(dy:ℂ)*I)^2+(s:ℂ)^2
        = (n:ℂ)*(dx:ℂ)^2+2*(n:ℂ)*(dx:ℂ)*(dy:ℂ)*I -
          (n:ℂ)*(dy:ℂ)^2+(s:ℂ)^2:=by ring_nf;rw [Complex.I_sq];ring
       _=_:=by rw [hndy2];push_cast;ring
     rw [hnh2,norm_mul,norm_mul,norm_div,norm_one,Complex.norm_ofNat]
     have hpart1:|(n:ℝ)*dx^2| ≤ 1/Real.sqrt (n:ℝ):=by
      rw [abs_mul,abs_of_pos hn_pos,abs_pow]
      have hdx2:|dx|^2 ≤ (1/(2*(n:ℝ)))^2:=pow_le_pow_left₀ (abs_nonneg _) hdx 2
      calc
       (n:ℝ) * |dx|^2 ≤ (n:ℝ)*(1/(2*(n:ℝ)))^2:=
         mul_le_mul_of_nonneg_left hdx2 hn_pos.le
       _=1/(4*(n:ℝ)):=by field_simp [hn_pos.ne'];ring
       _ ≤ 1/Real.sqrt (n:ℝ):=by
         refine div_le_div_of_nonneg_left zero_le_one hsqn_pos ?_
         have:(n:ℝ)=Real.sqrt (n:ℝ)*Real.sqrt (n:ℝ):=(Real.mul_self_sqrt hn_pos.le).symm
         nlinarith
     have hpart2:|2*(n:ℝ)*dx*dy| ≤ |s| / Real.sqrt (n:ℝ):=by
      rw [abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num:(0:ℝ)< 2),abs_of_pos hn_pos]
      have hdy_eq:|dy|=|s| / Real.sqrt (n:ℝ):=by dsimp only [dy];rw [abs_div,abs_of_pos hsqn_pos]
      rw [hdy_eq]
      calc
       2*(n:ℝ) * |dx| * (|s| / Real.sqrt (n:ℝ))
        ≤ 2*(n:ℝ)*(1/(2*(n:ℝ)))*(|s| / Real.sqrt (n:ℝ)):=
         mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdx (by positivity)) (by positivity)
       _=|s| / Real.sqrt (n:ℝ):=by field_simp [hn_pos.ne']
     have hsum_norm:‖(((n:ℝ)*dx^2:ℝ):ℂ)+(((2*(n:ℝ)*dx*dy:ℝ):ℂ))*I‖ ≤
       (1+2 * |s|)/Real.sqrt (n:ℝ):=by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real,norm_mul (((2*(n:ℝ)*dx*dy:ℝ):ℂ)),Complex.norm_real,
       Complex.norm_I,mul_one,Real.norm_eq_abs,Real.norm_eq_abs]
      rw [add_div]
      have h1s:|s| / Real.sqrt (n:ℝ) ≤ 2 * |s| / Real.sqrt (n:ℝ):=
       div_le_div_of_nonneg_right (by linarith [abs_nonneg s]) hsqn_pos.le
      linarith
     calc
      (1/2:ℝ)*‖z53 z₀‖*‖(((n:ℝ)*dx^2:ℝ):ℂ)+(((2*(n:ℝ)*dx*dy:ℝ):ℂ))*I‖
       ≤ 1*((1+2 * |s|)/Real.sqrt (n:ℝ)):=by
        have hhalf:(1/2:ℝ)*‖z53 z₀‖ ≤ 1:=by linarith
        exact mul_le_mul hhalf hsum_norm (norm_nonneg _) (by norm_num)
      _=_:=one_mul _
    refine (norm_add_le _ _).trans ?_
    have htot:(1+2 * |s|)/Real.sqrt (n:ℝ)+2*(1+|s|)^3/Real.sqrt (n:ℝ) =
      (1+2 * |s|+2*(1+|s|)^3)/Real.sqrt (n:ℝ):=by ring
    linarith
   ·
    have h:=hinv_sq.const_mul (1+2 * |s|+2*(1+|s|)^3)
    rw [mul_zero] at h
    exact h.congr fun n=>by ring
  have hexp_lim:Tendsto (fun n:ℕ =>
     Complex.exp ((n:ℂ)*(wPot (ζn n s)-wPot z₀)+z262 n (ζn n s)))
    atTop (𝓝 (Complex.exp (-(z53 z₀/2)*(s:ℂ)^2))):=by
   have hsum:=hquad_lim.add hrem_lim
   rw [add_zero] at hsum
   exact (Complex.continuous_exp.tendsto _).comp hsum
  have hprod_lim:Tendsto (fun n:ℕ =>
     z182 (ζn n s) *
      (1+Complex.exp (-2*I*(Real.pi:ℂ)*(n:ℂ)*ζn n s)) *
      Complex.exp ((n:ℂ)*(wPot (ζn n s)-wPot z₀)+z262 n (ζn n s)))
    atTop (𝓝 (fLim s)):=by
   have h:=(hp_lim.mul hcos_lim).mul hexp_lim
   simpa [fLim] using h
  refine hprod_lim.congr' ?_
  obtain ⟨N0,hN0⟩:=exists_nat_gt ((max s 0)^2)
  filter_upwards [eventually_ge_atTop (max N0 1)] with n hn
  have hs_in:s ≤ -Real.sqrt (n:ℝ)*z₀.im:=by
   have hsq:max s 0 ≤ Real.sqrt (n:ℝ):=by
    have h1':(max s 0)^2< (n:ℝ):=
     lt_of_lt_of_le hN0 (Nat.cast_le.mpr (le_trans (le_max_left _ _) hn))
    have h2':(max s 0)^2 ≤ (Real.sqrt (n:ℝ))^2:=by
     rw [Real.sq_sqrt (Nat.cast_nonneg n)];exact h1'.le
    nlinarith [le_max_right s 0,Real.sqrt_nonneg (n:ℝ)]
   have hle:s ≤ Real.sqrt (n:ℝ):=(le_max_left s 0).trans hsq
   nlinarith [hz₀_im_bd.2,Real.sqrt_nonneg (n:ℝ)]
  dsimp only [fn]
  rw [Set.indicator_of_mem (Set.mem_Iic.mpr hs_in)]
 have hmeas:∀ n:ℕ,AEStronglyMeasurable (fn (n+50)) volume:=by
  intro n
  set m:ℕ:=n+50
  have hm1:1 ≤ m:=by omega
  have hm50:50 ≤ m:=by omega
  have hm_pos:(0:ℝ)< m:=Nat.cast_pos.mpr hm1
  have hsq_pos:0< Real.sqrt (m:ℝ):=Real.sqrt_pos.mpr hm_pos
  have hms:=hx_strip m hm50
  have hint_g:Integrable (fun y:ℝ=>Z4.z88 m ((M m:ℂ)+1/2+(y:ℂ)*I)):=
   (hF_vert hm1 (hM_le m)).1
  have hint_ind:Integrable (Set.indicator (Set.Iic (0:ℝ))
    (fun y:ℝ=>Z4.z88 m ((M m:ℂ)+1/2+(y:ℂ)*I))):=
   hint_g.indicator measurableSet_Iic
  have hint_shift:Integrable (fun s:ℝ =>
    Set.indicator (Set.Iic (0:ℝ))
     (fun y:ℝ=>Z4.z88 m ((M m:ℂ)+1/2+(y:ℂ)*I))
     ((m:ℝ)*z₀.im+Real.sqrt (m:ℝ)*s)):=
   (hint_ind.comp_add_left ((m:ℝ)*z₀.im)).comp_mul_left' hsq_pos.ne'
  let c:ℂ:=((m:ℂ)^7)⁻¹*Complex.exp ((m:ℂ)*wPot z₀)
  have hc_ne:c≠0:=mul_ne_zero (inv_ne_zero (pow_ne_zero 7 (Nat.cast_ne_zero.mpr (by omega))))
   (Complex.exp_ne_zero _)
  have hpt_eq:∀ s:ℝ,fn m s=c⁻¹ *
    Set.indicator (Set.Iic (0:ℝ))
     (fun y:ℝ=>Z4.z88 m ((M m:ℂ)+1/2+(y:ℂ)*I))
     ((m:ℝ)*z₀.im+Real.sqrt (m:ℝ)*s):=by
   intro s
   have hiff:(m:ℝ)*z₀.im+Real.sqrt (m:ℝ)*s ≤ 0↔s ≤ -Real.sqrt (m:ℝ)*z₀.im:=by
    have hsq:Real.sqrt (m:ℝ)*Real.sqrt (m:ℝ)=(m:ℝ):=Real.mul_self_sqrt hm_pos.le
    constructor <;> intro hle
    ·
     have:Real.sqrt (m:ℝ)*s ≤ Real.sqrt (m:ℝ)*(-Real.sqrt (m:ℝ)*z₀.im):=by nlinarith [hsq]
     exact le_of_mul_le_mul_left this hsq_pos
    ·
     have:=mul_le_mul_of_nonneg_left hle hsq_pos.le
     nlinarith [hsq]
   by_cases hs:s ≤ -Real.sqrt (m:ℝ)*z₀.im
   ·
    have hy0:(m:ℝ)*z₀.im+Real.sqrt (m:ℝ)*s ≤ 0:=hiff.mpr hs
    dsimp only [fn]
    rw [Set.indicator_of_mem (Set.mem_Iic.mpr hs),Set.indicator_of_mem (Set.mem_Iic.mpr hy0)]
    have harg:(M m:ℂ)+1/2+(((m:ℝ)*z₀.im+Real.sqrt (m:ℝ)*s:ℝ):ℂ)*I =
      (m:ℂ)*ζn m s:=by
     dsimp only [ζn,x]
     have hsq_eq:(m:ℂ)*(((s/Real.sqrt (m:ℝ):ℝ):ℂ))=((Real.sqrt (m:ℝ)*s:ℝ):ℂ):=by
      rw [show (m:ℂ)=((m:ℝ):ℂ) by norm_cast,← Complex.ofReal_mul]
      congr 1
      calc
       (m:ℝ)*(s/Real.sqrt (m:ℝ))
        = (Real.sqrt (m:ℝ)*Real.sqrt (m:ℝ))*(s/Real.sqrt (m:ℝ)):=by
         rw [Real.mul_self_sqrt hm_pos.le]
       _=Real.sqrt (m:ℝ)*s:=by field_simp [hsq_pos.ne']
     have hx_eq:(m:ℂ)*((((M m:ℝ)+1/2)/(m:ℝ):ℝ):ℂ)=(M m:ℂ)+1/2:=by
      rw [show (m:ℂ)=((m:ℝ):ℂ) by norm_cast,← Complex.ofReal_mul,
       mul_div_cancel₀ _ hm_pos.ne']
      push_cast;rfl
     calc
      (M m:ℂ)+1/2+(((m:ℝ)*z₀.im+Real.sqrt (m:ℝ)*s:ℝ):ℂ)*I
       = (m:ℂ)*((((M m:ℝ)+1/2)/(m:ℝ):ℝ):ℂ) +
         ((m:ℂ)*(z₀.im:ℂ)+(m:ℂ)*((s/Real.sqrt (m:ℝ):ℝ):ℂ))*I:=by
        rw [hx_eq,hsq_eq];push_cast;ring
      _=(m:ℂ)*(((((M m:ℝ)+1/2)/(m:ℝ):ℝ):ℂ) +
         ((z₀.im+s/Real.sqrt (m:ℝ):ℝ):ℂ)*I):=by push_cast;ring
    rw [harg,z90 hlog_mul hstirling hfac_stirling hm1
     (by simp [ζn];exact hms.1) (by simp [ζn];exact hms.2)]
    have hexp_split:Complex.exp ((m:ℂ)*wPot (ζn m s)+z262 m (ζn m s)) =
      Complex.exp ((m:ℂ)*wPot z₀) *
       Complex.exp ((m:ℂ)*(wPot (ζn m s)-wPot z₀)+z262 m (ζn m s)):=by
     rw [← Complex.exp_add];congr 1;ring
    rw [hexp_split]
    have hmul_c:((m:ℂ)^7)⁻¹*z182 (ζn m s) *
       (1+Complex.exp (-2*I*(Real.pi:ℂ)*(m:ℂ)*ζn m s)) *
       (Complex.exp ((m:ℂ)*wPot z₀) *
        Complex.exp ((m:ℂ)*(wPot (ζn m s)-wPot z₀)+z262 m (ζn m s))) =
      c*(z182 (ζn m s) *
       (1+Complex.exp (-2*I*(Real.pi:ℂ)*(m:ℂ)*ζn m s)) *
       Complex.exp ((m:ℂ)*(wPot (ζn m s)-wPot z₀)+z262 m (ζn m s))):=by
     dsimp only [c];ring
    rw [hmul_c,← mul_assoc,inv_mul_cancel₀ hc_ne,one_mul]
   ·
    have hy0:¬ ((m:ℝ)*z₀.im+Real.sqrt (m:ℝ)*s ≤ 0):=mt hiff.mp hs
    dsimp only [fn]
    rw [Set.indicator_of_notMem (Set.mem_Iic.not.mpr hs),
     Set.indicator_of_notMem (Set.mem_Iic.not.mpr hy0),mul_zero]
  exact (hint_shift.const_mul c⁻¹).aestronglyMeasurable.congr (Filter.Eventually.of_forall fun s=>(hpt_eq s).symm)
 have hJ_lim:Tendsto J atTop (𝓝 (∫ s:ℝ,fLim s)):=by
  rw [← tendsto_add_atTop_iff_nat 50]
  exact tendsto_integral_of_dominated_convergence
   (fun s=>Cdom*(Real.exp (-(s^2)/280)+Real.exp (-|s| / 10)))
   hmeas (z106 Cdom)
   (fun n=>Filter.Eventually.of_forall fun s=>hdom_bd (n+50) (by omega) s)
   (Filter.Eventually.of_forall fun s=>(hpt_lim s).comp (tendsto_add_atTop_nat 50))
 set L₀:ℂ:=∫ s:ℝ,fLim s
 have hL0_eq:L₀=z182 z₀*(((Real.pi:ℂ)/(z53 z₀/2))^(1/2:ℂ)):=by
  dsimp only [L₀,fLim]
  rw [integral_const_mul]
  congr 1
  have hb_re:0< (z53 z₀/2).re:=by
   rw [Complex.div_ofNat_re];linarith
  exact integral_gaussian_complex hb_re
 have hL0_ne:L₀≠0:=by
  rw [hL0_eq]
  refine mul_ne_zero (z183 (by linarith [hz₀_re_bd.1])) ?_
  have hdiv_ne:(Real.pi:ℂ)/(z53 z₀/2)≠0:=by
   refine div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) ?_
   intro h0
   have:=congr_arg Complex.re h0
   rw [Complex.div_ofNat_re,Complex.zero_re] at this
   linarith
  rw [Complex.cpow_def_of_ne_zero hdiv_ne]
  exact Complex.exp_ne_zero _
 constructor
 ·
  refine ⟨‖L₀‖+1,by positivity,?_⟩
  have hJ_bd:∀ᶠ n:ℕ in atTop,‖J n‖ ≤ ‖L₀‖+1:=by
   have h1':=(Metric.tendsto_atTop.mp hJ_lim) 1 zero_lt_one
   obtain ⟨N0,hN0⟩:=h1'
   filter_upwards [eventually_ge_atTop N0] with n hn
   have hd:‖J n-L₀‖ < 1:=by simpa [dist_eq_norm] using hN0 n hn
   have htri:=norm_sub_norm_le (J n) L₀
   linarith
  filter_upwards [eventually_ge_atTop 50,hJ_bd] with n hn hJn
  rw [hF_eq_J n hn,abs_mul,abs_mul,abs_neg,abs_of_pos (by positivity),
   abs_of_pos (Real.exp_pos _)]
  have hpref_le:Real.sqrt (n:ℝ)/(Real.pi*(n:ℝ)^7) ≤ 1:=by
   have hn1:(1:ℝ) ≤ n:=by exact_mod_cast (show 1 ≤ n by omega)
   have hsq:Real.sqrt (n:ℝ) ≤ (n:ℝ):=by
    have:(Real.sqrt (n:ℝ))^2 ≤ (n:ℝ)^2:=by rw [Real.sq_sqrt (by linarith)];nlinarith
    nlinarith [Real.sqrt_nonneg (n:ℝ)]
   have hpow:(n:ℝ) ≤ Real.pi*(n:ℝ)^7:=by
    have h1':(n:ℝ) ≤ (n:ℝ)^7:=le_self_pow₀ hn1 (by norm_num)
    nlinarith [Real.two_le_pi]
   exact (div_le_one (by positivity)).mpr (hsq.trans hpow)
  have hre_le:|(Complex.exp (I*(((n:ℝ)*(wPot z₀).im:ℝ):ℂ))*J n).re| ≤ ‖L₀‖+1:=by
   refine (Complex.abs_re_le_norm _).trans ?_
   rw [norm_mul,Complex.norm_exp]
   have hre0:(I*(((n:ℝ)*(wPot z₀).im:ℝ):ℂ)).re=0:=by simp
   rw [hre0,Real.exp_zero,one_mul]
   exact hJn
  have hexp_le:Real.exp ((n:ℝ)*(wPot z₀).re) ≤ Real.exp (-227.4*(n:ℝ)):=by
   refine Real.exp_le_exp.mpr ?_
   nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  calc
   Real.sqrt (n:ℝ)/(Real.pi*(n:ℝ)^7)*Real.exp ((n:ℝ)*(wPot z₀).re) *
     |(Complex.exp (I*(((n:ℝ)*(wPot z₀).im:ℝ):ℂ))*J n).re|
    ≤ 1*Real.exp (-227.4*(n:ℝ))*(‖L₀‖+1):=by
     refine mul_le_mul (mul_le_mul hpref_le hexp_le (Real.exp_pos _).le zero_le_one)
      hre_le (abs_nonneg _) (by positivity)
   _=(‖L₀‖+1)*Real.exp (-227.4*(n:ℝ)):=by ring
 ·
  set r:ℝ:=‖L₀‖
  have hr:0< r:=norm_pos_iff.mpr hL0_ne
  obtain ⟨N0,hN0⟩:=Metric.tendsto_atTop.mp hJ_lim (r/16) (by positivity)
  filter_upwards [eventually_ge_atTop (max N0 50)] with n hn
  by_contra hboth
  push Not at hboth
  obtain ⟨hFn,hFn1⟩:=hboth
  have hn50:50 ≤ n:=le_trans (le_max_right _ _) hn
  have hnN0:N0 ≤ n:=le_trans (le_max_left _ _) hn
  have hre_n:(Complex.exp (I*(((n:ℝ)*(wPot z₀).im:ℝ):ℂ))*J n).re=0:=by
   rw [hF_eq_J n hn50] at hFn
   have hc_ne:-(Real.sqrt (n:ℝ)/(Real.pi*(n:ℝ)^7))*Real.exp ((n:ℝ)*(wPot z₀).re)≠0:=by
    have:0< Real.sqrt (n:ℝ)/(Real.pi*(n:ℝ)^7)*Real.exp ((n:ℝ)*(wPot z₀).re):=by
     have:(0:ℝ)< n:=Nat.cast_pos.mpr (by omega)
     positivity
    linarith
   exact (mul_eq_zero.mp hFn).resolve_left hc_ne
  have hre_n1:(Complex.exp (I*((((n+1:ℕ):ℝ)*(wPot z₀).im:ℝ):ℂ))*J (n+1)).re=0:=by
   rw [hF_eq_J (n+1) (by omega)] at hFn1
   have hc_ne:-(Real.sqrt ((n+1:ℕ):ℝ)/(Real.pi*((n+1:ℕ):ℝ)^7)) *
     Real.exp (((n+1:ℕ):ℝ)*(wPot z₀).re)≠0:=by
    have:0< Real.sqrt ((n+1:ℕ):ℝ)/(Real.pi*((n+1:ℕ):ℝ)^7) *
      Real.exp (((n+1:ℕ):ℝ)*(wPot z₀).re):=by positivity
    linarith
   exact (mul_eq_zero.mp hFn1).resolve_left hc_ne
  set θ : ℝ:=(wPot z₀).im
  set w:ℂ:=Complex.exp (I*(((n:ℝ)*θ : ℝ):ℂ))*L₀
  have hw_norm:‖w‖=r:=by
   dsimp only [w,r]
   rw [norm_mul,Complex.norm_exp]
   have:(I*(((n:ℝ)*θ : ℝ):ℂ)).re=0:=by simp
   rw [this,Real.exp_zero,one_mul]
  have hw_re_lt:|w.re| < r/16:=by
   have hdiff:w.re=(Complex.exp (I*(((n:ℝ)*θ : ℝ):ℂ))*(L₀-J n)).re:=by
    rw [mul_sub,Complex.sub_re,hre_n,sub_zero]
   rw [hdiff]
   calc
    |(Complex.exp (I*(((n:ℝ)*θ : ℝ):ℂ))*(L₀-J n)).re|
     ≤ ‖Complex.exp (I*(((n:ℝ)*θ : ℝ):ℂ))*(L₀-J n)‖:=Complex.abs_re_le_norm _
    _=‖J n-L₀‖:=by
      rw [norm_mul,Complex.norm_exp,show (I*(((n:ℝ)*θ : ℝ):ℂ)).re=0 by simp,
       Real.exp_zero,one_mul,norm_sub_rev]
    _< r/16:=by simpa [dist_eq_norm] using hN0 n hnN0
  have hw_rot_lt:|(Complex.exp (I*(θ : ℂ))*w).re| < r/16:=by
   have hrot:Complex.exp (I*(θ : ℂ))*w =
     Complex.exp (I*((((n+1:ℕ):ℝ)*θ : ℝ):ℂ))*L₀:=by
    dsimp only [w]
    rw [← mul_assoc,← Complex.exp_add]
    congr 2;push_cast;ring
   have hdiff:(Complex.exp (I*(θ : ℂ))*w).re =
     (Complex.exp (I*((((n+1:ℕ):ℝ)*θ : ℝ):ℂ))*(L₀-J (n+1))).re:=by
    rw [hrot,mul_sub,Complex.sub_re,hre_n1,sub_zero]
   rw [hdiff]
   calc
    |(Complex.exp (I*((((n+1:ℕ):ℝ)*θ : ℝ):ℂ))*(L₀-J (n+1))).re|
     ≤ ‖Complex.exp (I*((((n+1:ℕ):ℝ)*θ : ℝ):ℂ))*(L₀-J (n+1))‖:=Complex.abs_re_le_norm _
    _=‖J (n+1)-L₀‖:=by
      rw [norm_mul,Complex.norm_exp,show (I*((((n+1:ℕ):ℝ)*θ : ℝ):ℂ)).re=0 by simp,
       Real.exp_zero,one_mul,norm_sub_rev]
    _< r/16:=by simpa [dist_eq_norm] using hN0 (n+1) (by omega)
  have hrot_re:(Complex.exp (I*(θ : ℂ))*w).re=Real.cos θ*w.re-Real.sin θ*w.im:=by
   rw [Complex.mul_re,show I*(θ : ℂ)=(θ : ℂ)*I by ring,Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  have hsin_im:|Real.sin θ| * |w.im| < r/8:=by
   have heq:Real.sin θ*w.im=Real.cos θ*w.re-(Complex.exp (I*(θ : ℂ))*w).re:=by
    linarith [hrot_re]
   calc
    |Real.sin θ| * |w.im|=|Real.sin θ*w.im|:=(abs_mul _ _).symm
    _=|Real.cos θ*w.re-(Complex.exp (I*(θ : ℂ))*w).re|:=by rw [heq]
    _ ≤ |Real.cos θ*w.re|+|(Complex.exp (I*(θ : ℂ))*w).re|:=abs_sub _ _
    _ ≤ |w.re|+|(Complex.exp (I*(θ : ℂ))*w).re|:=by
      rw [abs_mul]
      have hcos1:|Real.cos θ| ≤ 1:=Real.abs_cos_le_one θ
      nlinarith [abs_nonneg w.re]
    _< r/8:=by linarith
  have hw_im_lt:|w.im| < r/2:=by
   have:(1/4:ℝ) * |w.im| < r/8:=lt_of_le_of_lt (mul_le_mul_of_nonneg_right hw0_sin (abs_nonneg _)) hsin_im
   linarith
  have hsq_eq:r^2=w.re^2+w.im^2:=by
   rw [← hw_norm,Complex.sq_norm,Complex.normSq_apply];ring
  have hre_sq:w.re^2< (r/16)^2:=by
   rw [← sq_abs];exact sq_lt_sq' (by linarith [abs_nonneg w.re]) hw_re_lt
  have him_sq:w.im^2< (r/2)^2:=by
   rw [← sq_abs];exact sq_lt_sq' (by linarith [abs_nonneg w.im]) hw_im_lt
  nlinarith
end Laplace
end Z5
private theorem zudilin_irrationality_main :
  ({5,7,9,11} ∩ { a:ℂ | ∃ x:ℝ,Irrational x∧riemannZeta a=(x:ℂ) }).Nonempty:=by
 by_contra hne
 have hnot_irr:∀ k:ℕ,(k:ℂ)∈({5,7,9,11}:Set ℂ)→ 2 ≤ k →
   ¬ Irrational (Z4.z285 k):=by
  intro k hk hk2 hirr
  exact hne ⟨(k:ℂ),hk,Z4.z285 k,hirr,
   Z4.z251 hk2⟩
 have hrat_of:∀ x:ℝ,¬ Irrational x→ ∃ q:ℚ,(q:ℝ)=x:=by
  intro x hx
  unfold Irrational at hx
  push Not at hx
  exact hx
 obtain ⟨q5,hq5⟩:=hrat_of _ (hnot_irr 5 (by simp) (by omega))
 obtain ⟨q7,hq7⟩:=hrat_of _ (hnot_irr 7 (by simp) (by omega))
 obtain ⟨q9,hq9⟩:=hrat_of _ (hnot_irr 9 (by simp) (by omega))
 obtain ⟨q11,hq11⟩:=hrat_of _ (hnot_irr 11 (by simp) (by omega))
 let Q:ℕ:=q5.den*q7.den*q9.den*q11.den
 have hQ_pos:0< Q:=by
  have h5:=q5.den_pos;have h7:=q7.den_pos;have h9:=q9.den_pos;have h11:=q11.den_pos
  positivity
 have hQ_mul:∀ q:ℚ,q.den ∣ Q→ ∃ m:ℤ,(Q:ℝ)*(q:ℝ)=(m:ℝ):=by
  intro q hdvd
  rcases hdvd with ⟨c,hc⟩
  refine ⟨(c:ℤ)*q.num,?_⟩
  have hq:(q:ℝ)=(q.num:ℝ)/(q.den:ℝ):=by exact_mod_cast (Rat.num_div_den q).symm
  have hden:(q.den:ℝ)≠0:=Nat.cast_ne_zero.mpr q.den_pos.ne'
  rw [hc,hq];push_cast;field_simp [hden]
 obtain ⟨m5,hm5⟩:=hQ_mul q5 ⟨q7.den*q9.den*q11.den,by dsimp only [Q];ring⟩
 obtain ⟨m7,hm7⟩:=hQ_mul q7 ⟨q5.den*q9.den*q11.den,by dsimp only [Q];ring⟩
 obtain ⟨m9,hm9⟩:=hQ_mul q9 ⟨q5.den*q7.den*q11.den,by dsimp only [Q];ring⟩
 obtain ⟨m11,hm11⟩:=hQ_mul q11 ⟨q5.den*q7.den*q9.den,by dsimp only [Q];ring⟩
 let Phi:ℕ→ ℕ:=fun n=>∏ p∈Nat.primesLE (33*n),p^Z2.z168 n p
 have hPhi_pos:∀ n:ℕ,0< Phi n:=fun n =>
  Finset.prod_pos fun p hp=>pow_pos (Nat.mem_primesLE.mp hp).2.pos _
 have hone_le:∀ n:ℕ,1 ≤ n→ Z4.z3 n≠0 →
   (1:ℝ) ≤ (Q:ℝ)*((Z4.D_B n:ℝ)/(Phi n:ℝ)) * |Z4.z3 n|:=by
  intro n hn hFn
  obtain ⟨a0,a5,a7,a9,a11,hlin⟩:=Z4.z72
   Z2.z168
   (fun n' p hpos y hy0 hy1=>Z2.z173 n' p hpos hy0 hy1) hn
  let K:ℤ:=a5*m5+a7*m7+a9*m9+a11*m11-(Q:ℤ)*a0
  have hK_eq:(Q:ℝ)*((Z4.D_B n:ℝ)/(Phi n:ℝ))*Z4.z3 n=(K:ℝ):=by
   have h1:(Q:ℝ)*(((Z4.D_B n:ℝ)/(Phi n:ℝ))*Z4.z3 n) =
     (Q:ℝ)*((a5:ℝ)*Z4.z285 5+(a7:ℝ)*Z4.z285 7 +
      (a9:ℝ)*Z4.z285 9+(a11:ℝ)*Z4.z285 11-(a0:ℝ)):=by
    rw [hlin]
   rw [mul_assoc,h1,← hq5,← hq7,← hq9,← hq11]
   dsimp only [K];push_cast
   linear_combination (a5:ℝ)*hm5+(a7:ℝ)*hm7+(a9:ℝ)*hm9+(a11:ℝ)*hm11
  have hK_ne:K≠0:=by
   intro h0
   have hKr:(K:ℝ)=0:=by exact_mod_cast h0
   rw [hKr] at hK_eq
   have hQr:(Q:ℝ)≠0:=Nat.cast_ne_zero.mpr hQ_pos.ne'
   have hDBr:(Z4.D_B n:ℝ)≠0:=Nat.cast_ne_zero.mpr (Z4.z2 n).ne'
   have hPhir:(Phi n:ℝ)≠0:=Nat.cast_ne_zero.mpr (hPhi_pos n).ne'
   exact mul_ne_zero (mul_ne_zero hQr (div_ne_zero hDBr hPhir)) hFn hK_eq
  have hK_abs:(1:ℝ) ≤ |(K:ℝ)|:=by
   have h1:(1:ℤ) ≤ |K|:=Int.one_le_abs hK_ne
   exact_mod_cast h1
  rw [← hK_eq,abs_mul,abs_mul,abs_of_pos (Nat.cast_pos.mpr hQ_pos),
   abs_of_pos (div_pos (Nat.cast_pos.mpr (Z4.z2 n))
    (Nat.cast_pos.mpr (hPhi_pos n)))] at hK_abs
  exact hK_abs
 have hpsi_ev:=Z1.z246 (1/10000) (by norm_num)
 have hpsi_mul:∀ c:ℕ,0< c →
   ∀ᶠ n:ℕ in Filter.atTop,
    Real.log (Nat.lcmUpto (c*n):ℝ) ≤ (1+1/10000:ℝ)*((c:ℝ)*(n:ℝ)):=by
  intro c hc
  have ht:Filter.Tendsto (fun n:ℕ=>((c*n:ℕ):ℝ)) Filter.atTop Filter.atTop:=by
   have h1:Filter.Tendsto (fun n:ℕ=>(c:ℝ)*(n:ℝ)) Filter.atTop Filter.atTop:=
    Filter.Tendsto.const_mul_atTop (Nat.cast_pos.mpr hc) tendsto_natCast_atTop_atTop
   exact h1.congr fun n=>by push_cast;rfl
  filter_upwards [ht.eventually hpsi_ev] with n hn
  rw [← Chebyshev.psi_eq_log_lcmUpto]
  simpa [Nat.cast_mul] using hn
 have hlog_DB:∀ᶠ n:ℕ in Filter.atTop,
   Real.log (Z4.D_B n:ℝ) ≤ (40305/100:ℝ)*(n:ℝ):=by
  filter_upwards [hpsi_mul 35 (by omega),hpsi_mul 34 (by omega),hpsi_mul 33 (by omega)] with n h35 h34 h33
  have h35p:(Nat.lcmUpto (35*n):ℝ)≠0:=Nat.cast_ne_zero.mpr (Nat.lcmUpto_pos _).ne'
  have h34p:(Nat.lcmUpto (34*n):ℝ)≠0:=Nat.cast_ne_zero.mpr (Nat.lcmUpto_pos _).ne'
  have h33p:(Nat.lcmUpto (33*n):ℝ)≠0:=Nat.cast_ne_zero.mpr (Nat.lcmUpto_pos _).ne'
  have hlog_eq:Real.log (Z4.D_B n:ℝ) =
    3*Real.log (Nat.lcmUpto (35*n):ℝ)+Real.log (Nat.lcmUpto (34*n):ℝ) +
     8*Real.log (Nat.lcmUpto (33*n):ℝ):=by
   unfold Z4.D_B
   push_cast
   rw [Real.log_mul (mul_ne_zero (pow_ne_zero 3 h35p) h34p) (pow_ne_zero 8 h33p),
    Real.log_mul (pow_ne_zero 3 h35p) h34p,Real.log_pow,Real.log_pow]
   push_cast;ring
  rw [hlog_eq]
  nlinarith [Nat.cast_nonneg (α:=ℝ) n]
 have hlog_Phi:∀ᶠ n:ℕ in Filter.atTop,(176:ℝ)*(n:ℝ) ≤ Real.log (Phi n:ℝ):=by
  filter_upwards [Z2.z121 Z1.z269] with n hn
  have hlog_eq:Real.log (Phi n:ℝ) =
    ∑ p∈Nat.primesLE (33*n),(Z2.z168 n p:ℝ)*Real.log (p:ℝ):=by
   dsimp only [Phi]
   rw [Nat.cast_prod,Real.log_prod (fun p hp=>Nat.cast_ne_zero.mpr (pow_pos (Nat.mem_primesLE.mp hp).2.pos _).ne')]
   refine Finset.sum_congr rfl fun p _=>by rw [Nat.cast_pow,Real.log_pow]
  rw [hlog_eq];exact hn
 obtain ⟨⟨C,hC_pos,hF_bd⟩,hF_ne⟩:=Z5.z4
  Z5.z125
  Z5.z143
  Z5.z49
  Z5.z131
  Z5.z100
  Z5.z95
  Z5.z94
  Z5.z73
  Z5.z249
  Z5.z250
  (fun hn hM=>Z4.z7
   Z3.z115 hn hM)
 have hsmall_exp:∀ᶠ n:ℕ in Filter.atTop,
   (Q:ℝ)*C*Real.exp (-(35/100:ℝ)*(n:ℝ))< 1:=by
  have ht1:Filter.Tendsto (fun n:ℕ=>-(35/100:ℝ)*(n:ℝ)) Filter.atTop Filter.atBot:=
   Filter.Tendsto.const_mul_atTop_of_neg (by norm_num) tendsto_natCast_atTop_atTop
  have ht2:Filter.Tendsto (fun n:ℕ=>(Q:ℝ)*C*Real.exp (-(35/100:ℝ)*(n:ℝ)))
    Filter.atTop (nhds 0):=by
   simpa using (Real.tendsto_exp_atBot.comp ht1).const_mul ((Q:ℝ)*C)
  exact ht2.eventually (gt_mem_nhds zero_lt_one)
 have hgood:∀ᶠ n:ℕ in Filter.atTop,
   1 ≤ n ∧
   (Q:ℝ)*((Z4.D_B n:ℝ)/(Phi n:ℝ)) * |Z4.z3 n| < 1:=by
  filter_upwards [Filter.eventually_ge_atTop (1:ℕ),hlog_DB,hlog_Phi,hF_bd,hsmall_exp] with
   n hn hDB hPhi hF hexp
  refine ⟨hn,?_⟩
  have hDBp:(0:ℝ)< Z4.D_B n:=Nat.cast_pos.mpr (Z4.z2 n)
  have hPhip:(0:ℝ)< Phi n:=Nat.cast_pos.mpr (hPhi_pos n)
  have hratio:(Z4.D_B n:ℝ)/(Phi n:ℝ) ≤ Real.exp ((22705/100:ℝ)*(n:ℝ)):=by
   rw [← Real.exp_log hDBp,← Real.exp_log hPhip,← Real.exp_sub]
   exact Real.exp_le_exp.mpr (by linarith)
  have hprod_le:(Q:ℝ)*((Z4.D_B n:ℝ)/(Phi n:ℝ)) * |Z4.z3 n| ≤
    (Q:ℝ)*C*Real.exp (-(35/100:ℝ)*(n:ℝ)):=by
   calc
    (Q:ℝ)*((Z4.D_B n:ℝ)/(Phi n:ℝ)) * |Z4.z3 n|
     ≤ (Q:ℝ)*Real.exp ((22705/100:ℝ)*(n:ℝ))*(C*Real.exp (-227.4*(n:ℝ))):=by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg Q)) hF (abs_nonneg _) (by positivity)
    _=(Q:ℝ)*C*(Real.exp ((22705/100:ℝ)*(n:ℝ))*Real.exp (-227.4*(n:ℝ))):=by ring
    _=(Q:ℝ)*C*Real.exp (-(35/100:ℝ)*(n:ℝ)):=by
      rw [← Real.exp_add];congr 2;ring
  exact hprod_le.trans_lt hexp
 have hgood_succ:∀ᶠ n:ℕ in Filter.atTop,
   (1 ≤ n+1 ∧
    (Q:ℝ)*((Z4.D_B (n+1):ℝ)/(Phi (n+1):ℝ)) *
     |Z4.z3 (n+1)| < 1):=
  (Filter.tendsto_add_atTop_nat 1).eventually hgood
 obtain ⟨n,⟨hn1,hlt0⟩,⟨hn2,hlt1⟩,hne_or⟩:=(hgood.and (hgood_succ.and hF_ne)).exists
 rcases hne_or with h0 | h1
 ·
  linarith [hone_le n hn1 h0]
 ·
  linarith [hone_le (n+1) hn2 h1]

theorem OMA.solution : type_of% @RiemannZetaValues.exists_irrational_of_five_seven_nine_eleven := by
  exact zudilin_irrationality_main
