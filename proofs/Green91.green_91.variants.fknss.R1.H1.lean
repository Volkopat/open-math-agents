import OMAReductions.R_Green91_green_91_variants_fknss_R1
open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped BigOperators NNReal ENNReal
private abbrev R:=ℝ
namespace Green91FKNSS
def fpS:ℤ:=10000000
private abbrev S0:R:=(fpS:R)
private noncomputable abbrev N01:=gaussianReal 0 1
private noncomputable abbrev PI:R:=Real.pi
private abbrev HD (f:R → R) (f' x:R):=HasDerivAt f f' x
private lemma hdp (n:ℕ) (x:R):HasDerivAt (fun t:R=>t^n) (n*x^(n - 1)) x:=hasDerivAt_pow n x
private lemma hdi (x:R):HasDerivAt id 1 x:=hasDerivAt_id x
private lemma aon {a:R} (h:0 ≤ a):|a| = a:=abs_of_nonneg h
private lemma dld {a b c:R} (h:a ≤ b) (hc:0 ≤ c):a/c ≤ b/c:=div_le_div_of_nonneg_right h hc
private lemma mlL {a b c:R} (h:b ≤ c) (ha:0 ≤ a):a*b ≤ a*c:=mul_le_mul_of_nonneg_left h ha
private lemma mlR {a b c:R} (h:a ≤ b) (hc:0 ≤ c):a*c ≤ b*c:=mul_le_mul_of_nonneg_right h hc
private lemma mlN {a b c:R} (h:b ≤ c) (ha:a ≤ 0):a*c ≤ a*b:=mul_le_mul_of_nonpos_left h ha
noncomputable def pP (x:R):R :=
 (sqrt (2*PI))⁻¹*exp (-x^2/2)
noncomputable def pC (x:R):R :=
 (N01 (Set.Iic x)).toReal
lemma pPg (x:R) :
  pP x=gaussianPDFReal 0 1 x:=by
 simp [pP,gaussianPDFReal,sub_zero,NNReal.coe_one,mul_one,neg_div]
lemma pPp (x:R):0 < pP x:=by
 rw [pP]
 positivity
lemma pPn (x:R):0<=pP x :=
 (pPp x).le
lemma stdPhiPDF_even (x:R):pP (-x)=pP x:=by
 simp [pP]
lemma stdPhiPDF_le_inv_sqrt_two_pi (x:R) :
  pP x<=(sqrt (2*PI))⁻¹:=by
 rw [pP]
 have h1:exp (-x^2/2)<=1:=by
  rw [exp_le_one_iff]
  nlinarith
 have h2:0<=(sqrt (2*PI))⁻¹:=by positivity
 nlinarith
lemma stdPhiCDF_eq_integral (x:R) :
  pC x=∫ t in Set.Iic x,pP t:=by
 rw [pC,gaussianReal_apply_eq_integral (μ:=0) (v:=1) one_ne_zero (Set.Iic x)]
 simp only [pPg]
 exact ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic fun t _ =>
  gaussianPDFReal_nonneg 0 1 t)
lemma ipP:Integrable pP:=by
 have heq:pP=gaussianPDFReal 0 1:=funext pPg
 rw [heq]
 exact integrable_gaussianPDFReal (0:R) (1:NNReal)
lemma integral_stdPhiPDF_univ:∫ t:R,pP t=1:=by
 simp_rw [pPg]
 exact integral_gaussianPDFReal_eq_one 0 one_ne_zero
lemma integral_stdPhiPDF_Iic_zero:∫ t in Set.Iic (0:R),pP t=1/2:=by
 have h1:(∫ t in Set.Iic (0:R),pP t)+(∫ t in Set.Ioi (0:R),pP t)=1:=by
  rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
   ipP.integrableOn ipP.integrableOn,
   Set.Iic_union_Ioi,setIntegral_univ,integral_stdPhiPDF_univ]
 have h2:∫ t in Set.Ioi (0:R),pP t=∫ t in Set.Iic (0:R),pP t:=by
  have hcomp:∫ t in Set.Ioi (0:R),pP t=∫ t in Set.Iio (0:R),pP t:=by
   simp_rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Iio]
   rw [← MeasureTheory.integral_neg_eq_self (f:=Set.indicator (Set.Ioi (0:R)) pP)]
   congr 1
   ext t
   by_cases ht:t < 0
   .
    have hnt:0 < -t:=by linarith
    simp [Set.indicator,ht,hnt,stdPhiPDF_even]
   .
    have hnt:¬ (0 < -t):=by linarith
    simp [Set.indicator,ht,hnt]
  rw [hcomp]
  exact setIntegral_congr_set Iio_ae_eq_Iic
 linarith
lemma stdPhiCDF_zero:pC 0=1/2:=by
 rw [stdPhiCDF_eq_integral,integral_stdPhiPDF_Iic_zero]
lemma stdPhiCDF_eq_half_add_intervalIntegral (x:R) :
  pC x=1/2+∫ t in (0:R)..x,pP t:=by
 rw [stdPhiCDF_eq_integral,← integral_stdPhiPDF_Iic_zero]
 by_cases hx:0<=x
 .
  rw [intervalIntegral.integral_of_le hx]
  rw [← setIntegral_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
   ipP.integrableOn ipP.integrableOn,
   Set.Iic_union_Ioc_eq_Iic hx]
 .
  have hx':x < 0:=lt_of_not_ge hx
  rw [intervalIntegral.integral_symm,intervalIntegral.integral_of_le hx'.le]
  have hunion:=setIntegral_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
   (ipP.integrableOn (s:=Set.Iic x))
   (ipP.integrableOn (s:=Set.Ioc x 0))
  rw [Set.Iic_union_Ioc_eq_Iic hx'.le] at hunion
  linarith
lemma stdPhiCDF_neg (x:R):pC (-x)=1 - pC x:=by
 rw [stdPhiCDF_eq_half_add_intervalIntegral (-x),stdPhiCDF_eq_half_add_intervalIntegral x]
 have hc:=intervalIntegral.integral_comp_neg (a:=(0:R)) (b:=x) (f:=pP)
 simp only [neg_zero,stdPhiPDF_even] at hc
 have hsym:=intervalIntegral.integral_symm (a:=(0:R)) (b:=-x) (f:=pP) (μ:=volume)
 linarith
lemma pCd (x:R):HD pC (pP x) x:=by
 have hcont:Continuous pP:=by
  unfold pP
  fun_prop
 have hd:=intervalIntegral.integral_hasDerivAt_right
  (f:=pP) (a:=(0:R)) (b:=x)
  (hcont.intervalIntegrable 0 x)
  (hcont.stronglyMeasurableAtFilter _ _)
  hcont.continuousAt
 have heq:pC=fun y=>(1/2:R)+∫ t in (0:R)..y,pP t :=
  funext stdPhiCDF_eq_half_add_intervalIntegral
 rw [heq]
 have hadd:=(hasDerivAt_const x (1/2:R)).fun_add hd
 simpa only [zero_add] using hadd
lemma pCm:StrictMono pC:=by
 refine strictMono_of_deriv_pos fun x=>?_
 rw [(pCd x).deriv]
 exact pPp x
lemma pCp (x:R):0 < pC x:=by
 rw [stdPhiCDF_eq_integral]
 have hsub:Set.Ioc (x - 1) x ⊆ Set.Iic x:=fun t ht=>ht.2
 have hle:∫ t in Set.Ioc (x - 1) x,pP t<=∫ t in Set.Iic x,pP t :=
  setIntegral_mono_set ipP.integrableOn
   (ae_of_all _ pPn) (Eventually.of_forall hsub)
 have hpos:0 < ∫ t in Set.Ioc (x - 1) x,pP t:=by
  rw [← intervalIntegral.integral_of_le (by linarith:x - 1<=x)]
  have hcont:Continuous pP:=by unfold pP;fun_prop
  exact intervalIntegral.integral_pos (by linarith) hcont.continuousOn
   (fun t _=>pPn t) ⟨x,by simp,pPp x⟩
 linarith
lemma stdPhiCDF_lt_one (x:R):pC x < 1:=by
 have h:=pCp (-x)
 rw [stdPhiCDF_neg] at h
 linarith
def dF (a b:ℤ):ℤ:=a/b
def dC (a b:ℤ):ℤ:=-((-a)/b)
def mF (a b:ℤ):ℤ:=(a*b)/fpS
def mC (a b:ℤ):ℤ:=-((-(a*b))/fpS)
lemma fpS_pos:(0:R) < S0:=by norm_num [S0,fpS]
lemma divFl_le {a b:ℤ} (hb:0 < b):((dF a b:ℤ):R)<=(a:R)/(b:R):=by
 rw [dF,le_div_iff₀ (Int.cast_pos.mpr hb)]
 exact_mod_cast Int.ediv_mul_le a (ne_of_gt hb)
lemma le_divCe {a b:ℤ} (hb:0 < b):(a:R)/(b:R)<=((dC a b:ℤ):R):=by
 rw [dC,div_le_iff₀ (Int.cast_pos.mpr hb)]
 have h:=Int.ediv_mul_le (-a) (ne_of_gt hb)
 have h':((-a/b:ℤ):R)*(b:R)<=(-a:R):=by exact_mod_cast h
 simp only [Int.cast_neg]
 linarith
lemma mulFl_le (a b:ℤ) :
  ((mF a b:ℤ):R)/S0<=((a:R)/S0)*((b:R)/S0):=by
 have hs:(0:R) < S0:=fpS_pos
 have h:=divFl_le (a:=a*b) (b:=fpS) (by norm_num [S0,fpS])
 have h1:((mF a b:ℤ):R)<=(a:R)*(b:R)/S0:=by
  simpa [mF,dF,Int.cast_mul] using h
 rw [div_le_iff₀ hs]
 calc ((mF a b:ℤ):R)<=(a:R)*(b:R)/S0:=h1
  _ = ((a:R)/S0)*((b:R)/S0)*S0:=by field_simp
lemma le_mulCe (a b:ℤ) :
  ((a:R)/S0)*((b:R)/S0)<=((mC a b:ℤ):R)/S0:=by
 have hs:(0:R) < S0:=fpS_pos
 have h:=le_divCe (a:=a*b) (b:=fpS) (by norm_num [S0,fpS])
 have h1:(a:R)*(b:R)/S0<=((mC a b:ℤ):R):=by
  simpa [mC,dC,Int.cast_mul] using h
 rw [le_div_iff₀ hs]
 calc ((a:R)/S0)*((b:R)/S0)*S0
   = (a:R)*(b:R)/S0:=by field_simp
  _ <= ((mC a b:ℤ):R):=h1
lemma exp_neg_taylor_aux:∀ m:ℕ,
  (∀ u:R,0<=u ->
   (∑ k ∈ Finset.range (2*m),(-1:R)^k*u^k/(Nat.factorial k:R))<=exp (-u)) /\
  (∀ u:R,0<=u ->
   exp (-u) <=
    ∑ k ∈ Finset.range (2*m+1),(-1:R)^k*u^k/(Nat.factorial k:R)):=by
 have hderiv_sum:∀ (n:ℕ) (s:R),
   HD (fun y:R=>∑ k ∈ Finset.range (n+1),(-1:R)^k*y^k/(Nat.factorial k:R))
    (-∑ k ∈ Finset.range n,(-1:R)^k*s^k/(Nat.factorial k:R)) s:=by
  intro n s
  have hsum:(fun y:R=>∑ k ∈ Finset.range (n+1),(-1:R)^k*y^k/(Nat.factorial k:R)) =
    fun y:R=>(1:R)+∑ k ∈ Finset.range n,(-1:R)^(k+1)*y^(k+1)/(Nat.factorial (k+1):R):=by
   ext y;rw [Finset.sum_range_succ'];simp [add_comm]
  rw [hsum]
  have hterm:∀ k ∈ Finset.range n,
    HD (fun y:R=>(-1:R)^(k+1)*y^(k+1)/(Nat.factorial (k+1):R))
     (-((-1:R)^k*s^k/(Nat.factorial k:R))) s:=by
   intro k _
   have h1:HD (fun y:R=>(-1:R)^(k+1)*y^(k+1)/(Nat.factorial (k+1):R))
     ((-1:R)^(k+1)*((↑(k+1):R)*s^k)/(Nat.factorial (k+1):R)) s :=
    ((hdp (k+1) s).const_mul ((-1:R)^(k+1))).div_const (Nat.factorial (k+1):R)
   have heq:(-1:R)^(k+1)*((↑(k+1):R)*s^k)/(Nat.factorial (k+1):R) =
     -((-1:R)^k*s^k/(Nat.factorial k:R)):=by
    rw [Nat.factorial_succ,Nat.cast_mul,pow_succ]
    have hk:((k+1:ℕ):R) ≠ 0:=by positivity
    have hf:(Nat.factorial k:R) ≠ 0:=by positivity
    field_simp
   rwa [heq] at h1
  have htot:=(hasDerivAt_const s (1:R)).fun_add (HasDerivAt.fun_sum hterm)
  simpa only [zero_add,Finset.sum_neg_distrib] using htot
 have hderiv_exp:∀ s:R,HD (fun y:R=>exp (-y)) (-exp (-s)) s:=by
  intro s
  have h:=(hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)
  simpa only [Function.comp_def,mul_neg,mul_one] using h
 have h_step_lo:∀ n:ℕ,
   (∀ t:R,0<=t->exp (-t)<=∑ k ∈ Finset.range n,(-1:R)^k*t^k/(Nat.factorial k:R)) ->
   ∀ t:R,0<=t->∑ k ∈ Finset.range (n+1),(-1:R)^k*t^k/(Nat.factorial k:R)<=exp (-t):=by
  intro n hprev t ht
  let F:R->R:=fun s =>
   exp (-s) - ∑ k ∈ Finset.range (n+1),(-1:R)^k*s^k/(Nat.factorial k:R)
  have hF0:F 0=0:=by simp [F,Finset.sum_range_succ']
  have hhd:∀ s:R,HD F
    (-exp (-s)+∑ k ∈ Finset.range n,(-1:R)^k*s^k/(Nat.factorial k:R)) s:=by
   intro s
   have h:=(hderiv_exp s).fun_sub (hderiv_sum n s)
   simpa only [sub_neg_eq_add] using h
  have hdiff:Differentiable R F:=fun s=>(hhd s).differentiableAt
  have hmono:MonotoneOn F (Set.Icc 0 t) :=
   monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hdiff.continuous.continuousOn
    hdiff.differentiableOn fun s hs=>by
     rw [interior_Icc] at hs
     rw [(hhd s).deriv]
     linarith [hprev s hs.1.le]
  have:=hmono ⟨le_rfl,ht⟩ ⟨ht,le_rfl⟩ ht
  linarith [hF0]
 have h_step_hi:∀ n:ℕ,
   (∀ t:R,0<=t->∑ k ∈ Finset.range n,(-1:R)^k*t^k/(Nat.factorial k:R)<=exp (-t)) ->
   ∀ t:R,0<=t->exp (-t)<=∑ k ∈ Finset.range (n+1),(-1:R)^k*t^k/(Nat.factorial k:R):=by
  intro n hprev t ht
  let F:R->R:=fun s =>
   (∑ k ∈ Finset.range (n+1),(-1:R)^k*s^k/(Nat.factorial k:R)) - exp (-s)
  have hF0:F 0=0:=by simp [F,Finset.sum_range_succ']
  have hhd:∀ s:R,HD F
    (-(∑ k ∈ Finset.range n,(-1:R)^k*s^k/(Nat.factorial k:R))+exp (-s)) s:=by
   intro s
   have h:=(hderiv_sum n s).fun_sub (hderiv_exp s)
   simpa only [sub_neg_eq_add] using h
  have hdiff:Differentiable R F:=fun s=>(hhd s).differentiableAt
  have hmono:MonotoneOn F (Set.Icc 0 t) :=
   monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hdiff.continuous.continuousOn
    hdiff.differentiableOn fun s hs=>by
     rw [interior_Icc] at hs
     rw [(hhd s).deriv]
     linarith [hprev s hs.1.le]
  have:=hmono ⟨le_rfl,ht⟩ ⟨ht,le_rfl⟩ ht
  linarith [hF0]
 intro m
 induction m with
 | zero =>
  refine ⟨fun u _=>by simp [exp_nonneg],fun u hu=>?_⟩
  simp only [Nat.mul_zero,zero_add,Finset.range_one,Finset.sum_singleton,pow_zero,
   mul_one,Nat.factorial_zero,Nat.cast_one,div_one,exp_le_one_iff]
  linarith
 | succ m ih =>
  have hlo:=h_step_lo (2*m+1) ih.2
  have hhi:=h_step_hi (2*m+2) hlo
  exact ⟨by simpa [Nat.mul_succ] using hlo,by simpa [Nat.mul_succ] using hhi⟩
lemma erf_int_taylor_bounds (x:R) (hx:0<=x) (m:ℕ) :
  (∑ k ∈ Finset.range (2*m),
    (-1:R)^k*x^(2*k+1)/((2:R)^k*(Nat.factorial k:R)*(2*k+1:R))) <=
   (∫ u in (0:R)..x,exp (-u^2/2)) /\
  (∫ u in (0:R)..x,exp (-u^2/2)) <=
   ∑ k ∈ Finset.range (2*m+1),
    (-1:R)^k*x^(2*k+1)/((2:R)^k*(Nat.factorial k:R)*(2*k+1:R)):=by
 have hint_term:∀ k:ℕ,
   ∫ u in (0:R)..x,(-1:R)^k*(u^2/2)^k/(Nat.factorial k:R) =
   (-1:R)^k*x^(2*k+1)/((2:R)^k*(Nat.factorial k:R)*(2*k+1:R)):=by
  intro k
  have hpow:∀ u:R,
    (-1:R)^k*(u^2/2)^k/(Nat.factorial k:R) =
    ((-1:R)^k/((2:R)^k*(Nat.factorial k:R)))*u^(2*k):=by
   intro u
   rw [div_pow,← pow_mul]
   ring
  simp_rw [hpow]
  rw [intervalIntegral.integral_const_mul,integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero (2*k)),sub_zero]
  push_cast
  have hd1:(2:R)^k ≠ 0:=by positivity
  have hd2:(Nat.factorial k:R) ≠ 0:=by positivity
  have hd3:(2*(k:R)+1) ≠ 0:=by positivity
  field_simp
 have hint_sum:∀ N:ℕ,
   ∫ u in (0:R)..x,(∑ k ∈ Finset.range N,(-1:R)^k*(u^2/2)^k/(Nat.factorial k:R)) =
   ∑ k ∈ Finset.range N,
    (-1:R)^k*x^(2*k+1)/((2:R)^k*(Nat.factorial k:R)*(2*k+1:R)):=by
  intro N
  rw [intervalIntegral.integral_finsetSum]
  . exact Finset.sum_congr rfl fun k _=>hint_term k
  . intro k _;exact Continuous.intervalIntegrable (by fun_prop) 0 x
 have hexp_int:IntervalIntegrable (fun u:R=>exp (-u^2/2)) volume 0 x :=
  Continuous.intervalIntegrable (by fun_prop) 0 x
 have hsum_int:∀ N:ℕ,IntervalIntegrable
   (fun u:R=>∑ k ∈ Finset.range N,(-1:R)^k*(u^2/2)^k/(Nat.factorial k:R))
   volume 0 x:=fun N=>Continuous.intervalIntegrable (by fun_prop) 0 x
 constructor
 .
  rw [← hint_sum (2*m)]
  refine intervalIntegral.integral_mono_on hx (hsum_int (2*m)) hexp_int fun u _=>?_
  simpa [neg_div] using (exp_neg_taylor_aux m).1 (u^2/2) (by positivity)
 .
  rw [← hint_sum (2*m+1)]
  refine intervalIntegral.integral_mono_on hx hexp_int (hsum_int (2*m+1)) fun u _=>?_
  simpa [neg_div] using (exp_neg_taylor_aux m).2 (u^2/2) (by positivity)
def eSL (isHi:Bool) (u:ℤ):ℕ->ℕ->ℤ->ℤ->ℤ->ℤ->ℤ
 | 0,_,_,_,_,acc=>acc
 | steps+1,k,fact,pLo,pHi,acc =>
  let fact':=fact*(k:ℤ)
  let pLo':=dF (pLo*u) fpS
  let pHi':=dC (pHi*u) fpS
  let acc' :=
   if k % 2 == 1 then
    if isHi then acc - dF pLo' fact' else acc - dC pHi' fact'
   else
    if isHi then acc+dC pHi' fact' else acc+dF pLo' fact'
  eSL isHi u steps (k+1) fact' pLo' pHi' acc'
def eS0 (x:ℤ):ℤ :=
 max 0 (eSL false (-x) 9 1 1 fpS fpS fpS)
def eS1 (x:ℤ):ℤ :=
 eSL true (-x) 10 1 1 fpS fpS fpS
def sqLoop (isHi:Bool):ℕ->ℤ->ℤ
 | 0,v=>v
 | n+1,v =>
  let v':=if isHi then mC v v else mF v v
  sqLoop isHi n v'
def eL (x:ℤ):ℤ :=
 if 0<=x then fpS
 else
  let y:=dF x 16
  if y < -fpS then 0 else sqLoop false 4 (eS0 y)
def eH (x:ℤ):ℤ :=
 if 0<=x then fpS
 else
  let y:=dC x 16
  if y < -fpS then fpS else sqLoop true 4 (eS1 y)
def i20:ℤ:=3989422
def i21:ℤ:=3989424
def iP0:ℤ:=1591549
def iP1:ℤ:=1591550
def erfLoop (isHi:Bool) (x2Lo x2Hi:ℤ):ℕ->ℕ->ℤ->ℤ->ℤ->ℤ->ℤ
 | 0,_,_,_,_,acc=>acc
 | steps+1,k,dBase,pLo,pHi,acc =>
  let dBase':=dBase*(2*(k:ℤ))
  let pLo':=dF (pLo*x2Lo) fpS
  let pHi':=dC (pHi*x2Hi) fpS
  let d:=dBase'*(2*(k:ℤ)+1)
  let acc' :=
   if k % 2 == 1 then
    if isHi then acc - dF pLo' d else acc - dC pHi' d
   else
    if isHi then acc+dC pHi' d else acc+dF pLo' d
  erfLoop isHi x2Lo x2Hi steps (k+1) dBase' pLo' pHi' acc'
def eP0 (x:ℤ):ℤ :=
 erfLoop false (dF (x*x) fpS) (dC (x*x) fpS) 15 1 1 x x x
def eP1 (x:ℤ):ℤ :=
 erfLoop true (dF (x*x) fpS) (dC (x*x) fpS) 16 1 1 x x x
def cL (x:ℤ):ℤ :=
 if 0<=x then fpS/2+mF i20 (eP0 x)
 else fpS - (fpS/2+mC i21 (eP1 (-x)))
def cH (x:ℤ):ℤ :=
 if 0<=x then fpS/2+mC i21 (eP1 x)
 else fpS - (fpS/2+mF i20 (eP0 (-x)))
def pL (x:ℤ):ℤ :=
 mF i20 (eL (-dC (x*x) (2*fpS)))
def pH (x:ℤ):ℤ :=
 mC i21 (eH (-dF (x*x) (2*fpS)))
lemma expSmallLoop_sound (isHi:Bool) (u:ℤ) (hu:0<=u) :
  ∀ (steps k:ℕ) (fact pLo pHi acc:ℤ),
   k>=1->fact=(Nat.factorial (k - 1):ℤ) ->
   0<=pLo ->
   ((pLo:R)/S0)<=((u:R)/S0)^(k - 1) ->
   ((u:R)/S0)^(k - 1)<=((pHi:R)/S0) ->
   (if isHi then
    (∑ j ∈ Finset.range k,(-1:R)^j*((u:R)/S0)^j/(Nat.factorial j:R)) <=
     (acc:R)/S0
    else
    (acc:R)/S0 <=
     ∑ j ∈ Finset.range k,(-1:R)^j*((u:R)/S0)^j/(Nat.factorial j:R)) ->
   (if isHi then
    (∑ j ∈ Finset.range (k+steps),(-1:R)^j*((u:R)/S0)^j/(Nat.factorial j:R)) <=
     (eSL isHi u steps k fact pLo pHi acc:R)/S0
    else
    (eSL isHi u steps k fact pLo pHi acc:R)/S0 <=
     ∑ j ∈ Finset.range (k+steps),(-1:R)^j*((u:R)/S0)^j/(Nat.factorial j:R)):=by
 intro steps
 induction steps with
 | zero =>
  intro k fact pLo pHi acc _ _ _ _ _ hacc
  simpa [eSL] using hacc
 | succ steps ih =>
  intro k fact pLo pHi acc hk hfact hpLo_nn hpLo hpHi hacc
  have hs:(0:R) < S0:=fpS_pos
  have huR:(0:R)<=(u:R)/S0:=by positivity
  have hfact':fact*(k:ℤ)=(Nat.factorial k:ℤ):=by
   rw [hfact]
   cases k with
   | zero=>omega
   | succ k'=>simp [Nat.factorial_succ,mul_comm]
  have hfact'_pos:(0:ℤ) < fact*(k:ℤ):=by
   rw [hfact'];exact_mod_cast Nat.factorial_pos k
  have hpow_eq:((u:R)/S0)^k=((u:R)/S0)^(k - 1)*((u:R)/S0):=by
   cases k with
   | zero=>omega
   | succ k'=>simp [pow_succ]
  have hpLo'_nn:0<=dF (pLo*u) fpS:=Int.ediv_nonneg (mul_nonneg hpLo_nn hu) (by norm_num [S0,fpS])
  have hpLo':((dF (pLo*u) fpS:ℤ):R)/S0<=((u:R)/S0)^k:=by
   rw [hpow_eq]
   calc ((dF (pLo*u) fpS:ℤ):R)/S0
     <= ((pLo:R)/S0)*((u:R)/S0):=mulFl_le pLo u
    _ <= ((u:R)/S0)^(k - 1)*((u:R)/S0) :=
      mlR hpLo huR
  have hpHi':((u:R)/S0)^k<=((dC (pHi*u) fpS:ℤ):R)/S0:=by
   rw [hpow_eq]
   calc ((u:R)/S0)^(k - 1)*((u:R)/S0)
     <= ((pHi:R)/S0)*((u:R)/S0) :=
      mlR hpHi huR
    _ <= ((dC (pHi*u) fpS:ℤ):R)/S0:=le_mulCe pHi u
  have hdiv_lo:((dF (dF (pLo*u) fpS) (fact*(k:ℤ)):ℤ):R)/S0 <=
    ((u:R)/S0)^k/(Nat.factorial k:R):=by
   have hd:=divFl_le (a:=dF (pLo*u) fpS) (b:=fact*(k:ℤ)) hfact'_pos
   have hfR:(0:R) < (Nat.factorial k:R):=by positivity
   have hfeq:((fact*(k:ℤ):ℤ):R)=(Nat.factorial k:R):=by exact_mod_cast hfact'
   rw [hfeq] at hd
   calc ((dF (dF (pLo*u) fpS) (fact*(k:ℤ)):ℤ):R)/S0
     <= (((dF (pLo*u) fpS:ℤ):R)/(Nat.factorial k:R))/S0 :=
      dld hd hs.le
    _ = (((dF (pLo*u) fpS:ℤ):R)/S0)/(Nat.factorial k:R):=by ring
    _ <= ((u:R)/S0)^k/(Nat.factorial k:R) :=
      dld hpLo' hfR.le
  have hdiv_hi:((u:R)/S0)^k/(Nat.factorial k:R) <=
    ((dC (dC (pHi*u) fpS) (fact*(k:ℤ)):ℤ):R)/S0:=by
   have hd:=le_divCe (a:=dC (pHi*u) fpS) (b:=fact*(k:ℤ)) hfact'_pos
   have hfR:(0:R) < (Nat.factorial k:R):=by positivity
   have hfeq:((fact*(k:ℤ):ℤ):R)=(Nat.factorial k:R):=by exact_mod_cast hfact'
   rw [hfeq] at hd
   calc ((u:R)/S0)^k/(Nat.factorial k:R)
     <= (((dC (pHi*u) fpS:ℤ):R)/S0)/(Nat.factorial k:R) :=
      dld hpHi' hfR.le
    _ = (((dC (pHi*u) fpS:ℤ):R)/(Nat.factorial k:R))/S0:=by ring
    _ <= ((dC (dC (pHi*u) fpS) (fact*(k:ℤ)):ℤ):R)/S0 :=
      dld hd hs.le
  have hstep_eq:k+(steps+1)=(k+1)+steps:=by omega
  rw [hstep_eq]
  refine ih (k+1) (fact*(k:ℤ)) (dF (pLo*u) fpS) (dC (pHi*u) fpS) _ (by omega)
   (by simpa using hfact') hpLo'_nn (by simpa using hpLo') (by simpa using hpHi') ?_
  rw [Finset.sum_range_succ]
  cases isHi <;> simp only [Bool.false_eq_true,↓reduceIte] at hacc ⊢
  .
   split_ifs with hodd
   .
    have hmod:k % 2=1:=by simpa using hodd
    have hsign:(-1:R)^k = -1:=Odd.neg_one_pow (Nat.odd_iff.mpr hmod)
    rw [hsign,Int.cast_sub,sub_div]
    have hneg:-1*((u:R)/S0)^k/(Nat.factorial k:R) =
      -(((u:R)/S0)^k/(Nat.factorial k:R)):=by ring
    rw [hneg]
    linarith
   .
    have hmod:k % 2=0:=by
     have:k % 2 ≠ 1:=by simpa using hodd
     omega
    have hsign:(-1:R)^k=1:=Even.neg_one_pow (Nat.even_iff.mpr hmod)
    rw [hsign,one_mul,Int.cast_add,add_div]
    linarith
  .
   split_ifs with hodd
   .
    have hmod:k % 2=1:=by simpa using hodd
    have hsign:(-1:R)^k = -1:=Odd.neg_one_pow (Nat.odd_iff.mpr hmod)
    rw [hsign,Int.cast_sub,sub_div]
    have hneg:-1*((u:R)/S0)^k/(Nat.factorial k:R) =
      -(((u:R)/S0)^k/(Nat.factorial k:R)):=by ring
    rw [hneg]
    linarith
   .
    have hmod:k % 2=0:=by
     have:k % 2 ≠ 1:=by simpa using hodd
     omega
    have hsign:(-1:R)^k=1:=Even.neg_one_pow (Nat.even_iff.mpr hmod)
    rw [hsign,one_mul,Int.cast_add,add_div]
    linarith
lemma expSmallLo_le {x:ℤ} (hx:x<=0) :
  ((eS0 x:ℤ):R)/S0<=exp ((x:R)/S0):=by
 have hs:(0:R) < S0:=fpS_pos
 have hu:0 <= -x:=by omega
 have h1:=expSmallLoop_sound false (-x) hu 9 1 1 fpS fpS fpS (le_rfl) (by simp) (by norm_num [S0,fpS])
  (by simp [div_self hs.ne']) (by simp [div_self hs.ne'])
  (by simp [div_self hs.ne'])
 simp only [Bool.false_eq_true,↓reduceIte] at h1
 have h2:=(exp_neg_taylor_aux 5).1 ((-x:ℤ)/S0) (by
  have:(0:R)<=((-x:ℤ):R):=by exact_mod_cast hu
  positivity)
 have hxe:-(((-x:ℤ):R)/S0)=(x:R)/S0:=by simp [neg_div]
 rw [hxe] at h2
 rw [eS0]
 by_cases h0:0<=eSL false (-x) 9 1 1 fpS fpS fpS
 . rw [max_eq_right h0];exact h1.trans (by simpa using h2)
 . rw [max_eq_left (le_of_not_ge h0)];simp [exp_nonneg]
lemma le_expSmallHi {x:ℤ} (hx:x<=0) :
  exp ((x:R)/S0)<=((eS1 x:ℤ):R)/S0:=by
 have hs:(0:R) < S0:=fpS_pos
 have hu:0 <= -x:=by omega
 have h1:=expSmallLoop_sound true (-x) hu 10 1 1 fpS fpS fpS (le_rfl) (by simp) (by norm_num [S0,fpS])
  (by simp [div_self hs.ne']) (by simp [div_self hs.ne'])
  (by simp [div_self hs.ne'])
 simp only [↓reduceIte] at h1
 have h2:=(exp_neg_taylor_aux 5).2 ((-x:ℤ)/S0) (by
  have:(0:R)<=((-x:ℤ):R):=by exact_mod_cast hu
  positivity)
 have hxe:-(((-x:ℤ):R)/S0)=(x:R)/S0:=by simp [neg_div]
 rw [hxe] at h2
 exact h2.trans (by simpa [eS1] using h1)
lemma sqLoop_lo_le:∀ (n:ℕ) (v:ℤ) (r:R),
  0<=v->((v:R)/S0)<=r ->
  ((sqLoop false n v:ℤ):R)/S0<=r^(2^n):=by
 intro n
 induction n with
 | zero=>intro v r _ h;simpa [sqLoop] using h
 | succ n ih =>
  intro v r hv h
  have hv':0<=mF v v:=Int.ediv_nonneg (mul_nonneg hv hv) (by norm_num [S0,fpS])
  have hr:0<=r:=le_trans (by
   have:(0:R)<=(v:R):=by exact_mod_cast hv
   have hs:(0:R) < S0:=fpS_pos
   positivity) h
  have hsq:((mF v v:ℤ):R)/S0<=r^2:=by
   calc ((mF v v:ℤ):R)/S0
     <= ((v:R)/S0)*((v:R)/S0):=mulFl_le v v
    _ <= r*r:=mul_self_le_mul_self (by
      have:(0:R)<=(v:R):=by exact_mod_cast hv
      have hs:(0:R) < S0:=fpS_pos
      positivity) h
    _ = r^2:=(sq r).symm
  have hres:=ih (mF v v) (r^2) hv' hsq
  simpa [sqLoop,pow_succ,pow_mul,mul_comm] using hres
lemma le_sqLoop_hi:∀ (n:ℕ) (v:ℤ) (r:R),
  0<=r->r<=((v:R)/S0) ->
  r^(2^n)<=((sqLoop true n v:ℤ):R)/S0:=by
 intro n
 induction n with
 | zero=>intro v r _ h;simpa [sqLoop] using h
 | succ n ih =>
  intro v r hr h
  have hsq:r^2<=((mC v v:ℤ):R)/S0:=by
   calc r^2=r*r:=sq r
    _ <= ((v:R)/S0)*((v:R)/S0):=mul_self_le_mul_self hr h
    _ <= ((mC v v:ℤ):R)/S0:=le_mulCe v v
  have hres:=ih (mC v v) (r^2) (sq_nonneg r) hsq
  simpa [sqLoop,pow_succ,pow_mul,mul_comm] using hres
lemma expNegLo_le {x:ℤ} (hx:x<=0) :
  ((eL x:ℤ):R)/S0<=exp ((x:R)/S0):=by
 have hs:(0:R) < S0:=fpS_pos
 unfold eL
 by_cases h0:0<=x
 .
  rw [if_pos h0]
  have hxeq:x=0:=by omega
  subst hxeq;simp [div_self hs.ne']
 .
  rw [if_neg h0]
  dsimp only
  split_ifs with h1
  . simp [exp_nonneg]
  .
   have hy:dF x 16<=0:=by unfold dF;omega
   have hyle:((dF x 16:ℤ):R)/S0<=((x:R)/S0)/16:=by
    have hd:=divFl_le (a:=x) (b:=16) (by norm_num)
    have h16:((16:ℤ):R)=16:=by norm_num
    rw [h16] at hd
    calc ((dF x 16:ℤ):R)/S0
      <= ((x:R)/16)/S0:=dld hd hs.le
     _ = ((x:R)/S0)/16:=by ring
   have hexp_y:((eS0 (dF x 16):ℤ):R)/S0 <=
     exp (((x:R)/S0)/16) :=
    (expSmallLo_le hy).trans (exp_le_exp.mpr hyle)
   have hsq:=sqLoop_lo_le 4 (eS0 (dF x 16))
    (exp (((x:R)/S0)/16)) (le_max_left _ _) hexp_y
   have hpow:(exp (((x:R)/S0)/16))^(2^4)=exp ((x:R)/S0):=by
    rw [← exp_nat_mul];congr 1;norm_num;ring
   rwa [hpow] at hsq
lemma le_expNegHi {x:ℤ} (hx:x<=0) :
  exp ((x:R)/S0)<=((eH x:ℤ):R)/S0:=by
 have hs:(0:R) < S0:=fpS_pos
 unfold eH
 by_cases h0:0<=x
 .
  rw [if_pos h0]
  have hxeq:x=0:=by omega
  subst hxeq;simp [div_self hs.ne']
 .
  rw [if_neg h0]
  dsimp only
  split_ifs with h1
  .
   rw [div_self hs.ne',exp_le_one_iff]
   exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hx) hs.le
  .
   have hy:dC x 16<=0:=by
    unfold dC
    have:0<=(-x)/16:=Int.ediv_nonneg (by omega) (by norm_num)
    omega
   have hyle:((x:R)/S0)/16<=((dC x 16:ℤ):R)/S0:=by
    have hd:=le_divCe (a:=x) (b:=16) (by norm_num)
    have h16:((16:ℤ):R)=16:=by norm_num
    rw [h16] at hd
    calc ((x:R)/S0)/16
      = ((x:R)/16)/S0:=by ring
     _ <= ((dC x 16:ℤ):R)/S0:=dld hd hs.le
   have hexp_y:exp (((x:R)/S0)/16) <=
     ((eS1 (dC x 16):ℤ):R)/S0 :=
    (exp_le_exp.mpr hyle).trans (le_expSmallHi hy)
   have hsq:=le_sqLoop_hi 4 (eS1 (dC x 16))
    (exp (((x:R)/S0)/16)) (exp_nonneg _) hexp_y
   have hpow:(exp (((x:R)/S0)/16))^(2^4)=exp ((x:R)/S0):=by
    rw [← exp_nat_mul];congr 1;norm_num;ring
   rwa [hpow] at hsq
lemma pi_bounds_invSqrt2Pi :
  ((i20:ℤ):R)/S0<=(sqrt (2*PI))⁻¹ /\
  (sqrt (2*PI))⁻¹<=((i21:ℤ):R)/S0:=by
 have hpi_lo:(3.141592:R) < PI:=pi_gt_d6
 have hpi_hi:PI < (3.141593:R):=pi_lt_d6
 have hpos:(0:R) < sqrt (2*PI):=by positivity
 constructor
 .
  rw [le_inv_comm₀ (by norm_num [i20,S0,fpS]) hpos]
  rw [sqrt_le_iff]
  constructor
  . norm_num [i20,S0,fpS]
  . norm_num [i20,S0,fpS];linarith
 .
  rw [inv_le_comm₀ hpos (by norm_num [i21,S0,fpS])]
  rw [le_sqrt (by norm_num [i21,S0,fpS]) (by linarith)]
  norm_num [i21,S0,fpS];linarith
lemma pi_bounds_inv2Pi :
  ((iP0:ℤ):R)/S0<=(2*PI)⁻¹ /\
  (2*PI)⁻¹<=((iP1:ℤ):R)/S0:=by
 have hpi_lo:(3.141592:R) < PI:=pi_gt_d6
 have hpi_hi:PI < (3.141593:R):=pi_lt_d6
 have hpos:(0:R) < 2*PI:=by linarith
 constructor
 .
  rw [le_inv_comm₀ (by norm_num [iP0,S0,fpS]) hpos]
  norm_num [iP0,S0,fpS];linarith
 .
  rw [inv_le_comm₀ hpos (by norm_num [iP1,S0,fpS])]
  norm_num [iP1,S0,fpS];linarith
lemma erfLoop_sound (isHi:Bool) (x x2Lo x2Hi:ℤ) (hx:0<=x)
  (hx2Lo_nn:0<=x2Lo)
  (hx2Lo:((x2Lo:R)/S0)<=((x:R)/S0)^2)
  (hx2Hi:((x:R)/S0)^2<=((x2Hi:R)/S0)) :
  ∀ (steps k:ℕ) (dBase pLo pHi acc:ℤ),
   k>=1->dBase=((2:ℤ)^(k - 1)*(Nat.factorial (k - 1):ℤ)) ->
   0<=pLo ->
   ((pLo:R)/S0)<=((x:R)/S0)^(2*(k - 1)+1) ->
   ((x:R)/S0)^(2*(k - 1)+1)<=((pHi:R)/S0) ->
   (if isHi then
    (∑ j ∈ Finset.range k,(-1:R)^j*((x:R)/S0)^(2*j+1) /
     ((2:R)^j*(Nat.factorial j:R)*(2*j+1:R)))<=(acc:R)/S0
    else
    (acc:R)/S0 <=
     ∑ j ∈ Finset.range k,(-1:R)^j*((x:R)/S0)^(2*j+1) /
      ((2:R)^j*(Nat.factorial j:R)*(2*j+1:R))) ->
   (if isHi then
    (∑ j ∈ Finset.range (k+steps),(-1:R)^j*((x:R)/S0)^(2*j+1) /
     ((2:R)^j*(Nat.factorial j:R)*(2*j+1:R))) <=
     (erfLoop isHi x2Lo x2Hi steps k dBase pLo pHi acc:R)/S0
    else
    (erfLoop isHi x2Lo x2Hi steps k dBase pLo pHi acc:R)/S0 <=
     ∑ j ∈ Finset.range (k+steps),(-1:R)^j*((x:R)/S0)^(2*j+1) /
      ((2:R)^j*(Nat.factorial j:R)*(2*j+1:R))):=by
 intro steps
 induction steps with
 | zero =>
  intro k dBase pLo pHi acc _ _ _ _ _ hacc
  simpa [erfLoop] using hacc
 | succ steps ih =>
  intro k dBase pLo pHi acc hk hdBase hpLo_nn hpLo hpHi hacc
  have hs:(0:R) < S0:=fpS_pos
  have hxR:(0:R)<=(x:R)/S0:=by positivity
  have hdBase':dBase*(2*(k:ℤ))=(2:ℤ)^k*(Nat.factorial k:ℤ):=by
   rw [hdBase]
   cases k with
   | zero=>omega
   | succ k' =>
    simp only [Nat.add_sub_cancel,pow_succ,Nat.factorial_succ,Nat.cast_mul]
    ring
  have hd_eq:((dBase*(2*(k:ℤ))*(2*(k:ℤ)+1):ℤ):R) =
    (2:R)^k*(Nat.factorial k:R)*(2*(k:R)+1):=by
   have h1:((dBase*(2*(k:ℤ)):ℤ):R)=(2:R)^k*(Nat.factorial k:R):=by
    exact_mod_cast hdBase'
   push_cast
   have h2:((dBase:R)*(2*(k:R)))=(2:R)^k*(Nat.factorial k:R):=by
    simpa using h1
   rw [h2]
  have hd_pos:(0:ℤ) < dBase*(2*(k:ℤ))*(2*(k:ℤ)+1):=by
   rw [hdBase']
   have h1:(0:ℤ) < (2:ℤ)^k:=by positivity
   have h2:(0:ℤ) < (Nat.factorial k:ℤ):=by exact_mod_cast Nat.factorial_pos k
   have h3:(0:ℤ) < 2*(k:ℤ)+1:=by omega
   positivity
  have hpow_eq:((x:R)/S0)^(2*k+1) =
    ((x:R)/S0)^(2*(k - 1)+1)*((x:R)/S0)^2:=by
   rw [← pow_add]
   congr 1
   omega
  have hpLo'_nn:0<=dF (pLo*x2Lo) fpS :=
   Int.ediv_nonneg (mul_nonneg hpLo_nn hx2Lo_nn) (by norm_num [S0,fpS])
  have hpLo':((dF (pLo*x2Lo) fpS:ℤ):R)/S0 <=
    ((x:R)/S0)^(2*k+1):=by
   rw [hpow_eq]
   calc ((dF (pLo*x2Lo) fpS:ℤ):R)/S0
     <= ((pLo:R)/S0)*((x2Lo:R)/S0):=mulFl_le pLo x2Lo
    _ <= ((x:R)/S0)^(2*(k - 1)+1)*((x:R)/S0)^2 :=
      mul_le_mul hpLo hx2Lo (by positivity) (by positivity)
  have hpHi':((x:R)/S0)^(2*k+1) <=
    ((dC (pHi*x2Hi) fpS:ℤ):R)/S0:=by
   rw [hpow_eq]
   have hpHi_nn:(0:R)<=(pHi:R)/S0:=le_trans (by positivity) hpHi
   calc ((x:R)/S0)^(2*(k - 1)+1)*((x:R)/S0)^2
     <= ((pHi:R)/S0)*((x2Hi:R)/S0) :=
      mul_le_mul hpHi hx2Hi (by positivity) hpHi_nn
    _ <= ((dC (pHi*x2Hi) fpS:ℤ):R)/S0:=le_mulCe pHi x2Hi
  have hdR_pos:(0:R) < (2:R)^k*(Nat.factorial k:R)*(2*(k:R)+1):=by positivity
  have hdiv_lo:((dF (dF (pLo*x2Lo) fpS) (dBase*(2*(k:ℤ))*(2*(k:ℤ)+1)):ℤ):R) /
    S0<=((x:R)/S0)^(2*k+1)/((2:R)^k*(Nat.factorial k:R)*(2*k+1:R)):=by
   have hd:=divFl_le (a:=dF (pLo*x2Lo) fpS) (b:=dBase*(2*(k:ℤ))*(2*(k:ℤ)+1)) hd_pos
   rw [hd_eq] at hd
   calc ((dF (dF (pLo*x2Lo) fpS) (dBase*(2*(k:ℤ))*(2*(k:ℤ)+1)):ℤ):R)/S0
     <= (((dF (pLo*x2Lo) fpS:ℤ):R)/((2:R)^k*(Nat.factorial k:R)*(2*k+1:R)))/S0 :=
      dld hd hs.le
    _ = (((dF (pLo*x2Lo) fpS:ℤ):R)/S0)/((2:R)^k*(Nat.factorial k:R)*(2*k+1:R)):=by ring
    _ <= ((x:R)/S0)^(2*k+1)/((2:R)^k*(Nat.factorial k:R)*(2*k+1:R)) :=
      dld hpLo' hdR_pos.le
  have hdiv_hi:((x:R)/S0)^(2*k+1)/((2:R)^k*(Nat.factorial k:R)*(2*k+1:R)) <=
    ((dC (dC (pHi*x2Hi) fpS) (dBase*(2*(k:ℤ))*(2*(k:ℤ)+1)):ℤ):R)/S0:=by
   have hd:=le_divCe (a:=dC (pHi*x2Hi) fpS) (b:=dBase*(2*(k:ℤ))*(2*(k:ℤ)+1)) hd_pos
   rw [hd_eq] at hd
   calc ((x:R)/S0)^(2*k+1)/((2:R)^k*(Nat.factorial k:R)*(2*k+1:R))
     <= (((dC (pHi*x2Hi) fpS:ℤ):R)/S0)/((2:R)^k*(Nat.factorial k:R)*(2*k+1:R)) :=
      dld hpHi' hdR_pos.le
    _ = (((dC (pHi*x2Hi) fpS:ℤ):R)/((2:R)^k*(Nat.factorial k:R)*(2*k+1:R)))/S0:=by ring
    _ <= ((dC (dC (pHi*x2Hi) fpS) (dBase*(2*(k:ℤ))*(2*(k:ℤ)+1)):ℤ):R)/S0 :=
      dld hd hs.le
  have hstep_eq:k+(steps+1)=(k+1)+steps:=by omega
  rw [hstep_eq]
  refine ih (k+1) (dBase*(2*(k:ℤ))) (dF (pLo*x2Lo) fpS) (dC (pHi*x2Hi) fpS) _ (by omega)
   (by simpa using hdBase') hpLo'_nn (by simpa using hpLo') (by simpa using hpHi') ?_
  rw [Finset.sum_range_succ]
  cases isHi <;> simp only [Bool.false_eq_true,↓reduceIte] at hacc ⊢
  .
   split_ifs with hodd
   .
    have hmod:k % 2=1:=by simpa using hodd
    have hsign:(-1:R)^k = -1:=Odd.neg_one_pow (Nat.odd_iff.mpr hmod)
    rw [hsign,Int.cast_sub,sub_div]
    have hneg:-1*((x:R)/S0)^(2*k+1)/((2:R)^k*(Nat.factorial k:R)*(2*k+1:R)) =
      -(((x:R)/S0)^(2*k+1)/((2:R)^k*(Nat.factorial k:R)*(2*k+1:R))):=by ring
    rw [hneg];linarith
   .
    have hmod:k % 2=0:=by
     have:k % 2 ≠ 1:=by simpa using hodd
     omega
    have hsign:(-1:R)^k=1:=Even.neg_one_pow (Nat.even_iff.mpr hmod)
    rw [hsign,one_mul,Int.cast_add,add_div];linarith
  .
   split_ifs with hodd
   .
    have hmod:k % 2=1:=by simpa using hodd
    have hsign:(-1:R)^k = -1:=Odd.neg_one_pow (Nat.odd_iff.mpr hmod)
    rw [hsign,Int.cast_sub,sub_div]
    have hneg:-1*((x:R)/S0)^(2*k+1)/((2:R)^k*(Nat.factorial k:R)*(2*k+1:R)) =
      -(((x:R)/S0)^(2*k+1)/((2:R)^k*(Nat.factorial k:R)*(2*k+1:R))):=by ring
    rw [hneg];linarith
   .
    have hmod:k % 2=0:=by
     have:k % 2 ≠ 1:=by simpa using hodd
     omega
    have hsign:(-1:R)^k=1:=Even.neg_one_pow (Nat.even_iff.mpr hmod)
    rw [hsign,one_mul,Int.cast_add,add_div];linarith
lemma erfIntPosLo_le {x:ℤ} (hx:0<=x) :
  ((eP0 x:ℤ):R)/S0<=∫ u in (0:R)..((x:R)/S0),exp (-u^2/2):=by
 have hxR:(0:R)<=(x:R)/S0:=div_nonneg (by exact_mod_cast hx) fpS_pos.le
 have hx2Lo_nn:0<=dF (x*x) fpS:=Int.ediv_nonneg (mul_nonneg hx hx) (by norm_num [S0,fpS])
 have hx2Lo:((dF (x*x) fpS:ℤ):R)/S0<=((x:R)/S0)^2:=by
  rw [sq];exact mulFl_le x x
 have hx2Hi:((x:R)/S0)^2<=((dC (x*x) fpS:ℤ):R)/S0:=by
  rw [sq];exact le_mulCe x x
 have h1:=erfLoop_sound false x (dF (x*x) fpS) (dC (x*x) fpS) hx hx2Lo_nn hx2Lo hx2Hi
  15 1 1 x x x le_rfl (by simp) hx (by simp) (by simp) (by simp)
 simp only [Bool.false_eq_true,↓reduceIte] at h1
 have h2:=(erf_int_taylor_bounds ((x:R)/S0) hxR 8).1
 exact h1.trans (by simpa [eP0] using h2)
lemma le_erfIntPosHi {x:ℤ} (hx:0<=x) :
  (∫ u in (0:R)..((x:R)/S0),exp (-u^2/2))<=((eP1 x:ℤ):R)/S0:=by
 have hxR:(0:R)<=(x:R)/S0:=div_nonneg (by exact_mod_cast hx) fpS_pos.le
 have hx2Lo_nn:0<=dF (x*x) fpS:=Int.ediv_nonneg (mul_nonneg hx hx) (by norm_num [S0,fpS])
 have hx2Lo:((dF (x*x) fpS:ℤ):R)/S0<=((x:R)/S0)^2:=by
  rw [sq];exact mulFl_le x x
 have hx2Hi:((x:R)/S0)^2<=((dC (x*x) fpS:ℤ):R)/S0:=by
  rw [sq];exact le_mulCe x x
 have h1:=erfLoop_sound true x (dF (x*x) fpS) (dC (x*x) fpS) hx hx2Lo_nn hx2Lo hx2Hi
  16 1 1 x x x le_rfl (by simp) hx (by simp) (by simp) (by simp)
 simp only [↓reduceIte] at h1
 have h2:=(erf_int_taylor_bounds ((x:R)/S0) hxR 8).2
 exact h2.trans (by simpa [eP1] using h1)
lemma phiCDFLo_le_nonneg {x:ℤ} (hx:0<=x) :
  ((fpS/2+mF i20 (eP0 x):ℤ):R)/S0 <=
   pC ((x:R)/S0):=by
 have hxR:(0:R)<=(x:R)/S0:=div_nonneg (by exact_mod_cast hx) fpS_pos.le
 have hhalf:((fpS/2:ℤ):R)/S0=1/2:=by norm_num [S0,fpS]
 rw [Int.cast_add,add_div,hhalf,stdPhiCDF_eq_half_add_intervalIntegral]
 simp only [pP,intervalIntegral.integral_const_mul]
 have hint_nn:0<=∫ u in (0:R)..((x:R)/S0),exp (-u^2/2) :=
  intervalIntegral.integral_nonneg hxR fun u _=>exp_nonneg _
 have h1:=mulFl_le i20 (eP0 x)
 have h2:((i20:ℤ):R)/S0*(((eP0 x:ℤ):R)/S0) <=
   (sqrt (2*PI))⁻¹*∫ u in (0:R)..((x:R)/S0),exp (-u^2/2):=by
  by_cases hneg:((eP0 x:ℤ):R)/S0<=0
  .
   exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by norm_num [i20,S0,fpS]) hneg)
    (mul_nonneg (by positivity) hint_nn)
  . exact mul_le_mul pi_bounds_invSqrt2Pi.1 (erfIntPosLo_le hx) (le_of_not_ge hneg) (by positivity)
 linarith [h1,h2]
lemma le_phiCDFHi_nonneg {x:ℤ} (hx:0<=x) :
  pC ((x:R)/S0) <=
   ((fpS/2+mC i21 (eP1 x):ℤ):R)/S0:=by
 have hxR:(0:R)<=(x:R)/S0:=div_nonneg (by exact_mod_cast hx) fpS_pos.le
 have hhalf:((fpS/2:ℤ):R)/S0=1/2:=by norm_num [S0,fpS]
 rw [Int.cast_add,add_div,hhalf,stdPhiCDF_eq_half_add_intervalIntegral]
 simp only [pP,intervalIntegral.integral_const_mul]
 have hint_nn:0<=∫ u in (0:R)..((x:R)/S0),exp (-u^2/2) :=
  intervalIntegral.integral_nonneg hxR fun u _=>exp_nonneg _
 have h1:=le_mulCe i21 (eP1 x)
 have h2:(sqrt (2*PI))⁻¹*(∫ u in (0:R)..((x:R)/S0),exp (-u^2/2)) <=
   ((i21:ℤ):R)/S0*(((eP1 x:ℤ):R)/S0) :=
  mul_le_mul pi_bounds_invSqrt2Pi.2 (le_erfIntPosHi hx) hint_nn (by norm_num [i21,S0,fpS])
 linarith [h1,h2]
lemma phiCDFLo_le (x:ℤ) :
  ((cL x:ℤ):R)/S0<=pC ((x:R)/S0):=by
 unfold cL
 split_ifs with hx
 . exact phiCDFLo_le_nonneg hx
 .
  have hnx:0 <= -x:=by omega
  have hhi:=le_phiCDFHi_nonneg hnx
  have hneg:pC ((x:R)/S0)=1 - pC (((-x:ℤ):R)/S0):=by
   have:((x:R)/S0) = -(((-x:ℤ):R)/S0):=by simp [neg_div]
   rw [this,stdPhiCDF_neg]
  rw [hneg,Int.cast_sub,sub_div,div_self fpS_pos.ne']
  linarith
lemma le_phiCDFHi (x:ℤ) :
  pC ((x:R)/S0)<=((cH x:ℤ):R)/S0:=by
 unfold cH
 split_ifs with hx
 . exact le_phiCDFHi_nonneg hx
 .
  have hnx:0 <= -x:=by omega
  have hlo:=phiCDFLo_le_nonneg hnx
  have hneg:pC ((x:R)/S0)=1 - pC (((-x:ℤ):R)/S0):=by
   have:((x:R)/S0) = -(((-x:ℤ):R)/S0):=by simp [neg_div]
   rw [this,stdPhiCDF_neg]
  rw [hneg,Int.cast_sub,sub_div,div_self fpS_pos.ne']
  linarith
lemma phiPDFLo_le (x:ℤ) :
  ((pL x:ℤ):R)/S0<=pP ((x:R)/S0):=by
 have hs:(0:R) < S0:=fpS_pos
 have harg_le:-((dC (x*x) (2*fpS):ℤ):R)/S0 <= -((x:R)/S0)^2/2:=by
  have hd:=le_divCe (a:=x*x) (b:=2*fpS) (by norm_num [S0,fpS])
  have h1:(x:R)*(x:R)/(2*S0)<=((dC (x*x) (2*fpS):ℤ):R):=by
   simpa [Int.cast_mul] using hd
  have h2:((x:R)/S0)^2/2<=((dC (x*x) (2*fpS):ℤ):R)/S0:=by
   calc ((x:R)/S0)^2/2=((x:R)*(x:R)/(2*S0))/S0:=by field_simp
    _ <= ((dC (x*x) (2*fpS):ℤ):R)/S0:=dld h1 hs.le
  rw [neg_div,neg_div]
  linarith
 have hce_nn:0<=dC (x*x) (2*fpS):=by
  have h0:(0:R)<=((dC (x*x) (2*fpS):ℤ):R) :=
   le_trans (div_nonneg (by exact_mod_cast mul_self_nonneg x) (by norm_num [S0,fpS]))
    (le_divCe (a:=x*x) (b:=2*fpS) (by norm_num [S0,fpS]))
  exact_mod_cast h0
 have hexp_le:((eL (-dC (x*x) (2*fpS)):ℤ):R)/S0 <=
   exp (-((x:R)/S0)^2/2):=by
  have h1:=expNegLo_le (x:=-dC (x*x) (2*fpS)) (by omega)
  have h2:((-dC (x*x) (2*fpS):ℤ):R)/S0 = -((dC (x*x) (2*fpS):ℤ):R)/S0:=by
   simp [neg_div]
  rw [h2] at h1
  exact h1.trans (exp_le_exp.mpr harg_le)
 unfold pL pP
 have h1:=mulFl_le i20 (eL (-dC (x*x) (2*fpS)))
 have h2:((i20:ℤ):R)/S0*(((eL (-dC (x*x) (2*fpS)):ℤ):R)/S0) <=
   (sqrt (2*PI))⁻¹*exp (-((x:R)/S0)^2/2):=by
  by_cases hneg:((eL (-dC (x*x) (2*fpS)):ℤ):R)/S0<=0
  .
   exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by norm_num [i20,S0,fpS]) hneg)
    (mul_nonneg (by positivity) (exp_nonneg _))
  . exact mul_le_mul pi_bounds_invSqrt2Pi.1 hexp_le (le_of_not_ge hneg) (by positivity)
 exact h1.trans h2
lemma le_phiPDFHi (x:ℤ) :
  pP ((x:R)/S0)<=((pH x:ℤ):R)/S0:=by
 have hs:(0:R) < S0:=fpS_pos
 have harg_ge:-((x:R)/S0)^2/2 <= -((dF (x*x) (2*fpS):ℤ):R)/S0:=by
  have hd:=divFl_le (a:=x*x) (b:=2*fpS) (by norm_num [S0,fpS])
  have h1:((dF (x*x) (2*fpS):ℤ):R)<=(x:R)*(x:R)/(2*S0):=by
   simpa [Int.cast_mul] using hd
  have h2:((dF (x*x) (2*fpS):ℤ):R)/S0<=((x:R)/S0)^2/2:=by
   calc ((dF (x*x) (2*fpS):ℤ):R)/S0
     <= ((x:R)*(x:R)/(2*S0))/S0:=dld h1 hs.le
    _ = ((x:R)/S0)^2/2:=by field_simp
  rw [neg_div,neg_div]
  linarith
 have hfl_nn:0<=dF (x*x) (2*fpS):=Int.ediv_nonneg (mul_self_nonneg x) (by norm_num [S0,fpS])
 have hexp_ge:exp (-((x:R)/S0)^2/2) <=
   ((eH (-dF (x*x) (2*fpS)):ℤ):R)/S0:=by
  have h1:=le_expNegHi (x:=-dF (x*x) (2*fpS)) (by omega)
  have h2:((-dF (x*x) (2*fpS):ℤ):R)/S0 = -((dF (x*x) (2*fpS):ℤ):R)/S0:=by
   simp [neg_div]
  rw [h2] at h1
  exact (exp_le_exp.mpr harg_ge).trans h1
 unfold pH pP
 have h1:=le_mulCe i21 (eH (-dF (x*x) (2*fpS)))
 have h2:(sqrt (2*PI))⁻¹*exp (-((x:R)/S0)^2/2) <=
   ((i21:ℤ):R)/S0*(((eH (-dF (x*x) (2*fpS)):ℤ):R)/S0) :=
  mul_le_mul pi_bounds_invSqrt2Pi.2 hexp_ge (exp_nonneg _) (by norm_num [i21,S0,fpS])
 exact h2.trans h1
lemma hasDerivAt_comp_fun {f g:R->R} {f' g' x:R}
  (hf:HD f f' (g x)) (hg:HD g g' x) :
  HD (fun y=>f (g y)) (f'*g') x :=
 hf.comp x hg
lemma stdPhiCDF_tendsto_one:Tendsto pC atTop (𝓝 1):=by
 have h1:Tendsto (fun z:R=>∫ t in Set.Iic z,pP t) atTop (𝓝 (∫ t:R,pP t)):=by
  simp_rw [← integral_indicator measurableSet_Iic]
  refine tendsto_integral_filter_of_dominated_convergence pP ?_ ?_ ipP ?_
  .
   exact Eventually.of_forall fun z =>
    (ipP.aestronglyMeasurable).indicator measurableSet_Iic
  .
   exact Eventually.of_forall fun z=>ae_of_all _ fun t=>by
    rw [Real.norm_eq_abs,aon (Set.indicator_nonneg (fun _ _=>pPn _) _)]
    exact Set.indicator_le_self' (fun _ _=>pPn _) t
  .
   exact ae_of_all _ fun t=>tendsto_const_nhds.congr' (by
    filter_upwards [eventually_ge_atTop t] with z hz
    simp [Set.indicator,hz])
 rw [integral_stdPhiPDF_univ] at h1
 simpa only [← stdPhiCDF_eq_integral] using h1
lemma integrableOn_abs_mul_stdPhiPDF_Ioi :
  IntegrableOn (fun u:R=>|u| * pP u) (Set.Ioi 0):=by
 have hgauss:IntegrableOn (fun u:R=>u*exp (-u^2/2)) (Set.Ioi 0):=by
  have hd:∀ u ∈ Set.Ioi (0:R),
    HD (fun v:R=>-exp (-v^2/2)) (u*exp (-u^2/2)) u:=by
   intro u _
   have h1:HD (fun v:R=>-v^2/2) (-u) u:=by
    have ha:HD (fun v:R=>-(v^2)) (-(2*u^1)) u :=
     (hdp 2 u).fun_neg
    have hb:=ha.div_const 2
    rwa [show -(2*u^1)/2 = -u by ring] at hb
   have h2:=(hasDerivAt_comp_fun (f:=exp) (g:=fun v:R=>-v^2/2)
    (hasDerivAt_exp (-u^2/2)) h1).fun_neg
   rwa [show -(exp (-u^2/2) * -u)=u*exp (-u^2/2) by ring] at h2
  have htend:Tendsto (fun v:R=>-exp (-v^2/2)) atTop (𝓝 0):=by
   have hsq:Tendsto (fun v:R=>v^2/2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num:2 ≠ 0)).atTop_div_const (by norm_num)
   have hneg:Tendsto (fun v:R=>-(v^2/2)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hsq
   have hneg':Tendsto (fun v:R=>-v^2/2) atTop atBot:=by
    simpa [neg_div] using hneg
   simpa using (tendsto_exp_atBot.comp hneg').neg
  exact integrableOn_Ioi_deriv_of_nonneg (Continuous.continuousWithinAt (by fun_prop))
   hd (fun u hu=>by have:0 < u:=hu;positivity) htend
 have hmul:IntegrableOn (fun u:R=>(sqrt (2*PI))⁻¹*(u*exp (-u^2/2))) (Set.Ioi 0) :=
  hgauss.const_mul (sqrt (2*PI))⁻¹
 refine hmul.congr_fun (fun u hu=>?_) measurableSet_Ioi
 have hup:0 < u:=hu
 unfold pP
 rw [abs_of_pos hup];ring
noncomputable def bP (β c:R):R :=
 1 - 2*∫ u in Set.Ioi (0:R),pC ((sqrt (1 - β)*u+c)/sqrt β)*pP u
lemma bivProb_integrand_integrable (β c:R) :
  IntegrableOn (fun u:R=>pC ((sqrt (1 - β)*u+c)/sqrt β)*pP u)
   (Set.Ioi (0:R)):=by
 refine ipP.integrableOn.mono' ?_ ?_
 .
  have hc:Continuous (fun u:R=>pC ((sqrt (1 - β)*u+c)/sqrt β)*pP u):=by
   have h1:Continuous pC :=
    continuous_iff_continuousAt.mpr fun x=>(pCd x).continuousAt
   have h2:Continuous pP:=by unfold pP;fun_prop
   fun_prop
  exact hc.aestronglyMeasurable
 .
  filter_upwards with u
  rw [Real.norm_eq_abs,abs_mul,aon (pCp _).le,
   aon (pPn _)]
  exact mul_le_of_le_one_left (pPn u) (stdPhiCDF_lt_one _).le
lemma bivProb_half (c:R):bP (1/2) c=(pC (-c))^2:=by
 have hF_eq:∀ x:R,bP (1/2) x =
   1 - 2*∫ u in Set.Ioi (0:R),pC (u+sqrt 2*x)*pP u:=by
  intro x
  unfold bP
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioi fun u _=>?_
  have h12:(1:R) - 1/2=1/2:=by norm_num
  rw [h12]
  have hsq:sqrt (1/2:R) ≠ 0:=by positivity
  have hmul:(sqrt (1/2:R)*u+x)/sqrt (1/2:R)=u+sqrt 2*x:=by
   have hinv:(sqrt (1/2:R))⁻¹=sqrt 2:=by
    rw [one_div,sqrt_inv,inv_inv]
   rw [add_div,mul_div_cancel_left₀ _ hsq,div_eq_mul_inv,hinv,mul_comm]
  rw [hmul]
 have hderiv_biv:∀ x:R,HD (fun y=>bP (1/2) y)
   (-2*pP x*pC (-x)) x:=by
  intro x
  have hfun:(fun y=>bP (1/2) y) =
    fun y=>1 - 2*∫ u in Set.Ioi (0:R),pC (u+sqrt 2*y)*pP u :=
   funext hF_eq
  rw [hfun]
  have hint_deriv:HD
    (fun y=>∫ u in Set.Ioi (0:R),pC (u+sqrt 2*y)*pP u)
    (∫ u in Set.Ioi (0:R),sqrt 2*pP (u+sqrt 2*x)*pP u) x:=by
   refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=fun y u=>pC (u+sqrt 2*y)*pP u)
    (F':=fun y u=>sqrt 2*pP (u+sqrt 2*y)*pP u)
    (bound:=fun u=>sqrt 2*(sqrt (2*PI))⁻¹*pP u)
    (s:=Set.univ) (x₀:=x) (μ:=volume.restrict (Set.Ioi (0:R)))
    Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_).2
   .
    exact Eventually.of_forall fun y=>by
     have hc:Continuous (fun u:R=>pC (u+sqrt 2*y)*pP u):=by
      have h1:Continuous pC :=
       continuous_iff_continuousAt.mpr fun z=>(pCd z).continuousAt
      have h2:Continuous pP:=by unfold pP;fun_prop
      fun_prop
     exact hc.aestronglyMeasurable
   .
    refine ipP.integrableOn.mono' ?_ ?_
    .
     have hc:Continuous (fun u:R=>pC (u+sqrt 2*x)*pP u):=by
      have h1:Continuous pC :=
       continuous_iff_continuousAt.mpr fun z=>(pCd z).continuousAt
      have h2:Continuous pP:=by unfold pP;fun_prop
      fun_prop
     exact hc.aestronglyMeasurable
    .
     filter_upwards with u
     rw [Real.norm_eq_abs,abs_mul,aon (pCp _).le,
      aon (pPn _)]
     exact mul_le_of_le_one_left (pPn u) (stdPhiCDF_lt_one _).le
   .
    have hc:Continuous (fun u:R=>sqrt 2*pP (u+sqrt 2*x)*pP u):=by
     have h2:Continuous pP:=by unfold pP;fun_prop
     fun_prop
    exact hc.aestronglyMeasurable
   .
    filter_upwards with u y _
    rw [Real.norm_eq_abs,abs_mul,abs_mul,aon (sqrt_nonneg 2),
     aon (pPn _),aon (pPn _)]
    have h1:=stdPhiPDF_le_inv_sqrt_two_pi (u+sqrt 2*y)
    exact mlR
     (mlL h1 (sqrt_nonneg 2)) (pPn u)
   . exact (ipP.const_mul _).integrableOn
   .
    filter_upwards with u y _
    have hlin:HD (fun z:R=>u+sqrt 2*z) (sqrt 2) y:=by
     simpa using (hasDerivAt_const y u).fun_add ((hdi y).const_mul (sqrt 2))
    have hcomp:HD (fun z:R=>pC (u+sqrt 2*z))
      (pP (u+sqrt 2*y)*sqrt 2) y :=
     hasDerivAt_comp_fun (pCd (u+sqrt 2*y)) hlin
    have hc:=hcomp.mul_const (pP u)
    rwa [show pP (u+sqrt 2*y)*sqrt 2*pP u =
      sqrt 2*pP (u+sqrt 2*y)*pP u by ring] at hc
  have heval:∫ u in Set.Ioi (0:R),sqrt 2*pP (u+sqrt 2*x)*pP u =
    pP x*pC (-x):=by
   have hpt:∀ u:R,
     sqrt 2*pP (u+sqrt 2*x)*pP u =
     pP x*(sqrt 2*pP (sqrt 2*u+x)):=by
    intro u
    unfold pP
    have hsq2:sqrt 2^2=2:=sq_sqrt (by norm_num)
    have hexp:-((u+sqrt 2*x)^2)/2 + -u^2/2 =
      -x^2/2 + -((sqrt 2*u+x)^2)/2:=by
     nlinarith [hsq2]
    calc sqrt 2*((sqrt (2*PI))⁻¹*exp (-(u+sqrt 2*x)^2/2)) *
       ((sqrt (2*PI))⁻¹*exp (-u^2/2))
      = sqrt 2*(sqrt (2*PI))⁻¹*(sqrt (2*PI))⁻¹ *
       (exp (-(u+sqrt 2*x)^2/2)*exp (-u^2/2)):=by ring
     _ = sqrt 2*(sqrt (2*PI))⁻¹*(sqrt (2*PI))⁻¹ *
       exp (-(u+sqrt 2*x)^2/2 + -u^2/2):=by rw [← exp_add]
     _ = sqrt 2*(sqrt (2*PI))⁻¹*(sqrt (2*PI))⁻¹ *
       exp (-x^2/2 + -(sqrt 2*u+x)^2/2):=by rw [hexp]
     _ = sqrt 2*(sqrt (2*PI))⁻¹*(sqrt (2*PI))⁻¹ *
       (exp (-x^2/2)*exp (-(sqrt 2*u+x)^2/2)):=by rw [exp_add]
     _ = (sqrt (2*PI))⁻¹*exp (-x^2/2) *
       (sqrt 2*((sqrt (2*PI))⁻¹*exp (-(sqrt 2*u+x)^2/2))):=by ring
   simp_rw [hpt,integral_const_mul]
   congr 1
   have hd_u:∀ u ∈ Set.Ioi (0:R),
     HD (fun v:R=>pC (sqrt 2*v+x))
      (sqrt 2*pP (sqrt 2*u+x)) u:=by
    intro u _
    have hlin:HD (fun v:R=>sqrt 2*v+x) (sqrt 2) u:=by
     simpa using ((hdi u).const_mul (sqrt 2)).fun_add (hasDerivAt_const u x)
    have hcomp:HD (fun v:R=>pC (sqrt 2*v+x))
      (pP (sqrt 2*u+x)*sqrt 2) u :=
     hasDerivAt_comp_fun (pCd (sqrt 2*u+x)) hlin
    rwa [mul_comm] at hcomp
   have hcont_at0:ContinuousWithinAt (fun v:R=>pC (sqrt 2*v+x)) (Set.Ici 0) 0:=by
    have hc:Continuous (fun v:R=>pC (sqrt 2*v+x)):=by
     have h1:Continuous pC :=
      continuous_iff_continuousAt.mpr fun z=>(pCd z).continuousAt
     fun_prop
    exact hc.continuousWithinAt
   have htend:Tendsto (fun v:R=>pC (sqrt 2*v+x)) atTop (𝓝 1) :=
    stdPhiCDF_tendsto_one.comp
     ((tendsto_id.const_mul_atTop (sqrt_pos.mpr (by norm_num))).atTop_add tendsto_const_nhds)
   have hint_u:IntegrableOn (fun u:R=>sqrt 2*pP (sqrt 2*u+x)) (Set.Ioi 0):=by
    have h1:Integrable (fun z:R=>pP (z+x)):=ipP.comp_add_right x
    have h2:Integrable (fun u:R=>pP (sqrt 2*u+x)) :=
     h1.comp_mul_left' (sqrt_pos.mpr (by norm_num)).ne'
    exact (h2.const_mul (sqrt 2)).integrableOn
   have hftc:=integral_Ioi_of_hasDerivAt_of_tendsto hcont_at0 hd_u hint_u htend
   simp only [mul_zero,zero_add] at hftc
   rw [← integral_const_mul,hftc,stdPhiCDF_neg]
  rw [heval] at hint_deriv
  have htot:HD (fun y:R=>1 - 2*∫ u in Set.Ioi (0:R),pC (u+sqrt 2*y)*pP u)
    (0 - 2*(pP x*pC (-x))) x :=
   (hasDerivAt_const x (1:R)).fun_sub (hint_deriv.const_mul 2)
  rwa [show 0 - 2*(pP x*pC (-x)) = -2*pP x*pC (-x) by ring] at htot
 have hderiv_sq:∀ x:R,HD (fun y=>(pC (-y))^2)
   (-2*pP x*pC (-x)) x:=by
  intro x
  have h1:HD (fun y:R=>pC (-y)) (pP (-x)*(-1)) x :=
   HasDerivAt.comp x (pCd (-x)) (hasDerivAt_neg x)
  have h2:=h1.fun_pow 2
  rw [stdPhiPDF_even] at h2
  have heq:((2:ℕ):R)*pC (-x)^(2 - 1)*(pP x * -1) =
    -2*pP x*pC (-x):=by norm_num;ring
  rwa [heq] at h2
 have hdiff_const:∀ x:R,bP (1/2) x - (pC (-x))^2 =
   bP (1/2) 0 - (pC (-0))^2:=by
  intro x
  refine is_const_of_deriv_eq_zero (f:=fun y=>bP (1/2) y - (pC (-y))^2)
   (fun y=>((hderiv_biv y).fun_sub (hderiv_sq y)).differentiableAt)
   (fun y=>by rw [((hderiv_biv y).fun_sub (hderiv_sq y)).deriv];ring) x 0
 have h0:bP (1/2) 0=1/4:=by
  rw [hF_eq 0]
  simp only [mul_zero,add_zero]
  have hd_u:∀ u ∈ Set.Ioi (0:R),
    HD (fun v:R=>(pC v)^2/2) (pC u*pP u) u:=by
   intro u _
   have h:=((pCd u).fun_pow 2).div_const 2
   have heq:((2:ℕ):R)*pC u^(2 - 1)*pP u/2 =
     pC u*pP u:=by norm_num;ring
   rwa [heq] at h
  have hcont0:ContinuousWithinAt (fun v:R=>(pC v)^2/2) (Set.Ici 0) 0:=by
   have hc:Continuous pC :=
    continuous_iff_continuousAt.mpr fun z=>(pCd z).continuousAt
   exact ((hc.pow 2).div_const 2).continuousWithinAt
  have htend:Tendsto (fun v:R=>(pC v)^2/2) atTop (𝓝 (1/2)):=by
   simpa using (stdPhiCDF_tendsto_one.pow 2).div_const 2
  have hint0:IntegrableOn (fun u:R=>pC u*pP u) (Set.Ioi 0):=by
   have h:=bivProb_integrand_integrable (1/2) 0
   refine h.congr_fun (fun u _=>?_) measurableSet_Ioi
   dsimp only
   have h12:(1:R) - 1/2=1/2:=by norm_num
   have hsq:sqrt (1/2:R) ≠ 0:=by positivity
   rw [add_zero,h12,mul_div_cancel_left₀ _ hsq]
  have hftc:=integral_Ioi_of_hasDerivAt_of_tendsto hcont0 hd_u hint0 htend
  rw [hftc,stdPhiCDF_zero]
  norm_num
 have hc0:=hdiff_const c
 rw [h0,neg_zero,stdPhiCDF_zero] at hc0
 linarith
lemma bPd (c:R) {β:R} (hβ0:0 < β) (hβ1:β < 1) :
  HD (fun b=>bP b c)
   ((2*PI*sqrt (β*(1 - β)))⁻¹*exp (-c^2/(2*β))) β:=by
 let δ:R:=min (β / 2) ((1 - β)/2)
 have hδ:0 < δ:=lt_min (by linarith) (by linarith)
 have hs_mem:Metric.ball β δ ∈ 𝓝 β:=Metric.ball_mem_nhds β hδ
 have hb_bounds:∀ b ∈ Metric.ball β δ,β / 2 < b/\b < (1+β)/2/\0 < b/\b < 1/\(1 - β)/2 < 1 - b:=by
  intro b hb
  rw [Metric.mem_ball,Real.dist_eq,abs_lt] at hb
  have h1:δ<=β / 2:=min_le_left _ _
  have h2:δ<=(1 - β)/2:=min_le_right _ _
  refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
 let w:R->R->R:=fun b u=>(sqrt (1 - b)*u+c)/sqrt b
 let w':R->R->R:=fun b u=>-(u+c*sqrt (1 - b))/(2*b*sqrt b*sqrt (1 - b))
 have hw_deriv:∀ u:R,∀ b ∈ Metric.ball β δ,HD (fun y=>w y u) (w' b u) b:=by
  intro u b hb
  obtain ⟨_,_,hb0,hb1,_⟩:=hb_bounds b hb
  have h1b:0 < 1 - b:=by linarith
  have hd_num:HD (fun y=>sqrt (1 - y)*u+c)
    ((-(1/(2*sqrt (1 - b))))*u) b:=by
   have h1:HD (fun y:R=>1 - y) (-1) b:=by
    simpa using (hasDerivAt_const b (1:R)).fun_sub (hdi b)
   have hcomp:HD (fun y:R=>sqrt (1 - y)) ((1/(2*sqrt (1 - b)))*(-1)) b :=
    HasDerivAt.comp b (hasDerivAt_sqrt h1b.ne') h1
   have h3:=(hcomp.mul_const u).fun_add (hasDerivAt_const b c)
   rwa [show 1/(2*sqrt (1 - b)) * -1*u+0=(-(1/(2*sqrt (1 - b))))*u by ring] at h3
  have hd_den:HD (fun y=>sqrt y) (1/(2*sqrt b)) b:=by
   simpa [one_div] using hasDerivAt_sqrt hb0.ne'
  have hq:=hd_num.fun_div hd_den (sqrt_pos.mpr hb0).ne'
  have hq_eq:(-(1/(2*sqrt (1 - b)))*u*sqrt b -
    (sqrt (1 - b)*u+c)*(1/(2*sqrt b)))/sqrt b^2=w' b u:=by
   unfold w'
   have hsb:sqrt b ≠ 0:=(sqrt_pos.mpr hb0).ne'
   have hs1b:sqrt (1 - b) ≠ 0:=(sqrt_pos.mpr h1b).ne'
   have hsqb:sqrt b^2=b:=sq_sqrt hb0.le
   have hsq1b:sqrt (1 - b)^2=1 - b:=sq_sqrt h1b.le
   rw [hsqb]
   field_simp
   rw [hsqb]
   have hsq1b':sqrt (1 - b)*(sqrt (1 - b)*u+c) =
     (1 - b)*u+sqrt (1 - b)*c:=by
    calc sqrt (1 - b)*(sqrt (1 - b)*u+c)
      = sqrt (1 - b)^2*u+sqrt (1 - b)*c:=by ring
     _ = (1 - b)*u+sqrt (1 - b)*c:=by rw [hsq1b]
   linarith
  rwa [hq_eq] at hq
 have hint_deriv:HD
   (fun b=>∫ u in Set.Ioi (0:R),pC (w b u)*pP u)
   (∫ u in Set.Ioi (0:R),pP (w β u)*w' β u*pP u) β:=by
  let C:R:=(sqrt (2*PI))⁻¹*(2*(β / 2)*sqrt (β / 2)*sqrt ((1 - β)/2))⁻¹
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
   (F:=fun b u=>pC (w b u)*pP u)
   (F':=fun b u=>pP (w b u)*w' b u*pP u)
   (bound:=fun u=>C*(|u| + |c|)*pP u)
   (s:=Metric.ball β δ) (x₀:=β) (μ:=volume.restrict (Set.Ioi (0:R)))
   hs_mem ?_ ?_ ?_ ?_ ?_ ?_).2
  . exact Eventually.of_forall fun b=>(bivProb_integrand_integrable b c).aestronglyMeasurable
  . exact bivProb_integrand_integrable β c
  .
   have hc:Continuous (fun u:R=>pP (w β u)*w' β u*pP u):=by
    unfold w w' pP;fun_prop
   exact hc.aestronglyMeasurable
  .
   filter_upwards with u b hb
   obtain ⟨hb_lo,_,hb0,hb1,h1b_lo⟩:=hb_bounds b hb
   have h1b:0 < 1 - b:=by linarith
   rw [Real.norm_eq_abs,abs_mul,abs_mul,aon (pPn _),
    aon (pPn _)]
   have hden_ge:2*(β / 2)*sqrt (β / 2)*sqrt ((1 - β)/2) <=
     2*b*sqrt b*sqrt (1 - b):=by
    have h1:sqrt (β / 2)<=sqrt b:=sqrt_le_sqrt hb_lo.le
    have h2:sqrt ((1 - β)/2)<=sqrt (1 - b):=sqrt_le_sqrt h1b_lo.le
    have h3:0<=sqrt (β / 2):=sqrt_nonneg _
    have h4:0<=sqrt ((1 - β)/2):=sqrt_nonneg _
    have h5:0 < β / 2:=by linarith
    have h6:0<=2*b*sqrt b:=by positivity
    nlinarith [mul_le_mul (mul_le_mul (by linarith:2*(β / 2)<=2*b) h1 h3 (by linarith)) h2 h4 h6]
   have hden_pos:0 < 2*(β / 2)*sqrt (β / 2)*sqrt ((1 - β)/2):=by positivity
   have hw'_le:|w' b u| <= (|u| + |c|)*(2*(β / 2)*sqrt (β / 2)*sqrt ((1 - β)/2))⁻¹:=by
    unfold w'
    rw [abs_div,abs_neg,abs_of_pos (by positivity:0 < 2*b*sqrt b*sqrt (1 - b)),div_eq_mul_inv]
    have hnum:|u+c*sqrt (1 - b)| <= |u| + |c| := by
     calc |u+c*sqrt (1 - b)| <= |u| + |c*sqrt (1 - b)| := abs_add_le _ _
      _ = |u| + |c| * sqrt (1 - b):=by rw [abs_mul,aon (sqrt_nonneg _)]
      _ <= |u| + |c| * 1:=by
        have hsq1:sqrt (1 - b)<=1:=by
         rw [sqrt_le_one];linarith
        nlinarith [abs_nonneg c]
      _ = |u| + |c| := by ring
    have hinv_le:(2*b*sqrt b*sqrt (1 - b))⁻¹ <=
      (2*(β / 2)*sqrt (β / 2)*sqrt ((1 - β)/2))⁻¹ :=
     inv_anti₀ hden_pos hden_ge
    exact mul_le_mul hnum hinv_le (by positivity) (by positivity)
   have hphi_le:=stdPhiPDF_le_inv_sqrt_two_pi (w b u)
   have hprod:pP (w b u) * |w' b u| <= C*(|u| + |c|):=by
    calc pP (w b u) * |w' b u|
      <= (sqrt (2*PI))⁻¹ *
       ((|u| + |c|)*(2*(β / 2)*sqrt (β / 2)*sqrt ((1 - β)/2))⁻¹) :=
       mul_le_mul hphi_le hw'_le (abs_nonneg _) (by positivity)
     _ = C*(|u| + |c|):=by ring
   exact mlR hprod (pPn u)
  .
   have h1:IntegrableOn (fun u:R=>C*(|u| * pP u)) (Set.Ioi 0) :=
    integrableOn_abs_mul_stdPhiPDF_Ioi.const_mul C
   have h2:IntegrableOn (fun u:R=>(C * |c|)*pP u) (Set.Ioi 0) :=
    (ipP.const_mul (C * |c|)).integrableOn
   have h3:IntegrableOn (fun u:R=>C*(|u| * pP u)+C * |c| * pP u) (Set.Ioi 0) :=
    h1.add h2
   exact h3.congr_fun (fun u _=>by ring) measurableSet_Ioi
  .
   filter_upwards with u b hb
   have hcomp:HD (fun y:R=>pC (w y u)) (pP (w b u)*w' b u) b :=
    hasDerivAt_comp_fun (pCd (w b u)) (hw_deriv u b hb)
   exact hcomp.mul_const (pP u)
 have h1β:0 < 1 - β:=by linarith
 have heval:∫ u in Set.Ioi (0:R),pP (w β u)*w' β u*pP u =
   -(4*PI*sqrt (β*(1 - β)))⁻¹*exp (-c^2/(2*β)):=by
  let K:R:=(4*PI*sqrt (β*(1 - β)))⁻¹*exp (-c^2/2)
  let G:R->R:=fun u=>K*exp (-(u+c*sqrt (1 - β))^2/(2*β))
  have hpt:∀ u:R,pP (w β u)*w' β u*pP u =
    K*((-(u+c*sqrt (1 - β)) / β)*exp (-(u+c*sqrt (1 - β))^2/(2*β))):=by
   intro u
   unfold pP w w' K
   have hsb:sqrt β ≠ 0:=(sqrt_pos.mpr hβ0).ne'
   have hs1b:sqrt (1 - β) ≠ 0:=(sqrt_pos.mpr h1β).ne'
   have hsqb:sqrt β^2=β:=sq_sqrt hβ0.le
   have hsq1b:sqrt (1 - β)^2=1 - β:=sq_sqrt h1β.le
   have hsq2pi:sqrt (2*PI)^2=2*PI:=sq_sqrt (by positivity)
   have hinv2pi:(sqrt (2*PI))⁻¹*(sqrt (2*PI))⁻¹=(2*PI)⁻¹:=by
    rw [← mul_inv,← sq,hsq2pi]
   have hsqrt_mul:sqrt (β*(1 - β))=sqrt β*sqrt (1 - β) :=
    sqrt_mul hβ0.le (1 - β)
   have hexp:-(((sqrt (1 - β)*u+c)/sqrt β)^2)/2 + -u^2/2 =
     -c^2/2 + -(u+c*sqrt (1 - β))^2/(2*β):=by
    rw [div_pow,hsqb]
    field_simp
    nlinarith [hsq1b]
   have hE:exp (-(((sqrt (1 - β)*u+c)/sqrt β)^2)/2)*exp (-u^2/2) =
     exp (-c^2/2)*exp (-(u+c*sqrt (1 - β))^2/(2*β)):=by
    rw [← exp_add,hexp,exp_add]
   calc (sqrt (2*PI))⁻¹*exp (-((sqrt (1 - β)*u+c)/sqrt β)^2/2) *
      (-(u+c*sqrt (1 - β))/(2*β*sqrt β*sqrt (1 - β))) *
      ((sqrt (2*PI))⁻¹*exp (-u^2/2))
     = ((sqrt (2*PI))⁻¹*(sqrt (2*PI))⁻¹) *
      (-(u+c*sqrt (1 - β))/(2*β*sqrt β*sqrt (1 - β))) *
      (exp (-((sqrt (1 - β)*u+c)/sqrt β)^2/2)*exp (-u^2/2)):=by ring
    _ = (2*PI)⁻¹ *
      (-(u+c*sqrt (1 - β))/(2*β*sqrt β*sqrt (1 - β))) *
      (exp (-c^2/2)*exp (-(u+c*sqrt (1 - β))^2/(2*β))):=by
      rw [hinv2pi,hE]
    _ = (4*PI*sqrt (β*(1 - β)))⁻¹*exp (-c^2/2) *
      (-(u+c*sqrt (1 - β)) / β*exp (-(u+c*sqrt (1 - β))^2/(2*β))):=by
      rw [hsqrt_mul]
      have hpi:PI ≠ 0:=pi_ne_zero
      field_simp
      ring
  have hGd:∀ u ∈ Set.Ioi (0:R),HD G (pP (w β u)*w' β u*pP u) u:=by
   intro u _
   rw [hpt u]
   have h1:HD (fun v:R=>-(v+c*sqrt (1 - β))^2/(2*β))
     (-(u+c*sqrt (1 - β)) / β) u:=by
    have ha:HD (fun v:R=>v+c*sqrt (1 - β)) 1 u:=by
     have h:=(hdi u).fun_add (hasDerivAt_const u (c*sqrt (1 - β)))
     rwa [add_zero] at h
    have hb:=((ha.fun_pow 2).fun_neg).div_const (2*β)
    have hbeq:-(((2:ℕ):R)*(u+c*sqrt (1 - β))^(2 - 1)*1)/(2*β) =
      -(u+c*sqrt (1 - β)) / β:=by
     have hβne:β ≠ 0:=hβ0.ne'
     norm_num;field_simp;ring
    rwa [hbeq] at hb
   have h2:HD (fun v:R=>exp (-(v+c*sqrt (1 - β))^2/(2*β)))
     (exp (-(u+c*sqrt (1 - β))^2/(2*β))*(-(u+c*sqrt (1 - β)) / β)) u :=
    HasDerivAt.comp u (hasDerivAt_exp _) h1
   have h3:=h2.const_mul K
   rwa [show K*(exp (-(u+c*sqrt (1 - β))^2/(2*β))*(-(u+c*sqrt (1 - β)) / β)) =
     K*(-(u+c*sqrt (1 - β)) / β*exp (-(u+c*sqrt (1 - β))^2/(2*β))) by ring] at h3
  have hGcont:ContinuousWithinAt G (Set.Ici 0) 0:=by
   have hc:Continuous G:=by unfold G;fun_prop
   exact hc.continuousWithinAt
  have hGtop:Tendsto G atTop (𝓝 0):=by
   have hlin:Tendsto (fun v:R=>v+c*sqrt (1 - β)) atTop atTop :=
    tendsto_id.atTop_add tendsto_const_nhds
   have hsq:Tendsto (fun v:R=>(v+c*sqrt (1 - β))^2/(2*β)) atTop atTop :=
    ((tendsto_pow_atTop (by norm_num:2 ≠ 0)).comp hlin).atTop_div_const (by linarith)
   have hneg:Tendsto (fun v:R=>-((v+c*sqrt (1 - β))^2/(2*β))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hsq
   have ht1:Tendsto (fun v:R=>-(v+c*sqrt (1 - β))^2/(2*β)) atTop atBot:=by
    simpa [neg_div] using hneg
   simpa using (tendsto_exp_atBot.comp ht1).const_mul K
  have hint_G':IntegrableOn (fun u:R=>pP (w β u)*w' β u*pP u) (Set.Ioi 0):=by
   have hbound:IntegrableOn (fun u:R=>(sqrt (2*PI))⁻¹ *
     ((|u| + |c|)/(2*β*sqrt β*sqrt (1 - β)))*pP u) (Set.Ioi 0):=by
    have h2:IntegrableOn (fun u:R=>|c| * pP u) (Set.Ioi 0) :=
     (ipP.const_mul |c|).integrableOn
    have h3:IntegrableOn (fun u:R =>
      ((sqrt (2*PI))⁻¹ / (2*β*sqrt β*sqrt (1 - β))) *
      (|u| * pP u + |c| * pP u)) (Set.Ioi 0) :=
     (integrableOn_abs_mul_stdPhiPDF_Ioi.add h2).const_mul _
    exact h3.congr_fun (fun u _=>by ring) measurableSet_Ioi
   refine hbound.mono' ?_ ?_
   .
    have hc:Continuous (fun u:R=>pP (w β u)*w' β u*pP u):=by
     unfold w w' pP;fun_prop
    exact hc.aestronglyMeasurable
   .
    filter_upwards with u
    rw [Real.norm_eq_abs,abs_mul,abs_mul,aon (pPn _),
     aon (pPn _)]
    have hnum:|u+c*sqrt (1 - β)| <= |u| + |c| := by
     calc |u+c*sqrt (1 - β)| <= |u| + |c*sqrt (1 - β)| := abs_add_le _ _
      _ = |u| + |c| * sqrt (1 - β):=by rw [abs_mul,aon (sqrt_nonneg _)]
      _ <= |u| + |c| * 1:=by
        have:sqrt (1 - β)<=1:=by rw [sqrt_le_one];linarith
        nlinarith [abs_nonneg c]
      _ = |u| + |c| := by ring
    have hw'_le:|w' β u| <= (|u| + |c|)/(2*β*sqrt β*sqrt (1 - β)):=by
     unfold w'
     rw [abs_div,abs_neg,abs_of_pos (by positivity:0 < 2*β*sqrt β*sqrt (1 - β))]
     exact dld hnum (by positivity)
    have hprod:=mul_le_mul (stdPhiPDF_le_inv_sqrt_two_pi (w β u)) hw'_le (abs_nonneg _) (by positivity)
    exact mlR hprod (pPn u)
  have hftc:=integral_Ioi_of_hasDerivAt_of_tendsto hGcont hGd hint_G' hGtop
  rw [hftc,zero_sub]
  unfold G K
  simp only [zero_add]
  have hsq1b:sqrt (1 - β)^2=1 - β:=sq_sqrt h1β.le
  have hexp0:-c^2/2 + -(c*sqrt (1 - β))^2/(2*β) = -c^2/(2*β):=by
   rw [mul_pow,hsq1b]
   field_simp
   ring
  calc -((4*PI*sqrt (β*(1 - β)))⁻¹*exp (-c^2/2) *
     exp (-(c*sqrt (1 - β))^2/(2*β)))
    = -(4*PI*sqrt (β*(1 - β)))⁻¹ *
     (exp (-c^2/2)*exp (-(c*sqrt (1 - β))^2/(2*β))):=by ring
   _ = -(4*PI*sqrt (β*(1 - β)))⁻¹*exp (-c^2/(2*β)):=by
     rw [← exp_add,hexp0]
 rw [heval] at hint_deriv
 have htot:HD (fun b=>bP b c)
   (0 - 2*(-(4*PI*sqrt (β*(1 - β)))⁻¹*exp (-c^2/(2*β)))) β :=
  (hasDerivAt_const β (1:R)).fun_sub (hint_deriv.const_mul 2)
 have htoteq:0 - 2*(-(4*PI*sqrt (β*(1 - β)))⁻¹*exp (-c^2/(2*β))) =
   (2*PI*sqrt (β*(1 - β)))⁻¹*exp (-c^2/(2*β)):=by
  have hpi:PI ≠ 0:=pi_ne_zero
  have hsq:sqrt (β*(1 - β)) ≠ 0:=(sqrt_pos.mpr (mul_pos hβ0 h1β)).ne'
  field_simp
  ring
 rwa [htoteq] at htot
lemma bivProb_le_cdf (c:R) {β:R} (hβ0:0 < β) (hβ1:β < 1) :
  bP β c<=pC (-c):=by
 have hmono:StrictMonoOn (fun b=>bP b c) (Set.Ioo 0 1):=by
  refine strictMonoOn_of_deriv_pos (convex_Ioo 0 1) ?_ ?_
  .
   exact continuousOn_iff_continuous_domRestrict.mpr (continuous_iff_continuousAt.mpr fun x =>
    ((bPd c x.2.1 x.2.2).continuousAt).comp continuous_subtype_val.continuousAt)
  .
   intro b hb
   rw [interior_Ioo] at hb
   rw [(bPd c hb.1 hb.2).deriv]
   have h1b:0 < 1 - b:=by linarith [hb.2]
   have hb0:0 < b:=hb.1
   have hsq:0 < sqrt (b*(1 - b)):=sqrt_pos.mpr (mul_pos hb0 h1b)
   positivity
 have htend:Tendsto (fun b=>bP b c) (𝓝[<] 1) (𝓝 (pC (-c))):=by
  have hint_t:Tendsto
    (fun b=>∫ u in Set.Ioi (0:R),pC ((sqrt (1 - b)*u+c)/sqrt b)*pP u)
    (𝓝[<] 1) (𝓝 (∫ u in Set.Ioi (0:R),pC c*pP u)):=by
   refine tendsto_integral_filter_of_dominated_convergence pP ?_ ?_ ipP.integrableOn ?_
   . exact Eventually.of_forall fun b=>(bivProb_integrand_integrable b c).aestronglyMeasurable
   .
    exact Eventually.of_forall fun b=>ae_of_all _ fun u=>by
     rw [Real.norm_eq_abs,abs_mul,aon (pCp _).le,
      aon (pPn _)]
     exact mul_le_of_le_one_left (pPn u) (stdPhiCDF_lt_one _).le
   .
    refine ae_of_all _ fun u=>?_
    have hcont_cdf:Continuous pC :=
     continuous_iff_continuousAt.mpr fun z=>(pCd z).continuousAt
    have h1:Tendsto (fun b:R=>(sqrt (1 - b)*u+c)/sqrt b) (𝓝[<] 1) (𝓝 c):=by
     have hc_at:ContinuousAt (fun b:R=>(sqrt (1 - b)*u+c)/sqrt b) 1:=by
      have hden:sqrt (1:R) ≠ 0:=by norm_num
      fun_prop (disch:=assumption)
     have ht:Tendsto (fun b:R=>(sqrt (1 - b)*u+c)/sqrt b) (𝓝[<] 1)
       (𝓝 ((sqrt (1 - 1)*u+c)/sqrt 1)) :=
      hc_at.tendsto.mono_left nhdsWithin_le_nhds
     simpa using ht
    exact (hcont_cdf.continuousAt.tendsto.comp h1).mul tendsto_const_nhds
  have hIoi:∫ u in Set.Ioi (0:R),pC c*pP u=pC c*(1/2):=by
   rw [integral_const_mul]
   have h1:(∫ t in Set.Iic (0:R),pP t)+(∫ t in Set.Ioi (0:R),pP t)=1:=by
    rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
     ipP.integrableOn ipP.integrableOn,
     Set.Iic_union_Ioi,setIntegral_univ,integral_stdPhiPDF_univ]
   rw [integral_stdPhiPDF_Iic_zero] at h1
   congr 1;linarith
  rw [hIoi] at hint_t
  have h2:=tendsto_const_nhds (x:=(1:R)).sub (hint_t.const_mul 2)
  have heq:1 - 2*(pC c*(1/2))=pC (-c):=by
   rw [stdPhiCDF_neg];ring
  rw [heq] at h2
  exact h2
 refine ge_of_tendsto htend ?_
 filter_upwards [Ioo_mem_nhdsLT hβ1] with b hb
 exact (hmono ⟨hβ0,hβ1⟩ ⟨hβ0.trans hb.1,hb.2⟩ hb.1).le
lemma arcsin_le_poly {r:R} (hr0:0<=r) (hr1:r<=1) :
  arcsin r<=r+(3/5:R)*r^3:=by
 let f:R->R:=fun x=>x+(3/5:R)*x^3 - arcsin x
 have hf_cont:ContinuousOn f (Set.Icc 0 1):=by
  unfold f;fun_prop
 have hf_deriv:∀ x ∈ Set.Ioo (0:R) 1,
   HD f (1+(9/5:R)*x^2 - (sqrt (1 - x^2))⁻¹) x:=by
  intro x hx
  have h1:HD (fun y:R=>y+(3/5:R)*y^3) (1+(9/5:R)*x^2) x:=by
   have ha:=(hdi x).fun_add ((hdp 3 x).const_mul (3/5:R))
   rwa [show 1+3/5*(((3:ℕ):R)*x^(3 - 1))=1+9/5*x^2 by norm_num;ring] at ha
  have h2:HD arcsin (sqrt (1 - x^2))⁻¹ x:=by
   have h:=hasDerivAt_arcsin (x:=x) (by linarith [hx.1]) (by linarith [hx.2])
   simpa [one_div] using h
  exact h1.fun_sub h2
 let s0:R:=(-1+sqrt 261)/18
 have hs0_sq:(81/25:R)*s0^2+(9/25:R)*s0 - 13/5=0:=by
  have hsq:sqrt 261^2=261:=sq_sqrt (by norm_num)
  unfold s0
  field_simp
  nlinarith [hsq]
 have hs0_gt:(0:R) < s0:=by
  unfold s0
  have:(1:R) < sqrt 261:=by rw [lt_sqrt (by norm_num)];norm_num
  linarith
 have hs0_lt:s0 < 1:=by
  unfold s0
  have:sqrt 261 < 19:=by rw [sqrt_lt' (by norm_num)];norm_num
  linarith
 let r0:R:=sqrt s0
 have hr0_pos:0 < r0:=sqrt_pos.mpr hs0_gt
 have hr0_lt:r0 < 1:=by
  rw [show r0=sqrt s0 from rfl,sqrt_lt' (by norm_num)]
  linarith
 have hr0_sq:r0^2=s0:=sq_sqrt hs0_gt.le
 have hpoly_sign:∀ x ∈ Set.Ioo (0:R) 1,
   (1+(9/5:R)*x^2)^2*(1 - x^2) - 1 =
   x^2*(13/5 - (9/25:R)*x^2 - (81/25:R)*x^4):=by
  intro x _;ring
 have hmono_left:MonotoneOn f (Set.Icc 0 r0):=by
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 r0)
   (hf_cont.mono (Set.Icc_subset_Icc_right hr0_lt.le))
   (fun x hx=>by
    rw [interior_Icc] at hx
    exact (hf_deriv x ⟨hx.1,hx.2.trans hr0_lt⟩).differentiableAt.differentiableWithinAt) ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(hf_deriv x ⟨hx.1,hx.2.trans hr0_lt⟩).deriv]
  have hx2_le:x^2<=s0:=by rw [← hr0_sq];nlinarith [hx.1,hx.2]
  have h1x2:0 < 1 - x^2:=by nlinarith [hx.1,hx.2,hr0_lt]
  have hsq_ge:1<=(1+(9/5:R)*x^2)^2*(1 - x^2):=by
   have hfac:0<=13/5 - (9/25:R)*x^2 - (81/25:R)*x^4:=by
    nlinarith [hs0_sq,hx2_le,sq_nonneg x]
   nlinarith [hpoly_sign x ⟨hx.1,hx.2.trans hr0_lt⟩,sq_nonneg x]
  have hprod_ge:1<=(1+(9/5:R)*x^2)*sqrt (1 - x^2):=by
   have h1:(1:R)^2<=((1+(9/5:R)*x^2)*sqrt (1 - x^2))^2:=by
    rw [mul_pow,sq_sqrt h1x2.le];linarith
   have hnn:0<=(1+(9/5:R)*x^2)*sqrt (1 - x^2):=by positivity
   nlinarith
  have hinv:(sqrt (1 - x^2))⁻¹<=1+(9/5:R)*x^2:=by
   have hpos:=sqrt_pos.mpr h1x2
   rw [inv_le_iff_one_le_mul₀' hpos]
   linarith
  linarith
 have hanti_right:AntitoneOn f (Set.Icc r0 1):=by
  refine antitoneOn_of_deriv_nonpos (convex_Icc r0 1)
   (hf_cont.mono (Set.Icc_subset_Icc_left hr0_pos.le))
   (fun x hx=>by
    rw [interior_Icc] at hx
    exact (hf_deriv x ⟨hr0_pos.trans hx.1,hx.2⟩).differentiableAt.differentiableWithinAt) ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(hf_deriv x ⟨hr0_pos.trans hx.1,hx.2⟩).deriv]
  have hx2_ge:s0<=x^2:=by rw [← hr0_sq];nlinarith [hx.1,hr0_pos]
  have h1x2:0 < 1 - x^2:=by nlinarith [hx.1,hx.2,hr0_pos]
  have hsq_le:(1+(9/5:R)*x^2)^2*(1 - x^2)<=1:=by
   have hfac:13/5 - (9/25:R)*x^2 - (81/25:R)*x^4<=0:=by
    nlinarith [hs0_sq,hx2_ge,hs0_gt]
   nlinarith [hpoly_sign x ⟨hr0_pos.trans hx.1,hx.2⟩,sq_nonneg x]
  have hprod_le:(1+(9/5:R)*x^2)*sqrt (1 - x^2)<=1:=by
   have h1:((1+(9/5:R)*x^2)*sqrt (1 - x^2))^2<=(1:R)^2:=by
    rw [mul_pow,sq_sqrt h1x2.le];linarith
   have hnn:0<=(1+(9/5:R)*x^2)*sqrt (1 - x^2):=by positivity
   nlinarith
  have hinv:1+(9/5:R)*x^2<=(sqrt (1 - x^2))⁻¹:=by
   have hpos:=sqrt_pos.mpr h1x2
   rw [← one_div,le_div_iff₀ hpos]
   linarith
  linarith
 have hf0:0<=f 0:=by simp [f]
 have hf1:0<=f 1:=by
  unfold f
  rw [arcsin_one]
  have hpi:PI < (3.141593:R):=pi_lt_d6
  linarith
 have hfr:0<=f r:=by
  by_cases hle:r<=r0
  . exact hf0.trans (hmono_left ⟨le_rfl,hr0_pos.le⟩ ⟨hr0,hle⟩ hr0)
  . exact hf1.trans (hanti_right ⟨le_of_not_ge hle,hr1⟩ ⟨hr0_lt.le,le_rfl⟩ hr1)
 unfold f at hfr
 linarith
noncomputable def bivPub1 (ρ c:R):R :=
 if 0<=ρ then
  (pC (-c))^2+((ρ+(3/5:R)*ρ^3)/(2*PI))*exp (-c^2/(1+ρ))
 else
  (pC (-c))^2+(ρ / (2*PI))*exp (-c^2/(1+ρ))
lemma bPu (c:R) {ρ:R} (hρ_lo:-1 < ρ) (hρ_hi:ρ < 1) :
  bP ((1+ρ)/2) c<=bivPub1 ρ c:=by
 have hβ0:0 < (1+ρ)/2:=by linarith
 have hβ1:(1+ρ)/2 < 1:=by linarith
 have h2β:2*((1+ρ)/2)=1+ρ:=by ring
 unfold bivPub1
 split_ifs with hρ0
 ·
  let E:R:=exp (-c^2/(1+ρ))
  let F:R->R:=fun b =>
   bP b c - (pC (-c))^2 - (arcsin (2*b - 1)/(2*PI))*E
  have hF_half:F (1/2)=0:=by
   unfold F
   rw [bivProb_half]
   norm_num
  have hF_cont:ContinuousOn F (Set.Icc (1/2) ((1+ρ)/2)):=by
   have hcb:ContinuousOn (fun b=>bP b c) (Set.Icc (1/2) ((1+ρ)/2)) :=
    fun b hb=>((bPd c (by linarith [hb.1]) (by linarith [hb.2,hβ1])).continuousAt).continuousWithinAt
   exact (hcb.sub continuousOn_const).sub ((by fun_prop:Continuous fun b:R=>arcsin (2*b - 1)/(2*PI)*E).continuousOn)
  have hF_anti:AntitoneOn F (Set.Icc (1/2) ((1+ρ)/2)):=by
   refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hF_cont ?_ ?_
   .
    intro b hb
    rw [interior_Icc] at hb
    have hb0:0 < b:=by linarith [hb.1]
    have hb1:b < 1:=by linarith [hb.2,hβ1]
    have h1:HD (fun x=>bP x c)
      ((2*PI*sqrt (b*(1 - b)))⁻¹*exp (-c^2/(2*b))) b :=
     bPd c hb0 hb1
    have h2:HD (fun x:R=>arcsin (2*x - 1)/(2*PI)*E)
      (((sqrt (1 - (2*b - 1)^2))⁻¹*2)/(2*PI)*E) b:=by
     have hlin:HD (fun x:R=>2*x - 1) 2 b:=by
      simpa using ((hdi b).const_mul 2).fun_sub (hasDerivAt_const b 1)
     have ha:=hasDerivAt_comp_fun
      (by simpa [one_div] using hasDerivAt_arcsin (x:=2*b - 1) (by linarith) (by linarith)) hlin
     exact (ha.div_const (2*PI)).mul_const E
    exact ((h1.fun_sub (hasDerivAt_const b _)).fun_sub h2).differentiableAt.differentiableWithinAt
   .
    intro b hb
    rw [interior_Icc] at hb
    have hb0:0 < b:=by linarith [hb.1]
    have hb1:b < 1:=by linarith [hb.2,hβ1]
    have h1:HD (fun x=>bP x c)
      ((2*PI*sqrt (b*(1 - b)))⁻¹*exp (-c^2/(2*b))) b :=
     bPd c hb0 hb1
    have h2:HD (fun x:R=>arcsin (2*x - 1)/(2*PI)*E)
      (((sqrt (1 - (2*b - 1)^2))⁻¹*2)/(2*PI)*E) b:=by
     have hlin:HD (fun x:R=>2*x - 1) 2 b:=by
      simpa using ((hdi b).const_mul 2).fun_sub (hasDerivAt_const b 1)
     have ha:=hasDerivAt_comp_fun
      (by simpa [one_div] using hasDerivAt_arcsin (x:=2*b - 1) (by linarith) (by linarith)) hlin
     exact (ha.div_const (2*PI)).mul_const E
    rw [((h1.fun_sub (hasDerivAt_const b _)).fun_sub h2).deriv]
    have hsq_eq:sqrt (1 - (2*b - 1)^2)=2*sqrt (b*(1 - b)):=by
     rw [show 1 - (2*b - 1)^2=4*(b*(1 - b)) by ring,sqrt_mul (by norm_num)]
     norm_num
    have hcoeff:((sqrt (1 - (2*b - 1)^2))⁻¹*2)/(2*PI) =
      (2*PI*sqrt (b*(1 - b)))⁻¹:=by
     rw [hsq_eq]
     have hpi:PI ≠ 0:=pi_ne_zero
     have hsq:sqrt (b*(1 - b)) ≠ 0:=(sqrt_pos.mpr (mul_pos hb0 (by linarith))).ne'
     field_simp
    rw [sub_zero,hcoeff]
    have hexp_le:exp (-c^2/(2*b))<=E:=by
     unfold E
     rw [exp_le_exp]
     have h2b_le:2*b<=1+ρ:=by linarith [hb.2]
     have h2b_pos:0 < 2*b:=by linarith
     have h1ρ_pos:0 < 1+ρ:=by linarith
     have hdiv:c^2/(1+ρ)<=c^2/(2*b) :=
      div_le_div_of_nonneg_left (sq_nonneg c) h2b_pos h2b_le
     rw [neg_div,neg_div]
     linarith
    have hpref_nn:0<=(2*PI*sqrt (b*(1 - b)))⁻¹:=by positivity
    nlinarith
  have hle:=hF_anti ⟨le_rfl,by linarith⟩ ⟨by linarith,le_rfl⟩ (by linarith:(1/2:R)<=(1+ρ)/2)
  rw [hF_half] at hle
  unfold F at hle
  have h2b:2*((1+ρ)/2) - 1=ρ:=by ring
  rw [h2b] at hle
  have hasin:=arcsin_le_poly hρ0 hρ_hi.le
  have hE_nn:0<=E:=exp_nonneg _
  have hpi_pos:0 < 2*PI:=by positivity
  have hstep:arcsin ρ / (2*PI)*E<=(ρ+3/5*ρ^3)/(2*PI)*E :=
   mlR (dld hasin hpi_pos.le) hE_nn
  linarith
 ·
  have hρ0':ρ < 0:=lt_of_not_ge hρ0
  let E:R:=exp (-c^2/(1+ρ))
  let F:R->R:=fun b=>bP b c - (b/PI)*E
  have hF_cont:ContinuousOn F (Set.Icc ((1+ρ)/2) (1/2)):=by
   have hcb:ContinuousOn (fun b=>bP b c) (Set.Icc ((1+ρ)/2) (1/2)) :=
    fun b hb=>((bPd c (by linarith [hb.1,hβ0]) (by linarith [hb.2])).continuousAt).continuousWithinAt
   exact hcb.sub ((by fun_prop:Continuous fun b:R=>b/PI*E).continuousOn)
  have hF_mono:MonotoneOn F (Set.Icc ((1+ρ)/2) (1/2)):=by
   refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hF_cont ?_ ?_
   .
    intro b hb
    rw [interior_Icc] at hb
    have h1:=bPd c (β:=b) (by linarith [hb.1,hβ0]) (by linarith [hb.2])
    have h2:HD (fun x:R=>x/PI*E) (1/PI*E) b :=
     ((hdi b).div_const PI).mul_const E
    exact (h1.fun_sub h2).differentiableAt.differentiableWithinAt
   .
    intro b hb
    rw [interior_Icc] at hb
    have hb0:0 < b:=by linarith [hb.1,hβ0]
    have hb1:b < 1:=by linarith [hb.2]
    have h1:=bPd c (β:=b) hb0 hb1
    have h2:HD (fun x:R=>x/PI*E) (1/PI*E) b :=
     ((hdi b).div_const PI).mul_const E
    rw [(h1.fun_sub h2).deriv]
    have hsq_le:sqrt (b*(1 - b))<=1/2:=by
     rw [sqrt_le_iff]
     exact ⟨by norm_num,by nlinarith [sq_nonneg (b - 1/2)]⟩
    have hpref_ge:1/PI<=(2*PI*sqrt (b*(1 - b)))⁻¹:=by
     rw [one_div,inv_le_inv₀ (by positivity) (by positivity)]
     nlinarith [pi_pos]
    have hexp_ge:E<=exp (-c^2/(2*b)):=by
     unfold E
     rw [exp_le_exp]
     have h2b_ge:1+ρ<=2*b:=by linarith [hb.1]
     have h1ρ_pos:0 < 1+ρ:=by linarith
     have hdiv:c^2/(2*b)<=c^2/(1+ρ) :=
      div_le_div_of_nonneg_left (sq_nonneg c) h1ρ_pos h2b_ge
     rw [neg_div,neg_div]
     linarith
    have hprod:=mul_le_mul hpref_ge hexp_ge (exp_nonneg _) (by positivity)
    linarith
  have hle:=hF_mono ⟨le_rfl,by linarith⟩ ⟨by linarith,le_rfl⟩ (by linarith:(1+ρ)/2<=1/2)
  unfold F at hle
  rw [bivProb_half] at hle
  have halg:(1/2:R)/PI*E - ((1+ρ)/2)/PI*E = -(ρ / (2*PI)*E):=by
   field_simp;ring
  linarith
noncomputable def gC:R:=1/20
noncomputable def bConst:R:=3/25
def gI:ℤ:=500000
def bInt:ℤ:=1200000
noncomputable def mR (x:R):R:=pP x/pC x
lemma millsRatio_pos (x:R):0 < mR x :=
 div_pos (pPp x) (pCp x)
lemma stdPhiPDF_hasDerivAt (x:R):HD pP (-x*pP x) x:=by
 have h1:HD (fun y:R=>-y^2/2) (-x) x:=by
  have ha:=(hdp 2 x).fun_neg.div_const 2
  rwa [show -(((2:ℕ):R)*x^(2 - 1))/2 = -x by norm_num;ring] at ha
 have h2:=(hasDerivAt_comp_fun (f:=exp) (g:=fun y:R=>-y^2/2)
  (hasDerivAt_exp (-x^2/2)) h1).const_mul (sqrt (2*PI))⁻¹
 have heq:(sqrt (2*PI))⁻¹*(exp (-x^2/2) * -x) = -x*pP x:=by
  unfold pP;ring
 rwa [heq] at h2
lemma millsRatio_add_pos (x:R):0 < x+mR x:=by
 by_cases hx:0<=x
 . linarith [millsRatio_pos x]
 .
  have hx':x < 0:=lt_of_not_ge hx
  rw [mR,show x+pP x/pC x=(x*pC x+pP x)/pC x by
   field_simp [(pCp x).ne']]
  refine div_pos ?_ (pCp x)
  have hphi_eq:∫ t in Set.Iic x,(-t)*pP t=pP x:=by
   have hd:∀ u ∈ Set.Ioi (-x),HD (fun v:R=>-pP v) (u*pP u) u:=by
    intro u _
    have h:=(stdPhiPDF_hasDerivAt u).fun_neg
    rwa [show -(-u*pP u)=u*pP u by ring] at h
   have hcont:ContinuousWithinAt (fun v:R=>-pP v) (Set.Ici (-x)) (-x) :=
    (by unfold pP;fun_prop:Continuous fun v:R=>-pP v).continuousWithinAt
   have htend:Tendsto (fun v:R=>-pP v) atTop (𝓝 0):=by
    have hsq:Tendsto (fun v:R=>v^2/2) atTop atTop :=
     (tendsto_pow_atTop (by norm_num:2 ≠ 0)).atTop_div_const (by norm_num)
    have hneg0:Tendsto (fun v:R=>-(v^2/2)) atTop atBot :=
     tendsto_neg_atTop_atBot.comp hsq
    have hneg:Tendsto (fun v:R=>-v^2/2) atTop atBot:=by
     simpa [neg_div] using hneg0
    simpa [pP] using ((tendsto_exp_atBot.comp hneg).const_mul (sqrt (2*PI))⁻¹).neg
   have hint_pos:IntegrableOn (fun u:R=>u*pP u) (Set.Ioi (-x)):=by
    have hsub:Set.Ioi (-x) ⊆ Set.Ioi (0:R):=fun u hu=>by
     change -x < u at hu
     change 0 < u;linarith
    exact (integrableOn_abs_mul_stdPhiPDF_Ioi.mono_set hsub).congr_fun
     (fun u hu=>by dsimp only;rw [abs_of_pos (hsub hu)]) measurableSet_Ioi
   have hftc:=integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hint_pos htend
   rw [zero_sub,neg_neg,stdPhiPDF_even] at hftc
   have hneg_int:∫ t in Set.Iio x,(-t)*pP t=∫ u in Set.Ioi (-x),u*pP u:=by
    simp_rw [← integral_indicator measurableSet_Iio,← integral_indicator measurableSet_Ioi]
    rw [← MeasureTheory.integral_neg_eq_self (f:=Set.indicator (Set.Ioi (-x)) (fun u:R=>u*pP u))]
    congr 1;ext t
    by_cases ht:t < x
    .
     have hnt:-x < -t:=by linarith
     simp [Set.indicator,ht,hnt,stdPhiPDF_even]
    .
     have hnt:¬ (-x < -t):=by linarith
     simp [Set.indicator,ht,hnt]
   rw [← setIntegral_congr_set Iio_ae_eq_Iic,hneg_int,hftc]
  have hlt:∫ t in Set.Iic x,(-x)*pP t < ∫ t in Set.Iic x,(-t)*pP t:=by
   have hdiff_nn:∀ t ∈ Set.Iic x,0<=((-t)*pP t - (-x)*pP t):=by
    intro t ht
    have:-x <= -t:=by linarith [ht.out]
    nlinarith [pPn t]
   have hint1:IntegrableOn (fun t:R=>(-x)*pP t) (Set.Iic x) :=
    (ipP.const_mul (-x)).integrableOn
   have hint2:IntegrableOn (fun t:R=>(-t)*pP t) (Set.Iic x):=by
    have hcomp:IntegrableOn (fun t:R=>(-t)*pP t) (Set.Iio x):=by
     rw [← integrable_indicator_iff measurableSet_Iio]
     have hsub:Set.Ioi (-x) ⊆ Set.Ioi (0:R):=fun u hu=>by
      change -x < u at hu;change 0 < u;linarith
     have hpos:IntegrableOn (fun u:R=>u*pP u) (Set.Ioi (-x)) :=
      (integrableOn_abs_mul_stdPhiPDF_Ioi.mono_set hsub).congr_fun
       (fun u hu=>by dsimp only;rw [abs_of_pos (hsub hu)]) measurableSet_Ioi
     have hpos':Integrable (Set.indicator (Set.Ioi (-x)) (fun u:R=>u*pP u)) :=
      (integrable_indicator_iff measurableSet_Ioi).mpr hpos
     have heq:Set.indicator (Set.Iio x) (fun t:R=>(-t)*pP t) =
       fun t=>Set.indicator (Set.Ioi (-x)) (fun u:R=>u*pP u) (-t):=by
      ext t
      by_cases ht:t < x
      .
       have hnt:-x < -t:=by linarith
       simp [Set.indicator,ht,hnt,stdPhiPDF_even]
      .
       have hnt:¬ (-x < -t):=by linarith
       simp [Set.indicator,ht,hnt]
     rw [heq];exact hpos'.comp_neg
    exact hcomp.congr_set_ae Iio_ae_eq_Iic.symm
   have hsub_int:Set.Ioc (x - 2) (x - 1) ⊆ Set.Iic x:=fun t ht=>by
    change t<=x;linarith [ht.2]
   have hpos_sub:0 < ∫ t in Set.Ioc (x - 2) (x - 1),((-t)*pP t - (-x)*pP t):=by
    rw [← intervalIntegral.integral_of_le (by linarith:x - 2<=x - 1)]
    have hc:Continuous (fun t:R=>(-t)*pP t - (-x)*pP t):=by
     unfold pP;fun_prop
    refine intervalIntegral.integral_pos (by linarith) hc.continuousOn
     (fun t ht=>hdiff_nn t (by change t<=x;linarith [ht.2]))
     ⟨x - 1,⟨by linarith,le_rfl⟩,?_⟩
    have hp:=pPp (x - 1)
    linarith
   have hle_tot:∫ t in Set.Ioc (x - 2) (x - 1),((-t)*pP t - (-x)*pP t) <=
     ∫ t in Set.Iic x,((-t)*pP t - (-x)*pP t) :=
    setIntegral_mono_set (hint2.sub hint1)
     ((ae_restrict_mem measurableSet_Iic).mono fun t ht=>hdiff_nn t ht)
     (Eventually.of_forall hsub_int)
   rw [integral_sub hint2 hint1] at hle_tot
   linarith
  rw [integral_const_mul,← stdPhiCDF_eq_integral,hphi_eq] at hlt
  linarith
lemma millsRatio_hasDerivAt (x:R) :
  HD mR (-(mR x)*(x+mR x)) x:=by
 have hd:=(stdPhiPDF_hasDerivAt x).fun_div (pCd x) (pCp x).ne'
 have heq:(-x*pP x*pC x - pP x*pP x)/pC x^2 =
   -(mR x)*(x+mR x):=by
  unfold mR
  have hpos:pC x ≠ 0:=(pCp x).ne'
  field_simp
  ring
 rwa [heq] at hd
lemma log_stdPhiCDF_hasDerivAt (x:R) :
  HD (fun y=>log (pC y)) (mR x) x :=
 (pCd x).log (pCp x).ne'
lemma log_stdPhiCDF_le_tangent (x₀ x:R) :
  log (pC x)<=log (pC x₀)+mR x₀*(x - x₀):=by
 have hr_anti:StrictAnti mR:=by
  refine strictAnti_of_deriv_neg fun y=>?_
  rw [(millsRatio_hasDerivAt y).deriv]
  have h1:=millsRatio_pos y
  have h2:=millsRatio_add_pos y
  nlinarith
 let F:R->R:=fun y=>log (pC y) - log (pC x₀) - mR x₀*(y - x₀)
 have hFd:∀ y:R,HD F (mR y - mR x₀) y:=by
  intro y
  have h1:=(log_stdPhiCDF_hasDerivAt y).fun_sub (hasDerivAt_const y (log (pC x₀)))
  have h2:HD (fun z:R=>mR x₀*(z - x₀)) (mR x₀) y:=by
   have ha:=((hdi y).fun_sub (hasDerivAt_const y x₀)).const_mul (mR x₀)
   rwa [show mR x₀*(1 - 0)=mR x₀ by ring] at ha
  have h3:=h1.fun_sub h2
  rwa [sub_zero] at h3
 have hF0:F x₀=0:=by simp [F]
 have hFx:F x<=0:=by
  by_cases hx:x₀<=x
  .
   have hanti:AntitoneOn F (Set.Icc x₀ x) :=
    antitoneOn_of_deriv_nonpos (convex_Icc x₀ x)
     (fun y _=>(hFd y).continuousAt.continuousWithinAt)
     (fun y _=>(hFd y).differentiableAt.differentiableWithinAt)
     (fun y hy=>by
      rw [interior_Icc] at hy
      rw [(hFd y).deriv]
      linarith [hr_anti hy.1])
   linarith [hanti ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx,hF0]
  .
   have hx':x<=x₀:=le_of_not_ge hx
   have hmono:MonotoneOn F (Set.Icc x x₀) :=
    monotoneOn_of_deriv_nonneg (convex_Icc x x₀)
     (fun y _=>(hFd y).continuousAt.continuousWithinAt)
     (fun y _=>(hFd y).differentiableAt.differentiableWithinAt)
     (fun y hy=>by
      rw [interior_Icc] at hy
      rw [(hFd y).deriv]
      linarith [hr_anti hy.2])
   linarith [hmono ⟨le_rfl,hx'⟩ ⟨hx',le_rfl⟩ hx',hF0]
 unfold F at hFx
 linarith
def tLInt:ℤ:=5230800
def tRInt:ℤ:=5230950
lemma cert_tStar_endpoints :
  mC tLInt (cH (tLInt - gI)) < pL (tLInt - gI) /\
  pH (tRInt - gI) < mF tRInt (cL (tRInt - gI)):=by decide
lemma exists_tStar:∃ t ∈ Set.Icc ((tLInt:R)/S0) ((tRInt:R)/S0),
  t=mR (t - gC):=by
 let h:R->R:=fun t=>t*pC (t - gC) - pP (t - gC)
 have hh_cont:Continuous h:=by
  have h1:Continuous pC :=
   continuous_iff_continuousAt.mpr fun z=>(pCd z).continuousAt
  have h2:Continuous pP:=by unfold pP;fun_prop
  unfold h;fun_prop
 have hgam:gC=(gI:R)/S0:=by norm_num [gC,gI,S0,fpS]
 have hL:h ((tLInt:R)/S0) < 0:=by
  unfold h
  rw [hgam,← sub_div,← Int.cast_sub]
  have h1:=mlL (le_phiCDFHi (tLInt - gI)) (by norm_num [tLInt,S0,fpS]:(0:R)<=(tLInt:R)/S0)
  have h2:=le_mulCe tLInt (cH (tLInt - gI))
  have h3:=phiPDFLo_le (tLInt - gI)
  have h4:((mC tLInt (cH (tLInt - gI)):ℤ):R)/S0 <
    ((pL (tLInt - gI):ℤ):R)/S0 :=
   div_lt_div_of_pos_right (by exact_mod_cast cert_tStar_endpoints.1) fpS_pos
  linarith
 have hR:0 < h ((tRInt:R)/S0):=by
  unfold h
  rw [hgam,← sub_div,← Int.cast_sub]
  have h1:=mlL (phiCDFLo_le (tRInt - gI)) (by norm_num [tRInt,S0,fpS]:(0:R)<=(tRInt:R)/S0)
  have h2:=mulFl_le tRInt (cL (tRInt - gI))
  have h3:=le_phiPDFHi (tRInt - gI)
  have h4:((pH (tRInt - gI):ℤ):R)/S0 <
    ((mF tRInt (cL (tRInt - gI)):ℤ):R)/S0 :=
   div_lt_div_of_pos_right (by exact_mod_cast cert_tStar_endpoints.2) fpS_pos
  linarith
 have hle:(tLInt:R)/S0<=(tRInt:R)/S0:=by norm_num [tLInt,tRInt,S0,fpS]
 have hmem:(0:R) ∈ Set.Icc (h ((tLInt:R)/S0)) (h ((tRInt:R)/S0)) :=
  ⟨hL.le,hR.le⟩
 obtain ⟨t,ht_mem,ht_eq⟩:=intermediate_value_Icc hle hh_cont.continuousOn hmem
 refine ⟨t,ht_mem,?_⟩
 unfold h at ht_eq
 unfold mR
 have hpos:=(pCp (t - gC)).ne'
 field_simp
 linarith
noncomputable def tStar:R:=Classical.choose exists_tStar
lemma tStar_mem:tStar ∈ Set.Icc ((tLInt:R)/S0) ((tRInt:R)/S0) :=
 (Classical.choose_spec exists_tStar).1
lemma tStar_eq_mills:tStar=mR (tStar - gC) :=
 (Classical.choose_spec exists_tStar).2
noncomputable def gStar:R:=-tStar^2/2+log (pC (tStar - gC))
noncomputable def aConst:R :=
 log (pC (tStar - gC)) +
  exp (-(tStar - gC)^2)/(4*PI*(pC (tStar - gC))^2) - 1/2
def xLInt:ℤ:=tLInt - gI
def xRInt:ℤ:=tRInt - gI
def i40:ℤ:=iP0/2
def i41:ℤ:=dC iP1 2
def gLoInt:ℤ:=-dC (tRInt*tRInt) (2*fpS)+(-3828512)
def aLoInt:ℤ :=
 (-3828512) +
  dF (i40*eL (-dC (xRInt*xRInt) fpS)) (mC (cH xRInt) (cH xRInt)) - fpS/2
def aHiInt:ℤ :=
 (-3828240) +
  dC (i41*eH (-dF (xLInt*xLInt) fpS)) (mF (cL xLInt) (cL xLInt)) - fpS/2
def gLoVal:ℤ:=-5196700
def aLoVal:ℤ:=-7460500
def aHiVal:ℤ:=-7460050
lemma cert_gA_vals :
  gLoVal<=gLoInt/\aLoVal<=aLoInt/\aHiInt<=aHiVal:=by decide
def oLL (y l:ℤ):Bool :=
 if y<=0 then false
 else if l<=0 then decide (eH l<=y)
 else decide (fpS<=mF y (eL (-l)))
def oLH (y l:ℤ):Bool :=
 if y<=0 then false
 else if l<=0 then decide (y<=eL l)
 else decide (mC y (eH (-l))<=fpS)
lemma oLLs {y l:ℤ} (h:oLL y l=true) :
  0 < y/\((l:R)/S0)<=log ((y:R)/S0):=by
 have hs:(0:R) < S0:=fpS_pos
 unfold oLL at h
 by_cases hy:y<=0
 . rw [if_pos hy] at h;exact absurd h (by decide)
 .
  rw [if_neg hy] at h
  have hy':0 < y:=by omega
  have hyR:(0:R) < (y:R)/S0:=div_pos (by exact_mod_cast hy') hs
  refine ⟨hy',?_⟩
  by_cases hl:l<=0
  .
   rw [if_pos hl] at h
   have hle:eH l<=y:=of_decide_eq_true h
   rw [le_log_iff_exp_le hyR]
   calc exp ((l:R)/S0)
     <= ((eH l:ℤ):R)/S0:=le_expNegHi hl
    _ <= (y:R)/S0:=dld (by exact_mod_cast hle) hs.le
  .
   rw [if_neg hl] at h
   have hle:fpS<=mF y (eL (-l)):=of_decide_eq_true h
   rw [le_log_iff_exp_le hyR]
   have h1:(1:R)<=((mF y (eL (-l)):ℤ):R)/S0:=by
    rw [one_le_div hs];exact_mod_cast hle
   have h2:((mF y (eL (-l)):ℤ):R)/S0 <=
     ((y:R)/S0)*(((eL (-l):ℤ):R)/S0):=mulFl_le y (eL (-l))
   have h3:((eL (-l):ℤ):R)/S0<=exp (-((l:R)/S0)):=by
    have:=expNegLo_le (x:=-l) (by omega)
    simpa [neg_div] using this
   have h4:(1:R)<=((y:R)/S0)*exp (-((l:R)/S0)) :=
    le_trans (h1.trans h2) (mlL h3 hyR.le)
   rw [exp_neg] at h4
   have hexp_pos:0 < exp ((l:R)/S0):=exp_pos _
   have h5:=mlR h4 hexp_pos.le
   rw [one_mul,mul_assoc,inv_mul_cancel₀ hexp_pos.ne',mul_one] at h5
   exact h5
lemma oLHs {y l:ℤ} (h:oLH y l=true) :
  0 < y/\log ((y:R)/S0)<=((l:R)/S0):=by
 have hs:(0:R) < S0:=fpS_pos
 unfold oLH at h
 by_cases hy:y<=0
 . rw [if_pos hy] at h;exact absurd h (by decide)
 .
  rw [if_neg hy] at h
  have hy':0 < y:=by omega
  have hyR:(0:R) < (y:R)/S0:=div_pos (by exact_mod_cast hy') hs
  refine ⟨hy',?_⟩
  by_cases hl:l<=0
  .
   rw [if_pos hl] at h
   have hle:y<=eL l:=of_decide_eq_true h
   rw [log_le_iff_le_exp hyR]
   calc (y:R)/S0
     <= ((eL l:ℤ):R)/S0:=dld (by exact_mod_cast hle) hs.le
    _ <= exp ((l:R)/S0):=expNegLo_le hl
  .
   rw [if_neg hl] at h
   have hle:mC y (eH (-l))<=fpS:=of_decide_eq_true h
   rw [log_le_iff_le_exp hyR]
   have h1:((mC y (eH (-l)):ℤ):R)/S0<=1:=by
    rw [div_le_one hs];exact_mod_cast hle
   have h2:((y:R)/S0)*(((eH (-l):ℤ):R)/S0) <=
     ((mC y (eH (-l)):ℤ):R)/S0:=le_mulCe y (eH (-l))
   have h3:exp (-((l:R)/S0))<=((eH (-l):ℤ):R)/S0:=by
    have:=le_expNegHi (x:=-l) (by omega)
    simpa [neg_div] using this
   have h4:((y:R)/S0)*exp (-((l:R)/S0))<=1 :=
    le_trans (mlL h3 hyR.le) (h2.trans h1)
   rw [exp_neg] at h4
   have hexp_pos:0 < exp ((l:R)/S0):=exp_pos _
   have h5:=mlR h4 hexp_pos.le
   rw [one_mul,mul_assoc,inv_mul_cancel₀ hexp_pos.ne',mul_one] at h5
   exact h5
def eQA (t0 t1 tm a:ℤ):ℤ :=
 let tc:=max t0 (min t1 a)
 (-dF (tc*tc) (2*fpS))+dC (a*(tc - tm)) fpS
def mQH (aLo aHi t0 t1 tm:ℤ):ℤ :=
 max (eQA t0 t1 tm aLo) (eQA t0 t1 tm aHi)
def hH0 (r0 r1 cLogLo cLogHi kLo kHi l1Lo l1Hi:ℤ):ℤ :=
 let rm:=(r0+r1)/2
 let half:=max (r1 - rm) (rm - r0)
 let onePrm:=fpS+rm
 let t1:=mC cLogHi onePrm
 let t2:=-dF (onePrm*l1Lo) (2*fpS)
 let t3:=if 0<=rm then -mF aLoVal rm else -mF aHiVal rm
 let rm2Fl:=dF (rm*rm) fpS
 let rm2Ce:=dC (rm*rm) fpS
 let rm3Lo:=if 0<=rm then mF rm2Fl rm else mF rm2Ce rm
 let t4:=-mF bInt rm3Lo
 let t5:=if 0<=rm then mC kHi rm else mC kLo rm
 let valHi:=t1+t2+t3+t4+t5
 let dLo:=cLogLo - dC (l1Hi+fpS) 2 - aHiVal - dC (3*bInt*rm2Ce) fpS+kLo
 let dHi:=cLogHi - dF (l1Lo+fpS) 2 - aLoVal - dF (3*bInt*rm2Fl) fpS+kHi
 let slopeAbs:=max (Int.natAbs dLo:ℤ) (Int.natAbs dHi:ℤ)
 valHi+mC slopeAbs half
def cLP (r0 r1 t0 t1 l1Lo l1Hi lPhLo lPhHi lUHi rm tm rmLo rmHi b1 cSqLo phLo:ℤ):Bool :=
 let q1:=mQH (mF (fpS+r0) rmLo) (mC (fpS+r1) rmHi) t0 t1 tm
 let phLoSq:=mF phLo phLo
 if phLo<=0 then false else
 if phLoSq<=0 then false else
 let eArg:=-dF (cSqLo*fpS) (fpS+r1)
 let eHi:=eH eArg
 let mHi:=dC (mC iP1 eHi*fpS) phLoSq
 let r1CubeHi:=mC (mC r1 r1) r1
 let shiftHi:=dC (6*r1CubeHi) 10
 let uM:=mC (rm+shiftHi) mHi
 if !oLH (fpS+uM) lUHi then false else
 let kLo:=dF (mF b1 mHi*fpS) (fpS+uM)
 let kHi:=dC (mC b1 mHi*fpS) (fpS+uM)
 let diffHi:=mC shiftHi mHi - uM
 let cTerm:=mC b1 lUHi+dC (mC b1 diffHi*fpS) (fpS+uM)
 decide (q1+hH0 r0 r1 lPhLo lPhHi kLo kHi l1Lo l1Hi+cTerm - gLoVal < 0)
def cLN (r0 r1 t0 t1 l1Lo l1Hi lPhLo lPhHi lUHi rm tm rmLo rmHi b0 cSqHi phHi:ℤ):Bool :=
 let q1:=mQH (mF (fpS+r0) rmLo) (mC (fpS+r1) rmHi) t0 t1 tm
 let phHiSq:=mC phHi phHi
 if phHiSq<=0 then false else
 let eArg:=-dC (cSqHi*fpS) (fpS+r0)
 let eLo:=eL eArg
 let mLo:=dF (mF iP0 eLo*fpS) phHiSq
 let uM:=mC rm mLo
 if fpS+uM<=500000 then
  let dHi:=mC r1 mLo
  if fpS+dHi<=500 then false
  else if !oLH (fpS+dHi) lUHi then false
  else decide (q1+hH0 r0 r1 lPhLo lPhHi 0 0 l1Lo l1Hi+mC b0 lUHi - gLoVal < 0)
 else
  if !oLH (fpS+uM) lUHi then false else
  let kLo:=dF (mF b0 mLo*fpS) (fpS+uM)
  let kHi:=dC (mC b0 mLo*fpS) (fpS+uM)
  let cTerm:=mC b0 lUHi+dC (mC b0 (-uM)*fpS) (fpS+uM)
  decide (q1+hH0 r0 r1 lPhLo lPhHi kLo kHi l1Lo l1Hi+cTerm - gLoVal < 0)
def cLH (r0 r1 t0 t1 l1Lo l1Hi lPhLo lPhHi lUHi:ℤ):Bool :=
 let rm:=(r0+r1)/2
 let tm:=(t0+t1)/2
 let xm:=tm - gI
 let phMLo:=cL xm
 let phMHi:=cH xm
 let pdfMLo:=pL xm
 let pdfMHi:=pH xm
 if phMLo < 500 then false else
 if !(oLL (fpS+rm) l1Lo && oLH (fpS+rm) l1Hi &&
    oLL phMLo lPhLo && oLH phMHi lPhHi) then false else
 let rmLo:=dF (pdfMLo*fpS) phMHi
 let rmHi:=dC (pdfMHi*fpS) phMLo
 let b0:=dF (fpS+r0) 2
 let b1:=dC (fpS+r1) 2
 let q2:=mQH (mF b0 rmLo) (mC b1 rmHi) t0 t1 tm
 let h2:=hH0 r0 r1 (dF lPhLo 2) (dC lPhHi 2) 0 0 l1Lo l1Hi
 if q2+h2 - gLoVal < 0 then true else
 let c0:=gI - t1
 let c1:=gI - t0
 let cSqLo:=if c0<=0/\0<=c1 then 0 else min (dF (c0*c0) fpS) (dF (c1*c1) fpS)
 let cSqHi:=max (dC (c0*c0) fpS) (dC (c1*c1) fpS)
 let phLo:=cL (t0 - gI)
 let phHi:=cH (t1 - gI)
 if 0<=r0 then cLP r0 r1 t0 t1 l1Lo l1Hi lPhLo lPhHi lUHi rm tm rmLo rmHi b1 cSqLo phLo
 else if r1<=0 then cLN r0 r1 t0 t1 l1Lo l1Hi lPhLo lPhHi lUHi rm tm rmLo rmHi b0 cSqHi phHi
 else false
inductive BoxTree
 | l:ℤ->ℕ->ℕ->ℤ->BoxTree
 | r:BoxTree->BoxTree->BoxTree
 | t:BoxTree->BoxTree->BoxTree
def cT0 (r0 r1 t0 t1:ℤ):BoxTree->Bool
 | .l a nc d e=>cLH r0 r1 t0 t1 a (a+501) (-(nc:ℤ)) (-(nc:ℤ)+(d:ℤ)) e
 | .r tl tr =>
  let rm:=(r0+r1)/2
  cT0 r0 rm t0 t1 tl && cT0 rm r1 t0 t1 tr
 | .t tl tr =>
  let tm:=(t0+t1)/2
  cT0 r0 r1 t0 tm tl && cT0 r0 r1 tm t1 tr
def outerTree0:BoxTree:=.t (.r (.l (-14167786) 19775781 566 0) (.l (-4346615) 19775781 566 (-35667))) (.r (.t (.r (.t (.l (-19572490) 11866679 527 (-399)) (.l (-19572490) 9404607 522 (-150315))) (.t (.l (-10678657) 11866679 527 (-1903591)) (.l (-10678657) 9404607 522 (-3433479)))) (.r (.t (.r (.l (-24010502) 7312771 518 (-3131582)) (.l (-16509362) 7312771 518 (-4837417))) (.r (.t (.r (.l (-27285969) 5972144 515 (-2151319)) (.l (-21547291) 5972144 515 (-3486157))) (.l (-24010502) 5180730 514 (-407472))) (.t (.l (-16509362) 5972144 515 (-3678385)) (.r (.l (-17924097) 5180730 514 (-2029522)) (.l (-15270193) 5180730 514 (-2282980)))))) (.t (.l (-10678657) 7312771 518 (-4105743)) (.r (.t (.l (-12271812) 5972144 515 (-3533469)) (.r (.l (-13174932) 5180730 514 (-2364239)) (.l (-11443541) 5180730 514 (-2344192)))) (.t (.l (-9304781) 5972144 515 (-3089440)) (.r (.l (-9968143) 5180730 514 (-2261418)) (.l (-8682699) 5180730 514 (-2138339)))))))) (.t (.r (.l (-6047036) 10587945 524 (-1723212)) (.l (-2893752) 10587945 524 (-1225418))) (.r (.t (.l (-6047036) 7312771 518 (-2805686)) (.r (.l (-7019607) 5566503 515 (-1884077)) (.l (-5160726) 5566503 515 (-1537221)))) (.t (.l (-2893752) 7312771 518 (-1484902)) (.r (.l (-3593822) 5566503 515 (-1159503)) (.l (-2239502) 5566503 515 (-770245)))))))
def outerTree1:BoxTree:=.r (.r (.r (.l (-24010502) 3818624 515 183) (.t (.r (.l (-17924097) 4295678 513 (-593293)) (.l (-15270193) 4295678 513 (-860761))) (.l (-16509362) 3381420 514 0))) (.r (.t (.r (.t (.l (-13174932) 4549708 515 (-1602861)) (.l (-13174932) 4052057 513 (-1038181))) (.t (.l (-11443541) 4549708 515 (-1665517)) (.l (-11443541) 4052057 513 (-1140608)))) (.l (-12271812) 3381420 514 (-363999))) (.t (.r (.t (.r (.l (-10317092) 4549708 515 (-1698719)) (.l (-9630964) 4549708 515 (-1680010))) (.l (-9968143) 4052057 513 (-1185226))) (.t (.r (.l (-8988905) 4549708 515 (-1651571)) (.l (-8385595) 4549708 515 (-1614909))) (.l (-8682699) 4052057 513 (-1186002)))) (.l (-9304781) 3381420 514 (-525289))))) (.r (.r (.t (.r (.t (.r (.l (-7816621) 4549708 515 (-1571270)) (.l (-7278285) 4549708 515 (-1521698))) (.r (.l (-7816621) 4052057 513 (-1182753)) (.l (-7278285) 4052057 513 (-1157299)))) (.t (.r (.l (-6767455) 4549708 515 (-1467069)) (.l (-6281456) 4549708 515 (-1408121))) (.r (.l (-6767455) 4052057 513 (-1126212)) (.t (.l (-6281456) 4172580 513 (-1241869)) (.l (-6281456) 3934081 514 (-1090192)))))) (.r (.l (-7543830) 3381420 514 (-610271)) (.t (.l (-6521503) 3595152 512 (-824702)) (.l (-6521503) 3177193 512 (-608087))))) (.t (.r (.t (.r (.l (-5817987) 4549708 515 (-1345469)) (.l (-5375049) 4549708 515 (-1279655))) (.r (.t (.l (-5817987) 4172580 513 (-1191083)) (.l (-5817987) 3934081 514 (-1049839))) (.t (.l (-5375049) 4172580 513 (-1136744)) (.l (-5375049) 3934081 514 (-1005663))))) (.t (.l (-4745388) 4549708 515 (-1169476)) (.r (.t (.l (-4950902) 4172580 513 (-1079316)) (.l (-4950902) 3934081 514 (-958129))) (.t (.l (-4544015) 4172580 513 (-1019196)) (.l (-4544015) 3934081 514 (-907633)))))) (.r (.t (.l (-5594065) 3595152 512 (-780797)) (.l (-5594065) 3177193 512 (-587939))) (.t (.l (-4745388) 3595152 512 (-721061)) (.l (-4745388) 3177193 512 (-552637)))))) (.r (.t (.r (.t (.l (-3963136) 4549708 515 (-1025589)) (.r (.t (.l (-4153039) 4172580 513 (-956735)) (.l (-4153039) 3934081 514 (-854522))) (.t (.l (-3776775) 4172580 513 (-892241)) (.l (-3776775) 3934081 514 (-799108))))) (.t (.l (-3237662) 4549708 515 (-875060)) (.r (.t (.l (-3414157) 4172580 513 (-825980)) (.l (-3414157) 3934081 514 (-741664))) (.t (.l (-3064229) 4172580 513 (-758187)) (.r (.l (-3150569) 3934081 514 (-699384)) (.l (-2978628) 3934081 514 (-669205))))))) (.r (.t (.r (.l (-4153039) 3595152 512 (-674473)) (.l (-3776775) 3595152 512 (-634549))) (.l (-3963136) 3177193 512 (-504594))) (.t (.r (.t (.l (-3414157) 3705657 513 (-663839)) (.l (-3414157) 3487083 512 (-592259))) (.t (.l (-3064229) 3705657 513 (-612385)) (.l (-3064229) 3487083 512 (-547838)))) (.l (-3237662) 3177193 512 (-445856))))) (.t (.r (.t (.l (-2561277) 4549708 515 (-719771)) (.r (.t (.l (-2726133) 4172580 513 (-689069)) (.r (.l (-2809591) 3934081 514 (-638650)) (.l (-2643366) 3934081 514 (-607748)))) (.t (.l (-2399096) 4172580 513 (-618810)) (.r (.t (.l (-2479858) 3992753 513 (-606579)) (.l (-2479858) 3876039 514 (-576515))) (.t (.l (-2318981) 3992753 513 (-573100)) (.l (-2318981) 3876039 514 (-544980))))))) (.t (.l (-1927758) 4549708 515 (-561159)) (.r (.t (.l (-2082416) 4172580 513 (-547570)) (.r (.t (.l (-2160650) 3992753 513 (-539364)) (.l (-2160650) 3876039 514 (-513154))) (.t (.l (-2004788) 3992753 513 (-505385)) (.l (-2004788) 3876039 514 (-481062))))) (.t (.l (-1775457) 4172580 513 (-475493)) (.r (.t (.l (-1851318) 3992753 513 (-471181)) (.l (-1851318) 3876039 514 (-448717))) (.t (.l (-1700168) 3992753 513 (-436772)) (.l (-1700168) 3876039 514 (-416139)))))))) (.r (.t (.r (.t (.l (-2726133) 3705657 513 (-559157)) (.l (-2726133) 3487083 512 (-501495))) (.t (.l (-2399096) 3705657 513 (-504347)) (.l (-2399096) 3487083 512 (-453423)))) (.l (-2561277) 3177193 512 (-378143))) (.t (.r (.t (.r (.l (-2160650) 3705657 513 (-463583)) (.l (-2004788) 3705657 513 (-435033))) (.l (-2082416) 3487083 512 (-403792))) (.t (.r (.l (-1851318) 3705657 513 (-406185)) (.t (.l (-1700168) 3761830 513 (-396239)) (.l (-1700168) 3650099 513 (-377059)))) (.l (-1775457) 3487083 512 (-352761)))) (.l (-1927758) 3177193 512 (-302904)))))))
def outerTree2:BoxTree:=.r (.t (.r (.l (-19572490) 1800859 512 0) (.l (-10678657) 1800859 512 (-952))) (.l (-14167786) 535121 511 0)) (.t (.r (.t (.l (-6047036) 2335382 513 (-122760)) (.l (-6047036) 1366069 511 0)) (.t (.l (-2893752) 2335382 513 (-132670)) (.l (-2893752) 1366069 511 0))) (.l (-4346615) 535121 511 0))
def outerTree3:BoxTree:=.t (.l (-779866) 19775781 566 0) (.t (.l (-779866) 10587945 524 (-405428)) (.t (.l (-779866) 7312771 518 (-424651)) (.l (-779866) 5566503 515 (-284995))))
def outerTree4:BoxTree:=.t (.t (.l (-779866) 2335382 513 (-55826)) (.l (-779866) 1366069 511 0)) (.l (-779866) 535121 511 0)
def outerTree5:BoxTree:=.t (.l 722956 19775781 566 0) (.t (.l 722956 10587945 524 1564680) (.t (.l 722956 7312771 518 626706) (.l 722956 5566503 515 429808)))
def outerTree6:BoxTree:=.t (.t (.l 722956 2335382 513 153215) (.l 722956 1366069 511 0)) (.l 722956 535121 511 0)
def outerTree7:BoxTree:=.t (.r (.l 3092962 19775781 566 0) (.l 5807929 19775781 566 0)) (.r (.t (.r (.l 2281060 10587945 524 4876625) (.t (.l 3843866 11866679 527 0) (.l 3843866 9404607 522 5642424))) (.r (.t (.l 2281060 7312771 518 2143837) (.r (.t (.l 1848973 5972144 515 1147308) (.l 1848973 5180730 514 958348)) (.t (.l 2695249 5972144 515 1762473) (.l 2695249 5180730 514 1481937)))) (.t (.l 3843866 7312771 518 3982470) (.r (.t (.l 3475461 5972144 515 2408483) (.l 3475461 5180730 514 2038016)) (.t (.l 4199181 5972144 515 3095554) (.r (.l 4023102 5180730 514 2430414) (.l 4372213 5180730 514 2732045))))))) (.t (.l 5807929 10587945 524 0) (.r (.t (.r (.l 4874040 7312771 518 5226365) (.t (.l 5506221 7802312 518 0) (.l 5506221 6844841 515 5340930))) (.r (.t (.l 4874040 5972144 515 3829945) (.r (.l 4709547 5180730 514 3045606) (.l 5035871 5180730 514 3371582))) (.t (.l 5506221 5972144 515 4614350) (.r (.t (.l 5351883 5371163 515 3710271) (.l 5351883 4995150 514 3435881)) (.t (.l 5658213 5371163 515 4061803) (.l 5658213 4995150 514 3767320)))))) (.t (.l 6385339 7312771 518 0) (.r (.t (.r (.l 5955438 5972144 515 5116580) (.l 6244082 5972144 515 0)) (.r (.t (.l 5955438 5371163 515 4426137) (.l 5955438 4995150 514 4111629)) (.t (.l 6244082 5371163 515 0) (.l 6244082 4995150 514 4468694)))) (.l 6662005 5566503 515 0))))))
def outerTree8:BoxTree:=.r (.r (.r (.t (.r (.t (.l 1625720 4549708 515 679073) (.r (.t (.l 1512196 4172580 513 536579) (.r (.t (.l 1454947 3992753 513 474574) (.l 1454947 3876039 514 456293)) (.t (.l 1569119 3992753 513 516041) (.l 1569119 3876039 514 496292)))) (.t (.l 1737969 4172580 513 626573) (.r (.t (.l 1682002 3992753 513 557787) (.l 1682002 3876039 514 536577)) (.t (.l 1793625 3992753 513 599829) (.l 1793625 3876039 514 577166)))))) (.t (.l 2067350 4549708 515 889895) (.r (.t (.l 1958757 4172580 513 717776) (.r (.t (.l 1904016 3992753 513 642186) (.l 1904016 3876039 514 618078)) (.l 2013201 3934081 514 684876))) (.t (.l 2174776 4172580 513 810340) (.r (.l 2121207 3934081 514 727918) (.l 2228059 3934081 514 771326)))))) (.r (.t (.r (.t (.r (.t (.l 1454947 3761830 513 438565) (.l 1454947 3650099 513 421376)) (.t (.l 1569119 3761830 513 477138) (.l 1569119 3650099 513 458562))) (.l 1512196 3487083 512 424031)) (.t (.r (.t (.l 1682002 3761830 513 516003) (.l 1682002 3650099 513 496050)) (.t (.l 1793625 3761830 513 555179) (.l 1793625 3650099 513 533853))) (.l 1737969 3487083 512 496686))) (.l 1625720 3177193 512 427884)) (.t (.r (.t (.r (.t (.l 1904016 3761830 513 594683) (.l 1904016 3650099 513 571989)) (.t (.l 2013201 3761830 513 634530) (.l 2013201 3650099 513 610471))) (.l 1958757 3487083 512 570690)) (.t (.r (.l 2121207 3705657 513 674735) (.l 2228059 3705657 513 715315)) (.l 2174776 3487083 512 646165))) (.l 2067350 3177193 512 567239)))) (.t (.r (.t (.l 2490299 4549708 515 1106461) (.r (.t (.l 2386226 4172580 513 904419) (.r (.l 2333782 3934081 514 815119) (.l 2438398 3934081 514 859313))) (.t (.l 2593298 4172580 513 1000159) (.l 2593298 3934081 514 930206)))) (.t (.l 2896082 4549708 515 1330114) (.r (.t (.l 2796169 4172580 513 1097701) (.l 2796169 3934081 514 1021795)) (.t (.l 2995006 4172580 513 1197186) (.l 2995006 3934081 514 1115323))))) (.r (.t (.r (.t (.r (.l 2333782 3705657 513 756286) (.l 2438398 3705657 513 797665)) (.l 2386226 3487083 512 723223)) (.t (.r (.l 2541931 3705657 513 839463) (.l 2644403 3705657 513 881701)) (.l 2593298 3487083 512 801982))) (.l 2490299 3177193 512 713027)) (.t (.r (.t (.l 2796169 3705657 513 950143) (.l 2796169 3487083 512 882558)) (.t (.l 2995006 3705657 513 1038017) (.l 2995006 3487083 512 965056))) (.l 2896082 3177193 512 866092))))) (.r (.t (.r (.t (.l 3286040 4549708 515 1562069) (.r (.t (.l 3189967 4172580 513 1298740) (.l 3189967 3934081 514 1210920)) (.t (.l 3381199 4172580 513 1402487) (.l 3381199 3934081 514 1308695)))) (.t (.l 3661360 4549708 515 1803417) (.r (.t (.l 3568842 4172580 513 1508552) (.l 3568842 3934081 514 1408763)) (.t (.l 3753029 4172580 513 1617045) (.l 3753029 3934081 514 1511238))))) (.r (.t (.r (.t (.l 3189967 3705657 513 1127943) (.l 3189967 3487083 512 1049598)) (.t (.l 3381199 3705657 513 1220031) (.l 3381199 3487083 512 1136274))) (.l 3286040 3177193 512 1027259)) (.t (.r (.t (.l 3568842 3705657 513 1314390) (.l 3568842 3487083 512 1225195)) (.t (.l 3753029 3705657 513 1411120) (.l 3753029 3487083 512 1316456))) (.l 3661360 3177193 512 1197312)))) (.t (.r (.t (.r (.l 3933885 4549708 515 1970801) (.l 4111528 4549708 515 2097490)) (.r (.t (.l 3933885 4172580 513 1728067) (.l 3933885 3934081 514 1616211)) (.t (.l 4111528 4172580 513 1841725) (.l 4111528 3934081 514 1723783)))) (.t (.r (.l 4286071 4549708 515 2226948) (.l 4457619 4549708 515 2359270)) (.r (.t (.l 4286071 4172580 513 1958100) (.l 4286071 3934081 514 1834045)) (.t (.l 4457619 4172580 513 2077278) (.l 4457619 3934081 514 1947074))))) (.r (.t (.r (.t (.l 3933885 3705657 513 1510323) (.l 3933885 3487083 512 1410152)) (.t (.l 4111528 3705657 513 1612092) (.l 4111528 3487083 512 1506374))) (.l 4023102 3177193 512 1376989)) (.t (.r (.t (.l 4286071 3705657 513 1716506) (.l 4286071 3487083 512 1605197)) (.t (.l 4457619 3705657 513 1823650) (.l 4457619 3487083 512 1706715))) (.l 4372213 3177193 512 1566951)))))) (.r (.r (.t (.r (.t (.r (.l 4626274 4549708 515 2494533) (.l 4792131 4549708 515 2632802)) (.r (.t (.l 4626274 4172580 513 2199336) (.l 4626274 3934081 514 2062946)) (.t (.l 4792131 4172580 513 2324344) (.l 4792131 3934081 514 2181725)))) (.t (.r (.l 4955283 4549708 515 2774130) (.l 5115815 4549708 515 2918572)) (.r (.t (.l 4955283 4172580 513 2452350) (.l 4955283 3934081 514 2303480)) (.t (.l 5115815 4172580 513 2583421) (.l 5115815 3934081 514 2428256))))) (.r (.t (.r (.t (.l 4626274 3705657 513 1933597) (.l 4626274 3487083 512 1810989)) (.t (.l 4792131 3705657 513 2046415) (.l 4792131 3487083 512 1918090))) (.l 4709547 3177193 512 1767801)) (.t (.r (.t (.l 4955283 3705657 513 2162166) (.l 4955283 3487083 512 2028074)) (.t (.l 5115815 3705657 513 2280898) (.l 5115815 3487083 512 2141003))) (.l 5035871 3177193 512 1980042)))) (.t (.r (.t (.r (.l 5273811 4549708 515 3066173) (.l 5429349 4549708 515 3216943)) (.r (.t (.l 5273811 4172580 513 2717596) (.l 5273811 3934081 514 2556107)) (.t (.l 5429349 4172580 513 2854907) (.l 5429349 3934081 514 2687059)))) (.t (.r (.l 5582505 4549708 515 3370926) (.l 5733351 4549708 515 3528120)) (.r (.t (.l 5582505 4172580 513 2995382) (.l 5582505 3934081 514 2821148)) (.t (.l 5733351 4172580 513 3139039) (.l 5733351 3934081 514 2958404))))) (.r (.t (.r (.t (.l 5273811 3705657 513 2402664) (.l 5273811 3487083 512 2256922)) (.t (.l 5429349 3705657 513 2527498) (.l 5429349 3487083 512 2375874))) (.l 5351883 3177193 512 2204099)) (.t (.r (.t (.l 5582505 3705657 513 2655444) (.l 5582505 3487083 512 2497897)) (.t (.l 5733351 3705657 513 2786521) (.l 5733351 3487083 512 2623012))) (.l 5658213 3177193 512 2440294))))) (.r (.t (.r (.t (.r (.l 5881955 4549708 515 3688535) (.t (.l 6028383 4680692 514 3852158) (.l 6028383 4421378 514 3639060))) (.r (.t (.l 5881955 4172580 513 3285897) (.l 5881955 3934081 514 3098832)) (.t (.l 6028383 4172580 513 3435956) (.l 6028383 3934081 514 3242448)))) (.t (.r (.t (.l 6172698 4680692 514 4018991) (.l 6172698 4421378 514 3798993)) (.t (.l 6314960 4680692 514 4189005) (.l 6314960 4421378 514 3962110))) (.r (.t (.l 6172698 4172580 513 3589214) (.l 6172698 3934081 514 3389248)) (.t (.l 6314960 4172580 513 3745656) (.l 6314960 3934081 514 3539229))))) (.r (.t (.r (.t (.l 5881955 3705657 513 2920745) (.l 5881955 3487083 512 2751252)) (.t (.l 6028383 3705657 513 3058132) (.l 6028383 3487083 512 2882628))) (.l 5955438 3177193 512 2688857)) (.t (.r (.t (.l 6172698 3705657 513 3198690) (.l 6172698 3487083 512 3017152)) (.t (.l 6314960 3705657 513 3342420) (.l 6314960 3487083 512 3154823))) (.l 6244082 3177193 512 2949925)))) (.l 6662005 3818624 515 0)))
def outerTree9:BoxTree:=.r (.t (.r (.t (.r (.l 1848973 2335382 513 430994) (.l 2695249 2335382 513 691954)) (.l 2281060 1366069 511 0)) (.t (.r (.l 3475461 2335382 513 984844) (.l 4199181 2335382 513 1315136)) (.l 3843866 1366069 511 0))) (.l 3092962 535121 511 0)) (.t (.r (.t (.r (.l 4874040 2335382 513 1687598) (.l 5506221 2335382 513 2105958)) (.l 5195125 1366069 511 0)) (.t (.r (.l 6100801 2335382 513 2572678) (.l 6662005 2335382 513 0)) (.l 6385339 1366069 511 0))) (.l 5807929 535121 511 0))
lemma outer_regions_cert :
  cT0 (-9600000) (-1500000) (-15000000) 3500000 outerTree0=true /\
  cT0 (-9600000) (-1500000) 3500000 7000000 outerTree1=true /\
  cT0 (-9600000) (-1500000) 7000000 20000000 outerTree2=true /\
  cT0 (-1500000) 0 (-15000000) 3500000 outerTree3=true /\
  cT0 (-1500000) 0 7000000 20000000 outerTree4=true /\
  cT0 0 1500000 (-15000000) 3500000 outerTree5=true /\
  cT0 0 1500000 7000000 20000000 outerTree6=true /\
  cT0 1500000 10000000 (-15000000) 3500000 outerTree7=true /\
  cT0 1500000 10000000 3500000 7000000 outerTree8=true /\
  cT0 1500000 10000000 7000000 20000000 outerTree9=true:=by decide
lemma gStar_ge_gLoVal:((gLoVal:R)/S0)<=gStar:=by
 have hs:(0:R) < S0:=fpS_pos
 have ht:=tStar_mem
 have hgam:gC=(gI:R)/S0:=by norm_num [gC,gI,S0,fpS]
 have htsq:tStar^2/2<=((dC (tRInt*tRInt) (2*fpS):ℤ):R)/S0:=by
  have h1:tStar^2<=((tRInt:R)/S0)^2:=by
   have ht0:0<=tStar:=le_trans (by norm_num [tLInt,S0,fpS]) ht.1
   nlinarith [ht.2]
  have hd:=le_divCe (a:=tRInt*tRInt) (b:=2*fpS) (by norm_num [S0,fpS])
  have h2:((tRInt:R)/S0)^2/2<=((dC (tRInt*tRInt) (2*fpS):ℤ):R)/S0:=by
   calc ((tRInt:R)/S0)^2/2
     = ((tRInt:R)*(tRInt:R)/(2*S0))/S0:=by field_simp
    _ <= ((dC (tRInt*tRInt) (2*fpS):ℤ):R)/S0 :=
      dld (by simpa [Int.cast_mul] using hd) hs.le
  linarith
 have hph_le:((cL (tLInt - gI):ℤ):R)/S0<=pC (tStar - gC):=by
  refine (phiCDFLo_le (tLInt - gI)).trans (pCm.monotone ?_)
  rw [hgam,Int.cast_sub,sub_div];linarith [ht.1]
 have hok:=oLLs (by decide:oLL (cL (tLInt - gI)) (-3828512)=true)
 have hlog:(((-3828512:ℤ):R)/S0)<=log (pC (tStar - gC)) :=
  hok.2.trans (log_le_log (div_pos (by exact_mod_cast hok.1) hs) hph_le)
 have hval:((gLoVal:R)/S0)<=((gLoInt:R)/S0) :=
  dld (by exact_mod_cast cert_gA_vals.1) hs.le
 unfold gStar
 unfold gLoInt at hval
 rw [Int.cast_add,Int.cast_neg,add_div,neg_div] at hval
 linarith
lemma aConst_bounds :
  ((aLoVal:R)/S0)<=aConst/\aConst<=((aHiVal:R)/S0):=by
 have hs:(0:R) < S0:=fpS_pos
 have ht:=tStar_mem
 have hgam:gC=(gI:R)/S0:=by norm_num [gC,gI,S0,fpS]
 have hx_lo:(xLInt:R)/S0<=tStar - gC:=by
  unfold xLInt;rw [hgam,Int.cast_sub,sub_div];linarith [ht.1]
 have hx_hi:tStar - gC<=(xRInt:R)/S0:=by
  unfold xRInt;rw [hgam,Int.cast_sub,sub_div];linarith [ht.2]
 have hx_pos:(0:R) < (xLInt:R)/S0:=by norm_num [xLInt,tLInt,gI,S0,fpS]
 have hph_lo:((cL xLInt:ℤ):R)/S0<=pC (tStar - gC) :=
  (phiCDFLo_le xLInt).trans (pCm.monotone hx_lo)
 have hph_hi:pC (tStar - gC)<=((cH xRInt:ℤ):R)/S0 :=
  (pCm.monotone hx_hi).trans (le_phiCDFHi xRInt)
 have hph_chk:500<=cL xLInt/\cL xLInt<=4*fpS /\
   500<=cH xRInt/\cH xRInt<=4*fpS /\
   0 < mF (cL xLInt) (cL xLInt) /\
   0 < mC (cH xRInt) (cH xRInt) /\
   0<=eL (-dC (xRInt*xRInt) fpS) /\
   0<=dF (xLInt*xLInt) fpS/\0<=dC (xRInt*xRInt) fpS:=by decide
 have hph_lo_pos:(0:R) < ((cL xLInt:ℤ):R)/S0 :=
  div_pos (by exact_mod_cast (by omega:0 < cL xLInt)) hs
 have hlog_lo:(((-3828512:ℤ):R)/S0)<=log (pC (tStar - gC)) :=
  (oLLs (by decide:oLL (cL xLInt) (-3828512)=true)).2.trans (log_le_log hph_lo_pos hph_lo)
 have hlog_hi:log (pC (tStar - gC))<=(((-3828240:ℤ):R)/S0) :=
  (log_le_log (pCp _) hph_hi).trans (oLHs (by decide:oLH (cH xRInt) (-3828240)=true)).2
 have hexp_lo:((eL (-dC (xRInt*xRInt) fpS):ℤ):R)/S0 <=
   exp (-(tStar - gC)^2):=by
  have h1:=expNegLo_le (x:=-dC (xRInt*xRInt) fpS) (by omega)
  have h2:-(tStar - gC)^2 >= -((dC (xRInt*xRInt) fpS:ℤ):R)/S0:=by
   have hsq:(tStar - gC)^2<=((xRInt:R)/S0)^2:=by nlinarith [hx_lo,hx_hi,hx_pos]
   have hd:=le_mulCe xRInt xRInt
   have hd':((xRInt:R)/S0)^2<=((dC (xRInt*xRInt) fpS:ℤ):R)/S0:=by
    simpa [sq,mC,dC] using hd
   rw [neg_div];linarith
  refine h1.trans (exp_le_exp.mpr ?_)
  simpa [neg_div] using h2
 have hexp_hi:exp (-(tStar - gC)^2) <=
   ((eH (-dF (xLInt*xLInt) fpS):ℤ):R)/S0:=by
  have h1:=le_expNegHi (x:=-dF (xLInt*xLInt) fpS) (by omega)
  have h2:-(tStar - gC)^2 <= -((dF (xLInt*xLInt) fpS:ℤ):R)/S0:=by
   have hsq:((xLInt:R)/S0)^2<=(tStar - gC)^2:=by nlinarith [hx_lo,hx_pos]
   have hd:((dF (xLInt*xLInt) fpS:ℤ):R)/S0<=((xLInt:R)/S0)^2:=by
    simpa [sq,mF,dF] using mulFl_le xLInt xLInt
   rw [neg_div];linarith
  refine (exp_le_exp.mpr ?_).trans h1
  simpa [neg_div] using h2
 have h4pi_lo:((i40:ℤ):R)/S0<=(4*PI)⁻¹:=by
  have h1:=pi_bounds_inv2Pi.1
  have h2:((i40:ℤ):R)<=((iP0:ℤ):R)/2:=by norm_num [i40,iP0]
  have h3:(4*PI)⁻¹=(2*PI)⁻¹ / 2:=by ring
  rw [h3]
  calc ((i40:ℤ):R)/S0<=(((iP0:ℤ):R)/2)/S0 :=
     dld h2 hs.le
   _ = (((iP0:ℤ):R)/S0)/2:=by ring
   _ <= (2*PI)⁻¹ / 2:=by linarith
 have h4pi_hi:(4*PI)⁻¹<=((i41:ℤ):R)/S0:=by
  have h1:=pi_bounds_inv2Pi.2
  have h2:((iP1:ℤ):R)/2<=((i41:ℤ):R):=by norm_num [i41,iP1,dC]
  have h3:(4*PI)⁻¹=(2*PI)⁻¹ / 2:=by ring
  rw [h3]
  calc (2*PI)⁻¹ / 2<=(((iP1:ℤ):R)/S0)/2:=by linarith
   _ = (((iP1:ℤ):R)/2)/S0:=by ring
   _ <= ((i41:ℤ):R)/S0:=dld h2 hs.le
 have hden_lo:((mF (cL xLInt) (cL xLInt):ℤ):R)/S0 <=
   (pC (tStar - gC))^2:=by
  calc ((mF (cL xLInt) (cL xLInt):ℤ):R)/S0
    <= (((cL xLInt:ℤ):R)/S0)*(((cL xLInt:ℤ):R)/S0):=mulFl_le _ _
   _ <= (pC (tStar - gC))^2:=by rw [sq];exact mul_self_le_mul_self hph_lo_pos.le hph_lo
 have hden_hi:(pC (tStar - gC))^2 <=
   ((mC (cH xRInt) (cH xRInt):ℤ):R)/S0:=by
  calc (pC (tStar - gC))^2
    = pC (tStar - gC)*pC (tStar - gC):=sq _
   _ <= (((cH xRInt:ℤ):R)/S0)*(((cH xRInt:ℤ):R)/S0) :=
     mul_self_le_mul_self (pCp _).le hph_hi
   _ <= ((mC (cH xRInt) (cH xRInt):ℤ):R)/S0:=le_mulCe _ _
 have hfrac_lo:((dF (i40*eL (-dC (xRInt*xRInt) fpS))
   (mC (cH xRInt) (cH xRInt)):ℤ):R)/S0 <=
   exp (-(tStar - gC)^2)/(4*PI*(pC (tStar - gC))^2):=by
  have hd:=divFl_le (a:=i40*eL (-dC (xRInt*xRInt) fpS))
   (b:=mC (cH xRInt) (cH xRInt)) hph_chk.2.2.2.2.2.1
  have hnum_le:(((i40:ℤ):R)/S0)*(((eL (-dC (xRInt*xRInt) fpS):ℤ):R)/S0) <=
    (4*PI)⁻¹*exp (-(tStar - gC)^2) :=
   mul_le_mul h4pi_lo hexp_lo (div_nonneg (by exact_mod_cast hph_chk.2.2.2.2.2.2.1) hs.le) (by positivity)
  have hden_pos:(0:R) < ((mC (cH xRInt) (cH xRInt):ℤ):R)/S0 :=
   div_pos (by exact_mod_cast hph_chk.2.2.2.2.2.1) hs
  have hstep1:((dF (i40*eL (-dC (xRInt*xRInt) fpS))
    (mC (cH xRInt) (cH xRInt)):ℤ):R)/S0 <=
    ((((i40:ℤ):R)/S0)*(((eL (-dC (xRInt*xRInt) fpS):ℤ):R)/S0)) /
    (((mC (cH xRInt) (cH xRInt):ℤ):R)/S0):=by
   have h1:((dF (i40*eL (-dC (xRInt*xRInt) fpS))
     (mC (cH xRInt) (cH xRInt)):ℤ):R)/S0 <=
     ((i40:R)*(eL (-dC (xRInt*xRInt) fpS):R) /
      (mC (cH xRInt) (cH xRInt):R))/S0 :=
    dld (by simpa [Int.cast_mul] using hd) hs.le
   refine h1.trans_eq ?_
   have hne:((mC (cH xRInt) (cH xRInt):ℤ):R) ≠ 0:=by
    exact_mod_cast (ne_of_gt hph_chk.2.2.2.2.2.1)
   field_simp
  have hstep2:((((i40:ℤ):R)/S0)*(((eL (-dC (xRInt*xRInt) fpS):ℤ):R)/S0)) /
    (((mC (cH xRInt) (cH xRInt):ℤ):R)/S0) <=
    ((4*PI)⁻¹*exp (-(tStar - gC)^2))/(pC (tStar - gC))^2:=by
   exact div_le_div₀ (by positivity) hnum_le (sq_pos_of_pos (pCp _)) hden_hi
  refine (hstep1.trans hstep2).trans_eq ?_
  ring
 have hfrac_hi:exp (-(tStar - gC)^2)/(4*PI*(pC (tStar - gC))^2) <=
   ((dC (i41*eH (-dF (xLInt*xLInt) fpS))
    (mF (cL xLInt) (cL xLInt)):ℤ):R)/S0:=by
  have hd:=le_divCe (a:=i41*eH (-dF (xLInt*xLInt) fpS))
   (b:=mF (cL xLInt) (cL xLInt)) hph_chk.2.2.2.2.1
  have hnum_le:(4*PI)⁻¹*exp (-(tStar - gC)^2) <=
    (((i41:ℤ):R)/S0)*(((eH (-dF (xLInt*xLInt) fpS):ℤ):R)/S0) :=
   mul_le_mul h4pi_hi hexp_hi (exp_nonneg _) (by norm_num [i41,iP1,dC,S0,fpS])
  have hden_pos:(0:R) < ((mF (cL xLInt) (cL xLInt):ℤ):R)/S0 :=
   div_pos (by exact_mod_cast hph_chk.2.2.2.2.1) hs
  have hstep1:((4*PI)⁻¹*exp (-(tStar - gC)^2))/(pC (tStar - gC))^2 <=
    ((((i41:ℤ):R)/S0)*(((eH (-dF (xLInt*xLInt) fpS):ℤ):R)/S0)) /
    (((mF (cL xLInt) (cL xLInt):ℤ):R)/S0) :=
   div_le_div₀ (le_trans (by positivity) hnum_le) hnum_le hden_pos hden_lo
  have hstep2:((((i41:ℤ):R)/S0)*(((eH (-dF (xLInt*xLInt) fpS):ℤ):R)/S0)) /
    (((mF (cL xLInt) (cL xLInt):ℤ):R)/S0) <=
    ((dC (i41*eH (-dF (xLInt*xLInt) fpS))
     (mF (cL xLInt) (cL xLInt)):ℤ):R)/S0:=by
   have h1:((i41:R)*(eH (-dF (xLInt*xLInt) fpS):R) /
     (mF (cL xLInt) (cL xLInt):R))/S0 <=
     ((dC (i41*eH (-dF (xLInt*xLInt) fpS))
      (mF (cL xLInt) (cL xLInt)):ℤ):R)/S0 :=
    dld (by simpa [Int.cast_mul] using hd) hs.le
   refine le_trans (le_of_eq ?_) h1
   have hne:((mF (cL xLInt) (cL xLInt):ℤ):R) ≠ 0:=by
    exact_mod_cast (ne_of_gt hph_chk.2.2.2.2.1)
   field_simp
  have hrew:exp (-(tStar - gC)^2)/(4*PI*(pC (tStar - gC))^2) =
    ((4*PI)⁻¹*exp (-(tStar - gC)^2))/(pC (tStar - gC))^2:=by ring
  rw [hrew]
  exact hstep1.trans hstep2
 have hhalf:((fpS/2:ℤ):R)/S0=1/2:=by norm_num [S0,fpS]
 have hval_lo:((aLoVal:R)/S0)<=((aLoInt:R)/S0) :=
  dld (by exact_mod_cast cert_gA_vals.2.1) hs.le
 have hval_hi:((aHiInt:R)/S0)<=((aHiVal:R)/S0) :=
  dld (by exact_mod_cast cert_gA_vals.2.2) hs.le
 unfold aConst
 constructor
 .
  unfold aLoInt at hval_lo
  rw [Int.cast_sub,Int.cast_add,sub_div,add_div,hhalf] at hval_lo
  linarith
 .
  unfold aHiInt at hval_hi
  rw [Int.cast_sub,Int.cast_add,sub_div,add_div,hhalf] at hval_hi
  linarith
lemma maxQuadHi_sound {aLo aHi t0 t1 tm:ℤ} {a t:R}
  (ha_lo:(aLo:R)/S0<=a) (ha_hi:a<=(aHi:R)/S0)
  (ht0:(t0:R)/S0<=t) (ht1:t<=(t1:R)/S0) :
  -t^2/2+a*(t - (tm:R)/S0)<=((mQH aLo aHi t0 t1 tm:ℤ):R)/S0:=by
 have hs:(0:R) < S0:=fpS_pos
 have heval:∀ (aI:ℤ),
   -t^2/2+((aI:R)/S0)*(t - (tm:R)/S0) <=
    ((eQA t0 t1 tm aI:ℤ):R)/S0:=by
  intro aI
  set tcI:ℤ:=max t0 (min t1 aI)
  have htc_quad:-t^2/2+((aI:R)/S0)*t <=
    -((tcI:R)/S0)^2/2+((aI:R)/S0)*((tcI:R)/S0):=by
   have h1:(t0:R)/S0<=(tcI:R)/S0 :=
    dld (by exact_mod_cast le_max_left t0 (min t1 aI)) hs.le
   have h2:(tcI:R)/S0<=(t1:R)/S0:=by
    have hle:tcI<=t1:=max_le (by
     have:(t0:R)/S0<=(t1:R)/S0:=ht0.trans ht1
     have:(t0:R)<=(t1:R):=(div_le_div_iff_of_pos_right hs).mp this
     exact_mod_cast this) (min_le_left t1 aI)
    exact dld (by exact_mod_cast hle) hs.le
   have hprod:0<=(((tcI:R)/S0) - ((aI:R)/S0))*(t - ((tcI:R)/S0)):=by
    by_cases hlt:aI < t0
    .
     have heq:tcI=t0:=max_eq_left (le_trans (min_le_right _ _) hlt.le)
     have h3:(aI:R)/S0<=(tcI:R)/S0:=by
      rw [heq];exact dld (by exact_mod_cast hlt.le) hs.le
     have h4:(tcI:R)/S0<=t:=by rw [heq];exact ht0
     nlinarith
    .
     by_cases hgt:t1 < aI
     .
      have h01:t0<=t1:=by
       have:(t0:R)<=(t1:R):=(div_le_div_iff_of_pos_right hs).mp (ht0.trans ht1)
       exact_mod_cast this
      have heq:tcI=t1:=by
       unfold tcI;rw [min_eq_left hgt.le,max_eq_right h01]
      have h3:(tcI:R)/S0<=(aI:R)/S0:=by
       rw [heq];exact dld (by exact_mod_cast hgt.le) hs.le
      have h4:t<=(tcI:R)/S0:=by rw [heq];exact ht1
      nlinarith
     .
      have heq:tcI=aI:=by
       unfold tcI;rw [min_eq_right (le_of_not_gt hgt),max_eq_right (le_of_not_gt hlt)]
      rw [heq];simp
   nlinarith [sq_nonneg (t - (tcI:R)/S0)]
  have hsq_fl:-((tcI:R)/S0)^2/2 <= -((dF (tcI*tcI) (2*fpS):ℤ):R)/S0:=by
   have hd:=divFl_le (a:=tcI*tcI) (b:=2*fpS) (by norm_num [S0,fpS])
   have h1:((dF (tcI*tcI) (2*fpS):ℤ):R)/S0<=((tcI:R)/S0)^2/2:=by
    calc ((dF (tcI*tcI) (2*fpS):ℤ):R)/S0
      <= ((tcI:R)*(tcI:R)/(2*S0))/S0 :=
       dld (by simpa [Int.cast_mul] using hd) hs.le
     _ = ((tcI:R)/S0)^2/2:=by field_simp
   rw [neg_div,neg_div];linarith
  have hmul_ce:((aI:R)/S0)*(((tcI:R)/S0) - ((tm:R)/S0)) <=
    ((dC (aI*(tcI - tm)) fpS:ℤ):R)/S0:=by
   have hm:=le_mulCe aI (tcI - tm)
   simpa [mC,dC,Int.cast_sub,sub_div] using hm
  unfold eQA
  dsimp only
  rw [Int.cast_add,Int.cast_neg,add_div,neg_div]
  linarith
 unfold mQH
 by_cases hsign:0<=t - (tm:R)/S0
 .
  have hlin:a*(t - (tm:R)/S0)<=((aHi:R)/S0)*(t - (tm:R)/S0) :=
   mlR ha_hi hsign
  have hmax:((eQA t0 t1 tm aHi:ℤ):R)/S0 <=
    ((max (eQA t0 t1 tm aLo) (eQA t0 t1 tm aHi):ℤ):R)/S0 :=
   dld (by exact_mod_cast le_max_right _ _) hs.le
  linarith [heval aHi]
 .
  have hlin:a*(t - (tm:R)/S0)<=((aLo:R)/S0)*(t - (tm:R)/S0) :=
   mul_le_mul_of_nonpos_right ha_lo (le_of_not_ge hsign)
  have hmax:((eQA t0 t1 tm aLo:ℤ):R)/S0 <=
    ((max (eQA t0 t1 tm aLo) (eQA t0 t1 tm aHi):ℤ):R)/S0 :=
   dld (by exact_mod_cast le_max_left _ _) hs.le
  linarith [heval aLo]
lemma hc_concave_tangent (cLog K ρ₀ ρ:R) (hρ₀0:-1 < ρ₀) (hρ₀1:ρ₀ < 1) (hρ0:-1 < ρ) (hρ1:ρ < 1) :
  let H:=fun r:R=>cLog*(1+r) - ((1+r)/2)*log (1+r) - aConst*r - bConst*r^3+K*r
  let H':=fun r:R=>cLog - (log (1+r)+1)/2 - aConst - 3*bConst*r^2+K
  H ρ<=H ρ₀+H' ρ₀*(ρ - ρ₀):=by
 intro H H'
 have hHd:∀ r ∈ Set.Ioo (-1:R) 1,HD H (H' r) r:=by
  intro r hr
  have h1r:0 < 1+r:=by linarith [hr.1]
  have h1:HD (fun x:R=>cLog*(1+x)) cLog r:=by
   have ha:=((hasDerivAt_const r (1:R)).fun_add (hdi r)).const_mul cLog
   rwa [show cLog*(0+1)=cLog by ring] at ha
  have h2:HD (fun x:R=>((1+x)/2)*log (1+x)) ((log (1+r)+1)/2) r:=by
   have ha:HD (fun x:R=>(1+x)/2) (1/2) r:=by
    have h:=((hasDerivAt_const r (1:R)).fun_add (hdi r)).div_const 2
    rwa [zero_add] at h
   have hb:HD (fun x:R=>log (1+x)) (1+r)⁻¹ r:=by
    have h:=((hasDerivAt_const r (1:R)).fun_add (hdi r)).log h1r.ne'
    rwa [zero_add,one_div] at h
   have hc:=ha.fun_mul hb
   have heq:1/2*log (1+r)+(1+r)/2*(1+r)⁻¹=(log (1+r)+1)/2:=by
    field_simp [h1r.ne']
   rwa [heq] at hc
  have h3:HD (fun x:R=>aConst*x) aConst r:=by
   simpa using (hdi r).const_mul aConst
  have h4:HD (fun x:R=>bConst*x^3) (3*bConst*r^2) r:=by
   have h:=(hdp 3 r).const_mul bConst
   rwa [show bConst*(((3:ℕ):R)*r^(3 - 1))=3*bConst*r^2 by norm_num;ring] at h
  have h5:HD (fun x:R=>K*x) K r:=by
   simpa using (hdi r).const_mul K
  exact (((h1.fun_sub h2).fun_sub h3).fun_sub h4).fun_add h5
 have hH'_anti:StrictAntiOn H' (Set.Ioo (-1:R) 1):=by
  have hH'd:∀ r ∈ Set.Ioo (-1:R) 1,HD H' (-(2*(1+r))⁻¹ - 6*bConst*r) r:=by
   intro r hr
   have h1r:0 < 1+r:=by linarith [hr.1]
   have h1:HD (fun x:R=>(log (1+x)+1)/2) ((2*(1+r))⁻¹) r:=by
    have ha:HD (fun x:R=>log (1+x)) (1+r)⁻¹ r:=by
     have h:=((hasDerivAt_const r (1:R)).fun_add (hdi r)).log h1r.ne'
     rwa [zero_add,one_div] at h
    have hb:=(ha.fun_add (hasDerivAt_const r (1:R))).div_const 2
    have heq:((1+r)⁻¹+0)/2=(2*(1+r))⁻¹:=by field_simp [h1r.ne'];ring
    rwa [heq] at hb
   have h2:HD (fun x:R=>3*bConst*x^2) (6*bConst*r) r:=by
    have h:=(hdp 2 r).const_mul (3*bConst)
    rwa [show 3*bConst*(((2:ℕ):R)*r^(2 - 1))=6*bConst*r by norm_num;ring] at h
   have htot:=((((hasDerivAt_const r cLog).fun_sub h1).fun_sub (hasDerivAt_const r aConst)).fun_sub h2).fun_add
    (hasDerivAt_const r K)
   rwa [show 0 - (2*(1+r))⁻¹ - 0 - 6*bConst*r+0 = -(2*(1+r))⁻¹ - 6*bConst*r by ring] at htot
  refine strictAntiOn_of_deriv_neg (convex_Ioo (-1) 1) ?_ ?_
  .
   exact continuousOn_iff_continuous_domRestrict.mpr (continuous_iff_continuousAt.mpr fun x =>
    ((hH'd x.1 x.2).continuousAt).comp continuous_subtype_val.continuousAt)
  .
   intro r hr
   rw [interior_Ioo] at hr
   rw [(hH'd r hr).deriv]
   have h1r:0 < 1+r:=by linarith [hr.1]
   have hquad:0 < 1+(36/25:R)*r*(1+r):=by
    nlinarith [sq_nonneg (r+1/2)]
   have hpos:0 < 2*(1+r):=by linarith
   unfold bConst
   have:-(2*(1+r))⁻¹ - 6*(3/25:R)*r = -(1+(36/25:R)*r*(1+r))/(2*(1+r)):=by
    field_simp [h1r.ne'];ring
   rw [this]
   exact div_neg_of_neg_of_pos (by linarith) hpos
 let F:R->R:=fun r=>H r - H ρ₀ - H' ρ₀*(r - ρ₀)
 have hFd:∀ r ∈ Set.Ioo (-1:R) 1,HD F (H' r - H' ρ₀) r:=by
  intro r hr
  have hlin:HD (fun x:R=>H' ρ₀*(x - ρ₀)) (H' ρ₀) r:=by
   have h:=((hdi r).fun_sub (hasDerivAt_const r ρ₀)).const_mul (H' ρ₀)
   rwa [show H' ρ₀*(1 - 0)=H' ρ₀ by ring] at h
  have h:=((hHd r hr).fun_sub (hasDerivAt_const r (H ρ₀))).fun_sub hlin
  rwa [sub_zero] at h
 have hF0:F ρ₀=0:=by simp [F]
 have hFρ:F ρ<=0:=by
  by_cases hle:ρ₀<=ρ
  .
   have hsub:Set.Icc ρ₀ ρ ⊆ Set.Ioo (-1:R) 1:=fun x hx=>⟨by linarith [hx.1],by linarith [hx.2]⟩
   have hanti:AntitoneOn F (Set.Icc ρ₀ ρ) :=
    antitoneOn_of_deriv_nonpos (convex_Icc ρ₀ ρ)
     (fun x hx=>(hFd x (hsub hx)).continuousAt.continuousWithinAt)
     (fun x hx=>(hFd x (hsub (interior_subset hx))).differentiableAt.differentiableWithinAt)
     (fun x hx=>by
      rw [interior_Icc] at hx
      rw [(hFd x (hsub ⟨hx.1.le,hx.2.le⟩)).deriv]
      linarith [hH'_anti ⟨hρ₀0,hρ₀1⟩ (hsub ⟨hx.1.le,hx.2.le⟩) hx.1])
   linarith [hanti ⟨le_rfl,hle⟩ ⟨hle,le_rfl⟩ hle,hF0]
  .
   have hle':ρ<=ρ₀:=le_of_not_ge hle
   have hsub:Set.Icc ρ ρ₀ ⊆ Set.Ioo (-1:R) 1:=fun x hx=>⟨by linarith [hx.1],by linarith [hx.2]⟩
   have hmono:MonotoneOn F (Set.Icc ρ ρ₀) :=
    monotoneOn_of_deriv_nonneg (convex_Icc ρ ρ₀)
     (fun x hx=>(hFd x (hsub hx)).continuousAt.continuousWithinAt)
     (fun x hx=>(hFd x (hsub (interior_subset hx))).differentiableAt.differentiableWithinAt)
     (fun x hx=>by
      rw [interior_Icc] at hx
      rw [(hFd x (hsub ⟨hx.1.le,hx.2.le⟩)).deriv]
      linarith [hH'_anti (hsub ⟨hx.1.le,hx.2.le⟩) ⟨hρ₀0,hρ₀1⟩ hx.2])
   linarith [hmono ⟨le_rfl,hle'⟩ ⟨hle',le_rfl⟩ hle',hF0]
 unfold F at hFρ
 linarith
lemma hHs {r0 r1 cLogLo cLogHi kLo kHi l1Lo l1Hi:ℤ} {cLog K ρ:R}
  (hr0_gt:-fpS < r0) (hr01:r0 < r1) (hr1_le:r1<=fpS)
  (hρ0:(r0:R)/S0<=ρ) (hρ1:ρ<=(r1:R)/S0) (hρ_lt:ρ < 1)
  (hc_lo:(cLogLo:R)/S0<=cLog) (hc_hi:cLog<=(cLogHi:R)/S0)
  (hk_lo:(kLo:R)/S0<=K) (hk_hi:K<=(kHi:R)/S0)
  (hl1_lo:oLL (fpS+(r0+r1)/2) l1Lo=true)
  (hl1_hi:oLH (fpS+(r0+r1)/2) l1Hi=true) :
  cLog*(1+ρ) - ((1+ρ)/2)*log (1+ρ) - aConst*ρ - bConst*ρ^3+K*ρ <=
   ((hH0 r0 r1 cLogLo cLogHi kLo kHi l1Lo l1Hi:ℤ):R)/S0:=by
 have hs:(0:R) < S0:=fpS_pos
 set rm:ℤ:=(r0+r1)/2
 have hrm_gt:-fpS < rm:=by omega
 have hrm_lt:rm < fpS:=by omega
 have hrm_lo_r:(-1:R) < (rm:R)/S0:=by
  rw [lt_div_iff₀ hs];norm_num;exact_mod_cast hrm_gt
 have hrm_hi_r:(rm:R)/S0 < 1:=by
  rw [div_lt_one hs];exact_mod_cast hrm_lt
 have hρ_gt:(-1:R) < ρ:=lt_of_lt_of_le (by rw [lt_div_iff₀ hs];norm_num;exact_mod_cast hr0_gt) hρ0
 have htan:=hc_concave_tangent cLog K ((rm:R)/S0) ρ hrm_lo_r hrm_hi_r hρ_gt hρ_lt
 dsimp only at htan
 have h1rm_eq:(1:R)+(rm:R)/S0=((fpS+rm:ℤ):R)/S0:=by
  rw [Int.cast_add,add_div,div_self hs.ne']
 have h1rm_pos:(0:R) < ((fpS+rm:ℤ):R)/S0:=by
  rw [← h1rm_eq];linarith
 have hlog_lo:=(oLLs hl1_lo).2
 have hlog_hi:=(oLHs hl1_hi).2
 rw [← h1rm_eq] at hlog_lo hlog_hi
 have ha:=aConst_bounds
 have ht1:cLog*(1+(rm:R)/S0)<=((mC cLogHi (fpS+rm):ℤ):R)/S0:=by
  rw [h1rm_eq]
  exact (mlR hc_hi h1rm_pos.le).trans (le_mulCe cLogHi (fpS+rm))
 have ht2:-(((1+(rm:R)/S0)/2)*log (1+(rm:R)/S0)) <=
   -((dF ((fpS+rm)*l1Lo) (2*fpS):ℤ):R)/S0:=by
  have h1:(((fpS+rm:ℤ):R)/S0)*((l1Lo:R)/S0)/2 <=
    ((1+(rm:R)/S0)/2)*log (1+(rm:R)/S0):=by
   rw [h1rm_eq]
   have h1':(((fpS+rm:ℤ):R)/S0)*((l1Lo:R)/S0) <=
     (((fpS+rm:ℤ):R)/S0)*log (((fpS+rm:ℤ):R)/S0) :=
    mlL (by rwa [h1rm_eq] at hlog_lo) h1rm_pos.le
   linarith
  have hd:=divFl_le (a:=(fpS+rm)*l1Lo) (b:=2*fpS) (by norm_num [S0,fpS])
  have h2:((dF ((fpS+rm)*l1Lo) (2*fpS):ℤ):R)/S0 <=
    (((fpS+rm:ℤ):R)/S0)*((l1Lo:R)/S0)/2:=by
   calc ((dF ((fpS+rm)*l1Lo) (2*fpS):ℤ):R)/S0
     <= (((fpS+rm:ℤ):R)*(l1Lo:R)/(2*S0))/S0 :=
      dld (by simpa [Int.cast_mul] using hd) hs.le
    _ = (((fpS+rm:ℤ):R)/S0)*((l1Lo:R)/S0)/2:=by field_simp
  rw [neg_div];linarith
 have ht3:-aConst*((rm:R)/S0) <=
   (((if 0<=rm then -mF aLoVal rm else -mF aHiVal rm):ℤ):R)/S0:=by
  split_ifs with hrm0
  .
   have hrmR:(0:R)<=(rm:R)/S0:=div_nonneg (by exact_mod_cast hrm0) hs.le
   have h1:((mF aLoVal rm:ℤ):R)/S0<=aConst*((rm:R)/S0) :=
    (mulFl_le aLoVal rm).trans (mlR ha.1 hrmR)
   simp only [Int.cast_neg,neg_div];linarith
  .
   have hrmR:(rm:R)/S0<=0:=div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (by omega:rm<=0)) hs.le
   have h1:((mF aHiVal rm:ℤ):R)/S0<=aConst*((rm:R)/S0) :=
    (mulFl_le aHiVal rm).trans (mul_le_mul_of_nonpos_right ha.2 hrmR)
   simp only [Int.cast_neg,neg_div];linarith
 have hrm2_lo:((dF (rm*rm) fpS:ℤ):R)/S0<=((rm:R)/S0)^2:=by
  rw [sq];exact mulFl_le rm rm
 have hrm2_hi:((rm:R)/S0)^2<=((dC (rm*rm) fpS:ℤ):R)/S0:=by
  rw [sq];exact le_mulCe rm rm
 have ht4:-bConst*((rm:R)/S0)^3 <=
   -(((mF bInt (if 0<=rm then mF (dF (rm*rm) fpS) rm else mF (dC (rm*rm) fpS) rm):ℤ):R)/S0):=by
  have hb_eq:bConst=(bInt:R)/S0:=by norm_num [bConst,bInt,S0,fpS]
  have hcube:(((if 0<=rm then mF (dF (rm*rm) fpS) rm else mF (dC (rm*rm) fpS) rm:ℤ):R)/S0) <=
    ((rm:R)/S0)^3:=by
   split_ifs with hrm0
   .
    have hrmR:(0:R)<=(rm:R)/S0:=div_nonneg (by exact_mod_cast hrm0) hs.le
    calc ((mF (dF (rm*rm) fpS) rm:ℤ):R)/S0
      <= (((dF (rm*rm) fpS:ℤ):R)/S0)*((rm:R)/S0):=mulFl_le _ _
     _ <= ((rm:R)/S0)^2*((rm:R)/S0):=mlR hrm2_lo hrmR
     _ = ((rm:R)/S0)^3:=by ring
   .
    have hrmR:(rm:R)/S0<=0:=div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (by omega:rm<=0)) hs.le
    calc ((mF (dC (rm*rm) fpS) rm:ℤ):R)/S0
      <= (((dC (rm*rm) fpS:ℤ):R)/S0)*((rm:R)/S0):=mulFl_le _ _
     _ <= ((rm:R)/S0)^2*((rm:R)/S0):=mul_le_mul_of_nonpos_right hrm2_hi hrmR
     _ = ((rm:R)/S0)^3:=by ring
  have hmul:((mF bInt (if 0<=rm then mF (dF (rm*rm) fpS) rm else mF (dC (rm*rm) fpS) rm):ℤ):R)/S0 <=
    bConst*((rm:R)/S0)^3:=by
   rw [hb_eq]
   exact (mulFl_le _ _).trans (mlL hcube (by norm_num [bInt,S0,fpS]))
  linarith
 have ht5:K*((rm:R)/S0) <=
   (((if 0<=rm then mC kHi rm else mC kLo rm):ℤ):R)/S0:=by
  split_ifs with hrm0
  .
   have hrmR:(0:R)<=(rm:R)/S0:=div_nonneg (by exact_mod_cast hrm0) hs.le
   exact (mlR hk_hi hrmR).trans (le_mulCe kHi rm)
  .
   have hrmR:(rm:R)/S0<=0:=div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (by omega:rm<=0)) hs.le
   exact (mul_le_mul_of_nonpos_right hk_lo hrmR).trans (le_mulCe kLo rm)
 set dLo:ℤ:=cLogLo - dC (l1Hi+fpS) 2 - aHiVal - dC (3*bInt*dC (rm*rm) fpS) fpS+kLo
 set dHi:ℤ:=cLogHi - dF (l1Lo+fpS) 2 - aLoVal - dF (3*bInt*dF (rm*rm) fpS) fpS+kHi
 have hd_lo:((dLo:R)/S0) <=
   cLog - (log (1+(rm:R)/S0)+1)/2 - aConst - 3*bConst*((rm:R)/S0)^2+K:=by
  have hlog2:(log (1+(rm:R)/S0)+1)/2<=((dC (l1Hi+fpS) 2:ℤ):R)/S0:=by
   have hd:=le_divCe (a:=l1Hi+fpS) (b:=2) (by norm_num)
   have h1:(((l1Hi:R)+S0)/2)/S0<=((dC (l1Hi+fpS) 2:ℤ):R)/S0 :=
    dld (by simpa [Int.cast_add] using hd) hs.le
   have h2:(((l1Hi:R)+S0)/2)/S0=((l1Hi:R)/S0+1)/2:=by field_simp
   rw [h2] at h1;linarith
  have hb3:3*bConst*((rm:R)/S0)^2 <=
    ((dC (3*bInt*dC (rm*rm) fpS) fpS:ℤ):R)/S0:=by
   have hb_eq:3*bConst=((3*bInt:ℤ):R)/S0:=by norm_num [bConst,bInt,S0,fpS]
   rw [hb_eq]
   exact (mlL hrm2_hi (by norm_num [bInt,S0,fpS])).trans (le_mulCe (3*bInt) (dC (rm*rm) fpS))
  unfold dLo
  simp only [Int.cast_add,Int.cast_sub,add_div,sub_div]
  linarith
 have hd_hi:cLog - (log (1+(rm:R)/S0)+1)/2 - aConst - 3*bConst*((rm:R)/S0)^2+K <=
   ((dHi:R)/S0):=by
  have hlog2:((dF (l1Lo+fpS) 2:ℤ):R)/S0<=(log (1+(rm:R)/S0)+1)/2:=by
   have hd:=divFl_le (a:=l1Lo+fpS) (b:=2) (by norm_num)
   have h1:((dF (l1Lo+fpS) 2:ℤ):R)/S0<=(((l1Lo:R)+S0)/2)/S0 :=
    dld (by simpa [Int.cast_add] using hd) hs.le
   have h2:(((l1Lo:R)+S0)/2)/S0=((l1Lo:R)/S0+1)/2:=by field_simp
   rw [h2] at h1;linarith
  have hb3:((dF (3*bInt*dF (rm*rm) fpS) fpS:ℤ):R)/S0 <=
    3*bConst*((rm:R)/S0)^2:=by
   have hb_eq:3*bConst=((3*bInt:ℤ):R)/S0:=by norm_num [bConst,bInt,S0,fpS]
   rw [hb_eq]
   exact (mulFl_le (3*bInt) (dF (rm*rm) fpS)).trans
    (mlL hrm2_lo (by norm_num [bInt,S0,fpS]))
  unfold dHi
  simp only [Int.cast_add,Int.cast_sub,add_div,sub_div]
  linarith
 set slopeAbs:ℤ:=max (Int.natAbs dLo:ℤ) (Int.natAbs dHi:ℤ)
 have hslope:|cLog - (log (1+(rm:R)/S0)+1)/2 - aConst -
   3*bConst*((rm:R)/S0)^2+K| <= ((slopeAbs:R)/S0):=by
  rw [abs_le]
  have h1:-((slopeAbs:R)/S0)<=(dLo:R)/S0:=by
   have:-slopeAbs<=dLo:=by
    have hle:(Int.natAbs dLo:ℤ)<=slopeAbs:=le_max_left _ _
    have hnat:-(Int.natAbs dLo:ℤ)<=dLo:=by cases Int.natAbs_eq dLo <;> omega
    omega
   rw [← neg_div];exact dld (by exact_mod_cast this) hs.le
  have h2:(dHi:R)/S0<=(slopeAbs:R)/S0:=by
   have:dHi<=slopeAbs:=by
    have hle:(Int.natAbs dHi:ℤ)<=slopeAbs:=le_max_right _ _
    have hnat:dHi<=(Int.natAbs dHi:ℤ):=Int.le_natAbs
    omega
   exact dld (by exact_mod_cast this) hs.le
  exact ⟨h1.trans hd_lo,hd_hi.trans h2⟩
 set half:ℤ:=max (r1 - rm) (rm - r0)
 have hdiff:|ρ - (rm:R)/S0| <= ((half:R)/S0):=by
  rw [abs_le]
  have h1:(r0:R)/S0 - (rm:R)/S0 >= -((half:R)/S0):=by
   have:rm - r0<=half:=le_max_right _ _
   rw [← sub_div,← neg_div]
   exact dld (by exact_mod_cast (by omega:-half<=r0 - rm)) hs.le
  have h2:(r1:R)/S0 - (rm:R)/S0<=((half:R)/S0):=by
   have:r1 - rm<=half:=le_max_left _ _
   rw [← sub_div]
   exact dld (by exact_mod_cast this) hs.le
  exact ⟨by linarith,by linarith⟩
 have hlin_err:(cLog - (log (1+(rm:R)/S0)+1)/2 - aConst -
   3*bConst*((rm:R)/S0)^2+K)*(ρ - (rm:R)/S0) <=
   ((mC slopeAbs half:ℤ):R)/S0:=by
  calc _ <= |cLog - (log (1+(rm:R)/S0)+1)/2 - aConst -
      3*bConst*((rm:R)/S0)^2+K| * |ρ - (rm:R)/S0| := by rw [← abs_mul];exact le_abs_self _
   _ <= ((slopeAbs:R)/S0)*((half:R)/S0) :=
     mul_le_mul hslope hdiff (abs_nonneg _) (le_trans (abs_nonneg _) hslope)
   _ <= ((mC slopeAbs half:ℤ):R)/S0:=le_mulCe slopeAbs half
 have hhc_eq:hH0 r0 r1 cLogLo cLogHi kLo kHi l1Lo l1Hi =
   mC cLogHi (fpS+rm)+(-dF ((fpS+rm)*l1Lo) (2*fpS)) +
   (if 0<=rm then -mF aLoVal rm else -mF aHiVal rm) +
   (-mF bInt (if 0<=rm then mF (dF (rm*rm) fpS) rm else mF (dC (rm*rm) fpS) rm)) +
   (if 0<=rm then mC kHi rm else mC kLo rm)+mC slopeAbs half:=rfl
 have hcast:((hH0 r0 r1 cLogLo cLogHi kLo kHi l1Lo l1Hi:ℤ):R)/S0 =
   ((mC cLogHi (fpS+rm):ℤ):R)/S0 +
   (-((dF ((fpS+rm)*l1Lo) (2*fpS):ℤ):R)/S0) +
   ((if 0<=rm then -mF aLoVal rm else -mF aHiVal rm:ℤ):R)/S0 +
   (-(((mF bInt (if 0<=rm then mF (dF (rm*rm) fpS) rm else mF (dC (rm*rm) fpS) rm):ℤ):R)/S0)) +
   ((if 0<=rm then mC kHi rm else mC kLo rm:ℤ):R)/S0 +
   ((mC slopeAbs half:ℤ):R)/S0:=by
  rw [hhc_eq];push_cast;ring
 rw [hcast]
 linarith only [htan,ht1,ht2,ht3,ht4,ht5,hlin_err]
lemma bivProb_pos {β:R} (c:R) (hβ0:0 < β) (hβ1:β < 1):0 < bP β c:=by
 have hIoi_half:∫ u in Set.Ioi (0:R),pP u=1/2:=by
  have h1:(∫ z in Set.Iic (0:R),pP z)+(∫ z in Set.Ioi (0:R),pP z)=1:=by
   rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
    ipP.integrableOn ipP.integrableOn,
    Set.Iic_union_Ioi,setIntegral_univ,integral_stdPhiPDF_univ]
  rw [integral_stdPhiPDF_Iic_zero] at h1;linarith
 have hlt_half:∫ u in Set.Ioi (0:R),
   pC ((sqrt (1 - β)*u+c)/sqrt β)*pP u < 1/2:=by
  rw [← hIoi_half]
  have hdiff_pos:0 < ∫ u in Set.Ioi (0:R),
    (pP u - pC ((sqrt (1 - β)*u+c)/sqrt β)*pP u):=by
   have hsub:Set.Ioc (0:R) 1 ⊆ Set.Ioi (0:R):=fun u hu=>hu.1
   have hnn:∀ u ∈ Set.Ioi (0:R),
     0<=pP u - pC ((sqrt (1 - β)*u+c)/sqrt β)*pP u:=fun u _=>by
    nlinarith [stdPhiCDF_lt_one ((sqrt (1 - β)*u+c)/sqrt β),pPn u]
   have hsub_pos:0 < ∫ u in Set.Ioc (0:R) 1,
     (pP u - pC ((sqrt (1 - β)*u+c)/sqrt β)*pP u):=by
    rw [← intervalIntegral.integral_of_le (by norm_num:(0:R)<=1)]
    have h1:Continuous pC:=continuous_iff_continuousAt.mpr fun z=>(pCd z).continuousAt
    have h2:Continuous pP:=by unfold pP;fun_prop
    have hc:Continuous (fun u:R =>
      pP u - pC ((sqrt (1 - β)*u+c)/sqrt β)*pP u):=by fun_prop
    refine intervalIntegral.integral_pos (by norm_num) hc.continuousOn
     (fun u _=>by nlinarith [stdPhiCDF_lt_one ((sqrt (1 - β)*u+c)/sqrt β),pPn u])
     ⟨1,⟨by norm_num,le_rfl⟩,by
      nlinarith [stdPhiCDF_lt_one ((sqrt (1 - β)*1+c)/sqrt β),pPp 1]⟩
   have hle_tot:∫ u in Set.Ioc (0:R) 1,
      (pP u - pC ((sqrt (1 - β)*u+c)/sqrt β)*pP u) <=
     ∫ u in Set.Ioi (0:R),
      (pP u - pC ((sqrt (1 - β)*u+c)/sqrt β)*pP u) :=
    setIntegral_mono_set
     (ipP.integrableOn.sub (bivProb_integrand_integrable β c))
     ((ae_restrict_mem measurableSet_Ioi).mono hnn) (LE.le.eventuallyLE hsub)
   exact lt_of_lt_of_le hsub_pos hle_tot
  rw [integral_sub ipP.integrableOn (bivProb_integrand_integrable β c)] at hdiff_pos
  linarith
 unfold bP;linarith
set_option maxHeartbeats 800000 in
lemma cLs {r0 r1 t0 t1 l1Lo l1Hi lPhLo lPhHi lUHi:ℤ} {ρ t:R}
  (hr0_gt:-fpS < r0) (hr01:r0 < r1) (hr1_le:r1<=fpS) (ht01:t0 < t1)
  (hρ0:(r0:R)/S0<=ρ) (hρ1:ρ<=(r1:R)/S0) (hρ_lt:ρ < 1)
  (ht0:(t0:R)/S0<=t) (ht1:t<=(t1:R)/S0)
  (hchk:cLH r0 r1 t0 t1 l1Lo l1Hi lPhLo lPhHi lUHi=true) :
  -t^2/2+((1+ρ)/2)*log (bP ((1+ρ)/2) (gC - t)) -
   ((1+ρ)/2)*log (1+ρ)<=gStar+aConst*ρ+bConst*ρ^3:=by
 have hs:(0:R) < S0:=fpS_pos
 have hgam:gC=(gI:R)/S0:=by norm_num [gC,gI,S0,fpS]
 have hρ_gt:(-1:R) < ρ:=lt_of_lt_of_le (by rw [lt_div_iff₀ hs];norm_num;exact_mod_cast hr0_gt) hρ0
 have hβ0:0 < (1+ρ)/2:=by linarith
 have hβ1:(1+ρ)/2 < 1:=by linarith
 set rm:ℤ:=(r0+r1)/2
 set tm:ℤ:=(t0+t1)/2
 set xm:ℤ:=tm - gI
 set phMLo:ℤ:=cL xm
 set phMHi:ℤ:=cH xm
 set pdfMLo:ℤ:=pL xm
 set pdfMHi:ℤ:=pH xm
 unfold cLH at hchk
 dsimp only at hchk
 by_cases hph500:phMLo < 500
 . rw [if_pos hph500] at hchk;exact absurd hchk (by decide)
 rw [if_neg hph500] at hchk
 by_cases hlogs:¬(oLL (fpS+rm) l1Lo=true/\oLH (fpS+rm) l1Hi=true /\
   oLL phMLo lPhLo=true/\oLH phMHi lPhHi=true)
 .
  have hfalse:(oLL (fpS+rm) l1Lo && oLH (fpS+rm) l1Hi &&
    oLL phMLo lPhLo && oLH phMHi lPhHi)=false:=by
   cases h1:oLL (fpS+rm) l1Lo <;> cases h2:oLH (fpS+rm) l1Hi <;>
    cases h3:oLL phMLo lPhLo <;> cases h4:oLH phMHi lPhHi <;> simp_all
  rw [hfalse] at hchk;simp at hchk
 push Not at hlogs
 obtain ⟨hl1Lo,hl1Hi,hlPhLo,hlPhHi⟩:=hlogs
 have htrue_logs:(oLL (fpS+rm) l1Lo && oLH (fpS+rm) l1Hi &&
   oLL phMLo lPhLo && oLH phMHi lPhHi)=true:=by simp [hl1Lo,hl1Hi,hlPhLo,hlPhHi]
 rw [htrue_logs] at hchk
 simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte] at hchk
 have hxm_eq:(tm:R)/S0 - gC=(xm:R)/S0:=by
  unfold xm;rw [hgam,Int.cast_sub,sub_div]
 have hphM_lo:((phMLo:R)/S0)<=pC ((xm:R)/S0):=phiCDFLo_le xm
 have hphM_hi:pC ((xm:R)/S0)<=((phMHi:R)/S0):=le_phiCDFHi xm
 have hpdfM_lo:((pdfMLo:R)/S0)<=pP ((xm:R)/S0):=phiPDFLo_le xm
 have hpdfM_hi:pP ((xm:R)/S0)<=((pdfMHi:R)/S0):=le_phiPDFHi xm
 have hphMLo_pos:0 < phMLo:=by omega
 have hphMHi_pos:0 < phMHi:=by
  have:((phMLo:R)/S0)<=((phMHi:R)/S0):=hphM_lo.trans hphM_hi
  have:(phMLo:R)<=(phMHi:R):=(div_le_div_iff_of_pos_right hs).mp this
  have:phMLo<=phMHi:=by exact_mod_cast this
  omega
 set rmLo:ℤ:=dF (pdfMLo*fpS) phMHi
 set rmHi:ℤ:=dC (pdfMHi*fpS) phMLo
 have hrm_lo:((rmLo:R)/S0)<=mR ((xm:R)/S0):=by
  have hd:=divFl_le (a:=pdfMLo*fpS) (b:=phMHi) hphMHi_pos
  have h1:((rmLo:R)/S0)<=(((pdfMLo:R)/S0)/((phMHi:R)/S0)):=by
   have hne:(phMHi:R) ≠ 0:=by exact_mod_cast hphMHi_pos.ne'
   calc ((rmLo:R)/S0)<=((pdfMLo:R)*S0/(phMHi:R))/S0 :=
      dld (by simpa [rmLo,Int.cast_mul] using hd) hs.le
    _ = ((pdfMLo:R)/S0)/((phMHi:R)/S0):=by field_simp
  refine h1.trans ?_
  unfold mR
  by_cases hneg:((pdfMLo:R)/S0)<=0
  .
   exact le_trans (div_nonpos_of_nonpos_of_nonneg hneg (div_nonneg (by exact_mod_cast hphMHi_pos.le) hs.le))
    (div_nonneg (pPn _) (pCp _).le)
  . exact div_le_div₀ (pPn _) hpdfM_lo (pCp _) hphM_hi
 have hrm_hi:mR ((xm:R)/S0)<=((rmHi:R)/S0):=by
  have hd:=le_divCe (a:=pdfMHi*fpS) (b:=phMLo) hphMLo_pos
  have h1:(((pdfMHi:R)/S0)/((phMLo:R)/S0))<=((rmHi:R)/S0):=by
   have hne:(phMLo:R) ≠ 0:=by exact_mod_cast hphMLo_pos.ne'
   calc ((pdfMHi:R)/S0)/((phMLo:R)/S0)
     = ((pdfMHi:R)*S0/(phMLo:R))/S0:=by field_simp
    _ <= ((rmHi:R)/S0) :=
      dld (by simpa [rmHi,Int.cast_mul] using hd) hs.le
  refine le_trans ?_ h1
  unfold mR
  exact div_le_div₀ (le_trans (pPn _) hpdfM_hi) hpdfM_hi
   (div_pos (by exact_mod_cast hphMLo_pos) hs) hphM_lo
 have hlPh_lo:((lPhLo:R)/S0)<=log (pC ((xm:R)/S0)) :=
  (oLLs hlPhLo).2.trans (log_le_log (div_pos (by exact_mod_cast hphMLo_pos) hs) hphM_lo)
 have hlPh_hi:log (pC ((xm:R)/S0))<=((lPhHi:R)/S0) :=
  (log_le_log (pCp _) hphM_hi).trans (oLHs hlPhHi).2
 set b0:ℤ:=dF (fpS+r0) 2
 set b1:ℤ:=dC (fpS+r1) 2
 have hb0_le:((b0:R)/S0)<=(1+ρ)/2:=by
  have hd:=divFl_le (a:=fpS+r0) (b:=2) (by norm_num)
  have h1:((b0:R)/S0)<=(1+(r0:R)/S0)/2:=by
   calc ((b0:R)/S0)<=((S0+(r0:R))/2)/S0 :=
      dld (by simpa [b0,Int.cast_add] using hd) hs.le
    _ = (1+(r0:R)/S0)/2:=by field_simp
  linarith
 have hb0_nn:0<=b0:=Int.ediv_nonneg (by omega) (by norm_num)
 have hb1_ge:(1+ρ)/2<=((b1:R)/S0):=by
  have hd:=le_divCe (a:=fpS+r1) (b:=2) (by norm_num)
  have h1:(1+(r1:R)/S0)/2<=((b1:R)/S0):=by
   calc (1+(r1:R)/S0)/2=((S0+(r1:R))/2)/S0:=by field_simp
    _ <= ((b1:R)/S0) :=
      dld (by simpa [b1,Int.cast_add] using hd) hs.le
  linarith
 have hlog_tan:log (pC (t - gC)) <=
   log (pC ((xm:R)/S0)) +
    mR ((xm:R)/S0)*(t - (tm:R)/S0):=by
  have h:=log_stdPhiCDF_le_tangent ((xm:R)/S0) (t - gC)
  rwa [show t - gC - (xm:R)/S0=t - (tm:R)/S0 by linarith [hxm_eq]] at h
 have hgLo:=gStar_ge_gLoVal
 have hbiv_pos:0 < bP ((1+ρ)/2) (gC - t):=bivProb_pos (gC - t) hβ0 hβ1
 by_cases hb2:mQH (mF b0 rmLo) (mC b1 rmHi) t0 t1 tm +
   hH0 r0 r1 (dF lPhLo 2) (dC lPhHi 2) 0 0 l1Lo l1Hi - gLoVal < 0
 .
  clear hchk
  have hprob_le:log (bP ((1+ρ)/2) (gC - t))<=log (pC (t - gC)):=by
   have hle:=bivProb_le_cdf (gC - t) hβ0 hβ1
   rw [neg_sub] at hle
   exact log_le_log hbiv_pos hle
  have hba_lo:((mF b0 rmLo:ℤ):R)/S0<=((1+ρ)/2)*mR ((xm:R)/S0):=by
   refine (mulFl_le b0 rmLo).trans ?_
   by_cases hneg:((rmLo:R)/S0)<=0
   .
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by exact_mod_cast hb0_nn) hs.le) hneg)
     (mul_nonneg hβ0.le (millsRatio_pos _).le)
   . exact mul_le_mul hb0_le hrm_lo (le_of_not_ge hneg) hβ0.le
  have hba_hi:((1+ρ)/2)*mR ((xm:R)/S0)<=((mC b1 rmHi:ℤ):R)/S0 :=
   (mul_le_mul hb1_ge hrm_hi (millsRatio_pos _).le (le_trans hβ0.le hb1_ge)).trans (le_mulCe b1 rmHi)
  have hq2:=maxQuadHi_sound (tm:=tm) hba_lo hba_hi ht0 ht1
  have hcl_lo:((dF lPhLo 2:ℤ):R)/S0<=log (pC ((xm:R)/S0))/2:=by
   have hd:=divFl_le (a:=lPhLo) (b:=2) (by norm_num)
   calc ((dF lPhLo 2:ℤ):R)/S0<=((lPhLo:R)/2)/S0 :=
      dld hd hs.le
    _ = ((lPhLo:R)/S0)/2:=by ring
    _ <= log (pC ((xm:R)/S0))/2:=by linarith
  have hcl_hi:log (pC ((xm:R)/S0))/2<=((dC lPhHi 2:ℤ):R)/S0:=by
   have hd:=le_divCe (a:=lPhHi) (b:=2) (by norm_num)
   calc log (pC ((xm:R)/S0))/2<=((lPhHi:R)/S0)/2:=by linarith
    _ = ((lPhHi:R)/2)/S0:=by ring
    _ <= ((dC lPhHi 2:ℤ):R)/S0:=dld hd hs.le
  have hh2:=hHs hr0_gt hr01 hr1_le hρ0 hρ1 hρ_lt hcl_lo hcl_hi
   (by simp:((0:ℤ):R)/S0<=0) (by simp:(0:R)<=((0:ℤ):R)/S0) hl1Lo hl1Hi
  have hneg_val:((mQH (mF b0 rmLo) (mC b1 rmHi) t0 t1 tm +
    hH0 r0 r1 (dF lPhLo 2) (dC lPhHi 2) 0 0 l1Lo l1Hi - gLoVal:ℤ):R)/S0 < 0 :=
   div_neg_of_neg_of_pos (by exact_mod_cast hb2) hs
  simp only [Int.cast_sub,Int.cast_add,sub_div,add_div] at hneg_val
  have hstep1:((1+ρ)/2)*log (bP ((1+ρ)/2) (gC - t)) <=
    ((1+ρ)/2)*log (pC ((xm:R)/S0)) +
     ((1+ρ)/2)*mR ((xm:R)/S0)*(t - (tm:R)/S0):=by
   nlinarith only [hβ0,hprob_le,hlog_tan]
  have halg:((1+ρ)/2)*log (pC ((xm:R)/S0)) =
    (log (pC ((xm:R)/S0))/2)*(1+ρ):=by ring
  simp only [zero_mul,add_zero] at hh2
  linarith only [hstep1,halg,hq2,hh2,hgLo,hneg_val]
 rw [if_neg hb2] at hchk
 revert hchk
 set c0:ℤ:=gI - t1
 set c1:ℤ:=gI - t0
 set cSqLo:ℤ:=if c0<=0/\0<=c1 then 0 else min (dF (c0*c0) fpS) (dF (c1*c1) fpS)
 set cSqHi:ℤ:=max (dC (c0*c0) fpS) (dC (c1*c1) fpS)
 have hc_lo:(c0:R)/S0<=gC - t:=by
  unfold c0;rw [hgam,Int.cast_sub,sub_div];linarith
 have hc_hi:gC - t<=(c1:R)/S0:=by
  unfold c1;rw [hgam,Int.cast_sub,sub_div];linarith
 have hcSqLo_le:((cSqLo:R)/S0)<=(gC - t)^2:=by
  unfold cSqLo
  split_ifs with h0
  . simp [sq_nonneg]
  .
   have hcase:0 < c0\/c1 < 0:=by omega
   rcases hcase with hc0p | hc1n
   .
    have h1:((c0:R)/S0)^2<=(gC - t)^2:=by
     have:(0:R)<=(c0:R)/S0:=div_nonneg (by exact_mod_cast hc0p.le) hs.le
     nlinarith only [hc_lo,this]
    have h2:((min (dF (c0*c0) fpS) (dF (c1*c1) fpS):ℤ):R)/S0 <=
      ((dF (c0*c0) fpS:ℤ):R)/S0 :=
     dld (by exact_mod_cast min_le_left _ _) hs.le
    exact (h2.trans (by rw [pow_two];exact mulFl_le c0 c0)).trans h1
   .
    have h1:((c1:R)/S0)^2<=(gC - t)^2:=by
     have:(c1:R)/S0<=0:=div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hc1n.le) hs.le
     nlinarith only [hc_hi,this]
    have h2:((min (dF (c0*c0) fpS) (dF (c1*c1) fpS):ℤ):R)/S0 <=
      ((dF (c1*c1) fpS:ℤ):R)/S0 :=
     dld (by exact_mod_cast min_le_right _ _) hs.le
    exact (h2.trans (by rw [pow_two];exact mulFl_le c1 c1)).trans h1
 have hcSqLo_nn:0<=cSqLo:=by
  unfold cSqLo
  split_ifs
  . exact le_rfl
  .
   exact le_min (Int.ediv_nonneg (mul_self_nonneg c0) (by norm_num [S0,fpS]))
    (Int.ediv_nonneg (mul_self_nonneg c1) (by norm_num [S0,fpS]))
 have hcSqHi_ge:(gC - t)^2<=((cSqHi:R)/S0):=by
  have h1:(gC - t)^2<=max (((c0:R)/S0)^2) (((c1:R)/S0)^2):=by
   by_cases hsign:0<=gC - t
   . exact le_trans (by nlinarith only [hsign,hc_hi]) (le_max_right _ _)
   . exact le_trans (by nlinarith only [hsign,hc_lo]) (le_max_left _ _)
  have hc0_sq:((c0:R)/S0)^2<=((dC (c0*c0) fpS:ℤ):R)/S0:=by
   rw [pow_two];exact le_mulCe c0 c0
  have hc1_sq:((c1:R)/S0)^2<=((dC (c1*c1) fpS:ℤ):R)/S0:=by
   rw [pow_two];exact le_mulCe c1 c1
  refine h1.trans (max_le ?_ ?_)
  .
   exact hc0_sq.trans
    (dld (by exact_mod_cast le_max_left (dC (c0*c0) fpS) (dC (c1*c1) fpS)) hs.le)
  .
   exact hc1_sq.trans
    (dld (by exact_mod_cast le_max_right (dC (c0*c0) fpS) (dC (c1*c1) fpS)) hs.le)
 have hcSqHi_nn:0<=cSqHi:=by
  have:(0:R)<=((cSqHi:R)/S0):=le_trans (sq_nonneg _) hcSqHi_ge
  have:(0:R)<=(cSqHi:R):=(div_nonneg_iff.mp this).elim (fun h=>h.1) (fun h=>by linarith only [h.2,hs])
  exact_mod_cast this
 set phLo:ℤ:=cL (t0 - gI)
 set phHi:ℤ:=cH (t1 - gI)
 have hph_lo:((phLo:R)/S0)<=pC (t - gC) :=
  (phiCDFLo_le (t0 - gI)).trans (pCm.monotone (by rw [hgam,Int.cast_sub,sub_div];linarith only [ht0]))
 have hph_hi:pC (t - gC)<=((phHi:R)/S0) :=
  (pCm.monotone (by rw [hgam,Int.cast_sub,sub_div];linarith only [ht1])).trans (le_phiCDFHi (t1 - gI))
 have h1r0_le:((fpS+r0:ℤ):R)/S0<=1+ρ:=by
  rw [Int.cast_add,add_div,div_self hs.ne'];linarith only [hρ0]
 have h1r1_ge:1+ρ<=((fpS+r1:ℤ):R)/S0:=by
  rw [Int.cast_add,add_div,div_self hs.ne'];linarith only [hρ1]
 have h2ba_lo:((mF (fpS+r0) rmLo:ℤ):R)/S0<=(1+ρ)*mR ((xm:R)/S0):=by
  refine (mulFl_le (fpS+r0) rmLo).trans ?_
  by_cases hneg:((rmLo:R)/S0)<=0
  .
   exact le_trans (mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by exact_mod_cast (by omega:0<=fpS+r0)) hs.le) hneg)
    (mul_nonneg (by linarith only [hρ_gt]) (millsRatio_pos _).le)
  . exact mul_le_mul h1r0_le hrm_lo (le_of_not_ge hneg) (by linarith only [hρ_gt])
 have h2ba_hi:(1+ρ)*mR ((xm:R)/S0)<=((mC (fpS+r1) rmHi:ℤ):R)/S0 :=
  (mul_le_mul h1r1_ge hrm_hi (millsRatio_pos _).le (by linarith only [hρ_gt,h1r1_ge])).trans (le_mulCe (fpS+r1) rmHi)
 have hq1:=maxQuadHi_sound (tm:=tm) h2ba_lo h2ba_hi ht0 ht1
 have hpub1:=bPu (gC - t) hρ_gt hρ_lt
 intro hchk
 by_cases hr0_nn:0<=r0
 .
  rw [if_pos hr0_nn] at hchk
  have hρ_nn:0<=ρ:=le_trans (div_nonneg (by exact_mod_cast hr0_nn) hs.le) hρ0
  let phLoSq:ℤ:=mF phLo phLo
  let eArg:ℤ:=-dF (cSqLo*fpS) (fpS+r1)
  let eHi:ℤ:=eH eArg
  let mHi:ℤ:=dC (mC iP1 eHi*fpS) phLoSq
  let r1CubeHi:ℤ:=mC (mC r1 r1) r1
  let shiftHi:ℤ:=dC (6*r1CubeHi) 10
  let uM:ℤ:=mC (rm+shiftHi) mHi
  let diffHi:ℤ:=mC shiftHi mHi - uM
  let cTerm:ℤ:=mC b1 lUHi+dC (mC b1 diffHi*fpS) (fpS+uM)
  have hchk':(if phLo<=0 then false else if phLoSq<=0 then false else
    if (!oLH (fpS+uM) lUHi)=true then false else
    decide (mQH (mF (fpS+r0) rmLo) (mC (fpS+r1) rmHi) t0 t1 tm +
     hH0 r0 r1 lPhLo lPhHi (dF (mF b1 mHi*fpS) (fpS+uM))
      (dC (mC b1 mHi*fpS) (fpS+uM)) l1Lo l1Hi+cTerm - gLoVal < 0))=true:=hchk
  clear hchk
  by_cases hphLo0:phLo<=0
  . rw [if_pos hphLo0] at hchk';exact absurd hchk' (by decide)
  rw [if_neg hphLo0] at hchk'
  by_cases hpsq:phLoSq<=0
  . rw [if_pos hpsq] at hchk';exact absurd hchk' (by decide)
  rw [if_neg hpsq] at hchk'
  have hphLo_pos:0 < phLo:=by omega
  have hpsq_pos:0 < phLoSq:=by omega
  have hphLoSq_le:((phLoSq:R)/S0)<=(pC (t - gC))^2:=by
   have h1:=mulFl_le phLo phLo
   have h2:(((phLo:R)/S0)*((phLo:R)/S0))<=(pC (t - gC))^2:=by
    rw [pow_two];exact mul_self_le_mul_self (div_nonneg (by exact_mod_cast hphLo_pos.le) hs.le) hph_lo
   exact h1.trans h2
  by_cases hokU:(!oLH (fpS+uM) lUHi)=true
  . rw [if_pos hokU] at hchk';exact absurd hchk' (by decide)
  rw [if_neg hokU] at hchk'
  have hneg_int:mQH (mF (fpS+r0) rmLo) (mC (fpS+r1) rmHi) t0 t1 tm +
    hH0 r0 r1 lPhLo lPhHi (dF (mF b1 mHi*fpS) (fpS+uM))
     (dC (mC b1 mHi*fpS) (fpS+uM)) l1Lo l1Hi+cTerm - gLoVal < 0 :=
   of_decide_eq_true hchk'
  clear hchk'
  have hokU':oLH (fpS+uM) lUHi=true:=by
   cases h:oLH (fpS+uM) lUHi <;> simp_all
  have huM_log:=oLHs hokU'
  have h1uM_pos:(0:R) < 1+(uM:R)/S0:=by
   have:(0:R) < ((fpS+uM:ℤ):R)/S0:=div_pos (by exact_mod_cast huM_log.1) hs
   rwa [Int.cast_add,add_div,div_self hs.ne'] at this
  have heArg_nonpos:eArg<=0:=by
   have:0<=dF (cSqLo*fpS) (fpS+r1):=Int.ediv_nonneg (mul_nonneg hcSqLo_nn (by norm_num [S0,fpS])) (by omega)
   omega
  have hexp_le:exp (-(gC - t)^2/(1+ρ))<=((eHi:R)/S0):=by
   have harg_le:-(gC - t)^2/(1+ρ)<=(eArg:R)/S0:=by
    have hd:=divFl_le (a:=cSqLo*fpS) (b:=fpS+r1) (by omega)
    have h1:((dF (cSqLo*fpS) (fpS+r1):ℤ):R)/S0 <=
      ((cSqLo:R)/S0)/(((fpS+r1:ℤ):R)/S0):=by
     have hne:((fpS+r1:ℤ):R) ≠ 0:=by exact_mod_cast (by omega:fpS+r1 ≠ 0)
     calc ((dF (cSqLo*fpS) (fpS+r1):ℤ):R)/S0
       <= ((cSqLo:R)*S0/((fpS+r1:ℤ):R))/S0 :=
        dld (by simpa [Int.cast_mul] using hd) hs.le
      _ = ((cSqLo:R)/S0)/(((fpS+r1:ℤ):R)/S0):=by field_simp
    have h2:((cSqLo:R)/S0)/(((fpS+r1:ℤ):R)/S0) <=
      (gC - t)^2/(1+ρ) :=
     div_le_div₀ (sq_nonneg _) hcSqLo_le (by linarith) h1r1_ge
    have h3:(eArg:R)/S0 = -((dF (cSqLo*fpS) (fpS+r1):ℤ):R)/S0:=by
     unfold eArg;simp [neg_div]
    rw [h3,neg_div,neg_div];linarith
   exact (exp_le_exp.mpr harg_le).trans (le_expNegHi heArg_nonpos)
  have hM_le:exp (-(gC - t)^2/(1+ρ))/(2*PI*(pC (t - gC))^2) <=
    ((mHi:R)/S0):=by
   have hnum:(2*PI)⁻¹*exp (-(gC - t)^2/(1+ρ)) <=
     ((mC iP1 eHi:ℤ):R)/S0 :=
    (mul_le_mul pi_bounds_inv2Pi.2 hexp_le (exp_nonneg _) (by norm_num [iP1,S0,fpS])).trans
     (le_mulCe iP1 eHi)
   have hdiv1:((2*PI)⁻¹*exp (-(gC - t)^2/(1+ρ)))/(pC (t - gC))^2 <=
     (((mC iP1 eHi:ℤ):R)/S0)/((phLoSq:R)/S0) :=
    div_le_div₀ (le_trans (by positivity) hnum) hnum (div_pos (by exact_mod_cast hpsq_pos) hs) hphLoSq_le
   have hdiv2:(((mC iP1 eHi:ℤ):R)/S0)/((phLoSq:R)/S0) <=
     ((mHi:R)/S0):=by
    have hd:=le_divCe (a:=mC iP1 eHi*fpS) (b:=phLoSq) hpsq_pos
    have hne:(phLoSq:R) ≠ 0:=by exact_mod_cast hpsq_pos.ne'
    calc (((mC iP1 eHi:ℤ):R)/S0)/((phLoSq:R)/S0)
      = (((mC iP1 eHi:ℤ):R)*S0/(phLoSq:R))/S0:=by field_simp
     _ <= ((mHi:R)/S0):=dld (by simpa [mHi,Int.cast_mul] using hd) hs.le
   refine le_trans (le_of_eq (by ring)) (hdiv1.trans hdiv2)
  have hM_nn:(0:R)<=(mHi:R)/S0:=le_trans (by positivity) hM_le
  have hshift_ge:(3/5:R)*ρ^3<=((shiftHi:R)/S0):=by
   have hr1_nn:(0:R)<=(r1:R)/S0:=div_nonneg (by exact_mod_cast (by omega:0<=r1)) hs.le
   have hcube:ρ^3<=((r1CubeHi:R)/S0):=by
    have h1:ρ^3<=((r1:R)/S0)^3:=pow_le_pow_left₀ hρ_nn hρ1 3
    have h2:((r1:R)/S0)^2<=((mC r1 r1:ℤ):R)/S0:=by rw [sq];exact le_mulCe r1 r1
    have h3:((r1:R)/S0)^3<=((r1CubeHi:R)/S0):=by
     calc ((r1:R)/S0)^3=((r1:R)/S0)^2*((r1:R)/S0):=by ring
      _ <= (((mC r1 r1:ℤ):R)/S0)*((r1:R)/S0):=mlR h2 hr1_nn
      _ <= ((r1CubeHi:R)/S0):=le_mulCe (mC r1 r1) r1
    exact h1.trans h3
   have hd:=le_divCe (a:=6*r1CubeHi) (b:=10) (by norm_num)
   calc (3/5:R)*ρ^3<=(3/5:R)*((r1CubeHi:R)/S0):=by linarith
    _ = ((6*(r1CubeHi:R))/10)/S0:=by ring
    _ <= ((shiftHi:R)/S0):=dld (by simpa [shiftHi,Int.cast_mul] using hd) hs.le
  let δ:R:=((ρ+(3/5:R)*ρ^3)/(2*PI*(pC (t - gC))^2)) *
    exp (-(gC - t)^2/(1+ρ))
  have hδ_nn:0<=δ:=by positivity
  have hδ_le:δ<=(ρ+(shiftHi:R)/S0)*((mHi:R)/S0):=by
   have h1:δ=(ρ+(3/5:R)*ρ^3)*(exp (-(gC - t)^2/(1+ρ))/(2*PI*(pC (t - gC))^2)):=by
    unfold δ;ring
   have h35_nn:(0:R)<=(3/5:R)*ρ^3:=by positivity
   rw [h1]
   exact mul_le_mul (by linarith only [hshift_ge]) hM_le (by positivity) (by linarith only [hρ_nn,hshift_ge,h35_nn])
  have hbiv_fact:bP ((1+ρ)/2) (gC - t)<=(pC (t - gC))^2*(1+δ):=by
   unfold bivPub1 at hpub1
   rw [if_pos hρ_nn,neg_sub] at hpub1
   refine hpub1.trans_eq ?_
   unfold δ
   have hne:pC (t - gC) ≠ 0:=(pCp _).ne'
   field_simp [hne]
  have hlog_biv:log (bP ((1+ρ)/2) (gC - t)) <=
    2*log (pC (t - gC))+log (1+δ):=by
   have h1:=log_le_log hbiv_pos hbiv_fact
   rw [log_mul (sq_pos_of_pos (pCp _)).ne' (by linarith),log_pow] at h1
   simpa using h1
  have hlog_conc:log (1+δ)<=log (1+(uM:R)/S0) +
    (δ - (uM:R)/S0)/(1+(uM:R)/S0):=by
   have h:=log_le_sub_one_of_pos (div_pos (by linarith:0 < 1+δ) h1uM_pos)
   rw [log_div (by linarith) h1uM_pos.ne'] at h
   have heq:(1+δ)/(1+(uM:R)/S0) - 1 =
     (δ - (uM:R)/S0)/(1+(uM:R)/S0):=by
    rw [div_sub_one h1uM_pos.ne'];congr 1;ring
   linarith
  have hlog_uM_hi:log (1+(uM:R)/S0)<=((lUHi:R)/S0):=by
   have h:=huM_log.2
   rwa [Int.cast_add,add_div,div_self hs.ne'] at h
  have hβ_logδ:((1+ρ)/2)*log (1+δ) <=
    ((b1:R)/S0)*log (1+δ) :=
   mlR hb1_ge (log_nonneg (by linarith))
  set K:R:=(((b1:R)/S0)*((mHi:R)/S0))/(1+(uM:R)/S0)
  have hb1_nn:(0:R)<=(b1:R)/S0:=le_trans hβ0.le hb1_ge
  have hK_lo:((dF (mF b1 mHi*fpS) (fpS+uM):ℤ):R)/S0<=K:=by
   have hd:=divFl_le (a:=mF b1 mHi*fpS) (b:=fpS+uM) huM_log.1
   have h1:((dF (mF b1 mHi*fpS) (fpS+uM):ℤ):R)/S0 <=
     (((mF b1 mHi:ℤ):R)/S0)/(1+(uM:R)/S0):=by
    have hne:((fpS+uM:ℤ):R) ≠ 0:=by exact_mod_cast huM_log.1.ne'
    have h1u:(1:R)+(uM:R)/S0=((fpS+uM:ℤ):R)/S0:=by
     rw [Int.cast_add,add_div,div_self hs.ne']
    rw [h1u]
    calc ((dF (mF b1 mHi*fpS) (fpS+uM):ℤ):R)/S0
      <= (((mF b1 mHi:ℤ):R)*S0/((fpS+uM:ℤ):R))/S0 :=
       dld (by simpa [Int.cast_mul] using hd) hs.le
     _ = (((mF b1 mHi:ℤ):R)/S0)/(((fpS+uM:ℤ):R)/S0):=by field_simp
   exact h1.trans (dld (mulFl_le b1 mHi) h1uM_pos.le)
  have hK_hi:K<=((dC (mC b1 mHi*fpS) (fpS+uM):ℤ):R)/S0:=by
   have hd:=le_divCe (a:=mC b1 mHi*fpS) (b:=fpS+uM) huM_log.1
   have h1:K<=(((mC b1 mHi:ℤ):R)/S0)/(1+(uM:R)/S0) :=
    dld (le_mulCe b1 mHi) h1uM_pos.le
   refine h1.trans ?_
   have hne:((fpS+uM:ℤ):R) ≠ 0:=by exact_mod_cast huM_log.1.ne'
   have h1u:(1:R)+(uM:R)/S0=((fpS+uM:ℤ):R)/S0:=by
    rw [Int.cast_add,add_div,div_self hs.ne']
   rw [h1u]
   calc (((mC b1 mHi:ℤ):R)/S0)/(((fpS+uM:ℤ):R)/S0)
     = (((mC b1 mHi:ℤ):R)*S0/((fpS+uM:ℤ):R))/S0:=by field_simp
    _ <= ((dC (mC b1 mHi*fpS) (fpS+uM):ℤ):R)/S0 :=
      dld (by simpa [Int.cast_mul] using hd) hs.le
  have hcTerm_ge:((b1:R)/S0)*log (1+(uM:R)/S0) +
    ((b1:R)/S0)*(((shiftHi:R)/S0)*((mHi:R)/S0) - (uM:R)/S0) /
    (1+(uM:R)/S0)<=((cTerm:R)/S0):=by
   have h1:((b1:R)/S0)*log (1+(uM:R)/S0)<=((mC b1 lUHi:ℤ):R)/S0 :=
    (mlL hlog_uM_hi hb1_nn).trans (le_mulCe b1 lUHi)
   have h2:((shiftHi:R)/S0)*((mHi:R)/S0) - (uM:R)/S0 <=
     ((diffHi:R)/S0):=by
    unfold diffHi;rw [Int.cast_sub,sub_div];linarith [le_mulCe shiftHi mHi]
   have h3:((b1:R)/S0)*(((shiftHi:R)/S0)*((mHi:R)/S0) - (uM:R)/S0) <=
     ((mC b1 diffHi:ℤ):R)/S0 :=
    (mlL h2 hb1_nn).trans (le_mulCe b1 diffHi)
   have h4:(((mC b1 diffHi:ℤ):R)/S0)/(1+(uM:R)/S0) <=
     ((dC (mC b1 diffHi*fpS) (fpS+uM):ℤ):R)/S0:=by
    have hd:=le_divCe (a:=mC b1 diffHi*fpS) (b:=fpS+uM) huM_log.1
    have hne:((fpS+uM:ℤ):R) ≠ 0:=by exact_mod_cast huM_log.1.ne'
    have h1u:(1:R)+(uM:R)/S0=((fpS+uM:ℤ):R)/S0:=by
     rw [Int.cast_add,add_div,div_self hs.ne']
    rw [h1u]
    calc (((mC b1 diffHi:ℤ):R)/S0)/(((fpS+uM:ℤ):R)/S0)
      = (((mC b1 diffHi:ℤ):R)*S0/((fpS+uM:ℤ):R))/S0:=by field_simp
     _ <= ((dC (mC b1 diffHi*fpS) (fpS+uM):ℤ):R)/S0 :=
       dld (by simpa [Int.cast_mul] using hd) hs.le
   have h34:((b1:R)/S0)*(((shiftHi:R)/S0)*((mHi:R)/S0) - (uM:R)/S0) /
     (1+(uM:R)/S0)<=((dC (mC b1 diffHi*fpS) (fpS+uM):ℤ):R)/S0 :=
    (dld h3 h1uM_pos.le).trans h4
   unfold cTerm;rw [Int.cast_add,add_div];linarith
  have hδ_split:((b1:R)/S0)*log (1+δ)<=K*ρ+((cTerm:R)/S0):=by
   have hnum:δ - (uM:R)/S0 <=
     (ρ+(shiftHi:R)/S0)*((mHi:R)/S0) - (uM:R)/S0:=by
    linarith only [hδ_le]
   have h1:((b1:R)/S0)*log (1+δ) <=
     ((b1:R)/S0)*(log (1+(uM:R)/S0) +
      ((ρ+(shiftHi:R)/S0)*((mHi:R)/S0) - (uM:R)/S0) /
      (1+(uM:R)/S0)) :=
    mlL (hlog_conc.trans (add_le_add le_rfl (dld hnum h1uM_pos.le))) hb1_nn
   have halg:((b1:R)/S0)*(log (1+(uM:R)/S0) +
      ((ρ+(shiftHi:R)/S0)*((mHi:R)/S0) - (uM:R)/S0) /
      (1+(uM:R)/S0)) =
     K*ρ+(((b1:R)/S0)*log (1+(uM:R)/S0) +
      ((b1:R)/S0)*(((shiftHi:R)/S0)*((mHi:R)/S0) - (uM:R)/S0) /
      (1+(uM:R)/S0)):=by
    unfold K;ring
   linarith only [h1,halg,hcTerm_ge]
  have hhc:=hHs hr0_gt hr01 hr1_le hρ0 hρ1 hρ_lt hlPh_lo hlPh_hi hK_lo hK_hi hl1Lo hl1Hi
  have hneg_r:((mQH (mF (fpS+r0) rmLo) (mC (fpS+r1) rmHi) t0 t1 tm +
    hH0 r0 r1 lPhLo lPhHi (dF (mF b1 mHi*fpS) (fpS+uM))
     (dC (mC b1 mHi*fpS) (fpS+uM)) l1Lo l1Hi+cTerm - gLoVal:ℤ):R)/S0 < 0 :=
   div_neg_of_neg_of_pos (by exact_mod_cast hneg_int) hs
  simp only [Int.cast_sub,Int.cast_add,sub_div,add_div] at hneg_r
  have hlog_step:((1+ρ)/2)*(2*log (pC (t - gC))) <=
    log (pC ((xm:R)/S0))*(1+ρ) +
     (1+ρ)*mR ((xm:R)/S0)*(t - (tm:R)/S0):=by
   have:((1+ρ)/2)*(2*log (pC (t - gC)))=(1+ρ)*log (pC (t - gC)):=by ring
   rw [this]
   nlinarith only [hρ_gt,hlog_tan]
  nlinarith only [hβ0,hlog_biv,hβ_logδ,hδ_split,hlog_step,hq1,hhc,hgLo,hneg_r]
 rw [if_neg hr0_nn] at hchk
 by_cases hr1_np:r1<=0
 .
  rw [if_pos hr1_np] at hchk
  have hρ_np:ρ<=0:=le_trans hρ1 (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hr1_np) hs.le)
  let phHiSq:ℤ:=mC phHi phHi
  let eArg:ℤ:=-dC (cSqHi*fpS) (fpS+r0)
  let eLo:ℤ:=eL eArg
  let mLo:ℤ:=dF (mF iP0 eLo*fpS) phHiSq
  let uM:ℤ:=mC rm mLo
  let dHi:ℤ:=mC r1 mLo
  let cTerm:ℤ:=mC b0 lUHi+dC (mC b0 (-uM)*fpS) (fpS+uM)
  have hchk':(if phHiSq<=0 then false else
    if fpS+uM<=500000 then
     if fpS+dHi<=500 then false
     else if (!oLH (fpS+dHi) lUHi)=true then false
     else decide (mQH (mF (fpS+r0) rmLo) (mC (fpS+r1) rmHi) t0 t1 tm +
      hH0 r0 r1 lPhLo lPhHi 0 0 l1Lo l1Hi+mC b0 lUHi - gLoVal < 0)
    else if (!oLH (fpS+uM) lUHi)=true then false
    else decide (mQH (mF (fpS+r0) rmLo) (mC (fpS+r1) rmHi) t0 t1 tm +
     hH0 r0 r1 lPhLo lPhHi (dF (mF b0 mLo*fpS) (fpS+uM))
      (dC (mC b0 mLo*fpS) (fpS+uM)) l1Lo l1Hi+cTerm - gLoVal < 0))=true:=hchk
  clear hchk
  by_cases hpsq:phHiSq<=0
  . rw [if_pos hpsq] at hchk';exact absurd hchk' (by decide)
  rw [if_neg hpsq] at hchk'
  have hpsq_pos:0 < phHiSq:=by omega
  have hphHiSq_ge:(pC (t - gC))^2<=((phHiSq:R)/S0):=by
   calc (pC (t - gC))^2=pC (t - gC)*pC (t - gC):=pow_two _
    _ <= ((phHi:R)/S0)*((phHi:R)/S0):=mul_self_le_mul_self (pCp _).le hph_hi
    _ <= ((phHiSq:R)/S0):=le_mulCe phHi phHi
  have heArg_nonpos:eArg<=0:=by
   have h0:(0:R)<=((dC (cSqHi*fpS) (fpS+r0):ℤ):R) :=
    le_trans (div_nonneg (by exact_mod_cast mul_nonneg hcSqHi_nn (by norm_num [S0,fpS])) (by exact_mod_cast (by omega:0<=fpS+r0)))
     (le_divCe (a:=cSqHi*fpS) (b:=fpS+r0) (by omega))
   have:0<=dC (cSqHi*fpS) (fpS+r0):=by exact_mod_cast h0
   omega
  have hexp_ge:((eLo:R)/S0)<=exp (-(gC - t)^2/(1+ρ)):=by
   have harg_ge:(eArg:R)/S0 <= -(gC - t)^2/(1+ρ):=by
    have hd:=le_divCe (a:=cSqHi*fpS) (b:=fpS+r0) (by omega)
    have h1:((cSqHi:R)/S0)/(((fpS+r0:ℤ):R)/S0) <=
      ((dC (cSqHi*fpS) (fpS+r0):ℤ):R)/S0:=by
     have hne:((fpS+r0:ℤ):R) ≠ 0:=by exact_mod_cast (by omega:fpS+r0 ≠ 0)
     calc ((cSqHi:R)/S0)/(((fpS+r0:ℤ):R)/S0)
       = ((cSqHi:R)*S0/((fpS+r0:ℤ):R))/S0:=by field_simp
      _ <= ((dC (cSqHi*fpS) (fpS+r0):ℤ):R)/S0 :=
        dld (by simpa [Int.cast_mul] using hd) hs.le
    have h2:(gC - t)^2/(1+ρ)<=((cSqHi:R)/S0)/(((fpS+r0:ℤ):R)/S0) :=
     div_le_div₀ (div_nonneg (by exact_mod_cast hcSqHi_nn) hs.le) hcSqHi_ge
      (div_pos (by exact_mod_cast (by omega:0 < fpS+r0)) hs) h1r0_le
    have h3:(eArg:R)/S0 = -((dC (cSqHi*fpS) (fpS+r0):ℤ):R)/S0:=by
     unfold eArg;simp [neg_div]
    rw [h3,neg_div,neg_div];linarith
   exact (expNegLo_le heArg_nonpos).trans (exp_le_exp.mpr harg_ge)
  have hM_ge:((mLo:R)/S0) <=
    exp (-(gC - t)^2/(1+ρ))/(2*PI*(pC (t - gC))^2):=by
   have hd:=divFl_le (a:=mF iP0 eLo*fpS) (b:=phHiSq) hpsq_pos
   have h1:((mLo:R)/S0)<=(((mF iP0 eLo:ℤ):R)/S0)/((phHiSq:R)/S0):=by
    have hne:(phHiSq:R) ≠ 0:=by exact_mod_cast hpsq_pos.ne'
    calc ((mLo:R)/S0)
      <= (((mF iP0 eLo:ℤ):R)*S0/(phHiSq:R))/S0 :=
       dld (by simpa [mLo,Int.cast_mul] using hd) hs.le
     _ = (((mF iP0 eLo:ℤ):R)/S0)/((phHiSq:R)/S0):=by field_simp
   refine h1.trans ?_
   by_cases heLo_neg:((eLo:R)/S0)<=0
   .
    have hm_np:((mF iP0 eLo:ℤ):R)/S0<=0 :=
     (mulFl_le iP0 eLo).trans (mul_nonpos_of_nonneg_of_nonpos (by norm_num [iP0,S0,fpS]) heLo_neg)
    exact le_trans (div_nonpos_of_nonpos_of_nonneg hm_np (div_nonneg (by exact_mod_cast hpsq_pos.le) hs.le)) (by positivity)
   .
    have hnum:((mF iP0 eLo:ℤ):R)/S0 <=
      (2*PI)⁻¹*exp (-(gC - t)^2/(1+ρ)) :=
     (mulFl_le iP0 eLo).trans (mul_le_mul pi_bounds_inv2Pi.1 hexp_ge (le_of_not_ge heLo_neg) (by positivity))
    have hdiv:=div_le_div₀ (by positivity) hnum (sq_pos_of_pos (pCp _)) hphHiSq_ge
    exact hdiv.trans_eq (by ring)
  have hM_lo_nn:0<=mLo:=by
   have he_nn:0<=eLo:=by
    unfold eLo eL
    split_ifs
    . norm_num [S0,fpS]
    .
     dsimp only
     split_ifs
     . exact le_rfl
     .
      have hsq_nn:∀ (k:ℕ) (v:ℤ),0<=v->0<=sqLoop false k v:=by
       intro k;induction k with
       | zero=>intro v hv;exact hv
       | succ k ih=>intro v hv;exact ih _ (Int.ediv_nonneg (mul_nonneg hv hv) (by norm_num [S0,fpS]))
      exact hsq_nn 4 _ (le_max_left _ _)
   exact Int.ediv_nonneg (mul_nonneg (Int.ediv_nonneg (mul_nonneg (by norm_num [iP0]) he_nn) (by norm_num [S0,fpS])) (by norm_num [S0,fpS])) hpsq_pos.le
  let δ:R:=(ρ / (2*PI*(pC (t - gC))^2))*exp (-(gC - t)^2/(1+ρ))
  have hδ_np:δ<=0:=mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hρ_np (by positivity)) (exp_nonneg _)
  have hδ_le:δ<=ρ*((mLo:R)/S0):=by
   have h1:δ=ρ*(exp (-(gC - t)^2/(1+ρ))/(2*PI*(pC (t - gC))^2)):=by
    unfold δ;ring
   rw [h1]
   exact mlN hM_ge hρ_np
  have hbiv_fact:bP ((1+ρ)/2) (gC - t)<=(pC (t - gC))^2*(1+δ):=by
   unfold bivPub1 at hpub1
   by_cases hρeq:0<=ρ
   .
    have hρ0:ρ=0:=le_antisymm hρ_np hρeq
    subst hρ0
    rw [if_pos le_rfl,neg_sub] at hpub1
    simp only [mul_zero,zero_pow (by norm_num:3 ≠ 0),zero_div,add_zero,δ] at hpub1 ⊢
    linarith
   .
    rw [if_neg hρeq,neg_sub] at hpub1
    refine hpub1.trans_eq ?_
    unfold δ
    have hne:pC (t - gC) ≠ 0:=(pCp _).ne'
    field_simp [hne]
  have h1δ_pos:0 < 1+δ:=by
   have h1:0 < (pC (t - gC))^2*(1+δ):=lt_of_lt_of_le hbiv_pos hbiv_fact
   exact pos_of_mul_pos_right h1 (sq_nonneg _)
  have hlog_biv:log (bP ((1+ρ)/2) (gC - t)) <=
    2*log (pC (t - gC))+log (1+δ):=by
   have h1:=log_le_log hbiv_pos hbiv_fact
   rw [log_mul (sq_pos_of_pos (pCp _)).ne' h1δ_pos.ne',log_pow] at h1
   simpa using h1
  have hβ_logδ:((1+ρ)/2)*log (1+δ)<=((b0:R)/S0)*log (1+δ) :=
   mul_le_mul_of_nonpos_right hb0_le (log_nonpos h1δ_pos.le (by linarith))
  have hlog_step:((1+ρ)/2)*(2*log (pC (t - gC))) <=
    log (pC ((xm:R)/S0))*(1+ρ) +
     (1+ρ)*mR ((xm:R)/S0)*(t - (tm:R)/S0):=by
   have:((1+ρ)/2)*(2*log (pC (t - gC)))=(1+ρ)*log (pC (t - gC)):=by ring
   rw [this];nlinarith only [hρ_gt,hlog_tan]
  by_cases huM_small:fpS+uM<=500000
  .
   rw [if_pos huM_small] at hchk'
   have hδ_le_dHi:δ<=((dHi:R)/S0):=by
    calc δ<=ρ*((mLo:R)/S0):=hδ_le
     _ <= ((r1:R)/S0)*((mLo:R)/S0) :=
       mlR hρ1 (div_nonneg (by exact_mod_cast hM_lo_nn) hs.le)
     _ <= ((dHi:R)/S0):=le_mulCe r1 mLo
   by_cases hd500:fpS+dHi<=500
   . rw [if_pos hd500] at hchk';exact absurd hchk' (by decide)
   rw [if_neg hd500] at hchk'
   by_cases hokU:(!oLH (fpS+dHi) lUHi)=true
   . rw [if_pos hokU] at hchk';exact absurd hchk' (by decide)
   rw [if_neg hokU] at hchk'
   have hneg_int:mQH (mF (fpS+r0) rmLo) (mC (fpS+r1) rmHi) t0 t1 tm +
     hH0 r0 r1 lPhLo lPhHi 0 0 l1Lo l1Hi+mC b0 lUHi - gLoVal < 0:=of_decide_eq_true hchk'
   clear hchk'
   have hokU':oLH (fpS+dHi) lUHi=true:=by cases h:oLH (fpS+dHi) lUHi <;> simp_all
   have hd_log:=oLHs hokU'
   have hlogδ_le:log (1+δ)<=((lUHi:R)/S0):=by
    have h1:=log_le_log h1δ_pos (by linarith:1+δ<=1+(dHi:R)/S0)
    have h2:=hd_log.2
    rw [Int.cast_add,add_div,div_self hs.ne'] at h2
    exact h1.trans h2
   have hmul_b0:((b0:R)/S0)*log (1+δ)<=((mC b0 lUHi:ℤ):R)/S0 :=
    (mlL hlogδ_le (div_nonneg (by exact_mod_cast hb0_nn) hs.le)).trans (le_mulCe b0 lUHi)
   have hhh:=hHs hr0_gt hr01 hr1_le hρ0 hρ1 hρ_lt hlPh_lo hlPh_hi
    (by simp:((0:ℤ):R)/S0<=0) (by simp:(0:R)<=((0:ℤ):R)/S0) hl1Lo hl1Hi
   simp only [zero_mul,add_zero] at hhh
   have hneg_r:((mQH (mF (fpS+r0) rmLo) (mC (fpS+r1) rmHi) t0 t1 tm +
     hH0 r0 r1 lPhLo lPhHi 0 0 l1Lo l1Hi+mC b0 lUHi - gLoVal:ℤ):R)/S0 < 0 :=
    div_neg_of_neg_of_pos (by exact_mod_cast hneg_int) hs
   simp only [Int.cast_sub,Int.cast_add,sub_div,add_div] at hneg_r
   nlinarith only [hβ0,hlog_biv,hβ_logδ,hmul_b0,hlog_step,hq1,hhh,hgLo,hneg_r]
  .
   rw [if_neg huM_small] at hchk'
   by_cases hokU:(!oLH (fpS+uM) lUHi)=true
   . rw [if_pos hokU] at hchk';exact absurd hchk' (by decide)
   rw [if_neg hokU] at hchk'
   have hneg_int:mQH (mF (fpS+r0) rmLo) (mC (fpS+r1) rmHi) t0 t1 tm +
     hH0 r0 r1 lPhLo lPhHi (dF (mF b0 mLo*fpS) (fpS+uM))
      (dC (mC b0 mLo*fpS) (fpS+uM)) l1Lo l1Hi+cTerm - gLoVal < 0:=of_decide_eq_true hchk'
   clear hchk'
   have hokU':oLH (fpS+uM) lUHi=true:=by cases h:oLH (fpS+uM) lUHi <;> simp_all
   have huM_log:=oLHs hokU'
   have h1uM_pos:(0:R) < 1+(uM:R)/S0:=by
    have:(0:R) < ((fpS+uM:ℤ):R)/S0:=div_pos (by exact_mod_cast huM_log.1) hs
    rwa [Int.cast_add,add_div,div_self hs.ne'] at this
   have hlog_conc:log (1+δ)<=log (1+(uM:R)/S0) +
     (δ - (uM:R)/S0)/(1+(uM:R)/S0):=by
    have h:=log_le_sub_one_of_pos (div_pos h1δ_pos h1uM_pos)
    rw [log_div h1δ_pos.ne' h1uM_pos.ne'] at h
    have heq:(1+δ)/(1+(uM:R)/S0) - 1 =
      (δ - (uM:R)/S0)/(1+(uM:R)/S0):=by
     rw [div_sub_one h1uM_pos.ne'];congr 1;ring
    linarith
   have hlog_uM_hi:log (1+(uM:R)/S0)<=((lUHi:R)/S0):=by
    have h:=huM_log.2
    rwa [Int.cast_add,add_div,div_self hs.ne'] at h
   set K:R:=(((b0:R)/S0)*((mLo:R)/S0))/(1+(uM:R)/S0)
   have hb0_nnR:(0:R)<=(b0:R)/S0:=div_nonneg (by exact_mod_cast hb0_nn) hs.le
   have hK_lo:((dF (mF b0 mLo*fpS) (fpS+uM):ℤ):R)/S0<=K:=by
    have hd:=divFl_le (a:=mF b0 mLo*fpS) (b:=fpS+uM) huM_log.1
    have hne:((fpS+uM:ℤ):R) ≠ 0:=by exact_mod_cast huM_log.1.ne'
    have h1u:(1:R)+(uM:R)/S0=((fpS+uM:ℤ):R)/S0:=by
     rw [Int.cast_add,add_div,div_self hs.ne']
    have h1:((dF (mF b0 mLo*fpS) (fpS+uM):ℤ):R)/S0 <=
      (((mF b0 mLo:ℤ):R)/S0)/(1+(uM:R)/S0):=by
     rw [h1u]
     calc ((dF (mF b0 mLo*fpS) (fpS+uM):ℤ):R)/S0
       <= (((mF b0 mLo:ℤ):R)*S0/((fpS+uM:ℤ):R))/S0 :=
        dld (by simpa [Int.cast_mul] using hd) hs.le
      _ = (((mF b0 mLo:ℤ):R)/S0)/(((fpS+uM:ℤ):R)/S0):=by field_simp
    exact h1.trans (dld (mulFl_le b0 mLo) h1uM_pos.le)
   have hK_hi:K<=((dC (mC b0 mLo*fpS) (fpS+uM):ℤ):R)/S0:=by
    have hd:=le_divCe (a:=mC b0 mLo*fpS) (b:=fpS+uM) huM_log.1
    have hne:((fpS+uM:ℤ):R) ≠ 0:=by exact_mod_cast huM_log.1.ne'
    have h1u:(1:R)+(uM:R)/S0=((fpS+uM:ℤ):R)/S0:=by
     rw [Int.cast_add,add_div,div_self hs.ne']
    refine (dld (le_mulCe b0 mLo) h1uM_pos.le).trans ?_
    rw [h1u]
    calc (((mC b0 mLo:ℤ):R)/S0)/(((fpS+uM:ℤ):R)/S0)
      = (((mC b0 mLo:ℤ):R)*S0/((fpS+uM:ℤ):R))/S0:=by field_simp
     _ <= ((dC (mC b0 mLo*fpS) (fpS+uM):ℤ):R)/S0 :=
       dld (by simpa [Int.cast_mul] using hd) hs.le
   have hcTerm_ge:((b0:R)/S0)*log (1+(uM:R)/S0) +
     ((b0:R)/S0)*(-((uM:R)/S0))/(1+(uM:R)/S0) <=
     ((cTerm:R)/S0):=by
    have h1:((b0:R)/S0)*log (1+(uM:R)/S0)<=((mC b0 lUHi:ℤ):R)/S0 :=
     (mlL hlog_uM_hi hb0_nnR).trans (le_mulCe b0 lUHi)
    have h2:((b0:R)/S0)*(-((uM:R)/S0))<=((mC b0 (-uM):ℤ):R)/S0:=by
     have:=le_mulCe b0 (-uM);simpa [neg_div] using this
    have h3:(((mC b0 (-uM):ℤ):R)/S0)/(1+(uM:R)/S0) <=
      ((dC (mC b0 (-uM)*fpS) (fpS+uM):ℤ):R)/S0:=by
     have hd:=le_divCe (a:=mC b0 (-uM)*fpS) (b:=fpS+uM) huM_log.1
     have hne:((fpS+uM:ℤ):R) ≠ 0:=by exact_mod_cast huM_log.1.ne'
     have h1u:(1:R)+(uM:R)/S0=((fpS+uM:ℤ):R)/S0:=by
      rw [Int.cast_add,add_div,div_self hs.ne']
     rw [h1u]
     calc (((mC b0 (-uM):ℤ):R)/S0)/(((fpS+uM:ℤ):R)/S0)
       = (((mC b0 (-uM):ℤ):R)*S0/((fpS+uM:ℤ):R))/S0:=by field_simp
      _ <= ((dC (mC b0 (-uM)*fpS) (fpS+uM):ℤ):R)/S0 :=
        dld (by simpa [Int.cast_mul] using hd) hs.le
    have h23:=(dld h2 h1uM_pos.le).trans h3
    unfold cTerm;rw [Int.cast_add,add_div];linarith
   have hδ_split:((b0:R)/S0)*log (1+δ)<=K*ρ+((cTerm:R)/S0):=by
    have hnum:δ - (uM:R)/S0<=ρ*((mLo:R)/S0) - (uM:R)/S0:=by
     linarith only [hδ_le]
    have h1:((b0:R)/S0)*log (1+δ) <=
      ((b0:R)/S0)*(log (1+(uM:R)/S0) +
       (ρ*((mLo:R)/S0) - (uM:R)/S0)/(1+(uM:R)/S0)) :=
     mlL (hlog_conc.trans (add_le_add le_rfl (dld hnum h1uM_pos.le))) hb0_nnR
    have halg:((b0:R)/S0)*(log (1+(uM:R)/S0) +
       (ρ*((mLo:R)/S0) - (uM:R)/S0)/(1+(uM:R)/S0)) =
      K*ρ+(((b0:R)/S0)*log (1+(uM:R)/S0) +
       ((b0:R)/S0)*(-((uM:R)/S0))/(1+(uM:R)/S0)):=by
     unfold K;ring
    linarith only [h1,halg,hcTerm_ge]
   have hhc:=hHs hr0_gt hr01 hr1_le hρ0 hρ1 hρ_lt hlPh_lo hlPh_hi hK_lo hK_hi hl1Lo hl1Hi
   have hneg_r:((mQH (mF (fpS+r0) rmLo) (mC (fpS+r1) rmHi) t0 t1 tm +
     hH0 r0 r1 lPhLo lPhHi (dF (mF b0 mLo*fpS) (fpS+uM))
      (dC (mC b0 mLo*fpS) (fpS+uM)) l1Lo l1Hi+cTerm - gLoVal:ℤ):R)/S0 < 0 :=
    div_neg_of_neg_of_pos (by exact_mod_cast hneg_int) hs
   simp only [Int.cast_sub,Int.cast_add,sub_div,add_div] at hneg_r
   nlinarith only [hβ0,hlog_biv,hβ_logδ,hδ_split,hlog_step,hq1,hhc,hgLo,hneg_r]
 . rw [if_neg hr1_np] at hchk;exact absurd hchk (by decide)
lemma cTs:∀ (tr:BoxTree) (r0 r1 t0 t1:ℤ),
  -fpS < r0->r0 < r1->r1<=fpS->t0 < t1 ->
  cT0 r0 r1 t0 t1 tr=true ->
  ∀ {ρ t:R},(r0:R)/S0<=ρ->ρ<=(r1:R)/S0->ρ < 1 ->
   (t0:R)/S0<=t->t<=(t1:R)/S0 ->
   -t^2/2+((1+ρ)/2)*log (bP ((1+ρ)/2) (gC - t)) -
    ((1+ρ)/2)*log (1+ρ)<=gStar+aConst*ρ+bConst*ρ^3:=by
 intro tr
 induction tr with
 | l a nc d e =>
  intro r0 r1 t0 t1 hr0 hr01 hr1 ht01 hchk ρ t hρ0 hρ1 hρ_lt ht0 ht1
  exact cLs hr0 hr01 hr1 ht01 hρ0 hρ1 hρ_lt ht0 ht1 hchk
 | r tl tr ihl ihr =>
  intro r0 r1 t0 t1 hr0 hr01 hr1 ht01 hchk ρ t hρ0 hρ1 hρ_lt ht0 ht1
  unfold cT0 at hchk
  dsimp only at hchk
  rw [Bool.and_eq_true] at hchk
  set rm:ℤ:=(r0+r1)/2
  by_cases hlt:r0=rm\/rm=r1
  ·
   have hrm_lt:rm < r1:=by omega
   have hrm_eq:r0=rm:=by omega
   have hle_rm:(rm:R)/S0<=ρ:=by rwa [← hrm_eq]
   exact ihr rm r1 t0 t1 (by omega) hrm_lt hr1 ht01 hchk.2 hle_rm hρ1 hρ_lt ht0 ht1
  .
   have hr0m:r0 < rm:=by omega
   have hrm1:rm < r1:=by omega
   by_cases hρm:ρ<=(rm:R)/S0
   . exact ihl r0 rm t0 t1 hr0 hr0m (by omega) ht01 hchk.1 hρ0 hρm hρ_lt ht0 ht1
   . exact ihr rm r1 t0 t1 (by omega) hrm1 hr1 ht01 hchk.2 (le_of_not_ge hρm) hρ1 hρ_lt ht0 ht1
 | t tl tr ihl ihr =>
  intro r0 r1 t0 t1 hr0 hr01 hr1 ht01 hchk ρ t hρ0 hρ1 hρ_lt ht0 ht1
  unfold cT0 at hchk
  dsimp only at hchk
  rw [Bool.and_eq_true] at hchk
  set tm:ℤ:=(t0+t1)/2
  by_cases hlt:t0=tm\/tm=t1
  .
   have htm_lt:tm < t1:=by omega
   have htm_eq:t0=tm:=by omega
   have hle_tm:(tm:R)/S0<=t:=by rwa [← htm_eq]
   exact ihr r0 r1 tm t1 hr0 hr01 hr1 htm_lt hchk.2 hρ0 hρ1 hρ_lt hle_tm ht1
  .
   have ht0m:t0 < tm:=by omega
   have htm1:tm < t1:=by omega
   by_cases htm:t<=(tm:R)/S0
   . exact ihl r0 r1 t0 tm hr0 hr01 hr1 ht0m hchk.1 hρ0 hρ1 hρ_lt ht0 htm
   . exact ihr r0 r1 tm t1 hr0 hr01 hr1 htm1 hchk.2 hρ0 hρ1 hρ_lt (le_of_not_ge htm) ht1
lemma neg_mul_log_le_inv_exp {x:R} (hx:0 < x):-x*log x<=exp (-1):=by
 have h:=log_le_sub_one_of_pos (div_pos (exp_pos (-1)) hx)
 rw [log_div (exp_pos _).ne' hx.ne',log_exp] at h
 have h1:=mlL h hx.le
 have heq:x*(exp (-1)/x - 1)=exp (-1) - x:=by field_simp
 rw [heq] at h1
 linarith
lemma inv_exp_lt_two_fifths:exp (-1:R) < 2/5:=by
 have h1:((eH (-fpS):ℤ):R)/S0 < 2/5:=by
  have hchk:eH (-fpS) < 4000000:=by decide
  have:(eH (-fpS):R) < 4000000:=by exact_mod_cast hchk
  norm_num [S0,fpS] at this ⊢;linarith
 have h2:=le_expNegHi (x:=-fpS) (by norm_num [S0,fpS])
 have h3:((-fpS:ℤ):R)/S0 = -1:=by norm_num [S0,fpS]
 rw [h3] at h2
 linarith
lemma analytic_tail_t_ge_2 {ρ t:R} (hρ0:-1 < ρ) (hρ1:ρ < 1) (ht:2<=t) :
  -t^2/2+((1+ρ)/2)*log (bP ((1+ρ)/2) (gC - t)) -
   ((1+ρ)/2)*log (1+ρ)<=gStar+aConst*ρ+bConst*ρ^3:=by
 have hβ0:0 < (1+ρ)/2:=by linarith
 have hβ1:(1+ρ)/2 < 1:=by linarith
 have hbiv_pos:=bivProb_pos (gC - t) hβ0 hβ1
 have hbiv_le1:bP ((1+ρ)/2) (gC - t)<=1 :=
  (bivProb_le_cdf _ hβ0 hβ1).trans (stdPhiCDF_lt_one _).le
 have hlog_np:log (bP ((1+ρ)/2) (gC - t))<=0 :=
  log_nonpos hbiv_pos.le hbiv_le1
 have h1:-((1+ρ)/2)*log (1+ρ)<=1/5:=by
  have:=neg_mul_log_le_inv_exp (show 0 < 1+ρ by linarith)
  linarith [inv_exp_lt_two_fifths]
 have hg:=gStar_ge_gLoVal
 have ha:=aConst_bounds
 have hg_num:(-52/100:R)<=gStar:=by norm_num [gLoVal,S0,fpS] at hg;linarith
 have ha_lo:(-75/100:R)<=aConst:=by norm_num [aLoVal,S0,fpS] at ha;linarith
 have ha_hi:aConst<=0:=by norm_num [aHiVal,S0,fpS] at ha;linarith
 have hrhs:(-139/100:R)<=gStar+aConst*ρ+bConst*ρ^3:=by
  have hb_eq:bConst=3/25:=rfl
  have habs:-1<=ρ^3:=by nlinarith [sq_nonneg ρ]
  by_cases hρs:0<=ρ
  .
   have:(-75/100:R)<=aConst*ρ:=by nlinarith
   nlinarith [sq_nonneg ρ]
  .
   have:0<=aConst*ρ:=mul_nonneg_of_nonpos_of_nonpos ha_hi (le_of_not_ge hρs)
   nlinarith
 have htsq:-t^2/2 <= -2:=by nlinarith
 have hterm:((1+ρ)/2)*log (bP ((1+ρ)/2) (gC - t))<=0 :=
  mul_nonpos_of_nonneg_of_nonpos hβ0.le hlog_np
 linarith
lemma analytic_tail_t_le_neg32 {ρ t:R} (hρ0:-1 < ρ) (hρ1:ρ < 1) (ht:t <= -3/2) :
  -t^2/2+((1+ρ)/2)*log (bP ((1+ρ)/2) (gC - t)) -
   ((1+ρ)/2)*log (1+ρ)<=gStar+aConst*ρ+bConst*ρ^3:=by
 have hβ0:0 < (1+ρ)/2:=by linarith
 have hβ1:(1+ρ)/2 < 1:=by linarith
 have hbiv_pos:=bivProb_pos (gC - t) hβ0 hβ1
 have hcdf_le:pC (t - gC)<=exp (-2):=by
  have hx:t - gC<=((-15500000:ℤ):R)/S0:=by
   norm_num [gC,S0,fpS];linarith
  have h1:=(pCm.monotone hx).trans (le_phiCDFHi (-15500000))
  have h2:((cH (-15500000):ℤ):R)/S0<=((eL (-2*fpS):ℤ):R)/S0:=by
   have hchk:cH (-15500000)<=eL (-2*fpS):=by decide
   exact dld (by exact_mod_cast hchk) fpS_pos.le
  have h3:=expNegLo_le (x:=-2*fpS) (by norm_num [S0,fpS])
  have h4:((-2*fpS:ℤ):R)/S0 = -2:=by norm_num [S0,fpS]
  rw [h4] at h3
  exact h1.trans (h2.trans h3)
 have hlog_le:log (bP ((1+ρ)/2) (gC - t)) <= -2:=by
  have h1:=bivProb_le_cdf (gC - t) hβ0 hβ1
  rw [neg_sub] at h1
  have h2:=log_le_log hbiv_pos (h1.trans hcdf_le)
  rwa [log_exp] at h2
 have hterm:((1+ρ)/2)*log (bP ((1+ρ)/2) (gC - t)) <= -(1+ρ):=by
  nlinarith
 have hg:=gStar_ge_gLoVal
 have ha:=aConst_bounds
 have hg_num:(-52/100:R)<=gStar:=by norm_num [gLoVal,S0,fpS] at hg;linarith
 have ha_lo:(-75/100:R)<=aConst:=by norm_num [aLoVal,S0,fpS] at ha;linarith
 have ha_hi:aConst<=0:=by norm_num [aHiVal,S0,fpS] at ha;linarith
 have htsq:-t^2/2 <= -9/8:=by nlinarith
 have hb_eq:bConst=3/25:=rfl
 by_cases hρs:0<=ρ
 .
  have hlog1:0<=log (1+ρ):=log_nonneg (by linarith)
  have hlogt:-((1+ρ)/2)*log (1+ρ)<=0:=by nlinarith
  have hb3:0<=bConst*ρ^3:=by rw [hb_eq];positivity
  nlinarith
 .
  have h1:-((1+ρ)/2)*log (1+ρ)<=1/5:=by
   have:=neg_mul_log_le_inv_exp (show 0 < 1+ρ by linarith)
   linarith [inv_exp_lt_two_fifths]
  have ha_nn:0<=aConst*ρ:=mul_nonneg_of_nonpos_of_nonpos ha_hi (le_of_not_ge hρs)
  have hρ3:(-1:R)<=ρ^3:=by nlinarith [sq_nonneg ρ]
  have hb3:-bConst<=bConst*ρ^3:=by rw [hb_eq];nlinarith
  linarith
lemma analytic_tail_rho_le_neg96 {ρ t:R} (hρ0:-1 < ρ) (hρ96:ρ <= -96/100) :
  -t^2/2+((1+ρ)/2)*log (bP ((1+ρ)/2) (gC - t)) -
   ((1+ρ)/2)*log (1+ρ)<=gStar+aConst*ρ+bConst*ρ^3:=by
 have hβ0:0 < (1+ρ)/2:=by linarith
 have hβ1:(1+ρ)/2 < 1:=by linarith
 have hbiv_pos:=bivProb_pos (gC - t) hβ0 hβ1
 have hlog_np:log (bP ((1+ρ)/2) (gC - t))<=0 :=
  log_nonpos hbiv_pos.le ((bivProb_le_cdf _ hβ0 hβ1).trans (stdPhiCDF_lt_one _).le)
 have hterm:((1+ρ)/2)*log (bP ((1+ρ)/2) (gC - t))<=0 :=
  mul_nonpos_of_nonneg_of_nonpos hβ0.le hlog_np
 have hmono:-(1+ρ)*log (1+ρ) <= -(4/100:R)*log (4/100:R):=by
  let g:R->R:=fun x=>-x*log x
  have hderiv:∀ x ∈ Set.Icc (1+ρ) (4/100:R),HD g (-log x - 1) x:=by
   intro x hx
   have hxp:0 < x:=lt_of_lt_of_le (by linarith) hx.1
   have h1:=((hdi x).fun_neg.fun_mul (hasDerivAt_log hxp.ne'))
   exact h1.congr_deriv (by simp only [Pi.neg_apply,id_eq];field_simp [hxp.ne'];ring)
  have hnonneg:∀ x ∈ Set.Icc (1+ρ) (4/100:R),0 <= -log x - 1:=by
   intro x hx
   have hxp:0 < x:=lt_of_lt_of_le (by linarith) hx.1
   have hexp:(4/100:R)<=exp (-1):=by
    have h1:=expNegLo_le (x:=-fpS) (by norm_num [S0,fpS])
    have h2:((-fpS:ℤ):R)/S0 = -1:=by norm_num [S0,fpS]
    rw [h2] at h1
    have hchk:400000<=eL (-fpS):=by decide
    have h3:(4/100:R)<=((eL (-fpS):ℤ):R)/S0:=by
     have:(400000:R)<=(eL (-fpS):R):=by exact_mod_cast hchk
     norm_num [S0,fpS] at this ⊢;linarith
    exact h3.trans h1
   have hlogx:log x <= -1:=by
    have:=log_le_log hxp (hx.2.trans hexp)
    rwa [log_exp] at this
   linarith
  have hinc:MonotoneOn g (Set.Icc (1+ρ) (4/100:R)) :=
   monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    (fun x hx=>(hderiv x hx).continuousAt.continuousWithinAt)
    (fun x hx=>(hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    (fun x hx=>by rw [(hderiv x (interior_subset hx)).deriv];exact hnonneg x (interior_subset hx))
  exact hinc ⟨le_rfl,by linarith⟩ ⟨by linarith,le_rfl⟩ (by linarith)
 have hlog004:-log (4/100:R)<=33/10:=by
  have h1:=le_expNegHi (x:=-33000000) (by norm_num)
  have h2:((-33000000:ℤ):R)/S0 = -33/10:=by norm_num [S0,fpS]
  rw [h2] at h1
  have hchk:eH (-33000000)<=400000:=by decide
  have h3:((eH (-33000000):ℤ):R)/S0<=4/100:=by
   have:(eH (-33000000):R)<=400000:=by exact_mod_cast hchk
   norm_num [S0,fpS] at this ⊢;linarith
  have h4:=log_le_log (exp_pos _) (h1.trans h3)
  rw [log_exp] at h4;linarith
 have hlog_bd:-((1+ρ)/2)*log (1+ρ)<=66/1000:=by nlinarith
 have hg:=gStar_ge_gLoVal
 have ha:=aConst_bounds
 have hg_num:(-51967/100000:R)<=gStar:=by norm_num [gLoVal,S0,fpS] at hg;linarith
 have ha_hi:aConst <= -746005/1000000:=by norm_num [aHiVal,S0,fpS] at ha;linarith
 have hb_eq:bConst=3/25:=rfl
 have hρ3:(-1:R)<=ρ^3:=by nlinarith [sq_nonneg ρ]
 have hb3:-bConst<=bConst*ρ^3:=by rw [hb_eq];nlinarith
 have ha_mul:(-746005/1000000:R)*(-96/100)<=aConst*ρ:=by nlinarith
 have htsq:-t^2/2<=0:=by nlinarith [sq_nonneg t]
 linarith
structure Iv where
 lo:ℤ
 hi:ℤ
structure Iv.mem (I:Iv) (x:R):Prop where
 lo_le:(I.lo:R)/S0<=x
 le_hi:x<=(I.hi:R)/S0
def Iv.pt (v:ℤ):Iv:=⟨v,v⟩
def Iv.add (I J:Iv):Iv:=⟨I.lo+J.lo,I.hi+J.hi⟩
def Iv.sub (I J:Iv):Iv:=⟨I.lo - J.hi,I.hi - J.lo⟩
def Iv.neg (I:Iv):Iv:=⟨-I.hi,-I.lo⟩
def Iv.scale2 (I:Iv):Iv:=⟨2*I.lo,2*I.hi⟩
def Iv.half (I:Iv):Iv:=⟨dF I.lo 2,dC I.hi 2⟩
def Iv.mul (I J:Iv):Iv :=
 let p1:=I.lo*J.lo;let p2:=I.lo*J.hi
 let p3:=I.hi*J.lo;let p4:=I.hi*J.hi
 ⟨dF (min (min p1 p2) (min p3 p4)) fpS,dC (max (max p1 p2) (max p3 p4)) fpS⟩
def Iv.sq (I:Iv):Iv :=
 if I.lo<=0/\0<=I.hi then
  ⟨0,dC (max (I.lo*I.lo) (I.hi*I.hi)) fpS⟩
 else
  ⟨dF (min (I.lo*I.lo) (I.hi*I.hi)) fpS,dC (max (I.lo*I.lo) (I.hi*I.hi)) fpS⟩
def Iv.divPos (I J:Iv):Iv :=
 ⟨if 0<=I.lo then dF (I.lo*fpS) J.hi else dF (I.lo*fpS) J.lo,
  if 0<=I.hi then dC (I.hi*fpS) J.lo else dC (I.hi*fpS) J.hi⟩
def Iv.expNeg (I:Iv):Iv:=⟨eL I.lo,eH I.hi⟩
lemma Iv.pt_mem (v:ℤ):(Iv.pt v).mem ((v:R)/S0):=⟨le_rfl,le_rfl⟩
lemma Iv.mem.add_mem {I J:Iv} {x y:R} (hx:I.mem x) (hy:J.mem y):(I.add J).mem (x+y):=by
 constructor <;> simp only [Iv.add,Int.cast_add,add_div] <;> linarith [hx.1,hx.2,hy.1,hy.2]
lemma Iv.mem.sub_mem {I J:Iv} {x y:R} (hx:I.mem x) (hy:J.mem y):(I.sub J).mem (x - y):=by
 constructor <;> simp only [Iv.sub,Int.cast_sub,sub_div] <;> linarith [hx.1,hx.2,hy.1,hy.2]
lemma Iv.mem.neg_mem {I:Iv} {x:R} (hx:I.mem x):I.neg.mem (-x):=by
 constructor <;> simp only [Iv.neg,Int.cast_neg,neg_div] <;> linarith [hx.1,hx.2]
lemma Iv.mem.scale2_mem {I:Iv} {x:R} (hx:I.mem x):I.scale2.mem (2*x):=by
 constructor <;> simp only [Iv.scale2,Int.cast_mul,Int.cast_ofNat,mul_div_assoc] <;> linarith [hx.1,hx.2]
lemma Iv.mem.half_mem {I:Iv} {x:R} (hx:I.mem x):I.half.mem (x/2):=by
 have hs:(0:R) < S0:=fpS_pos
 constructor <;> dsimp only [Iv.half]
 .
  have hd:=divFl_le (a:=I.lo) (b:=2) (by norm_num)
  have h1:((dF I.lo 2:ℤ):R)/S0<=((I.lo:R)/2)/S0 :=
   dld hd hs.le
  have h2:((I.lo:R)/2)/S0=((I.lo:R)/S0)/2:=by ring
  linarith [hx.1]
 .
  have hd:=le_divCe (a:=I.hi) (b:=2) (by norm_num)
  have h1:((I.hi:R)/2)/S0<=((dC I.hi 2:ℤ):R)/S0 :=
   dld hd hs.le
  have h2:((I.hi:R)/2)/S0=((I.hi:R)/S0)/2:=by ring
  linarith [hx.2]
lemma Iv.mem.mul_mem {I J:Iv} {x y:R} (hx:I.mem x) (hy:J.mem y):(I.mul J).mem (x*y):=by
 have hs:(0:R) < S0:=fpS_pos
 set a:=(I.lo:R)/S0;set b:=(I.hi:R)/S0
 set c:=(J.lo:R)/S0;set d:=(J.hi:R)/S0
 have hlo:min (min (a*c) (a*d)) (min (b*c) (b*d))<=x*y:=by
  by_cases hy0:0<=y
  .
   have h1:a*y<=x*y:=mlR hx.1 hy0
   by_cases ha0:0<=a
   . exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (mlL hy.1 ha0) h1))
   . exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (le_trans (mlN hy.2 (le_of_not_ge ha0)) h1))
  .
   have h1:b*y<=x*y:=mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hy0)
   by_cases hb0:0<=b
   . exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (le_trans (mlL hy.1 hb0) h1))
   . exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (mlN hy.2 (le_of_not_ge hb0)) h1))
 have hhi:x*y<=max (max (a*c) (a*d)) (max (b*c) (b*d)):=by
  by_cases hy0:0<=y
  .
   have h1:x*y<=b*y:=mlR hx.2 hy0
   by_cases hb0:0<=b
   . exact le_trans h1 (le_trans (mlL hy.2 hb0) (le_trans (le_max_right _ _) (le_max_right _ _)))
   . exact le_trans h1 (le_trans (mlN hy.1 (le_of_not_ge hb0)) (le_trans (le_max_left _ _) (le_max_right _ _)))
  .
   have h1:x*y<=a*y:=mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hy0)
   by_cases ha0:0<=a
   . exact le_trans h1 (le_trans (mlL hy.2 ha0) (le_trans (le_max_right _ _) (le_max_left _ _)))
   . exact le_trans h1 (le_trans (mlN hy.1 (le_of_not_ge ha0)) (le_trans (le_max_left _ _) (le_max_left _ _)))
 set mMin:ℤ:=min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi))
 set mMax:ℤ:=max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi))
 have hfl_step:∀ {p q:ℤ},mMin<=p*q->((dF mMin fpS:ℤ):R)/S0<=((p:R)/S0)*((q:R)/S0):=by
  intro p q hle
  have h1:=divFl_le (a:=mMin) (b:=fpS) (by norm_num [S0,fpS])
  have h2:(mMin:R)<=((p*q:ℤ):R):=by exact_mod_cast hle
  calc ((dF mMin fpS:ℤ):R)/S0
    <= ((mMin:R)/S0)/S0:=dld h1 hs.le
   _ <= (((p*q:ℤ):R)/S0)/S0:=dld (dld h2 hs.le) hs.le
   _ = ((p:R)/S0)*((q:R)/S0):=by rw [Int.cast_mul];ring
 have hce_step:∀ {p q:ℤ},p*q<=mMax->((p:R)/S0)*((q:R)/S0)<=((dC mMax fpS:ℤ):R)/S0:=by
  intro p q hle
  have h1:=le_divCe (a:=mMax) (b:=fpS) (by norm_num [S0,fpS])
  have h2:((p*q:ℤ):R)<=(mMax:R):=by exact_mod_cast hle
  calc ((p:R)/S0)*((q:R)/S0)
    = (((p*q:ℤ):R)/S0)/S0:=by rw [Int.cast_mul];ring
   _ <= ((mMax:R)/S0)/S0:=dld (dld h2 hs.le) hs.le
   _ <= ((dC mMax fpS:ℤ):R)/S0:=dld h1 hs.le
 constructor
 .
  exact (le_min (le_min (hfl_step ((min_le_left _ _).trans (min_le_left _ _)))
   (hfl_step ((min_le_left _ _).trans (min_le_right _ _))))
   (le_min (hfl_step ((min_le_right _ _).trans (min_le_left _ _)))
   (hfl_step ((min_le_right _ _).trans (min_le_right _ _))))).trans hlo
 .
  exact hhi.trans (max_le (max_le (hce_step ((le_max_left _ _).trans (le_max_left _ _)))
   (hce_step ((le_max_right _ _).trans (le_max_left _ _))))
   (max_le (hce_step ((le_max_left _ _).trans (le_max_right _ _)))
   (hce_step ((le_max_right _ _).trans (le_max_right _ _)))))
lemma Iv.mem.sq_mem {I:Iv} {x:R} (hx:I.mem x):I.sq.mem (x^2):=by
 have hs:(0:R) < S0:=fpS_pos
 have hhi:x^2<=((dC (max (I.lo*I.lo) (I.hi*I.hi)) fpS:ℤ):R)/S0:=by
  have h1:x^2<=max (((I.lo:R)/S0)^2) (((I.hi:R)/S0)^2):=by
   by_cases h0:0<=x
   . exact le_trans (by nlinarith [hx.2]) (le_max_right _ _)
   . exact le_trans (by nlinarith [hx.1]) (le_max_left _ _)
  have hlo_sq:((I.lo:R)/S0)^2<=((dC (I.lo*I.lo) fpS:ℤ):R)/S0:=by
   rw [pow_two];exact le_mulCe I.lo I.lo
  have hhi_sq:((I.hi:R)/S0)^2<=((dC (I.hi*I.hi) fpS:ℤ):R)/S0:=by
   rw [pow_two];exact le_mulCe I.hi I.hi
  refine h1.trans (max_le ?_ ?_)
  . exact hlo_sq.trans (dld (by exact_mod_cast le_divCe_mono (le_max_left (I.lo*I.lo) (I.hi*I.hi))) hs.le)
  . exact hhi_sq.trans (dld (by exact_mod_cast le_divCe_mono (le_max_right (I.lo*I.lo) (I.hi*I.hi))) hs.le)
 unfold Iv.sq
 split_ifs with h0
 . exact ⟨by simp [sq_nonneg],hhi⟩
 .
  refine ⟨?_,hhi⟩
  have hcase:0 < I.lo\/I.hi < 0:=by omega
  have hfl_step:∀ {p:ℤ},min (I.lo*I.lo) (I.hi*I.hi)<=p*p ->
    ((dF (min (I.lo*I.lo) (I.hi*I.hi)) fpS:ℤ):R)/S0<=((p:R)/S0)^2:=by
   intro p hle
   have hd:=divFl_le (a:=min (I.lo*I.lo) (I.hi*I.hi)) (b:=fpS) (by norm_num [S0,fpS])
   have h2:((min (I.lo*I.lo) (I.hi*I.hi):ℤ):R)<=((p*p:ℤ):R):=by exact_mod_cast hle
   calc ((dF (min (I.lo*I.lo) (I.hi*I.hi)) fpS:ℤ):R)/S0
     <= (((min (I.lo*I.lo) (I.hi*I.hi):ℤ):R)/S0)/S0:=dld hd hs.le
    _ <= (((p*p:ℤ):R)/S0)/S0:=dld (dld h2 hs.le) hs.le
    _ = ((p:R)/S0)^2:=by rw [Int.cast_mul];ring
  rcases hcase with hlo_p | hhi_n
  .
   have h1:((I.lo:R)/S0)^2<=x^2:=by
    have:(0:R)<=(I.lo:R)/S0:=div_nonneg (by exact_mod_cast hlo_p.le) hs.le
    nlinarith [hx.1]
   exact (hfl_step (min_le_left _ _)).trans h1
  .
   have h1:((I.hi:R)/S0)^2<=x^2:=by
    have:(I.hi:R)/S0<=0:=div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hhi_n.le) hs.le
    nlinarith [hx.2]
   exact (hfl_step (min_le_right _ _)).trans h1
where
 le_divCe_mono {a b:ℤ} (h:a<=b):dC a fpS<=dC b fpS:=by
  unfold dC
  have:(-b)/fpS<=(-a)/fpS:=Int.ediv_le_ediv (by norm_num [S0,fpS]) (by omega)
  omega
lemma Iv.mem.divPos_mem {I J:Iv} {x y:R} (hx:I.mem x) (hy:J.mem y) (hJ:0 < J.lo) :
  (I.divPos J).mem (x/y):=by
 have hs:(0:R) < S0:=fpS_pos
 have hJlo_pos:(0:R) < (J.lo:R)/S0:=div_pos (by exact_mod_cast hJ) hs
 have hy_pos:0 < y:=lt_of_lt_of_le hJlo_pos hy.1
 have hJhi_pos:0 < J.hi:=by
  have:(J.lo:R)/S0<=(J.hi:R)/S0:=hy.1.trans hy.2
  have:(J.lo:R)<=(J.hi:R):=(div_le_div_iff_of_pos_right hs).mp this
  have:J.lo<=J.hi:=by exact_mod_cast this
  omega
 have hJhi_posR:(0:R) < (J.hi:R)/S0:=div_pos (by exact_mod_cast hJhi_pos) hs
 constructor
 .
  unfold Iv.divPos;dsimp only
  split_ifs with h0
  .
   have hd:=divFl_le (a:=I.lo*fpS) (b:=J.hi) hJhi_pos
   have hne:(J.hi:R) ≠ 0:=by exact_mod_cast hJhi_pos.ne'
   have h1:((dF (I.lo*fpS) J.hi:ℤ):R)/S0<=((I.lo:R)/S0)/((J.hi:R)/S0):=by
    calc _ <= ((I.lo:R)*S0/(J.hi:R))/S0 :=
       dld (by simpa [Int.cast_mul] using hd) hs.le
     _ = ((I.lo:R)/S0)/((J.hi:R)/S0):=by field_simp
   exact h1.trans (div_le_div₀ (le_trans (div_nonneg (by exact_mod_cast h0) hs.le) hx.1) hx.1 hy_pos hy.2)
  .
   have hd:=divFl_le (a:=I.lo*fpS) (b:=J.lo) hJ
   have hne:(J.lo:R) ≠ 0:=by exact_mod_cast hJ.ne'
   have h1:((dF (I.lo*fpS) J.lo:ℤ):R)/S0<=((I.lo:R)/S0)/((J.lo:R)/S0):=by
    calc _ <= ((I.lo:R)*S0/(J.lo:R))/S0 :=
       dld (by simpa [Int.cast_mul] using hd) hs.le
     _ = ((I.lo:R)/S0)/((J.lo:R)/S0):=by field_simp
   have h2:((I.lo:R)/S0)/((J.lo:R)/S0)<=((I.lo:R)/S0)/y:=by
    rw [div_le_div_iff₀ hJlo_pos hy_pos]
    have:(I.lo:R)/S0<=0:=div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (by omega:I.lo<=0)) hs.le
    nlinarith [hy.1]
   exact h1.trans (h2.trans (dld hx.1 hy_pos.le))
 .
  unfold Iv.divPos;dsimp only
  split_ifs with h0
  .
   have hd:=le_divCe (a:=I.hi*fpS) (b:=J.lo) hJ
   have hne:(J.lo:R) ≠ 0:=by exact_mod_cast hJ.ne'
   have h1:((I.hi:R)/S0)/((J.lo:R)/S0)<=((dC (I.hi*fpS) J.lo:ℤ):R)/S0:=by
    calc _ = ((I.hi:R)*S0/(J.lo:R))/S0:=by field_simp
     _ <= _:=dld (by simpa [Int.cast_mul] using hd) hs.le
   exact (div_le_div₀ (div_nonneg (by exact_mod_cast h0) hs.le) hx.2 hJlo_pos hy.1).trans h1
  .
   have hd:=le_divCe (a:=I.hi*fpS) (b:=J.hi) hJhi_pos
   have hne:(J.hi:R) ≠ 0:=by exact_mod_cast hJhi_pos.ne'
   have h1:((I.hi:R)/S0)/((J.hi:R)/S0)<=((dC (I.hi*fpS) J.hi:ℤ):R)/S0:=by
    calc _ = ((I.hi:R)*S0/(J.hi:R))/S0:=by field_simp
     _ <= _:=dld (by simpa [Int.cast_mul] using hd) hs.le
   have h2:((I.hi:R)/S0)/y<=((I.hi:R)/S0)/((J.hi:R)/S0):=by
    rw [div_le_div_iff₀ hy_pos hJhi_posR]
    have:(I.hi:R)/S0<=0:=div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (by omega:I.hi<=0)) hs.le
    nlinarith [hy.2]
   exact ((dld hx.2 hy_pos.le).trans h2).trans h1
lemma Iv.mem.expNeg_mem {I:Iv} {x:R} (hx:I.mem x) (hI:I.hi<=0) :
  I.expNeg.mem (exp x):=by
 have hlo:I.lo<=0:=by
  have:(I.lo:R)/S0<=(I.hi:R)/S0:=hx.1.trans hx.2
  have:(I.lo:R)<=(I.hi:R):=(div_le_div_iff_of_pos_right fpS_pos).mp this
  have:I.lo<=I.hi:=by exact_mod_cast this
  omega
 exact ⟨(expNegLo_le hlo).trans (exp_le_exp.mpr hx.1),
     (exp_le_exp.mpr hx.2).trans (le_expNegHi hI)⟩
def cHC (r0 r1 t0 t1:ℤ) (Ph ph:Iv) (isPos:Bool):Bool :=
 let r:Iv:=⟨r0,r1⟩
 let u:Iv:=⟨fpS+r0,fpS+r1⟩
 let x:Iv:=⟨t0 - gI,t1 - gI⟩
 let inv2P:Iv:=⟨iP0,iP1⟩
 let Ph2:=Ph.sq
 let r2:=r.sq
 let p:=if isPos then inv2P.mul (r.add ((Iv.pt 6000000).mul (r2.mul r))) else inv2P.mul r
 let dp:=if isPos then inv2P.mul ((Iv.pt fpS).add ((Iv.pt 18000000).mul r2)) else inv2P
 let ddp:=if isPos then inv2P.mul ((Iv.pt 36000000).mul r) else Iv.pt 0
 let x2:=x.sq
 let x2u:=x2.divPos u
 let E:=x2u.neg.expNeg
 let u2:=u.sq
 let Er:=E.mul (x2.divPos u2)
 let twoXU:=x.scale2.divPos u
 let Et:=E.mul twoXU.neg
 let Err:=Er.mul ((x2u.sub (Iv.pt (2*fpS))).divPos u)
 let Ett:=E.mul (twoXU.sq.sub ((Iv.pt (2*fpS)).divPos u))
 let Ert:=Et.mul ((x2u.sub (Iv.pt fpS)).divPos u)
 let B:=Ph2.add (p.mul E)
 if B.lo<=0 then false else
 let Br:=(dp.mul E).add (p.mul Er)
 let Brr:=((ddp.mul E).add (dp.mul Er).scale2).add (p.mul Err)
 let ph2:=ph.sq
 let Phph:=Ph.mul ph
 let Bt:=Phph.scale2.add (p.mul Et)
 let Btt:=(ph2.scale2.sub (x.mul Phph).scale2).add (p.mul Ett)
 let Brt:=(dp.mul Et).add (p.mul Ert)
 let BrB:=Br.divPos B
 let BtB:=Bt.divPos B
 let BrrB:=Brr.divPos B
 let BttB:=Btt.divPos B
 let BrtB:=Brt.divPos B
 let halfU:=u.half
 let Qrr:=((BrB.add (halfU.mul (BrrB.sub BrB.sq))).sub ((Iv.pt fpS).divPos u.scale2)).sub
  ((Iv.pt (6*bInt)).mul r)
 let Qtt:=(Iv.pt (-fpS)).add (halfU.mul (BttB.sub BtB.sq))
 let Qrt:=BtB.half.add (halfU.mul (BrtB.sub (BrB.mul BtB)))
 if 0<=Qrr.hi || 0<=Qtt.hi then false else
 let qrrM:=-Qrr.hi
 let qttM:=-Qtt.hi
 let qrtM:=max (Int.natAbs Qrt.lo:ℤ) (Int.natAbs Qrt.hi:ℤ)
 decide (qrtM*qrtM < qrrM*qttM)
def checkHessRow (t0 t1:ℤ) (Ph ph:Iv) (isPos:Bool):ℕ->Bool
 | 0=>true
 | ir+1 =>
  let rStart:ℤ:=if isPos then 0 else -1500000
  let r0:=rStart+(ir:ℤ)*100000
  cHC r0 (r0+100000) t0 t1 Ph ph isPos && checkHessRow t0 t1 Ph ph isPos ir
def checkHessGrid:ℕ->Bool
 | 0=>true
 | it+1 =>
  let t0:ℤ:=3500000+(it:ℤ)*175000
  let t1:=t0+175000
  let Ph:Iv:=⟨cL (t0 - gI),cH (t1 - gI)⟩
  let ph:Iv:=⟨pL (t1 - gI),pH (t0 - gI)⟩
  checkHessRow t0 t1 Ph ph true 15 && checkHessRow t0 t1 Ph ph false 15 && checkHessGrid it
set_option maxHeartbeats 800000 in
lemma inner_hess_cert:checkHessGrid 20=true:=by decide
noncomputable def pBranch (isPos:Bool) (ρ:R):R :=
 if isPos then (2*PI)⁻¹*(ρ+(3/5)*ρ^3) else (2*PI)⁻¹*ρ
noncomputable def dpBranch (isPos:Bool) (ρ:R):R :=
 if isPos then (2*PI)⁻¹*(1+(9/5)*ρ^2) else (2*PI)⁻¹
noncomputable def ddpBranch (isPos:Bool) (ρ:R):R :=
 if isPos then (2*PI)⁻¹*((18/5)*ρ) else 0
noncomputable def BBranch (isPos:Bool) (ρ t:R):R :=
 (pC (t - gC))^2+pBranch isPos ρ*exp (-(t - gC)^2/(1+ρ))
noncomputable def QBranch (isPos:Bool) (ρ t:R):R :=
 -t^2/2+((1+ρ)/2)*log (BBranch isPos ρ t) - ((1+ρ)/2)*log (1+ρ) -
  (gStar+aConst*ρ+bConst*ρ^3)
noncomputable def hessCoeffs (isPos:Bool) (ρ t:R):R × R × R :=
 let u:=1+ρ
 let x:=t - gC
 let Ph:=pC x
 let ph:=pP x
 let p:=pBranch isPos ρ
 let dp:=dpBranch isPos ρ
 let ddp:=ddpBranch isPos ρ
 let E:=exp (-x^2/u)
 let Er:=E*(x^2/u^2)
 let Et:=E*(-(2*x/u))
 let Err:=Er*((x^2/u - 2)/u)
 let Ett:=E*((2*x/u)^2 - 2/u)
 let Ert:=Et*((x^2/u - 1)/u)
 let B:=Ph^2+p*E
 let Br:=dp*E+p*Er
 let Brr:=ddp*E+2*(dp*Er)+p*Err
 let Bt:=2*(Ph*ph)+p*Et
 let Btt:=(2*ph^2 - 2*(x*(Ph*ph)))+p*Ett
 let Brt:=dp*Et+p*Ert
 let BrB:=Br/B;let BtB:=Bt/B
 let BrrB:=Brr/B;let BttB:=Btt/B;let BrtB:=Brt/B
 let Qrr:=BrB+(u/2)*(BrrB - BrB^2) - 1/(2*u) - 6*bConst*ρ
 let Qtt:=-1+(u/2)*(BttB - BtB^2)
 let Qrt:=BtB/2+(u/2)*(BrtB - BrB*BtB)
 (Qrr,Qtt,Qrt)
lemma cHs {r0 r1 t0 t1:ℤ} {Ph ph:Iv} {isPos:Bool} {ρ t:R}
  (hr0:-fpS/2<=r0) (hr:(Iv.mk r0 r1).mem ρ) (ht:(Iv.mk t0 t1).mem t)
  (hPh:Ph.mem (pC (t - gC))) (hph:ph.mem (pP (t - gC)))
  (hchk:cHC r0 r1 t0 t1 Ph ph isPos=true) :
  0 < BBranch isPos ρ t /\
  (hessCoeffs isPos ρ t).1 < 0/\(hessCoeffs isPos ρ t).2.1 < 0 /\
  (hessCoeffs isPos ρ t).2.2^2 < (hessCoeffs isPos ρ t).1*(hessCoeffs isPos ρ t).2.1:=by
 have hs:(0:R) < S0:=fpS_pos
 have hgam:gC=(gI:R)/S0:=by norm_num [gC,gI,S0,fpS]
 have hinv2P:(Iv.mk iP0 iP1).mem (2*PI)⁻¹:=⟨pi_bounds_inv2Pi.1,pi_bounds_inv2Pi.2⟩
 set rI:Iv:=⟨r0,r1⟩
 set uI:Iv:=⟨fpS+r0,fpS+r1⟩
 set xI:Iv:=⟨t0 - gI,t1 - gI⟩
 set inv2P:Iv:=⟨iP0,iP1⟩
 have hu:uI.mem (1+ρ):=by
  constructor <;> simp only [uI,Int.cast_add,add_div,div_self hs.ne'] <;> linarith [hr.1,hr.2]
 have hx:xI.mem (t - gC):=by
  constructor <;> simp only [xI,Int.cast_sub,sub_div] <;> linarith [ht.1,ht.2,hgam]
 have hr01:r0<=r1:=by
  have:(r0:R)/S0<=(r1:R)/S0:=hr.1.trans hr.2
  have:(r0:R)<=(r1:R):=(div_le_div_iff_of_pos_right hs).mp this
  exact_mod_cast this
 have hu_pos:0 < uI.lo:=by dsimp [uI];norm_num [S0,fpS] at hr0 ⊢;omega
 have hu2_pos:0 < uI.sq.lo:=by
  unfold Iv.sq;dsimp only [uI];rw [if_neg (by norm_num [S0,fpS] at hr0 ⊢;omega)]
  have h1:(fpS+r0)*(fpS+r0)<=(fpS+r1)*(fpS+r1) :=
   mul_self_le_mul_self (by norm_num [S0,fpS] at hr0 ⊢;omega) (by omega)
  rw [min_eq_left h1]
  have hge:fpS<=(fpS+r0)*(fpS+r0):=by
   have h5:(5000000:ℤ)<=fpS+r0:=by norm_num [S0,fpS] at hr0 ⊢;omega
   have hsq:(5000000:ℤ)*5000000<=(fpS+r0)*(fpS+r0):=mul_self_le_mul_self (by norm_num) h5
   norm_num [S0,fpS] at hsq ⊢;linarith
  have hdiv:1<=((fpS+r0)*(fpS+r0))/fpS:=by
   have:=Int.ediv_le_ediv (by norm_num [S0,fpS]:(0:ℤ) < fpS) hge
   rwa [Int.ediv_self (by norm_num [S0,fpS])] at this
  unfold dF;exact Int.lt_of_lt_of_le (by norm_num) hdiv
 have hPh2:Ph.sq.mem ((pC (t - gC))^2):=hPh.sq_mem
 have hr2:rI.sq.mem (ρ^2):=hr.sq_mem
 have hp:(if isPos then inv2P.mul (rI.add ((Iv.pt 6000000).mul (rI.sq.mul rI))) else inv2P.mul rI).mem (pBranch isPos ρ):=by
  cases isPos <;> simp only [pBranch,↓reduceIte,Bool.false_eq_true]
  . exact hinv2P.mul_mem hr
  .
   have h35:(Iv.pt 6000000).mem (3/5:R):=by
    rw [show (3/5:R)=((6000000:ℤ):R)/S0 by norm_num [S0,fpS]];exact Iv.pt_mem 6000000
   have hr3:(rI.sq.mul rI).mem (ρ^3):=by simpa [pow_succ] using hr2.mul_mem hr
   exact hinv2P.mul_mem (hr.add_mem (h35.mul_mem hr3))
 have hdp:(if isPos then inv2P.mul ((Iv.pt fpS).add ((Iv.pt 18000000).mul rI.sq)) else inv2P).mem (dpBranch isPos ρ):=by
  cases isPos <;> simp only [dpBranch,↓reduceIte,Bool.false_eq_true]
  . exact hinv2P
  .
   have h1:(Iv.pt fpS).mem (1:R):=by
    rw [show (1:R)=((fpS:ℤ):R)/S0 by norm_num [S0,fpS]];exact Iv.pt_mem fpS
   have h95:(Iv.pt 18000000).mem (9/5:R):=by
    rw [show (9/5:R)=((18000000:ℤ):R)/S0 by norm_num [S0,fpS]];exact Iv.pt_mem 18000000
   exact hinv2P.mul_mem (h1.add_mem (h95.mul_mem hr2))
 have hddp:(if isPos then inv2P.mul ((Iv.pt 36000000).mul rI) else Iv.pt 0).mem (ddpBranch isPos ρ):=by
  cases isPos <;> simp only [ddpBranch,↓reduceIte,Bool.false_eq_true]
  . rw [show (0:R)=((0:ℤ):R)/S0 by norm_num];exact Iv.pt_mem 0
  .
   have h185:(Iv.pt 36000000).mem (18/5:R):=by
    rw [show (18/5:R)=((36000000:ℤ):R)/S0 by norm_num [S0,fpS]];exact Iv.pt_mem 36000000
   exact hinv2P.mul_mem (h185.mul_mem hr)
 set pI:=if isPos then inv2P.mul (rI.add ((Iv.pt 6000000).mul (rI.sq.mul rI))) else inv2P.mul rI
 set dpI:=if isPos then inv2P.mul ((Iv.pt fpS).add ((Iv.pt 18000000).mul rI.sq)) else inv2P
 set ddpI:=if isPos then inv2P.mul ((Iv.pt 36000000).mul rI) else Iv.pt 0
 set x2I:=xI.sq
 set x2uI:=x2I.divPos uI
 set EI:=x2uI.neg.expNeg
 have hx2:x2I.mem ((t - gC)^2):=hx.sq_mem
 have hx2u:x2uI.mem ((t - gC)^2/(1+ρ)):=hx2.divPos_mem hu hu_pos
 have hx2_lo_nn:0<=x2I.lo:=by
  unfold x2I Iv.sq;split_ifs
  . exact le_rfl
  . exact Int.ediv_nonneg (le_min (mul_self_nonneg _) (mul_self_nonneg _)) (by norm_num [S0,fpS])
 have hx2u_lo_nn:0<=x2uI.lo:=by
  unfold x2uI Iv.divPos;dsimp only;rw [if_pos hx2_lo_nn]
  exact Int.ediv_nonneg (mul_nonneg hx2_lo_nn (by norm_num [S0,fpS])) (by dsimp [uI];norm_num [S0,fpS] at hr0 ⊢;omega)
 have hE:EI.mem (exp (-(t - gC)^2/(1+ρ))):=by
  have h1:=hx2u.neg_mem.expNeg_mem (by dsimp [Iv.neg];omega)
  simpa [neg_div] using h1
 set u2I:=uI.sq
 set ErI:=EI.mul (x2I.divPos u2I)
 set twoXUI:=xI.scale2.divPos uI
 set EtI:=EI.mul twoXUI.neg
 set ErrI:=ErI.mul ((x2uI.sub (Iv.pt (2*fpS))).divPos uI)
 set EttI:=EI.mul (twoXUI.sq.sub ((Iv.pt (2*fpS)).divPos uI))
 set ErtI:=EtI.mul ((x2uI.sub (Iv.pt fpS)).divPos uI)
 have hu2:u2I.mem ((1+ρ)^2):=hu.sq_mem
 have hEr:ErI.mem (exp (-(t - gC)^2/(1+ρ))*((t - gC)^2/(1+ρ)^2)) :=
  hE.mul_mem (hx2.divPos_mem hu2 hu2_pos)
 have htwoXU:twoXUI.mem (2*(t - gC)/(1+ρ)):=hx.scale2_mem.divPos_mem hu hu_pos
 have hEt:EtI.mem (exp (-(t - gC)^2/(1+ρ)) * -(2*(t - gC)/(1+ρ))) :=
  hE.mul_mem htwoXU.neg_mem
 have hpt1:(Iv.pt fpS).mem (1:R):=by
  rw [show (1:R)=((fpS:ℤ):R)/S0 by norm_num [S0,fpS]];exact Iv.pt_mem fpS
 have hpt2:(Iv.pt (2*fpS)).mem (2:R):=by
  rw [show (2:R)=((2*fpS:ℤ):R)/S0 by norm_num [S0,fpS]];exact Iv.pt_mem (2*fpS)
 have hErr:ErrI.mem ((exp (-(t - gC)^2/(1+ρ))*((t - gC)^2/(1+ρ)^2)) *
   (((t - gC)^2/(1+ρ) - 2)/(1+ρ))) :=
  hEr.mul_mem ((hx2u.sub_mem hpt2).divPos_mem hu hu_pos)
 have hEtt:EttI.mem (exp (-(t - gC)^2/(1+ρ)) *
   ((2*(t - gC)/(1+ρ))^2 - 2/(1+ρ))) :=
  hE.mul_mem (htwoXU.sq_mem.sub_mem (hpt2.divPos_mem hu hu_pos))
 have hErt:ErtI.mem ((exp (-(t - gC)^2/(1+ρ)) * -(2*(t - gC)/(1+ρ))) *
   (((t - gC)^2/(1+ρ) - 1)/(1+ρ))) :=
  hEt.mul_mem ((hx2u.sub_mem hpt1).divPos_mem hu hu_pos)
 set BI:=Ph.sq.add (pI.mul EI)
 have hB:BI.mem (BBranch isPos ρ t):=hPh2.add_mem (hp.mul_mem hE)
 unfold cHC at hchk
 dsimp only at hchk
 by_cases hBlo:BI.lo<=0
 . rw [if_pos hBlo] at hchk;exact absurd hchk (by decide)
 rw [if_neg hBlo] at hchk
 have hB_lo_pos:0 < BI.lo:=by omega
 have hB_pos:0 < BBranch isPos ρ t:=lt_of_lt_of_le (div_pos (by exact_mod_cast hB_lo_pos) hs) hB.1
 set BrI:=(dpI.mul EI).add (pI.mul ErI)
 set BrrI:=((ddpI.mul EI).add (dpI.mul ErI).scale2).add (pI.mul ErrI)
 set ph2I:=ph.sq
 set PhphI:=Ph.mul ph
 set BtI:=PhphI.scale2.add (pI.mul EtI)
 set BttI:=(ph2I.scale2.sub (xI.mul PhphI).scale2).add (pI.mul EttI)
 set BrtI:=(dpI.mul EtI).add (pI.mul ErtI)
 set BrBI:=BrI.divPos BI
 set BtBI:=BtI.divPos BI
 set BrrBI:=BrrI.divPos BI
 set BttBI:=BttI.divPos BI
 set BrtBI:=BrtI.divPos BI
 set halfUI:=uI.half
 set QrrI:=((BrBI.add (halfUI.mul (BrrBI.sub BrBI.sq))).sub ((Iv.pt fpS).divPos uI.scale2)).sub
  ((Iv.pt (6*bInt)).mul rI)
 set QttI:=(Iv.pt (-fpS)).add (halfUI.mul (BttBI.sub BtBI.sq))
 set QrtI:=BtBI.half.add (halfUI.mul (BrtBI.sub (BrBI.mul BtBI)))
 have hBr:BrI.mem (dpBranch isPos ρ*exp (-(t - gC)^2/(1+ρ)) +
   pBranch isPos ρ*(exp (-(t - gC)^2/(1+ρ))*((t - gC)^2/(1+ρ)^2))) :=
  (hdp.mul_mem hE).add_mem (hp.mul_mem hEr)
 have hBrr:BrrI.mem (ddpBranch isPos ρ*exp (-(t - gC)^2/(1+ρ)) +
   2*(dpBranch isPos ρ*(exp (-(t - gC)^2/(1+ρ))*((t - gC)^2/(1+ρ)^2))) +
   pBranch isPos ρ*((exp (-(t - gC)^2/(1+ρ))*((t - gC)^2/(1+ρ)^2)) *
    (((t - gC)^2/(1+ρ) - 2)/(1+ρ)))) :=
  ((hddp.mul_mem hE).add_mem (hdp.mul_mem hEr).scale2_mem).add_mem (hp.mul_mem hErr)
 have hBt:BtI.mem (2*(pC (t - gC)*pP (t - gC)) +
   pBranch isPos ρ*(exp (-(t - gC)^2/(1+ρ)) * -(2*(t - gC)/(1+ρ)))) :=
  (hPh.mul_mem hph).scale2_mem.add_mem (hp.mul_mem hEt)
 have hBtt:BttI.mem ((2*(pP (t - gC))^2 -
   2*((t - gC)*(pC (t - gC)*pP (t - gC)))) +
   pBranch isPos ρ*(exp (-(t - gC)^2/(1+ρ)) *
    ((2*(t - gC)/(1+ρ))^2 - 2/(1+ρ)))) :=
  (hph.sq_mem.scale2_mem.sub_mem (hx.mul_mem (hPh.mul_mem hph)).scale2_mem).add_mem (hp.mul_mem hEtt)
 have hBrt:BrtI.mem (dpBranch isPos ρ*(exp (-(t - gC)^2/(1+ρ)) * -(2*(t - gC)/(1+ρ))) +
   pBranch isPos ρ*((exp (-(t - gC)^2/(1+ρ)) * -(2*(t - gC)/(1+ρ))) *
    (((t - gC)^2/(1+ρ) - 1)/(1+ρ)))) :=
  (hdp.mul_mem hEt).add_mem (hp.mul_mem hErt)
 have hBrB:=hBr.divPos_mem hB hB_lo_pos
 have hBtB:=hBt.divPos_mem hB hB_lo_pos
 have hBrrB:=hBrr.divPos_mem hB hB_lo_pos
 have hBttB:=hBtt.divPos_mem hB hB_lo_pos
 have hBrtB:=hBrt.divPos_mem hB hB_lo_pos
 have hhalfU:=hu.half_mem
 have h6b:(Iv.pt (6*bInt)).mem (6*bConst):=by
  rw [show 6*bConst=((6*bInt:ℤ):R)/S0 by norm_num [bConst,bInt,S0,fpS]];exact Iv.pt_mem (6*bInt)
 have hneg1:(Iv.pt (-fpS)).mem (-1:R):=by
  rw [show (-1:R)=((-fpS:ℤ):R)/S0 by norm_num [S0,fpS]];exact Iv.pt_mem (-fpS)
 have hQrr:QrrI.mem (hessCoeffs isPos ρ t).1:=by
  exact ((hBrB.add_mem (hhalfU.mul_mem (hBrrB.sub_mem hBrB.sq_mem))).sub_mem
   (hpt1.divPos_mem hu.scale2_mem (by dsimp [Iv.scale2,uI];norm_num [S0,fpS] at hr0 ⊢;omega))).sub_mem (h6b.mul_mem hr)
 have hQtt:QttI.mem (hessCoeffs isPos ρ t).2.1:=by
  exact hneg1.add_mem (hhalfU.mul_mem (hBttB.sub_mem hBtB.sq_mem))
 have hQrt:QrtI.mem (hessCoeffs isPos ρ t).2.2:=by
  exact hBtB.half_mem.add_mem (hhalfU.mul_mem (hBrtB.sub_mem (hBrB.mul_mem hBtB)))
 by_cases hsign:(decide (0<=QrrI.hi) || decide (0<=QttI.hi))=true
 . rw [if_pos hsign] at hchk;exact absurd hchk (by decide)
 rw [if_neg hsign] at hchk
 have hQrr_neg:QrrI.hi < 0:=by
  by_contra h;push Not at h
  have:(decide (0<=QrrI.hi) || decide (0<=QttI.hi))=true:=by simp [h]
  exact hsign this
 have hQtt_neg:QttI.hi < 0:=by
  by_contra h;push Not at h
  have:(decide (0<=QrrI.hi) || decide (0<=QttI.hi))=true:=by simp [h]
  exact hsign this
 have hdet_int:(max (Int.natAbs QrtI.lo:ℤ) (Int.natAbs QrtI.hi:ℤ)) *
   (max (Int.natAbs QrtI.lo:ℤ) (Int.natAbs QrtI.hi:ℤ)) < (-QrrI.hi)*(-QttI.hi) :=
  of_decide_eq_true hchk
 have hQrr_lt:(hessCoeffs isPos ρ t).1 < 0 :=
  lt_of_le_of_lt hQrr.2 (div_neg_of_neg_of_pos (by exact_mod_cast hQrr_neg) hs)
 have hQtt_lt:(hessCoeffs isPos ρ t).2.1 < 0 :=
  lt_of_le_of_lt hQtt.2 (div_neg_of_neg_of_pos (by exact_mod_cast hQtt_neg) hs)
 have hQrt_abs:|(hessCoeffs isPos ρ t).2.2| <=
   ((max (Int.natAbs QrtI.lo:ℤ) (Int.natAbs QrtI.hi:ℤ):ℤ):R)/S0:=by
  rw [abs_le]
  set m:ℤ:=max (Int.natAbs QrtI.lo:ℤ) (Int.natAbs QrtI.hi:ℤ)
  have h1:-m<=QrtI.lo:=by
   have:(Int.natAbs QrtI.lo:ℤ)<=m:=le_max_left _ _
   have:-(Int.natAbs QrtI.lo:ℤ)<=QrtI.lo:=by cases Int.natAbs_eq QrtI.lo <;> omega
   omega
  have h2:QrtI.hi<=m:=by
   have:(Int.natAbs QrtI.hi:ℤ)<=m:=le_max_right _ _
   have:QrtI.hi<=(Int.natAbs QrtI.hi:ℤ):=Int.le_natAbs
   omega
  exact ⟨le_trans (by rw [← neg_div];exact dld (by exact_mod_cast h1) hs.le) hQrt.1,
      le_trans hQrt.2 (dld (by exact_mod_cast h2) hs.le)⟩
 have hdet_r:(hessCoeffs isPos ρ t).2.2^2 < (hessCoeffs isPos ρ t).1*(hessCoeffs isPos ρ t).2.1:=by
  set m:ℤ:=max (Int.natAbs QrtI.lo:ℤ) (Int.natAbs QrtI.hi:ℤ)
  have hm_nn:0<=m:=le_trans (Int.natCast_nonneg _) (le_max_left _ _)
  have h1:(hessCoeffs isPos ρ t).2.2^2<=((m:R)/S0)^2:=by
   rw [← sq_abs]
   exact pow_le_pow_left₀ (abs_nonneg _) hQrt_abs 2
  have h2:((m:R)/S0)^2 < ((-QrrI.hi:R)/S0)*((-QttI.hi:R)/S0):=by
   have hcast:((m:R)*(m:R)) < ((-QrrI.hi:R)*(-QttI.hi:R)):=by
    have:(m*m:ℤ) < (-QrrI.hi)*(-QttI.hi):=hdet_int
    exact_mod_cast this
   have hs2:0 < S0^2:=sq_pos_of_pos hs
   calc ((m:R)/S0)^2=((m:R)*(m:R))/S0^2:=by ring
    _ < ((-QrrI.hi:R)*(-QttI.hi:R))/S0^2:=div_lt_div_of_pos_right hcast hs2
    _ = ((-QrrI.hi:R)/S0)*((-QttI.hi:R)/S0):=by ring
  have h3:((-QrrI.hi:R)/S0) <= -(hessCoeffs isPos ρ t).1:=by
   have:=hQrr.2;rw [neg_div];linarith
  have h4:((-QttI.hi:R)/S0) <= -(hessCoeffs isPos ρ t).2.1:=by
   have:=hQtt.2;rw [neg_div];linarith
  have h5:((-QrrI.hi:R)/S0)*((-QttI.hi:R)/S0) <=
    (-(hessCoeffs isPos ρ t).1)*(-(hessCoeffs isPos ρ t).2.1) :=
   mul_le_mul h3 h4 (div_nonneg (by exact_mod_cast (by omega:0 <= -QttI.hi)) hs.le) (by linarith)
  nlinarith
 exact ⟨hB_pos,hQrr_lt,hQtt_lt,hdet_r⟩
lemma checkHessRow_get {t0 t1:ℤ} {Ph ph:Iv} {isPos:Bool} :
  ∀ (n ir:ℕ),ir < n->checkHessRow t0 t1 Ph ph isPos n=true ->
   let rStart:ℤ:=if isPos then 0 else -1500000
   let r0:=rStart+(ir:ℤ)*100000
   cHC r0 (r0+100000) t0 t1 Ph ph isPos=true:=by
 intro n
 induction n with
 | zero=>intro ir hir;omega
 | succ k ih =>
  intro ir hir hchk
  unfold checkHessRow at hchk
  rw [Bool.and_eq_true] at hchk
  by_cases heq:ir=k
  . subst heq;exact hchk.1
  . exact ih ir (by omega) hchk.2
lemma checkHessGrid_get:∀ (n it:ℕ),it < n->checkHessGrid n=true ->
  let t0:ℤ:=3500000+(it:ℤ)*175000
  let t1:=t0+175000
  let Ph:Iv:=⟨cL (t0 - gI),cH (t1 - gI)⟩
  let ph:Iv:=⟨pL (t1 - gI),pH (t0 - gI)⟩
  checkHessRow t0 t1 Ph ph true 15=true/\checkHessRow t0 t1 Ph ph false 15=true:=by
 intro n
 induction n with
 | zero=>intro it hit;omega
 | succ k ih =>
  intro it hit hchk
  unfold checkHessGrid at hchk
  rw [Bool.and_eq_true,Bool.and_eq_true] at hchk
  by_cases heq:it=k
  . subst heq;exact hchk.1
  . exact ih it (by omega) hchk.2
lemma inner_hess_negdef {isPos:Bool} {ρ t:R}
  (hρ:if isPos then 0<=ρ/\ρ<=15/100 else -15/100<=ρ/\ρ<=0)
  (ht0:35/100<=t) (ht1:t<=70/100) :
  0 < BBranch isPos ρ t /\
  (hessCoeffs isPos ρ t).1 < 0/\(hessCoeffs isPos ρ t).2.1 < 0 /\
  (hessCoeffs isPos ρ t).2.2^2 < (hessCoeffs isPos ρ t).1*(hessCoeffs isPos ρ t).2.1:=by
 have hs:(0:R) < S0:=fpS_pos
 set it:ℕ:=min 19 (Int.toNat ⌊(t - 35/100)/(175/10000)⌋)
 have hit_lt:it < 20:=by omega
 set t0:ℤ:=3500000+(it:ℤ)*175000
 set t1:ℤ:=t0+175000
 have ht_mem:(Iv.mk t0 t1).mem t:=by
  set q:R:=(t - 35/100)/(175/10000)
  have hq_nn:0<=q:=div_nonneg (by linarith) (by norm_num)
  have hq_le:q<=20:=by
   have:t - 35/100<=35/100:=by linarith
   unfold q;linarith
  have hfl_nn:0<=⌊q⌋:=Int.floor_nonneg.mpr hq_nn
  have hfl_r:(⌊q⌋:R)<=q/\q < (⌊q⌋:R)+1:=⟨Int.floor_le q,Int.lt_floor_add_one q⟩
  have hit_cast:(it:R)=min 19 (⌊q⌋:R):=by
   unfold it
   have htn:((Int.toNat ⌊q⌋:ℕ):R)=(⌊q⌋:R):=by
    exact_mod_cast Int.toNat_of_nonneg hfl_nn
   by_cases h19:Int.toNat ⌊q⌋<=19
   . rw [min_eq_right h19,htn,min_eq_right (by rw [← htn];exact_mod_cast h19)]
   .
    have hge:19<=Int.toNat ⌊q⌋:=by omega
    rw [min_eq_left hge,min_eq_left (by rw [← htn];exact_mod_cast hge)];norm_num
  have hit_lo:(it:R)<=q:=by rw [hit_cast];exact (min_le_right _ _).trans hfl_r.1
  have hit_hi:q<=(it:R)+1:=by
   by_cases h19:(⌊q⌋:R)<=19
   . rw [hit_cast,min_eq_right h19];linarith [hfl_r.2]
   . rw [hit_cast,min_eq_left (le_of_not_ge h19)];linarith
  constructor <;> simp only [t0,t1,Int.cast_add,Int.cast_mul,Int.cast_natCast,add_div,mul_div_assoc]
  . norm_num [S0,fpS];unfold q at hit_lo;linarith
  . norm_num [S0,fpS];unfold q at hit_hi;linarith
 set rStart:ℤ:=if isPos then 0 else -1500000
 set rStartR:R:=if isPos then 0 else -15/100
 have hρ_range:rStartR<=ρ/\ρ<=rStartR+15/100:=by
  cases isPos <;> simp only [rStartR,↓reduceIte,Bool.false_eq_true] at hρ ⊢ <;> constructor <;> linarith [hρ.1,hρ.2]
 set ir:ℕ:=min 14 (Int.toNat ⌊(ρ - rStartR)/(1/100)⌋)
 have hir_lt:ir < 15:=by omega
 set r0:ℤ:=rStart+(ir:ℤ)*100000
 set r1:ℤ:=r0+100000
 have hr_mem:(Iv.mk r0 r1).mem ρ:=by
  set q:R:=(ρ - rStartR)/(1/100)
  have hq_nn:0<=q:=div_nonneg (by linarith [hρ_range.1]) (by norm_num)
  have hq_le:q<=15:=by unfold q;linarith [hρ_range.2]
  have hfl_nn:0<=⌊q⌋:=Int.floor_nonneg.mpr hq_nn
  have hfl_r:(⌊q⌋:R)<=q/\q < (⌊q⌋:R)+1:=⟨Int.floor_le q,Int.lt_floor_add_one q⟩
  have hir_cast:(ir:R)=min 14 (⌊q⌋:R):=by
   unfold ir
   have htn:((Int.toNat ⌊q⌋:ℕ):R)=(⌊q⌋:R):=by
    exact_mod_cast Int.toNat_of_nonneg hfl_nn
   by_cases h14:Int.toNat ⌊q⌋<=14
   . rw [min_eq_right h14,htn,min_eq_right (by rw [← htn];exact_mod_cast h14)]
   .
    have hge:14<=Int.toNat ⌊q⌋:=by omega
    rw [min_eq_left hge,min_eq_left (by rw [← htn];exact_mod_cast hge)];norm_num
  have hir_lo:(ir:R)<=q:=by rw [hir_cast];exact (min_le_right _ _).trans hfl_r.1
  have hir_hi:q<=(ir:R)+1:=by
   by_cases h14:(⌊q⌋:R)<=14
   . rw [hir_cast,min_eq_right h14];linarith [hfl_r.2]
   . rw [hir_cast,min_eq_left (le_of_not_ge h14)];linarith
  have hrs:(rStart:R)/S0=rStartR:=by
   cases isPos <;> norm_num [rStart,rStartR,S0,fpS]
  constructor <;> simp only [r0,r1,Int.cast_add,Int.cast_mul,Int.cast_natCast,add_div,mul_div_assoc]
  . rw [hrs];norm_num [S0,fpS];unfold q at hir_lo;linarith
  . rw [hrs];norm_num [S0,fpS];unfold q at hir_hi;linarith
 have hgam:gC=(gI:R)/S0:=by norm_num [gC,gI,S0,fpS]
 have hx_lo:((t0 - gI:ℤ):R)/S0<=t - gC:=by
  rw [hgam,Int.cast_sub,sub_div];linarith [ht_mem.1]
 have hx_hi:t - gC<=((t1 - gI:ℤ):R)/S0:=by
  rw [hgam,Int.cast_sub,sub_div];linarith [ht_mem.2]
 have hPh_mem:(Iv.mk (cL (t0 - gI)) (cH (t1 - gI))).mem (pC (t - gC)):=by
  generalize t0 - gI=z0 at hx_lo ⊢
  generalize t1 - gI=z1 at hx_hi ⊢
  exact ⟨(phiCDFLo_le z0).trans (pCm.monotone hx_lo),
      (pCm.monotone hx_hi).trans (le_phiCDFHi z1)⟩
 have hph_mem:(Iv.mk (pL (t1 - gI)) (pH (t0 - gI))).mem (pP (t - gC)):=by
  have h0_le:0<=((t0 - gI:ℤ):R)/S0:=by
   have:0<=t0 - gI:=by dsimp [t0];norm_num [gI];omega
   exact div_nonneg (by exact_mod_cast this) hs.le
  have hanti:∀ {a b:R},0<=a->a<=b->pP b<=pP a:=by
   intro a b ha hab
   unfold pP
   exact mlL (exp_le_exp.mpr (by nlinarith)) (by positivity)
  exact ⟨(phiPDFLo_le _).trans (hanti (h0_le.trans hx_lo) hx_hi),
      (hanti h0_le hx_lo).trans (le_phiPDFHi _)⟩
 have hrow:=checkHessGrid_get 20 it hit_lt inner_hess_cert
 have hcell:cHC r0 r1 t0 t1 ⟨cL (t0 - gI),cH (t1 - gI)⟩
   ⟨pL (t1 - gI),pH (t0 - gI)⟩ isPos=true:=by
  cases isPos
  . exact checkHessRow_get 15 ir hir_lt hrow.2
  . exact checkHessRow_get 15 ir hir_lt hrow.1
 have hr0_bd:-fpS/2<=r0:=by
  cases isPos <;> dsimp [r0,rStart] <;> norm_num [S0,fpS] <;> omega
 exact cHs hr0_bd hr_mem ht_mem hPh_mem hph_mem hcell
lemma ray_derivs (isPos:Bool) (ρ dt:R) {s:R}
  (hu_pos:0 < 1+s*ρ) (hB_pos:0 < BBranch isPos (s*ρ) (tStar+s*dt)) :
  let u:=1+s*ρ
  let x:=tStar+s*dt - gC
  let Ph:=pC x
  let ph:=pP x
  let p:=pBranch isPos (s*ρ)
  let dp:=dpBranch isPos (s*ρ)
  let E:=exp (-x^2/u)
  let Er:=E*(x^2/u^2)
  let Et:=E*(-(2*x/u))
  let B:=BBranch isPos (s*ρ) (tStar+s*dt)
  let Br:=dp*E+p*Er
  let Bt:=2*(Ph*ph)+p*Et
  let Q1 (z:R):R :=
   let uz:=1+z*ρ
   let xz:=tStar+z*dt - gC
   let Phz:=pC xz
   let phz:=pP xz
   let pz:=pBranch isPos (z*ρ)
   let dpz:=dpBranch isPos (z*ρ)
   let Ez:=exp (-xz^2/uz)
   let Erz:=Ez*(xz^2/uz^2)
   let Etz:=Ez*(-(2*xz/uz))
   let Bz:=BBranch isPos (z*ρ) (tStar+z*dt)
   let Brz:=dpz*Ez+pz*Erz
   let Btz:=2*(Phz*phz)+pz*Etz
   (-(tStar+z*dt)+(uz/2)*(Btz/Bz))*dt +
    ((1/2)*log Bz+(uz/2)*(Brz/Bz) - (1/2)*log uz - 1/2 -
     aConst - 3*bConst*(z*ρ)^2)*ρ
  HD (fun z=>QBranch isPos (z*ρ) (tStar+z*dt)) (Q1 s) s /\
  HD Q1
   ((hessCoeffs isPos (s*ρ) (tStar+s*dt)).1*ρ^2 +
    2*(hessCoeffs isPos (s*ρ) (tStar+s*dt)).2.2*ρ*dt +
    (hessCoeffs isPos (s*ρ) (tStar+s*dt)).2.1*dt^2) s:=by
 intro u x Ph ph p dp E Er Et B Br Bt Q1
 have hu_ne:u ≠ 0:=hu_pos.ne'
 have hB_ne:B ≠ 0:=hB_pos.ne'
 have hr_d:HD (fun z:R=>z*ρ) ρ s:=by
  simpa using (hdi s).mul_const ρ
 have hu_d:HD (fun z:R=>1+z*ρ) ρ s:=by
  simpa using (hasDerivAt_const s (1:R)).fun_add hr_d
 have ht_d:HD (fun z:R=>tStar+z*dt) dt s:=by
  simpa using (hasDerivAt_const s tStar).fun_add ((hdi s).mul_const dt)
 have hx_d:HD (fun z:R=>tStar+z*dt - gC) dt s:=by
  simpa using ht_d.sub_const gC
 have hp_d:HD (fun z=>pBranch isPos (z*ρ)) (dp*ρ) s:=by
  cases isPos <;> simp only [pBranch,dp,dpBranch,↓reduceIte,Bool.false_eq_true]
  . exact hr_d.const_mul (2*PI)⁻¹
  .
   have h3:=hr_d.fun_pow 3
   have h1:=(hr_d.fun_add (h3.const_mul (3/5))).const_mul (2*PI)⁻¹
   exact h1.congr_deriv (by ring)
 have hdp_d:HD (fun z=>dpBranch isPos (z*ρ)) (ddpBranch isPos (s*ρ)*ρ) s:=by
  cases isPos <;> simp only [dpBranch,ddpBranch,↓reduceIte,Bool.false_eq_true]
  . simpa using hasDerivAt_const s ((2*PI)⁻¹)
  .
   have h2:=hr_d.fun_pow 2
   have h1:=((hasDerivAt_const s (1:R)).fun_add (h2.const_mul (9/5))).const_mul (2*PI)⁻¹
   exact h1.congr_deriv (by ring)
 have hPh_d:HD (fun z=>pC (tStar+z*dt - gC)) (ph*dt) s :=
  hasDerivAt_comp_fun (pCd x) hx_d
 have hph_d:HD (fun z=>pP (tStar+z*dt - gC)) (-x*ph*dt) s :=
  hasDerivAt_comp_fun (stdPhiPDF_hasDerivAt x) hx_d
 have harg_d:HD (fun z=>-(tStar+z*dt - gC)^2/(1+z*ρ))
   (x^2/u^2*ρ+(-(2*x/u))*dt) s:=by
  have hnum:=(hx_d.fun_pow 2).fun_neg
  have hq:=hnum.fun_div hu_d hu_ne
  exact hq.congr_deriv (by field_simp [hu_ne];ring)
 have hE_d:HD (fun z=>exp (-(tStar+z*dt - gC)^2/(1+z*ρ)))
   (Er*ρ+Et*dt) s:=by
  have h1:=harg_d.exp
  exact h1.congr_deriv (by unfold Er Et;ring)
 have hEr_d:HD (fun z=>exp (-(tStar+z*dt - gC)^2/(1+z*ρ)) *
   ((tStar+z*dt - gC)^2/(1+z*ρ)^2))
   ((Er*((x^2/u - 2)/u))*ρ+(Et*((x^2/u - 1)/u))*dt) s:=by
  have hfrac:HD (fun z=>(tStar+z*dt - gC)^2/(1+z*ρ)^2)
    ((2*x/u^2)*dt - (2*x^2/u^3)*ρ) s:=by
   have hn:=hx_d.fun_pow 2
   have hd:=hu_d.fun_pow 2
   have hq:=hn.fun_div hd (pow_ne_zero 2 hu_ne)
   exact hq.congr_deriv (by field_simp [hu_ne];ring)
  have hm:=hE_d.fun_mul hfrac
  rwa [show (Er*ρ+Et*dt)*(x^2/u^2)+E*(2*x/u^2*dt - 2*x^2/u^3*ρ) =
   Er*((x^2/u - 2)/u)*ρ+Et*((x^2/u - 1)/u)*dt by
   unfold Er Et;field_simp;ring] at hm
 have hEt_d:HD (fun z=>exp (-(tStar+z*dt - gC)^2/(1+z*ρ)) *
   -(2*(tStar+z*dt - gC)/(1+z*ρ)))
   ((Et*((x^2/u - 1)/u))*ρ+(E*((2*x/u)^2 - 2/u))*dt) s:=by
  have hfrac:HD (fun z=>-(2*(tStar+z*dt - gC)/(1+z*ρ)))
    ((2*x/u^2)*ρ - (2/u)*dt) s:=by
   have hq:=(hx_d.const_mul 2).fun_div hu_d hu_ne
   have hn:=hq.fun_neg
   rwa [show -((2*dt*u - 2*x*ρ)/u^2)=2*x/u^2*ρ - 2/u*dt by field_simp;ring] at hn
  have hm:=hE_d.fun_mul hfrac
  rwa [show (Er*ρ+Et*dt) * -(2*x/u)+E*(2*x/u^2*ρ - 2/u*dt) =
   Et*((x^2/u - 1)/u)*ρ+E*((2*x/u)^2 - 2/u)*dt by
   unfold Er Et;field_simp;ring] at hm
 have hB_d:HD (fun z=>BBranch isPos (z*ρ) (tStar+z*dt)) (Br*ρ+Bt*dt) s:=by
  have h1:=hPh_d.fun_pow 2
  have h2:=hp_d.fun_mul hE_d
  have h3:=h1.fun_add h2
  exact h3.congr_deriv (by unfold Br Bt;ring)
 set Brr:=ddpBranch isPos (s*ρ)*E+2*(dp*Er)+p*(Er*((x^2/u - 2)/u))
 set Btt:=(2*ph^2 - 2*(x*(Ph*ph)))+p*(E*((2*x/u)^2 - 2/u))
 set Brt:=dp*Et+p*(Et*((x^2/u - 1)/u))
 have hBr_d:HD (fun z=>dpBranch isPos (z*ρ)*exp (-(tStar+z*dt - gC)^2/(1+z*ρ)) +
   pBranch isPos (z*ρ)*(exp (-(tStar+z*dt - gC)^2/(1+z*ρ)) *
    ((tStar+z*dt - gC)^2/(1+z*ρ)^2)))
   (Brr*ρ+Brt*dt) s:=by
  have h1:=(hdp_d.fun_mul hE_d).fun_add (hp_d.fun_mul hEr_d)
  rwa [show ddpBranch isPos (s*ρ)*ρ*E+dp*(Er*ρ+Et*dt) +
   (dp*ρ*Er+p*(Er*((x^2/u - 2)/u)*ρ+Et*((x^2/u - 1)/u)*dt)) =
   Brr*ρ+Brt*dt by unfold Brr Brt;ring] at h1
 have hBt_d:HD (fun z=>2*(pC (tStar+z*dt - gC)*pP (tStar+z*dt - gC)) +
   pBranch isPos (z*ρ)*(exp (-(tStar+z*dt - gC)^2/(1+z*ρ)) *
    -(2*(tStar+z*dt - gC)/(1+z*ρ))))
   (Brt*ρ+Btt*dt) s:=by
  have h1:=((hPh_d.fun_mul hph_d).const_mul 2).fun_add (hp_d.fun_mul hEt_d)
  rwa [show 2*(ph*dt*ph+Ph*(-x*ph*dt)) +
   (dp*ρ*Et+p*(Et*((x^2/u - 1)/u)*ρ+E*((2*x/u)^2 - 2/u)*dt)) =
   Brt*ρ+Btt*dt by unfold Brt Btt;ring] at h1
 have hQ0:HD (fun z=>QBranch isPos (z*ρ) (tStar+z*dt)) (Q1 s) s:=by
  unfold QBranch
  have ht2:=(ht_d.fun_pow 2).fun_neg.div_const 2
  have hlogB:=hB_d.log hB_ne
  have hlogU:=hu_d.log hu_ne
  have htermB:=(hu_d.div_const 2).fun_mul hlogB
  have htermU:=(hu_d.div_const 2).fun_mul hlogU
  have hlin:=((hasDerivAt_const s gStar).fun_add (hr_d.const_mul aConst)).fun_add
   ((hr_d.fun_pow 3).const_mul bConst)
  have hall:=((ht2.fun_add htermB).fun_sub htermU).fun_sub hlin
  refine hall.congr_deriv ?_
  change -(↑2*(tStar+s*dt)^(2 - 1)*dt)/2 +
    (ρ / 2*log B+u/2*((Br*ρ+Bt*dt)/B)) -
    (ρ / 2*log u+u/2*(ρ / u)) -
    (0+aConst*ρ+bConst*(↑3*(s*ρ)^(3 - 1)*ρ)) =
   (-(tStar+s*dt)+u/2*(Bt/B))*dt +
    (1/2*log B+u/2*(Br/B) - 1/2*log u - 1/2 - aConst - 3*bConst*(s*ρ)^2)*ρ
  field_simp [hu_ne,hB_ne]
  ring
 have hQ1:HD Q1
   ((hessCoeffs isPos (s*ρ) (tStar+s*dt)).1*ρ^2 +
    2*(hessCoeffs isPos (s*ρ) (tStar+s*dt)).2.2*ρ*dt +
    (hessCoeffs isPos (s*ρ) (tStar+s*dt)).2.1*dt^2) s:=by
  have hBtB_d:=hBt_d.fun_div hB_d hB_ne
  have hBrB_d:=hBr_d.fun_div hB_d hB_ne
  have hlogB:=hB_d.log hB_ne
  have hlogU:=hu_d.log hu_ne
  have hpart1:=(ht_d.fun_neg.fun_add ((hu_d.div_const 2).fun_mul hBtB_d)).mul_const dt
  have hpart2:=(((((hlogB.const_mul (1/2)).fun_add ((hu_d.div_const 2).fun_mul hBrB_d)).fun_sub
   (hlogU.const_mul (1/2))).sub_const (1/2)).sub_const aConst |>.fun_sub
   ((hr_d.fun_pow 2).const_mul (3*bConst))).mul_const ρ
  have hall:=hpart1.fun_add hpart2
  refine hall.congr_deriv ?_
  change (-dt+(ρ / 2*(Bt/B)+u/2*(((Brt*ρ+Btt*dt)*B - Bt*(Br*ρ+Bt*dt))/B^2)))*dt +
    ((1/2*((Br*ρ+Bt*dt)/B) +
     (ρ / 2*(Br/B)+u/2*(((Brr*ρ+Brt*dt)*B - Br*(Br*ρ+Bt*dt))/B^2)) -
     1/2*(ρ / u)) - 3*bConst*((↑2:R)*(s*ρ)^(2 - 1)*ρ))*ρ =
   (Br/B+u/2*(Brr/B - (Br/B)^2) - 1/(2*u) - 6*bConst*(s*ρ))*ρ^2 +
    2*(Bt/B/2+u/2*(Brt/B - (Br/B)*(Bt/B)))*ρ*dt +
    (-1+u/2*(Btt/B - (Bt/B)^2))*dt^2
  field_simp [hu_ne,hB_ne]
  ring
 exact ⟨hQ0,hQ1⟩
lemma inner_box_sound {ρ t:R} (hρ_lo:-15/100<=ρ) (hρ_hi:ρ<=15/100)
  (ht_lo:35/100<=t) (ht_hi:t<=70/100) :
  -t^2/2+((1+ρ)/2)*log (bP ((1+ρ)/2) (gC - t)) -
   ((1+ρ)/2)*log (1+ρ)<=gStar+aConst*ρ+bConst*ρ^3:=by
 have hβ0:0 < (1+ρ)/2:=by linarith
 have hβ1:(1+ρ)/2 < 1:=by linarith
 have hbiv_pos:=bivProb_pos (gC - t) hβ0 hβ1
 set isPos:Bool:=decide (0<=ρ)
 have hpub1:bP ((1+ρ)/2) (gC - t)<=BBranch isPos ρ t:=by
  have h:=bPu (gC - t) (show -1 < ρ by linarith) (show ρ < 1 by linarith)
  unfold bivPub1 at h
  unfold BBranch pBranch
  have hcsq:-(gC - t)^2 = -(t - gC)^2:=by ring
  have hneg:-(gC - t)=t - gC:=by ring
  rw [hcsq,hneg] at h
  by_cases h0:0<=ρ
  .
   simp only [isPos,h0,decide_true,↓reduceIte] at h ⊢
   exact h.trans_eq (by ring)
  .
   simp only [isPos,h0,decide_false,Bool.false_eq_true,↓reduceIte] at h ⊢
   exact h.trans_eq (by ring)
 suffices hQ:QBranch isPos ρ t<=0 by
  have hlog:=log_le_log hbiv_pos hpub1
  unfold QBranch at hQ
  nlinarith
 set dt:R:=t - tStar
 have htStar_in:(35/100:R)<=tStar/\tStar<=70/100:=by
  have ht:=tStar_mem
  norm_num [tLInt,tRInt,S0,fpS] at ht
  exact ⟨by linarith,by linarith⟩
 let f:R->R:=fun z=>QBranch isPos (z*ρ) (tStar+z*dt)
 let Q1:R->R:=fun z =>
  let uz:=1+z*ρ
  let xz:=tStar+z*dt - gC
  let Phz:=pC xz
  let phz:=pP xz
  let pz:=pBranch isPos (z*ρ)
  let dpz:=dpBranch isPos (z*ρ)
  let Ez:=exp (-xz^2/uz)
  let Erz:=Ez*(xz^2/uz^2)
  let Etz:=Ez*(-(2*xz/uz))
  let Bz:=BBranch isPos (z*ρ) (tStar+z*dt)
  let Brz:=dpz*Ez+pz*Erz
  let Btz:=2*(Phz*phz)+pz*Etz
  (-(tStar+z*dt)+(uz/2)*(Btz/Bz))*dt +
   ((1/2)*log Bz+(uz/2)*(Brz/Bz) - (1/2)*log uz - 1/2 -
    aConst - 3*bConst*(z*ρ)^2)*ρ
 have hseg:∀ z ∈ Set.Icc (0:R) 1,
   (if isPos then 0<=z*ρ/\z*ρ<=15/100 else -15/100<=z*ρ/\z*ρ<=0) /\
   35/100<=tStar+z*dt/\tStar+z*dt<=70/100:=by
  intro z hz
  refine ⟨?_,?_,?_⟩
  .
   by_cases h0:0<=ρ
   .
    simp only [isPos,h0,decide_true,↓reduceIte]
    exact ⟨mul_nonneg hz.1 h0,by nlinarith [hz.2]⟩
   .
    simp only [isPos,h0,decide_false,Bool.false_eq_true,↓reduceIte]
    exact ⟨by nlinarith [hz.2],mul_nonpos_of_nonneg_of_nonpos hz.1 (le_of_not_ge h0)⟩
  . unfold dt;nlinarith [hz.1,hz.2,htStar_in.1]
  . unfold dt;nlinarith [hz.1,hz.2,htStar_in.2]
 have hd_all:∀ z ∈ Set.Icc (0:R) 1,
   HD f (Q1 z) z /\
   HD Q1
    ((hessCoeffs isPos (z*ρ) (tStar+z*dt)).1*ρ^2 +
     2*(hessCoeffs isPos (z*ρ) (tStar+z*dt)).2.2*ρ*dt +
     (hessCoeffs isPos (z*ρ) (tStar+z*dt)).2.1*dt^2) z /\
   (hessCoeffs isPos (z*ρ) (tStar+z*dt)).1*ρ^2 +
    2*(hessCoeffs isPos (z*ρ) (tStar+z*dt)).2.2*ρ*dt +
    (hessCoeffs isPos (z*ρ) (tStar+z*dt)).2.1*dt^2<=0:=by
  intro z hz
  have hs_in:=hseg z hz
  have hhess:=inner_hess_negdef hs_in.1 hs_in.2.1 hs_in.2.2
  have hu_pos:0 < 1+z*ρ:=by
   cases his:isPos <;> simp only [his,Bool.false_eq_true,↓reduceIte] at hs_in <;> linarith [hs_in.1.1]
  have hd:=ray_derivs isPos ρ dt hu_pos hhess.1
  refine ⟨hd.1,hd.2,?_⟩
  set a:=(hessCoeffs isPos (z*ρ) (tStar+z*dt)).1
  set b:=(hessCoeffs isPos (z*ρ) (tStar+z*dt)).2.1
  set c:=(hessCoeffs isPos (z*ρ) (tStar+z*dt)).2.2
  have hmul:0<=a*(a*ρ^2+2*c*ρ*dt+b*dt^2):=by
   have hid:a*(a*ρ^2+2*c*ρ*dt+b*dt^2) =
     (a*ρ+c*dt)^2+(a*b - c^2)*dt^2:=by ring
   rw [hid]
   exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith [hhess.2.2.2]) (sq_nonneg _))
  nlinarith [hhess.2.1]
 have hQ1_anti:AntitoneOn Q1 (Set.Icc (0:R) 1) :=
  antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
   (fun z hz=>(hd_all z hz).2.1.continuousAt.continuousWithinAt)
   (fun z hz=>(hd_all z (interior_subset hz)).2.1.differentiableAt.differentiableWithinAt)
   (fun z hz=>by rw [(hd_all z (interior_subset hz)).2.1.deriv];exact (hd_all z (interior_subset hz)).2.2)
 have hQ1_zero:Q1 0=0:=by
  unfold Q1 BBranch pBranch dpBranch
  have hph_pos:0 < pC (tStar - gC):=pCp _
  have hph_ne:pC (tStar - gC) ≠ 0:=hph_pos.ne'
  have hlog2:log ((pC (tStar - gC))^2)=2*log (pC (tStar - gC)):=by
   rw [log_pow];ring
  have hmills:pP (tStar - gC)/pC (tStar - gC)=tStar:=by
   simpa [mR] using tStar_eq_mills.symm
  cases isPos <;> simp only [zero_mul,add_zero,zero_pow (by norm_num:2 ≠ 0),zero_pow (by norm_num:3 ≠ 0),
   mul_zero,mul_one,div_one,log_one,sub_zero,↓reduceIte,Bool.false_eq_true,aConst,hlog2]
  .
   have h1:-tStar+1/2*(2*(pC (tStar - gC)*pP (tStar - gC)) /
     (pC (tStar - gC))^2)=0:=by
    have:1/2*(2*(pC (tStar - gC)*pP (tStar - gC)) /
      (pC (tStar - gC))^2)=pP (tStar - gC)/pC (tStar - gC):=by
     field_simp
    rw [this,hmills];ring
   have h2:1/2*(2*log (pC (tStar - gC))) +
     1/2*((2*PI)⁻¹*exp (-(tStar - gC)^2)/(pC (tStar - gC))^2) -
     1/2 - (log (pC (tStar - gC)) +
      exp (-(tStar - gC)^2)/(4*PI*(pC (tStar - gC))^2) - 1/2)=0:=by
    field_simp;ring
   rw [h1,h2];ring
  .
   have h1:-tStar+1/2*(2*(pC (tStar - gC)*pP (tStar - gC)) /
     (pC (tStar - gC))^2)=0:=by
    have:1/2*(2*(pC (tStar - gC)*pP (tStar - gC)) /
      (pC (tStar - gC))^2)=pP (tStar - gC)/pC (tStar - gC):=by
     field_simp
    rw [this,hmills];ring
   have h2:1/2*(2*log (pC (tStar - gC))) +
     1/2*((2*PI)⁻¹*exp (-(tStar - gC)^2)/(pC (tStar - gC))^2) -
     1/2 - (log (pC (tStar - gC)) +
      exp (-(tStar - gC)^2)/(4*PI*(pC (tStar - gC))^2) - 1/2)=0:=by
    field_simp;ring
   rw [h1,h2];ring
 have hf_anti:AntitoneOn f (Set.Icc (0:R) 1) :=
  antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
   (fun z hz=>(hd_all z hz).1.continuousAt.continuousWithinAt)
   (fun z hz=>(hd_all z (interior_subset hz)).1.differentiableAt.differentiableWithinAt)
   (fun z hz=>by
    rw [(hd_all z (interior_subset hz)).1.deriv]
    have hle:=hQ1_anti ⟨le_rfl,by norm_num⟩ (interior_subset hz) (interior_subset hz).1
    linarith [hQ1_zero])
 have hf0:f 0=0:=by
  unfold f QBranch BBranch pBranch gStar
  cases isPos <;> simp only [zero_mul,add_zero,zero_pow (by norm_num:3 ≠ 0),mul_zero,
   log_one,↓reduceIte,Bool.false_eq_true]
  . rw [log_pow];ring
  . rw [log_pow];ring
 have hf1:f 1=QBranch isPos ρ t:=by
  unfold f dt;simp
 have hle:=hf_anti ⟨le_rfl,by norm_num⟩ ⟨by norm_num,le_rfl⟩ (by norm_num)
 linarith
theorem analytic_master {ρ t:R} (hρ0:-1 < ρ) (hρ1:ρ < 1) :
  -t^2/2+((1+ρ)/2)*log (bP ((1+ρ)/2) (gC - t)) -
   ((1+ρ)/2)*log (1+ρ)<=gStar+aConst*ρ+bConst*ρ^3:=by
 by_cases ht_hi:2<=t
 . exact analytic_tail_t_ge_2 hρ0 hρ1 ht_hi
 by_cases ht_lo:t <= -3/2
 . exact analytic_tail_t_le_neg32 hρ0 hρ1 ht_lo
 by_cases hρ_lo:ρ <= -96/100
 . exact analytic_tail_rho_le_neg96 hρ0 hρ_lo
 push Not at ht_hi ht_lo hρ_lo
 have hoc:=outer_regions_cert
 by_cases hρ_m15:ρ <= -15/100
 .
  by_cases ht_35:t<=35/100
  .
   exact cTs outerTree0 (-9600000) (-1500000) (-15000000) 3500000 (by decide) (by decide) (by decide) (by decide)
    hoc.1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith) hρ1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith)
  .
   by_cases ht_70:t<=70/100
   .
    exact cTs outerTree1 (-9600000) (-1500000) 3500000 7000000 (by decide) (by decide) (by decide) (by decide)
     hoc.2.1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith) hρ1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith)
   .
    exact cTs outerTree2 (-9600000) (-1500000) 7000000 20000000 (by decide) (by decide) (by decide) (by decide)
     hoc.2.2.1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith) hρ1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith)
 .
  by_cases hρ_15:ρ<=15/100
  .
   by_cases ht_35:t<=35/100
   .
    by_cases hρ_z:ρ<=0
    .
     exact cTs outerTree3 (-1500000) 0 (-15000000) 3500000 (by decide) (by decide) (by decide) (by decide)
      hoc.2.2.2.1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith) hρ1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith)
    .
     exact cTs outerTree5 0 1500000 (-15000000) 3500000 (by decide) (by decide) (by decide) (by decide)
      hoc.2.2.2.2.2.1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith) hρ1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith)
   .
    by_cases ht_70:t<=70/100
    . exact inner_box_sound (by linarith) hρ_15 (by linarith) ht_70
    .
     by_cases hρ_z:ρ<=0
     .
      exact cTs outerTree4 (-1500000) 0 7000000 20000000 (by decide) (by decide) (by decide) (by decide)
       hoc.2.2.2.2.1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith) hρ1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith)
     .
      exact cTs outerTree6 0 1500000 7000000 20000000 (by decide) (by decide) (by decide) (by decide)
       hoc.2.2.2.2.2.2.1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith) hρ1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith)
  .
   by_cases ht_35:t<=35/100
   .
    exact cTs outerTree7 1500000 10000000 (-15000000) 3500000 (by decide) (by decide) (by decide) (by decide)
     hoc.2.2.2.2.2.2.2.1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith) hρ1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith)
   .
    by_cases ht_70:t<=70/100
    .
     exact cTs outerTree8 1500000 10000000 3500000 7000000 (by decide) (by decide) (by decide) (by decide)
      hoc.2.2.2.2.2.2.2.2.1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith) hρ1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith)
    .
     exact cTs outerTree9 1500000 10000000 7000000 20000000 (by decide) (by decide) (by decide) (by decide)
      hoc.2.2.2.2.2.2.2.2.2 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith) hρ1 (by norm_num [S0,fpS];linarith) (by norm_num [S0,fpS];linarith)
abbrev Ei (n:ℕ):={p:Fin n × Fin n // p.1 < p.2}
noncomputable def gE (n:ℕ):Measure (Ei n->R) :=
 Measure.pi (fun _:Ei n=>N01)
instance (n:ℕ):IsProbabilityMeasure (gE n):=by
 unfold gE;infer_instance
def ev0 {n:ℕ} (W:Ei n->R) (i j:Fin n):R :=
 if h:i < j then W ⟨(i,j),h⟩ else if h':j < i then W ⟨(j,i),h'⟩ else 0
lemma continuous_edgeVal {n:ℕ} (i j:Fin n):Continuous (fun W:Ei n->R=>ev0 W i j):=by
 unfold ev0;split_ifs <;> fun_prop
lemma edgeVal_single {n:ℕ} (e:Ei n) (i j:Fin n) :
  ev0 (Pi.single e (1:R)) i j =
   if (i=e.1.1/\j=e.1.2)\/(i=e.1.2/\j=e.1.1) then 1 else 0:=by
 unfold ev0
 by_cases h1:i < j
 .
  rw [dif_pos h1]
  by_cases he:(⟨(i,j),h1⟩:Ei n)=e
  . subst he;rw [Pi.single_eq_same,if_pos (Or.inl ⟨rfl,rfl⟩)]
  .
   have hne:¬((i=e.1.1/\j=e.1.2)\/(i=e.1.2/\j=e.1.1)):=by
    rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    . exact he rfl
    . exact (not_lt_of_gt e.2) h1
   rw [if_neg hne,Pi.single_eq_of_ne he]
 .
  by_cases h2:j < i
  .
   rw [dif_neg h1,dif_pos h2]
   by_cases he:(⟨(j,i),h2⟩:Ei n)=e
   . subst he;rw [Pi.single_eq_same,if_pos (Or.inr ⟨rfl,rfl⟩)]
   .
    have hne:¬((i=e.1.1/\j=e.1.2)\/(i=e.1.2/\j=e.1.1)):=by
     rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
     . exact (not_lt_of_gt e.2) h2
     . exact he rfl
    rw [if_neg hne,Pi.single_eq_of_ne he]
  .
   rw [dif_neg h1,dif_neg h2]
   have hij:i=j:=le_antisymm (not_lt.mp h2) (not_lt.mp h1)
   have hne:¬((i=e.1.1/\j=e.1.2)\/(i=e.1.2/\j=e.1.1)):=by
    rintro (⟨rfl,h⟩ | ⟨rfl,h⟩) <;> exact e.2.ne (by omega)
   rw [if_neg hne]
def bS (m:ℕ):Finset (Finset (Fin (2*m))) :=
 Finset.univ.filter (fun s=>s.card=m)
lemma card_bisections (m:ℕ):(bS m).card=(2*m).choose m:=by
 have h:bS m=Finset.powersetCard m Finset.univ:=by
  ext s;simp [bS,Finset.mem_powersetCard]
 rw [h,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]
def spin {n:ℕ} (s:Finset (Fin n)) (i:Fin n):R:=if i ∈ s then 1 else -1
lemma spin_sq {n:ℕ} (s:Finset (Fin n)) (i:Fin n):(spin s i)^2=1:=by
 unfold spin;split_ifs <;> norm_num
lemma spin_mul_sq {n:ℕ} (s:Finset (Fin n)) (i j:Fin n):(spin s i*spin s j)^2=1:=by
 rw [mul_pow,spin_sq,spin_sq,one_mul]
noncomputable def fv0 (n:ℕ) (W:Ei n->R) (s:Finset (Fin n)) (i:Fin n):R :=
 (sqrt (n:R))⁻¹*∑ j:Fin n,ev0 W i j*(spin s i*spin s j)
def aF (n:ℕ) (s:Finset (Fin n)):Set (Ei n->R) :=
 {W | ∀ i:Fin n,gC<=fv0 n W s i}
open scoped Classical in
noncomputable def friendlyCount (m:ℕ) (W:Ei (2*m)->R):R :=
 ∑ s ∈ bS m,if W ∈ aF (2*m) s then (1:R) else 0
lemma charFunDual_gaussianReal_std (L:StrongDual R R) :
  charFunDual (N01) L=Complex.exp (-((L 1:ℂ)^2)/2):=by
 have h1:charFunDual (N01) L=charFun (N01) (L 1):=by
  rw [charFunDual_apply,charFun_apply_real]
  congr 1;ext x
  have hL:L x=L 1*x:=by
   have:=L.map_smul x (1:R)
   simp only [smul_eq_mul,mul_one] at this
   rw [this,mul_comm]
  rw [hL,Complex.ofReal_mul]
 rw [h1,charFun_gaussianReal]
 simp only [Complex.ofReal_zero,mul_zero,zero_mul,zero_sub,NNReal.coe_one,Complex.ofReal_one,one_mul]
 congr 1;ring
lemma charFunDual_pi_gaussianReal_map {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (T:(ι->R) →L[R] (κ->R)) (L:StrongDual R (κ->R)) :
  charFunDual ((Measure.pi (fun _:ι=>N01)).map T) L =
   Complex.exp (-((∑ e:ι,(∑ j:κ,L (Pi.single j 1)*T (Pi.single e 1) j)^2:R):ℂ)/2):=by
 rw [charFunDual_map,charFunDual_pi]
 have hL_exp:∀ (x:κ->R),L x=∑ j:κ,L (Pi.single j 1)*x j:=by
  intro x
  have hx:x=∑ j:κ,x j • Pi.single j (1:R):=by
   ext k;simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs=>rw [hx]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _=>?_
  rw [L.map_smul,smul_eq_mul,mul_comm]
 simp_rw [charFunDual_gaussianReal_std,← Complex.exp_sum]
 congr 1
 simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.single_apply,
  Complex.ofReal_sum,Complex.ofReal_pow,Finset.sum_div,← Finset.sum_neg_distrib]
 refine Finset.sum_congr rfl fun e _=>?_
 have h1:L (T (Pi.single e (1:R)))=∑ j:κ,L (Pi.single j 1)*T (Pi.single e 1) j :=
  hL_exp (T (Pi.single e 1))
 rw [h1,Complex.ofReal_sum]
lemma pi_gaussianReal_map_eq {ι₁ ι₂ κ:Type*}
  [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] [Fintype κ] [DecidableEq κ]
  (T₁:(ι₁->R) →L[R] (κ->R)) (T₂:(ι₂->R) →L[R] (κ->R))
  (hcov:∀ ξ:κ->R,
   ∑ e:ι₁,(∑ j:κ,ξ j*T₁ (Pi.single e 1) j)^2 =
   ∑ e:ι₂,(∑ j:κ,ξ j*T₂ (Pi.single e 1) j)^2) :
  (Measure.pi (fun _:ι₁=>N01)).map T₁ =
  (Measure.pi (fun _:ι₂=>N01)).map T₂:=by
 refine Measure.ext_of_charFunDual (funext fun L=>?_)
 rw [charFunDual_pi_gaussianReal_map,charFunDual_pi_gaussianReal_map,hcov (fun j=>L (Pi.single j 1))]
lemma gaussianPDFReal_zero_one (x:R):gaussianPDFReal 0 1 x=pP x :=
 (pPg x).symm
lemma gaussianReal_Iic (a:R):(N01 (Set.Iic a)).toReal=pC a:=rfl
lemma continuous_stdPhiPDF:Continuous pP:=by unfold pP;fun_prop
lemma continuous_stdPhiCDF:Continuous pC :=
 continuous_iff_continuousAt.mpr fun z=>(pCd z).continuousAt
lemma gaussianReal_Ici (a:R):(N01 (Set.Ici a)).toReal=pC (-a):=by
 have h1:(N01).map (fun x:R=>-x)=N01:=by
  simpa using gaussianReal_map_neg (μ:=0) (v:=1)
 have h2:N01 (Set.Ici a)=N01 (Set.Iic (-a)):=by
  conv_lhs=>rw [← h1]
  rw [Measure.map_apply (by fun_prop) measurableSet_Ici]
  have hset:(fun x:R=>-x) ⁻¹' Set.Ici a=Set.Iic (-a):=by
   ext x;simp only [Set.mem_preimage,Set.mem_Ici,Set.mem_Iic]
   constructor <;> intro h <;> linarith
  rw [hset]
 rw [h2,gaussianReal_Iic]
lemma gaussianReal_Icc (a b:R) (hab:a<=b) :
  (N01 (Set.Icc a b)).toReal=pC b - pC a:=by
 have hdisj:Disjoint (Set.Iic a) (Set.Ioc a b):=Set.Iic_disjoint_Ioc le_rfl
 have hunion:Set.Iic a ∪ Set.Ioc a b=Set.Iic b:=Set.Iic_union_Ioc_eq_Iic hab
 have hmeas:N01 (Set.Ioc a b)=N01 (Set.Icc a b):=by
  have hdiff:Set.Icc a b=Set.Ioc a b ∪ {a}:=by
   ext x;simp only [Set.mem_Icc,Set.mem_union,Set.mem_Ioc,Set.mem_singleton_iff]
   constructor
   .
    intro ⟨h1,h2⟩;rcases eq_or_lt_of_le h1 with rfl | hlt
    . exact Or.inr rfl
    . exact Or.inl ⟨hlt,h2⟩
   .
    rintro (⟨h1,h2⟩ | rfl)
    . exact ⟨h1.le,h2⟩
    . exact ⟨le_rfl,hab⟩
  haveI:=nullSingletonClass_gaussianReal (μ:=0) one_ne_zero
  have hdisj_a:Disjoint (Set.Ioc a b) {a}:=by
   rw [Set.disjoint_singleton_right];intro h;linarith [h.1]
  rw [hdiff,measure_union hdisj_a (measurableSet_singleton a),measure_singleton,add_zero]
 have hadd:N01 (Set.Iic b)=N01 (Set.Iic a)+N01 (Set.Ioc a b):=by
  rw [← hunion,measure_union hdisj measurableSet_Ioc]
 have htoR:=congrArg ENNReal.toReal hadd
 rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),hmeas,gaussianReal_Iic,gaussianReal_Iic] at htoR
 linarith
lemma gaussianReal_Icc_le_len (a b:R) (hab:a<=b) :
  (N01 (Set.Icc a b)).toReal<=(b - a)/sqrt (2*PI):=by
 rw [gaussianReal_apply_eq_integral 0 one_ne_zero (Set.Icc a b)]
 simp_rw [gaussianPDFReal_zero_one]
 rw [ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc fun x _=>pPn x)]
 have hle:∀ x ∈ Set.Icc a b,pP x<=(sqrt (2*PI))⁻¹:=fun x _=>by
  unfold pP
  have:exp (-x^2/2)<=1:=exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  nlinarith [inv_nonneg.mpr (sqrt_nonneg (2*PI))]
 have h1:=setIntegral_mono_on ipP.integrableOn
  (integrableOn_const (hs:=measure_Icc_lt_top.ne)) measurableSet_Icc hle
 rw [setIntegral_const,Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith),smul_eq_mul] at h1
 linarith [div_eq_mul_inv (b - a) (sqrt (2*PI))]
lemma gaussianReal_Icc_symm_ge {ε:R} (hε:0<=ε) :
  2*ε*pP ε<=(N01 (Set.Icc (-ε) ε)).toReal:=by
 rw [gaussianReal_apply_eq_integral 0 one_ne_zero (Set.Icc (-ε) ε)]
 simp_rw [gaussianPDFReal_zero_one]
 rw [ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc fun x _=>pPn x)]
 have hge:∀ x ∈ Set.Icc (-ε) ε,pP ε<=pP x:=fun x hx=>by
  unfold pP
  exact mlL (exp_le_exp.mpr (by nlinarith [hx.1,hx.2])) (by positivity)
 have h1:=setIntegral_mono_on (integrableOn_const (hs:=measure_Icc_lt_top.ne))
  ipP.integrableOn measurableSet_Icc hge
 rw [setIntegral_const,Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith),smul_eq_mul] at h1
 linarith
lemma gaussian_abs_le_symm (σ μ r:R) (hσ:0 < σ) (hr:0<=r) :
  (N01 {z | |σ*z+μ| <= r}).toReal <=
   (N01 {z | |σ*z| <= r}).toReal:=by
 have hset1:{z:R | |σ*z+μ| <= r}=Set.Icc ((-r - μ) / σ) ((r - μ) / σ):=by
  ext z;simp only [Set.mem_ofPred_eq,Set.mem_Icc,abs_le,le_div_iff₀ hσ,div_le_iff₀ hσ]
  constructor <;> intro ⟨h1,h2⟩ <;> constructor <;> linarith
 have hset2:{z:R | |σ*z| <= r}=Set.Icc (-r / σ) (r / σ):=by
  ext z;simp only [Set.mem_ofPred_eq,Set.mem_Icc,abs_le,le_div_iff₀ hσ,div_le_iff₀ hσ]
  constructor <;> intro ⟨h1,h2⟩ <;> constructor <;> linarith
 rw [hset1,hset2,gaussianReal_Icc _ _ (dld (by linarith) hσ.le),
   gaussianReal_Icc _ _ (dld (by linarith) hσ.le)]
 set a:R:=r / σ
 set c:R:=μ / σ
 have ha:0<=a:=div_nonneg hr hσ.le
 have hrew:(r - μ) / σ=a - c/\(-r - μ) / σ = -a - c:=by unfold a c;constructor <;> ring
 rw [hrew.1,hrew.2,neg_div]
 let g:R->R:=fun u=>pC (a - u) - pC (-a - u)
 have hderiv:∀ u:R,HD g (pP (-a - u) - pP (a - u)) u:=by
  intro u
  have h1:=hasDerivAt_comp_fun (pCd (a - u)) ((hasDerivAt_const u a).sub (hdi u))
  have h2:=hasDerivAt_comp_fun (pCd (-a - u)) ((hasDerivAt_const u (-a)).sub (hdi u))
  have h3:=h1.fun_sub h2
  exact h3.congr_deriv (by ring)
 have hanti:AntitoneOn g (Set.Ici 0) :=
  antitoneOn_of_deriv_nonpos (convex_Ici 0)
   (fun u _=>(hderiv u).continuousAt.continuousWithinAt)
   (fun u _=>(hderiv u).differentiableAt.differentiableWithinAt)
   (fun u hu=>by
    rw [(hderiv u).deriv]
    have hu0:0<=u:=(interior_subset hu)
    unfold pP
    have hexp:exp (-(-a - u)^2/2)<=exp (-(a - u)^2/2) :=
     exp_le_exp.mpr (by nlinarith)
    nlinarith [inv_nonneg.mpr (sqrt_nonneg (2*PI))])
 have heven:∀ u:R,g (-u)=g u:=fun u=>by
  unfold g
  have h1:=stdPhiCDF_neg (a - u)
  have h2:=stdPhiCDF_neg (-a - u)
  have hr1:-(a - u) = -a - -u:=by ring
  have hr2:-(-a - u)=a - -u:=by ring
  rw [hr1] at h1;rw [hr2] at h2;linarith
 by_cases hc:0<=c
 . simpa [g] using hanti (le_rfl:(0:R)<=0) hc hc
 .
  have:=hanti (le_rfl:(0:R)<=0) (by linarith:0 <= -c) (by linarith:0 <= -c)
  rw [heven c] at this;simpa [g] using this
lemma bPg {β:R} (c:R) (hβ0:0 < β) (hβ1:β < 1) :
  bP β c =
   ((N01).prod (N01)
    {z:R × R | c<=sqrt β*z.1 - sqrt (1 - β) * |z.2|}).toReal:=by
 have hsβ:0 < sqrt β:=sqrt_pos.mpr hβ0
 set S:Set (R × R):={z | c<=sqrt β*z.1 - sqrt (1 - β) * |z.2|}
 have hS_meas:MeasurableSet S:=by
  have hcont:Continuous (fun z:R × R=>sqrt β*z.1 - sqrt (1 - β) * |z.2|):=by fun_prop
  exact measurableSet_le measurable_const hcont.measurable
 rw [Measure.prod_apply_symm hS_meas]
 have hslice:∀ u:R,N01 ((fun x=>(x,u)) ⁻¹' S) =
   ENNReal.ofReal (1 - pC ((sqrt (1 - β) * |u| + c)/sqrt β)):=by
  intro u
  have hpre:((fun x=>(x,u)) ⁻¹' S)=Set.Ici ((sqrt (1 - β) * |u| + c)/sqrt β):=by
   ext x;simp only [Set.mem_preimage,S,Set.mem_ofPred_eq,Set.mem_Ici,div_le_iff₀ hsβ]
   constructor <;> intro h <;> linarith
  rw [hpre]
  have htoR:=gaussianReal_Ici ((sqrt (1 - β) * |u| + c)/sqrt β)
  rw [stdPhiCDF_neg] at htoR
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _),htoR]
 simp_rw [hslice]
 have hmeas_f:Measurable (fun u:R=>1 - pC ((sqrt (1 - β) * |u| + c)/sqrt β)):=by
  have h1:Continuous pC:=continuous_iff_continuousAt.mpr fun z=>(pCd z).continuousAt
  exact (by fun_prop:Continuous (fun u:R=>1 - pC ((sqrt (1 - β) * |u| + c)/sqrt β))).measurable
 have hnn_f:∀ u:R,0<=1 - pC ((sqrt (1 - β) * |u| + c)/sqrt β):=fun u=>by
  linarith [stdPhiCDF_lt_one ((sqrt (1 - β) * |u| + c)/sqrt β)]
 have hint_f:Integrable (fun u:R=>1 - pC ((sqrt (1 - β) * |u| + c)/sqrt β)) (N01):=by
  refine Integrable.of_bound hmeas_f.aestronglyMeasurable 1 (Eventually.of_forall fun u=>?_)
  rw [Real.norm_eq_abs,aon (hnn_f u)]
  linarith [pCp ((sqrt (1 - β) * |u| + c)/sqrt β)]
 rw [← ofReal_integral_eq_lintegral_ofReal hint_f (Eventually.of_forall hnn_f),
   ENNReal.toReal_ofReal (integral_nonneg hnn_f),
   integral_gaussianReal_eq_integral_smul one_ne_zero]
 simp_rw [smul_eq_mul,gaussianPDFReal_zero_one]
 have hint_prod:Integrable (fun u:R=>pP u*pC ((sqrt (1 - β) * |u| + c)/sqrt β)):=by
  have h1:Continuous pC:=continuous_iff_continuousAt.mpr fun z=>(pCd z).continuousAt
  have h2:Continuous pP:=by unfold pP;fun_prop
  refine ipP.mono (by fun_prop:Continuous (fun u:R=>pP u*pC ((sqrt (1 - β) * |u| + c)/sqrt β))).aestronglyMeasurable (Eventually.of_forall fun u=>?_)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,aon (mul_nonneg (pPn u) (pCp _).le),
    aon (pPn u)]
  nlinarith [stdPhiCDF_lt_one ((sqrt (1 - β) * |u| + c)/sqrt β),pPn u]
 have hsub_eq:(∫ u:R,pP u*(1 - pC ((sqrt (1 - β) * |u| + c)/sqrt β))) =
   1 - ∫ u:R,pP u*pC ((sqrt (1 - β) * |u| + c)/sqrt β):=by
  have heq:(fun u:R=>pP u*(1 - pC ((sqrt (1 - β) * |u| + c)/sqrt β))) =
    fun u:R=>pP u - pP u*pC ((sqrt (1 - β) * |u| + c)/sqrt β):=by
   ext u;ring
  rw [heq,integral_sub ipP hint_prod,integral_stdPhiPDF_univ]
 rw [hsub_eq]
 have hsplit:(∫ u:R,pP u*pC ((sqrt (1 - β) * |u| + c)/sqrt β)) =
   (∫ u in Set.Iic (0:R),pP u*pC ((sqrt (1 - β) * |u| + c)/sqrt β)) +
   (∫ u in Set.Ioi (0:R),pP u*pC ((sqrt (1 - β) * |u| + c)/sqrt β)):=by
  rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hint_prod.integrableOn hint_prod.integrableOn,
    Set.Iic_union_Ioi,setIntegral_univ]
 have hrefl:(∫ u in Set.Iic (0:R),pP u*pC ((sqrt (1 - β) * |u| + c)/sqrt β)) =
   ∫ u in Set.Ioi (0:R),pP u*pC ((sqrt (1 - β) * |u| + c)/sqrt β):=by
  have hneg:=integral_comp_neg_Ioi (0:R) (fun u:R=>pP u*pC ((sqrt (1 - β) * |u| + c)/sqrt β))
  simp only [neg_zero] at hneg
  have heven:∀ u:R,pP (-u)*pC ((sqrt (1 - β) * |-u| + c)/sqrt β) =
    pP u*pC ((sqrt (1 - β) * |u| + c)/sqrt β):=fun u=>by
   have hpdf:pP (-u)=pP u:=by unfold pP;rw [neg_sq]
   rw [hpdf,abs_neg]
  simp_rw [heven] at hneg
  exact hneg.symm
 have hIoi_eq:(∫ u in Set.Ioi (0:R),pP u*pC ((sqrt (1 - β) * |u| + c)/sqrt β)) =
   ∫ u in Set.Ioi (0:R),pC ((sqrt (1 - β)*u+c)/sqrt β)*pP u:=by
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu=>?_
  rw [abs_of_pos hu,mul_comm]
 rw [hsplit,hrefl,hIoi_eq]
 unfold bP;ring
lemma bDc {u:ℕ} (hu:2<=u) {σ:R} (hσ:0 < σ) (s:R) (r:Fin u->R)
  (hr:∀ i,0<=r i) :
  (Measure.pi (fun _:Fin u=>N01)
   {x:Fin u->R | ∀ i:Fin u,|σ*(x i - (∑ j,x j)/(u:R))+s/(u:R)| <= r i}).toReal <=
  sqrt (u:R)*∏ i:Fin (u - 1),
   (N01 {z | |σ*z| <= r ⟨i.1,by omega⟩}).toReal:=by
 have hu_pos:(0:R) < (u:R):=by exact_mod_cast (by omega:0 < u)
 have hu_ne:(u:R) ≠ 0:=hu_pos.ne'
 set μu:Measure (Fin u->R):=Measure.pi (fun _:Fin u=>N01)
 set A:Set (Fin u->R) :=
  {x | ∀ i:Fin u,|σ*(x i - (∑ j,x j)/(u:R))+s/(u:R)| <= r i}
 let T₁L:(Fin u->R) →ₗ[R] (Option (Fin u)->R) :=
  {
   toFun:=fun x o=>match o with
    | none=>(∑ j,x j)/(u:R)
    | some i=>x i - (∑ j,x j)/(u:R)
   map_add':=fun x y=>by
    ext o;cases o with
    | none=>simp [Finset.sum_add_distrib,add_div]
    | some i=>simp [Finset.sum_add_distrib,add_div];ring
   map_smul':=fun c x=>by
    ext o;cases o with
    | none=>simp [← Finset.mul_sum,mul_div_assoc]
    | some i=>simp [← Finset.mul_sum,mul_div_assoc];ring }
 let T₂L:(Option (Fin u)->R) →ₗ[R] (Option (Fin u)->R) :=
  {
   toFun:=fun z o=>match o with
    | none=>(sqrt (u:R))⁻¹*z none
    | some i=>z (some i) - (∑ j:Fin u,z (some j))/(u:R)
   map_add':=fun x y=>by
    ext o;cases o with
    | none=>simp [mul_add]
    | some i=>simp [Finset.sum_add_distrib,add_div];ring
   map_smul':=fun c x=>by
    ext o;cases o with
    | none=>simp;ring
    | some i=>simp [← Finset.mul_sum,mul_div_assoc];ring }
 let T₁:(Fin u->R) →L[R] (Option (Fin u)->R):=T₁L.toContinuousLinearMap
 let T₂:(Option (Fin u)->R) →L[R] (Option (Fin u)->R):=T₂L.toContinuousLinearMap
 have hlaw:μu.map T₁=(Measure.pi (fun _:Option (Fin u)=>N01)).map T₂:=by
  refine pi_gaussianReal_map_eq T₁ T₂ fun ξ=>?_
  set a:R:=ξ none
  set bbar:R:=(∑ j:Fin u,ξ (some j))/(u:R)
  have hL1:∀ e:Fin u,∑ o:Option (Fin u),ξ o*T₁ (Pi.single e 1) o =
    a/(u:R)+(ξ (some e) - bbar):=by
   intro e
   rw [Fintype.sum_option]
   have h1:T₁ (Pi.single e 1) none=1/(u:R):=by
    change (∑ j:Fin u,(Pi.single e (1:R):Fin u->R) j)/(u:R)=1/(u:R)
    simp
   have h2:∀ i:Fin u,T₁ (Pi.single e 1) (some i)=(if i=e then 1 else 0) - 1/(u:R):=by
    intro i
    change (Pi.single e (1:R):Fin u->R) i - (∑ j:Fin u,(Pi.single e (1:R):Fin u->R) j)/(u:R)=_
    simp [Pi.single_apply]
   rw [h1]
   simp_rw [h2,mul_sub,Finset.sum_sub_distrib,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true,← Finset.sum_mul]
   unfold a bbar;ring
  have hsum_zero:∑ e:Fin u,(ξ (some e) - bbar)=0:=by
   rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
   unfold bbar;field_simp;ring
  have hLHS:∑ e:Fin u,(∑ o:Option (Fin u),ξ o*T₁ (Pi.single e 1) o)^2 =
    a^2/(u:R)+∑ e:Fin u,(ξ (some e) - bbar)^2:=by
   simp_rw [hL1,add_sq,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
   have hcross:∑ e:Fin u,2*(a/(u:R))*(ξ (some e) - bbar)=0:=by
    rw [← Finset.mul_sum,hsum_zero,mul_zero]
   rw [hcross,add_zero]
   congr 1;field_simp
  have hRHS:∑ o':Option (Fin u),(∑ o:Option (Fin u),ξ o*T₂ (Pi.single o' 1) o)^2 =
    a^2/(u:R)+∑ e:Fin u,(ξ (some e) - bbar)^2:=by
   rw [Fintype.sum_option]
   congr 1
   .
    rw [Fintype.sum_option]
    have hnone:T₂ (Pi.single none 1) none=(sqrt (u:R))⁻¹:=by
     change (sqrt (u:R))⁻¹*(Pi.single none (1:R):Option (Fin u)->R) none=_
     simp
    have hsome:∀ i:Fin u,T₂ (Pi.single none 1) (some i)=0:=fun i=>by
     change (Pi.single none (1:R):Option (Fin u)->R) (some i) -
      (∑ j:Fin u,(Pi.single none (1:R):Option (Fin u)->R) (some j))/(u:R)=0
     simp
    simp_rw [hnone,hsome,mul_zero,Finset.sum_const_zero,add_zero]
    rw [mul_pow,inv_pow,sq_sqrt hu_pos.le];unfold a;ring
   .
    refine Finset.sum_congr rfl fun e _=>?_
    congr 1
    rw [Fintype.sum_option]
    have hnone:T₂ (Pi.single (some e) 1) none=0:=by
     change (sqrt (u:R))⁻¹*(Pi.single (some e) (1:R):Option (Fin u)->R) none=0
     simp
    have hsome:∀ i:Fin u,T₂ (Pi.single (some e) 1) (some i)=(if i=e then 1 else 0) - 1/(u:R):=fun i=>by
     change (Pi.single (some e) (1:R):Option (Fin u)->R) (some i) -
      (∑ j:Fin u,(Pi.single (some e) (1:R):Option (Fin u)->R) (some j))/(u:R)=_
     have hsum1:∑ j:Fin u,(Pi.single (some e) (1:R):Option (Fin u)->R) (some j)=1:=by
      simp [Pi.single_apply]
     rw [hsum1];simp [Pi.single_apply]
    simp_rw [hnone,mul_zero,zero_add,hsome,mul_sub,Finset.sum_sub_distrib,mul_ite,mul_one,mul_zero,
     Finset.sum_ite_eq',Finset.mem_univ,if_true,← Finset.sum_mul]
    unfold bbar;ring
  rw [hLHS,hRHS]
 have hbound_δ:∀ δ:R,0 < δ ->
   (μu A).toReal<=sqrt (u:R)*exp (δ^2*(u:R)/2) *
    ∏ i:Fin (u - 1),(N01 {z | |σ*z| <= r ⟨i.1,by omega⟩+σ*δ}).toReal:=by
  intro δ hδ
  set S_opt:Set (Option (Fin u)->R) :=
   {y | |y none| <= δ/\∀ i:Fin u,|σ*y (some i)+s/(u:R)| <= r i}
  have hS_meas:MeasurableSet S_opt:=by
   have h1:MeasurableSet {y:Option (Fin u)->R | |y none| <= δ} :=
    measurableSet_le (continuous_abs.comp (continuous_apply none)).measurable measurable_const
   have h2:MeasurableSet {y:Option (Fin u)->R | ∀ i:Fin u,|σ*y (some i)+s/(u:R)| <= r i}:=by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
     measurableSet_le (continuous_abs.comp ((continuous_const.mul (continuous_apply (some i))).add continuous_const)).measurable measurable_const
   exact h1.inter h2
  have hLHS_eq:μu (T₁ ⁻¹' S_opt) =
    N01 (Set.Icc (-(δ*sqrt (u:R))) (δ*sqrt (u:R)))*μu A:=by
   have hmap:=congrArg (fun m:Measure (Option (Fin u)->R)=>m S_opt) hlaw
   rw [Measure.map_apply T₁.continuous.measurable hS_meas,
     Measure.map_apply T₂.continuous.measurable hS_meas] at hmap
   rw [hmap]
   let eOpt:(Option (Fin u)->R) ≃ᵐ (Fin u->R) × R:=MeasurableEquiv.piOptionEquivProd (fun _=>R)
   have heOpt_mp:MeasurePreserving eOpt
     (Measure.pi (fun _:Option (Fin u)=>N01))
     (μu.prod (N01)):=by
    have hsymm:MeasurePreserving eOpt.symm (μu.prod (N01))
      (Measure.pi (fun _:Option (Fin u)=>N01)) :=
     ⟨eOpt.symm.measurable,by
      simpa [eOpt,μu] using MeasureTheory.Measure.pi_map_piOptionEquivProd (fun _:Option (Fin u)=>N01)⟩
    simpa using hsymm.symm eOpt.symm
   set Iδ:Set R:=Set.Icc (-(δ*sqrt (u:R))) (δ*sqrt (u:R))
   have hpre_eq:T₂ ⁻¹' S_opt=eOpt ⁻¹' (A ×ˢ Iδ):=by
    ext z
    have he1:(eOpt z).1=fun i:Fin u=>z (some i):=rfl
    have he2:(eOpt z).2=z none:=rfl
    simp only [Set.mem_preimage,S_opt,Set.mem_ofPred_eq,Set.mem_prod,Iδ,Set.mem_Icc,A,he1,he2]
    constructor
    .
     rintro ⟨h1,h2⟩
     refine ⟨h2,?_⟩
     change |(sqrt (u:R))⁻¹*z none| <= δ at h1
     rw [abs_mul,abs_of_pos (inv_pos.mpr (sqrt_pos.mpr hu_pos)),inv_mul_le_iff₀ (sqrt_pos.mpr hu_pos),
       abs_le] at h1
     exact ⟨by linarith,by linarith⟩
    .
     rintro ⟨h3,⟨h1,h2⟩⟩
     refine ⟨?_,h3⟩
     change |(sqrt (u:R))⁻¹*z none| <= δ
     rw [abs_mul,abs_of_pos (inv_pos.mpr (sqrt_pos.mpr hu_pos)),inv_mul_le_iff₀ (sqrt_pos.mpr hu_pos),
       abs_le]
     exact ⟨by linarith,by linarith⟩
   have hA_meas:MeasurableSet A:=by
    rw [show A=⋂ i:Fin u,{x:Fin u->R | |σ*(x i - (∑ j,x j)/(u:R))+s/(u:R)| <= r i} by ext x;simp [A]]
    refine MeasurableSet.iInter fun i=>measurableSet_le ?_ measurable_const
    have hc:Continuous (fun x:Fin u->R=>|σ*(x i - (∑ j,x j)/(u:R))+s/(u:R)|):=by fun_prop
    exact hc.measurable
   rw [hpre_eq,heOpt_mp.measure_preimage (hA_meas.prod measurableSet_Icc).nullMeasurableSet,
     Measure.prod_prod,mul_comm]
  let eU:Fin (u - 1+1) ≃ Fin u:=finCongr (by omega)
  let e1:(Fin u->R) ≃ᵐ (Fin (u - 1+1)->R):=MeasurableEquiv.piCongrLeft (fun _=>R) eU.symm
  let e2:(Fin (u - 1+1)->R) ≃ᵐ R × (Fin (u - 1)->R) :=
   MeasurableEquiv.piFinSuccAbove (fun _:Fin (u - 1+1)=>R) (Fin.last (u - 1))
  let eProd:(Fin u->R) ≃ᵐ R × (Fin (u - 1)->R):=e1.trans e2
  have heProd_mp:MeasurePreserving eProd μu
    ((N01).prod (Measure.pi (fun _:Fin (u - 1)=>N01))):=by
   have h1:MeasurePreserving e1 μu (Measure.pi (fun _:Fin (u - 1+1)=>N01)):=by
    simpa [e1,μu] using measurePreserving_piCongrLeft (fun _:Fin (u - 1+1)=>N01) eU.symm
   have h2:MeasurePreserving e2 (Measure.pi (fun _:Fin (u - 1+1)=>N01))
     ((N01).prod (Measure.pi (fun _:Fin (u - 1)=>N01))) :=
    measurePreserving_piFinSuccAbove (fun _:Fin (u - 1+1)=>N01) (Fin.last (u - 1))
   exact h2.comp h1
  set B_prod:Set (R × (Fin (u - 1)->R)) :=
   {p | |p.1+∑ i:Fin (u - 1),p.2 i| <= (u:R)*δ /\
      ∀ i:Fin (u - 1),|σ*p.2 i+s/(u:R)| <= r ⟨i.1,by omega⟩+σ*δ}
  have hB_meas:MeasurableSet B_prod:=by
   have h1:MeasurableSet {p:R × (Fin (u - 1)->R) | |p.1+∑ i:Fin (u - 1),p.2 i| <= (u:R)*δ} :=
    measurableSet_le (by fun_prop:Continuous (fun p:R × (Fin (u - 1)->R)=>|p.1+∑ i:Fin (u - 1),p.2 i|)).measurable measurable_const
   have h2:MeasurableSet {p:R × (Fin (u - 1)->R) | ∀ i:Fin (u - 1),|σ*p.2 i+s/(u:R)| <= r ⟨i.1,by omega⟩+σ*δ}:=by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
     measurableSet_le (by fun_prop:Continuous (fun p:R × (Fin (u - 1)->R)=>|σ*p.2 i+s/(u:R)|)).measurable measurable_const
   exact h1.inter h2
  have hsub:T₁ ⁻¹' S_opt ⊆ eProd ⁻¹' B_prod:=by
   intro x hx
   rcases hx with ⟨hmean,hcoord⟩
   change |(∑ j:Fin u,x j)/(u:R)| <= δ at hmean
   have hsum_eq:(eProd x).1+∑ i:Fin (u - 1),(eProd x).2 i=∑ j:Fin u,x j:=by
    have hs1:∑ j:Fin (u - 1+1),e1 x j=∑ j:Fin u,x j:=by
     refine Fintype.sum_equiv eU (fun j=>e1 x j) (fun j=>x j) fun j=>?_
     simp [e1,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft]
    rw [← hs1,Fin.sum_univ_castSucc,add_comm]
    simp [eProd,e2,MeasurableEquiv.piFinSuccAbove_apply,Fin.init]
   have h2coord:∀ i:Fin (u - 1),(eProd x).2 i=x ⟨i.1,by omega⟩:=fun i=>by
    have hstep1:(eProd x).2 i=e1 x i.castSucc:=by
     simp [eProd,e2,MeasurableEquiv.piFinSuccAbove_apply,Fin.init]
    rw [hstep1]
    simp only [e1,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
    congr 1
   refine ⟨?_,fun i=>?_⟩
   .
    rw [hsum_eq]
    rw [abs_div,abs_of_pos hu_pos,div_le_iff₀ hu_pos] at hmean
    linarith
   .
    rw [h2coord i]
    have hi:=hcoord ⟨i.1,by omega⟩
    change |σ*(x ⟨i.1,by omega⟩ - (∑ j:Fin u,x j)/(u:R))+s/(u:R)| <= r ⟨i.1,by omega⟩ at hi
    have htri:|σ*x ⟨i.1,by omega⟩+s/(u:R)| <=
      |σ*(x ⟨i.1,by omega⟩ - (∑ j:Fin u,x j)/(u:R))+s/(u:R)| +
      |σ*((∑ j:Fin u,x j)/(u:R))| := by
     have:=abs_add_le (σ*(x ⟨i.1,by omega⟩ - (∑ j:Fin u,x j)/(u:R))+s/(u:R))
      (σ*((∑ j:Fin u,x j)/(u:R)))
     rwa [show σ*(x ⟨i.1,by omega⟩ - (∑ j:Fin u,x j)/(u:R))+s/(u:R) +
      σ*((∑ j:Fin u,x j)/(u:R))=σ*x ⟨i.1,by omega⟩+s/(u:R) by ring] at this
    rw [abs_mul,abs_of_pos hσ] at htri
    nlinarith
  have hRHS_ub:(μu (T₁ ⁻¹' S_opt)).toReal <=
    ((2*(u:R)*δ)/sqrt (2*PI)) *
     ∏ i:Fin (u - 1),(N01 {z | |σ*z| <= r ⟨i.1,by omega⟩+σ*δ}).toReal:=by
   have hle1:μu (T₁ ⁻¹' S_opt)<=((N01).prod (Measure.pi (fun _:Fin (u - 1)=>N01))) B_prod:=by
    calc μu (T₁ ⁻¹' S_opt)<=μu (eProd ⁻¹' B_prod):=measure_mono hsub
     _ = _:=heProd_mp.measure_preimage hB_meas.nullMeasurableSet
   rw [Measure.prod_apply_symm hB_meas] at hle1
   set C_set:Set (Fin (u - 1)->R) :=
    Set.univ.pi (fun i:Fin (u - 1)=>{z:R | |σ*z+s/(u:R)| <= r ⟨i.1,by omega⟩+σ*δ})
   have hslice_le:∀ y:Fin (u - 1)->R,
     N01 ((fun z=>(z,y)) ⁻¹' B_prod) <=
      ENNReal.ofReal ((2*(u:R)*δ)/sqrt (2*PI))*Set.indicator C_set (fun _=>1) y:=by
    intro y
    by_cases hy:y ∈ C_set
    .
     rw [Set.indicator_of_mem hy,mul_one]
     have hsub_y:((fun z=>(z,y)) ⁻¹' B_prod) ⊆
       Set.Icc (-(∑ i,y i) - (u:R)*δ) (-(∑ i,y i)+(u:R)*δ):=by
      intro z hz
      have h1:=hz.1
      rw [abs_le] at h1
      exact ⟨by linarith,by linarith⟩
     have hle_y:=measure_mono hsub_y (μ:=N01)
     have hlen:=gaussianReal_Icc_le_len (-(∑ i,y i) - (u:R)*δ) (-(∑ i,y i)+(u:R)*δ) (by nlinarith)
     have hrew:-(∑ i,y i)+(u:R)*δ - (-(∑ i,y i) - (u:R)*δ)=2*(u:R)*δ:=by ring
     rw [hrew] at hlen
     exact hle_y.trans (by rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)];exact ENNReal.ofReal_le_ofReal hlen)
    .
     rw [Set.indicator_of_notMem hy,mul_zero]
     have hempty:((fun z=>(z,y)) ⁻¹' B_prod)=∅:=by
      ext z;simp only [Set.mem_preimage,B_prod,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      rintro ⟨_,h2⟩;exact hy fun i _=>h2 i
     rw [hempty,measure_empty]
   have hlint_le:(∫⁻ y,N01 ((fun z=>(z,y)) ⁻¹' B_prod) ∂Measure.pi (fun _:Fin (u - 1)=>N01)) <=
     ENNReal.ofReal ((2*(u:R)*δ)/sqrt (2*PI)) *
      Measure.pi (fun _:Fin (u - 1)=>N01) C_set:=by
    calc _ <= ∫⁻ y,ENNReal.ofReal ((2*(u:R)*δ)/sqrt (2*PI)) *
        Set.indicator C_set (fun _=>1) y ∂Measure.pi (fun _:Fin (u - 1)=>N01) :=
       lintegral_mono hslice_le
     _ = ENNReal.ofReal ((2*(u:R)*δ)/sqrt (2*PI)) *
        ∫⁻ y,Set.indicator C_set (fun _=>1) y ∂Measure.pi (fun _:Fin (u - 1)=>N01) :=
       lintegral_const_mul _ (Measurable.indicator measurable_const (MeasurableSet.univ_pi fun i =>
        measurableSet_le (by fun_prop:Continuous (fun z:R=>|σ*z+s/(u:R)|)).measurable measurable_const))
     _ = _:=by
       rw [lintegral_indicator (MeasurableSet.univ_pi fun i =>
        measurableSet_le (by fun_prop:Continuous (fun z:R=>|σ*z+s/(u:R)|)).measurable measurable_const),
        setLIntegral_one]
   have hpi:(Measure.pi (fun _:Fin (u - 1)=>N01) C_set).toReal =
     ∏ i:Fin (u - 1),(N01 {z | |σ*z+s/(u:R)| <= r ⟨i.1,by omega⟩+σ*δ}).toReal:=by
    rw [Measure.pi_pi,ENNReal.toReal_prod]
   have htot:=ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) (hle1.trans hlint_le)
   rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),hpi] at htot
   refine htot.trans (mlL ?_ (by positivity))
   exact Finset.prod_le_prod (fun i _=>ENNReal.toReal_nonneg) fun i _ =>
    gaussian_abs_le_symm σ (s/(u:R)) (r ⟨i.1,by omega⟩+σ*δ) hσ (by nlinarith [hr ⟨i.1,by omega⟩])
  have hlow_Icc:=gaussianReal_Icc_symm_ge (ε:=δ*sqrt (u:R)) (by positivity)
  have hlow_pos:0 < 2*(δ*sqrt (u:R))*pP (δ*sqrt (u:R)):=by
   have:=pPp (δ*sqrt (u:R));positivity
  have hprod_toR:=congrArg ENNReal.toReal hLHS_eq
  rw [ENNReal.toReal_mul] at hprod_toR
  have hmul_le:2*(δ*sqrt (u:R))*pP (δ*sqrt (u:R))*(μu A).toReal <=
    ((2*(u:R)*δ)/sqrt (2*PI)) *
     ∏ i:Fin (u - 1),(N01 {z | |σ*z| <= r ⟨i.1,by omega⟩+σ*δ}).toReal:=by
   have h1:=mlR hlow_Icc (ENNReal.toReal_nonneg:0<=(μu A).toReal)
   linarith [hprod_toR,hRHS_ub]
  have hcoeff:((2*(u:R)*δ)/sqrt (2*PI)) /
    (2*(δ*sqrt (u:R))*pP (δ*sqrt (u:R))) =
    sqrt (u:R)*exp (δ^2*(u:R)/2):=by
   unfold pP
   have hs2p:sqrt (2*PI) ≠ 0:=(sqrt_pos.mpr (by positivity)).ne'
   have hsu:sqrt (u:R) ≠ 0:=(sqrt_pos.mpr hu_pos).ne'
   have hsq:sqrt (u:R)*sqrt (u:R)=(u:R):=mul_self_sqrt hu_pos.le
   have hexp:-(δ*sqrt (u:R))^2/2 = -(δ^2*(u:R)/2):=by
    rw [mul_pow,sq_sqrt hu_pos.le];ring
   rw [hexp,exp_neg]
   have hpos_e:exp (δ^2*(u:R)/2) ≠ 0:=(exp_pos _).ne'
   field_simp [hs2p,hsu,hδ.ne',hpos_e]
   nlinarith [hsq]
  have hdiv:=(le_div_iff₀' hlow_pos).mpr hmul_le
  rw [mul_div_right_comm,hcoeff] at hdiv
  exact hdiv
 have hRHS_tendsto:Tendsto (fun δ:R=>sqrt (u:R)*exp (δ^2*(u:R)/2) *
   ∏ i:Fin (u - 1),(N01 {z | |σ*z| <= r ⟨i.1,by omega⟩+σ*δ}).toReal)
   (nhdsWithin 0 (Set.Ioi 0))
   (𝓝 (sqrt (u:R)*∏ i:Fin (u - 1),(N01 {z | |σ*z| <= r ⟨i.1,by omega⟩}).toReal)):=by
  have hcont_Phi:Continuous pC :=
   continuous_iff_continuousAt.mpr fun z=>(pCd z).continuousAt
  have hterm:∀ i:Fin (u - 1),
    Tendsto (fun δ:R=>(N01 {z | |σ*z| <= r ⟨i.1,by omega⟩+σ*δ}).toReal)
     (nhdsWithin 0 (Set.Ioi 0))
     (𝓝 (N01 {z | |σ*z| <= r ⟨i.1,by omega⟩}).toReal):=by
   intro i
   have hrew:∀ᶠ δ in nhdsWithin (0:R) (Set.Ioi 0),
     (N01 {z | |σ*z| <= r ⟨i.1,by omega⟩+σ*δ}).toReal =
     pC ((r ⟨i.1,by omega⟩+σ*δ) / σ) - pC (-(r ⟨i.1,by omega⟩+σ*δ) / σ):=by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hpos:0<=r ⟨i.1,by omega⟩+σ*δ:=by nlinarith [hr ⟨i.1,by omega⟩,Set.mem_Ioi.mp hδ]
    have hset:{z:R | |σ*z| <= r ⟨i.1,by omega⟩+σ*δ} =
      Set.Icc (-(r ⟨i.1,by omega⟩+σ*δ) / σ) ((r ⟨i.1,by omega⟩+σ*δ) / σ):=by
     ext z;simp only [Set.mem_ofPred_eq,Set.mem_Icc,abs_le,le_div_iff₀ hσ,div_le_iff₀ hσ]
     constructor <;> intro ⟨h1,h2⟩ <;> constructor <;> linarith
    rw [hset,gaussianReal_Icc _ _ (dld (by linarith) hσ.le)]
   have hlim_eq:(N01 {z | |σ*z| <= r ⟨i.1,by omega⟩}).toReal =
     pC ((r ⟨i.1,by omega⟩+σ*0) / σ) - pC (-(r ⟨i.1,by omega⟩+σ*0) / σ):=by
    have hset:{z:R | |σ*z| <= r ⟨i.1,by omega⟩} =
      Set.Icc (-(r ⟨i.1,by omega⟩) / σ) (r ⟨i.1,by omega⟩ / σ):=by
     ext z;simp only [Set.mem_ofPred_eq,Set.mem_Icc,abs_le,le_div_iff₀ hσ,div_le_iff₀ hσ]
     constructor <;> intro ⟨h1,h2⟩ <;> constructor <;> linarith
    rw [hset,gaussianReal_Icc _ _ (dld (by linarith [hr ⟨i.1,by omega⟩]) hσ.le)]
    simp
   rw [hlim_eq]
   refine Tendsto.congr' (hrew.mono fun _ h=>h.symm) ?_
   have hc:Continuous (fun δ:R=>pC ((r ⟨i.1,by omega⟩+σ*δ) / σ) -
     pC (-(r ⟨i.1,by omega⟩+σ*δ) / σ)):=by fun_prop
   exact (hc.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  have hprod:=tendsto_finsetProd Finset.univ fun i _=>hterm i
  have hexp:Tendsto (fun δ:R=>sqrt (u:R)*exp (δ^2*(u:R)/2))
    (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (sqrt (u:R))):=by
   have hc:Continuous (fun δ:R=>sqrt (u:R)*exp (δ^2*(u:R)/2)):=by fun_prop
   simpa using (hc.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  exact hexp.mul hprod
 exact ge_of_tendsto hRHS_tendsto (eventually_nhdsWithin_of_forall fun δ hδ=>hbound_δ δ hδ)
lemma sBL {n:ℕ} (hn:4<=n) (s:Finset (Fin n)) :
  (sqrt (2*PI)*exp (1/2))⁻¹*exp (-tStar*sqrt (n:R)) *
   exp ((n:R)*gStar)<=(gE n (aF n s)).toReal:=by
 have hn_pos:(0:R) < (n:R):=by exact_mod_cast (by omega:0 < n)
 have hn2_pos:(0:R) < ((n:R) - 2)/(n:R):=by
  have:(4:R)<=(n:R):=by exact_mod_cast hn
  exact div_pos (by linarith) hn_pos
 let T₁L:(Ei n->R) →ₗ[R] (Fin n->R) :=
  {
   toFun:=fun W i=>fv0 n W s i
   map_add':=fun W₁ W₂=>by
    ext i;dsimp only [fv0,ev0]
    simp only [Pi.add_apply]
    rw [← mul_add,← Finset.sum_add_distrib]
    congr 1;refine Finset.sum_congr rfl fun j _=>?_
    split_ifs <;> ring
   map_smul':=fun c W=>by
    ext i;dsimp only [fv0,ev0]
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    rw [← mul_assoc,mul_comm c,mul_assoc]
    congr 1;rw [Finset.mul_sum];refine Finset.sum_congr rfl fun j _=>?_
    split_ifs <;> ring }
 let T₂L:(Option (Fin n)->R) →ₗ[R] (Fin n->R) :=
  {
   toFun:=fun z i=>sqrt (((n:R) - 2)/(n:R))*z (some i)+(sqrt (n:R))⁻¹*z none
   map_add':=fun x y=>by ext i;simp;ring
   map_smul':=fun c x=>by ext i;simp;ring }
 let T₁:(Ei n->R) →L[R] (Fin n->R):=T₁L.toContinuousLinearMap
 let T₂:(Option (Fin n)->R) →L[R] (Fin n->R):=T₂L.toContinuousLinearMap
 have hlaw:(gE n).map T₁=(Measure.pi (fun _:Option (Fin n)=>N01)).map T₂:=by
  refine pi_gaussianReal_map_eq T₁ T₂ fun ξ=>?_
  have hL1:∀ e:Ei n,
    (∑ i:Fin n,ξ i*T₁ (Pi.single e 1) i)^2=(ξ e.1.1+ξ e.1.2)^2/(n:R):=by
   intro e
   have hterm:∀ i:Fin n,T₁ (Pi.single e 1) i =
     (sqrt (n:R))⁻¹*(spin s e.1.1*spin s e.1.2) *
      ((if i=e.1.1 then 1 else 0)+(if i=e.1.2 then 1 else 0)):=by
    intro i
    change (sqrt (n:R))⁻¹*∑ j:Fin n,ev0 (Pi.single e 1) i j*(spin s i*spin s j)=_
    simp_rw [edgeVal_single]
    by_cases h1:i=e.1.1
    .
     subst h1
     have hne:e.1.1 ≠ e.1.2:=e.2.ne
     have hsum:(∑ j:Fin n,(if (e.1.1=e.1.1/\j=e.1.2)\/(e.1.1=e.1.2/\j=e.1.1) then (1:R) else 0) *
       (spin s e.1.1*spin s j))=spin s e.1.1*spin s e.1.2:=by
      simp [hne]
     rw [hsum,if_pos rfl,if_neg hne];ring
    .
     by_cases h2:i=e.1.2
     .
      subst h2
      have hne:e.1.2 ≠ e.1.1:=e.2.ne'
      have hsum:(∑ j:Fin n,(if (e.1.2=e.1.1/\j=e.1.2)\/(e.1.2=e.1.2/\j=e.1.1) then (1:R) else 0) *
        (spin s e.1.2*spin s j))=spin s e.1.2*spin s e.1.1:=by
       simp [hne]
      rw [hsum,if_neg hne,if_pos rfl];ring
     .
      have hsum:(∑ j:Fin n,(if (i=e.1.1/\j=e.1.2)\/(i=e.1.2/\j=e.1.1) then (1:R) else 0) *
        (spin s i*spin s j))=0:=by simp [h1,h2]
      rw [hsum,if_neg h1,if_neg h2];ring
   have hsum_i:∑ i:Fin n,ξ i*T₁ (Pi.single e 1) i =
     (sqrt (n:R))⁻¹*(spin s e.1.1*spin s e.1.2)*(ξ e.1.1+ξ e.1.2):=by
    simp_rw [hterm]
    have:∀ i:Fin n,ξ i*((sqrt (n:R))⁻¹*(spin s e.1.1*spin s e.1.2) *
      ((if i=e.1.1 then 1 else 0)+(if i=e.1.2 then 1 else 0))) =
      (sqrt (n:R))⁻¹*(spin s e.1.1*spin s e.1.2) *
       ((if i=e.1.1 then ξ i else 0)+(if i=e.1.2 then ξ i else 0)):=fun i=>by
     split_ifs <;> ring
    simp_rw [this,← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
   rw [hsum_i,mul_pow,mul_pow,inv_pow,sq_sqrt hn_pos.le,spin_mul_sq,mul_one];ring
  have hpair_sum:2*∑ e:Ei n,(ξ e.1.1+ξ e.1.2)^2 =
    ∑ i:Fin n,∑ j:Fin n,(if i ≠ j then (ξ i+ξ j)^2 else 0):=by
   have h1:(∑ p:Fin n × Fin n,if p.1 < p.2 then (ξ p.1+ξ p.2)^2 else 0) =
     ∑ e:Ei n,(ξ e.1.1+ξ e.1.2)^2:=by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype (Finset.univ.filter fun p:Fin n × Fin n=>p.1 < p.2)
     (fun _=>by simp) (fun p:Fin n × Fin n=>(ξ p.1+ξ p.2)^2)
   have h2:(∑ p:Fin n × Fin n,if p.2 < p.1 then (ξ p.1+ξ p.2)^2 else 0) =
     ∑ p:Fin n × Fin n,if p.1 < p.2 then (ξ p.1+ξ p.2)^2 else 0:=by
    refine Fintype.sum_equiv (Equiv.prodComm (Fin n) (Fin n)) _ _ fun p=>?_
    simp [add_comm]
   have h3:(∑ p:Fin n × Fin n,if p.1 ≠ p.2 then (ξ p.1+ξ p.2)^2 else 0) =
     (∑ p:Fin n × Fin n,if p.1 < p.2 then (ξ p.1+ξ p.2)^2 else 0) +
     (∑ p:Fin n × Fin n,if p.2 < p.1 then (ξ p.1+ξ p.2)^2 else 0):=by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _=>?_
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    . simp [hlt,hlt.ne,not_lt.mpr hlt.le]
    . simp [heq]
    . simp [hgt,hgt.ne',not_lt.mpr hgt.le]
   rw [← Fintype.sum_prod_type',h3,h2,h1];ring
  have hfull:(∑ i:Fin n,∑ j:Fin n,if i ≠ j then (ξ i+ξ j)^2 else 0) =
    2*(((n:R) - 2)*∑ i:Fin n,ξ i^2+(∑ i:Fin n,ξ i)^2):=by
   have hdiag:∀ i:Fin n,(∑ j:Fin n,if i ≠ j then (ξ i+ξ j)^2 else 0) =
     (∑ j:Fin n,(ξ i+ξ j)^2) - 4*ξ i^2:=fun i=>by
    have:(∑ j:Fin n,(ξ i+ξ j)^2) =
      (∑ j:Fin n,if i ≠ j then (ξ i+ξ j)^2 else 0) +
      (∑ j:Fin n,if i=j then (ξ i+ξ j)^2 else 0):=by
     rw [← Finset.sum_add_distrib]
     refine Finset.sum_congr rfl fun j _=>by by_cases h:i=j <;> simp [h]
    have hd:(∑ j:Fin n,if i=j then (ξ i+ξ j)^2 else 0)=4*ξ i^2:=by
     simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte];ring
    linarith
   simp_rw [hdiag,Finset.sum_sub_distrib,← Finset.mul_sum]
   have hexp:∑ i:Fin n,∑ j:Fin n,(ξ i+ξ j)^2 =
     2*(n:R)*(∑ i:Fin n,ξ i^2)+2*(∑ i:Fin n,ξ i)^2:=by
    simp_rw [add_sq,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have h1:∑ i:Fin n,∑ j:Fin n,2*ξ i*ξ j=2*(∑ i:Fin n,ξ i)^2:=by
     simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul,sq]
    rw [h1,← Finset.mul_sum];ring
   rw [hexp];ring
  have hLHS:∑ e:Ei n,(∑ i:Fin n,ξ i*T₁ (Pi.single e 1) i)^2 =
    (((n:R) - 2)/(n:R))*(∑ i:Fin n,ξ i^2)+(∑ i:Fin n,ξ i)^2/(n:R):=by
   simp_rw [hL1,← Finset.sum_div]
   have hsum_e:∑ e:Ei n,(ξ e.1.1+ξ e.1.2)^2 =
     ((n:R) - 2)*∑ i:Fin n,ξ i^2+(∑ i:Fin n,ξ i)^2:=by linarith
   rw [hsum_e];ring
  have hRHS:∑ o:Option (Fin n),(∑ i:Fin n,ξ i*T₂ (Pi.single o 1) i)^2 =
    (((n:R) - 2)/(n:R))*(∑ i:Fin n,ξ i^2)+(∑ i:Fin n,ξ i)^2/(n:R):=by
   rw [Fintype.sum_option,add_comm]
   congr 1
   .
    have hterm:∀ k:Fin n,∑ i:Fin n,ξ i*T₂ (Pi.single (some k) 1) i =
      sqrt (((n:R) - 2)/(n:R))*ξ k:=fun k=>by
     have:∀ i:Fin n,T₂ (Pi.single (some k) 1) i=if i=k then sqrt (((n:R) - 2)/(n:R)) else 0:=fun i=>by
      change sqrt (((n:R) - 2)/(n:R))*(Pi.single (some k) (1:R):Option (Fin n)->R) (some i) +
       (sqrt (n:R))⁻¹*(Pi.single (some k) (1:R):Option (Fin n)->R) none=_
      simp [Pi.single_apply]
     simp_rw [this,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true];ring
    simp_rw [hterm,mul_pow,sq_sqrt hn2_pos.le,← Finset.mul_sum]
   .
    have:∀ i:Fin n,T₂ (Pi.single none 1) i=(sqrt (n:R))⁻¹:=fun i=>by
     change sqrt (((n:R) - 2)/(n:R))*(Pi.single none (1:R):Option (Fin n)->R) (some i) +
      (sqrt (n:R))⁻¹*(Pi.single none (1:R):Option (Fin n)->R) none=_
     simp
    simp_rw [this,← Finset.sum_mul,mul_pow,inv_pow,sq_sqrt hn_pos.le];ring
  rw [hLHS,hRHS]
 set S_pos:Set (Fin n->R):={y | ∀ i:Fin n,gC<=y i}
 have hS_meas:MeasurableSet S_pos:=by
  rw [show S_pos=⋂ i:Fin n,{y:Fin n->R | gC<=y i} by ext y;simp [S_pos]]
  exact MeasurableSet.iInter fun i=>measurableSet_le measurable_const (continuous_apply i).measurable
 have hmap:=congrArg (fun m:Measure (Fin n->R)=>m S_pos) hlaw
 rw [Measure.map_apply T₁.continuous.measurable hS_meas,
   Measure.map_apply T₂.continuous.measurable hS_meas] at hmap
 have hpre1:T₁ ⁻¹' S_pos=aF n s:=rfl
 rw [hpre1] at hmap
 set a0:R:=tStar*sqrt (n:R)
 set E_box:Set (Option (Fin n)->R) :=
  Set.univ.pi fun o:Option (Fin n) =>
   match o with
   | none=>Set.Icc a0 (a0+1)
   | some _=>Set.Ici (gC - tStar)
 have hsub:E_box ⊆ T₂ ⁻¹' S_pos:=by
  intro z hz i
  have hg:a0<=z none:=(hz none (Set.mem_univ _)).1
  have hzi:gC - tStar<=z (some i):=hz (some i) (Set.mem_univ _)
  change gC<=sqrt (((n:R) - 2)/(n:R))*z (some i)+(sqrt (n:R))⁻¹*z none
  have htStar_gt:gC < tStar:=by
   have ht:=tStar_mem;norm_num [gC,tLInt,S0,fpS] at ht ⊢;linarith
  have hsqrt_le:sqrt (((n:R) - 2)/(n:R))<=1:=by
   rw [sqrt_le_one];rw [div_le_one hn_pos];linarith
  have hterm1:gC - tStar<=sqrt (((n:R) - 2)/(n:R))*z (some i):=by
   by_cases hzs:0<=z (some i)
   . exact le_trans (by linarith) (mul_nonneg (sqrt_nonneg _) hzs)
   .
    have:sqrt (((n:R) - 2)/(n:R))*z (some i)>=1*z (some i):=by
     nlinarith [hsqrt_le]
    linarith
  have hterm2:tStar<=(sqrt (n:R))⁻¹*z none:=by
   have h1:=mlL hg (inv_nonneg.mpr (sqrt_nonneg (n:R)))
   have h2:(sqrt (n:R))⁻¹*a0=tStar:=by
    unfold a0;field_simp [(sqrt_pos.mpr hn_pos).ne']
   linarith
  linarith
 have hle_m:=measure_mono hsub (μ:=Measure.pi (fun _:Option (Fin n)=>N01))
 rw [← hmap] at hle_m
 have hpi:(Measure.pi (fun _:Option (Fin n)=>N01) E_box).toReal =
   (N01 (Set.Icc a0 (a0+1))).toReal*(pC (tStar - gC))^n:=by
  rw [Measure.pi_pi,ENNReal.toReal_prod,Fintype.prod_option]
  congr 1
  simp only [gaussianReal_Ici,neg_sub,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
 have hIcc_lb:(sqrt (2*PI)*exp (1/2))⁻¹*exp (-tStar*sqrt (n:R)) *
   exp (-(n:R)*tStar^2/2)<=(N01 (Set.Icc a0 (a0+1))).toReal:=by
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero (Set.Icc a0 (a0+1))]
  simp_rw [gaussianPDFReal_zero_one]
  rw [ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc fun x _=>pPn x)]
  have ha0_nn:0<=a0:=by
   have ht:=tStar_mem;norm_num [tLInt,S0,fpS] at ht
   exact mul_nonneg (by linarith) (sqrt_nonneg _)
  have hge:∀ x ∈ Set.Icc a0 (a0+1),pP (a0+1)<=pP x:=fun x hx=>by
   unfold pP
   exact mlL (exp_le_exp.mpr (by nlinarith [hx.1,hx.2])) (by positivity)
  have h1:=setIntegral_mono_on (integrableOn_const (hs:=measure_Icc_lt_top.ne))
   ipP.integrableOn measurableSet_Icc hge
  rw [setIntegral_const,Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (by norm_num:0<=a0+1 - a0),
    show a0+1 - a0=1 by ring,one_smul] at h1
  refine le_trans ?_ h1
  unfold pP
  have hexp_eq:exp (-(a0+1)^2/2) =
    exp (-(1/2))*exp (-tStar*sqrt (n:R))*exp (-(n:R)*tStar^2/2):=by
   rw [← exp_add,← exp_add]
   congr 1
   have hsq:a0^2=tStar^2*(n:R):=by unfold a0;rw [mul_pow,sq_sqrt hn_pos.le]
   linarith [show (a0+1)^2=a0^2+2*a0+1 by ring,hsq]
  rw [hexp_eq,exp_neg,mul_inv]
  ring_nf;exact le_rfl
 have htot:=ENNReal.toReal_mono (measure_ne_top _ _) hle_m
 rw [hpi] at htot
 refine le_trans ?_ htot
 have hgStar_exp:exp ((n:R)*gStar) =
   exp (-(n:R)*tStar^2/2)*(pC (tStar - gC))^n:=by
  unfold gStar
  have hlogn:exp ((n:R)*log (pC (tStar - gC))) =
    (pC (tStar - gC))^n:=by
   rw [exp_nat_mul,exp_log (pCp _)]
  rw [mul_add,exp_add,hlogn]
  congr 1;ring
 rw [hgStar_exp,← mul_assoc]
 exact mlR (by linarith [hIcc_lb]) (pow_nonneg (pCp _).le n)
lemma choose_central_lower (m:ℕ):(2:R)^(2*m)/((2*m:R)+1)<=((2*m).choose m:R):=by
 have hsum:∑ k ∈ Finset.range (2*m+1),(2*m).choose k=2^(2*m):=Nat.sum_range_choose (2*m)
 have hmax:∀ k ∈ Finset.range (2*m+1),(2*m).choose k<=(2*m).choose m:=fun k _=>by
  simpa [Nat.mul_div_cancel_left m (by norm_num:0 < 2)] using Nat.choose_le_middle k (2*m)
 have hle:2^(2*m)<=(2*m+1)*(2*m).choose m:=by
  calc 2^(2*m)=∑ k ∈ Finset.range (2*m+1),(2*m).choose k:=hsum.symm
   _ <= ∑ _k ∈ Finset.range (2*m+1),(2*m).choose m:=Finset.sum_le_sum hmax
   _ = (2*m+1)*(2*m).choose m:=by simp
 have hleR:(2:R)^(2*m)<=((2*m:R)+1)*((2*m).choose m:R):=by exact_mod_cast hle
 rwa [div_le_iff₀' (by positivity:(0:R) < (2*m:R)+1)]
open scoped Classical in
lemma first_moment_lower {m:ℕ} (hm:2<=m) :
  (sqrt (2*PI)*exp (1/2))⁻¹*((2*m:R)+1)⁻¹ *
   exp (-tStar*sqrt (2*m:R))*exp ((2*m:R)*(log 2+gStar)) <=
  ∫ W,friendlyCount m W ∂(gE (2*m)):=by
 have hmeas_s:∀ s:Finset (Fin (2*m)),MeasurableSet (aF (2*m) s):=fun s=>by
  rw [show aF (2*m) s=⋂ i:Fin (2*m),{W | gC<=fv0 (2*m) W s i} by
   ext W;simp [aF]]
  refine MeasurableSet.iInter fun i=>measurableSet_le measurable_const ?_
  have hc:Continuous (fun W:Ei (2*m)->R=>fv0 (2*m) W s i):=by
   unfold fv0;exact continuous_const.mul (continuous_finsetSum _ fun j _ => (continuous_edgeVal i j).mul continuous_const)
  exact hc.measurable
 have hint_s:∀ s:Finset (Fin (2*m)),
   Integrable (fun W=>if W ∈ aF (2*m) s then (1:R) else 0) (gE (2*m)):=fun s=>by
  have heq:(fun W=>if W ∈ aF (2*m) s then (1:R) else 0) =
    Set.indicator (aF (2*m) s) (fun _=>(1:R)):=by
   ext W;simp [Set.indicator]
  rw [heq]
  exact (integrable_const (1:R)).indicator (hmeas_s s)
 have hEq:∫ W,friendlyCount m W ∂(gE (2*m)) =
   ∑ s ∈ bS m,(gE (2*m) (aF (2*m) s)).toReal:=by
  unfold friendlyCount
  rw [integral_finsetSum _ fun s _=>hint_s s]
  refine Finset.sum_congr rfl fun s _=>?_
  have heq:(fun W=>if W ∈ aF (2*m) s then (1:R) else 0) =
    Set.indicator (aF (2*m) s) (1:(Ei (2*m)->R)->R):=by
   ext W;simp [Set.indicator]
  rw [heq,integral_indicator_one (hmeas_s s),Measure.real]
 rw [hEq]
 have hterm:=fun s:Finset (Fin (2*m))=>sBL (n:=2*m) (by omega) s
 have hsum_lb:((bS m).card:R) *
   ((sqrt (2*PI)*exp (1/2))⁻¹*exp (-tStar*sqrt (2*m:R)) *
    exp ((2*m:R)*gStar)) <=
   ∑ s ∈ bS m,(gE (2*m) (aF (2*m) s)).toReal:=by
  have h1:=Finset.sum_le_sum fun s (_:s ∈ bS m)=>hterm s
  simpa [Finset.sum_const,nsmul_eq_mul,Nat.cast_mul] using h1
 refine le_trans ?_ hsum_lb
 rw [card_bisections]
 have hch:=choose_central_lower m
 have hexp2:exp ((2*m:R)*(log 2+gStar)) =
   (2:R)^(2*m)*exp ((2*m:R)*gStar):=by
  rw [mul_add,exp_add,show (2*m:R)*log 2=((2*m:ℕ):R)*log 2 by push_cast;rfl,
    exp_nat_mul,exp_log (by norm_num)]
 rw [hexp2]
 have hpos_fac:0<=(sqrt (2*PI)*exp (1/2))⁻¹ *
   exp (-tStar*sqrt (2*m:R))*exp ((2*m:R)*gStar):=by positivity
 have h1:=mlR hch hpos_fac
 calc (sqrt (2*PI)*exp (1/2))⁻¹*((2*m:R)+1)⁻¹ *
    exp (-tStar*sqrt (2*m:R))*((2:R)^(2*m)*exp ((2*m:R)*gStar))
   = (2:R)^(2*m)/((2*m:R)+1) *
     ((sqrt (2*PI)*exp (1/2))⁻¹ *
      exp (-tStar*sqrt (2*m:R))*exp ((2*m:R)*gStar)):=by ring
  _ <= ((2*m).choose m:R) *
     ((sqrt (2*PI)*exp (1/2))⁻¹ *
      exp (-tStar*sqrt (2*m:R))*exp ((2*m:R)*gStar)):=h1
lemma choose_entropy_bound {m k:ℕ} (hk0:0 < k) (hkm:k < m) :
  (m.choose k:R) <=
   exp (-(k:R)*log ((k:R)/(m:R)) -
    ((m - k:ℕ):R)*log (((m - k:ℕ):R)/(m:R))):=by
 have hm_pos:(0:R) < (m:R):=by exact_mod_cast (by omega:0 < m)
 set p:R:=(k:R)/(m:R)
 set q:R:=((m - k:ℕ):R)/(m:R)
 have hp_pos:0 < p:=div_pos (by exact_mod_cast hk0) hm_pos
 have hq_pos:0 < q:=div_pos (by exact_mod_cast (by omega:0 < m - k)) hm_pos
 have hpq:p+q=1:=by
  unfold p q;rw [← add_div,← Nat.cast_add,Nat.add_sub_of_le hkm.le,div_self hm_pos.ne']
 have hsum:(1:R)=∑ j ∈ Finset.range (m+1),p^j*q^(m - j)*(m.choose j:R):=by
  rw [← add_pow,hpq,one_pow]
 have hterm:p^k*q^(m - k)*(m.choose k:R)<=1:=by
  rw [hsum]
  exact Finset.single_le_sum (f:=fun j=>p^j*q^(m - j)*(m.choose j:R))
   (fun j _=>by positivity) (Finset.mem_range.mpr (by omega:k < m+1))
 have hden_pos:0 < p^k*q^(m - k):=by positivity
 have hle:(m.choose k:R)<=(p^k*q^(m - k))⁻¹:=by
  have h1:=mlL hterm (inv_nonneg.mpr hden_pos.le)
  rwa [← mul_assoc,inv_mul_cancel₀ hden_pos.ne',one_mul,mul_one] at h1
 refine hle.trans_eq ?_
 rw [mul_inv,← exp_log (inv_pos.mpr (pow_pos hp_pos k)),
   ← exp_log (inv_pos.mpr (pow_pos hq_pos (m - k))),← exp_add,
   log_inv,log_inv,log_pow,log_pow]
 congr 1;ring
lemma bivProb_antitone {β:R} (hβ0:0 < β) (hβ1:β < 1) {c₁ c₂:R} (hc:c₁<=c₂) :
  bP β c₂<=bP β c₁:=by
 unfold bP
 have hsβ:0 < sqrt β:=sqrt_pos.mpr hβ0
 have hle:∫ u in Set.Ioi (0:R),pC ((sqrt (1 - β)*u+c₁)/sqrt β)*pP u <=
   ∫ u in Set.Ioi (0:R),pC ((sqrt (1 - β)*u+c₂)/sqrt β)*pP u :=
  setIntegral_mono_on (bivProb_integrand_integrable β c₁) (bivProb_integrand_integrable β c₂)
   measurableSet_Ioi fun u _ =>
    mlR
     (pCm.monotone (dld (by linarith) hsβ.le))
     (pPn u)
 linarith
noncomputable def pairFactor (n u:ℕ):R :=
 ∫ g,((N01).prod (N01)
  {z:R × R | gC - (sqrt (n:R))⁻¹*g <=
   sqrt (((u:R) - 2)/(n:R))*z.1 - sqrt (((n:R) - (u:R))/(n:R)) * |z.2|}).toReal^(u - 1)
  ∂(N01)
lemma pairFactor_nonneg (n u:ℕ):0<=pairFactor n u :=
 integral_nonneg fun _=>pow_nonneg ENNReal.toReal_nonneg _
set_option maxHeartbeats 800000 in
lemma pFU {n u:ℕ} (hn:8<=n) (hu0:4<=u) (hu1:u<=n - 4) :
  let β':R:=((u:R) - 2)/((n:R) - 2)
  let ρ:R:=2*β' - 1
  pairFactor n u <=
   7*sqrt (n:R)*exp (((n:R) - 2)*(gStar+aConst*ρ+bConst*ρ^3+β'*log (2*β'))):=by
 intro β' ρ
 have hn_pos:(0:R) < (n:R):=by exact_mod_cast (by omega:0 < n)
 have hn2_pos:(0:R) < (n:R) - 2:=by
  have:(8:R)<=(n:R):=by exact_mod_cast hn
  linarith
 have hu2_pos:(0:R) < (u:R) - 2:=by
  have:(4:R)<=(u:R):=by exact_mod_cast hu0
  linarith
 have hnu_pos:(0:R) < (n:R) - (u:R):=by
  have:(u:R)<=(n:R) - 4:=by
   have:(u+4:ℕ)<=n:=by omega
   have:((u+4:ℕ):R)<=(n:R):=by exact_mod_cast this
   push_cast at this;linarith
  linarith
 have hβ0:0 < β':=div_pos hu2_pos hn2_pos
 have hβ1:β' < 1:=by
  unfold β';rw [div_lt_one hn2_pos];linarith
 have h1mβ:1 - β'=((n:R) - (u:R))/((n:R) - 2):=by
  unfold β';field_simp [hn2_pos.ne'];ring
 have hρ0:-1 < ρ:=by unfold ρ;linarith
 have hρ1:ρ < 1:=by unfold ρ;linarith
 have h1ρ:(1+ρ)/2=β':=by unfold ρ;ring
 have h2β:1+ρ=2*β':=by unfold ρ;ring
 have hpt:∀ g:R,
   ((N01).prod (N01)
    {z:R × R | gC - (sqrt (n:R))⁻¹*g <=
     sqrt (((u:R) - 2)/(n:R))*z.1 - sqrt (((n:R) - (u:R))/(n:R)) * |z.2|}).toReal^(u - 1) <=
   (bP β' (gC - g/sqrt ((n:R) - 2)))^(u - 2):=by
  intro g
  set α:R:=sqrt (((n:R) - 2)/(n:R))
  have hα_pos:0 < α:=sqrt_pos.mpr (div_pos hn2_pos hn_pos)
  have hα_le1:α<=1:=by
   unfold α;rw [sqrt_le_one,div_le_one hn_pos];linarith
  have hset_eq :
    {z:R × R | gC - (sqrt (n:R))⁻¹*g <=
     sqrt (((u:R) - 2)/(n:R))*z.1 - sqrt (((n:R) - (u:R))/(n:R)) * |z.2|} =
    {z:R × R | gC / α - g/sqrt ((n:R) - 2) <=
     sqrt β'*z.1 - sqrt (1 - β') * |z.2|}:=by
   have h1:sqrt (((u:R) - 2)/(n:R))=α*sqrt β':=by
    unfold α β'
    rw [← sqrt_mul (div_nonneg hn2_pos.le hn_pos.le)]
    congr 1;field_simp [hn2_pos.ne']
   have h2:sqrt (((n:R) - (u:R))/(n:R))=α*sqrt (1 - β'):=by
    unfold α;rw [h1mβ,← sqrt_mul (div_nonneg hn2_pos.le hn_pos.le)]
    congr 1;field_simp [hn2_pos.ne']
   have h3:(sqrt (n:R))⁻¹*g=α*(g/sqrt ((n:R) - 2)):=by
    unfold α
    rw [sqrt_div hn2_pos.le]
    have hs1:sqrt (n:R) ≠ 0:=(sqrt_pos.mpr hn_pos).ne'
    have hs2:sqrt ((n:R) - 2) ≠ 0:=(sqrt_pos.mpr hn2_pos).ne'
    field_simp [hs1,hs2]
   ext z
   simp only [Set.mem_ofPred_eq,h1,h2,h3]
   constructor <;> intro h
   .
    have h':α*(gC / α - g/sqrt ((n:R) - 2))<=α*(sqrt β'*z.1 - sqrt (1 - β') * |z.2|):=by
     have hl:α*(gC / α - g/sqrt ((n:R) - 2))=gC - α*(g/sqrt ((n:R) - 2)):=by
      field_simp [hα_pos.ne']
     rw [hl];linarith
    exact le_of_mul_le_mul_left h' hα_pos
   .
    have h':=mlL h hα_pos.le
    have hl:α*(gC / α - g/sqrt ((n:R) - 2))=gC - α*(g/sqrt ((n:R) - 2)):=by
     field_simp [hα_pos.ne']
    rw [hl] at h';linarith
  rw [hset_eq,← bPg _ hβ0 hβ1]
  have hcg:gC - g/sqrt ((n:R) - 2)<=gC / α - g/sqrt ((n:R) - 2):=by
   have:gC<=gC / α:=by
    rw [le_div_iff₀ hα_pos]
    have:(0:R) < gC:=by norm_num [gC]
    nlinarith
   linarith
  have hb_le:bP β' (gC / α - g/sqrt ((n:R) - 2))<=bP β' (gC - g/sqrt ((n:R) - 2)) :=
   bivProb_antitone hβ0 hβ1 hcg
  have hb_pos:0 < bP β' (gC / α - g/sqrt ((n:R) - 2)):=bivProb_pos _ hβ0 hβ1
  have hb_le1:bP β' (gC - g/sqrt ((n:R) - 2))<=1 :=
   (bivProb_le_cdf _ hβ0 hβ1).trans (stdPhiCDF_lt_one _).le
  have hp1:=pow_le_pow_left₀ hb_pos.le hb_le (u - 1)
  have hp2:(bP β' (gC - g/sqrt ((n:R) - 2)))^(u - 1) <=
    (bP β' (gC - g/sqrt ((n:R) - 2)))^(u - 2) :=
   pow_le_pow_of_le_one (bivProb_pos _ hβ0 hβ1).le hb_le1 (by omega)
  exact hp1.trans hp2
 unfold pairFactor
 rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
 simp_rw [smul_eq_mul,gaussianPDFReal_zero_one]
 set F:R->R:=fun g=>pP g*(bP β' (gC - g/sqrt ((n:R) - 2)))^(u - 2)
 have hcont_biv:Continuous (fun c:R=>bP β' c):=by
  have h1:Continuous pC:=continuous_iff_continuousAt.mpr fun z=>(pCd z).continuousAt
  have h2:Continuous (fun c:R=>∫ u in Set.Ioi (0:R),pC ((sqrt (1 - β')*u+c)/sqrt β')*pP u):=by
   refine continuous_of_dominated (bound:=fun u=>pP u) ?_ ?_ ipP.integrableOn ?_
   . intro c;exact ((continuous_stdPhiCDF.comp (by fun_prop)).mul continuous_stdPhiPDF).aestronglyMeasurable
   .
    intro c;refine Eventually.of_forall fun u=>?_
    rw [Real.norm_eq_abs,aon (mul_nonneg (pCp _).le (pPn u))]
    nlinarith [stdPhiCDF_lt_one ((sqrt (1 - β')*u+c)/sqrt β'),pPn u]
   . refine Eventually.of_forall fun u=>by fun_prop
  unfold bP;fun_prop
 have hint_F:Integrable F:=by
  have hcont_F:Continuous F:=by
   have hpdf:Continuous pP:=by unfold pP;fun_prop
   unfold F;fun_prop
  refine ipP.mono hcont_F.aestronglyMeasurable (Eventually.of_forall fun g=>?_)
  have hb_nn:0<=bP β' (gC - g/sqrt ((n:R) - 2)):=(bivProb_pos _ hβ0 hβ1).le
  have hb_le1:bP β' (gC - g/sqrt ((n:R) - 2))<=1 :=
   (bivProb_le_cdf _ hβ0 hβ1).trans (stdPhiCDF_lt_one _).le
  rw [Real.norm_eq_abs,Real.norm_eq_abs,aon (mul_nonneg (pPn g) (pow_nonneg hb_nn _)),
    aon (pPn g)]
  exact mul_le_of_le_one_right (pPn g) (pow_le_one₀ hb_nn hb_le1)
 have hint_lhs:Integrable (fun g:R=>pP g *
   ((N01).prod (N01)
    {z:R × R | gC - (sqrt (n:R))⁻¹*g <=
     sqrt (((u:R) - 2)/(n:R))*z.1 - sqrt (((n:R) - (u:R))/(n:R)) * |z.2|}).toReal^(u - 1)):=by
  set α:R:=sqrt (((n:R) - 2)/(n:R))
  have hα_pos:0 < α:=sqrt_pos.mpr (div_pos hn2_pos hn_pos)
  have hfun_eq:(fun g:R=>((N01).prod (N01)
    {z:R × R | gC - (sqrt (n:R))⁻¹*g <=
     sqrt (((u:R) - 2)/(n:R))*z.1 - sqrt (((n:R) - (u:R))/(n:R)) * |z.2|}).toReal) =
    fun g:R=>bP β' (gC / α - g/sqrt ((n:R) - 2)):=by
   ext g
   rw [bPg _ hβ0 hβ1]
   congr 2;ext z
   have h1:sqrt (((u:R) - 2)/(n:R))=α*sqrt β':=by
    unfold α β';rw [← sqrt_mul (div_nonneg hn2_pos.le hn_pos.le)];congr 1;field_simp [hn2_pos.ne']
   have h2:sqrt (((n:R) - (u:R))/(n:R))=α*sqrt (1 - β'):=by
    unfold α;rw [h1mβ,← sqrt_mul (div_nonneg hn2_pos.le hn_pos.le)];congr 1;field_simp [hn2_pos.ne']
   have h3:(sqrt (n:R))⁻¹*g=α*(g/sqrt ((n:R) - 2)):=by
    unfold α;rw [sqrt_div hn2_pos.le]
    field_simp [(sqrt_pos.mpr hn_pos).ne',(sqrt_pos.mpr hn2_pos).ne']
   simp only [Set.mem_ofPred_eq,h1,h2,h3]
   constructor <;> intro h
   .
    have h':α*(gC / α - g/sqrt ((n:R) - 2))<=α*(sqrt β'*z.1 - sqrt (1 - β') * |z.2|):=by
     have hl:α*(gC / α - g/sqrt ((n:R) - 2))=gC - α*(g/sqrt ((n:R) - 2)):=by
      field_simp [hα_pos.ne']
     rw [hl];linarith
    exact le_of_mul_le_mul_left h' hα_pos
   .
    have h':=mlL h hα_pos.le
    have hl:α*(gC / α - g/sqrt ((n:R) - 2))=gC - α*(g/sqrt ((n:R) - 2)):=by
     field_simp [hα_pos.ne']
    rw [hl] at h';linarith
  have hpdf:Continuous pP:=by unfold pP;fun_prop
  have hcont:Continuous (fun g:R=>pP g*(bP β' (gC / α - g/sqrt ((n:R) - 2)))^(u - 1)):=by
   fun_prop
  have hsm:AEStronglyMeasurable (fun g:R=>pP g *
    ((N01).prod (N01)
     {z:R × R | gC - (sqrt (n:R))⁻¹*g <=
      sqrt (((u:R) - 2)/(n:R))*z.1 - sqrt (((n:R) - (u:R))/(n:R)) * |z.2|}).toReal^(u - 1)) volume:=by
   have:(fun g:R=>pP g *
     ((N01).prod (N01)
      {z:R × R | gC - (sqrt (n:R))⁻¹*g <=
       sqrt (((u:R) - 2)/(n:R))*z.1 - sqrt (((n:R) - (u:R))/(n:R)) * |z.2|}).toReal^(u - 1)) =
     fun g:R=>pP g*(bP β' (gC / α - g/sqrt ((n:R) - 2)))^(u - 1):=by
    ext g;rw [congrFun hfun_eq g]
   rw [this];exact hcont.aestronglyMeasurable
  refine ipP.mono hsm (Eventually.of_forall fun g=>?_)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,aon (mul_nonneg (pPn g) (pow_nonneg ENNReal.toReal_nonneg _)),
    aon (pPn g)]
  have hle1:((N01).prod (N01)
    {z:R × R | gC - (sqrt (n:R))⁻¹*g <=
     sqrt (((u:R) - 2)/(n:R))*z.1 - sqrt (((n:R) - (u:R))/(n:R)) * |z.2|}).toReal<=1:=by
   have h1:(N01).prod (N01)
     {z:R × R | gC - (sqrt (n:R))⁻¹*g <=
      sqrt (((u:R) - 2)/(n:R))*z.1 - sqrt (((n:R) - (u:R))/(n:R)) * |z.2|}<=1:=prob_le_one
   simpa using ENNReal.toReal_mono ENNReal.one_ne_top h1
  exact mul_le_of_le_one_right (pPn g) (pow_le_one₀ ENNReal.toReal_nonneg hle1)
 have hle_F:(∫ g:R,pP g *
   ((N01).prod (N01)
    {z:R × R | gC - (sqrt (n:R))⁻¹*g <=
     sqrt (((u:R) - 2)/(n:R))*z.1 - sqrt (((n:R) - (u:R))/(n:R)) * |z.2|}).toReal^(u - 1)) <=
   ∫ g:R,F g :=
  integral_mono hint_lhs hint_F fun g=>mlL (hpt g) (pPn g)
 set sN:R:=sqrt ((n:R) - 2)
 have hsN_pos:0 < sN:=sqrt_pos.mpr hn2_pos
 have hchg:∫ g:R,F g=sN*∫ t':R,F (sN*t'):=by
  have h:=Measure.integral_comp_mul_left F sN
  rw [abs_inv,abs_of_pos hsN_pos,smul_eq_mul] at h
  rw [h,← mul_assoc,mul_inv_cancel₀ hsN_pos.ne',one_mul]
 set G:R->R:=fun t'=>F (sN*t')
 have hint_G:Integrable G:=hint_F.comp_mul_left' hsN_pos.ne'
 have hsplit:∫ t':R,G t'=(∫ t' in Set.Icc (-3:R) 3,G t')+∫ t' in (Set.Icc (-3:R) 3)ᶜ,G t':=by
  rw [← setIntegral_union disjoint_compl_right measurableSet_Icc.compl hint_G.integrableOn hint_G.integrableOn,
    Set.union_compl_self,setIntegral_univ]
 set E_val:R:=exp (((n:R) - 2)*(gStar+aConst*ρ+bConst*ρ^3+β'*log (2*β')))
 have hmain:∫ t' in Set.Icc (-3:R) 3,G t'<=(6/sqrt (2*PI))*E_val:=by
  have hle_pt:∀ t' ∈ Set.Icc (-3:R) 3,G t'<=(sqrt (2*PI))⁻¹*E_val:=by
   intro t' _
   have hG_eq:G t'=(sqrt (2*PI))⁻¹ *
     exp (((n:R) - 2)*(-t'^2/2+β'*log (bP β' (gC - t')))):=by
    unfold G F pP
    rw [mul_div_cancel_left₀ t' hsN_pos.ne']
    have hbpos:=bivProb_pos (gC - t') hβ0 hβ1
    have hsq:(sN*t')^2=((n:R) - 2)*t'^2:=by
     unfold sN;rw [mul_pow,sq_sqrt hn2_pos.le]
    have hu2_eq:((u - 2:ℕ):R)=((n:R) - 2)*β':=by
     unfold β'
     rw [Nat.cast_sub (by omega:2<=u),Nat.cast_ofNat]
     field_simp [hn2_pos.ne']
    have harg:((n:R) - 2)*(β'*log (bP β' (gC - t'))) =
      ((u - 2:ℕ):R)*log (bP β' (gC - t')):=by
     rw [hu2_eq];ring
    rw [mul_assoc,hsq,mul_add,exp_add,harg,exp_nat_mul,exp_log hbpos]
    congr 2;ring
   rw [hG_eq]
   refine mlL (exp_le_exp.mpr ?_) (by positivity)
   have hm:=analytic_master (ρ:=ρ) (t:=t') hρ0 hρ1
   rw [h1ρ,h2β] at hm
   exact mlL (by linarith) hn2_pos.le
  have h1:=setIntegral_mono_on hint_G.integrableOn (integrableOn_const (hs:=measure_Icc_lt_top.ne))
   measurableSet_Icc hle_pt
  rw [setIntegral_const,Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (by norm_num),smul_eq_mul] at h1
  linarith [show ((3:R) - -3)*((sqrt (2*PI))⁻¹*E_val)=(6/sqrt (2*PI))*E_val by ring]
 have htail:∫ t' in (Set.Icc (-3:R) 3)ᶜ,G t'<=E_val:=by
  have hle_pt:∀ t' ∈ (Set.Icc (-3:R) 3)ᶜ,G t'<=exp (-(((n:R) - 3)*(9/2)))*pP t':=by
   intro t' ht'
   have ht_sq:9<=t'^2:=by
    simp only [Set.mem_compl_iff,Set.mem_Icc,not_and_or,not_le] at ht'
    rcases ht' with h1 | h2 <;> nlinarith
   have hG_le:G t'<=pP (sN*t'):=by
    unfold G F
    rw [mul_div_cancel_left₀ t' hsN_pos.ne']
    have hb_nn:0<=bP β' (gC - t'):=(bivProb_pos _ hβ0 hβ1).le
    have hb_le1:bP β' (gC - t')<=1:=(bivProb_le_cdf _ hβ0 hβ1).trans (stdPhiCDF_lt_one _).le
    exact mul_le_of_le_one_right (pPn _) (pow_le_one₀ hb_nn hb_le1)
   refine hG_le.trans ?_
   unfold pP
   have hsq:(sN*t')^2=((n:R) - 2)*t'^2:=by
    unfold sN;rw [mul_pow,sq_sqrt hn2_pos.le]
   rw [hsq,← mul_assoc,mul_comm (exp _),mul_assoc,← exp_add]
   refine mlL (exp_le_exp.mpr ?_) (by positivity)
   have hn3:(0:R)<=(n:R) - 3:=by
    have:(8:R)<=(n:R):=by exact_mod_cast hn
    linarith
   nlinarith
  have h1:=setIntegral_mono_on hint_G.integrableOn (ipP.const_mul _).integrableOn
   measurableSet_Icc.compl hle_pt
  have h2:∫ t' in (Set.Icc (-3:R) 3)ᶜ,exp (-(((n:R) - 3)*(9/2)))*pP t' <=
    exp (-(((n:R) - 3)*(9/2))):=by
   rw [integral_const_mul]
   have hle1:∫ t' in (Set.Icc (-3:R) 3)ᶜ,pP t'<=1:=by
    rw [← integral_stdPhiPDF_univ]
    exact setIntegral_le_integral ipP (Eventually.of_forall pPn)
   nlinarith [exp_pos (-(((n:R) - 3)*(9/2)))]
  refine (h1.trans h2).trans (exp_le_exp.mpr ?_)
  have hg:=gStar_ge_gLoVal
  have ha:=aConst_bounds
  have hg_num:(-52/100:R)<=gStar:=by norm_num [gLoVal,S0,fpS] at hg;linarith
  have ha_lo:(-75/100:R)<=aConst:=by norm_num [aLoVal,S0,fpS] at ha;linarith
  have ha_hi:aConst<=0:=by norm_num [aHiVal,S0,fpS] at ha;linarith
  have hblog:-2/5<=β'*log (2*β'):=by
   have h:=neg_mul_log_le_inv_exp (show 0 < 2*β' by positivity)
   linarith [inv_exp_lt_two_fifths]
  have hrhs_ge:(-2:R)<=gStar+aConst*ρ+bConst*ρ^3+β'*log (2*β'):=by
   have hb_eq:bConst=3/25:=rfl
   have hρ3:-1<=ρ^3:=by nlinarith [sq_nonneg ρ]
   have haρ:(-75/100:R)<=aConst*ρ:=by
    by_cases h0:0<=ρ
    . nlinarith
    . have:0<=aConst*ρ:=mul_nonneg_of_nonpos_of_nonpos ha_hi (le_of_not_ge h0);linarith
   nlinarith [hb_eq,hρ3,haρ,hg_num,hblog]
  have hn8:(8:R)<=(n:R):=by exact_mod_cast hn
  nlinarith
 have hsqrt_le:sN<=sqrt (n:R):=sqrt_le_sqrt (by linarith)
 have hpi_ge:(1:R)<=sqrt (2*PI):=by
  rw [le_sqrt (by norm_num) (by positivity)];linarith [pi_gt_three]
 have h6_le:6/sqrt (2*PI)<=6:=by
  rw [div_le_iff₀ (by positivity)];linarith
 have hE_nn:0<=E_val:=exp_nonneg _
 have htot:∫ t':R,G t'<=7*E_val:=by rw [hsplit];nlinarith
 calc _ <= ∫ g:R,F g:=hle_F
  _ = sN*∫ t':R,G t':=hchg
  _ <= sN*(7*E_val):=mlL htot hsN_pos.le
  _ <= sqrt (n:R)*(7*E_val):=mlR hsqrt_le (by positivity)
  _ = 7*sqrt (n:R)*E_val:=by ring
private noncomputable def pairT1L {n u v:ℕ} (s:Finset (Fin n))
  {U V:Finset (Fin n)} (eU:Fin u ≃ {i:Fin n // i ∈ U}) (eV:Fin v ≃ {i:Fin n // i ∈ V}) :
  (Ei n->R) →ₗ[R] (((Fin u ⊕ Fin v) ⊕ (Fin u ⊕ Fin v))->R) where
 toFun W q:=match q with
  | .inl (.inl i)=>(sqrt (n:R))⁻¹*∑ k:Fin u,ev0 W (eU i).1 (eU k).1*(spin s (eU i).1*spin s (eU k).1)
  | .inl (.inr j)=>(sqrt (n:R))⁻¹*∑ l:Fin v,ev0 W (eV j).1 (eV l).1*(spin s (eV j).1*spin s (eV l).1)
  | .inr (.inl i)=>(sqrt (n:R))⁻¹*∑ l:Fin v,ev0 W (eU i).1 (eV l).1*(spin s (eU i).1*spin s (eV l).1)
  | .inr (.inr j)=>(sqrt (n:R))⁻¹*∑ k:Fin u,ev0 W (eV j).1 (eU k).1*(spin s (eV j).1*spin s (eU k).1)
 map_add' W₁ W₂:=by
  ext q;rcases q with (i | j) | (i | j) <;>
  .
   dsimp only;unfold ev0;simp only [Pi.add_apply]
   rw [← mul_add,← Finset.sum_add_distrib];congr 1
   refine Finset.sum_congr rfl fun _ _=>?_;split_ifs <;> ring
 map_smul' r W:=by
  ext q;rcases q with (i | j) | (i | j) <;>
  .
   dsimp only;unfold ev0;simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
   rw [← mul_assoc,mul_comm r,mul_assoc];congr 1;rw [Finset.mul_sum]
   refine Finset.sum_congr rfl fun _ _=>?_;split_ifs <;> ring
private noncomputable def pairT2L (n u v:ℕ) :
  ((((Fin u ⊕ Unit) ⊕ (Fin v ⊕ Unit)) ⊕ ((Fin u ⊕ Fin v) ⊕ Unit))->R) →ₗ[R]
  (((Fin u ⊕ Fin v) ⊕ (Fin u ⊕ Fin v))->R) where
 toFun Z q:=match q with
  | .inl (.inl i)=>sqrt (((u:R) - 2)/(n:R))*Z (.inl (.inl (.inl i)))+(sqrt (n:R))⁻¹*Z (.inl (.inl (.inr ())))
  | .inl (.inr j)=>sqrt (((v:R) - 2)/(n:R))*Z (.inl (.inr (.inl j)))+(sqrt (n:R))⁻¹*Z (.inl (.inr (.inr ())))
  | .inr (.inl i)=>sqrt ((v:R)/(n:R))*(Z (.inr (.inl (.inl i))) - (∑ k:Fin u,Z (.inr (.inl (.inl k))))/(u:R)) +
    (sqrt ((u:R)*(v:R)/(n:R))/(u:R))*Z (.inr (.inr ()))
  | .inr (.inr j)=>sqrt ((u:R)/(n:R))*(Z (.inr (.inl (.inr j))) - (∑ l:Fin v,Z (.inr (.inl (.inr l))))/(v:R)) +
    (sqrt ((u:R)*(v:R)/(n:R))/(v:R))*Z (.inr (.inr ()))
 map_add' X Y:=by
  ext q;rcases q with (i | j) | (i | j)
  . simp;ring
  . simp;ring
  . simp [Finset.sum_add_distrib,add_div];ring
  . simp [Finset.sum_add_distrib,add_div];ring
 map_smul' r X:=by
  ext q;rcases q with (i | j) | (i | j)
  . simp;ring
  . simp;ring
  . simp [← Finset.mul_sum,mul_div_assoc];ring
  . simp [← Finset.mul_sum,mul_div_assoc];ring
set_option maxHeartbeats 800000 in
private lemma pGL {n u v:ℕ} (hn_ge8:8<=n) (hu_ge4:4<=u) (hv_ge4:4<=v)
  (s:Finset (Fin n)) {U V:Finset (Fin n)}
  (hdisj:Disjoint U V) (hun:U ∪ V=Finset.univ)
  (eU:Fin u ≃ {i:Fin n // i ∈ U}) (eV:Fin v ≃ {i:Fin n // i ∈ V}) :
  (gE n).map (pairT1L s eU eV).toContinuousLinearMap =
   (Measure.pi (fun _:((Fin u ⊕ Unit) ⊕ (Fin v ⊕ Unit)) ⊕ ((Fin u ⊕ Fin v) ⊕ Unit)=>N01)).map
    (pairT2L n u v).toContinuousLinearMap:=by
 have hn_pos:(0:R) < (n:R):=by exact_mod_cast (by omega:0 < n)
 have hu_pos:(0:R) < (u:R):=by exact_mod_cast (by omega:0 < u)
 have hv_pos:(0:R) < (v:R):=by exact_mod_cast (by omega:0 < v)
 have hnotU_V:∀ x:Fin n,x ∉ U->x ∈ V:=fun x hx=>by
  have:x ∈ U ∪ V:=by rw [hun];exact Finset.mem_univ x
  exact (Finset.mem_union.mp this).resolve_left hx
 have hU_notV:∀ x:Fin n,x ∈ U->x ∉ V:=fun x hx hvx=>Finset.disjoint_left.mp hdisj hx hvx
 have hsum_UV:∀ (f:Fin n->R),∑ w:Fin n,f w=(∑ k:Fin u,f (eU k).1)+∑ l:Fin v,f (eV l).1:=by
  intro f
  rw [← hun,Finset.sum_union hdisj]
  congr 1
  .
   rw [← Finset.sum_attach U f]
   exact (Fintype.sum_equiv eU (fun k=>f (eU k).1) (fun x:{i // i ∈ U}=>f x.1) fun _=>rfl).symm
  .
   rw [← Finset.sum_attach V f]
   exact (Fintype.sum_equiv eV (fun l=>f (eV l).1) (fun x:{i // i ∈ V}=>f x.1) fun _=>rfl).symm
 let κ:=(Fin u ⊕ Fin v) ⊕ (Fin u ⊕ Fin v)
 let ι:=((Fin u ⊕ Unit) ⊕ (Fin v ⊕ Unit)) ⊕ ((Fin u ⊕ Fin v) ⊕ Unit)
 let T₁:=(pairT1L s eU eV).toContinuousLinearMap
 let T₂:=(pairT2L n u v).toContinuousLinearMap
 refine pi_gaussianReal_map_eq T₁ T₂ fun ξ=>?_
 set ξa:Fin u->R:=fun i=>ξ (.inl (.inl i))
 set ξc:Fin v->R:=fun j=>ξ (.inl (.inr j))
 set ξb:Fin u->R:=fun i=>ξ (.inr (.inl i))
 set ξd:Fin v->R:=fun j=>ξ (.inr (.inr j))
 have hLHS:∑ e:Ei n,(∑ q:κ,ξ q*T₁ (Pi.single e 1) q)^2 =
   (((u:R) - 2)/(n:R)*∑ i:Fin u,ξa i^2+(∑ i:Fin u,ξa i)^2/(n:R)) +
   (((v:R) - 2)/(n:R)*∑ j:Fin v,ξc j^2+(∑ j:Fin v,ξc j)^2/(n:R)) +
   ((v:R)/(n:R)*∑ i:Fin u,ξb i^2+(u:R)/(n:R)*∑ j:Fin v,ξd j^2 +
    2*(∑ i:Fin u,ξb i)*(∑ j:Fin v,ξd j)/(n:R)):=by
  let gPair:Fin n->Fin n->R:=fun p q =>
   if hp:p ∈ U then
    if hq:q ∈ U then (ξa (eU.symm ⟨p,hp⟩)+ξa (eU.symm ⟨q,hq⟩))^2/(n:R)
    else (ξb (eU.symm ⟨p,hp⟩)+ξd (eV.symm ⟨q,hnotU_V q hq⟩))^2/(n:R)
   else
    if hq:q ∈ U then (ξb (eU.symm ⟨q,hq⟩)+ξd (eV.symm ⟨p,hnotU_V p hp⟩))^2/(n:R)
    else (ξc (eV.symm ⟨p,hnotU_V p hp⟩)+ξc (eV.symm ⟨q,hnotU_V q hq⟩))^2/(n:R)
  have hterm_e:∀ e:Ei n,(∑ q:κ,ξ q*T₁ (Pi.single e 1) q)^2=gPair e.1.1 e.1.2:=by
   intro e
   have hsum_q:∑ q:κ,ξ q*T₁ (Pi.single e 1) q =
     (∑ i:Fin u,ξa i*T₁ (Pi.single e 1) (.inl (.inl i))) +
     (∑ j:Fin v,ξc j*T₁ (Pi.single e 1) (.inl (.inr j))) +
     ((∑ i:Fin u,ξb i*T₁ (Pi.single e 1) (.inr (.inl i))) +
      (∑ j:Fin v,ξd j*T₁ (Pi.single e 1) (.inr (.inr j)))):=by
    simp only [κ,Fintype.sum_sum_type];rfl
   rw [hsum_q]
   have hbilin:∀ {a b:ℕ} (f:Fin a->Fin n) (g:Fin b->Fin n) (hf:Function.Injective f) (hg:Function.Injective g)
     (w:Fin a->R),
     (∑ i:Fin a,w i*((sqrt (n:R))⁻¹*∑ j:Fin b,ev0 (Pi.single e 1) (f i) (g j)*(spin s (f i)*spin s (g j)))) =
     (sqrt (n:R))⁻¹*(spin s e.1.1*spin s e.1.2) *
      ((∑ i:Fin a,if f i=e.1.1/\∃ j,g j=e.1.2 then w i else 0) +
       (∑ i:Fin a,if f i=e.1.2/\∃ j,g j=e.1.1 then w i else 0)):=by
    intro a b f g hf hg w
    have he12:e.1.1 ≠ e.1.2:=e.2.ne
    have he21:e.1.2 ≠ e.1.1:=e.2.ne'
    have hinner:∀ i:Fin a,
      ∑ j:Fin b,ev0 (Pi.single e 1) (f i) (g j)*(spin s (f i)*spin s (g j)) =
      (spin s e.1.1*spin s e.1.2) *
       ((if f i=e.1.1/\∃ j,g j=e.1.2 then (1:R) else 0) +
        (if f i=e.1.2/\∃ j,g j=e.1.1 then (1:R) else 0)):=by
     intro i
     simp_rw [edgeVal_single]
     by_cases h1:f i=e.1.1
     .
      have h12:f i ≠ e.1.2:=by rw [h1];exact he12
      by_cases hex:∃ j:Fin b,g j=e.1.2
      .
       obtain ⟨j0,hj0⟩:=hex
       have hsum:∑ j:Fin b,(if (f i=e.1.1/\g j=e.1.2)\/(f i=e.1.2/\g j=e.1.1) then (1:R) else 0) *
         (spin s (f i)*spin s (g j))=spin s e.1.1*spin s e.1.2:=by
        rw [Finset.sum_eq_single j0]
        . simp [h1,hj0]
        .
         intro j _ hj;have:g j ≠ e.1.2:=fun heq=>hj (hg (heq.trans hj0.symm))
         simp [h1,h12,this,he12]
        . intro h;exact absurd (Finset.mem_univ j0) h
       rw [hsum,if_pos ⟨h1,j0,hj0⟩,if_neg (by simp [h12])];ring
      .
       have hsum:∑ j:Fin b,(if (f i=e.1.1/\g j=e.1.2)\/(f i=e.1.2/\g j=e.1.1) then (1:R) else 0) *
         (spin s (f i)*spin s (g j))=0 :=
        Finset.sum_eq_zero fun j _=>by have:g j ≠ e.1.2:=fun h=>hex ⟨j,h⟩;simp [h1,h12,this,he12]
       rw [hsum,if_neg (by simp [hex]),if_neg (by simp [h12])];ring
     .
      by_cases h2:f i=e.1.2
      .
       by_cases hex:∃ j:Fin b,g j=e.1.1
       .
        obtain ⟨j0,hj0⟩:=hex
        have hsum:∑ j:Fin b,(if (f i=e.1.1/\g j=e.1.2)\/(f i=e.1.2/\g j=e.1.1) then (1:R) else 0) *
          (spin s (f i)*spin s (g j))=spin s e.1.2*spin s e.1.1:=by
         rw [Finset.sum_eq_single j0]
         . simp [h2,hj0]
         .
          intro j _ hj;have:g j ≠ e.1.1:=fun heq=>hj (hg (heq.trans hj0.symm))
          simp [h1,h2,this,he21]
         . intro h;exact absurd (Finset.mem_univ j0) h
        rw [hsum,if_neg (by simp [h1]),if_pos ⟨h2,j0,hj0⟩];ring
       .
        have hsum:∑ j:Fin b,(if (f i=e.1.1/\g j=e.1.2)\/(f i=e.1.2/\g j=e.1.1) then (1:R) else 0) *
          (spin s (f i)*spin s (g j))=0 :=
         Finset.sum_eq_zero fun j _=>by have:g j ≠ e.1.1:=fun h=>hex ⟨j,h⟩;simp [h1,h2,this,he21]
        rw [hsum,if_neg (by simp [h1]),if_neg (by simp [hex])];ring
      .
       have hsum:∑ j:Fin b,(if (f i=e.1.1/\g j=e.1.2)\/(f i=e.1.2/\g j=e.1.1) then (1:R) else 0) *
         (spin s (f i)*spin s (g j))=0:=Finset.sum_eq_zero fun j _=>by simp [h1,h2]
       rw [hsum,if_neg (by simp [h1]),if_neg (by simp [h2])];ring
    simp_rw [hinner]
    have hrew:∀ i:Fin a,w i*((sqrt (n:R))⁻¹*((spin s e.1.1*spin s e.1.2) *
      ((if f i=e.1.1/\∃ j,g j=e.1.2 then (1:R) else 0) +
       (if f i=e.1.2/\∃ j,g j=e.1.1 then (1:R) else 0)))) =
      (sqrt (n:R))⁻¹*(spin s e.1.1*spin s e.1.2) *
       ((if f i=e.1.1/\∃ j,g j=e.1.2 then w i else 0) +
        (if f i=e.1.2/\∃ j,g j=e.1.1 then w i else 0)):=fun i=>by split_ifs <;> ring
    simp_rw [hrew,← Finset.mul_sum,Finset.sum_add_distrib]
   have hfU:Function.Injective (fun k:Fin u=>(eU k).1):=Subtype.val_injective.comp eU.injective
   have hfV:Function.Injective (fun l:Fin v=>(eV l).1):=Subtype.val_injective.comp eV.injective
   have hmemU:∀ x:Fin n,(∃ k:Fin u,(eU k).1=x) ↔ x ∈ U:=fun x =>
    ⟨fun ⟨k,hk⟩=>hk ▸ (eU k).2,fun hx=>⟨eU.symm ⟨x,hx⟩,by simp⟩⟩
   have hmemV:∀ x:Fin n,(∃ l:Fin v,(eV l).1=x) ↔ x ∈ V:=fun x =>
    ⟨fun ⟨l,hl⟩=>hl ▸ (eV l).2,fun hx=>⟨eV.symm ⟨x,hx⟩,by simp⟩⟩
   have hsum_single_U:∀ (x:Fin n) (hx:x ∈ U) (w:Fin u->R),
     (∑ k:Fin u,if (eU k).1=x then w k else 0)=w (eU.symm ⟨x,hx⟩):=fun x hx w=>by
    rw [Finset.sum_eq_single (eU.symm ⟨x,hx⟩)]
    . simp
    .
     intro k _ hk;have:(eU k).1 ≠ x:=fun h=>hk (eU.injective (Subtype.ext (by simpa using h)))
     simp [this]
    . intro h;exact absurd (Finset.mem_univ _) h
   have hsum_single_V:∀ (x:Fin n) (hx:x ∈ V) (w:Fin v->R),
     (∑ l:Fin v,if (eV l).1=x then w l else 0)=w (eV.symm ⟨x,hx⟩):=fun x hx w=>by
    rw [Finset.sum_eq_single (eV.symm ⟨x,hx⟩)]
    . simp
    .
     intro l _ hl;have:(eV l).1 ≠ x:=fun h=>hl (eV.injective (Subtype.ext (by simpa using h)))
     simp [this]
    . intro h;exact absurd (Finset.mem_univ _) h
   have hsum_zero_U:∀ (x:Fin n) (hx:x ∉ U) (w:Fin u->R),
     (∑ k:Fin u,if (eU k).1=x then w k else 0)=0:=fun x hx w =>
    Finset.sum_eq_zero fun k _=>if_neg (fun (h:(eU k).1=x)=>hx (h ▸ (eU k).2))
   have hsum_zero_V:∀ (x:Fin n) (hx:x ∉ V) (w:Fin v->R),
     (∑ l:Fin v,if (eV l).1=x then w l else 0)=0:=fun x hx w =>
    Finset.sum_eq_zero fun l _=>if_neg (fun (h:(eV l).1=x)=>hx (h ▸ (eV l).2))
   dsimp only [T₁,pairT1L,LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,AddHom.coe_mk,gPair]
   rw [hbilin _ _ hfU hfU ξa,hbilin _ _ hfV hfV ξc,hbilin _ _ hfU hfV ξb,hbilin _ _ hfV hfU ξd]
   simp_rw [hmemU,hmemV]
   have hsq_fac:∀ c:R,((sqrt (n:R))⁻¹*(spin s e.1.1*spin s e.1.2)*c)^2=c^2/(n:R):=fun c=>by
    rw [mul_pow,mul_pow,inv_pow,sq_sqrt hn_pos.le,spin_mul_sq,mul_one];ring
   by_cases hp:e.1.1 ∈ U <;> by_cases hq:e.1.2 ∈ U
   .
    simp only [hp,hq,hU_notV _ hp,hU_notV _ hq,and_true,and_false,dif_pos,dif_neg,↓reduceIte,
     Finset.sum_const_zero,add_zero,zero_add,mul_zero,
     hsum_single_U _ hp,hsum_single_U _ hq,hsum_zero_V _ (hU_notV _ hp),hsum_zero_V _ (hU_notV _ hq)]
    exact hsq_fac _
   .
    have hqv:=hnotU_V _ hq
    simp only [hp,hq,hqv,hU_notV _ hp,and_true,and_false,dif_pos,dif_neg,↓reduceIte,
     Finset.sum_const_zero,add_zero,zero_add,mul_zero,
     hsum_single_U _ hp,hsum_single_V _ hqv,hsum_zero_U _ hq,hsum_zero_V _ (hU_notV _ hp)]
    rw [← mul_add];exact hsq_fac _
   .
    have hpv:=hnotU_V _ hp
    simp only [hp,hq,hpv,hU_notV _ hq,and_true,and_false,dif_pos,dif_neg,↓reduceIte,
     Finset.sum_const_zero,add_zero,zero_add,mul_zero,
     hsum_single_U _ hq,hsum_single_V _ hpv,hsum_zero_U _ hp,hsum_zero_V _ (hU_notV _ hq)]
    rw [← mul_add];exact hsq_fac _
   .
    have hpv:=hnotU_V _ hp;have hqv:=hnotU_V _ hq
    simp only [hp,hq,hpv,hqv,and_true,and_false,dif_pos,dif_neg,↓reduceIte,
     Finset.sum_const_zero,add_zero,zero_add,mul_zero,
     hsum_single_V _ hpv,hsum_single_V _ hqv,hsum_zero_U _ hp,hsum_zero_U _ hq]
    exact hsq_fac _
  have hgPair_symm:∀ p q:Fin n,gPair p q=gPair q p:=fun p q=>by
   dsimp only [gPair]
   by_cases hp:p ∈ U <;> by_cases hq:q ∈ U
   . rw [dif_pos hp,dif_pos hq,dif_pos hq,dif_pos hp];ring
   . rw [dif_pos hp,dif_neg hq,dif_neg hq,dif_pos hp]
   . rw [dif_neg hp,dif_pos hq,dif_pos hq,dif_neg hp]
   . rw [dif_neg hp,dif_neg hq,dif_neg hq,dif_neg hp];ring
  have hdouble:2*∑ e:Ei n,(∑ q:κ,ξ q*T₁ (Pi.single e 1) q)^2 =
    ∑ p:Fin n,∑ q:Fin n,if p ≠ q then gPair p q else 0:=by
   have h1:(∑ p:Fin n × Fin n,if p.1 < p.2 then gPair p.1 p.2 else 0) =
     ∑ e:Ei n,(∑ q:κ,ξ q*T₁ (Pi.single e 1) q)^2:=by
    rw [← Finset.sum_filter]
    have hsub:∑ p ∈ Finset.univ.filter (fun p:Fin n × Fin n=>p.1 < p.2),gPair p.1 p.2 =
      ∑ e:Ei n,gPair e.1.1 e.1.2 :=
     Finset.sum_subtype (Finset.univ.filter fun p:Fin n × Fin n=>p.1 < p.2)
      (fun _=>by simp) (fun p:Fin n × Fin n=>gPair p.1 p.2)
    rw [hsub]
    exact Finset.sum_congr rfl fun e _=>(hterm_e e).symm
   have h2:(∑ p:Fin n × Fin n,if p.2 < p.1 then gPair p.1 p.2 else 0) =
     ∑ p:Fin n × Fin n,if p.1 < p.2 then gPair p.1 p.2 else 0 :=
    Fintype.sum_equiv (Equiv.prodComm (Fin n) (Fin n)) _ _ fun p=>by
     dsimp only [Equiv.prodComm_apply,Prod.fst_swap,Prod.snd_swap]
     rw [hgPair_symm p.1 p.2]
     rfl
   have h3:(∑ p:Fin n × Fin n,if p.1 ≠ p.2 then gPair p.1 p.2 else 0) =
     (∑ p:Fin n × Fin n,if p.1 < p.2 then gPair p.1 p.2 else 0) +
     (∑ p:Fin n × Fin n,if p.2 < p.1 then gPair p.1 p.2 else 0):=by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _=>?_
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    . simp [hlt,hlt.ne,not_lt.mpr hlt.le]
    . simp [heq]
    . simp [hgt,hgt.ne',not_lt.mpr hgt.le]
   rw [← Fintype.sum_prod_type',h3,h2,h1];ring
  have hquad_block:∀ {k:ℕ} (w:Fin k->R),
    (∑ i:Fin k,∑ j:Fin k,if i ≠ j then (w i+w j)^2 else 0) =
    2*(((k:R) - 2)*∑ i:Fin k,w i^2+(∑ i:Fin k,w i)^2):=by
   intro k w
   have hdiag:∀ i:Fin k,(∑ j:Fin k,if i ≠ j then (w i+w j)^2 else 0) =
     (∑ j:Fin k,(w i+w j)^2) - 4*w i^2:=fun i=>by
    have:(∑ j:Fin k,(w i+w j)^2) =
      (∑ j:Fin k,if i ≠ j then (w i+w j)^2 else 0) +
      (∑ j:Fin k,if i=j then (w i+w j)^2 else 0):=by
     rw [← Finset.sum_add_distrib]
     exact Finset.sum_congr rfl fun j _=>by by_cases h:i=j <;> simp [h]
    have hd:(∑ j:Fin k,if i=j then (w i+w j)^2 else 0)=4*w i^2:=by
     simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte];ring
    linarith
   simp_rw [hdiag,Finset.sum_sub_distrib,← Finset.mul_sum]
   have hexp:∑ i:Fin k,∑ j:Fin k,(w i+w j)^2 =
     2*(k:R)*(∑ i:Fin k,w i^2)+2*(∑ i:Fin k,w i)^2:=by
    simp_rw [add_sq,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have h1:∑ i:Fin k,∑ j:Fin k,2*w i*w j=2*(∑ i:Fin k,w i)^2:=by
     simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul,sq]
    rw [h1,← Finset.mul_sum];ring
   rw [hexp];ring
  have hcross_block:∑ i:Fin u,∑ j:Fin v,(ξb i+ξd j)^2 =
    (v:R)*∑ i:Fin u,ξb i^2+(u:R)*∑ j:Fin v,ξd j^2 +
     2*(∑ i:Fin u,ξb i)*(∑ j:Fin v,ξd j):=by
   simp_rw [add_sq,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
   have h1:∑ i:Fin u,∑ j:Fin v,2*ξb i*ξd j=2*(∑ i:Fin u,ξb i)*(∑ j:Fin v,ξd j):=by
    simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul]
   rw [h1,← Finset.mul_sum];ring
  have hUV_ne:∀ (i:Fin u) (j:Fin v),(eU i).1 ≠ (eV j).1:=fun i j h =>
   Finset.disjoint_left.mp hdisj (eU i).2 (h ▸ (eV j).2)
  have hV_notU:∀ j:Fin v,(eV j).1 ∉ U:=fun j h =>
   Finset.disjoint_left.mp hdisj h (eV j).2
  have hfull_eq:(∑ p:Fin n,∑ q:Fin n,if p ≠ q then gPair p q else 0) =
    (∑ i:Fin u,∑ k:Fin u,if i ≠ k then (ξa i+ξa k)^2 else 0)/(n:R) +
    (∑ j:Fin v,∑ l:Fin v,if j ≠ l then (ξc j+ξc l)^2 else 0)/(n:R) +
    2*(∑ i:Fin u,∑ j:Fin v,(ξb i+ξd j)^2)/(n:R):=by
   rw [hsum_UV]
   simp_rw [hsum_UV,Finset.sum_add_distrib]
   have hUU:(∑ i:Fin u,∑ k:Fin u,if (eU i).1 ≠ (eU k).1 then gPair (eU i).1 (eU k).1 else 0) =
     (∑ i:Fin u,∑ k:Fin u,if i ≠ k then (ξa i+ξa k)^2 else 0)/(n:R):=by
    rw [Finset.sum_div];refine Finset.sum_congr rfl fun i _=>?_
    rw [Finset.sum_div];refine Finset.sum_congr rfl fun k _=>?_
    have hne:((eU i).1 ≠ (eU k).1) ↔ (i ≠ k) :=
     not_congr ⟨fun h=>eU.injective (Subtype.ext h),fun h=>by rw [h]⟩
    by_cases hik:i ≠ k
    .
     rw [if_pos (hne.mpr hik),if_pos hik];dsimp only [gPair]
     simp only [dif_pos (eU i).2,dif_pos (eU k).2,Subtype.coe_eta,Equiv.symm_apply_apply]
    . rw [if_neg (mt hne.mp hik),if_neg hik,zero_div]
   have hVV:(∑ j:Fin v,∑ l:Fin v,if (eV j).1 ≠ (eV l).1 then gPair (eV j).1 (eV l).1 else 0) =
     (∑ j:Fin v,∑ l:Fin v,if j ≠ l then (ξc j+ξc l)^2 else 0)/(n:R):=by
    rw [Finset.sum_div];refine Finset.sum_congr rfl fun j _=>?_
    rw [Finset.sum_div];refine Finset.sum_congr rfl fun l _=>?_
    have hne:((eV j).1 ≠ (eV l).1) ↔ (j ≠ l) :=
     not_congr ⟨fun h=>eV.injective (Subtype.ext h),fun h=>by rw [h]⟩
    by_cases hjl:j ≠ l
    .
     rw [if_pos (hne.mpr hjl),if_pos hjl];dsimp only [gPair]
     simp only [dif_neg (hV_notU j),dif_neg (hV_notU l),Subtype.coe_eta,Equiv.symm_apply_apply]
    . rw [if_neg (mt hne.mp hjl),if_neg hjl,zero_div]
   have hUV:(∑ i:Fin u,∑ j:Fin v,if (eU i).1 ≠ (eV j).1 then gPair (eU i).1 (eV j).1 else 0) =
     (∑ i:Fin u,∑ j:Fin v,(ξb i+ξd j)^2)/(n:R):=by
    rw [Finset.sum_div];refine Finset.sum_congr rfl fun i _=>?_
    rw [Finset.sum_div];refine Finset.sum_congr rfl fun j _=>?_
    rw [if_pos (hUV_ne i j)];dsimp only [gPair]
    simp only [dif_pos (eU i).2,dif_neg (hV_notU j),Subtype.coe_eta,Equiv.symm_apply_apply]
   have hVU:(∑ j:Fin v,∑ i:Fin u,if (eV j).1 ≠ (eU i).1 then gPair (eV j).1 (eU i).1 else 0) =
     (∑ i:Fin u,∑ j:Fin v,(ξb i+ξd j)^2)/(n:R):=by
    rw [Finset.sum_comm,Finset.sum_div];refine Finset.sum_congr rfl fun i _=>?_
    rw [Finset.sum_div];refine Finset.sum_congr rfl fun j _=>?_
    rw [if_pos (hUV_ne i j).symm];dsimp only [gPair]
    simp only [dif_pos (eU i).2,dif_neg (hV_notU j),Subtype.coe_eta,Equiv.symm_apply_apply]
   rw [hUU,hVV,hUV,hVU];ring
  rw [hquad_block ξa,hquad_block ξc,hcross_block] at hfull_eq
  rw [hfull_eq] at hdouble
  have h2eq:2*(((u:R) - 2)*∑ i:Fin u,ξa i^2+(∑ i:Fin u,ξa i)^2)/(n:R) +
    2*(((v:R) - 2)*∑ j:Fin v,ξc j^2+(∑ j:Fin v,ξc j)^2)/(n:R) +
    2*((v:R)*∑ i:Fin u,ξb i^2+(u:R)*∑ j:Fin v,ξd j^2 +
     2*(∑ i:Fin u,ξb i)*(∑ j:Fin v,ξd j))/(n:R) =
    2*((((u:R) - 2)/(n:R)*∑ i:Fin u,ξa i^2+(∑ i:Fin u,ξa i)^2/(n:R)) +
     (((v:R) - 2)/(n:R)*∑ j:Fin v,ξc j^2+(∑ j:Fin v,ξc j)^2/(n:R)) +
     ((v:R)/(n:R)*∑ i:Fin u,ξb i^2+(u:R)/(n:R)*∑ j:Fin v,ξd j^2 +
      2*(∑ i:Fin u,ξb i)*(∑ j:Fin v,ξd j)/(n:R))):=by ring
  linarith [hdouble,h2eq]
 have hRHS:∑ e:ι,(∑ q:κ,ξ q*T₂ (Pi.single e 1) q)^2 =
   (((u:R) - 2)/(n:R)*∑ i:Fin u,ξa i^2+(∑ i:Fin u,ξa i)^2/(n:R)) +
   (((v:R) - 2)/(n:R)*∑ j:Fin v,ξc j^2+(∑ j:Fin v,ξc j)^2/(n:R)) +
   ((v:R)/(n:R)*∑ i:Fin u,ξb i^2+(u:R)/(n:R)*∑ j:Fin v,ξd j^2 +
    2*(∑ i:Fin u,ξb i)*(∑ j:Fin v,ξd j)/(n:R)):=by
  simp only [ι,Fintype.sum_sum_type,Fintype.sum_unique]
  have hu4R:(4:R)<=(u:R):=by exact_mod_cast hu_ge4
  have hv4R:(4:R)<=(v:R):=by exact_mod_cast hv_ge4
  have hsq_u:(sqrt (((u:R) - 2)/(n:R)))^2=((u:R) - 2)/(n:R) :=
   sq_sqrt (div_nonneg (by linarith) hn_pos.le)
  have hsq_v:(sqrt (((v:R) - 2)/(n:R)))^2=((v:R) - 2)/(n:R) :=
   sq_sqrt (div_nonneg (by linarith) hn_pos.le)
  have hsq_vn:(sqrt ((v:R)/(n:R)))^2=(v:R)/(n:R):=sq_sqrt (by positivity)
  have hsq_un:(sqrt ((u:R)/(n:R)))^2=(u:R)/(n:R):=sq_sqrt (by positivity)
  have hsq_uvn:(sqrt ((u:R)*(v:R)/(n:R)))^2=(u:R)*(v:R)/(n:R):=sq_sqrt (by positivity)
  have hsq_n:(sqrt (n:R))^2=(n:R):=sq_sqrt hn_pos.le
  have hb1:∑ k:Fin u,(∑ q:κ,ξ q*T₂ (Pi.single (.inl (.inl (.inl k))) 1) q)^2 =
    ((u:R) - 2)/(n:R)*∑ i:Fin u,ξa i^2:=by
   rw [Finset.mul_sum];refine Finset.sum_congr rfl fun k _=>?_
   have hq:∑ q:κ,ξ q*T₂ (Pi.single (.inl (.inl (.inl k))) 1) q =
     sqrt (((u:R) - 2)/(n:R))*ξa k:=by
    simp only [κ,Fintype.sum_sum_type]
    have h0:∀ q:κ,T₂ (Pi.single (.inl (.inl (.inl k))) 1) q =
      match q with
      | .inl (.inl i)=>if i=k then sqrt (((u:R) - 2)/(n:R)) else 0
      | _=>0:=fun q=>by
     rcases q with (i | j) | (i | j) <;>
     . change _ = _;simp [T₂,pairT2L,Pi.single_apply]
    simp_rw [h0];simp [ξa,mul_comm]
   rw [hq,mul_pow,hsq_u]
  have hb2:(∑ q:κ,ξ q*T₂ (Pi.single (.inl (.inl (.inr ()))) 1) q)^2=(∑ i:Fin u,ξa i)^2/(n:R):=by
   have hq:∑ q:κ,ξ q*T₂ (Pi.single (.inl (.inl (.inr ()))) 1) q =
     (sqrt (n:R))⁻¹*∑ i:Fin u,ξa i:=by
    simp only [κ,Fintype.sum_sum_type]
    have h0:∀ q:κ,T₂ (Pi.single (.inl (.inl (.inr ()))) 1) q =
      match q with
      | .inl (.inl _)=>(sqrt (n:R))⁻¹
      | _=>0:=fun q=>by
     rcases q with (i | j) | (i | j) <;> (change _ = _;simp [T₂,pairT2L])
    simp_rw [h0];simp [ξa,mul_comm,← Finset.mul_sum]
   rw [hq,mul_pow,inv_pow,hsq_n];ring
  have hb3:∑ l:Fin v,(∑ q:κ,ξ q*T₂ (Pi.single (.inl (.inr (.inl l))) 1) q)^2 =
    ((v:R) - 2)/(n:R)*∑ j:Fin v,ξc j^2:=by
   rw [Finset.mul_sum];refine Finset.sum_congr rfl fun l _=>?_
   have hq:∑ q:κ,ξ q*T₂ (Pi.single (.inl (.inr (.inl l))) 1) q =
     sqrt (((v:R) - 2)/(n:R))*ξc l:=by
    simp only [κ,Fintype.sum_sum_type]
    have h0:∀ q:κ,T₂ (Pi.single (.inl (.inr (.inl l))) 1) q =
      match q with
      | .inl (.inr j)=>if j=l then sqrt (((v:R) - 2)/(n:R)) else 0
      | _=>0:=fun q=>by
     rcases q with (i | j) | (i | j) <;> (change _ = _;simp [T₂,pairT2L,Pi.single_apply])
    simp_rw [h0];simp [ξc,mul_comm]
   rw [hq,mul_pow,hsq_v]
  have hb4:(∑ q:κ,ξ q*T₂ (Pi.single (.inl (.inr (.inr ()))) 1) q)^2=(∑ j:Fin v,ξc j)^2/(n:R):=by
   have hq:∑ q:κ,ξ q*T₂ (Pi.single (.inl (.inr (.inr ()))) 1) q =
     (sqrt (n:R))⁻¹*∑ j:Fin v,ξc j:=by
    simp only [κ,Fintype.sum_sum_type]
    have h0:∀ q:κ,T₂ (Pi.single (.inl (.inr (.inr ()))) 1) q =
      match q with
      | .inl (.inr _)=>(sqrt (n:R))⁻¹
      | _=>0:=fun q=>by
     rcases q with (i | j) | (i | j) <;> (change _ = _;simp [T₂,pairT2L])
    simp_rw [h0];simp [ξc,mul_comm,← Finset.mul_sum]
   rw [hq,mul_pow,inv_pow,hsq_n];ring
  have hb5:∑ k:Fin u,(∑ q:κ,ξ q*T₂ (Pi.single (.inr (.inl (.inl k))) 1) q)^2 =
    (v:R)/(n:R)*((∑ i:Fin u,ξb i^2) - (∑ i:Fin u,ξb i)^2/(u:R)):=by
   have hterm:∀ k:Fin u,(∑ q:κ,ξ q*T₂ (Pi.single (.inr (.inl (.inl k))) 1) q)^2 =
     (v:R)/(n:R)*(ξb k - (∑ i:Fin u,ξb i)/(u:R))^2:=fun k=>by
    have hq:∑ q:κ,ξ q*T₂ (Pi.single (.inr (.inl (.inl k))) 1) q =
      sqrt ((v:R)/(n:R))*(ξb k - (∑ i:Fin u,ξb i)/(u:R)):=by
     simp only [κ,Fintype.sum_sum_type]
     have h0:∀ q:κ,T₂ (Pi.single (.inr (.inl (.inl k))) 1) q =
       match q with
       | .inr (.inl i)=>sqrt ((v:R)/(n:R))*((if i=k then (1:R) else 0) - 1/(u:R))
       | _=>0:=fun q=>by
      rcases q with (i | j) | (i | j) <;> (change _ = _;simp [T₂,pairT2L,Pi.single_apply])
     simp_rw [h0]
     simp only [mul_zero,Finset.sum_const_zero,add_zero,zero_add]
     have h1:∀ i:Fin u,ξ (.inr (.inl i))*(sqrt ((v:R)/(n:R))*((if i=k then (1:R) else 0) - 1/(u:R))) =
       sqrt ((v:R)/(n:R))*((if i=k then ξb i else 0) - ξb i/(u:R)):=fun i=>by
      unfold ξb;split_ifs <;> ring
     simp_rw [h1,← Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,← Finset.sum_div]
    rw [hq,mul_pow,hsq_vn]
   simp_rw [hterm,← Finset.mul_sum]
   congr 1
   set mb:=(∑ i:Fin u,ξb i)/(u:R)
   simp_rw [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
   have hcross:∑ i:Fin u,2*ξb i*mb=2*(∑ i:Fin u,ξb i)*mb:=by
    simp_rw [← Finset.sum_mul,← Finset.mul_sum]
   rw [hcross];unfold mb;field_simp [hu_pos.ne'];ring
  have hb6:∑ l:Fin v,(∑ q:κ,ξ q*T₂ (Pi.single (.inr (.inl (.inr l))) 1) q)^2 =
    (u:R)/(n:R)*((∑ j:Fin v,ξd j^2) - (∑ j:Fin v,ξd j)^2/(v:R)):=by
   have hterm:∀ l:Fin v,(∑ q:κ,ξ q*T₂ (Pi.single (.inr (.inl (.inr l))) 1) q)^2 =
     (u:R)/(n:R)*(ξd l - (∑ j:Fin v,ξd j)/(v:R))^2:=fun l=>by
    have hq:∑ q:κ,ξ q*T₂ (Pi.single (.inr (.inl (.inr l))) 1) q =
      sqrt ((u:R)/(n:R))*(ξd l - (∑ j:Fin v,ξd j)/(v:R)):=by
     simp only [κ,Fintype.sum_sum_type]
     have h0:∀ q:κ,T₂ (Pi.single (.inr (.inl (.inr l))) 1) q =
       match q with
       | .inr (.inr j)=>sqrt ((u:R)/(n:R))*((if j=l then (1:R) else 0) - 1/(v:R))
       | _=>0:=fun q=>by
      rcases q with (i | j) | (i | j) <;> (change _ = _;simp [T₂,pairT2L,Pi.single_apply])
     simp_rw [h0]
     simp only [mul_zero,Finset.sum_const_zero,add_zero,zero_add]
     have h1:∀ j:Fin v,ξ (.inr (.inr j))*(sqrt ((u:R)/(n:R))*((if j=l then (1:R) else 0) - 1/(v:R))) =
       sqrt ((u:R)/(n:R))*((if j=l then ξd j else 0) - ξd j/(v:R)):=fun j=>by
      unfold ξd;split_ifs <;> ring
     simp_rw [h1,← Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,← Finset.sum_div]
    rw [hq,mul_pow,hsq_un]
   simp_rw [hterm,← Finset.mul_sum]
   congr 1
   set md:=(∑ j:Fin v,ξd j)/(v:R)
   simp_rw [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
   have hcross:∑ j:Fin v,2*ξd j*md=2*(∑ j:Fin v,ξd j)*md:=by
    simp_rw [← Finset.sum_mul,← Finset.mul_sum]
   rw [hcross];unfold md;field_simp [hv_pos.ne'];ring
  have hb7:(∑ q:κ,ξ q*T₂ (Pi.single (.inr (.inr ())) 1) q)^2 =
    (v:R)/(n:R)*((∑ i:Fin u,ξb i)^2/(u:R)) +
    (u:R)/(n:R)*((∑ j:Fin v,ξd j)^2/(v:R)) +
    2*(∑ i:Fin u,ξb i)*(∑ j:Fin v,ξd j)/(n:R):=by
   have hq:∑ q:κ,ξ q*T₂ (Pi.single (.inr (.inr ())) 1) q =
     sqrt ((u:R)*(v:R)/(n:R))*((∑ i:Fin u,ξb i)/(u:R)+(∑ j:Fin v,ξd j)/(v:R)):=by
    simp only [κ,Fintype.sum_sum_type]
    have h0:∀ q:κ,T₂ (Pi.single (.inr (.inr ())) 1) q =
      match q with
      | .inr (.inl _)=>sqrt ((u:R)*(v:R)/(n:R))/(u:R)
      | .inr (.inr _)=>sqrt ((u:R)*(v:R)/(n:R))/(v:R)
      | _=>0:=fun q=>by
     rcases q with (i | j) | (i | j) <;> (change _ = _;simp [T₂,pairT2L,Pi.single_apply])
    simp_rw [h0]
    simp only [mul_zero,Finset.sum_const_zero,add_zero,zero_add,← Finset.sum_mul]
    unfold ξb ξd;ring
   rw [hq,mul_pow,hsq_uvn];field_simp [hu_pos.ne',hv_pos.ne',hn_pos.ne'];ring
  rw [hb1,hb2,hb3,hb4,hb5,hb6,hb7];ring
 rw [hLHS,hRHS]
private lemma lintegral_pi_prod_fin {α:Type*} [MeasurableSpace α] (μ:Measure α) [IsProbabilityMeasure μ] :
  ∀ {w:ℕ} (f:Fin w->α->ENNReal),(∀ k,Measurable (f k)) ->
   (∫⁻ x:Fin w->α,∏ k:Fin w,f k (x k) ∂Measure.pi (fun _:Fin w=>μ)) =
   ∏ k:Fin w,∫⁻ a:α,f k a ∂μ
 | 0,_,_=>by simp
 | w+1,f,hf=>by
   let e:=MeasurableEquiv.piFinSuccAbove (fun _:Fin (w+1)=>α) 0
   have hmp:MeasurePreserving e (Measure.pi (fun _:Fin (w+1)=>μ))
     (μ.prod (Measure.pi (fun _:Fin w=>μ))) :=
    measurePreserving_piFinSuccAbove (fun _:Fin (w+1)=>μ) 0
   have hcomp:∀ x:Fin (w+1)->α,
     (∏ k:Fin (w+1),f k (x k))=f 0 (e x).1*∏ k:Fin w,f k.succ ((e x).2 k):=fun x=>by
    rw [Fin.prod_univ_succ];rfl
   simp_rw [hcomp]
   have hm1:Measurable (fun y:Fin w->α=>∏ k:Fin w,f k.succ (y k)) :=
    Finset.measurable_prod _ fun k _=>(hf k.succ).comp (measurable_pi_apply k)
   have h1:=hmp.lintegral_comp (((hf 0).comp measurable_fst).mul (hm1.comp measurable_snd))
   have h1':(∫⁻ x:Fin (w+1)->α,f 0 (e x).1*∏ k:Fin w,f k.succ ((e x).2 k) ∂Measure.pi (fun _:Fin (w+1)=>μ)) =
     ∫⁻ p:α × (Fin w->α),f 0 p.1*∏ k:Fin w,f k.succ (p.2 k) ∂(μ.prod (Measure.pi (fun _:Fin w=>μ))):=h1
   rw [h1',lintegral_prod_mul (hf 0).aemeasurable hm1.aemeasurable,
     lintegral_pi_prod_fin μ (fun k=>f k.succ) (fun k=>hf k.succ),Fin.prod_univ_succ]
lemma pBP {m:ℕ} (hm:4<=m) {s t:Finset (Fin (2*m))}
  (hs:s ∈ bS m) (ht:t ∈ bS m)
  (hk0:2<=(s ∩ t).card) (hk1:(s ∩ t).card<=m - 2) :
  let u:=2*(s ∩ t).card
  let v:=2*m - u
  (gE (2*m) (aF (2*m) s ∩ aF (2*m) t)).toReal <=
   sqrt ((u:R)*(v:R))*pairFactor (2*m) u*pairFactor (2*m) v:=by
 intro u v
 let n:ℕ:=2*m
 have hn_ge8:8<=n:=by omega
 have hu_ge4:4<=u:=by omega
 have hv_ge4:4<=v:=by omega
 have huv:u+v=n:=by omega
 have hn_pos:(0:R) < (n:R):=by exact_mod_cast (by omega:0 < n)
 have hu_pos:(0:R) < (u:R):=by exact_mod_cast (by omega:0 < u)
 have hv_pos:(0:R) < (v:R):=by exact_mod_cast (by omega:0 < v)
 set U:Finset (Fin n):=Finset.univ.filter (fun i=>spin s i=spin t i)
 set V:Finset (Fin n):=Finset.univ.filter (fun i=>spin s i ≠ spin t i)
 have hdisjUV:Disjoint U V:=by
  rw [Finset.disjoint_left];intro i h1 h2
  exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
 have hunUV:U ∪ V=Finset.univ:=by
  ext i;simp only [U,V,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,iff_true];exact em _
 have hU_eq:U=(s ∩ t) ∪ (sᶜ ∩ tᶜ):=by
  ext i
  have h1:i ∈ U ↔ spin s i=spin t i:=by simp [U]
  rw [h1,Finset.mem_union,Finset.mem_inter,Finset.mem_inter,Finset.mem_compl,Finset.mem_compl]
  unfold spin;by_cases hs':i ∈ s <;> by_cases ht':i ∈ t <;> simp [hs',ht'] <;> norm_num
 have hU_card:U.card=u:=by
  rw [hU_eq,Finset.card_union_of_disjoint]
  .
   have hsc:(sᶜ ∩ tᶜ).card=(s ∩ t).card:=by
    have hcomp:sᶜ ∩ tᶜ=(s ∪ t)ᶜ:=(Finset.compl_union s t).symm
    rw [hcomp,Finset.card_compl,Fintype.card_fin]
    have hs_c:s.card=m:=(Finset.mem_filter.mp hs).2
    have ht_c:t.card=m:=(Finset.mem_filter.mp ht).2
    have hun:(s ∪ t).card+(s ∩ t).card=s.card+t.card:=Finset.card_union_add_card_inter s t
    omega
   omega
  .
   rw [Finset.disjoint_left];intro i h1 h2
   exact (Finset.mem_compl.mp (Finset.mem_inter.mp h2).1) (Finset.mem_inter.mp h1).1
 have hV_card:V.card=v:=by
  have hadd:=Finset.card_union_of_disjoint hdisjUV
  rw [hunUV,Finset.card_univ,Fintype.card_fin,hU_card] at hadd;omega
 let eU:Fin u ≃ {i:Fin n // i ∈ U}:=(Fintype.equivFinOfCardEq (by simp [hU_card])).symm
 let eV:Fin v ≃ {i:Fin n // i ∈ V}:=(Fintype.equivFinOfCardEq (by simp [hV_card])).symm
 let aVal (W:Ei n->R) (i:Fin u):R :=
  (sqrt (n:R))⁻¹*∑ k:Fin u,ev0 W (eU i).1 (eU k).1*(spin s (eU i).1*spin s (eU k).1)
 let cVal (W:Ei n->R) (j:Fin v):R :=
  (sqrt (n:R))⁻¹*∑ l:Fin v,ev0 W (eV j).1 (eV l).1*(spin s (eV j).1*spin s (eV l).1)
 let bVal (W:Ei n->R) (i:Fin u):R :=
  (sqrt (n:R))⁻¹*∑ l:Fin v,ev0 W (eU i).1 (eV l).1*(spin s (eU i).1*spin s (eV l).1)
 let dVal (W:Ei n->R) (j:Fin v):R :=
  (sqrt (n:R))⁻¹*∑ k:Fin u,ev0 W (eV j).1 (eU k).1*(spin s (eV j).1*spin s (eU k).1)
 have hsum_UV:∀ (f:Fin n->R),∑ w:Fin n,f w=(∑ k:Fin u,f (eU k).1)+∑ l:Fin v,f (eV l).1:=by
  intro f
  rw [← hunUV,Finset.sum_union hdisjUV]
  congr 1
  .
   rw [← Finset.sum_attach U f]
   exact (Fintype.sum_equiv eU (fun k=>f (eU k).1) (fun x:{i // i ∈ U}=>f x.1) fun _=>rfl).symm
  .
   rw [← Finset.sum_attach V f]
   exact (Fintype.sum_equiv eV (fun l=>f (eV l).1) (fun x:{i // i ∈ V}=>f x.1) fun _=>rfl).symm
 have hspin_U:∀ k:Fin u,spin t (eU k).1=spin s (eU k).1:=fun k =>
  (Finset.mem_filter.mp (eU k).2).2.symm
 have hspin_V:∀ l:Fin v,spin t (eV l).1 = -spin s (eV l).1:=fun l=>by
  have hne:=(Finset.mem_filter.mp (eV l).2).2
  unfold spin at hne ⊢
  by_cases h1:(eV l).1 ∈ s <;> by_cases h2:(eV l).1 ∈ t <;> simp_all
 have hdecomp_U:∀ (W:Ei n->R) (i:Fin u),
   fv0 n W s (eU i).1=aVal W i+bVal W i /\
   fv0 n W t (eU i).1=aVal W i - bVal W i:=by
  intro W i
  unfold fv0 aVal bVal
  constructor
  . rw [hsum_UV,mul_add]
  .
   rw [hsum_UV,mul_add]
   have h1:∑ k:Fin u,ev0 W (eU i).1 (eU k).1*(spin t (eU i).1*spin t (eU k).1) =
     ∑ k:Fin u,ev0 W (eU i).1 (eU k).1*(spin s (eU i).1*spin s (eU k).1) :=
    Finset.sum_congr rfl fun k _=>by rw [hspin_U i,hspin_U k]
   have h2:∑ l:Fin v,ev0 W (eU i).1 (eV l).1*(spin t (eU i).1*spin t (eV l).1) =
     -(∑ l:Fin v,ev0 W (eU i).1 (eV l).1*(spin s (eU i).1*spin s (eV l).1)):=by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _=>by rw [hspin_U i,hspin_V l];ring
   rw [h1,h2];ring
 have hdecomp_V:∀ (W:Ei n->R) (j:Fin v),
   fv0 n W s (eV j).1=cVal W j+dVal W j /\
   fv0 n W t (eV j).1=cVal W j - dVal W j:=by
  intro W j
  unfold fv0 cVal dVal
  constructor
  . rw [hsum_UV,mul_add,add_comm]
  .
   rw [hsum_UV,mul_add,add_comm]
   have h1:∑ l:Fin v,ev0 W (eV j).1 (eV l).1*(spin t (eV j).1*spin t (eV l).1) =
     ∑ l:Fin v,ev0 W (eV j).1 (eV l).1*(spin s (eV j).1*spin s (eV l).1) :=
    Finset.sum_congr rfl fun l _=>by rw [hspin_V j,hspin_V l];ring
   have h2:∑ k:Fin u,ev0 W (eV j).1 (eU k).1*(spin t (eV j).1*spin t (eU k).1) =
     -(∑ k:Fin u,ev0 W (eV j).1 (eU k).1*(spin s (eV j).1*spin s (eU k).1)):=by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _=>by rw [hspin_V j,hspin_U k];ring
   rw [h1,h2];ring
 let κ:=(Fin u ⊕ Fin v) ⊕ (Fin u ⊕ Fin v)
 let ι:=((Fin u ⊕ Unit) ⊕ (Fin v ⊕ Unit)) ⊕ ((Fin u ⊕ Fin v) ⊕ Unit)
 let T₁:(Ei n->R) →L[R] (κ->R):=(pairT1L s eU eV).toContinuousLinearMap
 let T₂:(ι->R) →L[R] (κ->R):=(pairT2L n u v).toContinuousLinearMap
 have hlaw:(gE n).map T₁=(Measure.pi (fun _:ι=>N01)).map T₂ :=
  pGL hn_ge8 hu_ge4 hv_ge4 s hdisjUV hunUV eU eV
 set E_pair:Set (κ->R) :=
  {y | (∀ i:Fin u,|y (.inr (.inl i))| <= y (.inl (.inl i)) - gC) /\
     (∀ j:Fin v,|y (.inr (.inr j))| <= y (.inl (.inr j)) - gC)}
 have hE_meas:MeasurableSet E_pair:=by
  have h1:MeasurableSet {y:κ->R | ∀ i:Fin u,|y (.inr (.inl i))| <= y (.inl (.inl i)) - gC}:=by
   rw [Set.ofPred_forall]
   exact MeasurableSet.iInter fun i=>measurableSet_le
    (continuous_abs.comp (continuous_apply _)).measurable ((continuous_apply _).sub continuous_const).measurable
  have h2:MeasurableSet {y:κ->R | ∀ j:Fin v,|y (.inr (.inr j))| <= y (.inl (.inr j)) - gC}:=by
   rw [Set.ofPred_forall]
   exact MeasurableSet.iInter fun j=>measurableSet_le
    (continuous_abs.comp (continuous_apply _)).measurable ((continuous_apply _).sub continuous_const).measurable
  exact h1.inter h2
 have hsub_pair:aF n s ∩ aF n t ⊆ T₁ ⁻¹' E_pair:=by
  intro W ⟨hWs,hWt⟩
  refine ⟨fun i=>?_,fun j=>?_⟩
  .
   have h1:=hWs (eU i).1;have h2:=hWt (eU i).1
   rw [(hdecomp_U W i).1] at h1;rw [(hdecomp_U W i).2] at h2
   change |bVal W i| <= aVal W i - gC
   rw [abs_le];exact ⟨by linarith,by linarith⟩
  .
   have h1:=hWs (eV j).1;have h2:=hWt (eV j).1
   rw [(hdecomp_V W j).1] at h1;rw [(hdecomp_V W j).2] at h2
   change |dVal W j| <= cVal W j - gC
   rw [abs_le];exact ⟨by linarith,by linarith⟩
 have hle_T2:(gE n (aF n s ∩ aF n t)).toReal <=
   (Measure.pi (fun _:ι=>N01) (T₂ ⁻¹' E_pair)).toReal:=by
  have h1:=measure_mono hsub_pair (μ:=gE n)
  have hmap:=congrArg (fun μ:Measure (κ->R)=>μ E_pair) hlaw
  rw [Measure.map_apply T₁.continuous.measurable hE_meas,
    Measure.map_apply T₂.continuous.measurable hE_meas] at hmap
  rw [hmap] at h1
  exact ENNReal.toReal_mono (measure_ne_top _ _) h1
 let ιAC:=(Fin u ⊕ Unit) ⊕ (Fin v ⊕ Unit)
 let ιBD:=Fin u ⊕ Fin v
 let eTop:(ι->R) ≃ᵐ (ιAC->R) × ((ιBD ⊕ Unit)->R):=MeasurableEquiv.sumPiEquivProdPi (fun _=>R)
 let eBDS:((ιBD ⊕ Unit)->R) ≃ᵐ (ιBD->R) × (Unit->R):=MeasurableEquiv.sumPiEquivProdPi (fun _=>R)
 let eBD:(ιBD->R) ≃ᵐ (Fin u->R) × (Fin v->R):=MeasurableEquiv.sumPiEquivProdPi (fun _=>R)
 let eAC:(ιAC->R) ≃ᵐ ((Fin u ⊕ Unit)->R) × ((Fin v ⊕ Unit)->R):=MeasurableEquiv.sumPiEquivProdPi (fun _=>R)
 let eAG:((Fin u ⊕ Unit)->R) ≃ᵐ (Fin u->R) × (Unit->R):=MeasurableEquiv.sumPiEquivProdPi (fun _=>R)
 let eCG:((Fin v ⊕ Unit)->R) ≃ᵐ (Fin v->R) × (Unit->R):=MeasurableEquiv.sumPiEquivProdPi (fun _=>R)
 set μU:Measure (Fin u->R):=Measure.pi (fun _:Fin u=>N01)
 set μV:Measure (Fin v->R):=Measure.pi (fun _:Fin v=>N01)
 set μ1:Measure (Unit->R):=Measure.pi (fun _:Unit=>N01)
 set μAC:Measure (ιAC->R):=Measure.pi (fun _:ιAC=>N01)
 set μBDS:Measure ((ιBD ⊕ Unit)->R):=Measure.pi (fun _:ιBD ⊕ Unit=>N01)
 set μBD:Measure (ιBD->R):=Measure.pi (fun _:ιBD=>N01)
 have hT2_split:Measure.pi (fun _:ι=>N01) (T₂ ⁻¹' E_pair) =
   ∫⁻ x:ιAC->R,∫⁻ s0:Unit->R,
    (μU {B:Fin u->R | ∀ i:Fin u,
     |sqrt ((v:R)/(n:R))*(B i - (∑ k,B k)/(u:R)) +
      (sqrt ((u:R)*(v:R)/(n:R))*s0 ())/(u:R)| <=
     sqrt (((u:R) - 2)/(n:R))*x (.inl (.inl i))+(sqrt (n:R))⁻¹*x (.inl (.inr ())) - gC}) *
    (μV {D:Fin v->R | ∀ j:Fin v,
     |sqrt ((u:R)/(n:R))*(D j - (∑ l,D l)/(v:R)) +
      (sqrt ((u:R)*(v:R)/(n:R))*s0 ())/(v:R)| <=
     sqrt (((v:R) - 2)/(n:R))*x (.inr (.inl j))+(sqrt (n:R))⁻¹*x (.inr (.inr ())) - gC})
   ∂μ1 ∂μAC:=by
  have hmp1:MeasurePreserving eTop (Measure.pi (fun _:ι=>N01)) (μAC.prod μBDS) :=
   measurePreserving_sumPiEquivProdPi (fun _:ι=>N01)
  have hmp2:MeasurePreserving eBDS μBDS (μBD.prod μ1) :=
   measurePreserving_sumPiEquivProdPi (fun _:ιBD ⊕ Unit=>N01)
  have hmp3:MeasurePreserving eBD μBD (μU.prod μV) :=
   measurePreserving_sumPiEquivProdPi (fun _:ιBD=>N01)
  set S1:Set ((ιAC->R) × ((ιBD ⊕ Unit)->R)):=eTop.symm ⁻¹' (T₂ ⁻¹' E_pair)
  have hS1_m:MeasurableSet S1:=(T₂.continuous.measurable.comp eTop.symm.measurable) hE_meas
  have h1:Measure.pi (fun _:ι=>N01) (T₂ ⁻¹' E_pair)=(μAC.prod μBDS) S1:=by
   rw [← hmp1.measure_preimage hS1_m.nullMeasurableSet];rfl
  rw [h1,Measure.prod_apply hS1_m]
  refine lintegral_congr fun x=>?_
  set S2:Set ((ιBD->R) × (Unit->R)):=eBDS.symm ⁻¹' ((fun y=>(x,y)) ⁻¹' S1)
  have hS2_m:MeasurableSet S2:=eBDS.symm.measurable ((measurable_prodMk_left) hS1_m)
  have h2:μBDS ((fun y=>(x,y)) ⁻¹' S1)=(μBD.prod μ1) S2:=by
   rw [← hmp2.measure_preimage hS2_m.nullMeasurableSet];rfl
  rw [h2,Measure.prod_apply_symm hS2_m]
  refine lintegral_congr fun s0=>?_
  set Au:Set (Fin u->R):={B | ∀ i:Fin u,
   |sqrt ((v:R)/(n:R))*(B i - (∑ k,B k)/(u:R)) +
    (sqrt ((u:R)*(v:R)/(n:R))*s0 ())/(u:R)| <=
   sqrt (((u:R) - 2)/(n:R))*x (.inl (.inl i))+(sqrt (n:R))⁻¹*x (.inl (.inr ())) - gC}
  set Av:Set (Fin v->R):={D | ∀ j:Fin v,
   |sqrt ((u:R)/(n:R))*(D j - (∑ l,D l)/(v:R)) +
    (sqrt ((u:R)*(v:R)/(n:R))*s0 ())/(v:R)| <=
   sqrt (((v:R) - 2)/(n:R))*x (.inr (.inl j))+(sqrt (n:R))⁻¹*x (.inr (.inr ())) - gC}
  have hAu_m:MeasurableSet Au:=by
   rw [show Au=⋂ i:Fin u,{B:Fin u->R |
     |sqrt ((v:R)/(n:R))*(B i - (∑ k,B k)/(u:R)) +
      (sqrt ((u:R)*(v:R)/(n:R))*s0 ())/(u:R)| <=
     sqrt (((u:R) - 2)/(n:R))*x (.inl (.inl i))+(sqrt (n:R))⁻¹*x (.inl (.inr ())) - gC} by
    ext B;simp [Au]]
   exact MeasurableSet.iInter fun i=>measurableSet_le
    (by fun_prop:Continuous (fun B:Fin u->R =>
     |sqrt ((v:R)/(n:R))*(B i - (∑ k,B k)/(u:R)) +
      (sqrt ((u:R)*(v:R)/(n:R))*s0 ())/(u:R)|)).measurable measurable_const
  have hAv_m:MeasurableSet Av:=by
   rw [show Av=⋂ j:Fin v,{D:Fin v->R |
     |sqrt ((u:R)/(n:R))*(D j - (∑ l,D l)/(v:R)) +
      (sqrt ((u:R)*(v:R)/(n:R))*s0 ())/(v:R)| <=
     sqrt (((v:R) - 2)/(n:R))*x (.inr (.inl j))+(sqrt (n:R))⁻¹*x (.inr (.inr ())) - gC} by
    ext D;simp [Av]]
   exact MeasurableSet.iInter fun j=>measurableSet_le
    (by fun_prop:Continuous (fun D:Fin v->R =>
     |sqrt ((u:R)/(n:R))*(D j - (∑ l,D l)/(v:R)) +
      (sqrt ((u:R)*(v:R)/(n:R))*s0 ())/(v:R)|)).measurable measurable_const
  have hpre_BD:((fun bd=>(bd,s0)) ⁻¹' S2)=eBD ⁻¹' (Au ×ˢ Av):=by
   have heTop:∀ (a:ιAC->R) (b:(ιBD ⊕ Unit)->R) (q:ι),eTop.symm (a,b) q=Sum.elim a b q :=
    fun _ _ q=>by cases q <;> rfl
   have heBDS:∀ (a:ιBD->R) (b:Unit->R) (q:ιBD ⊕ Unit),eBDS.symm (a,b) q=Sum.elim a b q :=
    fun _ _ q=>by cases q <;> rfl
   have heBD1:∀ (bd:ιBD->R) (i:Fin u),(eBD bd).1 i=bd (.inl i):=fun _ _=>rfl
   have heBD2:∀ (bd:ιBD->R) (j:Fin v),(eBD bd).2 j=bd (.inr j):=fun _ _=>rfl
   ext bd
   simp only [Set.mem_preimage,S2,S1,E_pair,Set.mem_ofPred_eq,Set.mem_prod,Au,Av]
   have hrew_u:sqrt ((u:R)*(v:R)/(n:R))/(u:R)*s0 () =
     sqrt ((u:R)*(v:R)/(n:R))*s0 ()/(u:R):=by ring
   have hrew_v:sqrt ((u:R)*(v:R)/(n:R))/(v:R)*s0 () =
     sqrt ((u:R)*(v:R)/(n:R))*s0 ()/(v:R):=by ring
   simp only [T₂,pairT2L,LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,AddHom.coe_mk,
    heTop,heBDS,heBD1,heBD2,Sum.elim_inl,Sum.elim_inr,hrew_u,hrew_v]
  rw [hpre_BD,hmp3.measure_preimage (hAu_m.prod hAv_m).nullMeasurableSet,Measure.prod_prod]
 have hdec_u:∀ (x:ιAC->R) (s0:Unit->R),
   μU {B:Fin u->R | ∀ i:Fin u,
    |sqrt ((v:R)/(n:R))*(B i - (∑ k,B k)/(u:R)) +
     (sqrt ((u:R)*(v:R)/(n:R))*s0 ())/(u:R)| <=
    sqrt (((u:R) - 2)/(n:R))*x (.inl (.inl i))+(sqrt (n:R))⁻¹*x (.inl (.inr ())) - gC} <=
   ENNReal.ofReal (sqrt (u:R))*∏ i:Fin (u - 1),
    N01 {z | gC - (sqrt (n:R))⁻¹*x (.inl (.inr ())) <=
     sqrt (((u:R) - 2)/(n:R))*x (.inl (.inl ⟨i.1,by omega⟩)) - sqrt ((v:R)/(n:R)) * |z|}:=by
  intro x s0
  set r:Fin u->R:=fun i =>
   sqrt (((u:R) - 2)/(n:R))*x (.inl (.inl i))+(sqrt (n:R))⁻¹*x (.inl (.inr ())) - gC
  by_cases hr_nn:∀ i:Fin u,0<=r i
  .
   have hbd:=bDc (by omega:2<=u) (sqrt_pos.mpr (div_pos hv_pos hn_pos))
    (sqrt ((u:R)*(v:R)/(n:R))*s0 ()) r hr_nn
   have hset:∀ i:Fin (u - 1),
     {z:R | |sqrt ((v:R)/(n:R))*z| <= r ⟨i.1,by omega⟩} =
     {z:R | gC - (sqrt (n:R))⁻¹*x (.inl (.inr ())) <=
      sqrt (((u:R) - 2)/(n:R))*x (.inl (.inl ⟨i.1,by omega⟩)) - sqrt ((v:R)/(n:R)) * |z|}:=by
    intro i;ext z;simp only [Set.mem_ofPred_eq,abs_mul,abs_of_pos (sqrt_pos.mpr (div_pos hv_pos hn_pos)),r]
    constructor <;> intro h <;> linarith
   simp_rw [hset] at hbd
   rw [← ENNReal.ofReal_toReal (measure_ne_top μU _)]
   refine (ENNReal.ofReal_le_ofReal hbd).trans_eq ?_
   rw [ENNReal.ofReal_mul (sqrt_nonneg _),ENNReal.ofReal_prod_of_nonneg (fun _ _=>ENNReal.toReal_nonneg)]
   congr 1;exact Finset.prod_congr rfl fun i _=>ENNReal.ofReal_toReal (measure_ne_top _ _)
  .
   push Not at hr_nn
   obtain ⟨i0,hi0⟩:=hr_nn
   have hempty:{B:Fin u->R | ∀ i:Fin u,
     |sqrt ((v:R)/(n:R))*(B i - (∑ k,B k)/(u:R)) +
      (sqrt ((u:R)*(v:R)/(n:R))*s0 ())/(u:R)| <= r i}=∅:=by
    ext B;simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    intro h;linarith [h i0,abs_nonneg (sqrt ((v:R)/(n:R))*(B i0 - (∑ k,B k)/(u:R)) +
     (sqrt ((u:R)*(v:R)/(n:R))*s0 ())/(u:R))]
   rw [hempty,measure_empty];exact bot_le
 have hdec_v:∀ (x:ιAC->R) (s0:Unit->R),
   μV {D:Fin v->R | ∀ j:Fin v,
    |sqrt ((u:R)/(n:R))*(D j - (∑ l,D l)/(v:R)) +
     (sqrt ((u:R)*(v:R)/(n:R))*s0 ())/(v:R)| <=
    sqrt (((v:R) - 2)/(n:R))*x (.inr (.inl j))+(sqrt (n:R))⁻¹*x (.inr (.inr ())) - gC} <=
   ENNReal.ofReal (sqrt (v:R))*∏ j:Fin (v - 1),
    N01 {z | gC - (sqrt (n:R))⁻¹*x (.inr (.inr ())) <=
     sqrt (((v:R) - 2)/(n:R))*x (.inr (.inl ⟨j.1,by omega⟩)) - sqrt ((u:R)/(n:R)) * |z|}:=by
  intro x s0
  set r:Fin v->R:=fun j =>
   sqrt (((v:R) - 2)/(n:R))*x (.inr (.inl j))+(sqrt (n:R))⁻¹*x (.inr (.inr ())) - gC
  by_cases hr_nn:∀ j:Fin v,0<=r j
  .
   have hbd:=bDc (by omega:2<=v) (sqrt_pos.mpr (div_pos hu_pos hn_pos))
    (sqrt ((u:R)*(v:R)/(n:R))*s0 ()) r hr_nn
   have hset:∀ j:Fin (v - 1),
     {z:R | |sqrt ((u:R)/(n:R))*z| <= r ⟨j.1,by omega⟩} =
     {z:R | gC - (sqrt (n:R))⁻¹*x (.inr (.inr ())) <=
      sqrt (((v:R) - 2)/(n:R))*x (.inr (.inl ⟨j.1,by omega⟩)) - sqrt ((u:R)/(n:R)) * |z|}:=by
    intro j;ext z;simp only [Set.mem_ofPred_eq,abs_mul,abs_of_pos (sqrt_pos.mpr (div_pos hu_pos hn_pos)),r]
    constructor <;> intro h <;> linarith
   simp_rw [hset] at hbd
   rw [← ENNReal.ofReal_toReal (measure_ne_top μV _)]
   refine (ENNReal.ofReal_le_ofReal hbd).trans_eq ?_
   rw [ENNReal.ofReal_mul (sqrt_nonneg _),ENNReal.ofReal_prod_of_nonneg (fun _ _=>ENNReal.toReal_nonneg)]
   congr 1;exact Finset.prod_congr rfl fun j _=>ENNReal.ofReal_toReal (measure_ne_top _ _)
  .
   push Not at hr_nn
   obtain ⟨j0,hj0⟩:=hr_nn
   have hempty:{D:Fin v->R | ∀ j:Fin v,
     |sqrt ((u:R)/(n:R))*(D j - (∑ l,D l)/(v:R)) +
      (sqrt ((u:R)*(v:R)/(n:R))*s0 ())/(v:R)| <= r j}=∅:=by
    ext D;simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    intro h;linarith [h j0,abs_nonneg (sqrt ((u:R)/(n:R))*(D j0 - (∑ l,D l)/(v:R)) +
     (sqrt ((u:R)*(v:R)/(n:R))*s0 ())/(v:R))]
   rw [hempty,measure_empty];exact bot_le
 have hfactor_one:∀ (w:ℕ) (hw0:4<=w) (hw1:w<=n - 4),
   (∫⁻ y:(Fin w ⊕ Unit)->R,
    ∏ i:Fin (w - 1),
     N01 {z | gC - (sqrt (n:R))⁻¹*y (.inr ()) <=
      sqrt (((w:R) - 2)/(n:R))*y (.inl ⟨i.1,by omega⟩) - sqrt (((n:R) - (w:R))/(n:R)) * |z|}
    ∂Measure.pi (fun _:Fin w ⊕ Unit=>N01)) =
   ENNReal.ofReal (pairFactor n w):=by
  intro w hw0 hw1
  let eWG:((Fin w ⊕ Unit)->R) ≃ᵐ (Fin w->R) × (Unit->R):=MeasurableEquiv.sumPiEquivProdPi (fun _=>R)
  let eU1:(Unit->R) ≃ᵐ R:=MeasurableEquiv.funUnique Unit R
  have hmpWG:MeasurePreserving eWG (Measure.pi (fun _:Fin w ⊕ Unit=>N01))
    ((Measure.pi (fun _:Fin w=>N01)).prod μ1) :=
   measurePreserving_sumPiEquivProdPi (fun _:Fin w ⊕ Unit=>N01)
  have hmpU1:MeasurePreserving eU1 μ1 (N01):=by
   simpa [eU1,μ1] using MeasureTheory.measurePreserving_funUnique (N01) Unit
  let eAll:((Fin w ⊕ Unit)->R) ≃ᵐ (Fin w->R) × R:=eWG.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) eU1)
  have hmpAll:MeasurePreserving eAll (Measure.pi (fun _:Fin w ⊕ Unit=>N01))
    ((Measure.pi (fun _:Fin w=>N01)).prod (N01)) :=
   (MeasurePreserving.prod (MeasurePreserving.id _) hmpU1).comp hmpWG
  set gFun:(Fin w->R) × R->ENNReal:=fun p =>
   ∏ i:Fin (w - 1),
    N01 {z | gC - (sqrt (n:R))⁻¹*p.2 <=
     sqrt (((w:R) - 2)/(n:R))*p.1 ⟨i.1,by omega⟩ - sqrt (((n:R) - (w:R))/(n:R)) * |z|}
  have hgFun_m:Measurable gFun:=by
   refine Finset.measurable_prod _ fun i _=>?_
   have hS_m:MeasurableSet {q:((Fin w->R) × R) × R |
     gC - (sqrt (n:R))⁻¹*q.1.2 <=
      sqrt (((w:R) - 2)/(n:R))*q.1.1 ⟨i.1,by omega⟩ - sqrt (((n:R) - (w:R))/(n:R)) * |q.2|} :=
    measurableSet_le (by fun_prop:Continuous (fun q:((Fin w->R) × R) × R=>gC - (sqrt (n:R))⁻¹*q.1.2)).measurable
     (by fun_prop:Continuous (fun q:((Fin w->R) × R) × R =>
      sqrt (((w:R) - 2)/(n:R))*q.1.1 ⟨i.1,by omega⟩ - sqrt (((n:R) - (w:R))/(n:R)) * |q.2|)).measurable
   simpa using measurable_measure_prodMk_left hS_m (ν:=N01)
  have h1:(∫⁻ y:(Fin w ⊕ Unit)->R,gFun (eAll y) ∂Measure.pi (fun _:Fin w ⊕ Unit=>N01)) =
    ∫⁻ p:(Fin w->R) × R,gFun p ∂((Measure.pi (fun _:Fin w=>N01)).prod (N01)):=by
   rw [← hmpAll.lintegral_comp hgFun_m]
  have hcomp_eq:∀ y:(Fin w ⊕ Unit)->R,gFun (eAll y) =
    ∏ i:Fin (w - 1),
     N01 {z | gC - (sqrt (n:R))⁻¹*y (.inr ()) <=
      sqrt (((w:R) - 2)/(n:R))*y (.inl ⟨i.1,by omega⟩) - sqrt (((n:R) - (w:R))/(n:R)) * |z|}:=fun _=>rfl
  simp_rw [← hcomp_eq]
  rw [h1,lintegral_prod_symm _ hgFun_m.aemeasurable]
  have hinner:∀ g:R,
    (∫⁻ A:Fin w->R,gFun (A,g) ∂Measure.pi (fun _:Fin w=>N01)) =
    ((N01).prod (N01)
     {z:R × R | gC - (sqrt (n:R))⁻¹*g <=
      sqrt (((w:R) - 2)/(n:R))*z.1 - sqrt (((n:R) - (w:R))/(n:R)) * |z.2|})^(w - 1):=by
   intro g
   set f1:R->ENNReal:=fun a =>
    N01 {z | gC - (sqrt (n:R))⁻¹*g <=
     sqrt (((w:R) - 2)/(n:R))*a - sqrt (((n:R) - (w:R))/(n:R)) * |z|}
   have hf1_m:Measurable f1:=by
    have hSm:MeasurableSet {q:R × R | gC - (sqrt (n:R))⁻¹*g <=
      sqrt (((w:R) - 2)/(n:R))*q.1 - sqrt (((n:R) - (w:R))/(n:R)) * |q.2|} :=
     measurableSet_le measurable_const (by fun_prop:Continuous (fun q:R × R =>
      sqrt (((w:R) - 2)/(n:R))*q.1 - sqrt (((n:R) - (w:R))/(n:R)) * |q.2|)).measurable
    simpa [f1] using measurable_measure_prodMk_left hSm (ν:=N01)
   set fAll:Fin w->R->ENNReal:=fun k a=>if k.1 < w - 1 then f1 a else 1
   have hprod_eq:∀ A:Fin w->R,gFun (A,g)=∏ k:Fin w,fAll k (A k):=fun A=>by
    unfold gFun fAll
    have hrew:(∏ k:Fin w,if k.1 < w - 1 then f1 (A k) else 1) =
      ∏ k ∈ Finset.univ.filter (fun k:Fin w=>k.1 < w - 1),f1 (A k):=by
     rw [Finset.prod_filter]
    rw [hrew]
    refine (Finset.prod_bij (fun (i:Fin (w - 1)) _=>(⟨i.1,by omega⟩:Fin w))
     (fun i _=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.2⟩)
     (fun _ _ _ _ h=>Fin.ext (by simpa using congrArg Fin.val h))
     (fun k hk=>⟨⟨k.1,(Finset.mem_filter.mp hk).2⟩,Finset.mem_univ _,rfl⟩)
     (fun _ _=>rfl))
   simp_rw [hprod_eq]
   rw [lintegral_pi_prod_fin (N01) fAll (fun k=>by
    unfold fAll;split_ifs
    . exact hf1_m
    . exact measurable_const)]
   have hprod2:(∏ k:Fin w,∫⁻ a,fAll k a ∂N01) =
     (∫⁻ a,f1 a ∂N01)^(w - 1):=by
    have hval:∀ k:Fin w,(∫⁻ a,fAll k a ∂N01) =
      if k.1 < w - 1 then ∫⁻ a,f1 a ∂N01 else 1:=fun k=>by
     unfold fAll;split_ifs
     . rfl
     . simp
    simp_rw [hval,← Finset.prod_filter,Finset.prod_const]
    congr 1
    have hcard:(Finset.univ.filter fun k:Fin w=>k.1 < w - 1).card=w - 1:=by
     have hbij:(Finset.univ.filter fun k:Fin w=>k.1 < w - 1).card=(Finset.univ:Finset (Fin (w - 1))).card :=
      Finset.card_bij (fun (k:Fin w) hk=>(⟨k.1,(Finset.mem_filter.mp hk).2⟩:Fin (w - 1)))
       (fun _ _=>Finset.mem_univ _)
       (fun _ _ _ _ h=>Fin.ext (by simpa using congrArg Fin.val h))
       (fun i _=>⟨⟨i.1,by omega⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.2⟩,rfl⟩)
     simpa using hbij
    rw [hcard]
   rw [hprod2]
   congr 1
   have hSm:MeasurableSet {z:R × R | gC - (sqrt (n:R))⁻¹*g <=
     sqrt (((w:R) - 2)/(n:R))*z.1 - sqrt (((n:R) - (w:R))/(n:R)) * |z.2|} :=
    measurableSet_le measurable_const (by fun_prop:Continuous (fun z:R × R =>
     sqrt (((w:R) - 2)/(n:R))*z.1 - sqrt (((n:R) - (w:R))/(n:R)) * |z.2|)).measurable
   rw [Measure.prod_apply hSm];rfl
  simp_rw [hinner]
  unfold pairFactor
  rw [ofReal_integral_eq_lintegral_ofReal]
  .
   refine lintegral_congr fun g=>?_
   rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (measure_ne_top _ _)]
  .
   have hSm:MeasurableSet {q:R × (R × R) | gC - (sqrt (n:R))⁻¹*q.1 <=
     sqrt (((w:R) - 2)/(n:R))*q.2.1 - sqrt (((n:R) - (w:R))/(n:R)) * |q.2.2|} :=
    measurableSet_le (by fun_prop:Continuous (fun q:R × (R × R)=>gC - (sqrt (n:R))⁻¹*q.1)).measurable
     (by fun_prop:Continuous (fun q:R × (R × R) =>
      sqrt (((w:R) - 2)/(n:R))*q.2.1 - sqrt (((n:R) - (w:R))/(n:R)) * |q.2.2|)).measurable
   have hm_g:Measurable (fun g:R=>(((N01).prod (N01)
     {z:R × R | gC - (sqrt (n:R))⁻¹*g <=
      sqrt (((w:R) - 2)/(n:R))*z.1 - sqrt (((n:R) - (w:R))/(n:R)) * |z.2|}).toReal)^(w - 1)) :=
    ((measurable_measure_prodMk_left hSm (ν:=(N01).prod (N01))).ennreal_toReal).pow_const _
   refine Integrable.of_bound hm_g.aestronglyMeasurable 1 (Eventually.of_forall fun g=>?_)
   rw [Real.norm_eq_abs,aon (pow_nonneg ENNReal.toReal_nonneg _)]
   exact pow_le_one₀ ENNReal.toReal_nonneg (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ:=(N01).prod (N01))))
  . exact Eventually.of_forall fun _=>pow_nonneg ENNReal.toReal_nonneg _
 have hlint_tot:Measure.pi (fun _:ι=>N01) (T₂ ⁻¹' E_pair) <=
   ENNReal.ofReal (sqrt ((u:R)*(v:R)))*(ENNReal.ofReal (pairFactor n u)*ENNReal.ofReal (pairFactor n v)):=by
  rw [hT2_split]
  have hstep1:(∫⁻ x:ιAC->R,∫⁻ s0:Unit->R,
    (μU {B:Fin u->R | ∀ i:Fin u,
     |sqrt ((v:R)/(n:R))*(B i - (∑ k,B k)/(u:R)) +
      (sqrt ((u:R)*(v:R)/(n:R))*s0 ())/(u:R)| <=
     sqrt (((u:R) - 2)/(n:R))*x (.inl (.inl i))+(sqrt (n:R))⁻¹*x (.inl (.inr ())) - gC}) *
    (μV {D:Fin v->R | ∀ j:Fin v,
     |sqrt ((u:R)/(n:R))*(D j - (∑ l,D l)/(v:R)) +
      (sqrt ((u:R)*(v:R)/(n:R))*s0 ())/(v:R)| <=
     sqrt (((v:R) - 2)/(n:R))*x (.inr (.inl j))+(sqrt (n:R))⁻¹*x (.inr (.inr ())) - gC})
    ∂μ1 ∂μAC) <=
    ∫⁻ x:ιAC->R,
     ENNReal.ofReal (sqrt ((u:R)*(v:R))) *
     ((∏ i:Fin (u - 1),
       N01 {z | gC - (sqrt (n:R))⁻¹*x (.inl (.inr ())) <=
        sqrt (((u:R) - 2)/(n:R))*x (.inl (.inl ⟨i.1,by omega⟩)) - sqrt ((v:R)/(n:R)) * |z|}) *
      (∏ j:Fin (v - 1),
       N01 {z | gC - (sqrt (n:R))⁻¹*x (.inr (.inr ())) <=
        sqrt (((v:R) - 2)/(n:R))*x (.inr (.inl ⟨j.1,by omega⟩)) - sqrt ((u:R)/(n:R)) * |z|}))
    ∂μAC:=by
   refine lintegral_mono fun x=>?_
   refine (lintegral_mono fun s0=>?_).trans_eq (by rw [lintegral_const,measure_univ,mul_one])
   refine (mul_le_mul' (hdec_u x s0) (hdec_v x s0)).trans_eq ?_
   rw [mul_mul_mul_comm,← ENNReal.ofReal_mul (sqrt_nonneg _),← sqrt_mul hu_pos.le]
  refine hstep1.trans_eq ?_
  have hmpAC:MeasurePreserving eAC μAC
    ((Measure.pi (fun _:Fin u ⊕ Unit=>N01)).prod
     (Measure.pi (fun _:Fin v ⊕ Unit=>N01))) :=
   measurePreserving_sumPiEquivProdPi (fun _:ιAC=>N01)
  have hv_eq:(v:R)=(n:R) - (u:R):=by
   have:(u+v:ℕ)=n:=huv;have:((u+v:ℕ):R)=(n:R):=by exact_mod_cast this
   push_cast at this;linarith
  have hu_eq:(u:R)=(n:R) - (v:R):=by linarith
  set fU:((Fin u ⊕ Unit)->R)->ENNReal:=fun y =>
   ∏ i:Fin (u - 1),
    N01 {z | gC - (sqrt (n:R))⁻¹*y (.inr ()) <=
     sqrt (((u:R) - 2)/(n:R))*y (.inl ⟨i.1,by omega⟩) - sqrt (((n:R) - (u:R))/(n:R)) * |z|}
  set fV:((Fin v ⊕ Unit)->R)->ENNReal:=fun y =>
   ∏ j:Fin (v - 1),
    N01 {z | gC - (sqrt (n:R))⁻¹*y (.inr ()) <=
     sqrt (((v:R) - 2)/(n:R))*y (.inl ⟨j.1,by omega⟩) - sqrt (((n:R) - (v:R))/(n:R)) * |z|}
  have hfU_m:Measurable fU:=Finset.measurable_prod _ fun i _=>by
   have hSm:MeasurableSet {q:((Fin u ⊕ Unit)->R) × R |
     gC - (sqrt (n:R))⁻¹*q.1 (.inr ()) <=
      sqrt (((u:R) - 2)/(n:R))*q.1 (.inl ⟨i.1,by omega⟩) - sqrt (((n:R) - (u:R))/(n:R)) * |q.2|} :=
    measurableSet_le (by fun_prop:Continuous (fun q:((Fin u ⊕ Unit)->R) × R=>gC - (sqrt (n:R))⁻¹*q.1 (.inr ()))).measurable
     (by fun_prop:Continuous (fun q:((Fin u ⊕ Unit)->R) × R =>
      sqrt (((u:R) - 2)/(n:R))*q.1 (.inl ⟨i.1,by omega⟩) - sqrt (((n:R) - (u:R))/(n:R)) * |q.2|)).measurable
   simpa using measurable_measure_prodMk_left hSm (ν:=N01)
  have hfV_m:Measurable fV:=Finset.measurable_prod _ fun j _=>by
   have hSm:MeasurableSet {q:((Fin v ⊕ Unit)->R) × R |
     gC - (sqrt (n:R))⁻¹*q.1 (.inr ()) <=
      sqrt (((v:R) - 2)/(n:R))*q.1 (.inl ⟨j.1,by omega⟩) - sqrt (((n:R) - (v:R))/(n:R)) * |q.2|} :=
    measurableSet_le (by fun_prop:Continuous (fun q:((Fin v ⊕ Unit)->R) × R=>gC - (sqrt (n:R))⁻¹*q.1 (.inr ()))).measurable
     (by fun_prop:Continuous (fun q:((Fin v ⊕ Unit)->R) × R =>
      sqrt (((v:R) - 2)/(n:R))*q.1 (.inl ⟨j.1,by omega⟩) - sqrt (((n:R) - (v:R))/(n:R)) * |q.2|)).measurable
   simpa using measurable_measure_prodMk_left hSm (ν:=N01)
  have hcomp_AC:∀ x:ιAC->R,
    (∏ i:Fin (u - 1),
     N01 {z | gC - (sqrt (n:R))⁻¹*x (.inl (.inr ())) <=
      sqrt (((u:R) - 2)/(n:R))*x (.inl (.inl ⟨i.1,by omega⟩)) - sqrt ((v:R)/(n:R)) * |z|}) *
    (∏ j:Fin (v - 1),
     N01 {z | gC - (sqrt (n:R))⁻¹*x (.inr (.inr ())) <=
      sqrt (((v:R) - 2)/(n:R))*x (.inr (.inl ⟨j.1,by omega⟩)) - sqrt ((u:R)/(n:R)) * |z|}) =
    fU (eAC x).1*fV (eAC x).2:=fun x=>by
   congr 1
   . refine Finset.prod_congr rfl fun i _=>?_;rw [hv_eq];rfl
   . refine Finset.prod_congr rfl fun j _=>?_;rw [hu_eq];rfl
  simp_rw [hcomp_AC]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  have hprod_int:(∫⁻ x:ιAC->R,fU (eAC x).1*fV (eAC x).2 ∂μAC) =
    ∫⁻ p:((Fin u ⊕ Unit)->R) × ((Fin v ⊕ Unit)->R),fU p.1*fV p.2 ∂((Measure.pi (fun _:Fin u ⊕ Unit=>N01)).prod
     (Measure.pi (fun _:Fin v ⊕ Unit=>N01))) :=
   hmpAC.lintegral_comp ((hfU_m.comp measurable_fst).mul (hfV_m.comp measurable_snd))
  rw [hprod_int,lintegral_prod_mul hfU_m.aemeasurable hfV_m.aemeasurable,
    hfactor_one u hu_ge4 (by omega),hfactor_one v hv_ge4 (by omega)]
 have htot:=ENNReal.toReal_mono
  (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) hlint_tot
 rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (sqrt_nonneg _),
   ENNReal.toReal_ofReal (pairFactor_nonneg n u),ENNReal.toReal_ofReal (pairFactor_nonneg n v)] at htot
 linarith [hle_T2,htot]
lemma card_bisections_inter {m k:ℕ} {s:Finset (Fin (2*m))} (hs:s ∈ bS m) :
  ((bS m).filter fun t=>(s ∩ t).card=k).card=(m.choose k)^2:=by
 have hs_c:s.card=m:=(Finset.mem_filter.mp hs).2
 have hsc_c:sᶜ.card=m:=by rw [Finset.card_compl,Fintype.card_fin,hs_c];omega
 have hbij:((bS m).filter fun t=>(s ∩ t).card=k).card =
   ((s.powersetCard k) ×ˢ (sᶜ.powersetCard (m - k))).card:=by
  refine Finset.card_bij (fun t _=>(s ∩ t,sᶜ ∩ t)) ?_ ?_ ?_
  .
   intro t ht
   obtain ⟨htb,htk⟩:=Finset.mem_filter.mp ht
   have htc:t.card=m:=(Finset.mem_filter.mp htb).2
   rw [Finset.mem_product,Finset.mem_powersetCard,Finset.mem_powersetCard]
   refine ⟨⟨Finset.inter_subset_left,htk⟩,⟨Finset.inter_subset_left,?_⟩⟩
   have hdisj:Disjoint (s ∩ t) (sᶜ ∩ t):=by
    rw [Finset.disjoint_left];intro x h1 h2
    exact (Finset.mem_compl.mp (Finset.mem_inter.mp h2).1) (Finset.mem_inter.mp h1).1
   have hun:(s ∩ t) ∪ (sᶜ ∩ t)=t:=by
    ext x;simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_compl];tauto
   have hadd:=Finset.card_union_of_disjoint hdisj
   rw [hun,htc,htk] at hadd;dsimp only;omega
  .
   intro t₁ _ t₂ _ heq
   have h1:s ∩ t₁=s ∩ t₂:=congrArg Prod.fst heq
   have h2:sᶜ ∩ t₁=sᶜ ∩ t₂:=congrArg Prod.snd heq
   ext x;by_cases hx:x ∈ s
   . have:=Finset.ext_iff.mp h1 x;simp [hx] at this;exact this
   . have:=Finset.ext_iff.mp h2 x;simp [hx] at this;exact this
  .
   intro ⟨a,b⟩ hab
   rw [Finset.mem_product,Finset.mem_powersetCard,Finset.mem_powersetCard] at hab
   obtain ⟨⟨ha_s,ha_c⟩,⟨hb_s,hb_c⟩⟩:=hab
   have hdisj:Disjoint a b:=by
    rw [Finset.disjoint_left];intro x h1 h2
    exact (Finset.mem_compl.mp (hb_s h2)) (ha_s h1)
   have hkm:k<=m:=by
    have:=Finset.card_le_card ha_s;omega
   refine ⟨a ∪ b,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩,?_⟩
   . rw [Finset.card_union_of_disjoint hdisj,ha_c,hb_c];omega
   .
    have heq:s ∩ (a ∪ b)=a:=by
     ext x;simp only [Finset.mem_inter,Finset.mem_union]
     constructor
     .
      rintro ⟨hxs,hxa | hxb⟩
      . exact hxa
      . exact absurd hxs (Finset.mem_compl.mp (hb_s hxb))
     . intro hxa;exact ⟨ha_s hxa,Or.inl hxa⟩
    rw [heq,ha_c]
   .
    ext x
    .
     simp only [Finset.mem_inter,Finset.mem_union]
     constructor
     .
      rintro ⟨hxs,hxa | hxb⟩
      . exact hxa
      . exact absurd hxs (Finset.mem_compl.mp (hb_s hxb))
     . intro hxa;exact ⟨ha_s hxa,Or.inl hxa⟩
    .
     simp only [Finset.mem_inter,Finset.mem_union,Finset.mem_compl]
     constructor
     .
      rintro ⟨hxs,hxa | hxb⟩
      . exact absurd (ha_s hxa) hxs
      . exact hxb
     . intro hxb;exact ⟨Finset.mem_compl.mp (hb_s hxb),Or.inr hxb⟩
 rw [hbij,Finset.card_product,Finset.card_powersetCard,Finset.card_powersetCard,hs_c,hsc_c]
 by_cases hkm:k<=m
 . rw [Nat.choose_symm hkm,sq]
 . rw [Nat.choose_eq_zero_of_lt (by omega),zero_mul,zero_pow (by norm_num)]
set_option maxHeartbeats 800000 in
open scoped Classical in
lemma sMU {m:ℕ} (hm:4<=m) :
  ∫ W,(friendlyCount m W)^2 ∂(gE (2*m)) <=
   4*(m:R)^2*(∫ W,friendlyCount m W ∂(gE (2*m))) +
   49*exp 20*((2*m:R)^7)*exp (2*(2*m:R)*(log 2+gStar)):=by
 set n:ℕ:=2*m
 have hn_ge8:8<=n:=by omega
 have hn_pos:(0:R) < (n:R):=by exact_mod_cast (by omega:0 < n)
 have hmeas_s:∀ s:Finset (Fin n),MeasurableSet (aF n s):=fun s=>by
  rw [show aF n s=⋂ i:Fin n,{W | gC<=fv0 n W s i} by ext W;simp [aF]]
  exact MeasurableSet.iInter fun i=>measurableSet_le measurable_const
   (by unfold fv0;exact continuous_const.mul (continuous_finsetSum _ fun j _ => (continuous_edgeVal i j).mul continuous_const):Continuous (fun W:Ei n->R=>fv0 n W s i)).measurable
 have h1st_eq:∫ W,friendlyCount m W ∂(gE n) =
   ∑ s ∈ bS m,(gE n (aF n s)).toReal:=by
  unfold friendlyCount
  rw [integral_finsetSum _ fun s _=>by
   have:(fun W=>if W ∈ aF n s then (1:R) else 0)=Set.indicator (aF n s) (1:(Ei n->R)->R):=by
    ext W;simp [Set.indicator]
   rw [this];exact (integrable_const 1).indicator (hmeas_s s)]
  refine Finset.sum_congr rfl fun s _=>?_
  have:(fun W=>if W ∈ aF n s then (1:R) else 0)=Set.indicator (aF n s) (1:(Ei n->R)->R):=by
   ext W;simp [Set.indicator]
  rw [this,integral_indicator_one (hmeas_s s),Measure.real]
 have h2nd_eq:∫ W,(friendlyCount m W)^2 ∂(gE n) =
   ∑ s ∈ bS m,∑ t ∈ bS m,(gE n (aF n s ∩ aF n t)).toReal:=by
  have hsq:∀ W:Ei n->R,(friendlyCount m W)^2 =
    ∑ s ∈ bS m,∑ t ∈ bS m,Set.indicator (aF n s ∩ aF n t) (1:(Ei n->R)->R) W:=fun W=>by
   unfold friendlyCount
   rw [sq,Finset.sum_mul]
   refine Finset.sum_congr rfl fun s _=>?_
   rw [Finset.mul_sum]
   refine Finset.sum_congr rfl fun t _=>?_
   by_cases h1:W ∈ aF n s <;> by_cases h2:W ∈ aF n t <;> simp [n,h1,h2]
  simp_rw [hsq]
  have hint_st:∀ s t:Finset (Fin n),
    Integrable (Set.indicator (aF n s ∩ aF n t) (1:(Ei n->R)->R)) (gE n) :=
   fun s t=>(integrable_const (1:R)).indicator ((hmeas_s s).inter (hmeas_s t))
  rw [integral_finsetSum _ fun s _=>integrable_finsetSum _ fun t _=>hint_st s t]
  refine Finset.sum_congr rfl fun s _=>?_
  rw [integral_finsetSum _ fun t _=>hint_st s t]
  refine Finset.sum_congr rfl fun t _=>?_
  rw [integral_indicator_one ((hmeas_s s).inter (hmeas_s t)),Measure.real]
 rw [h2nd_eq,h1st_eq]
 have hsplit_t:∀ s ∈ bS m,
   ∑ t ∈ bS m,(gE n (aF n s ∩ aF n t)).toReal <=
   4*(m:R)^2*(gE n (aF n s)).toReal +
   ∑ k ∈ Finset.Icc 2 (m - 2),((m.choose k:R)^2) *
    (sqrt ((2*k:R)*((n - 2*k:ℕ):R))*pairFactor n (2*k)*pairFactor n (n - 2*k)):=by
  intro s hs
  have hpart:∑ t ∈ bS m,(gE n (aF n s ∩ aF n t)).toReal =
    ∑ k ∈ Finset.range (m+1),
     ∑ t ∈ (bS m).filter (fun t=>(s ∩ t).card=k),
      (gE n (aF n s ∩ aF n t)).toReal:=by
   rw [← Finset.sum_fiberwise_of_maps_to (g:=fun t=>(s ∩ t).card)]
   intro t ht
   rw [Finset.mem_range]
   have:(s ∩ t).card<=s.card:=Finset.card_le_card Finset.inter_subset_left
   have hs_c:s.card=m:=(Finset.mem_filter.mp hs).2
   omega
  rw [hpart]
  have hsub_icc:Finset.Icc 2 (m - 2) ⊆ Finset.range (m+1):=by
   intro k hk;rw [Finset.mem_Icc] at hk;rw [Finset.mem_range];omega
  rw [← Finset.sum_sdiff hsub_icc]
  refine add_le_add ?_ ?_
  ·
   have hle_b:∀ k ∈ Finset.range (m+1) \ Finset.Icc 2 (m - 2),
     ∑ t ∈ (bS m).filter (fun t=>(s ∩ t).card=k),
      (gE n (aF n s ∩ aF n t)).toReal <=
     ((m.choose k:R)^2)*(gE n (aF n s)).toReal:=by
    intro k _
    have h1:∑ t ∈ (bS m).filter (fun t=>(s ∩ t).card=k),
      (gE n (aF n s ∩ aF n t)).toReal <=
      ∑ _t ∈ (bS m).filter (fun t=>(s ∩ t).card=k),
       (gE n (aF n s)).toReal :=
     Finset.sum_le_sum fun t _=>ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_left)
    rw [Finset.sum_const,nsmul_eq_mul,card_bisections_inter hs,Nat.cast_pow] at h1
    exact h1
   refine (Finset.sum_le_sum hle_b).trans ?_
   rw [← Finset.sum_mul]
   refine mlR ?_ ENNReal.toReal_nonneg
   have hset_bd:Finset.range (m+1) \ Finset.Icc 2 (m - 2) ⊆ {0,1,m - 1,m}:=by
    intro k hk
    rw [Finset.mem_sdiff,Finset.mem_range,Finset.mem_Icc] at hk
    simp only [Finset.mem_insert,Finset.mem_singleton];omega
   have hsum_le:∑ k ∈ Finset.range (m+1) \ Finset.Icc 2 (m - 2),(m.choose k:R)^2 <=
     ∑ k ∈ ({0,1,m - 1,m}:Finset ℕ),(m.choose k:R)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hset_bd (fun _ _ _=>sq_nonneg _)
   refine hsum_le.trans ?_
   have h1:∑ k ∈ ({0,1,m - 1,m}:Finset ℕ),(m.choose k:R)^2 <=
     (m.choose 0:R)^2+(m.choose 1:R)^2+(m.choose (m - 1):R)^2+(m.choose m:R)^2:=by
    have ha:∀ (a:ℕ) (S:Finset ℕ),∑ k ∈ insert a S,(m.choose k:R)^2 <=
      (m.choose a:R)^2+∑ k ∈ S,(m.choose k:R)^2:=fun a S=>by
     by_cases h:a ∈ S
     . rw [Finset.insert_eq_of_mem h];linarith [sq_nonneg (m.choose a:R)]
     . rw [Finset.sum_insert h]
    have h1:=ha 0 {1,m - 1,m}
    have h2:=ha 1 {m - 1,m}
    have h3:=ha (m - 1) {m}
    simp only [Finset.sum_singleton] at h3
    linarith
   have hch_symm:m.choose (m - 1)=m:=by
    rw [Nat.choose_symm (by omega:1<=m),Nat.choose_one_right]
   simp only [Nat.choose_zero_right,Nat.choose_one_right,hch_symm,Nat.choose_self,Nat.cast_one] at h1
   have hm1:(1:R)<=(m:R):=by exact_mod_cast (by omega:1<=m)
   nlinarith
  ·
   refine Finset.sum_le_sum fun k hk=>?_
   rw [Finset.mem_Icc] at hk
   have h1:∑ t ∈ (bS m).filter (fun t=>(s ∩ t).card=k),
     (gE n (aF n s ∩ aF n t)).toReal <=
     ∑ _t ∈ (bS m).filter (fun t=>(s ∩ t).card=k),
      (sqrt ((2*k:R)*((n - 2*k:ℕ):R))*pairFactor n (2*k)*pairFactor n (n - 2*k)):=by
    refine Finset.sum_le_sum fun t ht=>?_
    obtain ⟨htb,htk⟩:=Finset.mem_filter.mp ht
    have hpair:=pBP hm hs htb (by omega) (by omega)
    simpa [htk,n,Nat.cast_mul,Nat.cast_ofNat] using hpair
   rw [Finset.sum_const,nsmul_eq_mul,card_bisections_inter hs,Nat.cast_pow] at h1
   exact h1
 have hsum_s:=Finset.sum_le_sum hsplit_t
 rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,card_bisections] at hsum_s
 refine hsum_s.trans (add_le_add le_rfl ?_)
 have hterm_k:∀ k ∈ Finset.Icc 2 (m - 2),
   ((2*m).choose m:R)*((m.choose k:R)^2 *
    (sqrt ((2*k:R)*((n - 2*k:ℕ):R))*pairFactor n (2*k)*pairFactor n (n - 2*k))) <=
   49*exp 20*((n:R)^6)*exp (2*(n:R)*(log 2+gStar)):=by
  intro k hk
  rw [Finset.mem_Icc] at hk
  set u:ℕ:=2*k
  set v:ℕ:=n - u
  have hu4:4<=u:=by omega
  have hv4:4<=v:=by omega
  have hu_n4:u<=n - 4:=by omega
  have hv_n4:v<=n - 4:=by omega
  have huv:u+v=n:=by omega
  have hn2_pos:(0:R) < (n:R) - 2:=by
   have:(8:R)<=(n:R):=by exact_mod_cast hn_ge8
   linarith
  set β₁:R:=((u:R) - 2)/((n:R) - 2)
  set β₂:R:=((v:R) - 2)/((n:R) - 2)
  set ρ₁:R:=2*β₁ - 1
  set ρ₂:R:=2*β₂ - 1
  have hpf1:=pFU hn_ge8 hu4 hu_n4
  have hpf2:=pFU hn_ge8 hv4 hv_n4
  have hch1:((2*m).choose m:R)<=exp ((n:R)*log 2):=by
   have hle:(2*m).choose m<=2^(2*m):=by
    rw [← Nat.sum_range_choose (2*m)]
    exact Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr (by omega))
   have hleR:((2*m).choose m:R)<=(2:R)^(2*m):=by exact_mod_cast hle
   refine hleR.trans_eq ?_
   rw [show (n:R)*log 2=((2*m:ℕ):R)*log 2 from rfl,
     exp_nat_mul,exp_log (by norm_num)]
  have hch2:(m.choose k:R)^2 <=
    exp (-(u:R)*log ((u:R)/(n:R)) - (v:R)*log ((v:R)/(n:R))):=by
   have h1:=choose_entropy_bound (m:=m) (k:=k) (by omega) (by omega)
   have h2:=pow_le_pow_left₀ (by positivity) h1 2
   rw [← exp_nat_mul] at h2
   refine h2.trans_eq ?_
   have hu_div:(k:R)/(m:R)=(u:R)/(n:R):=by
    unfold u n;push_cast;ring
   have hv_div:((m - k:ℕ):R)/(m:R)=(v:R)/(n:R):=by
    have hmk:2*(m - k)=v:=by omega
    have hmkR:(2:R)*((m - k:ℕ):R)=(v:R):=by exact_mod_cast hmk
    unfold n;push_cast;rw [← hmkR];ring
   have huR:(2:R)*(k:R)=(u:R):=by unfold u;push_cast;ring
   have hvR:(2:R)*((m - k:ℕ):R)=(v:R):=by
    have:2*(m - k)=v:=by omega
    exact_mod_cast this
   rw [hu_div,hv_div];congr 1;push_cast;rw [← huR,← hvR];ring
  have hsqrt_uv:sqrt ((2*k:R)*((n - 2*k:ℕ):R))<=(n:R):=by
   have hu_le:(2*k:R)<=(n:R):=by exact_mod_cast (by omega:2*k<=n)
   have hv_le:((n - 2*k:ℕ):R)<=(n:R):=by exact_mod_cast (by omega:n - 2*k<=n)
   calc sqrt ((2*k:R)*((n - 2*k:ℕ):R))
     <= sqrt ((n:R)*(n:R)):=sqrt_le_sqrt (mul_le_mul hu_le hv_le (by positivity) hn_pos.le)
    _ = (n:R):=sqrt_mul_self hn_pos.le
  have hprod_le:((2*m).choose m:R)*((m.choose k:R)^2 *
    (sqrt ((2*k:R)*((n - 2*k:ℕ):R))*pairFactor n u*pairFactor n v)) <=
    49*(n:R)^2 *
    exp ((n:R)*log 2 - (u:R)*log ((u:R)/(n:R)) - (v:R)*log ((v:R)/(n:R)) +
     ((n:R) - 2)*(gStar+aConst*ρ₁+bConst*ρ₁^3+β₁*log (2*β₁)) +
     ((n:R) - 2)*(gStar+aConst*ρ₂+bConst*ρ₂^3+β₂*log (2*β₂))):=by
   have hpf12:pairFactor n u*pairFactor n v <=
     (7*sqrt (n:R)*exp (((n:R) - 2)*(gStar+aConst*ρ₁+bConst*ρ₁^3+β₁*log (2*β₁)))) *
     (7*sqrt (n:R)*exp (((n:R) - 2)*(gStar+aConst*ρ₂+bConst*ρ₂^3+β₂*log (2*β₂)))) :=
    mul_le_mul hpf1 hpf2 (pairFactor_nonneg n v) (by positivity)
   have hstep1:sqrt ((2*k:R)*((n - 2*k:ℕ):R))*pairFactor n u*pairFactor n v <=
     (n:R)*((7*sqrt (n:R)*exp (((n:R) - 2)*(gStar+aConst*ρ₁+bConst*ρ₁^3+β₁*log (2*β₁)))) *
      (7*sqrt (n:R)*exp (((n:R) - 2)*(gStar+aConst*ρ₂+bConst*ρ₂^3+β₂*log (2*β₂))))):=by
    rw [mul_assoc]
    exact mul_le_mul hsqrt_uv hpf12 (mul_nonneg (pairFactor_nonneg n u) (pairFactor_nonneg n v)) hn_pos.le
   have hnn1:0<=sqrt ((2*k:R)*((n - 2*k:ℕ):R))*pairFactor n u*pairFactor n v :=
    mul_nonneg (mul_nonneg (sqrt_nonneg _) (pairFactor_nonneg n u)) (pairFactor_nonneg n v)
   have hstep2:=mul_le_mul hch1 (mul_le_mul hch2 hstep1 hnn1 (by positivity))
    (mul_nonneg (sq_nonneg _) hnn1) (by positivity)
   refine hstep2.trans_eq ?_
   have hsqn:sqrt (n:R)*sqrt (n:R)=(n:R):=mul_self_sqrt hn_pos.le
   calc exp ((n:R)*log 2) *
      (exp (-(u:R)*log ((u:R)/(n:R)) - (v:R)*log ((v:R)/(n:R))) *
       ((n:R)*((7*sqrt (n:R)*exp (((n:R) - 2)*(gStar+aConst*ρ₁+bConst*ρ₁^3+β₁*log (2*β₁)))) *
        (7*sqrt (n:R)*exp (((n:R) - 2)*(gStar+aConst*ρ₂+bConst*ρ₂^3+β₂*log (2*β₂)))))))
     = 49*(n:R)*(sqrt (n:R)*sqrt (n:R)) *
       (exp ((n:R)*log 2) *
        exp (-(u:R)*log ((u:R)/(n:R)) - (v:R)*log ((v:R)/(n:R))) *
        exp (((n:R) - 2)*(gStar+aConst*ρ₁+bConst*ρ₁^3+β₁*log (2*β₁))) *
        exp (((n:R) - 2)*(gStar+aConst*ρ₂+bConst*ρ₂^3+β₂*log (2*β₂)))):=by ring
    _ = _:=by rw [hsqn,← exp_add,← exp_add,← exp_add];congr 1 <;> ring
  refine hprod_le.trans ?_
  have hexp_le:(n:R)*log 2 - (u:R)*log ((u:R)/(n:R)) - (v:R)*log ((v:R)/(n:R)) +
    ((n:R) - 2)*(gStar+aConst*ρ₁+bConst*ρ₁^3+β₁*log (2*β₁)) +
    ((n:R) - 2)*(gStar+aConst*ρ₂+bConst*ρ₂^3+β₂*log (2*β₂)) <=
    20+4*log (n:R)+2*(n:R)*(log 2+gStar):=by
   have huvR:(u:R)+(v:R)=(n:R):=by exact_mod_cast huv
   have hu_pos:(0:R) < (u:R):=by exact_mod_cast (by omega:0 < u)
   have hv_pos:(0:R) < (v:R):=by exact_mod_cast (by omega:0 < v)
   have hβ1_pos:0 < β₁:=div_pos (by have:(4:R)<=(u:R):=by { exact_mod_cast hu4 };linarith) hn2_pos
   have hβ2_pos:0 < β₂:=div_pos (by have:(4:R)<=(v:R):=by { exact_mod_cast hv4 };linarith) hn2_pos
   have hent:∀ (w:ℕ) (hw4:4<=w) (hwn:w<=n - 4),
     ((n:R) - 2)*((((w:R) - 2)/((n:R) - 2))*log (2*(((w:R) - 2)/((n:R) - 2)))) -
      (w:R)*log ((w:R)/(n:R)) <=
     ((w:R) - 2)*log 2+2*log (n:R):=by
    intro w hw4 hwn
    have hw_pos:(0:R) < (w:R):=by exact_mod_cast (by omega:0 < w)
    have hw2_pos:(0:R) < (w:R) - 2:=by
     have:(4:R)<=(w:R):=by exact_mod_cast hw4
     linarith
    have hwnR:(w:R) < (n:R):=by exact_mod_cast (by omega:w < n)
    have hcoeff:((n:R) - 2)*(((w:R) - 2)/((n:R) - 2))=(w:R) - 2:=by field_simp [hn2_pos.ne']
    rw [← mul_assoc,hcoeff,log_mul (by norm_num) (div_pos hw2_pos hn2_pos).ne']
    have hrat:((w:R) - 2)/((n:R) - 2)<=(w:R)/(n:R):=by
     rw [div_le_div_iff₀ hn2_pos hn_pos];nlinarith
    have hlog1:log (((w:R) - 2)/((n:R) - 2))<=log ((w:R)/(n:R)) :=
     log_le_log (div_pos hw2_pos hn2_pos) hrat
    have hlog2:-log ((w:R)/(n:R))<=log (n:R):=by
     have hw1:(1:R)<=(w:R):=by exact_mod_cast (by omega:1<=w)
     have:=log_le_log (div_pos one_pos hn_pos) (dld hw1 hn_pos.le)
     rw [log_div one_ne_zero hn_pos.ne',log_one,zero_sub] at this;linarith
    nlinarith [mlL hlog1 hw2_pos.le]
   have hent_u:((n:R) - 2)*(β₁*log (2*β₁)) - (u:R)*log ((u:R)/(n:R)) <=
     ((u:R) - 2)*log 2+2*log (n:R):=hent u hu4 hu_n4
   have hent_v:((n:R) - 2)*(β₂*log (2*β₂)) - (v:R)*log ((v:R)/(n:R)) <=
     ((v:R) - 2)*log 2+2*log (n:R):=hent v hv4 hv_n4
   have hρ_sum:ρ₁+ρ₂ = -4/((n:R) - 2):=by
    unfold ρ₁ ρ₂ β₁ β₂;field_simp [hn2_pos.ne'];linarith
   have hρ1_bd:-1 < ρ₁/\ρ₁ < 1:=by
    unfold ρ₁ β₁
    have hu_lt:(u:R) < (n:R):=by exact_mod_cast (by omega:u < n)
    constructor
    . have:0 < ((u:R) - 2)/((n:R) - 2):=hβ1_pos;linarith
    . have:((u:R) - 2)/((n:R) - 2) < 1:=(div_lt_one hn2_pos).mpr (by linarith);linarith
   have hρ2_bd:-1 < ρ₂/\ρ₂ < 1:=by
    unfold ρ₂ β₂
    have hv_lt:(v:R) < (n:R):=by exact_mod_cast (by omega:v < n)
    constructor
    . have:0 < ((v:R) - 2)/((n:R) - 2):=hβ2_pos;linarith
    . have:((v:R) - 2)/((n:R) - 2) < 1:=(div_lt_one hn2_pos).mpr (by linarith);linarith
   have ha_bd:=aConst_bounds
   have ha_lo:(-1:R)<=aConst:=by norm_num [aLoVal,S0,fpS] at ha_bd;linarith
   have ha_hi:aConst<=0:=by norm_num [aHiVal,S0,fpS] at ha_bd;linarith
   have hg_bd:=gStar_ge_gLoVal
   have hg_lo:(-1:R)<=gStar:=by norm_num [gLoVal,S0,fpS] at hg_bd;linarith
   have hodd_a:((n:R) - 2)*(aConst*(ρ₁+ρ₂))<=4:=by
    rw [hρ_sum,show ((n:R) - 2)*(aConst*(-4/((n:R) - 2))) = -4*aConst by field_simp [hn2_pos.ne']]
    linarith
   have hodd_b:((n:R) - 2)*(bConst*(ρ₁^3+ρ₂^3))<=12:=by
    have hfac:ρ₁^3+ρ₂^3=(ρ₁+ρ₂)*(ρ₁^2 - ρ₁*ρ₂+ρ₂^2):=by ring
    have hq_nn:0<=ρ₁^2 - ρ₁*ρ₂+ρ₂^2:=by nlinarith [sq_nonneg (ρ₁ - ρ₂),sq_nonneg (ρ₁+ρ₂)]
    have hq_le:ρ₁^2 - ρ₁*ρ₂+ρ₂^2<=3:=by nlinarith [hρ1_bd.1,hρ1_bd.2,hρ2_bd.1,hρ2_bd.2]
    rw [hfac,hρ_sum]
    have h1:((n:R) - 2)*(bConst*(-4/((n:R) - 2)*(ρ₁^2 - ρ₁*ρ₂+ρ₂^2))) =
      -4*bConst*(ρ₁^2 - ρ₁*ρ₂+ρ₂^2):=by field_simp [hn2_pos.ne']
    rw [h1]
    have hb_eq:bConst=3/25:=rfl
    nlinarith
   have hlog2_nn:0<=log 2:=log_nonneg (by norm_num)
   have hlin_comb:(n:R)*log 2 - (u:R)*log ((u:R)/(n:R)) - (v:R)*log ((v:R)/(n:R)) +
     ((n:R) - 2)*(gStar+aConst*ρ₁+bConst*ρ₁^3+β₁*log (2*β₁)) +
     ((n:R) - 2)*(gStar+aConst*ρ₂+bConst*ρ₂^3+β₂*log (2*β₂)) =
     (n:R)*log 2+2*(n:R)*gStar - 4*gStar +
     (((n:R) - 2)*(aConst*(ρ₁+ρ₂)))+(((n:R) - 2)*(bConst*(ρ₁^3+ρ₂^3))) +
     (((n:R) - 2)*(β₁*log (2*β₁)) - (u:R)*log ((u:R)/(n:R))) +
     (((n:R) - 2)*(β₂*log (2*β₂)) - (v:R)*log ((v:R)/(n:R))):=by ring
   have hsum_log2:((u:R) - 2)*log 2+((v:R) - 2)*log 2=((n:R) - 4)*log 2:=by
    rw [← huvR];ring
   rw [hlin_comb]
   linarith only [hent_u,hent_v,hsum_log2,hodd_a,hodd_b,hg_lo,hlog2_nn]
  calc 49*(n:R)^2*exp _
    <= 49*(n:R)^2*exp (20+4*log (n:R)+2*(n:R)*(log 2+gStar)) :=
     mlL (exp_le_exp.mpr hexp_le) (by positivity)
   _ = 49*exp 20*((n:R)^6)*exp (2*(n:R)*(log 2+gStar)):=by
     rw [exp_add,exp_add,show (4:R)*log (n:R)=((4:ℕ):R)*log (n:R) by norm_num,
       exp_nat_mul,exp_log hn_pos]
     ring
 rw [Finset.mul_sum]
 refine (Finset.sum_le_sum hterm_k).trans ?_
 rw [Finset.sum_const,Nat.card_Icc,nsmul_eq_mul]
 have hcard_le:((m - 2+1 - 2:ℕ):R)<=(n:R):=by exact_mod_cast (by omega:m - 2+1 - 2<=n)
 have hpos:0<=49*exp 20*(n:R)^6*exp (2*(n:R)*(log 2+gStar)):=by positivity
 calc ((m - 2+1 - 2:ℕ):R)*(49*exp 20*(n:R)^6*exp (2*(n:R)*(log 2+gStar)))
   <= (n:R)*(49*exp 20*(n:R)^6*exp (2*(n:R)*(log 2+gStar))) :=
    mlR hcard_le hpos
  _ = 49*exp 20*(n:R)^7*exp (2*(n:R)*(log 2+gStar)):=by ring
  _ = 49*exp 20*((2*m:R)^7)*exp (2*(2*m:R)*(log 2+gStar)):=by simp [n]
lemma paley_zygmund {α:Type*} [MeasurableSpace α] (μ:Measure α) [IsProbabilityMeasure μ]
  {X:α->R} (hX_nn:∀ x,0<=X x) (hX_m:Measurable X) (hX_int:Integrable X μ)
  (hX2_int:Integrable (fun x=>(X x)^2) μ) :
  (∫ x,X x ∂μ)^2<=(∫ x,(X x)^2 ∂μ)*(μ {x | 0 < X x}).toReal:=by
 set S:Set α:={x | 0 < X x}
 have hS_m:MeasurableSet S:=measurableSet_lt measurable_const hX_m
 set E2:R:=∫ x,(X x)^2 ∂μ
 set p:R:=(μ S).toReal
 have hE2_nn:0<=E2:=integral_nonneg fun x=>sq_nonneg (X x)
 have hp_nn:0<=p:=ENNReal.toReal_nonneg
 have hX_eq:∀ x,X x=X x*Set.indicator S (fun _=>(1:R)) x:=fun x=>by
  by_cases hx:0 < X x
  . simp [S,hx]
  .
   have:X x=0:=le_antisymm (not_lt.mp hx) (hX_nn x)
   simp [S,this]
 have hquad:∀ t:R,0<=t^2*E2 - 2*t*(∫ x,X x ∂μ)+p:=by
  intro t
  have hint1:Integrable (fun x=>t^2*(X x)^2) μ:=hX2_int.const_mul (t^2)
  have hint2:Integrable (fun x=>2*t*X x) μ:=hX_int.const_mul (2*t)
  have hint3:Integrable (Set.indicator S (1:α->R)) μ:=(integrable_const 1).indicator hS_m
  have hnn:0<=∫ x,(t*X x - Set.indicator S (1:α->R) x)^2 ∂μ :=
   integral_nonneg fun x=>sq_nonneg _
  have hexp:∀ x,(t*X x - Set.indicator S (1:α->R) x)^2 =
    ((fun y=>t^2*(X y)^2) - (fun y=>2*t*X y)) x+Set.indicator S (1:α->R) x:=fun x=>by
   simp only [Pi.sub_apply]
   by_cases hx:x ∈ S
   . simp [hx];ring
   .
    have h0:X x=0:=le_antisymm (not_lt.mp hx) (hX_nn x)
    simp [hx,h0]
  simp_rw [hexp] at hnn
  rw [integral_add (hint1.sub hint2) hint3] at hnn
  simp only [Pi.sub_apply] at hnn
  rw [integral_sub hint1 hint2,integral_const_mul,integral_const_mul,integral_indicator_one hS_m,Measure.real] at hnn
  exact hnn
 by_cases hE2_0:E2=0
 .
  have hlin:∀ t:R,0 <= -2*t*(∫ x,X x ∂μ)+p:=fun t=>by
   have:=hquad t;rw [hE2_0,mul_zero,zero_sub] at this;linarith
  have hEX0:∫ x,X x ∂μ=0:=by
   by_contra hne
   have:=hlin ((p+1)/(2*(∫ x,X x ∂μ)))
   have hrew:-2*((p+1)/(2*∫ x,X x ∂μ))*(∫ x,X x ∂μ)+p = -1:=by field_simp [hne];ring
   linarith
  rw [hEX0,zero_pow (by norm_num),hE2_0,zero_mul]
 .
  have hE2_pos:0 < E2:=lt_of_le_of_ne hE2_nn (Ne.symm hE2_0)
  have h:=hquad ((∫ x,X x ∂μ)/E2)
  have hrew:((∫ x,X x ∂μ)/E2)^2*E2 - 2*((∫ x,X x ∂μ)/E2)*(∫ x,X x ∂μ)+p =
    p - (∫ x,X x ∂μ)^2/E2:=by field_simp [hE2_pos.ne'];ring
  rw [hrew] at h
  have:(∫ x,X x ∂μ)^2/E2<=p:=by linarith
  rwa [div_le_iff₀ hE2_pos,mul_comm] at this
open scoped Classical in
lemma gAL :
  ∃ c:R,0 < c/\∀ᶠ m:ℕ in atTop,
   c*((2*m:R)^9)⁻¹*exp (-2*tStar*sqrt (2*m:R)) <=
   (gE (2*m) {W | ∃ s ∈ bS m,W ∈ aF (2*m) s}).toReal:=by
 have hg:=gStar_ge_gLoVal
 have hlog2:(69/100:R)<=log 2:=by
  have h1:=le_expNegHi (x:=-6900000) (by norm_num)
  have h2:((-6900000:ℤ):R)/S0 = -69/100:=by norm_num [S0,fpS]
  rw [h2] at h1
  have hchk:eH (-6900000)<=5050000:=by decide
  have hlo:=expNegLo_le (x:=-6900000) (by norm_num)
  rw [h2] at hlo
  have hchk2:5000000<=eL (-6900000):=by decide
  have h3:(1/2:R)<=((eL (-6900000):ℤ):R)/S0:=by
   have:(5000000:R)<=(eL (-6900000):R):=by exact_mod_cast hchk2
   norm_num [S0,fpS] at this ⊢;linarith
  have h4:=log_le_log (by norm_num) (h3.trans hlo)
  rw [log_exp,log_div one_ne_zero (by norm_num),log_one,zero_sub] at h4
  linarith
 have hgap:(17/100:R)<=log 2+gStar:=by
  norm_num [gLoVal,S0,fpS] at hg;linarith
 set c1:R:=(sqrt (2*PI)*exp (1/2))⁻¹ / 2
 have hc1_pos:0 < c1:=by positivity
 set c2:R:=49*exp 20+1
 have hc2_pos:0 < c2:=by positivity
 refine ⟨c1^2/c2,by positivity,?_⟩
 have htend:Tendsto (fun m:ℕ=>4*(m:R)^2 *
   (c1⁻¹*(2*m:R)*exp (tStar*sqrt (2*m:R))*exp (-(2*m:R)*(log 2+gStar))))
   atTop (𝓝 0):=by
  have hzero:Tendsto (fun m:ℕ=>c1⁻¹*8*((m:R)^3*exp (-(m:R)/10))) atTop (𝓝 0):=by
   have h1:Tendsto (fun x:R=>x^3*exp (-x/10)) atTop (𝓝 0):=by
    have h:=tendsto_pow_mul_exp_neg_atTop_nhds_zero 3
    have hcomp:Tendsto (fun x:R=>(x/10)^3*exp (-(x/10))) atTop (𝓝 0) :=
     h.comp (tendsto_id.atTop_div_const (by norm_num))
    have hmul:=hcomp.const_mul (1000:R)
    simp only [mul_zero] at hmul
    refine hmul.congr fun x=>?_;ring_nf
   simpa using (h1.comp tendsto_natCast_atTop_atTop).const_mul (c1⁻¹*8)
  refine squeeze_zero_norm' ?_ hzero
  filter_upwards [eventually_ge_atTop 100] with m hm
  have hmR:(100:R)<=(m:R):=by exact_mod_cast hm
  have hnn:0<=4*(m:R)^2 *
    (c1⁻¹*(2*m:R)*exp (tStar*sqrt (2*m:R))*exp (-(2*m:R)*(log 2+gStar))):=by
   positivity
  rw [Real.norm_eq_abs,aon hnn]
  have ht_hi:tStar<=6/10:=by
   have ht:=tStar_mem;norm_num [tRInt,S0,fpS] at ht;linarith
  have hsq_le:sqrt (2*m:R)<=(m:R)/5:=by
   rw [sqrt_le_iff];exact ⟨by positivity,by nlinarith⟩
  have hexp_le:tStar*sqrt (2*m:R) + -(2*m:R)*(log 2+gStar) <= -(m:R)/10:=by
   nlinarith [hgap,ht_hi,hsq_le,sqrt_nonneg (2*m:R)]
  have h1:=exp_le_exp.mpr hexp_le
  rw [exp_add] at h1
  nlinarith [mlL h1 (show 0<=c1⁻¹*8*(m:R)^3 by positivity)]
 have hev_small:∀ᶠ m:ℕ in atTop,
   4*(m:R)^2 *
    (c1⁻¹*(2*m:R)*exp (tStar*sqrt (2*m:R))*exp (-(2*m:R)*(log 2+gStar)))<=1 :=
  (htend.eventually (gt_mem_nhds (by norm_num:(0:R) < 1))).mono fun _ h=>h.le
 filter_upwards [eventually_ge_atTop 4,hev_small] with m hm hsmall
 set n:ℕ:=2*m
 have hn_pos:(0:R) < (n:R):=by exact_mod_cast (by omega:0 < n)
 have h1st:=first_moment_lower (by omega:2<=m)
 have h2nd:=sMU hm
 set EX:R:=∫ W,friendlyCount m W ∂(gE n)
 set EX2:R:=∫ W,(friendlyCount m W)^2 ∂(gE n)
 set E_exp:R:=exp ((n:R)*(log 2+gStar))
 have hE_pos:0 < E_exp:=exp_pos _
 have hEX_lb:c1*(n:R)⁻¹*exp (-tStar*sqrt (n:R))*E_exp<=EX:=by
  refine le_trans ?_ h1st
  have h2n:((2*m:R)+1)⁻¹>=((2*(2*m:R))⁻¹):=by
   rw [ge_iff_le,inv_le_inv₀ (by positivity) (by positivity)]
   have:(4:R)<=(m:R):=by exact_mod_cast hm
   linarith
  have hrew:c1*(n:R)⁻¹=(sqrt (2*PI)*exp (1/2))⁻¹*(2*(2*m:R))⁻¹:=by
   unfold c1 n;push_cast;ring
  have hn_cast:(n:R)=(2*m:R):=by unfold n;push_cast;ring
  unfold E_exp
  rw [hrew,hn_cast]
  exact mlR (mlR
   (mlL h2n (inv_nonneg.mpr (mul_nonneg (sqrt_nonneg _) (exp_nonneg _)))) (exp_nonneg _)) (exp_nonneg _)
 have hEX_pos:0 < EX:=lt_of_lt_of_le (by positivity) hEX_lb
 have hmeas_s:∀ s:Finset (Fin n),MeasurableSet (aF n s):=fun s=>by
  rw [show aF n s=⋂ i:Fin n,{W | gC<=fv0 n W s i} by ext W;simp [aF]]
  exact MeasurableSet.iInter fun i=>measurableSet_le measurable_const
   (by unfold fv0;exact continuous_const.mul (continuous_finsetSum _ fun j _ => (continuous_edgeVal i j).mul continuous_const):Continuous (fun W:Ei n->R=>fv0 n W s i)).measurable
 have hX_m:Measurable (friendlyCount m) :=
  Finset.measurable_sum _ fun s _=>measurable_const.ite (hmeas_s s) measurable_const
 have hX_nn:∀ W,0<=friendlyCount m W:=fun W=>Finset.sum_nonneg fun s _=>by split_ifs <;> norm_num
 have hX_bd:∀ W,friendlyCount m W<=((bS m).card:R):=fun W=>by
  unfold friendlyCount
  calc _ <= ∑ _s ∈ bS m,(1:R):=Finset.sum_le_sum fun s _=>by split_ifs <;> norm_num
   _ = _:=by simp
 have hX_int:Integrable (friendlyCount m) (gE n) :=
  Integrable.of_bound hX_m.aestronglyMeasurable ((bS m).card:R)
   (Eventually.of_forall fun W=>by rw [Real.norm_eq_abs,aon (hX_nn W)];exact hX_bd W)
 have hX2_int:Integrable (fun W=>(friendlyCount m W)^2) (gE n) :=
  Integrable.of_bound (hX_m.pow_const 2).aestronglyMeasurable (((bS m).card:R)^2)
   (Eventually.of_forall fun W=>by
    rw [Real.norm_eq_abs,aon (sq_nonneg _)]
    exact pow_le_pow_left₀ (hX_nn W) (hX_bd W) 2)
 have hpz:=paley_zygmund (gE n) hX_nn hX_m hX_int hX2_int
 have hset_eq:{W:Ei n->R | 0 < friendlyCount m W}={W | ∃ s ∈ bS m,W ∈ aF n s}:=by
  ext W;simp only [Set.mem_ofPred_eq,friendlyCount]
  constructor
  .
   intro hpos
   by_contra hno;push Not at hno
   have h0:∑ s ∈ bS m,(if W ∈ aF n s then (1:R) else 0)=0 :=
    Finset.sum_eq_zero fun s hs=>if_neg (hno s hs)
   linarith
  .
   rintro ⟨s,hs,hWs⟩
   have h1:(1:R)<=∑ t ∈ bS m,if W ∈ aF n t then (1:R) else 0:=by
    calc (1:R)=if W ∈ aF n s then (1:R) else 0:=(if_pos hWs).symm
     _ <= _:=Finset.single_le_sum (f:=fun t=>if W ∈ aF n t then (1:R) else 0)
       (fun t _=>by split_ifs <;> norm_num) hs
   linarith
 rw [hset_eq] at hpz
 have h4m_le:4*(m:R)^2*EX<=EX^2:=by
  have hinv:EX⁻¹<=c1⁻¹*(n:R)*exp (tStar*sqrt (n:R))*E_exp⁻¹:=by
   rw [inv_le_iff_one_le_mul₀' hEX_pos]
   have hmul:c1⁻¹*(n:R)*exp (tStar*sqrt (n:R))*E_exp⁻¹ *
     (c1*(n:R)⁻¹*exp (-tStar*sqrt (n:R))*E_exp)=1:=by
    rw [show -tStar*sqrt (n:R) = -(tStar*sqrt (n:R)) by ring,exp_neg]
    field_simp [hc1_pos.ne',hn_pos.ne',(exp_pos (tStar*sqrt (n:R))).ne',hE_pos.ne']
   calc (1:R)=_:=hmul.symm
    _ <= c1⁻¹*(n:R)*exp (tStar*sqrt (n:R))*E_exp⁻¹*EX :=
      mlL hEX_lb (by positivity)
    _ = EX*(c1⁻¹*(n:R)*exp (tStar*sqrt (n:R))*E_exp⁻¹):=mul_comm _ _
  have h4m1:4*(m:R)^2*EX⁻¹<=1:=by
   refine (mlL hinv (by positivity)).trans ?_
   have hE_inv:E_exp⁻¹=exp (-(2*m:R)*(log 2+gStar)):=by
    unfold E_exp n;rw [← exp_neg];congr 1;push_cast;ring
   rw [hE_inv]
   simpa [n] using hsmall
  have:=mlR h4m1 (sq_nonneg EX)
  have hrew:4*(m:R)^2*EX⁻¹*EX^2=4*(m:R)^2*EX:=by field_simp [hEX_pos.ne']
  linarith
 have h1_le_big:(1:R)<=(c1^2)⁻¹*(n:R)^9*exp (2*tStar*sqrt (n:R)):=by
  have hc1_lt1:c1<=1:=by
   unfold c1
   have h1:(1:R)<=sqrt (2*PI)*exp (1/2):=by
    have ha:(1:R)<=sqrt (2*PI):=by
     rw [le_sqrt (by norm_num) (by positivity)];linarith [pi_gt_three]
    have hb:(1:R)<=exp (1/2):=one_le_exp (by norm_num)
    nlinarith
   have hinv:(sqrt (2*PI)*exp (1/2))⁻¹<=1:=inv_le_one_of_one_le₀ h1
   linarith
  have hc1sq:(1:R)<=(c1^2)⁻¹:=(one_le_inv₀ (sq_pos_of_pos hc1_pos)).mpr (by nlinarith)
  have hn9:(1:R)<=(n:R)^9:=one_le_pow₀ (by exact_mod_cast (by omega:1<=n))
  have hexp1:(1:R)<=exp (2*tStar*sqrt (n:R)):=by
   apply one_le_exp
   have ht:=tStar_mem;norm_num [tLInt,S0,fpS] at ht
   exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (sqrt_nonneg _)
  nlinarith [mul_le_mul hc1sq hn9 zero_le_one (by positivity)]
 have hEX2_le:EX2<=c2*(c1^2)⁻¹*(n:R)^9*exp (2*tStar*sqrt (n:R))*EX^2:=by
  have hE2_le:(n:R)^7*exp (2*(n:R)*(log 2+gStar)) <=
    (c1^2)⁻¹*(n:R)^9*exp (2*tStar*sqrt (n:R))*EX^2:=by
   have hsq_lb:=pow_le_pow_left₀ (by positivity) hEX_lb 2
   have hrew:(c1^2)⁻¹*(n:R)^9*exp (2*tStar*sqrt (n:R)) *
     (c1*(n:R)⁻¹*exp (-tStar*sqrt (n:R))*E_exp)^2 =
     (n:R)^7*exp (2*(n:R)*(log 2+gStar)):=by
    have h1:exp (2*tStar*sqrt (n:R))*(exp (-tStar*sqrt (n:R)))^2=1:=by
     rw [← exp_nat_mul,← exp_add,
      show 2*tStar*sqrt (n:R)+((2:ℕ):R)*(-tStar*sqrt (n:R))=0 by push_cast;ring,
      exp_zero]
    have h2:E_exp^2=exp (2*(n:R)*(log 2+gStar)):=by
     unfold E_exp;rw [← exp_nat_mul];congr 1;ring
    calc (c1^2)⁻¹*(n:R)^9*exp (2*tStar*sqrt (n:R)) *
       (c1*(n:R)⁻¹*exp (-tStar*sqrt (n:R))*E_exp)^2
      = ((c1^2)⁻¹*c1^2)*((n:R)^9*((n:R)⁻¹)^2) *
        (exp (2*tStar*sqrt (n:R))*(exp (-tStar*sqrt (n:R)))^2)*E_exp^2:=by ring
     _ = _:=by rw [inv_mul_cancel₀ (sq_pos_of_pos hc1_pos).ne',h1,h2];field_simp [hn_pos.ne']
   rw [← hrew]
   exact mlL hsq_lb (by positivity)
  have hstep:EX2<=EX^2+49*exp 20*((n:R)^7*exp (2*(n:R)*(log 2+gStar))):=by
   have h2nd':EX2<=4*(m:R)^2*EX+49*exp 20*((n:R)^7*exp (2*(n:R)*(log 2+gStar))):=by
    simpa [EX2,EX,n,mul_assoc] using h2nd
   linarith
  have hEX2_1:EX^2<=(c1^2)⁻¹*(n:R)^9*exp (2*tStar*sqrt (n:R))*EX^2:=by
   nlinarith [h1_le_big,sq_nonneg EX]
  unfold c2
  nlinarith [mlL hE2_le (show 0<=49*exp 20 by positivity)]
 have hEX2_pos:0 < EX2:=by
  have:0 < EX^2:=sq_pos_of_pos hEX_pos
  nlinarith [hpz,ENNReal.toReal_nonneg (a:=gE n {W | ∃ s ∈ bS m,W ∈ aF n s})]
 have hp_lb:EX^2/EX2<=(gE n {W | ∃ s ∈ bS m,W ∈ aF n s}).toReal:=by
  rwa [div_le_iff₀' hEX2_pos]
 refine le_trans ?_ hp_lb
 rw [le_div_iff₀ hEX2_pos]
 have hrew:c1^2/c2*((n:R)^9)⁻¹*exp (-2*tStar*sqrt (n:R)) *
   (c2*(c1^2)⁻¹*(n:R)^9*exp (2*tStar*sqrt (n:R))*EX^2)=EX^2:=by
  have hexp1:exp (-2*tStar*sqrt (n:R))*exp (2*tStar*sqrt (n:R))=1:=by
   rw [← exp_add,show -2*tStar*sqrt (n:R)+2*tStar*sqrt (n:R)=0 by ring,exp_zero]
  calc c1^2/c2*((n:R)^9)⁻¹*exp (-2*tStar*sqrt (n:R)) *
     (c2*(c1^2)⁻¹*(n:R)^9*exp (2*tStar*sqrt (n:R))*EX^2)
    = (c1^2*(c1^2)⁻¹)*(c2/c2)*(((n:R)^9)⁻¹*(n:R)^9) *
      (exp (-2*tStar*sqrt (n:R))*exp (2*tStar*sqrt (n:R)))*EX^2:=by ring
   _ = EX^2:=by
     rw [mul_inv_cancel₀ (sq_pos_of_pos hc1_pos).ne',div_self hc2_pos.ne',
       inv_mul_cancel₀ (pow_ne_zero 9 hn_pos.ne'),hexp1];ring
 have hfinal:=mlL hEX2_le (show 0<=c1^2/c2*((n:R)^9)⁻¹*exp (-2*tStar*sqrt (n:R)) by positivity)
 rw [hrew] at hfinal
 have hn_cast:(n:R)=(2*m:R):=by unfold n;push_cast;ring
 rwa [hn_cast] at hfinal
def sQ0 (u:R):R:=1 - u^4*(35 - 84*u+70*u^2 - 20*u^3)
def sQ1 (u:R):R:=-140*u^3*(1 - u)^3
def sQ2 (u:R):R:=-420*u^2*(1 - u)^2*(1 - 2*u)
def sQ3 (u:R):R:=-840*u*(1 - u)*(1 - 5*u+5*u^2)
lemma splineQ_hasDerivAt (u:R):HD sQ0 (sQ1 u) u:=by
 have h:sQ0=fun x:R=>1 - 35*x^4+84*x^5 - 70*x^6+20*x^7:=by
  ext x;unfold sQ0;ring
 rw [h]
 have h4:HD (fun x:R=>35*x^4) (35*(4*u^3)) u:=by
  simpa using (hdp 4 u).const_mul (35:R)
 have h5:HD (fun x:R=>84*x^5) (84*(5*u^4)) u:=by
  simpa using (hdp 5 u).const_mul (84:R)
 have h6:HD (fun x:R=>70*x^6) (70*(6*u^5)) u:=by
  simpa using (hdp 6 u).const_mul (70:R)
 have h7:HD (fun x:R=>20*x^7) (20*(7*u^6)) u:=by
  simpa using (hdp 7 u).const_mul (20:R)
 exact (((((hasDerivAt_const u (1:R)).fun_sub h4).fun_add h5).fun_sub h6).fun_add h7).congr_deriv
  (by unfold sQ1;ring)
lemma splineQ1_hasDerivAt (u:R):HD sQ1 (sQ2 u) u:=by
 have h:sQ1=fun x:R=>-140*x^3+420*x^4 - 420*x^5+140*x^6:=by
  ext x;unfold sQ1;ring
 rw [h]
 have h3:HD (fun x:R=>-140*x^3) (-140*(3*u^2)) u:=by
  simpa using (hdp 3 u).const_mul (-140:R)
 have h4:HD (fun x:R=>420*x^4) (420*(4*u^3)) u:=by
  simpa using (hdp 4 u).const_mul (420:R)
 have h5:HD (fun x:R=>420*x^5) (420*(5*u^4)) u:=by
  simpa using (hdp 5 u).const_mul (420:R)
 have h6:HD (fun x:R=>140*x^6) (140*(6*u^5)) u:=by
  simpa using (hdp 6 u).const_mul (140:R)
 exact (((h3.fun_add h4).fun_sub h5).fun_add h6).congr_deriv (by unfold sQ2;ring)
lemma splineQ2_hasDerivAt (u:R):HD sQ2 (sQ3 u) u:=by
 have h:sQ2=fun x:R=>-420*x^2+1680*x^3 - 2100*x^4+840*x^5:=by
  ext x;unfold sQ2;ring
 rw [h]
 have h2:HD (fun x:R=>-420*x^2) (-420*(2*u)) u:=by
  simpa using (hdp 2 u).const_mul (-420:R)
 have h3:HD (fun x:R=>1680*x^3) (1680*(3*u^2)) u:=by
  simpa using (hdp 3 u).const_mul (1680:R)
 have h4:HD (fun x:R=>2100*x^4) (2100*(4*u^3)) u:=by
  simpa using (hdp 4 u).const_mul (2100:R)
 have h5:HD (fun x:R=>840*x^5) (840*(5*u^4)) u:=by
  simpa using (hdp 5 u).const_mul (840:R)
 exact (((h2.fun_add h3).fun_sub h4).fun_add h5).congr_deriv (by unfold sQ3;ring)
lemma hasDerivAt_piecewise_Ioo {f P P':R->R} {a b c0 c1:R} (hab:a < b)
  (hlo:∀ x ≤ a,f x=c0) (hmid:∀ x,a<=x->x<=b->f x=P x) (hhi:∀ x,b<=x->f x=c1)
  (hP:∀ x,HD P (P' x) x) (hPa:P' a=0) (hPb:P' b=0) (x:R) :
  HD f (if a < x/\x < b then P' x else 0) x:=by
 by_cases h1:x < a
 .
  rw [if_neg (by rintro ⟨hA,_⟩;linarith)]
  refine (hasDerivAt_const x c0).congr_of_eventuallyEq ?_
  filter_upwards [eventually_lt_nhds h1] with y hy using hlo y hy.le
 by_cases h2:b < x
 .
  rw [if_neg (by rintro ⟨_,hB⟩;linarith)]
  refine (hasDerivAt_const x c1).congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds h2] with y hy using hhi y hy.le
 by_cases h3:a < x/\x < b
 .
  rw [if_pos h3]
  refine (hP x).congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds h3.1,eventually_lt_nhds h3.2] with y hy1 hy2
  exact hmid y hy1.le hy2.le
 push Not at h1 h2
 rcases eq_or_lt_of_le h1 with hax | hax
 .
  subst hax
  unfold HD;rw [if_neg (by rintro ⟨hA,_⟩;linarith),← hasDerivWithinAt_univ,← Set.Iic_union_Ici (a:=a)]
  refine HasDerivWithinAt.union ?_ ?_
  . refine ((hasDerivAt_const a c0).hasDerivWithinAt).congr (fun y hy=>hlo y hy) (hlo a le_rfl)
  .
   have hd:=(hP a).hasDerivWithinAt (s:=Set.Ici a)
   rw [hPa] at hd
   refine hd.congr_of_eventuallyEq ?_ (hmid a le_rfl hab.le)
   filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (eventually_lt_nhds hab)] with y hy1 hy2
   exact hmid y hy1 hy2.le
 .
  have hxb:b=x:=by
   by_contra hne;exact h3 ⟨hax,lt_of_le_of_ne h2 (Ne.symm hne)⟩
  subst hxb
  unfold HD;rw [if_neg (by rintro ⟨_,hB⟩;linarith),← hasDerivWithinAt_univ,← Set.Iic_union_Ici (a:=b)]
  refine HasDerivWithinAt.union ?_ ?_
  .
   have hd:=(hP b).hasDerivWithinAt (s:=Set.Iic b)
   rw [hPb] at hd
   refine hd.congr_of_eventuallyEq ?_ (hmid b hab.le le_rfl)
   filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (eventually_gt_nhds hab)] with y hy1 hy2
   exact hmid y hy2.le hy1
  . refine ((hasDerivAt_const b c1).hasDerivWithinAt).congr (fun y hy=>hhi y hy) (hhi b le_rfl)
noncomputable def psi (x:R):R :=
 if x<=1/40 then 1 else if x < 1/20 then sQ0 (40*x - 1) else 0
noncomputable def psi1 (x:R):R :=
 if 1/40 < x/\x < 1/20 then 40*sQ1 (40*x - 1) else 0
noncomputable def psi2 (x:R):R :=
 if 1/40 < x/\x < 1/20 then 1600*sQ2 (40*x - 1) else 0
noncomputable def psi3 (x:R):R :=
 if 1/40 < x/\x < 1/20 then 64000*sQ3 (40*x - 1) else 0
lemma psi_hasDerivAt (x:R):HD psi (psi1 x) x:=by
 unfold psi1
 refine hasDerivAt_piecewise_Ioo (P:=fun y=>sQ0 (40*y - 1))
  (P':=fun y=>40*sQ1 (40*y - 1)) (a:=1/40) (b:=1/20) (c0:=1) (c1:=0)
  (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ x
 . intro y hy;unfold psi;rw [if_pos hy]
 .
  intro y hy1 hy2;unfold psi
  rcases eq_or_lt_of_le hy1 with rfl | hlt
  . rw [if_pos le_rfl];norm_num [sQ0]
  .
   rw [if_neg (not_le.mpr hlt)]
   rcases eq_or_lt_of_le hy2 with rfl | hlt2
   . rw [if_neg (lt_irrefl _)];norm_num [sQ0]
   . rw [if_pos hlt2]
 . intro y hy;unfold psi;rw [if_neg (by linarith),if_neg (by linarith)]
 .
  intro y
  have haff:HD (fun z:R=>40*z - 1) 40 y :=
   (((hdi y).const_mul (40:R)).sub_const 1).congr_deriv (by ring)
  have hc:HD (sQ0 ∘ fun z:R=>40*z - 1) (sQ1 (40*y - 1)*40) y :=
   (splineQ_hasDerivAt (40*y - 1)).comp y haff
  exact hc.congr_deriv (by ring)
 . norm_num [sQ1]
 . norm_num [sQ1]
lemma psi1_hasDerivAt (x:R):HD psi1 (psi2 x) x:=by
 unfold psi2
 refine hasDerivAt_piecewise_Ioo (P:=fun y=>40*sQ1 (40*y - 1))
  (P':=fun y=>1600*sQ2 (40*y - 1)) (a:=1/40) (b:=1/20) (c0:=0) (c1:=0)
  (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ x
 . intro y hy;unfold psi1;rw [if_neg (by rintro ⟨hA,_⟩;linarith)]
 .
  intro y hy1 hy2;unfold psi1
  by_cases h:1/40 < y/\y < 1/20
  . rw [if_pos h]
  .
   rw [if_neg h]
   rcases eq_or_lt_of_le hy1 with rfl | hlt
   . norm_num [sQ1]
   .
    have:y=1/20:=by by_contra hne;exact h ⟨hlt,lt_of_le_of_ne hy2 hne⟩
    subst this;norm_num [sQ1]
 . intro y hy;unfold psi1;rw [if_neg (by rintro ⟨_,hB⟩;linarith)]
 .
  intro y
  have haff:HD (fun z:R=>40*z - 1) 40 y :=
   (((hdi y).const_mul (40:R)).sub_const 1).congr_deriv (by ring)
  have hc:HD (fun z:R=>40*(sQ1 ∘ fun w:R=>40*w - 1) z) (40*(sQ2 (40*y - 1)*40)) y :=
   ((splineQ1_hasDerivAt (40*y - 1)).comp y haff).const_mul (40:R)
  exact hc.congr_deriv (by ring)
 . norm_num [sQ2]
 . norm_num [sQ2]
lemma psi2_hasDerivAt (x:R):HD psi2 (psi3 x) x:=by
 unfold psi3
 refine hasDerivAt_piecewise_Ioo (P:=fun y=>1600*sQ2 (40*y - 1))
  (P':=fun y=>64000*sQ3 (40*y - 1)) (a:=1/40) (b:=1/20) (c0:=0) (c1:=0)
  (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ x
 . intro y hy;unfold psi2;rw [if_neg (by rintro ⟨hA,_⟩;linarith)]
 .
  intro y hy1 hy2;unfold psi2
  by_cases h:1/40 < y/\y < 1/20
  . rw [if_pos h]
  .
   rw [if_neg h]
   rcases eq_or_lt_of_le hy1 with rfl | hlt
   . norm_num [sQ2]
   .
    have:y=1/20:=by by_contra hne;exact h ⟨hlt,lt_of_le_of_ne hy2 hne⟩
    subst this;norm_num [sQ2]
 . intro y hy;unfold psi2;rw [if_neg (by rintro ⟨_,hB⟩;linarith)]
 .
  intro y
  have haff:HD (fun z:R=>40*z - 1) 40 y :=
   (((hdi y).const_mul (40:R)).sub_const 1).congr_deriv (by ring)
  have hc:HD (fun z:R=>1600*(sQ2 ∘ fun w:R=>40*w - 1) z) (1600*(sQ3 (40*y - 1)*40)) y :=
   ((splineQ2_hasDerivAt (40*y - 1)).comp y haff).const_mul (1600:R)
  exact hc.congr_deriv (by ring)
 . norm_num [sQ3]
 . norm_num [sQ3]
lemma psi_eq_one {x:R} (hx:x<=gC/2):psi x=1:=by
 unfold psi;rw [if_pos (by unfold gC at hx;linarith)]
lemma psi_eq_zero {x:R} (hx:gC<=x):psi x=0:=by
 unfold psi;unfold gC at hx;rw [if_neg (by linarith),if_neg (by linarith)]
lemma psi_bounds (x:R):0<=psi x/\psi x<=1:=by
 unfold psi
 split_ifs with h1 h2
 . exact ⟨by norm_num,le_rfl⟩
 .
  have hu0:0<=40*x - 1:=by linarith
  have hu1:40*x - 1<=1:=by linarith
  have hanti:AntitoneOn sQ0 (Set.Icc 0 1):=by
   refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    (fun y _=>(splineQ_hasDerivAt y).continuousAt.continuousWithinAt)
    (fun y _=>(splineQ_hasDerivAt y).differentiableAt.differentiableWithinAt) ?_
   intro y hy
   rw [interior_Icc] at hy
   rw [(splineQ_hasDerivAt y).deriv]
   unfold sQ1
   have h1':0<=y^3:=pow_nonneg hy.1.le 3
   have h2':0<=(1 - y)^3:=pow_nonneg (by linarith [hy.2]) 3
   nlinarith
  have hge:sQ0 1<=sQ0 (40*x - 1):=hanti ⟨hu0,hu1⟩ ⟨by norm_num,le_rfl⟩ hu1
  have hle:sQ0 (40*x - 1)<=sQ0 0:=hanti ⟨le_rfl,by norm_num⟩ ⟨hu0,hu1⟩ hu0
  have hq0:sQ0 0=1:=by norm_num [sQ0]
  have hq1:sQ0 1=0:=by norm_num [sQ0]
  rw [hq1] at hge;rw [hq0] at hle
  exact ⟨hge,hle⟩
 . exact ⟨le_rfl,by norm_num⟩
lemma psi1_abs_le (x:R):|psi1 x| <= 120:=by
 unfold psi1
 split_ifs with h
 .
  set u:=40*x - 1
  have hu0:0<=u:=by linarith [h.1]
  have hu1:0<=1 - u:=by linarith [h.2]
  have hprod:0<=u*(1 - u)/\u*(1 - u)<=1/4:=⟨mul_nonneg hu0 hu1,by nlinarith [sq_nonneg (u - 1/2)]⟩
  have hcub:(u*(1 - u))^3<=(1/4:R)^3:=pow_le_pow_left₀ hprod.1 hprod.2 3
  unfold sQ1
  rw [show 40*(-140*u^3*(1 - u)^3) = -5600*(u*(1 - u))^3 by ring,
    abs_mul,abs_neg,aon (by norm_num:(0:R)<=5600),
    aon (pow_nonneg hprod.1 3)]
  nlinarith
 . norm_num
lemma psi2_abs_le (x:R):|psi2 x| <= 48000:=by
 unfold psi2
 split_ifs with h
 .
  set u:=40*x - 1
  have hu0:0<=u:=by linarith [h.1]
  have hu1:0<=1 - u:=by linarith [h.2]
  have hprod:0<=u*(1 - u)/\u*(1 - u)<=1/4:=⟨mul_nonneg hu0 hu1,by nlinarith [sq_nonneg (u - 1/2)]⟩
  have hsq:(u*(1 - u))^2<=(1/4:R)^2:=pow_le_pow_left₀ hprod.1 hprod.2 2
  have hmid:|1 - 2*u| <= 1:=abs_le.mpr ⟨by linarith,by linarith⟩
  unfold sQ2
  rw [show 1600*(-420*u^2*(1 - u)^2*(1 - 2*u)) =
    (-672000*(u*(1 - u))^2)*(1 - 2*u) by ring,
    abs_mul,abs_mul,abs_neg,aon (by norm_num:(0:R)<=672000),
    aon (pow_nonneg hprod.1 2)]
  have h1:672000*(u*(1 - u))^2<=48000:=by nlinarith
  nlinarith [abs_nonneg (1 - 2*u)]
 . norm_num
lemma psi3_abs_le (x:R):|psi3 x| <= 13440000:=by
 unfold psi3
 split_ifs with h
 .
  set u:=40*x - 1
  have hu0:0<=u:=by linarith [h.1]
  have hu1:0<=1 - u:=by linarith [h.2]
  have hprod:0<=u*(1 - u)/\u*(1 - u)<=1/4:=⟨mul_nonneg hu0 hu1,by nlinarith [sq_nonneg (u - 1/2)]⟩
  have hpoly:|1 - 5*u+5*u^2| <= 1:=by
   have:1 - 5*u+5*u^2=1 - 5*(u*(1 - u)):=by ring
   rw [this,abs_le];constructor <;> linarith [hprod.1,hprod.2]
  unfold sQ3
  rw [show 64000*(-840*u*(1 - u)*(1 - 5*u+5*u^2)) =
    (-53760000*(u*(1 - u)))*(1 - 5*u+5*u^2) by ring,
    abs_mul,abs_mul,abs_neg,aon (by norm_num:(0:R)<=53760000),
    aon hprod.1]
  have h1:53760000*(u*(1 - u))<=13440000:=by linarith [hprod.2]
  nlinarith [abs_nonneg (1 - 5*u+5*u^2)]
 . norm_num
lemma psi_continuous:Continuous psi:=fun_prop_or_deriv where
 fun_prop_or_deriv:=continuous_iff_continuousAt.mpr fun x=>(psi_hasDerivAt x).continuousAt
lemma psi1_continuous:Continuous psi1 :=
 continuous_iff_continuousAt.mpr fun x=>(psi1_hasDerivAt x).continuousAt
noncomputable def badFrac (m:ℕ) (A:Ei (2*m)->R) (s:Finset (Fin (2*m))):R :=
 (1/(2*m:R))*∑ i:Fin (2*m),psi (fv0 (2*m) A s i)
noncomputable def sM (m:ℕ) (lam:R) (A:Ei (2*m)->R):R :=
 -(1/(lam*(2*m:R))) *
  log (((bS m).card:R)⁻¹*∑ s ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i)))
lemma bisections_nonempty (m:ℕ):(bS m).Nonempty:=by
 have hc:0 < (bS m).card:=by
  rw [card_bisections];exact Nat.choose_pos (by omega)
 exact Finset.card_pos.mp hc
lemma sMb {m:ℕ} (hm:1<=m) {lam:R} (hlam:0 < lam) (A:Ei (2*m)->R) :
  0<=sM m lam A/\sM m lam A<=1:=by
 have hn:(0:R) < (2*m:R):=by positivity
 have hln:0 < lam*(2*m:R):=mul_pos hlam hn
 have hcard:(0:R) < ((bS m).card:R):=by exact_mod_cast (bisections_nonempty m).card_pos
 have hsum_le:∑ s ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i)) <=
   ((bS m).card:R):=by
  calc _ <= ∑ _s ∈ bS m,(1:R):=Finset.sum_le_sum fun s _=>by rw [← exp_zero];apply exp_le_exp.mpr;have hnn:0<=∑ i:Fin (2*m),psi (fv0 (2*m) A s i):=Finset.sum_nonneg fun i _=>(psi_bounds _).1;nlinarith
   _ = ((bS m).card:R):=by simp
 have hsum_ge:((bS m).card:R)*exp (-lam*(2*m:R)) <=
   ∑ s ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i)):=by
  calc ((bS m).card:R)*exp (-lam*(2*m:R))
    = ∑ _s ∈ bS m,exp (-lam*(2*m:R)):=by simp
   _ <= _:=Finset.sum_le_sum fun s _=>by
      apply exp_le_exp.mpr
      have hle:∑ i:Fin (2*m),psi (fv0 (2*m) A s i)<=(2*m:R):=by
       calc _ <= ∑ _i:Fin (2*m),(1:R):=Finset.sum_le_sum fun i _=>(psi_bounds _).2
        _ = (2*m:R):=by simp
      nlinarith
 have havg_pos:0 < ((bS m).card:R)⁻¹ *
   ∑ s ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i)) :=
  mul_pos (inv_pos.mpr hcard) (Finset.sum_pos (fun s _=>exp_pos _) (bisections_nonempty m))
 have havg_le:((bS m).card:R)⁻¹ *
   ∑ s ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i))<=1:=by
  rw [inv_mul_le_iff₀ hcard];linarith
 have havg_ge:exp (-lam*(2*m:R))<=((bS m).card:R)⁻¹ *
   ∑ s ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i)):=by
  rw [le_inv_mul_iff₀ hcard];linarith
 unfold sM
 constructor
 .
  have hlog:log (((bS m).card:R)⁻¹ *
    ∑ s ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i)))<=0 :=
   log_nonpos havg_pos.le havg_le
  nlinarith [div_pos one_pos hln]
 .
  have hlog:-lam*(2*m:R)<=log (((bS m).card:R)⁻¹ *
    ∑ s ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i))):=by
   have:=log_le_log (exp_pos _) havg_ge
   rwa [log_exp] at this
  have hmul:=mlN hlog (show -(1/(lam*(2*m:R)))<=0 by
   have:0 < 1/(lam*(2*m:R)):=div_pos one_pos hln;linarith)
  refine hmul.trans_eq ?_
  field_simp [hlam.ne',hn.ne']
lemma softMin_ge_exists_badFrac {m:ℕ} (hm:1<=m) {lam:R} (hlam:0 < lam)
  (A:Ei (2*m)->R) :
  ∃ s ∈ bS m,badFrac m A s<=sM m lam A:=by
 obtain ⟨s0,hs0,hmin⟩:=Finset.exists_min_image (bS m) (fun s=>badFrac m A s) (bisections_nonempty m)
 refine ⟨s0,hs0,?_⟩
 have hn:(0:R) < (2*m:R):=by positivity
 have hln:0 < lam*(2*m:R):=mul_pos hlam hn
 have hcard:(0:R) < ((bS m).card:R):=by exact_mod_cast (bisections_nonempty m).card_pos
 have hsum_le:∑ s ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i)) <=
   ((bS m).card:R)*exp (-lam*(2*m:R)*badFrac m A s0):=by
  calc _ <= ∑ _s ∈ bS m,exp (-lam*(2*m:R)*badFrac m A s0):=by refine Finset.sum_le_sum fun s hs=>exp_le_exp.mpr ?_;have hle:=hmin s hs;have hrew:∑ i:Fin (2*m),psi (fv0 (2*m) A s i)=(2*m:R)*badFrac m A s:=by { unfold badFrac;field_simp [hn.ne'] };rw [hrew];nlinarith
   _ = _:=by simp
 have havg_pos:0 < ((bS m).card:R)⁻¹ *
   ∑ s ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i)) :=
  mul_pos (inv_pos.mpr hcard) (Finset.sum_pos (fun s _=>exp_pos _) (bisections_nonempty m))
 have havg_le:((bS m).card:R)⁻¹ *
   ∑ s ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i)) <=
   exp (-lam*(2*m:R)*badFrac m A s0):=by
  rw [inv_mul_le_iff₀ hcard];exact hsum_le
 have hlog:log (((bS m).card:R)⁻¹ *
   ∑ s ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i))) <=
   -lam*(2*m:R)*badFrac m A s0:=by
  simpa [log_exp] using log_le_log havg_pos havg_le
 unfold sM
 have hmul:=mlN hlog (show -(1/(lam*(2*m:R)))<=0 by
  have:0 < 1/(lam*(2*m:R)):=div_pos one_pos hln;linarith)
 refine le_trans ?_ hmul
 apply le_of_eq;field_simp [hlam.ne',hn.ne']
lemma softMin_le_of_mem_allFriendly {m:ℕ} (hm:1<=m) {lam:R} (hlam:0 < lam)
  {A:Ei (2*m)->R} {s:Finset (Fin (2*m))} (hs:s ∈ bS m)
  (hA:A ∈ aF (2*m) s) :
  sM m lam A<=log 2/lam:=by
 have hn:(0:R) < (2*m:R):=by positivity
 have hln:0 < lam*(2*m:R):=mul_pos hlam hn
 have hcard_pos:(0:R) < ((bS m).card:R):=by exact_mod_cast (bisections_nonempty m).card_pos
 have hcard_le:((bS m).card:R)<=(2:R)^(2*m):=by
  rw [card_bisections]
  have hnat:(2*m).choose m<=2^(2*m):=by
   have:=Nat.sum_range_choose (2*m)
   have hmem:m ∈ Finset.range (2*m+1):=Finset.mem_range.mpr (by omega)
   exact (Finset.single_le_sum (f:=fun k=>(2*m).choose k) (fun _ _=>Nat.zero_le _) hmem).trans this.le
  exact_mod_cast hnat
 have hsum_zero:∑ i:Fin (2*m),psi (fv0 (2*m) A s i)=0 :=
  Finset.sum_eq_zero fun i _=>psi_eq_zero (hA i)
 have hsum_ge:(1:R)<=∑ t ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A t i)):=by
  calc (1:R)=exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i)):=by rw [hsum_zero,mul_zero,exp_zero]
   _ <= _:=Finset.single_le_sum (f:=fun t=>exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A t i)))
     (fun t _=>(exp_pos _).le) hs
 have havg_ge:((bS m).card:R)⁻¹<=((bS m).card:R)⁻¹ *
   ∑ t ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A t i)):=by
  nlinarith [inv_pos.mpr hcard_pos]
 have hlog:-((2*m:R)*log 2)<=log (((bS m).card:R)⁻¹ *
   ∑ t ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A t i))):=by
  have h1:=log_le_log (inv_pos.mpr hcard_pos) havg_ge
  rw [log_inv] at h1
  have h2:log ((bS m).card:R)<=(2*m:R)*log 2:=by
   calc log ((bS m).card:R)<=log ((2:R)^(2*m)):=log_le_log hcard_pos hcard_le
    _ = (2*m:R)*log 2:=by rw [log_pow];push_cast;ring
  linarith
 unfold sM
 have hmul:=mlN hlog (show -(1/(lam*(2*m:R)))<=0 by
  have:0 < 1/(lam*(2*m:R)):=div_pos one_pos hln;linarith)
 refine hmul.trans_eq ?_
 field_simp [hlam.ne',hn.ne']
lemma sMc (m:ℕ) (lam:R):Continuous (sM m lam):=by
 have hfield:∀ s i,Continuous (fun A:Ei (2*m)->R=>fv0 (2*m) A s i):=fun s i=>by
  unfold fv0 ev0
  refine continuous_const.mul (continuous_finset_sum _ fun j _=>?_)
  split_ifs <;> fun_prop
 unfold sM
 refine continuous_const.mul (Continuous.log ?_ ?_)
 .
  refine continuous_const.mul (continuous_finset_sum _ fun s _=>?_)
  exact continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun i _=>psi_continuous.comp (hfield s i)))
 .
  intro A
  have hcard:(0:R) < ((bS m).card:R):=by exact_mod_cast (bisections_nonempty m).card_pos
  exact (mul_pos (inv_pos.mpr hcard) (Finset.sum_pos (fun s _=>exp_pos _) (bisections_nonempty m))).ne'
lemma log_sum_exp_derivs {ι:Type*} (S:Finset ι) (hS:S.Nonempty) (c:R) (hc:0 < c)
  (u u1 u2 u3:ι->R->R) {M1 M2 M3:R} (hM1:0<=M1) (hM2:0<=M2) (hM3:0<=M3)
  (hd1:∀ s ∈ S,∀ x,HD (u s) (u1 s x) x)
  (hd2:∀ s ∈ S,∀ x,HD (u1 s) (u2 s x) x)
  (hd3:∀ s ∈ S,∀ x,HD (u2 s) (u3 s x) x)
  (hb1:∀ s ∈ S,∀ x,|u1 s x| <= M1)
  (hb2:∀ s ∈ S,∀ x,|u2 s x| <= M2)
  (hb3:∀ s ∈ S,∀ x,|u3 s x| <= M3) :
  let G:=fun x=>log (c*∑ s ∈ S,exp (u s x))
  let Z:=fun x=>∑ s ∈ S,exp (u s x)
  let Z1:=fun x=>∑ s ∈ S,exp (u s x)*u1 s x
  let Z2:=fun x=>∑ s ∈ S,exp (u s x)*(u2 s x+(u1 s x)^2)
  let Z3:=fun x=>∑ s ∈ S,exp (u s x)*(u3 s x+3*u1 s x*u2 s x+(u1 s x)^3)
  let G1:=fun x=>Z1 x/Z x
  let G2:=fun x=>Z2 x/Z x - (Z1 x/Z x)^2
  let G3:=fun x=>Z3 x/Z x - 3*(Z2 x/Z x)*(Z1 x/Z x)+2*(Z1 x/Z x)^3
  (∀ x,HD G (G1 x) x) /\
  (∀ x,HD G1 (G2 x) x) /\
  (∀ x,HD G2 (G3 x) x) /\
  (∀ x,|G1 x| <= M1) /\
  (∀ x,|G3 x| <= M3+6*M1*M2+6*M1^3):=by
 intro G Z Z1 Z2 Z3 G1 G2 G3
 have hZpos:∀ x,0 < Z x:=fun x=>Finset.sum_pos (fun s _=>exp_pos _) hS
 have hZ1d:∀ x,HD Z (Z1 x) x:=fun x=>by
  simpa [Z,Z1] using HasDerivAt.fun_sum (u:=S) fun s hs=>(hd1 s hs x).exp
 have hZ2d:∀ x,HD Z1 (Z2 x) x:=fun x =>
  (HasDerivAt.fun_sum (u:=S) fun s hs=>((hd1 s hs x).exp).fun_mul (hd2 s hs x)).congr_deriv
   (by dsimp only [Z2];refine Finset.sum_congr rfl fun s _=>?_;ring)
 have hZ3d:∀ x,HD Z2 (Z3 x) x:=fun x =>
  (HasDerivAt.fun_sum (u:=S) fun s hs =>
   ((hd1 s hs x).exp).fun_mul ((hd3 s hs x).fun_add ((hd2 s hs x).pow 2))).congr_deriv
   (by dsimp only [Z3];refine Finset.sum_congr rfl fun s _=>?_;norm_num;ring)
 have hG1d:∀ x,HD G (G1 x) x:=fun x =>
  (((hZ1d x).const_mul c).log (mul_pos hc (hZpos x)).ne').congr_deriv
   (by dsimp only [G1];field_simp [hc.ne',(hZpos x).ne'])
 have hG2d:∀ x,HD G1 (G2 x) x:=fun x =>
  ((hZ2d x).fun_div (hZ1d x) (hZpos x).ne').congr_deriv
   (by dsimp only [G2];field_simp [(hZpos x).ne'])
 have hG3d:∀ x,HD G2 (G3 x) x:=fun x =>
  (((hZ3d x).fun_div (hZ1d x) (hZpos x).ne').fun_sub ((hG2d x).pow 2)).congr_deriv
   (by dsimp only [G3,G2,G1];norm_num;field_simp [(hZpos x).ne'];ring)
 have hw_bd:∀ (x:R) (f:ι->R) (B:R),(∀ s ∈ S,|f s| <= B) ->
   |∑ s ∈ S,exp (u s x)*f s| / Z x<=B:=fun x f B hB=>by
  rw [div_le_iff₀ (hZpos x)]
  calc |∑ s ∈ S,exp (u s x)*f s|
    <= ∑ s ∈ S,|exp (u s x)*f s| := Finset.abs_sum_le_sum_abs _ _
   _ = ∑ s ∈ S,exp (u s x) * |f s| := Finset.sum_congr rfl fun s _=>by
      rw [abs_mul,abs_of_pos (exp_pos _)]
   _ <= ∑ s ∈ S,exp (u s x)*B:=Finset.sum_le_sum fun s hs =>
      mlL (hB s hs) (exp_pos _).le
   _ = B*Z x:=by rw [← Finset.sum_mul,mul_comm]
 have hG1_bd:∀ x,|G1 x| <= M1:=fun x=>by
  unfold G1;rw [abs_div,abs_of_pos (hZpos x)];exact hw_bd x (fun s=>u1 s x) M1 (fun s hs=>hb1 s hs x)
 have hG3_bd:∀ x,|G3 x| <= M3+6*M1*M2+6*M1^3:=fun x=>by
  have h1:|Z1 x/Z x| <= M1:=hG1_bd x
  have h2:|Z2 x/Z x| <= M2+M1^2:=by
   rw [abs_div,abs_of_pos (hZpos x)]
   refine hw_bd x (fun s=>u2 s x+(u1 s x)^2) (M2+M1^2) fun s hs=>?_
   have:=hb1 s hs x;have:=hb2 s hs x
   have hsq:|(u1 s x)^2| <= M1^2:=by rw [abs_pow];exact pow_le_pow_left₀ (abs_nonneg _) (hb1 s hs x) 2
   exact (abs_add_le _ _).trans (add_le_add (hb2 s hs x) hsq)
  have h3:|Z3 x/Z x| <= M3+3*M1*M2+M1^3:=by
   rw [abs_div,abs_of_pos (hZpos x)]
   refine hw_bd x (fun s=>u3 s x+3*u1 s x*u2 s x+(u1 s x)^3) (M3+3*M1*M2+M1^3) fun s hs=>?_
   have hb1s:=hb1 s hs x;have hb2s:=hb2 s hs x;have hb3s:=hb3 s hs x
   have hm12:|3*u1 s x*u2 s x| <= 3*M1*M2:=by
    rw [abs_mul,abs_mul,aon (by norm_num:(0:R)<=3)]
    nlinarith [abs_nonneg (u1 s x),abs_nonneg (u2 s x)]
   have hcub:|(u1 s x)^3| <= M1^3:=by rw [abs_pow];exact pow_le_pow_left₀ (abs_nonneg _) hb1s 3
   exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hb3s hm12)) hcub)
  have ha:|3*(Z2 x/Z x)*(Z1 x/Z x)| <= 3*(M2+M1^2)*M1:=by
   rw [abs_mul,abs_mul,aon (by norm_num:(0:R)<=3)]
   nlinarith [abs_nonneg (Z2 x/Z x),abs_nonneg (Z1 x/Z x)]
  have hb:|2*(Z1 x/Z x)^3| <= 2*M1^3:=by
   rw [abs_mul,abs_pow,aon (by norm_num:(0:R)<=2)]
   nlinarith [pow_le_pow_left₀ (abs_nonneg (Z1 x/Z x)) h1 3]
  unfold G3
  calc |Z3 x/Z x - 3*(Z2 x/Z x)*(Z1 x/Z x)+2*(Z1 x/Z x)^3|
    <= |Z3 x/Z x - 3*(Z2 x/Z x)*(Z1 x/Z x)| + |2*(Z1 x/Z x)^3| := abs_add_le _ _
   _ <= (|Z3 x/Z x| + |3*(Z2 x/Z x)*(Z1 x/Z x)|) + |2*(Z1 x/Z x)^3| :=
     add_le_add (abs_sub _ _) le_rfl
   _ <= (M3+3*M1*M2+M1^3)+3*(M2+M1^2)*M1+2*M1^3:=by linarith
   _ = M3+6*M1*M2+6*M1^3:=by ring
 exact ⟨hG1d,hG2d,hG3d,hG1_bd,hG3_bd⟩
lemma fieldVal_update_deriv {n:ℕ} (A:Ei n->R) (e:Ei n) (s:Finset (Fin n)) (i:Fin n) :
  let c:=if i=e.1.1\/i=e.1.2 then (sqrt (n:R))⁻¹*(spin s e.1.1*spin s e.1.2) else 0
  ∀ x,HD (fun y=>fv0 n (Function.update A e y) s i) c x:=by
 intro c x
 unfold fv0
 have hsum:∀ j:Fin n,HD (fun y=>ev0 (Function.update A e y) i j*(spin s i*spin s j))
   (if (i=e.1.1/\j=e.1.2)\/(i=e.1.2/\j=e.1.1) then spin s e.1.1*spin s e.1.2 else 0) x:=by
  intro j
  by_cases hij:i < j
  .
   by_cases he:(⟨(i,j),hij⟩:Ei n)=e
   .
    have hi:i=e.1.1:=by rw [← he]
    have hj:j=e.1.2:=by rw [← he]
    rw [if_pos (Or.inl ⟨hi,hj⟩)]
    have heq:(fun y=>ev0 (Function.update A e y) i j*(spin s i*spin s j)) =
      fun y=>y*(spin s e.1.1*spin s e.1.2):=by
     ext y;unfold ev0;rw [dif_pos hij,he,Function.update_self,hi,hj]
    rw [heq];simpa using (hdi x).mul_const (spin s e.1.1*spin s e.1.2)
   .
    have hne:¬((i=e.1.1/\j=e.1.2)\/(i=e.1.2/\j=e.1.1)):=by
     rintro (⟨rfl,rfl⟩ | ⟨h1,h2⟩)
     . exact he (Subtype.ext rfl)
     . exact lt_asymm hij (h1 ▸ h2 ▸ e.2)
    rw [if_neg hne]
    have heq:(fun y=>ev0 (Function.update A e y) i j*(spin s i*spin s j)) =
      fun _=>A ⟨(i,j),hij⟩*(spin s i*spin s j):=by
     ext y;simp [ev0,hij,Function.update_of_ne he]
    rw [heq];exact hasDerivAt_const x _
  .
   by_cases hji:j < i
   .
    by_cases he:(⟨(j,i),hji⟩:Ei n)=e
    .
     have hj:j=e.1.1:=by rw [← he]
     have hi:i=e.1.2:=by rw [← he]
     rw [if_pos (Or.inr ⟨hi,hj⟩)]
     have heq:(fun y=>ev0 (Function.update A e y) i j*(spin s i*spin s j)) =
       fun y=>y*(spin s e.1.1*spin s e.1.2):=by
      ext y;unfold ev0;rw [dif_neg hij,dif_pos hji,he,Function.update_self,hi,hj,mul_comm (spin s e.1.2)]
     rw [heq];simpa using (hdi x).mul_const (spin s e.1.1*spin s e.1.2)
    .
     have hne:¬((i=e.1.1/\j=e.1.2)\/(i=e.1.2/\j=e.1.1)):=by
      rintro (⟨h1,h2⟩ | ⟨rfl,rfl⟩)
      . exact lt_asymm hji (h1 ▸ h2 ▸ e.2)
      . exact he (Subtype.ext rfl)
     rw [if_neg hne]
     have heq:(fun y=>ev0 (Function.update A e y) i j*(spin s i*spin s j)) =
       fun _=>A ⟨(j,i),hji⟩*(spin s i*spin s j):=by
      ext y;simp [ev0,hij,hji,Function.update_of_ne he]
     rw [heq];exact hasDerivAt_const x _
   .
    have hne:¬((i=e.1.1/\j=e.1.2)\/(i=e.1.2/\j=e.1.1)):=by
     have:i=j:=le_antisymm (not_lt.mp hji) (not_lt.mp hij)
     subst this;rintro (⟨h1,h2⟩ | ⟨h1,h2⟩)
     . exact e.2.ne (h1.symm.trans h2)
     . exact e.2.ne (h2.symm.trans h1)
    rw [if_neg hne]
    have heq:(fun y=>ev0 (Function.update A e y) i j*(spin s i*spin s j))=fun _=>0:=by
     ext y;simp [ev0,hij,hji]
    rw [heq];exact hasDerivAt_const x 0
 refine ((HasDerivAt.fun_sum (u:=Finset.univ) fun j _=>hsum j).const_mul (sqrt (n:R))⁻¹).congr_deriv ?_
 dsimp only [c]
 by_cases hi1:i=e.1.1
 .
  rw [if_pos (Or.inl hi1)];congr 1
  rw [Finset.sum_eq_single e.1.2]
  . rw [if_pos (Or.inl ⟨hi1,rfl⟩)]
  .
   intro j _ hj;rw [if_neg];rintro (⟨_,h2⟩ | ⟨h1,_⟩)
   . exact hj h2
   . exact e.2.ne (hi1.symm.trans h1)
  . intro h;exact absurd (Finset.mem_univ _) h
 .
  by_cases hi2:i=e.1.2
  .
   rw [if_pos (Or.inr hi2)];congr 1
   rw [Finset.sum_eq_single e.1.1]
   . rw [if_pos (Or.inr ⟨hi2,rfl⟩)]
   .
    intro j _ hj;rw [if_neg];rintro (⟨h1,_⟩ | ⟨_,h2⟩)
    . exact hi1 h1
    . exact hj h2
   . intro h;exact absurd (Finset.mem_univ _) h
  .
   rw [if_neg (by tauto),mul_eq_zero];right
   exact Finset.sum_eq_zero fun j _=>if_neg (by tauto)
lemma softMin_coord_derivs {m:ℕ} (hm:1<=m) {lam:R} (hlam:0 < lam)
  (A:Ei (2*m)->R) (e:Ei (2*m)) :
  ∃ g1 g2 g3:R->R,
   (∀ x,HD (fun y=>sM m lam (Function.update A e y)) (g1 x) x) /\
   (∀ x,HD g1 (g2 x) x) /\
   (∀ x,HD g2 (g3 x) x) /\
   (∀ x,|g1 x| <= 240/((2*m:R)*sqrt (2*m:R))) /\
   (∀ x,|g3 x| <= (26880000+138240000*lam+82944000*lam^2) /
     ((2*m:R)^2*sqrt (2*m:R))):=by
 let n:ℕ:=2*m
 have hn:(0:R) < (n:R):=by positivity
 have hsn:0 < sqrt (n:R):=sqrt_pos.mpr hn
 have hcard:(0:R) < ((bS m).card:R):=by exact_mod_cast (bisections_nonempty m).card_pos
 let c:Finset (Fin n)->Fin n->R:=fun s i =>
  if i=e.1.1\/i=e.1.2 then (sqrt (n:R))⁻¹*(spin s e.1.1*spin s e.1.2) else 0
 let u:Finset (Fin n)->R->R:=fun s x=>-lam*∑ i:Fin n,psi (fv0 n (Function.update A e x) s i)
 let u1:Finset (Fin n)->R->R:=fun s x=>-lam*∑ i:Fin n,psi1 (fv0 n (Function.update A e x) s i)*c s i
 let u2:Finset (Fin n)->R->R:=fun s x=>-lam*∑ i:Fin n,psi2 (fv0 n (Function.update A e x) s i)*(c s i)^2
 let u3:Finset (Fin n)->R->R:=fun s x=>-lam*∑ i:Fin n,psi3 (fv0 n (Function.update A e x) s i)*(c s i)^3
 have hc_abs:∀ s i,|c s i| = if i=e.1.1\/i=e.1.2 then (sqrt (n:R))⁻¹ else 0:=fun s i=>by
  unfold c;split_ifs
  .
   rw [abs_mul,abs_of_pos (inv_pos.mpr hsn)]
   have hsq:|spin s e.1.1*spin s e.1.2| = 1:=by
    have h1:(spin s e.1.1*spin s e.1.2)^2=1:=spin_mul_sq s _ _
    nlinarith [sq_abs (spin s e.1.1*spin s e.1.2),abs_nonneg (spin s e.1.1*spin s e.1.2)]
   rw [hsq,mul_one]
  . simp
 have hsum_c':∀ (s:Finset (Fin n)) (k:ℕ),1<=k->∀ (f:Fin n->R) (B:R),0<=B->(∀ i,|f i| <= B) ->
   |∑ i:Fin n,f i*(c s i)^k| <= 2*B*((sqrt (n:R))⁻¹)^k:=fun s k hk f B hB hf=>by
  calc |∑ i:Fin n,f i*(c s i)^k|
    <= ∑ i:Fin n,|f i*(c s i)^k| := Finset.abs_sum_le_sum_abs _ _
   _ = ∑ i:Fin n,|f i| * |c s i| ^ k:=Finset.sum_congr rfl fun i _=>by rw [abs_mul,abs_pow]
   _ <= ∑ i:Fin n,if i=e.1.1\/i=e.1.2 then B*((sqrt (n:R))⁻¹)^k else 0:=by
     refine Finset.sum_le_sum fun i _=>?_
     rw [hc_abs];split_ifs
     . exact mlR (hf i) (by positivity)
     . rw [zero_pow (by omega:k ≠ 0),mul_zero]
   _ = 2*B*((sqrt (n:R))⁻¹)^k:=by
     rw [show (∑ i:Fin n,if i=e.1.1\/i=e.1.2 then B*((sqrt (n:R))⁻¹)^k else 0) =
       ((Finset.univ.filter fun i:Fin n=>i=e.1.1\/i=e.1.2).card:R)*(B*((sqrt (n:R))⁻¹)^k) by
      rw [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul]]
     have hfilt:Finset.univ.filter (fun i:Fin n=>i=e.1.1\/i=e.1.2)={e.1.1,e.1.2}:=by
      ext i;simp
     rw [hfilt,Finset.card_pair e.2.ne];push_cast;ring
 have hd1:∀ s ∈ bS m,∀ x,HD (u s) (u1 s x) x:=fun s _ x =>
  (HasDerivAt.fun_sum (u:=Finset.univ) fun i _ =>
   (psi_hasDerivAt _).comp x (fieldVal_update_deriv A e s i x)).const_mul (-lam)
 have hd2:∀ s ∈ bS m,∀ x,HD (u1 s) (u2 s x) x:=fun s _ x =>
  ((HasDerivAt.fun_sum (u:=Finset.univ) fun i _ =>
   ((psi1_hasDerivAt _).comp x (fieldVal_update_deriv A e s i x)).mul_const (c s i)).const_mul (-lam)).congr_deriv
   (by dsimp only [u2];congr 1;refine Finset.sum_congr rfl fun i _=>?_;ring)
 have hd3:∀ s ∈ bS m,∀ x,HD (u2 s) (u3 s x) x:=fun s _ x =>
  ((HasDerivAt.fun_sum (u:=Finset.univ) fun i _ =>
   ((psi2_hasDerivAt _).comp x (fieldVal_update_deriv A e s i x)).mul_const ((c s i)^2)).const_mul (-lam)).congr_deriv
   (by dsimp only [u3];congr 1;refine Finset.sum_congr rfl fun i _=>?_;ring)
 set M1:R:=240*lam*(sqrt (n:R))⁻¹
 set M2:R:=96000*lam*((sqrt (n:R))⁻¹)^2
 set M3:R:=26880000*lam*((sqrt (n:R))⁻¹)^3
 have hb1:∀ s ∈ bS m,∀ x,|u1 s x| <= M1:=fun s _ x=>by
  unfold u1
  rw [abs_mul,abs_neg,abs_of_pos hlam]
  have h:=hsum_c' s 1 le_rfl (fun i=>psi1 (fv0 n (Function.update A e x) s i)) 120 (by norm_num) (fun _=>psi1_abs_le _)
  simp only [pow_one] at h
  calc lam * |∑ i:Fin n,psi1 (fv0 n (Function.update A e x) s i)*c s i|
    <= lam*(2*120*(sqrt (n:R))⁻¹):=mlL h hlam.le
   _ = M1:=by unfold M1;ring
 have hb2:∀ s ∈ bS m,∀ x,|u2 s x| <= M2:=fun s _ x=>by
  unfold u2
  rw [abs_mul,abs_neg,abs_of_pos hlam]
  have h:=hsum_c' s 2 (by omega) (fun i=>psi2 (fv0 n (Function.update A e x) s i)) 48000 (by norm_num) (fun _=>psi2_abs_le _)
  calc lam * |∑ i:Fin n,psi2 (fv0 n (Function.update A e x) s i)*(c s i)^2|
    <= lam*(2*48000*((sqrt (n:R))⁻¹)^2):=mlL h hlam.le
   _ = M2:=by unfold M2;ring
 have hb3:∀ s ∈ bS m,∀ x,|u3 s x| <= M3:=fun s _ x=>by
  unfold u3
  rw [abs_mul,abs_neg,abs_of_pos hlam]
  have h:=hsum_c' s 3 (by omega) (fun i=>psi3 (fv0 n (Function.update A e x) s i)) 13440000 (by norm_num) (fun _=>psi3_abs_le _)
  calc lam * |∑ i:Fin n,psi3 (fv0 n (Function.update A e x) s i)*(c s i)^3|
    <= lam*(2*13440000*((sqrt (n:R))⁻¹)^3):=mlL h hlam.le
   _ = M3:=by unfold M3;ring
 let Z:R->R:=fun x=>∑ s ∈ bS m,exp (u s x)
 let Z1:R->R:=fun x=>∑ s ∈ bS m,exp (u s x)*u1 s x
 let Z2:R->R:=fun x=>∑ s ∈ bS m,exp (u s x)*(u2 s x+(u1 s x)^2)
 let Z3:R->R:=fun x=>∑ s ∈ bS m,exp (u s x)*(u3 s x+3*u1 s x*u2 s x+(u1 s x)^3)
 let G1:R->R:=fun x=>Z1 x/Z x
 let G2:R->R:=fun x=>Z2 x/Z x - (Z1 x/Z x)^2
 let G3:R->R:=fun x=>Z3 x/Z x - 3*(Z2 x/Z x)*(Z1 x/Z x)+2*(Z1 x/Z x)^3
 have hlog:=log_sum_exp_derivs (bS m) (bisections_nonempty m) (((bS m).card:R)⁻¹)
  (inv_pos.mpr hcard) u u1 u2 u3 (by positivity) (by positivity) (by positivity) hd1 hd2 hd3 hb1 hb2 hb3
 obtain ⟨hGd1,hGd2,hGd3,hGb1,hGb3⟩:=hlog
 let scale:R:=-(1/(lam*(2*m:R)))
 refine ⟨fun x=>scale*G1 x,fun x=>scale*G2 x,fun x=>scale*G3 x,?_,?_,?_,?_,?_⟩
 .
  intro x
  unfold sM
  exact (hGd1 x).const_mul scale
 . intro x;exact (hGd2 x).const_mul scale
 . intro x;exact (hGd3 x).const_mul scale
 .
  intro x
  have hn_eq:(n:R)=(2*m:R):=by unfold n;push_cast;ring
  rw [abs_mul,show |scale| = (lam*(n:R))⁻¹ by
   unfold scale;rw [← hn_eq,abs_neg,one_div,abs_of_pos (inv_pos.mpr (mul_pos hlam hn))]]
  calc (lam*(n:R))⁻¹ * |G1 x| <= (lam*(n:R))⁻¹*M1:=mlL (hGb1 x) (by positivity)
   _ = 240/((2*m:R)*sqrt (2*m:R)):=by unfold M1;rw [← hn_eq];field_simp [hlam.ne',hn.ne',hsn.ne']
 .
  intro x
  have hn_eq:(n:R)=(2*m:R):=by unfold n;push_cast;ring
  rw [abs_mul,show |scale| = (lam*(n:R))⁻¹ by
   unfold scale;rw [← hn_eq,abs_neg,one_div,abs_of_pos (inv_pos.mpr (mul_pos hlam hn))]]
  calc (lam*(n:R))⁻¹ * |G3 x| <= (lam*(n:R))⁻¹*(M3+6*M1*M2+6*M1^3) :=
     mlL (hGb3 x) (by positivity)
   _ = (26880000+138240000*lam+82944000*lam^2)/((2*m:R)^2*sqrt (2*m:R)):=by
     unfold M1 M2 M3;rw [← hn_eq]
     have hsq:sqrt (n:R)^2=(n:R):=sq_sqrt hn.le
     have hcub:((sqrt (n:R))⁻¹)^3=((n:R)*sqrt (n:R))⁻¹:=by
      rw [inv_pow,pow_succ,hsq,mul_inv]
     have halg:(lam*(n:R))⁻¹*(26880000*lam*((sqrt (n:R))⁻¹)^3 +
       6*(240*lam*(sqrt (n:R))⁻¹)*(96000*lam*((sqrt (n:R))⁻¹)^2) +
       6*(240*lam*(sqrt (n:R))⁻¹)^3) =
       (26880000+138240000*lam+82944000*lam^2)*((n:R)⁻¹*((sqrt (n:R))⁻¹)^3):=by
      field_simp [hlam.ne',hn.ne',hsn.ne'];ring
     rw [halg,hcub];field_simp [hn.ne',hsn.ne']
noncomputable def sG (m:ℕ) (lam:R) (A:Ei (2*m)->R) (e:Ei (2*m)):R :=
 let n:ℕ:=2*m
 let Z:R:=∑ s ∈ bS m,exp (-lam*∑ i:Fin n,psi (fv0 n A s i))
 ((n:R)*sqrt (n:R))⁻¹*Z⁻¹ *
  ∑ s ∈ bS m,exp (-lam*∑ i:Fin n,psi (fv0 n A s i)) *
   (spin s e.1.1*spin s e.1.2)*(psi1 (fv0 n A s e.1.1)+psi1 (fv0 n A s e.1.2))
lemma sGa {m:ℕ} (hm:1<=m) (lam:R) (A:Ei (2*m)->R) (e:Ei (2*m)) :
  |sG m lam A e| <= 240/((2*m:R)*sqrt (2*m:R)):=by
 unfold sG;dsimp only
 have hn:(0:R) < ((2*m:ℕ):R):=by positivity
 have hsn:0 < sqrt ((2*m:ℕ):R):=sqrt_pos.mpr hn
 set Z:R:=∑ s ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i))
 have hZ:0 < Z:=Finset.sum_pos (fun s _=>exp_pos _) (bisections_nonempty m)
 rw [abs_mul,abs_mul,abs_of_pos (inv_pos.mpr (mul_pos hn hsn)),abs_of_pos (inv_pos.mpr hZ)]
 have hsum:|∑ s ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i)) *
   (spin s e.1.1*spin s e.1.2)*(psi1 (fv0 (2*m) A s e.1.1)+psi1 (fv0 (2*m) A s e.1.2))| <= 240*Z:=by
  calc _ <= ∑ s ∈ bS m,|exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i)) *
      (spin s e.1.1*spin s e.1.2)*(psi1 (fv0 (2*m) A s e.1.1)+psi1 (fv0 (2*m) A s e.1.2))| :=
      Finset.abs_sum_le_sum_abs _ _
   _ <= ∑ s ∈ bS m,exp (-lam*∑ i:Fin (2*m),psi (fv0 (2*m) A s i))*240:=by
     refine Finset.sum_le_sum fun s _=>?_
     rw [abs_mul,abs_mul,abs_of_pos (exp_pos _)]
     have hsp:|spin s e.1.1*spin s e.1.2| = 1:=by
      have h1:=spin_mul_sq s e.1.1 e.1.2
      nlinarith [sq_abs (spin s e.1.1*spin s e.1.2),abs_nonneg (spin s e.1.1*spin s e.1.2)]
     rw [hsp,mul_one]
     refine mlL ?_ (exp_pos _).le
     exact (abs_add_le _ _).trans (by linarith [psi1_abs_le (fv0 (2*m) A s e.1.1),psi1_abs_le (fv0 (2*m) A s e.1.2)])
   _ = 240*Z:=by rw [← Finset.sum_mul,mul_comm]
 calc (((2*m:ℕ):R)*sqrt ((2*m:ℕ):R))⁻¹*Z⁻¹*_
   <= (((2*m:ℕ):R)*sqrt ((2*m:ℕ):R))⁻¹*Z⁻¹*(240*Z):=mlL hsum (by positivity)
  _ = 240/((2*m:R)*sqrt (2*m:R)):=by push_cast;field_simp [hZ.ne',hn.ne',hsn.ne']
lemma sGc (m:ℕ) (lam:R) (e:Ei (2*m)) :
  Continuous (fun A=>sG m lam A e):=by
 have hfield:∀ s i,Continuous (fun A:Ei (2*m)->R=>fv0 (2*m) A s i):=fun s i=>by
  unfold fv0 ev0
  refine continuous_const.mul (continuous_finset_sum _ fun j _=>?_)
  split_ifs <;> fun_prop
 unfold sG;dsimp only
 refine (continuous_const.mul (Continuous.inv₀ ?_ ?_)).mul ?_
 .
  exact continuous_finset_sum _ fun s _=>continuous_exp.comp (continuous_const.mul
   (continuous_finset_sum _ fun i _=>psi_continuous.comp (hfield s i)))
 . intro A;exact (Finset.sum_pos (fun s _=>exp_pos _) (bisections_nonempty m)).ne'
 .
  exact continuous_finset_sum _ fun s _ =>
   ((continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun i _=>psi_continuous.comp (hfield s i)))).mul
    continuous_const).mul ((psi1_continuous.comp (hfield s e.1.1)).add (psi1_continuous.comp (hfield s e.1.2)))
lemma fieldVal_rot_eq {n:ℕ} (x y:Ei n->R) (θ:R) (s:Finset (Fin n)) (i:Fin n) :
  fv0 n (sin θ • y+cos θ • x) s i=sin θ*fv0 n y s i+cos θ*fv0 n x s i:=by
 unfold fv0
 rw [mul_left_comm (sin θ),mul_left_comm (cos θ),← mul_add]
 congr 1
 rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
 refine Finset.sum_congr rfl fun j _=>?_
 unfold ev0;split_ifs <;> simp <;> ring
lemma fieldVal_rot_deriv {n:ℕ} (x y:Ei n->R) (s:Finset (Fin n)) (i:Fin n) (θ:R) :
  HD (fun t=>fv0 n (sin t • y+cos t • x) s i)
   (fv0 n (cos θ • y - sin θ • x) s i) θ:=by
 have heq:(fun t=>fv0 n (sin t • y+cos t • x) s i) =
   fun t=>sin t*fv0 n y s i+cos t*fv0 n x s i :=
  funext fun t=>fieldVal_rot_eq x y t s i
 rw [heq]
 have hd:=((hasDerivAt_sin θ).mul_const (fv0 n y s i)).fun_add ((hasDerivAt_cos θ).mul_const (fv0 n x s i))
 refine hd.congr_deriv ?_
 have hlin:fv0 n (cos θ • y - sin θ • x) s i=cos θ*fv0 n y s i - sin θ*fv0 n x s i:=by
  unfold fv0
  rw [mul_left_comm (cos θ),mul_left_comm (sin θ),← mul_sub]
  congr 1
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _=>?_
  unfold ev0;split_ifs <;> simp <;> ring
 rw [hlin];ring
lemma sum_psi1_fieldVal_eq {n:ℕ} (A B:Ei n->R) (s:Finset (Fin n)) :
  ∑ i:Fin n,psi1 (fv0 n A s i)*fv0 n B s i =
  (sqrt (n:R))⁻¹*∑ e:Ei n,B e*(spin s e.1.1*spin s e.1.2) *
   (psi1 (fv0 n A s e.1.1)+psi1 (fv0 n A s e.1.2)):=by
 have h1:∑ i:Fin n,psi1 (fv0 n A s i)*fv0 n B s i =
   (sqrt (n:R))⁻¹*∑ p:Fin n × Fin n,psi1 (fv0 n A s p.1)*ev0 B p.1 p.2*(spin s p.1*spin s p.2):=by
  rw [Fintype.sum_prod_type,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _=>?_
  conv_lhs=>arg 2;unfold fv0
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _=>by ring
 rw [h1];congr 1
 have hsplit:∑ p:Fin n × Fin n,psi1 (fv0 n A s p.1)*ev0 B p.1 p.2*(spin s p.1*spin s p.2) =
   (∑ p ∈ Finset.univ.filter (fun p:Fin n × Fin n=>p.1 < p.2),
    psi1 (fv0 n A s p.1)*ev0 B p.1 p.2*(spin s p.1*spin s p.2)) +
   (∑ p ∈ Finset.univ.filter (fun p:Fin n × Fin n=>p.2 < p.1),
    psi1 (fv0 n A s p.1)*ev0 B p.1 p.2*(spin s p.1*spin s p.2)):=by
  rw [← Finset.sum_union (Finset.disjoint_filter.mpr fun p _ h1 h2=>lt_asymm h1 h2)]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun p _ hp=>?_
  simp only [Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,not_or,not_lt] at hp
  have heq:p.1=p.2:=le_antisymm hp.2 hp.1
  rw [heq,show ev0 B p.2 p.2=0 by unfold ev0;simp];ring
 rw [hsplit]
 have hpart1:∑ p ∈ Finset.univ.filter (fun p:Fin n × Fin n=>p.1 < p.2),
   psi1 (fv0 n A s p.1)*ev0 B p.1 p.2*(spin s p.1*spin s p.2) =
   ∑ e:Ei n,B e*(spin s e.1.1*spin s e.1.2)*psi1 (fv0 n A s e.1.1):=by
  refine (Finset.sum_nbij (fun e:Ei n=>e.1) (fun e _=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.2⟩)
   (fun _ _ _ _ h=>Subtype.ext h) (fun p hp=>⟨⟨p,(Finset.mem_filter.mp hp).2⟩,Finset.mem_univ _,rfl⟩)
   fun e _=>?_).symm
  have:ev0 B e.1.1 e.1.2=B e:=by unfold ev0;rw [dif_pos e.2]
  rw [this];ring
 have hpart2:∑ p ∈ Finset.univ.filter (fun p:Fin n × Fin n=>p.2 < p.1),
   psi1 (fv0 n A s p.1)*ev0 B p.1 p.2*(spin s p.1*spin s p.2) =
   ∑ e:Ei n,B e*(spin s e.1.1*spin s e.1.2)*psi1 (fv0 n A s e.1.2):=by
  refine (Finset.sum_nbij (fun e:Ei n=>(e.1.2,e.1.1))
   (fun e _=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.2⟩)
   (fun e1 _ e2 _ h=>Subtype.ext (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)))
   (fun p hp=>⟨⟨(p.2,p.1),(Finset.mem_filter.mp hp).2⟩,Finset.mem_univ _,by cases p;rfl⟩)
   fun e _=>?_).symm
  have:ev0 B e.1.2 e.1.1=B e:=by unfold ev0;rw [dif_neg (not_lt.mpr e.2.le),dif_pos e.2]
  rw [this];ring
 rw [hpart1,hpart2,← Finset.sum_add_distrib]
 refine Finset.sum_congr rfl fun e _=>by ring
lemma softMin_rot_hasDerivAt {m:ℕ} (hm:1<=m) {lam:R} (hlam:0 < lam)
  (x y:Ei (2*m)->R) (θ:R) :
  HD (fun t=>sM m lam (sin t • y+cos t • x))
   (∑ e:Ei (2*m),sG m lam (sin θ • y+cos θ • x) e*(cos θ*y e - sin θ*x e)) θ:=by
 let n:ℕ:=2*m
 have hn:(0:R) < (n:R):=by positivity
 have hcard:(0:R) < ((bS m).card:R):=by exact_mod_cast (bisections_nonempty m).card_pos
 let A:=sin θ • y+cos θ • x
 let B:=cos θ • y - sin θ • x
 let Z:R:=∑ s ∈ bS m,exp (-lam*∑ i:Fin n,psi (fv0 n A s i))
 have hZ:0 < Z:=Finset.sum_pos (fun s _=>exp_pos _) (bisections_nonempty m)
 have hZ_d:HD (fun t=>∑ s ∈ bS m,exp (-lam*∑ i:Fin n,psi (fv0 n (sin t • y+cos t • x) s i)))
   (∑ s ∈ bS m,exp (-lam*∑ i:Fin n,psi (fv0 n A s i)) *
    (-lam*∑ i:Fin n,psi1 (fv0 n A s i)*fv0 n B s i)) θ:=by
  refine HasDerivAt.fun_sum (u:=bS m) fun s _=>?_
  exact ((HasDerivAt.fun_sum (u:=Finset.univ) fun i _ =>
   (psi_hasDerivAt _).comp θ (fieldVal_rot_deriv x y s i θ)).const_mul (-lam)).exp
 have htot:=((hZ_d.const_mul (((bS m).card:R)⁻¹)).log (mul_pos (inv_pos.mpr hcard) hZ).ne').const_mul
  (-(1/(lam*(2*m:R))))
 unfold sM
 refine htot.congr_deriv ?_
 have hn_eq:(2*m:R)=(n:R):=by unfold n;push_cast;ring
 rw [hn_eq]
 have hrew:∑ s ∈ bS m,exp (-lam*∑ i:Fin n,psi (fv0 n A s i)) *
   (-lam*∑ i:Fin n,psi1 (fv0 n A s i)*fv0 n B s i) =
   -lam*(sqrt (n:R))⁻¹*∑ e:Ei n,B e *
    ∑ s ∈ bS m,exp (-lam*∑ i:Fin n,psi (fv0 n A s i)) *
     (spin s e.1.1*spin s e.1.2)*(psi1 (fv0 n A s e.1.1)+psi1 (fv0 n A s e.1.2)):=by
  trans (∑ s ∈ bS m,∑ e:Ei n,
   (-lam*(sqrt (n:R))⁻¹)*(B e*(exp (-lam*∑ i:Fin n,psi (fv0 n A s i)) *
    (spin s e.1.1*spin s e.1.2)*(psi1 (fv0 n A s e.1.1)+psi1 (fv0 n A s e.1.2)))))
  .
   refine Finset.sum_congr rfl fun s _=>?_
   rw [sum_psi1_fieldVal_eq A B s]
   simp_rw [Finset.mul_sum]
   refine Finset.sum_congr rfl fun e _=>by ring
  .
   rw [Finset.sum_comm,Finset.mul_sum]
   refine Finset.sum_congr rfl fun e _=>?_
   simp_rw [Finset.mul_sum]
 rw [hrew]
 unfold sG;dsimp only
 have h1:-(1/(lam*(n:R))) *
   ((((bS m).card:R)⁻¹*(-lam*(sqrt (n:R))⁻¹ *
    ∑ e:Ei n,B e*∑ s ∈ bS m,exp (-lam*∑ i:Fin n,psi (fv0 n A s i)) *
     (spin s e.1.1*spin s e.1.2)*(psi1 (fv0 n A s e.1.1)+psi1 (fv0 n A s e.1.2)))) /
   (((bS m).card:R)⁻¹*Z)) =
   ((n:R)*sqrt (n:R))⁻¹*Z⁻¹ *
    ∑ e:Ei n,B e*∑ s ∈ bS m,exp (-lam*∑ i:Fin n,psi (fv0 n A s i)) *
     (spin s e.1.1*spin s e.1.2)*(psi1 (fv0 n A s e.1.1)+psi1 (fv0 n A s e.1.2)):=by
  field_simp [hlam.ne',hn.ne',hcard.ne',hZ.ne',(sqrt_pos.mpr hn).ne']
 rw [h1,Finset.mul_sum]
 refine Finset.sum_congr rfl fun e _=>?_
 have hBe:B e=cos θ*y e - sin θ*x e:=by simp [B]
 rw [hBe];ring
lemma card_EdgeIdx (n:ℕ):Fintype.card (Ei n)=n.choose 2:=by
 have h1:Fintype.card (Ei n)=(Finset.univ.powersetCard 2:Finset (Finset (Fin n))).card:=by
  rw [← Fintype.card_coe]
  refine Fintype.card_of_bijective (f:=fun e:Ei n=>(⟨{e.1.1,e.1.2},
   Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,Finset.card_pair e.2.ne⟩⟩ :
    {s:Finset (Fin n) // s ∈ (Finset.univ:Finset (Fin n)).powersetCard 2})) ⟨?_,?_⟩
  .
   intro e1 e2 heq
   have hset:({e1.1.1,e1.1.2}:Finset (Fin n))={e2.1.1,e2.1.2}:=congrArg Subtype.val heq
   have hm1:e1.1.1 ∈ ({e2.1.1,e2.1.2}:Finset (Fin n)):=hset ▸ Finset.mem_insert_self _ _
   have hm2:e1.1.2 ∈ ({e2.1.1,e2.1.2}:Finset (Fin n)):=hset ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
   simp only [Finset.mem_insert,Finset.mem_singleton] at hm1 hm2
   rcases hm1 with h1 | h1 <;> rcases hm2 with h2 | h2
   . exact absurd (h1.trans h2.symm) e1.2.ne
   . exact Subtype.ext (Prod.ext h1 h2)
   . exact absurd (h1 ▸ h2 ▸ e1.2) (lt_asymm e2.2)
   . exact absurd (h1.trans h2.symm) e1.2.ne
  .
   rintro ⟨s,hs⟩
   obtain ⟨_,hcard⟩:=Finset.mem_powersetCard.mp hs
   obtain ⟨a,b,hab,rfl⟩:=Finset.card_eq_two.mp hcard
   rcases lt_or_gt_of_ne hab with hlt | hgt
   . exact ⟨⟨(a,b),hlt⟩,Subtype.ext rfl⟩
   . exact ⟨⟨(b,a),hgt⟩,Subtype.ext (Finset.pair_comm b a)⟩
 rw [h1,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]
lemma card_EdgeIdx_le (n:ℕ):(Fintype.card (Ei n):R)<=(n:R)^2/2:=by
 rw [card_EdgeIdx,Nat.choose_two_right]
 have h:(n*(n - 1)/2:ℕ)*2<=n*n:=by
  calc (n*(n - 1)/2)*2<=n*(n - 1):=Nat.div_mul_le_self _ 2
   _ <= n*n:=Nat.mul_le_mul_left n (Nat.sub_le n 1)
 have hR:((n*(n - 1)/2:ℕ):R)*2<=(n:R)*(n:R):=by exact_mod_cast h
 nlinarith
lemma lintegral_pi_prod_fin':∀ (k:ℕ) (f:Fin k->R->ENNReal),
  (∀ i,Measurable (f i)) ->
  ∫⁻ x:Fin k->R,∏ i:Fin k,f i (x i) ∂Measure.pi (fun _:Fin k=>N01) =
  ∏ i:Fin k,∫⁻ z:R,f i z ∂N01:=by
 intro k
 induction k with
 | zero=>intro f _;simp
 | succ k ih =>
  intro f hf
  have hmp:=measurePreserving_piFinSuccAbove (fun _:Fin (k+1)=>N01) (0:Fin (k+1))
  let e0:=MeasurableEquiv.piFinSuccAbove (fun _:Fin (k+1)=>R) (0:Fin (k+1))
  have hrew:∀ x:Fin (k+1)->R,∏ i:Fin (k+1),f i (x i) =
    f 0 (e0 x).1*∏ j:Fin k,f j.succ ((e0 x).2 j):=fun x=>by
   rw [Fin.prod_univ_succ];rfl
  simp_rw [hrew]
  rw [hmp.lintegral_comp (by fun_prop:Measurable fun p:R × (Fin k->R)=>f 0 p.1*∏ j:Fin k,f j.succ (p.2 j)),
    lintegral_prod_mul (hf 0).aemeasurable (by fun_prop:Measurable fun y:Fin k->R=>∏ j:Fin k,f j.succ (y j)).aemeasurable,
    ih (fun j=>f j.succ) (fun j=>hf j.succ),Fin.prod_univ_succ]
lemma lintegral_exp_linear_gauss {ι:Type*} [Fintype ι] [DecidableEq ι] (v:ι->R) :
  ∫⁻ y:ι->R,ENNReal.ofReal (exp (∑ e:ι,v e*y e)) ∂(Measure.pi (fun _:ι=>N01)) =
  ENNReal.ofReal (exp ((∑ e:ι,(v e)^2)/2)):=by
 have heq:∀ y:ι->R,ENNReal.ofReal (exp (∑ e:ι,v e*y e)) =
   ∏ e:ι,ENNReal.ofReal (exp (v e*y e)):=fun y=>by
  rw [exp_sum,ENNReal.ofReal_prod_of_nonneg (fun e _=>(exp_pos _).le)]
 simp_rw [heq]
 let eFin:Fin (Fintype.card ι) ≃ ι:=(Fintype.equivFin ι).symm
 have hmp:MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _:ι=>R) eFin)
   (Measure.pi (fun _:Fin (Fintype.card ι)=>N01))
   (Measure.pi (fun _:ι=>N01)) :=
  measurePreserving_piCongrLeft (fun _:ι=>N01) eFin
 rw [← hmp.lintegral_comp (by fun_prop:Measurable fun y:ι->R=>∏ e:ι,ENNReal.ofReal (exp (v e*y e)))]
 have hcomp:∀ z:Fin (Fintype.card ι)->R,
   ∏ e:ι,ENNReal.ofReal (exp (v e*MeasurableEquiv.piCongrLeft (fun _:ι=>R) eFin z e)) =
   ∏ k:Fin (Fintype.card ι),ENNReal.ofReal (exp (v (eFin k)*z k)):=fun z=>by
  refine (Fintype.prod_equiv eFin _ _ fun k=>?_).symm
  congr 3
  simp [MeasurableEquiv.piCongrLeft_apply_apply]
 simp_rw [hcomp]
 rw [lintegral_pi_prod_fin' (Fintype.card ι) (fun k x=>ENNReal.ofReal (exp (v (eFin k)*x)))
  (fun k=>by fun_prop)]
 have h1d:∀ a:R,∫⁻ x:R,ENNReal.ofReal (exp (a*x)) ∂(N01) =
   ENNReal.ofReal (exp (a^2/2)):=fun a=>by
  have hmgf:=congrFun (mgf_id_gaussianReal (μ:=0) (v:=1)) a
  simp only [mgf,id_eq,zero_mul,NNReal.coe_one,one_mul,zero_add] at hmgf
  have hint:Integrable (fun x:R=>exp (a*x)) (N01):=by
   have hmem:=integrable_exp_mul_gaussianReal (μ:=0) (v:=1) a
   simpa using hmem
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _=>(exp_pos _).le),hmgf]
 simp_rw [h1d]
 rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _=>(exp_pos _).le),← exp_sum,
   Fintype.sum_equiv eFin (fun k=>(v (eFin k))^2/2) (fun e=>(v e)^2/2) (fun _=>rfl),
   ← Finset.sum_div]
lemma pisier_softMin_mgf {m:ℕ} (hm:1<=m) {lam:R} (hlam:0 < lam) {t:R} (ht:0<=t) :
  ∫⁻ x,ENNReal.ofReal (exp (t*((∫ y,sM m lam y ∂gE (2*m)) - sM m lam x))) ∂gE (2*m) <=
  ENNReal.ofReal (exp (t^2*π^2*28800/(2*m:R))):=by
 set n:ℕ:=2*m
 set F:(Ei n->R)->R:=sM m lam
 set μ:Measure (Ei n->R):=gE n
 have hn:(0:R) < (n:R):=by positivity
 have hF_cont:Continuous F:=sMc m lam
 have hF_bd:∀ x,0<=F x/\F x<=1:=fun x=>sMb hm hlam x
 have hF_int:Integrable F μ :=
  Integrable.of_bound hF_cont.aestronglyMeasurable 1 (Eventually.of_forall fun x=>by
   rw [Real.norm_eq_abs,aon (hF_bd x).1];exact (hF_bd x).2)
 have hstep1:∫⁻ x,ENNReal.ofReal (exp (t*((∫ y,F y ∂μ) - F x))) ∂μ <=
   ∫⁻ x,∫⁻ y,ENNReal.ofReal (exp (t*(F y - F x))) ∂μ ∂μ:=by
  refine lintegral_mono fun x=>?_
  have hj:exp (t*((∫ y,F y ∂μ) - F x))<=∫ y,exp (t*(F y - F x)) ∂μ:=by
   have hlin:∫ y,t*(F y - F x) ∂μ=t*((∫ y,F y ∂μ) - F x):=by
    rw [integral_const_mul,integral_sub hF_int (integrable_const (F x)),integral_const,
      probReal_univ,one_smul]
   rw [← hlin]
   refine convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun _=>Set.mem_univ _)
    ((hF_int.sub (integrable_const (F x))).const_mul t) ?_
   refine Integrable.of_bound ((continuous_exp.comp (continuous_const.mul (hF_cont.sub continuous_const))).aestronglyMeasurable)
    (exp t) (Eventually.of_forall fun y=>?_)
   simp only [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (exp_pos _)]
   exact exp_le_exp.mpr (by nlinarith [(hF_bd x).1,(hF_bd y).2])
  have hint_y:Integrable (fun y=>exp (t*(F y - F x))) μ:=by
   refine Integrable.of_bound ((continuous_exp.comp (continuous_const.mul (hF_cont.sub continuous_const))).aestronglyMeasurable)
    (exp t) (Eventually.of_forall fun y=>?_)
   rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
   exact exp_le_exp.mpr (by nlinarith [(hF_bd x).1,(hF_bd y).2])
  rw [← ofReal_integral_eq_lintegral_ofReal hint_y (Eventually.of_forall fun _=>(exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal hj
 let ν:Measure R:=ENNReal.ofReal (2 / π) • volume.restrict (Set.Icc 0 (π / 2))
 have hν_prob:IsProbabilityMeasure ν:=by
  constructor
  simp only [ν,Measure.smul_apply,Measure.restrict_apply_univ,Real.volume_Icc,sub_zero,smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity:(0:R)<=2 / π)]
  have hmul:(2 / π)*(π / 2)=1:=by field_simp [pi_pos.ne']
  rw [hmul,ENNReal.ofReal_one]
 let G:(Ei n->R)->(Ei n->R)->R->R:=fun x y θ =>
  ∑ e:Ei n,sG m lam (sin θ • y+cos θ • x) e*(cos θ*y e - sin θ*x e)
 have hG_cont_all:Continuous (fun p:((Ei n->R) × (Ei n->R)) × R=>G p.1.1 p.1.2 p.2):=by
  unfold G
  refine continuous_finset_sum _ fun e _=>Continuous.mul ?_ ?_
  .
   refine (sGc m lam e).comp ?_
   exact ((continuous_sin.comp continuous_snd).smul (continuous_snd.comp continuous_fst)).add
    ((continuous_cos.comp continuous_snd).smul (continuous_fst.comp continuous_fst))
  .
   exact ((continuous_cos.comp continuous_snd).mul ((continuous_apply e).comp (continuous_snd.comp continuous_fst))).sub
    ((continuous_sin.comp continuous_snd).mul ((continuous_apply e).comp (continuous_fst.comp continuous_fst)))
 have hstep2:∀ x y:Ei n->R,
   ENNReal.ofReal (exp (t*(F y - F x))) <=
   ∫⁻ θ,ENNReal.ofReal (exp ((π / 2)*t*G x y θ)) ∂ν:=fun x y=>by
  have hG_cont:Continuous (fun θ=>G x y θ):=by
   unfold G
   refine continuous_finset_sum _ fun e _=>Continuous.mul ?_ ?_
   . exact (sGc m lam e).comp ((continuous_sin.smul continuous_const).add (continuous_cos.smul continuous_const))
   . exact (continuous_cos.mul continuous_const).sub (continuous_sin.mul continuous_const)
  have hftc:F y - F x=∫ θ in (0:R)..(π / 2),G x y θ:=by
   have hd:=fun θ (_:θ ∈ Set.uIcc (0:R) (π / 2))=>softMin_rot_hasDerivAt hm hlam x y θ
   have h:=intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hG_cont.intervalIntegrable 0 (π / 2))
   have h0:sin (0:R) • y+cos (0:R) • x=x:=by simp
   have hpi:sin (π / 2) • y+cos (π / 2) • x=y:=by simp
   simpa [F,h0,hpi] using h.symm
  have havg:t*(F y - F x)=∫ θ,((π / 2)*t*G x y θ) ∂ν:=by
   rw [hftc,integral_smul_measure,ENNReal.toReal_ofReal (by positivity:(0:R)<=2 / π),
     smul_eq_mul,integral_const_mul,integral_Icc_eq_integral_Ioc,
     ← intervalIntegral.integral_of_le (by positivity:(0:R)<=π / 2)]
   have:(2 / π)*((π / 2)*t)=t:=by field_simp [pi_pos.ne']
   rw [← mul_assoc,this]
  have hG_int_ν:Integrable (fun θ=>(π / 2)*t*G x y θ) ν:=by
   have h1:ContinuousOn (fun θ=>(π / 2)*t*G x y θ) (Set.Icc 0 (π / 2)) :=
    (continuous_const.mul hG_cont).continuousOn
   exact (h1.integrableOn_Icc).smul_measure ENNReal.ofReal_ne_top
  have hexp_int_ν:Integrable (fun θ=>exp ((π / 2)*t*G x y θ)) ν:=by
   have h1:ContinuousOn (fun θ=>exp ((π / 2)*t*G x y θ)) (Set.Icc 0 (π / 2)) :=
    (continuous_exp.comp (continuous_const.mul hG_cont)).continuousOn
   exact (h1.integrableOn_Icc).smul_measure ENNReal.ofReal_ne_top
  have hj:=convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
   (Eventually.of_forall fun _=>Set.mem_univ _) hG_int_ν hexp_int_ν
  rw [← havg] at hj
  rw [← ofReal_integral_eq_lintegral_ofReal hexp_int_ν (Eventually.of_forall fun _=>(exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal hj
 have hprod_eq:∫⁻ x,∫⁻ y,ENNReal.ofReal (exp (t*(F y - F x))) ∂μ ∂μ <=
   ∫⁻ θ,∫⁻ p:(Ei n->R) × (Ei n->R),
    ENNReal.ofReal (exp ((π / 2)*t*G p.1 p.2 θ)) ∂(μ.prod μ) ∂ν:=by
  have h1:∫⁻ x,∫⁻ y,ENNReal.ofReal (exp (t*(F y - F x))) ∂μ ∂μ <=
    ∫⁻ x,∫⁻ y,∫⁻ θ,ENNReal.ofReal (exp ((π / 2)*t*G x y θ)) ∂ν ∂μ ∂μ :=
   lintegral_mono fun x=>lintegral_mono fun y=>hstep2 x y
  refine h1.trans_eq ?_
  have hmeas:Measurable (fun p:((Ei n->R) × (Ei n->R)) × R =>
    ENNReal.ofReal (exp ((π / 2)*t*G p.1.1 p.1.2 p.2))) :=
   (ENNReal.continuous_ofReal.comp (continuous_exp.comp (continuous_const.mul hG_cont_all))).measurable
  rw [← lintegral_prod (fun p:(Ei n->R) × (Ei n->R) =>
    ∫⁻ θ,ENNReal.ofReal (exp ((π / 2)*t*G p.1 p.2 θ)) ∂ν)
    (hmeas.lintegral_prod_right').aemeasurable]
  exact lintegral_lintegral_swap hmeas.aemeasurable
 have hrot:∀ θ:R,
   ∫⁻ p:(Ei n->R) × (Ei n->R),
    ENNReal.ofReal (exp ((π / 2)*t*G p.1 p.2 θ)) ∂(μ.prod μ) =
   ∫⁻ p:(Ei n->R) × (Ei n->R),
    ENNReal.ofReal (exp ((π / 2)*t*∑ e:Ei n,sG m lam p.1 e*p.2 e)) ∂(μ.prod μ):=by
  intro θ
  let eSum:=MeasurableEquiv.sumPiEquivProdPi (fun _:Ei n ⊕ Ei n=>R)
  have hmpSum:MeasurePreserving eSum (Measure.pi (fun _:Ei n ⊕ Ei n=>N01)) (μ.prod μ) :=
   measurePreserving_sumPiEquivProdPi (fun _:Ei n ⊕ Ei n=>N01)
  let Rlin:(Ei n ⊕ Ei n->R) →ₗ[R] (Ei n ⊕ Ei n->R) :=
   {
    toFun:=fun z s=>match s with
     | .inl e=>sin θ*z (.inr e)+cos θ*z (.inl e)
     | .inr e=>cos θ*z (.inr e) - sin θ*z (.inl e)
    map_add':=fun a b=>by ext s;cases s <;> simp <;> ring
    map_smul':=fun r a=>by ext s;cases s <;> simp <;> ring }
  let Rrot:(Ei n ⊕ Ei n->R) →L[R] (Ei n ⊕ Ei n->R) :=
   LinearMap.toContinuousLinearMap Rlin
  have hlaw:(Measure.pi (fun _:Ei n ⊕ Ei n=>N01)).map Rrot =
    Measure.pi (fun _:Ei n ⊕ Ei n=>N01):=by
   have h:=pi_gaussianReal_map_eq Rrot (ContinuousLinearMap.id R (Ei n ⊕ Ei n->R)) ?_
   . simpa using h
   .
    intro ξ
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    have hLHS1:∀ e:Ei n,
      (∑ j:Ei n ⊕ Ei n,ξ j*Rrot (Pi.single (.inl e) 1) j) =
      ξ (.inl e)*cos θ - ξ (.inr e)*sin θ:=fun e=>by
     rw [Fintype.sum_sum_type,Finset.sum_eq_single e,Finset.sum_eq_single e]
     . simp [Rrot,Rlin];ring
     . intro j _ hj;simp [Rrot,Rlin,Pi.single_apply,hj]
     . intro h;exact absurd (Finset.mem_univ _) h
     . intro j _ hj;simp [Rrot,Rlin,Pi.single_apply,hj]
     . intro h;exact absurd (Finset.mem_univ _) h
    have hLHS2:∀ e:Ei n,
      (∑ j:Ei n ⊕ Ei n,ξ j*Rrot (Pi.single (.inr e) 1) j) =
      ξ (.inl e)*sin θ+ξ (.inr e)*cos θ:=fun e=>by
     rw [Fintype.sum_sum_type,Finset.sum_eq_single e,Finset.sum_eq_single e]
     . simp [Rrot,Rlin]
     . intro j _ hj;simp [Rrot,Rlin,Pi.single_apply,hj]
     . intro h;exact absurd (Finset.mem_univ _) h
     . intro j _ hj;simp [Rrot,Rlin,Pi.single_apply,hj]
     . intro h;exact absurd (Finset.mem_univ _) h
    have hRHS:∀ s:Ei n ⊕ Ei n,
      (∑ j:Ei n ⊕ Ei n,ξ j*ContinuousLinearMap.id R (Ei n ⊕ Ei n->R) (Pi.single s (1:R)) j)=ξ s:=fun s=>by
     rw [Finset.sum_eq_single s]
     . simp
     . intro j _ hj;simp [Pi.single_apply,hj]
     . intro h;exact absurd (Finset.mem_univ _) h
    simp_rw [hLHS1,hLHS2,hRHS]
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _=>?_
    have hsc:=sin_sq_add_cos_sq θ
    nlinarith [sq_nonneg (ξ (.inl e)),sq_nonneg (ξ (.inr e))]
  let Φ:(Ei n->R) × (Ei n->R)->ENNReal:=fun p =>
   ENNReal.ofReal (exp ((π / 2)*t*∑ e:Ei n,sG m lam p.1 e*p.2 e))
  have hΦ_meas:Measurable Φ:=by
   refine ENNReal.continuous_ofReal.measurable.comp (continuous_exp.measurable.comp
    (continuous_const.mul (continuous_finset_sum _ fun e _ =>
     ((sGc m lam e).comp continuous_fst).mul ((continuous_apply e).comp continuous_snd))).measurable)
  have hcomp_R:∀ z:Ei n ⊕ Ei n->R,
    Φ (eSum (Rrot z))=ENNReal.ofReal (exp ((π / 2)*t*G (eSum z).1 (eSum z).2 θ)):=fun z=>by
   dsimp only [Φ,G,eSum,MeasurableEquiv.sumPiEquivProdPi,Equiv.sumArrowEquivProdArrow,Rrot,
    LinearMap.coe_toContinuousLinearMap',Rlin,LinearMap.coe_mk,AddHom.coe_mk]
   congr 3
  calc ∫⁻ p,ENNReal.ofReal (exp ((π / 2)*t*G p.1 p.2 θ)) ∂(μ.prod μ)
    = ∫⁻ z,ENNReal.ofReal (exp ((π / 2)*t*G (eSum z).1 (eSum z).2 θ))
      ∂(Measure.pi (fun _:Ei n ⊕ Ei n=>N01)):=by rw [← hmpSum.lintegral_comp]; exact (ENNReal.continuous_ofReal.comp (continuous_exp.comp (continuous_const.mul (hG_cont_all.comp (continuous_id.prodMk continuous_const))))).measurable
   _ = ∫⁻ z,Φ (eSum (Rrot z)) ∂(Measure.pi (fun _:Ei n ⊕ Ei n=>N01)):=by
     simp_rw [hcomp_R]
   _ = ∫⁻ z,Φ (eSum z) ∂((Measure.pi (fun _:Ei n ⊕ Ei n=>N01)).map Rrot):=by
     symm
     exact lintegral_map (hΦ_meas.comp eSum.measurable) Rrot.continuous.measurable
   _ = ∫⁻ z,Φ (eSum z) ∂(Measure.pi (fun _:Ei n ⊕ Ei n=>N01)):=by rw [hlaw]
   _ = ∫⁻ p,Φ p ∂(μ.prod μ):=hmpSum.lintegral_comp hΦ_meas
 have hinner:∫⁻ p:(Ei n->R) × (Ei n->R),
   ENNReal.ofReal (exp ((π / 2)*t*∑ e:Ei n,sG m lam p.1 e*p.2 e)) ∂(μ.prod μ) <=
   ENNReal.ofReal (exp (t^2*π^2*28800/(n:R))):=by
  have hΦ_meas:Measurable (fun p:(Ei n->R) × (Ei n->R) =>
    ENNReal.ofReal (exp ((π / 2)*t*∑ e:Ei n,sG m lam p.1 e*p.2 e))) :=
   ENNReal.continuous_ofReal.measurable.comp (continuous_exp.measurable.comp
    (continuous_const.mul (continuous_finset_sum _ fun e _ =>
     ((sGc m lam e).comp continuous_fst).mul ((continuous_apply e).comp continuous_snd))).measurable)
  rw [lintegral_prod _ hΦ_meas.aemeasurable]
  refine (lintegral_mono fun u=>?_).trans_eq (by rw [lintegral_const,measure_univ,mul_one])
  have hrew:∀ v:Ei n->R,
    (π / 2)*t*∑ e:Ei n,sG m lam u e*v e =
    ∑ e:Ei n,((π / 2)*t*sG m lam u e)*v e:=fun v=>by
   rw [Finset.mul_sum];refine Finset.sum_congr rfl fun e _=>by ring
  simp_rw [hrew]
  dsimp only [μ];unfold gE
  rw [lintegral_exp_linear_gauss]
  apply ENNReal.ofReal_le_ofReal;apply exp_le_exp.mpr
  have hn_eq:(n:R)=(2*m:R):=by unfold n;push_cast;ring
  have hsum_sq:∑ e:Ei n,((π / 2)*t*sG m lam u e)^2 <=
    t^2*π^2*57600/(n:R):=by
   have hterm:∀ e:Ei n,((π / 2)*t*sG m lam u e)^2 <=
     (π / 2*t)^2*(240/((n:R)*sqrt (n:R)))^2:=fun e=>by
    rw [mul_pow]
    refine mlL ?_ (sq_nonneg _)
    rw [← sq_abs,hn_eq]
    exact pow_le_pow_left₀ (abs_nonneg _) (sGa hm lam u e) 2
   calc ∑ e:Ei n,((π / 2)*t*sG m lam u e)^2
     <= ∑ _e:Ei n,(π / 2*t)^2*(240/((n:R)*sqrt (n:R)))^2 :=
      Finset.sum_le_sum fun e _=>hterm e
    _ = (Fintype.card (Ei n):R)*((π / 2*t)^2*(240/((n:R)*sqrt (n:R)))^2):=by simp
    _ <= ((n:R)^2/2)*((π / 2*t)^2*(240/((n:R)*sqrt (n:R)))^2) :=
      mlR (card_EdgeIdx_le n) (by positivity)
    _ = t^2*π^2*7200/(n:R):=by
      have hsq:sqrt (n:R)^2=(n:R):=sq_sqrt hn.le
      rw [div_pow,mul_pow,mul_pow,hsq];field_simp [hn.ne'];ring
    _ <= t^2*π^2*57600/(n:R):=by
      have hnn:(0:R)<=t^2*π^2/(n:R):=by positivity
      rw [show t^2*π^2*7200/(n:R)=7200*(t^2*π^2/(n:R)) by ring,
        show t^2*π^2*57600/(n:R)=57600*(t^2*π^2/(n:R)) by ring]
      exact mlR (by norm_num) hnn
  have hdiv2:=dld hsum_sq (by norm_num:(0:R)<=2)
  refine hdiv2.trans_eq (by ring)
 have hn_eq:(n:R)=(2*m:R):=by unfold n;push_cast;ring
 rw [← hn_eq]
 calc ∫⁻ x,ENNReal.ofReal (exp (t*((∫ y,F y ∂μ) - F x))) ∂μ
   <= ∫⁻ x,∫⁻ y,ENNReal.ofReal (exp (t*(F y - F x))) ∂μ ∂μ:=hstep1
  _ <= ∫⁻ θ,∫⁻ p,ENNReal.ofReal (exp ((π / 2)*t*G p.1 p.2 θ)) ∂(μ.prod μ) ∂ν:=hprod_eq
  _ = ∫⁻ _θ,∫⁻ p,ENNReal.ofReal (exp ((π / 2)*t*∑ e:Ei n,sG m lam p.1 e*p.2 e))
     ∂(μ.prod μ) ∂ν:=by simp_rw [hrot]
  _ <= ∫⁻ _θ,ENNReal.ofReal (exp (t^2*π^2*28800/(n:R))) ∂ν:=lintegral_mono fun _=>hinner
  _ = ENNReal.ofReal (exp (t^2*π^2*28800/(n:R))):=by rw [lintegral_const,measure_univ,mul_one]
lemma softMin_gauss_expectation_eventually_le {lam ε:R} (hlam:0 < lam) (hε:0 < ε) :
  ∀ᶠ m:ℕ in atTop,
   ∫ W,sM m lam W ∂(gE (2*m))<=log 2/lam+ε:=by
 obtain ⟨c,hc_pos,hlb⟩:=gAL
 have hlog_tend:Tendsto (fun m:ℕ =>
   (log (c⁻¹)+9*log (2*m:R)+2*tStar*sqrt (2*m:R))/(2*m:R)) atTop (𝓝 0):=by
  have h1:Tendsto (fun m:ℕ=>log (c⁻¹)/(2*m:R)) atTop (𝓝 0):=by
   have:=tendsto_const_nhds (x:=log (c⁻¹)/2) |>.div_atTop tendsto_natCast_atTop_atTop
   refine this.congr fun m=>by ring
  have h2:Tendsto (fun m:ℕ=>9*(log (2*m:R)/(2*m:R))) atTop (𝓝 0):=by
   have hl:Tendsto (fun x:R=>log x/x) atTop (𝓝 0):=by
    simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
   have h2m:Tendsto (fun m:ℕ=>(2*m:R)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
   simpa using (hl.comp h2m).const_mul 9
  have h3:Tendsto (fun m:ℕ=>2*tStar/sqrt (2*m:R)) atTop (𝓝 0):=by
   have hsq:Tendsto (fun m:ℕ=>sqrt (2*m:R)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num:(0:R) < 1/2) |>.comp
     (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)) |>.congr (fun m=>(sqrt_eq_rpow _).symm)
   exact tendsto_const_nhds.div_atTop hsq
  have hsum:Tendsto (fun m:ℕ =>
    log (c⁻¹)/(2*m:R)+9*(log (2*m:R)/(2*m:R))+2*tStar/sqrt (2*m:R))
    atTop (𝓝 (0+0+0)):=(h1.add h2).add h3
  simp only [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hn:(0:R) < (2*m:R):=by positivity
  have hsn:0 < sqrt (2*m:R):=sqrt_pos.mpr hn
  have h2:2*tStar/sqrt (2*m:R)=(2*tStar*sqrt (2*m:R))/(2*m:R):=by
   rw [div_eq_div_iff hsn.ne' hn.ne']
   calc 2*tStar*(2*m:R)=2*tStar*(sqrt (2*m:R)*sqrt (2*m:R)):=by rw [mul_self_sqrt hn.le]
    _ = 2*tStar*sqrt (2*m:R)*sqrt (2*m:R):=by ring
  rw [h2];ring
 have hsmall:=hlog_tend.eventually (gt_mem_nhds (show (0:R) < ε^2/(4*π^2*28800) by positivity))
 filter_upwards [hlb,hsmall,eventually_ge_atTop 1] with m hm_lb hm_sm hm1
 let n:ℕ:=2*m
 have hn:(0:R) < (n:R):=by positivity
 set μ:=gE n
 set E:Set (Ei n->R):={W | ∃ s ∈ bS m,W ∈ aF n s}
 set EX:R:=∫ W,sM m lam W ∂μ
 by_cases hEX:EX<=log 2/lam+ε
 . exact hEX
 push Not at hEX
 have hΔ:ε < EX - log 2/lam:=by linarith
 have hΔ_pos:0 < EX - log 2/lam:=lt_trans hε hΔ
 set V:R:=π^2*28800/(n:R)
 have hV_pos:0 < V:=by positivity
 set t:R:=(EX - log 2/lam)/(2*V)
 have ht_pos:0 < t:=div_pos hΔ_pos (by positivity)
 have hmgf:=pisier_softMin_mgf hm1 hlam ht_pos.le
 have hE_meas:MeasurableSet E:=by
  have heq:E=⋃ s ∈ bS m,aF n s:=by ext W;simp [E]
  rw [heq]
  refine Finset.measurableSet_biUnion _ fun s _=>?_
  rw [show aF n s=⋂ i:Fin n,{W | gC<=fv0 n W s i} by ext W;simp [aF]]
  exact MeasurableSet.iInter fun i=>measurableSet_le measurable_const
   (by unfold fv0 ev0;refine (continuous_const.mul (continuous_finset_sum _ fun j _=>?_)).measurable;split_ifs <;> fun_prop)
 have hmarkov:ENNReal.ofReal (exp (t*(EX - log 2/lam)))*μ E <=
   ENNReal.ofReal (exp (t^2*V)):=by
  calc ENNReal.ofReal (exp (t*(EX - log 2/lam)))*μ E
    = ∫⁻ _W in E,ENNReal.ofReal (exp (t*(EX - log 2/lam))) ∂μ:=by rw [setLIntegral_const]
   _ <= ∫⁻ W in E,ENNReal.ofReal (exp (t*(EX - sM m lam W))) ∂μ:=by
     refine setLIntegral_mono' hE_meas fun W hW=>ENNReal.ofReal_le_ofReal (exp_le_exp.mpr ?_)
     obtain ⟨s,hs,hWs⟩:=hW
     have hle:=softMin_le_of_mem_allFriendly hm1 hlam hs hWs
     nlinarith
   _ <= ∫⁻ W,ENNReal.ofReal (exp (t*(EX - sM m lam W))) ∂μ:=setLIntegral_le_lintegral _ _
   _ <= ENNReal.ofReal (exp (t^2*V)):=by
     have hVeq:t^2*π^2*28800/(2*m:R)=t^2*V:=by unfold V n;push_cast;ring
     rw [← hVeq];exact hmgf
 have hm_lb':c*((n:R)^9)⁻¹*exp (-2*tStar*sqrt (n:R))<=(μ E).toReal:=by
  have hn_eq:(n:R)=(2*m:R):=by unfold n;push_cast;ring
  simpa [hn_eq,μ,E,n] using hm_lb
 have hprob_pos:0 < (μ E).toReal :=
  lt_of_lt_of_le (by positivity) hm_lb'
 have hmarkovR:exp (t*(EX - log 2/lam))*(μ E).toReal<=exp (t^2*V):=by
  have htoR:=ENNReal.toReal_mono ENNReal.ofReal_ne_top hmarkov
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (exp_pos _).le,ENNReal.toReal_ofReal (exp_pos _).le] at htoR
  exact htoR
 have hlog_ineq:t*(EX - log 2/lam) - t^2*V<=log ((μ E).toReal⁻¹):=by
  have h1:=log_le_log (mul_pos (exp_pos _) hprob_pos) hmarkovR
  rw [log_mul (exp_pos _).ne' hprob_pos.ne',log_exp,log_exp] at h1
  rw [log_inv];linarith
 have hquad:t*(EX - log 2/lam) - t^2*V=(EX - log 2/lam)^2/(4*V):=by
  unfold t;field_simp [hV_pos.ne'];ring
 have hinv_le:log ((μ E).toReal⁻¹)<=log (c⁻¹)+9*log (n:R)+2*tStar*sqrt (n:R):=by
  have h1:(μ E).toReal⁻¹<=(c*((n:R)^9)⁻¹*exp (-2*tStar*sqrt (n:R)))⁻¹ :=
   inv_anti₀ (by positivity) hm_lb'
  have h2:=log_le_log (inv_pos.mpr hprob_pos) h1
  refine h2.trans_eq ?_
  rw [mul_inv,mul_inv,inv_inv,← exp_neg,
    log_mul (mul_pos (inv_pos.mpr hc_pos) (pow_pos hn 9)).ne' (exp_pos _).ne',
    log_mul (inv_pos.mpr hc_pos).ne' (pow_pos hn 9).ne',log_pow,log_exp]
  push_cast;ring
 have hfinal:(EX - log 2/lam)^2/(4*V) < (EX - log 2/lam)^2/(4*V):=by
  have hlt1:ε^2/(4*V) < (EX - log 2/lam)^2/(4*V) :=
   div_lt_div_of_pos_right (pow_lt_pow_left₀ hΔ hε.le (by norm_num)) (by positivity)
  have hlt2:log (c⁻¹)+9*log (n:R)+2*tStar*sqrt (n:R) < ε^2/(4*V):=by
   have hm_sm':(log (c⁻¹)+9*log (n:R)+2*tStar*sqrt (n:R))/(n:R) <
     ε^2/(4*π^2*28800):=by
    have hn_eq:(n:R)=(2*m:R):=by unfold n;push_cast;ring
    simpa [hn_eq] using hm_sm
   have hmul:=mul_lt_mul_of_pos_right hm_sm' hn
   rw [div_mul_cancel₀ _ hn.ne'] at hmul
   refine hmul.trans_eq ?_
   unfold V;field_simp [hn.ne',pi_pos.ne']
  linarith
 exact absurd hfinal (lt_irrefl _)
noncomputable def rad1:Measure R :=
 (1/2:ENNReal) • Measure.dirac 1+(1/2:ENNReal) • Measure.dirac (-1)
instance:IsProbabilityMeasure rad1:=by
 constructor
 simp only [rad1,Measure.add_apply,Measure.smul_apply,Measure.dirac_apply' _ MeasurableSet.univ,
  Set.indicator_univ,Pi.one_apply,smul_eq_mul,mul_one]
 rw [← two_mul,ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
noncomputable def rE (n:ℕ):Measure (Ei n->R) :=
 Measure.pi (fun _:Ei n=>rad1)
instance (n:ℕ):IsProbabilityMeasure (rE n):=by
 unfold rE;infer_instance
lemma integral_rad1 (f:R->R):∫ x,f x ∂rad1=(1/2:R)*f 1+(1/2:R)*f (-1):=by
 have hi1:Integrable f ((1/2:ENNReal) • Measure.dirac 1) :=
  (integrable_dirac (by exact enorm_lt_top)).smul_measure (by norm_num)
 have hi2:Integrable f ((1/2:ENNReal) • Measure.dirac (-1)) :=
  (integrable_dirac (by exact enorm_lt_top)).smul_measure (by norm_num)
 unfold rad1
 rw [integral_add_measure hi1 hi2,integral_smul_measure,integral_smul_measure,
   integral_dirac,integral_dirac]
 simp [smul_eq_mul]
lemma integrable_rad1 (f:R->R):Integrable f rad1:=by
 unfold rad1
 exact ((integrable_dirac (by exact enorm_lt_top)).smul_measure (by norm_num)).add_measure
  ((integrable_dirac (by exact enorm_lt_top)).smul_measure (by norm_num))
lemma gaussian_moments' :
  (∫ x:R,x ∂N01=0) /\
  (∫ x:R,x^2 ∂N01=1) /\
  (∫ x:R,|x| ^ 3 ∂N01<=20) /\
  Integrable (fun x:R=>x) (N01) /\
  Integrable (fun x:R=>x^2) (N01) /\
  Integrable (fun x:R=>|x| ^ 3) (N01):=by
 have hm1:∫ x:R,x ∂N01=0:=integral_id_gaussianReal
 have hint1:Integrable (fun x:R=>x) (N01) :=
  (memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable le_rfl
 have hint2:Integrable (fun x:R=>x^2) (N01) :=
  (memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable_sq
 have hm2:∫ x:R,x^2 ∂N01=1:=by
  have hv:=variance_id_gaussianReal (μ:=0) (v:=1)
  rw [variance_eq_integral measurable_id.aemeasurable] at hv
  simpa [hm1] using hv
 have hdom:∀ x:R,|x| ^ 3<=6*(exp x+exp (-x)):=fun x=>by
  have hpos:∀ u:R,0<=u->u^3/6<=exp u:=fun u hu=>by
   have h:=sum_le_exp_of_nonneg hu 4
   simp [Finset.sum_range_succ,Nat.factorial] at h
   linarith [sq_nonneg u]
  rcases le_total 0 x with hx | hx
  . rw [aon hx];linarith [hpos x hx,exp_pos (-x)]
  . rw [abs_of_nonpos hx];linarith [hpos (-x) (by linarith),exp_pos x]
 have hint_exp:Integrable (fun x:R=>6*(exp x+exp (-x))) (N01):=by
  have hp:=integrable_exp_mul_gaussianReal (μ:=0) (v:=1) 1
  have hn:=integrable_exp_mul_gaussianReal (μ:=0) (v:=1) (-1)
  simp only [one_mul,neg_one_mul] at hp hn
  exact (hp.add hn).const_mul 6
 have hint3:Integrable (fun x:R=>|x| ^ 3) (N01) :=
  Integrable.mono' hint_exp (by fun_prop:Continuous fun x:R=>|x| ^ 3).aestronglyMeasurable
   (Eventually.of_forall fun x=>by rw [Real.norm_eq_abs,aon (by positivity)];exact hdom x)
 have hm3:∫ x:R,|x| ^ 3 ∂N01<=20:=by
  calc ∫ x:R,|x| ^ 3 ∂N01
    <= ∫ x:R,6*(exp x+exp (-x)) ∂N01:=integral_mono hint3 hint_exp hdom
   _ = 6*((∫ x:R,exp (1*x) ∂N01)+(∫ x:R,exp ((-1)*x) ∂N01)):=by
     have hp:=integrable_exp_mul_gaussianReal (μ:=0) (v:=1) 1
     have hn:=integrable_exp_mul_gaussianReal (μ:=0) (v:=1) (-1)
     rw [integral_const_mul,integral_add (by simpa using hp) (by simpa using hn)];simp
   _ = 12*exp (1/2):=by
     have h1:∫ x:R,exp (1*x) ∂N01=exp (1/2):=by
      have:=congrFun (mgf_id_gaussianReal (μ:=0) (v:=1)) 1
      simpa [mgf] using this
     have h2:∫ x:R,exp ((-1)*x) ∂N01=exp (1/2):=by
      have:=congrFun (mgf_id_gaussianReal (μ:=0) (v:=1)) (-1)
      simpa [mgf] using this
     rw [h1,h2];ring
   _ <= 20:=by
     have he:exp (1/2:R)<=5/3:=by
      have:=exp_bound (x:=1/2) (by norm_num) (n:=4) (by norm_num)
      simp [Finset.sum_range_succ,Nat.factorial] at this
      linarith [(abs_le.mp this).2]
     linarith
 exact ⟨hm1,hm2,hm3,hint1,hint2,hint3⟩
lemma taylor3_bound {g g1 g2 g3:R->R} {M3:R} (hM3:0<=M3)
  (hd1:∀ x,HD g (g1 x) x)
  (hd2:∀ x,HD g1 (g2 x) x)
  (hd3:∀ x,HD g2 (g3 x) x)
  (hb3:∀ x,|g3 x| <= M3) (x:R) :
  |g x - (g 0+g1 0*x+g2 0/2*x^2)| <= M3/6 * |x| ^ 3:=by
 let h:=fun t=>g t - (g 0+g1 0*t+g2 0/2*t^2)
 let h1:=fun t=>g1 t - (g1 0+g2 0*t)
 let h2:=fun t=>g2 t - g2 0
 have hh1:∀ t,HD h (h1 t) t:=fun t =>
  ((hd1 t).fun_sub (((hasDerivAt_const t (g 0)).fun_add ((hdi t).const_mul (g1 0))).fun_add
   ((hdp 2 t).const_mul (g2 0/2)))).congr_deriv (by dsimp only [h1];ring)
 have hh2:∀ t,HD h1 (h2 t) t:=fun t =>
  ((hd2 t).fun_sub ((hasDerivAt_const t (g1 0)).fun_add ((hdi t).const_mul (g2 0)))).congr_deriv
   (by dsimp only [h2];ring)
 have hh3:∀ t,HD h2 (g3 t) t:=fun t=>by simpa [h2] using (hd3 t).sub_const (g2 0)
 have h2_bd:∀ t,|h2 t| <= M3 * |t| := fun t=>by
  have hpos:∀ s ≥ 0,|h2 s| <= M3*s:=fun s hs=>by
   have hdu:∀ y,HD (fun y=>M3*y - h2 y) (M3 - g3 y) y:=fun y=>by
    simpa using ((hdi y).const_mul M3).fun_sub (hh3 y)
   have hdl:∀ y,HD (fun y=>M3*y+h2 y) (M3+g3 y) y:=fun y=>by
    simpa using ((hdi y).const_mul M3).fun_add (hh3 y)
   have hu:MonotoneOn (fun y=>M3*y - h2 y) (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun y _=>(hdu y).continuousAt.continuousWithinAt)
     (fun y _=>(hdu y).differentiableAt.differentiableWithinAt)
     (fun y _=>by rw [(hdu y).deriv];linarith [(abs_le.mp (hb3 y)).2])
   have hl:MonotoneOn (fun y=>M3*y+h2 y) (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun y _=>(hdl y).continuousAt.continuousWithinAt)
     (fun y _=>(hdl y).differentiableAt.differentiableWithinAt)
     (fun y _=>by rw [(hdl y).deriv];linarith [(abs_le.mp (hb3 y)).1])
   have h0u:=hu Set.self_mem_Ici hs hs;simp [h2] at h0u
   have h0l:=hl Set.self_mem_Ici hs hs;simp [h2] at h0l
   exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hneg:∀ s ≤ 0,|h2 s| <= M3*(-s):=fun s hs=>by
   have hdu:∀ y,HD (fun y=>-M3*y - h2 y) (-M3 - g3 y) y:=fun y=>by
    simpa using ((hdi y).const_mul (-M3)).fun_sub (hh3 y)
   have hdl:∀ y,HD (fun y=>-M3*y+h2 y) (-M3+g3 y) y:=fun y=>by
    simpa using ((hdi y).const_mul (-M3)).fun_add (hh3 y)
   have hu:AntitoneOn (fun y=>-M3*y - h2 y) (Set.Iic 0) :=
    antitoneOn_of_deriv_nonpos (convex_Iic 0) (fun y _=>(hdu y).continuousAt.continuousWithinAt)
     (fun y _=>(hdu y).differentiableAt.differentiableWithinAt)
     (fun y _=>by rw [(hdu y).deriv];linarith [(abs_le.mp (hb3 y)).1])
   have hl:AntitoneOn (fun y=>-M3*y+h2 y) (Set.Iic 0) :=
    antitoneOn_of_deriv_nonpos (convex_Iic 0) (fun y _=>(hdl y).continuousAt.continuousWithinAt)
     (fun y _=>(hdl y).differentiableAt.differentiableWithinAt)
     (fun y _=>by rw [(hdl y).deriv];linarith [(abs_le.mp (hb3 y)).2])
   have h0u:=hu hs Set.self_mem_Iic hs;simp [h2] at h0u
   have h0l:=hl hs Set.self_mem_Iic hs;simp [h2] at h0l
   exact abs_le.mpr ⟨by linarith,by linarith⟩
  rcases le_total 0 t with ht | ht
  . rw [aon ht];exact hpos t ht
  . rw [abs_of_nonpos ht];exact hneg t ht
 have h1_bd:∀ t,|h1 t| <= M3/2*t^2:=fun t=>by
  rcases le_total 0 t with ht | ht
  .
   have hu:MonotoneOn (fun y=>M3/2*y^2 - h1 y) (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
     (fun y _=>(((hdp 2 y).const_mul (M3/2)).fun_sub (hh2 y)).continuousAt.continuousWithinAt)
     (fun y _=>(((hdp 2 y).const_mul (M3/2)).fun_sub (hh2 y)).differentiableAt.differentiableWithinAt)
     (fun y hy=>by
      rw [interior_Ici] at hy
      rw [((((hdp 2 y).const_mul (M3/2)).fun_sub (hh2 y)).deriv)]
      have hb:=(abs_le.mp (h2_bd y)).2;rw [abs_of_pos hy] at hb;norm_num;linarith)
   have hl:MonotoneOn (fun y=>M3/2*y^2+h1 y) (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
     (fun y _=>(((hdp 2 y).const_mul (M3/2)).fun_add (hh2 y)).continuousAt.continuousWithinAt)
     (fun y _=>(((hdp 2 y).const_mul (M3/2)).fun_add (hh2 y)).differentiableAt.differentiableWithinAt)
     (fun y hy=>by
      rw [interior_Ici] at hy
      rw [((((hdp 2 y).const_mul (M3/2)).fun_add (hh2 y)).deriv)]
      have hb:=(abs_le.mp (h2_bd y)).1;rw [abs_of_pos hy] at hb;norm_num;linarith)
   have h0u:=hu Set.self_mem_Ici ht ht;simp [h1] at h0u
   have h0l:=hl Set.self_mem_Ici ht ht;simp [h1] at h0l
   exact abs_le.mpr ⟨by linarith,by linarith⟩
  .
   have hu:AntitoneOn (fun y=>M3/2*y^2 - h1 y) (Set.Iic 0) :=
    antitoneOn_of_deriv_nonpos (convex_Iic 0)
     (fun y _=>(((hdp 2 y).const_mul (M3/2)).fun_sub (hh2 y)).continuousAt.continuousWithinAt)
     (fun y _=>(((hdp 2 y).const_mul (M3/2)).fun_sub (hh2 y)).differentiableAt.differentiableWithinAt)
     (fun y hy=>by
      rw [interior_Iic] at hy
      rw [((((hdp 2 y).const_mul (M3/2)).fun_sub (hh2 y)).deriv)]
      have hb:=(abs_le.mp (h2_bd y)).1;rw [abs_of_neg hy] at hb;norm_num;linarith)
   have hl:AntitoneOn (fun y=>M3/2*y^2+h1 y) (Set.Iic 0) :=
    antitoneOn_of_deriv_nonpos (convex_Iic 0)
     (fun y _=>(((hdp 2 y).const_mul (M3/2)).fun_add (hh2 y)).continuousAt.continuousWithinAt)
     (fun y _=>(((hdp 2 y).const_mul (M3/2)).fun_add (hh2 y)).differentiableAt.differentiableWithinAt)
     (fun y hy=>by
      rw [interior_Iic] at hy
      rw [((((hdp 2 y).const_mul (M3/2)).fun_add (hh2 y)).deriv)]
      have hb:=(abs_le.mp (h2_bd y)).2;rw [abs_of_neg hy] at hb;norm_num;linarith)
   have h0u:=hu ht Set.self_mem_Iic ht;simp [h1] at h0u
   have h0l:=hl ht Set.self_mem_Iic ht;simp [h1] at h0l
   exact abs_le.mpr ⟨by linarith,by linarith⟩
 rcases le_total 0 x with hx | hx
 .
  rw [aon hx]
  have hu:MonotoneOn (fun y=>M3/6*y^3 - h y) (Set.Ici 0) :=
   monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun y _=>(((hdp 3 y).const_mul (M3/6)).fun_sub (hh1 y)).continuousAt.continuousWithinAt)
    (fun y _=>(((hdp 3 y).const_mul (M3/6)).fun_sub (hh1 y)).differentiableAt.differentiableWithinAt)
    (fun y _=>by
     rw [((((hdp 3 y).const_mul (M3/6)).fun_sub (hh1 y)).deriv)]
     have hb:=(abs_le.mp (h1_bd y)).2;norm_num;linarith)
  have hl:MonotoneOn (fun y=>M3/6*y^3+h y) (Set.Ici 0) :=
   monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun y _=>(((hdp 3 y).const_mul (M3/6)).fun_add (hh1 y)).continuousAt.continuousWithinAt)
    (fun y _=>(((hdp 3 y).const_mul (M3/6)).fun_add (hh1 y)).differentiableAt.differentiableWithinAt)
    (fun y _=>by
     rw [((((hdp 3 y).const_mul (M3/6)).fun_add (hh1 y)).deriv)]
     have hb:=(abs_le.mp (h1_bd y)).1;norm_num;linarith)
  have h0u:=hu Set.self_mem_Ici hx hx;simp [h] at h0u
  have h0l:=hl Set.self_mem_Ici hx hx;simp [h] at h0l
  exact abs_le.mpr ⟨by linarith,by linarith⟩
 .
  rw [abs_of_nonpos hx]
  have hu:AntitoneOn (fun y=>-(M3/6)*y^3 - h y) (Set.Iic 0) :=
   antitoneOn_of_deriv_nonpos (convex_Iic 0)
    (fun y _=>(((hdp 3 y).const_mul (-(M3/6))).fun_sub (hh1 y)).continuousAt.continuousWithinAt)
    (fun y _=>(((hdp 3 y).const_mul (-(M3/6))).fun_sub (hh1 y)).differentiableAt.differentiableWithinAt)
    (fun y _=>by
     rw [((((hdp 3 y).const_mul (-(M3/6))).fun_sub (hh1 y)).deriv)]
     have hb:=(abs_le.mp (h1_bd y)).1;norm_num;linarith)
  have hl:AntitoneOn (fun y=>-(M3/6)*y^3+h y) (Set.Iic 0) :=
   antitoneOn_of_deriv_nonpos (convex_Iic 0)
    (fun y _=>(((hdp 3 y).const_mul (-(M3/6))).fun_add (hh1 y)).continuousAt.continuousWithinAt)
    (fun y _=>(((hdp 3 y).const_mul (-(M3/6))).fun_add (hh1 y)).differentiableAt.differentiableWithinAt)
    (fun y _=>by
     rw [((((hdp 3 y).const_mul (-(M3/6))).fun_add (hh1 y)).deriv)]
     have hb:=(abs_le.mp (h1_bd y)).2;norm_num;linarith)
  have h0u:=hu hx Set.self_mem_Iic hx;simp [h] at h0u
  have h0l:=hl hx Set.self_mem_Iic hx;simp [h] at h0l
  have hrew:M3/6*(-x)^3 = -(M3/6)*x^3:=by ring
  rw [hrew];exact abs_le.mpr ⟨by linarith,by linarith⟩
lemma lindeberg_one_dim {g g1 g2 g3:R->R} {M3:R} (hM3:0<=M3)
  (hbd:∀ x,|g x| <= 1)
  (hd1:∀ x,HD g (g1 x) x)
  (hd2:∀ x,HD g1 (g2 x) x)
  (hd3:∀ x,HD g2 (g3 x) x)
  (hb3:∀ x,|g3 x| <= M3) :
  |∫ x,g x ∂rad1 - ∫ x,g x ∂N01| <= 4*M3:=by
 obtain ⟨hm1,hm2,hm3,hint1,hint2,hint3⟩:=gaussian_moments'
 let P:R->R:=fun x=>g 0+g1 0*x+g2 0/2*x^2
 have hP_rad:∫ x,P x ∂rad1=g 0+g2 0/2:=by
  rw [integral_rad1];unfold P;ring
 have hP_g:∫ x,P x ∂N01=g 0+g2 0/2:=by
  have h1:Integrable (fun x:R=>g 0+g1 0*x) (N01) :=
   (integrable_const (g 0)).add (hint1.const_mul (g1 0))
  have h2:Integrable (fun x:R=>g2 0/2*x^2) (N01) :=
   hint2.const_mul (g2 0/2)
  have hadd1:∫ x,P x ∂N01 =
    (∫ x,(g 0+g1 0*x) ∂N01)+∫ x,(g2 0/2*x^2) ∂N01 :=
   integral_add h1 h2
  have hadd2:∫ x,(g 0+g1 0*x) ∂N01 =
    (∫ _x,g 0 ∂N01)+∫ x,(g1 0*x) ∂N01 :=
   integral_add (integrable_const (g 0)) (hint1.const_mul (g1 0))
  rw [hadd1,hadd2,integral_const,probReal_univ,one_smul,integral_const_mul,integral_const_mul,hm1,hm2]
  ring
 have hg_cont:Continuous g:=continuous_iff_continuousAt.mpr fun x=>(hd1 x).continuousAt
 have hg_int_g:Integrable g (N01) :=
  Integrable.of_bound hg_cont.aestronglyMeasurable 1 (Eventually.of_forall fun x=>by simpa [Real.norm_eq_abs] using hbd x)
 have hP_int_g:Integrable P (N01) :=
  ((integrable_const (g 0)).add (hint1.const_mul (g1 0))).add (hint2.const_mul (g2 0/2))
 have hdiff:∫ x,g x ∂rad1 - ∫ x,g x ∂N01 =
   (∫ x,(g x - P x) ∂rad1) - (∫ x,(g x - P x) ∂N01):=by
  rw [integral_sub (integrable_rad1 g) (integrable_rad1 P),integral_sub hg_int_g hP_int_g,hP_rad,hP_g]
  ring
 rw [hdiff]
 have h1:|∫ x,(g x - P x) ∂rad1| <= M3/6:=by
  rw [integral_rad1]
  have ha:|g 1 - P 1| <= M3/6:=by simpa [P] using taylor3_bound hM3 hd1 hd2 hd3 hb3 1
  have hb:|g (-1) - P (-1)| <= M3/6:=by simpa [P] using taylor3_bound hM3 hd1 hd2 hd3 hb3 (-1)
  calc |(1/2:R)*(g 1 - P 1)+(1/2:R)*(g (-1) - P (-1))|
    <= |(1/2:R)*(g 1 - P 1)| + |(1/2:R)*(g (-1) - P (-1))| := abs_add_le _ _
   _ = (1/2:R) * |g 1 - P 1| + (1/2:R) * |g (-1) - P (-1)| := by
     rw [abs_mul,abs_mul,aon (by norm_num:(0:R)<=1/2)]
   _ <= (1/2:R)*(M3/6)+(1/2:R)*(M3/6):=by linarith
   _ = M3/6:=by ring
 have h2:|∫ x,(g x - P x) ∂N01| <= 20*(M3/6):=by
  calc |∫ x,(g x - P x) ∂N01|
    <= ∫ x,|g x - P x| ∂N01:=abs_integral_le_integral_abs
   _ <= ∫ x,(M3/6) * |x| ^ 3 ∂N01 :=
     integral_mono (hg_int_g.sub hP_int_g).abs (hint3.const_mul _) (taylor3_bound hM3 hd1 hd2 hd3 hb3)
   _ = (M3/6)*∫ x,|x| ^ 3 ∂N01:=integral_const_mul _ _
   _ <= (M3/6)*20:=mlL hm3 (by positivity)
   _ = 20*(M3/6):=by ring
 calc |(∫ x,(g x - P x) ∂rad1) - (∫ x,(g x - P x) ∂N01)|
   <= |∫ x,(g x - P x) ∂rad1| + |∫ x,(g x - P x) ∂N01| := abs_sub _ _
  _ <= M3/6+20*(M3/6):=add_le_add h1 h2
  _ <= 4*M3:=by linarith [hM3]
lemma piCongrLeft_apply_symm {ι₁ ι₂:Type*} (e:ι₁ ≃ ι₂) (z:ι₁->R) (y:ι₂) :
  MeasurableEquiv.piCongrLeft (fun _:ι₂=>R) e z y=z (e.symm y):=by
 have h:=MeasurableEquiv.piCongrLeft_apply_apply (β:=fun _:ι₂=>R) e z (e.symm y)
 simpa using h
lemma lindeberg_step_fin {N:ℕ} (F:(Fin N->R)->R) (hFc:Continuous F) (hFbd:∀ z,|F z| <= 1)
  {M3:R} (hM3:0<=M3)
  (hderiv:∀ (z:Fin N->R) (i:Fin N),∃ g1 g2 g3:R->R,
   (∀ x,HD (fun y=>F (Function.update z i y)) (g1 x) x) /\
   (∀ x,HD g1 (g2 x) x) /\
   (∀ x,HD g2 (g3 x) x) /\
   (∀ x,|g3 x| <= M3))
  (k:ℕ) (hk:k < N) :
  |∫ z,F z ∂Measure.pi (fun i:Fin N=>if i.1 < k+1 then rad1 else N01) -
   ∫ z,F z ∂Measure.pi (fun i:Fin N=>if i.1 < k then rad1 else N01)| <= 4*M3:=by
 cases N with
 | zero=>omega
 | succ N' =>
  let ik:Fin (N'+1):=⟨k,hk⟩
  let ν1:Fin (N'+1)->Measure R:=fun i=>if i.1 < k+1 then rad1 else N01
  let ν0:Fin (N'+1)->Measure R:=fun i=>if i.1 < k then rad1 else N01
  haveI:∀ i,IsProbabilityMeasure (ν1 i):=fun i=>by unfold ν1;split_ifs <;> infer_instance
  haveI:∀ i,IsProbabilityMeasure (ν0 i):=fun i=>by unfold ν0;split_ifs <;> infer_instance
  have hsame:∀ j:Fin N',ν1 (ik.succAbove j)=ν0 (ik.succAbove j):=fun j=>by
   unfold ν1 ν0
   have hne:(ik.succAbove j).1 ≠ k:=fun heq=>Fin.succAbove_ne ik j (Fin.ext heq)
   by_cases hlt:(ik.succAbove j).1 < k
   . rw [if_pos (by omega),if_pos hlt]
   . rw [if_neg (by omega),if_neg hlt]
  have hik1:ν1 ik=rad1:=by simp [ν1,ik]
  have hik0:ν0 ik=N01:=by simp [ν0,ik]
  let eSplit:=MeasurableEquiv.piFinSuccAbove (fun _:Fin (N'+1)=>R) ik
  have hmp1:=measurePreserving_piFinSuccAbove ν1 ik
  have hmp0:=measurePreserving_piFinSuccAbove ν0 ik
  let μtail:Measure (Fin N'->R):=Measure.pi (fun j:Fin N'=>ν0 (ik.succAbove j))
  haveI:IsProbabilityMeasure μtail:=by unfold μtail;infer_instance
  have htail_eq:Measure.pi (fun j:Fin N'=>ν1 (ik.succAbove j))=μtail:=by
   unfold μtail;congr 1;funext j;exact hsame j
  let G:R × (Fin N'->R)->R:=fun p=>F (eSplit.symm p)
  have hG_cont:Continuous G:=by
   refine hFc.comp (continuous_pi fun i=>?_)
   by_cases hi:i=ik
   .
    subst hi
    have:(fun p:R × (Fin N'->R)=>eSplit.symm p ik)=Prod.fst:=by ext p;simp [eSplit]
    rw [this];exact continuous_fst
   .
    obtain ⟨j,rfl⟩:=Fin.exists_succAbove_eq hi
    have:(fun p:R × (Fin N'->R)=>eSplit.symm p (ik.succAbove j))=fun p=>p.2 j:=by
     ext p;simp [eSplit]
    rw [this];exact (continuous_apply j).comp continuous_snd
  have hG_int1:Integrable G (rad1.prod μtail) :=
   Integrable.of_bound hG_cont.aestronglyMeasurable 1 (Eventually.of_forall fun p=>by simpa [Real.norm_eq_abs] using hFbd (eSplit.symm p))
  have hG_int0:Integrable G ((N01).prod μtail) :=
   Integrable.of_bound hG_cont.aestronglyMeasurable 1 (Eventually.of_forall fun p=>by simpa [Real.norm_eq_abs] using hFbd (eSplit.symm p))
  have hI1:∫ z,F z ∂Measure.pi ν1=∫ y,(∫ x,G (x,y) ∂rad1) ∂μtail:=by
   have hc:=hmp1.integral_comp' (g:=G)
   have heq:(fun z=>G (eSplit z))=F:=funext fun z=>by
    dsimp only [G];exact congrArg F (eSplit.symm_apply_apply z)
   rw [heq] at hc
   rw [hc,hik1,htail_eq,integral_prod_symm _ hG_int1]
  have hI0:∫ z,F z ∂Measure.pi ν0=∫ y,(∫ x,G (x,y) ∂N01) ∂μtail:=by
   have hc:=hmp0.integral_comp' (g:=G)
   have heq:(fun z=>G (eSplit z))=F:=funext fun z=>by
    dsimp only [G];exact congrArg F (eSplit.symm_apply_apply z)
   rw [heq] at hc
   rw [hc,hik0,integral_prod_symm _ hG_int0]
  change |∫ z,F z ∂Measure.pi ν1 - ∫ z,F z ∂Measure.pi ν0| <= 4*M3
  rw [hI1,hI0,← integral_sub hG_int1.integral_prod_right hG_int0.integral_prod_right]
  calc |∫ y,(∫ x,G (x,y) ∂rad1 - ∫ x,G (x,y) ∂N01) ∂μtail|
    <= ∫ y,|∫ x,G (x,y) ∂rad1 - ∫ x,G (x,y) ∂N01| ∂μtail:=abs_integral_le_integral_abs
   _ <= ∫ _y,4*M3 ∂μtail:=by
     refine integral_mono (hG_int1.integral_prod_right.sub hG_int0.integral_prod_right).abs
      (integrable_const _) fun y=>?_
     have hGy_eq:(fun x=>G (x,y))=fun x=>F (Function.update (eSplit.symm (0,y)) ik x):=by
      ext x;simp only [G];congr 1;ext i
      by_cases hi:i=ik
      . subst hi;simp [eSplit]
      .
       obtain ⟨j,rfl⟩:=Fin.exists_succAbove_eq hi
       simp [Function.update_of_ne hi,eSplit]
     rw [hGy_eq]
     obtain ⟨g1,g2,g3,hd1,hd2,hd3,hb3⟩:=hderiv (eSplit.symm (0,y)) ik
     exact lindeberg_one_dim hM3 (fun x=>hFbd _) hd1 hd2 hd3 hb3
   _ = 4*M3:=by rw [integral_const,probReal_univ,one_smul]
lemma softMin_lindeberg {m:ℕ} (hm:1<=m) {lam:R} (hlam:0 < lam) :
  |∫ A,sM m lam A ∂rE (2*m) - ∫ A,sM m lam A ∂gE (2*m)| <=
  2*(26880000+138240000*lam+82944000*lam^2)/sqrt (2*m:R):=by
 set n:ℕ:=2*m
 set N:ℕ:=Fintype.card (Ei n)
 let eFin:Fin N ≃ Ei n:=(Fintype.equivFin (Ei n)).symm
 let F:(Fin N->R)->R:=fun z=>sM m lam (MeasurableEquiv.piCongrLeft (fun _:Ei n=>R) eFin z)
 have hF_cont:Continuous F :=
  (sMc m lam).comp (continuous_pi fun e=>by
   have:(fun z:Fin N->R=>MeasurableEquiv.piCongrLeft (fun _:Ei n=>R) eFin z e) =
     fun z=>z (eFin.symm e):=funext fun z=>piCongrLeft_apply_symm eFin z e
   rw [this];exact continuous_apply (eFin.symm e))
 have hF_bd:∀ z,|F z| <= 1:=fun z=>by
  have hb:=sMb hm hlam (MeasurableEquiv.piCongrLeft (fun _:Ei n=>R) eFin z)
  rw [aon hb.1];exact hb.2
 let μk:ℕ->Measure (Fin N->R):=fun k =>
  Measure.pi (fun i:Fin N=>if i.1 < k then rad1 else N01)
 have hμ0:∫ z,F z ∂μk 0=∫ A,sM m lam A ∂gE n:=by
  have heq:μk 0=Measure.pi (fun _:Fin N=>N01):=by
   unfold μk;congr 1
  rw [heq]
  exact (measurePreserving_piCongrLeft (fun _:Ei n=>N01) eFin).integral_comp' (g:=sM m lam)
 have hμN:∫ z,F z ∂μk N=∫ A,sM m lam A ∂rE n:=by
  have heq:μk N=Measure.pi (fun _:Fin N=>rad1):=by
   unfold μk;congr 1;funext i;exact if_pos i.2
  rw [heq]
  exact (measurePreserving_piCongrLeft (fun _:Ei n=>rad1) eFin).integral_comp' (g:=sM m lam)
 rw [← hμ0,← hμN]
 set M3:R:=(26880000+138240000*lam+82944000*lam^2)/((2*m:R)^2*sqrt (2*m:R))
 have hM3_nn:0<=M3:=by positivity
 have hderiv:∀ (z:Fin N->R) (i:Fin N),∃ g1 g2 g3:R->R,
   (∀ x,HD (fun y=>F (Function.update z i y)) (g1 x) x) /\
   (∀ x,HD g1 (g2 x) x) /\
   (∀ x,HD g2 (g3 x) x) /\
   (∀ x,|g3 x| <= M3):=fun z i=>by
  let A0:Ei n->R:=MeasurableEquiv.piCongrLeft (fun _:Ei n=>R) eFin z
  have hupd:(fun y=>F (Function.update z i y))=fun y=>sM m lam (Function.update A0 (eFin i) y):=by
   ext y;simp only [F];congr 1;ext e
   rw [piCongrLeft_apply_symm]
   by_cases he:e=eFin i
   . subst he;simp
   .
    have hne:eFin.symm e ≠ i:=fun h=>he (by rw [← h,Equiv.apply_symm_apply])
    rw [Function.update_of_ne he,Function.update_of_ne hne];exact (piCongrLeft_apply_symm eFin z e).symm
  rw [hupd]
  obtain ⟨g1,g2,g3,hd1,hd2,hd3,_,hb3⟩:=softMin_coord_derivs hm hlam A0 (eFin i)
  exact ⟨g1,g2,g3,hd1,hd2,hd3,hb3⟩
 have htel:|∫ z,F z ∂μk N - ∫ z,F z ∂μk 0| <= (N:R)*(4*M3):=by
  have hsum:∫ z,F z ∂μk N - ∫ z,F z ∂μk 0 =
    ∑ k ∈ Finset.range N,(∫ z,F z ∂μk (k+1) - ∫ z,F z ∂μk k) :=
   (Finset.sum_range_sub (fun k=>∫ z,F z ∂μk k) N).symm
  rw [hsum]
  calc |∑ k ∈ Finset.range N,(∫ z,F z ∂μk (k+1) - ∫ z,F z ∂μk k)|
    <= ∑ k ∈ Finset.range N,|∫ z,F z ∂μk (k+1) - ∫ z,F z ∂μk k| := Finset.abs_sum_le_sum_abs _ _
   _ <= ∑ _k ∈ Finset.range N,(4*M3) :=
     Finset.sum_le_sum fun k hk=>lindeberg_step_fin F hF_cont hF_bd hM3_nn hderiv k (Finset.mem_range.mp hk)
   _ = (N:R)*(4*M3):=by simp
 refine htel.trans ?_
 have hn:(0:R) < (n:R):=by positivity
 have hn_eq:(n:R)=(2*m:R):=by unfold n;push_cast;ring
 calc (N:R)*(4*M3)<=((n:R)^2/2)*(4*M3) :=
    mlR (card_EdgeIdx_le n) (by positivity)
  _ = 2*(26880000+138240000*lam+82944000*lam^2)/sqrt (2*m:R):=by
    unfold M3;rw [hn_eq];field_simp [(show (2*m:R) ≠ 0 by positivity),(sqrt_pos.mpr (show (0:R) < 2*m by positivity)).ne'];ring
lemma cosh_le_exp_half_sq (u:R):(exp u+exp (-u))/2<=exp (u^2/2):=by
 have hpos:∀ x:R,0<=x->(exp x+exp (-x))/2<=exp (x^2/2):=fun x hx=>by
  have h1:∀ y:R,0<=y->(exp y - exp (-y))/2<=y*((exp y+exp (-y))/2):=fun y hy=>by
   let g:=fun t:R=>t*((exp t+exp (-t))/2) - (exp t - exp (-t))/2
   have hgd:∀ t:R,HD g (t*((exp t - exp (-t))/2)) t:=fun t=>by
    have he1:HD (fun s:R=>exp (-s)) (-exp (-t)) t:=by
     simpa using (hdi t).neg.exp
    have hsum:HD (fun s:R=>(exp s+exp (-s))/2) ((exp t - exp (-t))/2) t :=
     (((hasDerivAt_exp t).fun_add he1).div_const 2).congr_deriv (by ring)
    have hdiff:HD (fun s:R=>(exp s - exp (-s))/2) ((exp t+exp (-t))/2) t :=
     (((hasDerivAt_exp t).fun_sub he1).div_const 2).congr_deriv (by ring)
    have hmul:HD (fun s:R=>s*((exp s+exp (-s))/2))
      (1*((exp t+exp (-t))/2)+t*((exp t - exp (-t))/2)) t :=
     (hdi t).fun_mul hsum
    exact (hmul.fun_sub hdiff).congr_deriv (by ring)
   have hmono:MonotoneOn g (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
     (fun t _=>(hgd t).continuousAt.continuousWithinAt)
     (fun t _=>(hgd t).differentiableAt.differentiableWithinAt)
     (fun t ht=>by
      rw [interior_Ici] at ht;rw [(hgd t).deriv]
      have ht0:(0:R) < t:=ht
      have hex:exp (-t)<=exp t:=exp_le_exp.mpr (by linarith)
      nlinarith)
   have:=hmono Set.self_mem_Ici hy hy
   simp [g] at this;linarith
  let f:=fun t:R=>exp (-(t^2/2))*((exp t+exp (-t))/2)
  have hfd:∀ t:R,HD f
    (exp (-(t^2/2))*((exp t - exp (-t))/2 - t*((exp t+exp (-t))/2))) t:=fun t=>by
   have hd1:HD (fun s:R=>exp (-(s^2/2))) (exp (-(t^2/2))*(-t)) t:=by
    have hsq:HD (fun s:R=>-(s^2/2)) (-t) t :=
     (((hdp 2 t).div_const 2).fun_neg).congr_deriv (by norm_num)
    exact (hsq.exp).congr_deriv (by ring)
   have he1:HD (fun s:R=>exp (-s)) (-exp (-t)) t:=by
    simpa using (hdi t).neg.exp
   have hd2:HD (fun s:R=>(exp s+exp (-s))/2) ((exp t - exp (-t))/2) t :=
    (((hasDerivAt_exp t).fun_add he1).div_const 2).congr_deriv (by ring)
   exact (hd1.fun_mul hd2).congr_deriv (by ring)
  have hanti:AntitoneOn f (Set.Ici 0) :=
   antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun t _=>(hfd t).continuousAt.continuousWithinAt)
    (fun t _=>(hfd t).differentiableAt.differentiableWithinAt)
    (fun t ht=>by
     rw [interior_Ici] at ht;rw [(hfd t).deriv]
     have:=h1 t ht.le
     exact mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (by linarith))
  have hle:=hanti Set.self_mem_Ici hx hx
  simp only [f,sq,mul_zero,zero_div,neg_zero,exp_zero,one_mul] at hle
  norm_num at hle
  have:=mlL hle (exp_pos (x^2/2)).le
  have hcancel:exp (x^2/2)*(exp (-(x*x/2))*((exp x+exp (-x))/2))=(exp x+exp (-x))/2:=by
   rw [← mul_assoc,← exp_add,show x^2/2 + -(x*x/2)=0 by ring,exp_zero,one_mul]
  linarith
 rcases le_total 0 u with hu | hu
 . exact hpos u hu
 . simpa [add_comm,neg_sq] using hpos (-u) (by linarith)
lemma mcdiarmid_mgf_fin:∀ (N:ℕ) (F:(Fin N->R)->R) (c:R),0<=c ->
  Continuous F->(∀ z,|F z| <= 1) ->
  (∀ z i,|F (Function.update z i 1) - F (Function.update z i (-1))| <= c) ->
  ∀ t:R,0<=t ->
   ∫ z,exp (t*(F z - ∫ w,F w ∂Measure.pi (fun _:Fin N=>rad1)))
    ∂Measure.pi (fun _:Fin N=>rad1)<=exp (t^2*(N:R)*c^2/8):=by
 intro N
 induction N with
 | zero =>
  intro F c _ _ _ _ t _
  have hconst:∀ z w:Fin 0->R,F z=F w:=fun z w=>congrArg F (Subsingleton.elim z w)
  have hmean:∫ w,F w ∂Measure.pi (fun _:Fin 0=>rad1)=F (fun i=>Fin.elim0 i):=by
   have:F=fun _=>F (fun i=>Fin.elim0 i):=funext fun w=>hconst w _
   rw [this,integral_const,probReal_univ,one_smul]
  simp_rw [hmean,hconst _ (fun i=>Fin.elim0 i),sub_self,mul_zero,exp_zero]
  rw [integral_const,probReal_univ,one_smul];norm_num
 | succ N ih =>
  intro F c hc hFc hFbd hdiff t ht
  let μN:Measure (Fin N->R):=Measure.pi (fun _:Fin N=>rad1)
  let μS:Measure (Fin (N+1)->R):=Measure.pi (fun _:Fin (N+1)=>rad1)
  let e0:=MeasurableEquiv.piFinSuccAbove (fun _:Fin (N+1)=>R) (0:Fin (N+1))
  have hmp:=measurePreserving_piFinSuccAbove (fun _:Fin (N+1)=>rad1) (0:Fin (N+1))
  let Fp:R × (Fin N->R)->R:=fun p=>F (e0.symm p)
  have hFp_cont:Continuous Fp:=by
   refine hFc.comp (continuous_pi fun i=>?_)
   cases i using Fin.cases with
   | zero =>
    have:(fun p:R × (Fin N->R)=>e0.symm p 0)=Prod.fst:=by ext p;simp [e0]
    rw [this];exact continuous_fst
   | succ j =>
    have:(fun p:R × (Fin N->R)=>e0.symm p j.succ)=fun p=>p.2 j:=by
     ext p;simpa [e0] using (MeasurableEquiv.piFinSuccAbove_symm_apply_succAbove (0:Fin (N+1)) j p)
    rw [this];exact (continuous_apply j).comp continuous_snd
  let G:(Fin N->R)->R:=fun y=>(1/2:R)*Fp (1,y)+(1/2:R)*Fp (-1,y)
  have hG_cont:Continuous G :=
   (continuous_const.mul (hFp_cont.comp (continuous_const.prodMk continuous_id))).add
    (continuous_const.mul (hFp_cont.comp (continuous_const.prodMk continuous_id)))
  have hG_bd:∀ y,|G y| <= 1:=fun y=>by
   unfold G
   calc |(1/2:R)*Fp (1,y)+(1/2:R)*Fp (-1,y)|
     <= (1/2:R) * |Fp (1,y)| + (1/2:R) * |Fp (-1,y)| := by refine (abs_add_le _ _).trans ?_;rw [abs_mul,abs_mul,aon (by norm_num:(0:R)<=1/2)]
    _ <= 1:=by linarith [hFbd (e0.symm (1,y)),hFbd (e0.symm (-1,y))]
  have hG_diff:∀ y j,|G (Function.update y j 1) - G (Function.update y j (-1))| <= c:=fun y j=>by
   have hupd:∀ x v:R,e0.symm (x,Function.update y j v) =
     Function.update (e0.symm (x,y)) j.succ v:=fun x v=>by
    ext i;cases i using Fin.cases with
    | zero =>
     rw [Function.update_of_ne (Fin.succ_ne_zero j).symm]
     simp [e0]
    | succ k =>
     have h1:e0.symm (x,Function.update y j v) k.succ=Function.update y j v k:=by
      simpa [e0] using (MeasurableEquiv.piFinSuccAbove_symm_apply_succAbove (0:Fin (N+1)) k (x,Function.update y j v))
     have h2:e0.symm (x,y) k.succ=y k:=by
      simpa [e0] using (MeasurableEquiv.piFinSuccAbove_symm_apply_succAbove (0:Fin (N+1)) k (x,y))
     by_cases hkj:k=j
     . subst hkj;simp [h1]
     . simp [h1,h2,hkj]
   unfold G Fp
   rw [hupd 1 1,hupd 1 (-1),hupd (-1) 1,hupd (-1) (-1)]
   have hrew:(1/2:R)*F (Function.update (e0.symm (1,y)) j.succ 1) +
      (1/2:R)*F (Function.update (e0.symm (-1,y)) j.succ 1) -
     ((1/2:R)*F (Function.update (e0.symm (1,y)) j.succ (-1)) +
      (1/2:R)*F (Function.update (e0.symm (-1,y)) j.succ (-1))) =
     (1/2:R)*(F (Function.update (e0.symm (1,y)) j.succ 1) -
      F (Function.update (e0.symm (1,y)) j.succ (-1))) +
     (1/2:R)*(F (Function.update (e0.symm (-1,y)) j.succ 1) -
      F (Function.update (e0.symm (-1,y)) j.succ (-1))):=by ring
   rw [hrew]
   calc _ <= (1/2:R) * |F (Function.update (e0.symm (1,y)) j.succ 1) -
        F (Function.update (e0.symm (1,y)) j.succ (-1))| +
       (1/2:R) * |F (Function.update (e0.symm (-1,y)) j.succ 1) -
        F (Function.update (e0.symm (-1,y)) j.succ (-1))| := by refine (abs_add_le _ _).trans ?_;rw [abs_mul,abs_mul,aon (by norm_num:(0:R)<=1/2)]
    _ <= c:=by linarith [hdiff (e0.symm (1,y)) j.succ,hdiff (e0.symm (-1,y)) j.succ]
  have hmean_eq:∫ w,F w ∂μS=∫ y,G y ∂μN:=by
   have h1:∫ w,F w ∂μS=∫ p,Fp p ∂(rad1.prod μN):=by
    have hc:=hmp.integral_comp' (g:=Fp)
    have heq:(fun w=>Fp (e0 w))=F:=funext fun w=>by
     dsimp only [Fp];exact congrArg F (e0.symm_apply_apply w)
    rw [heq] at hc
    exact hc
   have hint:Integrable Fp (rad1.prod μN) :=
    Integrable.of_bound hFp_cont.aestronglyMeasurable 1 (Eventually.of_forall fun p=>by simpa [Real.norm_eq_abs] using hFbd (e0.symm p))
   rw [h1,integral_prod_symm _ hint]
   refine integral_congr_ae (Eventually.of_forall fun y=>?_)
   exact integral_rad1 (fun x=>Fp (x,y))
  rw [hmean_eq]
  set M:=∫ y,G y ∂μN
  let H:R × (Fin N->R)->R:=fun p=>exp (t*(Fp p - M))
  have hH_int:Integrable H (rad1.prod μN):=by
   refine Integrable.of_bound ((continuous_exp.comp (continuous_const.mul (hFp_cont.sub continuous_const))).aestronglyMeasurable)
    (exp (t*(1 + |M|))) (Eventually.of_forall fun p=>?_)
   rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
   exact exp_le_exp.mpr (mlL (by linarith [(abs_le.mp (hFbd (e0.symm p))).2,neg_abs_le M]) ht)
  have hsplit:∫ z,exp (t*(F z - M)) ∂μS=∫ y,(∫ x,H (x,y) ∂rad1) ∂μN:=by
   have h1:∫ z,exp (t*(F z - M)) ∂μS=∫ p,H p ∂(rad1.prod μN):=by
    have hc:=hmp.integral_comp' (g:=H)
    have heq:(fun w=>H (e0 w))=fun z=>exp (t*(F z - M)):=funext fun w=>by
     dsimp only [H,Fp];rw [e0.symm_apply_apply w]
    rw [heq] at hc
    exact hc
   rw [h1,integral_prod_symm _ hH_int]
  rw [hsplit]
  have hinner:∀ y:Fin N->R,∫ x,H (x,y) ∂rad1<=exp (t^2*c^2/8)*exp (t*(G y - M)):=fun y=>by
   rw [integral_rad1]
   set d:R:=(Fp (1,y) - Fp (-1,y))/2
   have hd_abs:|d| <= c/2:=by
    have hupd0:∀ v:R,e0.symm (v,y)=Function.update (e0.symm (0,y)) 0 v:=fun v=>by
     ext i;cases i using Fin.cases with
     | zero=>simp [e0]
     | succ j =>
      have h1:e0.symm (v,y) j.succ=y j:=by
       simpa [e0] using (MeasurableEquiv.piFinSuccAbove_symm_apply_succAbove (0:Fin (N+1)) j (v,y))
      have h2:e0.symm (0,y) j.succ=y j:=by
       simpa [e0] using (MeasurableEquiv.piFinSuccAbove_symm_apply_succAbove (0:Fin (N+1)) j (0,y))
      simp [h1,h2]
    unfold d Fp;rw [hupd0 1,hupd0 (-1),abs_div,aon (by norm_num:(0:R)<=2)]
    exact dld (hdiff (e0.symm (0,y)) 0) (by norm_num)
   have h1:Fp (1,y) - M=(G y - M)+d:=by unfold G d;ring
   have h2:Fp (-1,y) - M=(G y - M) - d:=by unfold G d;ring
   have heq:(1/2:R)*H (1,y)+(1/2:R)*H (-1,y) =
     ((exp (t*d)+exp (-(t*d)))/2)*exp (t*(G y - M)):=by
    dsimp only [H]
    have he1:exp (t*(G y - M+d))=exp (t*(G y - M))*exp (t*d):=by
     rw [mul_add,exp_add]
    have he2:exp (t*(G y - M - d))=exp (t*(G y - M))*exp (-(t*d)):=by
     rw [mul_sub,sub_eq_add_neg,exp_add]
    rw [h1,h2,he1,he2]
    ring
   rw [heq]
   refine mlR ?_ (exp_pos _).le
   refine (cosh_le_exp_half_sq (t*d)).trans (exp_le_exp.mpr ?_)
   have hsq:(t*d)^2<=(t*(c/2))^2:=by
    rw [mul_pow,mul_pow]
    exact mlL (by rw [← sq_abs d];exact pow_le_pow_left₀ (abs_nonneg d) hd_abs 2) (sq_nonneg t)
   nlinarith
  have hG_exp_int:Integrable (fun y=>exp (t*(G y - M))) μN:=by
   refine Integrable.of_bound ((continuous_exp.comp (continuous_const.mul (hG_cont.sub continuous_const))).aestronglyMeasurable)
    (exp (t*(1 + |M|))) (Eventually.of_forall fun y=>?_)
   rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
   exact exp_le_exp.mpr (mlL (by linarith [(abs_le.mp (hG_bd y)).2,neg_abs_le M]) ht)
  calc ∫ y,(∫ x,H (x,y) ∂rad1) ∂μN
    <= ∫ y,exp (t^2*c^2/8)*exp (t*(G y - M)) ∂μN :=
     integral_mono hH_int.integral_prod_right (hG_exp_int.const_mul _) hinner
   _ = exp (t^2*c^2/8)*∫ y,exp (t*(G y - M)) ∂μN:=integral_const_mul _ _
   _ <= exp (t^2*c^2/8)*exp (t^2*(N:R)*c^2/8) :=
     mlL (ih G c hc hG_cont hG_bd hG_diff t ht) (exp_pos _).le
   _ = exp (t^2*((N+1:ℕ):R)*c^2/8):=by rw [← exp_add];congr 1;push_cast;ring
lemma softMin_rad_tail_tendsto_zero {lam δ:R} (hlam:0 < lam) (hδ:0 < δ) :
  Tendsto (fun m:ℕ=>(rE (2*m) {A | (∫ W,sM m lam W ∂rE (2*m))+δ<=sM m lam A}).toReal)
   atTop (𝓝 0):=by
 have hexp_tend:Tendsto (fun m:ℕ=>exp (-δ^2*(2*m:R)/460800)) atTop (𝓝 0):=by
  have hlin:Tendsto (fun m:ℕ=>-δ^2*(2*m:R)/460800) atTop atBot:=by
   have hpos:(0:R) < δ^2*2/460800:=by positivity
   have h:=tendsto_natCast_atTop_atTop.const_mul_atTop hpos
   have hn:Tendsto (fun m:ℕ=>-(δ^2*2/460800*(m:R))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h
   exact hn.congr fun m=>by ring
  exact tendsto_exp_atBot.comp hlin
 refine squeeze_zero' (Eventually.of_forall fun _=>ENNReal.toReal_nonneg) ?_ hexp_tend
 filter_upwards [eventually_ge_atTop 1] with m hm
 let n:ℕ:=2*m
 have hn:(0:R) < (n:R):=by positivity
 have hsn:0 < sqrt (n:R):=sqrt_pos.mpr hn
 set N:ℕ:=Fintype.card (Ei n)
 let eFin:Fin N ≃ Ei n:=(Fintype.equivFin (Ei n)).symm
 let F:(Fin N->R)->R:=fun z=>sM m lam (MeasurableEquiv.piCongrLeft (fun _:Ei n=>R) eFin z)
 have hF_cont:Continuous F :=
  (sMc m lam).comp (continuous_pi fun e=>by
   have:(fun z:Fin N->R=>MeasurableEquiv.piCongrLeft (fun _:Ei n=>R) eFin z e) =
     fun z=>z (eFin.symm e):=funext fun z=>piCongrLeft_apply_symm eFin z e
   rw [this];exact continuous_apply (eFin.symm e))
 have hF_bd:∀ z,|F z| <= 1:=fun z=>by
  have hb:=sMb hm hlam (MeasurableEquiv.piCongrLeft (fun _:Ei n=>R) eFin z)
  rw [aon hb.1];exact hb.2
 set c:R:=480/((n:R)*sqrt (n:R))
 have hc_nn:0<=c:=by positivity
 have hdiff:∀ z i,|F (Function.update z i 1) - F (Function.update z i (-1))| <= c:=fun z i=>by
  let A0:Ei n->R:=MeasurableEquiv.piCongrLeft (fun _:Ei n=>R) eFin z
  have hupd:∀ v:R,MeasurableEquiv.piCongrLeft (fun _:Ei n=>R) eFin (Function.update z i v) =
    Function.update A0 (eFin i) v:=fun v=>by
   ext e;rw [piCongrLeft_apply_symm]
   by_cases he:e=eFin i
   . subst he;simp
   .
    have hne:eFin.symm e ≠ i:=fun h=>he (by rw [← h,Equiv.apply_symm_apply])
    rw [Function.update_of_ne he,Function.update_of_ne hne];exact (piCongrLeft_apply_symm eFin z e).symm
  simp only [F,hupd]
  obtain ⟨g1,_,_,hd1,_,_,hb1,_⟩:=softMin_coord_derivs hm hlam A0 (eFin i)
  have hmvt:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
   (fun x _=>(hd1 x).hasDerivWithinAt) (fun x _=>by simpa [Real.norm_eq_abs] using hb1 x)
   (convex_Icc (-1:R) 1) (by norm_num:(-1:R) ∈ Set.Icc (-1) 1) (by norm_num:(1:R) ∈ Set.Icc (-1) 1)
  have hn_eq:(n:R)=(2*m:R):=by unfold n;push_cast;ring
  simp only [Real.norm_eq_abs] at hmvt
  have hnorm:|(1:R) - (-1)| = 2:=by norm_num
  rw [hnorm] at hmvt
  refine hmvt.trans_eq ?_
  unfold c;rw [hn_eq,sqrt_mul (by norm_num:(0:R)<=2)];ring
 set μN:=Measure.pi (fun _:Fin N=>rad1)
 have hmp:MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _:Ei n=>R) eFin) μN (rE n) :=
  measurePreserving_piCongrLeft (fun _:Ei n=>rad1) eFin
 have hmean:∫ W,sM m lam W ∂rE n=∫ z,F z ∂μN:=(hmp.integral_comp' (g:=sM m lam)).symm
 set M:=∫ z,F z ∂μN
 set t:R:=δ*(n:R)/230400
 have ht_pos:0 < t:=by positivity
 have hmgf:=mcdiarmid_mgf_fin N F c hc_nn hF_cont hF_bd hdiff t ht_pos.le
 have hNcsq:(N:R)*c^2/8<=115200/(n:R):=by
  have hsq:sqrt (n:R)^2=(n:R):=sq_sqrt hn.le
  calc (N:R)*c^2/8<=((n:R)^2/2)*c^2/8 :=
     dld (mlR (card_EdgeIdx_le n) (sq_nonneg c)) (by norm_num)
   _ = 14400/(n:R):=by unfold c;rw [div_pow,mul_pow,hsq];field_simp [hn.ne'];ring
   _ <= 115200/(n:R):=dld (by norm_num) hn.le
 have hset_eq:(rE n {A | (∫ W,sM m lam W ∂rE n)+δ<=sM m lam A}) =
   μN {z | M+δ<=F z}:=by
  rw [hmean]
  have hm_set:MeasurableSet {A:Ei n->R | M+δ<=sM m lam A} :=
   measurableSet_le measurable_const (sMc m lam).measurable
  simpa [F] using (hmp.measure_preimage hm_set.nullMeasurableSet).symm
 rw [hset_eq]
 have hmeas_S:MeasurableSet {z:Fin N->R | M+δ<=F z} :=
  measurableSet_le measurable_const hF_cont.measurable
 have hmarkov:exp (t*δ)*(μN {z | M+δ<=F z}).toReal<=exp (t^2*(115200/(n:R))):=by
  have h1:ENNReal.ofReal (exp (t*δ))*μN {z | M+δ<=F z} <=
    ENNReal.ofReal (exp (t^2*(N:R)*c^2/8)):=by
   calc ENNReal.ofReal (exp (t*δ))*μN {z | M+δ<=F z}
     = ∫⁻ _z in {z | M+δ<=F z},ENNReal.ofReal (exp (t*δ)) ∂μN:=by rw [setLIntegral_const]
    _ <= ∫⁻ z in {z | M+δ<=F z},ENNReal.ofReal (exp (t*(F z - M))) ∂μN :=
      setLIntegral_mono' hmeas_S fun z hz=>ENNReal.ofReal_le_ofReal (exp_le_exp.mpr (by
       have hz':M+δ<=F z:=hz;nlinarith))
    _ <= ∫⁻ z,ENNReal.ofReal (exp (t*(F z - M))) ∂μN:=setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ z,exp (t*(F z - M)) ∂μN):=by
      have hint:Integrable (fun z=>exp (t*(F z - M))) μN :=
       Integrable.of_bound ((continuous_exp.comp (continuous_const.mul (hF_cont.sub continuous_const))).aestronglyMeasurable)
        (exp (t*(1 + |M|))) (Eventually.of_forall fun z=>by
         rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
         exact exp_le_exp.mpr (mlL (by linarith [(abs_le.mp (hF_bd z)).2,neg_abs_le M]) ht_pos.le))
      rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _=>(exp_pos _).le)]
    _ <= ENNReal.ofReal (exp (t^2*(N:R)*c^2/8)):=ENNReal.ofReal_le_ofReal hmgf
  have hto:=ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (exp_pos _).le,ENNReal.toReal_ofReal (exp_pos _).le] at hto
  refine hto.trans (exp_le_exp.mpr ?_)
  have:t^2*(N:R)*c^2/8=t^2*((N:R)*c^2/8):=by ring
  rw [this];exact mlL hNcsq (sq_nonneg t)
 have hdiv:(μN {z | M+δ<=F z}).toReal<=exp (t^2*(115200/(n:R)) - t*δ):=by
  rw [exp_sub,le_div_iff₀ (exp_pos _),mul_comm];exact hmarkov
 refine hdiv.trans_eq (congrArg exp ?_)
 have hn_eq:(n:R)=(2*m:R):=by unfold n;push_cast;ring
 unfold t;rw [hn_eq];field_simp [hn.ne',(show (2*m:R) ≠ 0 by positivity)];ring
lemma radEdge_exists_nearly_friendly {ε:R} (hε:0 < ε) :
  Tendsto (fun m:ℕ=>rE (2*m) {A | ∃ s ∈ bS m,
   (2*m:R) - ε*(2*m:R) <=
    ((Finset.univ.filter fun i:Fin (2*m)=>gC/2<=fv0 (2*m) A s i).card:R)})
   atTop (𝓝 1):=by
 set lam:R:=4*log 2 / ε
 have hlog2_pos:0 < log 2:=log_pos (by norm_num)
 have hlam:0 < lam:=by positivity
 have hlog_lam:log 2/lam=ε / 4:=by unfold lam;field_simp [hε.ne',hlog2_pos.ne']
 have hgauss:=softMin_gauss_expectation_eventually_le hlam (show (0:R) < ε / 4 by linarith)
 have hlind_tend:Tendsto (fun m:ℕ =>
   2*(26880000+138240000*lam+82944000*lam^2)/sqrt (2*m:R)) atTop (𝓝 0):=by
  have hsq:Tendsto (fun m:ℕ=>sqrt (2*m:R)) atTop atTop :=
   (tendsto_rpow_atTop (by norm_num:(0:R) < 1/2)).comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)) |>.congr (fun m=>(sqrt_eq_rpow _).symm)
  exact tendsto_const_nhds.div_atTop hsq
 have hlind_sm:=hlind_tend.eventually (gt_mem_nhds (show (0:R) < ε / 4 by linarith))
 have htail:=softMin_rad_tail_tendsto_zero hlam (show (0:R) < ε / 4 by linarith)
 have hcompl:Tendsto (fun m:ℕ =>
   ENNReal.ofReal (1 - (rE (2*m) {A | (∫ W,sM m lam W ∂rE (2*m))+ε / 4<=sM m lam A}).toReal))
   atTop (𝓝 1):=by
  have h1:Tendsto (fun m:ℕ =>
    1 - (rE (2*m) {A | (∫ W,sM m lam W ∂rE (2*m))+ε / 4<=sM m lam A}).toReal)
    atTop (𝓝 1):=by simpa using tendsto_const_nhds.sub htail
  simpa [Function.comp_def,ENNReal.ofReal_one] using (ENNReal.continuous_ofReal.tendsto 1).comp h1
 refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hcompl tendsto_const_nhds ?_ (Eventually.of_forall fun _=>prob_le_one)
 filter_upwards [hgauss,hlind_sm,eventually_ge_atTop 1] with m hgm hlm hm1
 let n:ℕ:=2*m
 have hn:(0:R) < (n:R):=by positivity
 have hn_eq:(n:R)=(2*m:R):=by unfold n;push_cast;ring
 have hEX_rad:∫ A,sM m lam A ∂rE n<=3*ε / 4:=by
  have hl:=softMin_lindeberg hm1 hlam
  have h1:=(abs_le.mp hl).2
  linarith [hgm,hlm,hlog_lam]
 set Bad:Set (Ei n->R):={A | (∫ W,sM m lam W ∂rE n)+ε / 4<=sM m lam A}
 set Good:Set (Ei n->R):={A | ∃ s ∈ bS m,
  (2*m:R) - ε*(2*m:R)<=((Finset.univ.filter fun i:Fin n=>gC/2<=fv0 n A s i).card:R)}
 have hsub:Badᶜ ⊆ Good:=by
  intro A hA
  have hlt:sM m lam A < ε:=by
   have:¬((∫ W,sM m lam W ∂rE n)+ε / 4<=sM m lam A):=hA
   linarith
  obtain ⟨s,hs,hbf⟩:=softMin_ge_exists_badFrac hm1 hlam A
  refine ⟨s,hs,?_⟩
  have hbad_cnt:((Finset.univ.filter fun i:Fin n=>¬(gC/2<=fv0 n A s i)).card:R) <=
    ∑ i:Fin n,psi (fv0 n A s i):=by
   calc ((Finset.univ.filter fun i:Fin n=>¬(gC/2<=fv0 n A s i)).card:R)
     = ∑ i ∈ Finset.univ.filter (fun i:Fin n=>¬(gC/2<=fv0 n A s i)),(1:R):=by simp
    _ = ∑ i ∈ Finset.univ.filter (fun i:Fin n=>¬(gC/2<=fv0 n A s i)),psi (fv0 n A s i) :=
      Finset.sum_congr rfl fun i hi=>(psi_eq_one (le_of_lt (not_le.mp (Finset.mem_filter.mp hi).2))).symm
    _ <= ∑ i:Fin n,psi (fv0 n A s i) :=
      Finset.sum_le_univ_sum_of_nonneg fun i=>(psi_bounds _).1
  have hsum_lt:∑ i:Fin n,psi (fv0 n A s i)<=ε*(n:R):=by
   have hbf_le:badFrac m A s<=ε:=hbf.trans hlt.le
   have hdiv:(1/(2*m:R))*∑ i:Fin n,psi (fv0 n A s i)<=ε:=hbf_le
   rw [one_div,inv_mul_le_iff₀ (show (0:R) < 2*m by positivity)] at hdiv
   rw [← hn_eq,mul_comm] at hdiv
   exact hdiv
  have hcompl_card:(Finset.univ.filter fun i:Fin n=>gC/2<=fv0 n A s i).card +
    (Finset.univ.filter fun i:Fin n=>¬(gC/2<=fv0 n A s i)).card=n:=by
   rw [Finset.card_filter_add_card_filter_not,Finset.card_univ,Fintype.card_fin]
  have hcompl_R:((Finset.univ.filter fun i:Fin n=>gC/2<=fv0 n A s i).card:R) +
    ((Finset.univ.filter fun i:Fin n=>¬(gC/2<=fv0 n A s i)).card:R)=(n:R):=by
   exact_mod_cast hcompl_card
  have h2:(n:R) - ε*(n:R)<=((Finset.univ.filter fun i:Fin n=>gC/2<=fv0 n A s i).card:R):=by
   linarith
  rw [hn_eq] at h2
  exact h2
 have hBad_meas:MeasurableSet Bad:=measurableSet_le measurable_const (sMc m lam).measurable
 have h1:ENNReal.ofReal (1 - (rE n Bad).toReal)=rE n Badᶜ:=by
  rw [measure_compl hBad_meas (measure_ne_top _ _),measure_univ]
  have hne:rE n Bad ≠ ⊤:=measure_ne_top _ _
  rw [ENNReal.ofReal_sub 1 ENNReal.toReal_nonneg,ENNReal.ofReal_one,ENNReal.ofReal_toReal hne]
 rw [h1]
 exact measure_mono hsub
open scoped Classical in
noncomputable def graphToSign {n:ℕ} (G:SimpleGraph (Fin n)):Ei n->R :=
 fun e=>if G.Adj e.1.1 e.1.2 then 1 else -1
lemma graphToSign_injective (n:ℕ):Function.Injective (@graphToSign n):=by
 classical
 intro G1 G2 h
 ext u v
 rcases lt_trichotomy u v with hlt | rfl | hgt
 .
  have he:=congrFun h ⟨(u,v),hlt⟩
  simp only [graphToSign] at he
  by_cases h1:G1.Adj u v <;> by_cases h2:G2.Adj u v <;> simp [h1,h2] at he ⊢ <;> norm_num at he
 . simp [SimpleGraph.irrefl]
 .
  have he:=congrFun h ⟨(v,u),hgt⟩
  simp only [graphToSign] at he
  rw [G1.adj_comm,G2.adj_comm]
  by_cases h1:G1.Adj v u <;> by_cases h2:G2.Adj v u <;> simp [h1,h2] at he ⊢ <;> norm_num at he
open scoped Classical in
lemma radEdge_eq_card_mul (n:ℕ) (Q:(Ei n->R)->Prop) :
  rE n {A | Q A} =
  ((Finset.univ.filter (fun G:SimpleGraph (Fin n)=>Q (graphToSign G))).card:ENNReal) *
   (1/2:ENNReal)^(n.choose 2):=by
 let S:Finset (Ei n->R):=Finset.univ.image graphToSign
 have hrad1_sing:∀ x:R,rad1 {x}=if x=1\/x = -1 then (1/2:ENNReal) else 0:=fun x=>by
  unfold rad1
  simp only [Measure.add_apply,Measure.smul_apply,Measure.dirac_apply' _ (measurableSet_singleton x),
   Set.indicator_apply,Set.mem_singleton_iff,Pi.one_apply,smul_eq_mul]
  by_cases h1:x=1
  . subst h1;norm_num
  .
   by_cases h2:x = -1
   . subst h2;norm_num
   .
    have hn1:(1:R) ≠ x:=Ne.symm h1
    have hn2:(-1:R) ≠ x:=Ne.symm h2
    simp [h1,h2,hn1,hn2]
 have hpt:∀ G:SimpleGraph (Fin n),rE n {graphToSign G}=(1/2:ENNReal)^(n.choose 2):=fun G=>by
  unfold rE
  rw [Measure.pi_singleton]
  have hprod:∀ e:Ei n,rad1 {graphToSign G e}=(1/2:ENNReal):=fun e=>by
   rw [hrad1_sing];unfold graphToSign;by_cases h:G.Adj e.1.1 e.1.2 <;> simp [h]
  simp_rw [hprod,Finset.prod_const,Finset.card_univ,card_EdgeIdx]
 have hS_full:rE n (S:Set (Ei n->R))=1:=by
  have hdisj:(S:Set (Ei n->R))=⋃ G:SimpleGraph (Fin n),{graphToSign G}:=by
   ext A;simp [S]
  rw [hdisj,measure_iUnion (fun G1 G2 hne=>Set.disjoint_singleton.mpr fun heq=>hne (graphToSign_injective n heq))
   (fun _=>measurableSet_singleton _)]
  simp_rw [hpt,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hcardG:Fintype.card (SimpleGraph (Fin n))=2^(n.choose 2):=by
   have hbij:Fintype.card (SimpleGraph (Fin n))=Fintype.card (Ei n->Bool):=by
    refine Fintype.card_of_bijective (f:=fun (G:SimpleGraph (Fin n)) (e:Ei n)=>decide (G.Adj e.1.1 e.1.2))
     ⟨fun G1 G2 h=>?_,fun b=>?_⟩
    .
     ext u v
     rcases lt_trichotomy u v with hlt | rfl | hgt
     . simpa using congrFun h ⟨(u,v),hlt⟩
     . simp [SimpleGraph.irrefl]
     . rw [G1.adj_comm,G2.adj_comm];simpa using congrFun h ⟨(v,u),hgt⟩
    .
     refine ⟨{
          Adj:=fun (u v:Fin n)=>if h:u < v then b ⟨(u,v),h⟩=true
           else if h':v < u then b ⟨(v,u),h'⟩=true else False
          symm:=⟨fun u v h=>by
           by_cases hlt:u < v
           . rw [dif_neg (not_lt.mpr hlt.le),dif_pos hlt];rwa [dif_pos hlt] at h
           .
            by_cases hgt:v < u
            . rw [dif_pos hgt];rwa [dif_neg hlt,dif_pos hgt] at h
            . simp [hlt,hgt] at h⟩
          loopless:=⟨fun u h=>by simp at h⟩ },?_⟩
     ext e;simp [e.2]
   rw [hbij,Fintype.card_fun,Fintype.card_bool,card_EdgeIdx]
  rw [hcardG,Nat.cast_pow,Nat.cast_ofNat,← mul_pow,
    ENNReal.mul_div_cancel (by norm_num) (by norm_num),one_pow]
 have hcompl0:rE n (S:Set (Ei n->R))ᶜ=0:=by
  rw [measure_compl S.measurableSet (measure_ne_top _ _),measure_univ,hS_full,tsub_self]
 have hQ_eq:rE n {A | Q A}=rE n ({A | Q A} ∩ (S:Set (Ei n->R))):=by
  have hle1:rE n ({A | Q A} ∩ (S:Set (Ei n->R)))<=rE n {A | Q A} :=
   measure_mono Set.inter_subset_left
  have hle2:rE n {A | Q A}<=rE n ({A | Q A} ∩ (S:Set (Ei n->R))):=by
   calc rE n {A | Q A}
     <= rE n (({A | Q A} ∩ S) ∪ (S:Set (Ei n->R))ᶜ) :=
      measure_mono fun A hA=>by by_cases hS:A ∈ (S:Set (Ei n->R)) <;> simp [hA,hS]
    _ <= rE n ({A | Q A} ∩ S)+rE n (S:Set (Ei n->R))ᶜ:=measure_union_le _ _
    _ = rE n ({A | Q A} ∩ S):=by rw [hcompl0,add_zero]
  exact le_antisymm hle2 hle1
 rw [hQ_eq]
 have hinter:({A | Q A} ∩ (S:Set (Ei n->R))) =
   ⋃ G ∈ Finset.univ.filter (fun G:SimpleGraph (Fin n)=>Q (graphToSign G)),{graphToSign G}:=by
  ext A;simp only [Set.mem_inter_iff,Set.mem_setOf_eq,Finset.mem_coe,S,Finset.mem_image,
   Finset.mem_univ,true_and,Set.mem_iUnion,Finset.mem_filter,Set.mem_singleton_iff]
  constructor
  . rintro ⟨hQ,G,rfl⟩;exact ⟨G,hQ,rfl⟩
  . rintro ⟨G,hQ,rfl⟩;exact ⟨hQ,G,rfl⟩
 rw [hinter,measure_biUnion_finset
  (fun G1 _ G2 _ hne=>Set.disjoint_singleton.mpr fun heq=>hne (graphToSign_injective n heq))
  (fun _ _=>measurableSet_singleton _)]
 simp_rw [hpt,Finset.sum_const,nsmul_eq_mul]
lemma edgeSet_ncard_le_choose_two {n:ℕ} (G:SimpleGraph (Fin n)) :
  G.edgeSet.ncard<=n.choose 2:=by
 classical
 rw [← card_EdgeIdx n,Set.ncard_eq_toFinset_card']
 have hle:G.edgeSet.toFinset.card<=(Finset.univ.image (fun e:Ei n=>s(e.1.1,e.1.2))).card:=by
  refine Finset.card_le_card fun e he=>?_
  rw [Set.mem_toFinset] at he
  induction e using Sym2.ind with
  | _ u v =>
   have hadj:G.Adj u v:=he
   rcases lt_or_gt_of_ne hadj.ne with hlt | hgt
   . exact Finset.mem_image.mpr ⟨⟨(u,v),hlt⟩,Finset.mem_univ _,rfl⟩
   . exact Finset.mem_image.mpr ⟨⟨(v,u),hgt⟩,Finset.mem_univ _,Sym2.eq_swap⟩
 exact hle.trans (Finset.card_image_le.trans (by simp))
open scoped Classical in
lemma green91_prob_eq_card_mul' (n:ℕ) (P:SimpleGraph (Fin n)->Prop) :
  Green91.prob n P =
  ((Finset.univ.filter P).card:ENNReal)*(1/2:ENNReal)^(n.choose 2):=by
 unfold Green91.prob
 have hset:{G:SimpleGraph (Fin n) | P G}=⋃ G ∈ Finset.univ.filter P,{G}:=by
  ext G;simp
 have hmeas_sing:∀ G:SimpleGraph (Fin n),MeasurableSet ({G}:Set (SimpleGraph (Fin n))):=fun G=>by
  have heq:({G}:Set (SimpleGraph (Fin n)))=SimpleGraph.Adj ⁻¹' {G.Adj}:=by
   ext H;simp only [Set.mem_singleton_iff,Set.mem_preimage];exact SimpleGraph.ext_iff
  rw [heq]
  exact SimpleGraph.measurable_adj (measurableSet_singleton G.Adj)
 rw [hset,measure_biUnion_finset (fun G1 _ G2 _ hne=>Set.disjoint_singleton.mpr hne)
  (fun G _=>hmeas_sing G)]
 have hsing:∀ G:SimpleGraph (Fin n),
   SimpleGraph.binomialRandom (Fin n) ⟨1/2,by norm_num⟩ {G}=(1/2:ENNReal)^(n.choose 2):=fun G=>by
  rw [SimpleGraph.binomialRandom_singleton]
  have hp:(unitInterval.toNNReal ⟨1/2,by norm_num⟩:ENNReal)=(1/2:ENNReal):=by
   have h1:(unitInterval.toNNReal ⟨1/2,by norm_num⟩:NNReal)=(1/2:NNReal):=by
    ext;norm_num
   rw [h1];norm_num
  have hsp:(unitInterval.toNNReal (unitInterval.symm ⟨1/2,by norm_num⟩):ENNReal)=(1/2:ENNReal):=by
   have:unitInterval.symm ⟨1/2,by norm_num⟩=⟨1/2,by norm_num⟩:=by ext;norm_num
   rw [this,hp]
  rw [hp,hsp,← pow_add,Nat.card_eq_fintype_card,Fintype.card_fin,
    Nat.add_sub_of_le (edgeSet_ncard_le_choose_two G)]
 simp_rw [hsing,Finset.sum_const,nsmul_eq_mul]
lemma green91_prob_eq_radEdge (n:ℕ) (Q:(Ei n->R)->Prop) :
  Green91.prob n (fun G=>Q (graphToSign G))=rE n {A | Q A}:=by
 rw [green91_prob_eq_card_mul',radEdge_eq_card_mul]
lemma fieldVal_graphToSign_eq_friendliness {m:ℕ} (G:SimpleGraph (Fin (2*m)))
  {s:Finset (Fin (2*m))} (hs:s ∈ bS m) (v:Fin (2*m)) :
  fv0 (2*m) (graphToSign G) s v =
  (sqrt (2*m:R))⁻¹*(2*(Green91.friendliness G s v:R)+1):=by
 classical
 unfold fv0
 congr 1
 . push_cast;rfl
 have hterm:∀ w:Fin (2*m),
   ev0 (graphToSign G) v w*(spin s v*spin s w) =
   if w=v then 0
   else if G.Adj v w/\(w ∈ s ↔ v ∈ s) then 1
   else if G.Adj v w/\¬(w ∈ s ↔ v ∈ s) then -1
   else if ¬G.Adj v w/\(w ∈ s ↔ v ∈ s) then -1
   else 1:=fun w=>by
  by_cases hwv:w=v
  . subst hwv;rw [if_pos rfl];unfold ev0;simp
  .
   rw [if_neg hwv]
   have hedge:ev0 (graphToSign G) v w=if G.Adj v w then 1 else -1:=by
    unfold ev0 graphToSign
    rcases lt_or_gt_of_ne (Ne.symm hwv) with hlt | hgt
    . rw [dif_pos hlt]
    . rw [dif_neg (not_lt.mpr hgt.le),dif_pos hgt,G.adj_comm]
   have hsp:spin s v*spin s w=if (w ∈ s ↔ v ∈ s) then 1 else -1:=by
    unfold spin;by_cases hv:v ∈ s <;> by_cases hw:w ∈ s <;> simp [hv,hw]
   rw [hedge,hsp]
   by_cases ha:G.Adj v w <;> by_cases hb:(w ∈ s ↔ v ∈ s) <;> simp [ha,hb]
 have hsum:∑ w:Fin (2*m),ev0 (graphToSign G) v w*(spin s v*spin s w) =
   2*((Finset.univ.filter fun w=>G.Adj v w/\(w ∈ s ↔ v ∈ s)).card:R) -
   2*((Finset.univ.filter fun w=>G.Adj v w/\¬(w ∈ s ↔ v ∈ s)).card:R) +
   ((Finset.univ.filter fun w=>w ≠ v/\¬(w ∈ s ↔ v ∈ s)).card:R) -
   ((Finset.univ.filter fun w=>w ≠ v/\(w ∈ s ↔ v ∈ s)).card:R):=by
  have hpt:∀ w:Fin (2*m),
    ev0 (graphToSign G) v w*(spin s v*spin s w) =
    (if G.Adj v w/\(w ∈ s ↔ v ∈ s) then (2:R) else 0) -
    (if G.Adj v w/\¬(w ∈ s ↔ v ∈ s) then (2:R) else 0) +
    (if w ≠ v/\¬(w ∈ s ↔ v ∈ s) then (1:R) else 0) -
    (if w ≠ v/\(w ∈ s ↔ v ∈ s) then (1:R) else 0):=fun w=>by
   rw [hterm w]
   by_cases hwv:w=v
   . subst hwv;simp [SimpleGraph.irrefl]
   .
    by_cases ha:G.Adj v w <;> by_cases hb:(w ∈ s ↔ v ∈ s) <;>
     simp [hwv,ha,hb] <;> norm_num
  simp only [hpt,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_ite,Finset.sum_const_zero,
   add_zero,Finset.sum_const,nsmul_eq_mul]
  ring
 rw [hsum]
 have hscard:s.card=m:=(Finset.mem_filter.mp hs).2
 have hdiff_side:((Finset.univ.filter fun w:Fin (2*m)=>w ≠ v/\¬(w ∈ s ↔ v ∈ s)).card:R) -
   ((Finset.univ.filter fun w:Fin (2*m)=>w ≠ v/\(w ∈ s ↔ v ∈ s)).card:R)=1:=by
  have hsame_card:(Finset.univ.filter fun w:Fin (2*m)=>(w ∈ s ↔ v ∈ s)).card=m:=by
   by_cases hv:v ∈ s
   . convert hscard using 2;ext w;simp [hv]
   .
    have hcompl:(Finset.univ.filter fun w:Fin (2*m)=>w ∉ s).card=m:=by
     have h1:=Finset.card_filter_add_card_filter_not (s:=Finset.univ) (p:=fun w:Fin (2*m)=>w ∈ s)
     have h2:(Finset.univ.filter fun w:Fin (2*m)=>w ∈ s).card=m:=by convert hscard using 2;ext w;simp
     simp only [Finset.card_univ,Fintype.card_fin] at h1;omega
    convert hcompl using 2;ext w;simp [hv]
  have hopp_card:(Finset.univ.filter fun w:Fin (2*m)=>w ≠ v/\¬(w ∈ s ↔ v ∈ s)).card=m:=by
   have h1:(Finset.univ.filter fun w:Fin (2*m)=>¬(w ∈ s ↔ v ∈ s)).card=m:=by
    have htot:=Finset.card_filter_add_card_filter_not (s:=Finset.univ) (p:=fun w:Fin (2*m)=>(w ∈ s ↔ v ∈ s))
    simp only [Finset.card_univ,Fintype.card_fin,hsame_card] at htot;omega
   convert h1 using 2;ext w;simp only [Finset.mem_filter,Finset.mem_univ,true_and,and_iff_right_iff_imp]
   intro h hEq;subst hEq;exact h Iff.rfl
  have hsame_ne:(Finset.univ.filter fun w:Fin (2*m)=>w ≠ v/\(w ∈ s ↔ v ∈ s)).card+1=m:=by
   have hrew:Finset.univ.filter (fun w:Fin (2*m)=>(w ∈ s ↔ v ∈ s)) =
     insert v (Finset.univ.filter (fun w:Fin (2*m)=>w ≠ v/\(w ∈ s ↔ v ∈ s))):=by
    ext w;simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
    by_cases h:w=v
    . subst h;simp
    . simp [h]
   calc (Finset.univ.filter fun w:Fin (2*m)=>w ≠ v/\(w ∈ s ↔ v ∈ s)).card+1
     = (insert v (Finset.univ.filter fun w:Fin (2*m)=>w ≠ v/\(w ∈ s ↔ v ∈ s))).card :=
       (Finset.card_insert_of_notMem (by simp)).symm
    _ = (Finset.univ.filter fun w:Fin (2*m)=>(w ∈ s ↔ v ∈ s)).card:=by rw [← hrew]
    _ = m:=hsame_card
  rw [hopp_card]
  have hR:((Finset.univ.filter fun w:Fin (2*m)=>w ≠ v/\(w ∈ s ↔ v ∈ s)).card:R)+1=(m:R):=by
   exact_mod_cast hsame_ne
  linarith
 unfold Green91.friendliness
 push_cast
 linarith
lemma green91_even_strong {ε:R} (hε:0 < ε) :
  Tendsto (fun m:ℕ=>Green91.prob (2*m) fun G =>
   ∃ s:Finset (Fin (2*m)),s.card=m /\
    (2*m:R) - ε*(2*m:R) <=
     ((Finset.univ.filter fun v:Fin (2*m)=>2<=Green91.friendliness G s v).card:R))
   atTop (𝓝 1):=by
 have hrad:=radEdge_exists_nearly_friendly hε
 refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hrad tendsto_const_nhds ?_
  (Eventually.of_forall fun m=>by unfold Green91.prob;exact prob_le_one)
 filter_upwards [eventually_ge_atTop 10000] with m hm
 rw [← green91_prob_eq_radEdge]
 unfold Green91.prob
 refine measure_mono fun G hG=>?_
 obtain ⟨s,hs,hcard⟩:=hG
 refine ⟨s,(Finset.mem_filter.mp hs).2,hcard.trans ?_⟩
 have hsub:Finset.univ.filter (fun v:Fin (2*m)=>gC/2<=fv0 (2*m) (graphToSign G) s v) ⊆
   Finset.univ.filter (fun v:Fin (2*m)=>2<=Green91.friendliness G s v):=by
  intro v hv
  have hf:=(Finset.mem_filter.mp hv).2
  rw [fieldVal_graphToSign_eq_friendliness G hs v] at hf
  have hsn:(140:R)<=sqrt (2*m:R):=by
   rw [le_sqrt (by norm_num) (by positivity)]
   have:(20000:R)<=(2*m:R):=by exact_mod_cast (by omega:20000<=2*m)
   linarith
  have hsn_pos:0 < sqrt (2*m:R):=by linarith
  have hmul:(gC/2)*sqrt (2*m:R)<=2*(Green91.friendliness G s v:R)+1:=by
   have:=mlL hf hsn_pos.le
   rwa [mul_comm (sqrt (2*m:R)) (gC/2),← mul_assoc,mul_inv_cancel₀ hsn_pos.ne',one_mul] at this
  have hgt:(3:R) < 2*(Green91.friendliness G s v:R)+1:=by
   unfold gC at hmul;linarith
  have hint:(1:ℤ) < Green91.friendliness G s v:=by
   have:(2:R) < 2*(Green91.friendliness G s v:R):=by linarith
   have:(1:R) < (Green91.friendliness G s v:R):=by linarith
   exact_mod_cast this
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
 exact_mod_cast Finset.card_le_card hsub
def projGraph {m:ℕ} (G:SimpleGraph (Fin (2*m+1))):SimpleGraph (Fin (2*m)) :=
 G.comap Fin.castSucc
lemma green91_prob_projGraph (m:ℕ) (P:SimpleGraph (Fin (2*m))->Prop) :
  Green91.prob (2*m+1) (fun G=>P (projGraph G))=Green91.prob (2*m) P:=by
 classical
 rw [green91_prob_eq_card_mul',green91_prob_eq_card_mul']
 have hchoose:(2*m+1).choose 2=(2*m).choose 2+2*m:=by
  rw [Nat.choose_succ_succ,Nat.choose_one_right,add_comm]
 have hcard:(Finset.univ.filter fun G:SimpleGraph (Fin (2*m+1))=>P (projGraph G)).card =
   (Finset.univ.filter P).card*2^(2*m):=by
  have hbij:(Finset.univ.filter fun G:SimpleGraph (Fin (2*m+1))=>P (projGraph G)).card =
    ((Finset.univ.filter P) ×ˢ (Finset.univ:Finset (Fin (2*m)->Bool))).card:=by
   refine Finset.card_bij (fun G _=>(projGraph G,fun v:Fin (2*m)=>decide (G.Adj v.castSucc (Fin.last (2*m)))))
    (fun G hG=>Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hG).2⟩,Finset.mem_univ _⟩)
    (fun G1 _ G2 _ heq=>?_)
    (fun p hp=>?_)
   .
    have h1:projGraph G1=projGraph G2:=congrArg Prod.fst heq
    have h2:∀ v:Fin (2*m),G1.Adj v.castSucc (Fin.last (2*m)) ↔ G2.Adj v.castSucc (Fin.last (2*m)):=fun v=>by
     simpa using congrFun (congrArg Prod.snd heq) v
    ext u v
    cases u using Fin.lastCases with
    | last =>
     cases v using Fin.lastCases with
     | last=>simp [SimpleGraph.irrefl]
     | cast j=>rw [G1.adj_comm,G2.adj_comm];exact h2 j
    | cast i =>
     cases v using Fin.lastCases with
     | last=>exact h2 i
     | cast j =>
      have:=congrFun (congrFun (congrArg SimpleGraph.Adj h1) i) j
      simpa [projGraph] using this
   .
    obtain ⟨hP',_⟩:=Finset.mem_product.mp hp
    let G':=p.1
    let b:=p.2
    let G:SimpleGraph (Fin (2*m+1)) :=
     {
      Adj:=fun (u v:Fin (2*m+1)) =>
       if hu:u.1 < 2*m then
        if hv:v.1 < 2*m then G'.Adj ⟨u.1,hu⟩ ⟨v.1,hv⟩ else b ⟨u.1,hu⟩=true
       else
        if hv:v.1 < 2*m then b ⟨v.1,hv⟩=true else False
      symm:=⟨fun u v h=>by
       by_cases hu:u.1 < 2*m <;> by_cases hv:v.1 < 2*m <;> simp only [hu,hv,dite_true,dite_false] at h ⊢
       . exact G'.symm.symm _ _ h
       . exact h
       . exact h⟩
      loopless:=⟨fun u h=>by
       by_cases hu:u.1 < 2*m <;> simp only [hu,dite_true,dite_false] at h
       . exact G'.loopless.irrefl _ h⟩ }
    have hproj:projGraph G=G':=by
     ext i j;simp [projGraph,G,i.2,j.2]
    have hlast:(fun v:Fin (2*m)=>decide (G.Adj v.castSucc (Fin.last (2*m))))=b:=by
     ext v;simp [G,v.2]
    refine ⟨G,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hproj.symm ▸ (Finset.mem_filter.mp hP').2⟩,?_⟩
    exact Prod.ext hproj (by convert hlast)
  rw [hbij,Finset.card_product,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
 rw [hcard,hchoose,pow_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
 calc ((Finset.univ.filter P).card:ENNReal)*(2:ENNReal)^(2*m) *
    ((1/2:ENNReal)^(2*m).choose 2*(1/2:ENNReal)^(2*m))
   = ((Finset.univ.filter P).card:ENNReal)*(1/2:ENNReal)^(2*m).choose 2 *
    (((2:ENNReal)*(1/2:ENNReal))^(2*m)):=by rw [mul_pow];ring
  _ = ((Finset.univ.filter P).card:ENNReal)*(1/2:ENNReal)^(2*m).choose 2:=by
    rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num),one_pow,mul_one]
lemma friendliness_projGraph_diff {m:ℕ} (G:SimpleGraph (Fin (2*m+1)))
  (s:Finset (Fin (2*m))) (v:Fin (2*m)) :
  Green91.friendliness (projGraph G) s v - 1 <=
   Green91.friendliness G (s.map Fin.castSuccEmb) v.castSucc:=by
 classical
 set s':=s.map Fin.castSuccEmb
 have hmem:∀ w:Fin (2*m),w.castSucc ∈ s' ↔ w ∈ s:=fun w=>by
  simp [s',Fin.castSuccEmb_apply]
 have hsame:(Finset.univ.filter fun w:Fin (2*m)=>(projGraph G).Adj v w/\(w ∈ s ↔ v ∈ s)).card <=
   (Finset.univ.filter fun w:Fin (2*m+1)=>G.Adj v.castSucc w/\(w ∈ s' ↔ v.castSucc ∈ s')).card:=by
  have hmap:((Finset.univ.filter fun w:Fin (2*m)=>(projGraph G).Adj v w/\(w ∈ s ↔ v ∈ s)).map Fin.castSuccEmb) ⊆
    Finset.univ.filter (fun w:Fin (2*m+1)=>G.Adj v.castSucc w/\(w ∈ s' ↔ v.castSucc ∈ s')):=by
   intro x hx
   obtain ⟨w,hw,rfl⟩:=Finset.mem_map.mp hx
   obtain ⟨hadj,hiff⟩:=(Finset.mem_filter.mp hw).2
   exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj,by rw [Fin.castSuccEmb_apply,hmem w,hmem v];exact hiff⟩
  simpa using Finset.card_le_card hmap
 have hopp:(Finset.univ.filter fun w:Fin (2*m+1)=>G.Adj v.castSucc w/\¬(w ∈ s' ↔ v.castSucc ∈ s')).card <=
   (Finset.univ.filter fun w:Fin (2*m)=>(projGraph G).Adj v w/\¬(w ∈ s ↔ v ∈ s)).card+1:=by
  have hsub:Finset.univ.filter (fun w:Fin (2*m+1)=>G.Adj v.castSucc w/\¬(w ∈ s' ↔ v.castSucc ∈ s')) ⊆
    insert (Fin.last (2*m)) ((Finset.univ.filter fun w:Fin (2*m)=>(projGraph G).Adj v w/\¬(w ∈ s ↔ v ∈ s)).map Fin.castSuccEmb):=by
   intro x hx
   obtain ⟨hadj,hiff⟩:=(Finset.mem_filter.mp hx).2
   cases x using Fin.lastCases with
   | last=>exact Finset.mem_insert_self _ _
   | cast w =>
    refine Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj,?_⟩,rfl⟩)
    rwa [hmem w,hmem v] at hiff
  calc _ <= (insert (Fin.last (2*m)) ((Finset.univ.filter fun w:Fin (2*m)=>(projGraph G).Adj v w/\¬(w ∈ s ↔ v ∈ s)).map Fin.castSuccEmb)).card :=
     Finset.card_le_card hsub
   _ <= _ + 1:=by simpa using Finset.card_insert_le _ _
 unfold Green91.friendliness
 omega
lemma green91_odd_from_even {ε:R} (hε:0 < ε) :
  Tendsto (fun m:ℕ=>Green91.prob (2*m+1) fun G =>
   ∃ s:Finset (Fin (2*m+1)),s.card=m /\
    (2*m+1:R) - ε*(2*m+1:R)<=(Green91.numFriendly G s:R))
   atTop (𝓝 1):=by
 have hev:=green91_even_strong (show (0:R) < ε / 2 by linarith)
 refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hev tendsto_const_nhds ?_
  (Eventually.of_forall fun m=>by unfold Green91.prob;exact prob_le_one)
 have hbig:∀ᶠ m:ℕ in atTop,(2 / ε:R)<=(2*m:R) :=
  (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num:(0:R) < 2)).eventually (Ici_mem_atTop (2 / ε))
 filter_upwards [hbig] with m hm
 rw [← green91_prob_projGraph]
 unfold Green91.prob
 refine measure_mono fun G hG=>?_
 obtain ⟨s,hscard,hcnt⟩:=hG
 refine ⟨s.map Fin.castSuccEmb,by simpa using hscard,?_⟩
 have hnum:(Finset.univ.filter fun v:Fin (2*m)=>2<=Green91.friendliness (projGraph G) s v).card <=
   Green91.numFriendly G (s.map Fin.castSuccEmb):=by
  unfold Green91.numFriendly
  have hsub:((Finset.univ.filter fun v:Fin (2*m)=>2<=Green91.friendliness (projGraph G) s v).map Fin.castSuccEmb) ⊆
    Finset.univ.filter (fun v:Fin (2*m+1)=>0 < Green91.friendliness G (s.map Fin.castSuccEmb) v):=by
   intro x hx
   obtain ⟨v,hv,rfl⟩:=Finset.mem_map.mp hx
   have h2:=(Finset.mem_filter.mp hv).2
   have hdiff:=friendliness_projGraph_diff G s v
   exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [Fin.castSuccEmb_apply];omega⟩
  simpa using Finset.card_le_card hsub
 have hnumR:((Finset.univ.filter fun v:Fin (2*m)=>2<=Green91.friendliness (projGraph G) s v).card:R) <=
   (Green91.numFriendly G (s.map Fin.castSuccEmb):R):=by exact_mod_cast hnum
 have h1:(1:R)<=(ε / 2)*(2*m:R):=by
  have:=mlL hm (show (0:R)<=ε / 2 by linarith)
  rwa [show (ε / 2)*(2 / ε)=1 by field_simp [hε.ne']] at this
 linarith
end Green91FKNSS
theorem OMA.solution : OMA.R_Green91_green_91_variants_fknss_R1.H1 := by
 intro k
 set ε:R:=1/((k:R)+1)
 have hε:0 < ε:=by positivity
 have hev:=Green91FKNSS.green91_even_strong hε
 have hodd:=Green91FKNSS.green91_odd_from_even hε
 have hev':Tendsto (fun m:ℕ=>Green91.prob (2*m) fun G =>
   ∃ s:Finset (Fin (2*m)),s.card=(2*m)/2 /\
    ((2*m:ℕ):R) - ε*((2*m:ℕ):R)<=(Green91.numFriendly G s:R)) atTop (𝓝 1):=by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hev tendsto_const_nhds
   (Eventually.of_forall fun m=>?_) (Eventually.of_forall fun m=>by unfold Green91.prob;exact prob_le_one)
  unfold Green91.prob
  refine measure_mono fun G hG=>?_
  obtain ⟨s,hsc,hcnt⟩:=hG
  refine ⟨s,by omega,?_⟩
  have hle:(Finset.univ.filter fun v:Fin (2*m)=>2<=Green91.friendliness G s v).card <=
    Green91.numFriendly G s:=by
   unfold Green91.numFriendly
   exact Finset.card_le_card fun v hv=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,by have:=(Finset.mem_filter.mp hv).2;omega⟩
  have hleR:((Finset.univ.filter fun v:Fin (2*m)=>2<=Green91.friendliness G s v).card:R) <=
    (Green91.numFriendly G s:R):=by exact_mod_cast hle
  push_cast;linarith
 have hodd':Tendsto (fun m:ℕ=>Green91.prob (2*m+1) fun G =>
   ∃ s:Finset (Fin (2*m+1)),s.card=(2*m+1)/2 /\
    ((2*m+1:ℕ):R) - ε*((2*m+1:ℕ):R)<=(Green91.numFriendly G s:R)) atTop (𝓝 1):=by
  refine hodd.congr fun m=>?_
  congr 1;ext G;constructor <;> rintro ⟨s,hsc,hcnt⟩ <;> refine ⟨s,by omega,?_⟩ <;> (push_cast at hcnt ⊢;exact hcnt)
 rw [tendsto_atTop_nhds] at hev' hodd' ⊢
 intro U hU hUo
 obtain ⟨M1,hM1⟩:=hev' U hU hUo
 obtain ⟨M2,hM2⟩:=hodd' U hU hUo
 refine ⟨2*max M1 M2,fun n hn=>?_⟩
 rcases Nat.even_or_odd n with ⟨m,rfl⟩ | ⟨m,rfl⟩
 .
  have hm:M1<=m:=by omega
  rw [← two_mul]
  exact hM1 m hm
 .
  have hm:M2<=m:=by omega
  exact hM2 m hm
