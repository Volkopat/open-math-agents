import OMAStatements.S_mo_451543

namespace OMA.S_mo_451543
open Filter Finset
open scoped Topology

private lemma secant_aux (f : ℝ → ℝ) (g : FiniteGap f) (a b p t : ℝ) (hab : a≠b)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (ht : 0 ≤ t) :
    let q := 1-p
    let x := q*a+p*b
    let u := (a+t*q*x)/(1+t*q)
    let v := (b+t*p*x)/(1+t*p)
    0 ≤ (1+t*q)*(f a+f u)+(1+t*p)*(f b+f v)-2*(f a+f b+t*f x) := by
  let q := 1-p
  let x := q*a+p*b
  let u := (a+t*q*x)/(1+t*q)
  let v := (b+t*p*x)/(1+t*p)
  have hq : 0 ≤ q := sub_nonneg.mpr hp1
  have hu : u*(1+t*q)=a+t*q*x := div_mul_cancel₀ _ (by positivity)
  have hv : v*(1+t*p)=b+t*p*x := div_mul_cancel₀ _ (by positivity)
  let w : Fin 3 → Fin 2 → ℝ := ![![1,0],![0,1],![t*q,t*p]]
  let X : Fin 3 → ℝ := ![a,b,x]
  let Y : Fin 2 → ℝ := ![a,b]
  let Z : Fin 2 → ℝ := ![u,v]
  have hy : Function.Injective Y := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [Y]
  have hh := g 3 2 w X Y Z (fun i j => by fin_cases i <;> fin_cases j <;> simp [w] <;> positivity) hy
    (fun i => by fin_cases i <;> simp [X,Y,w,Fin.sum_univ_two,x,q]; ring)
    (fun j => by fin_cases j <;> simp [w,X,Z,Fin.sum_univ_three] <;> nlinarith only [hu,hv])
  simp [w,X,Y,Z,Fin.sum_univ_two,Fin.sum_univ_three] at hh
  change 0 ≤ (1+t*q)*(f a+f u)+(1+t*p)*(f b+f v)-2*(f a+f b+t*f x)
  dsimp [q] at hh ⊢
  linarith only [hh]

private lemma right_deriv_nn {F : ℝ→ℝ} {d : ℝ} (hd : HasDerivAt F d 0)
    (hm : ∀ᶠ t in 𝓝[>] (0:ℝ), F 0 ≤ F t) : 0 ≤ d := by
  apply ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
  filter_upwards [hm,self_mem_nhdsWithin] with t ht hp
  rw [slope_def_field,sub_zero]
  exact div_nonneg (sub_nonneg.mpr ht) (show 0<t from hp).le


private lemma deriv_mixed (f : ℝ→ℝ) (hf : Differentiable ℝ f) (a d x : ℝ) :
    HasDerivAt (fun t : ℝ => (1+t*d)*(f a+f ((a+t*d*x)/(1+t*d))))
      (2*d*f a + d*(x-a)*deriv f a) 0 := by
  have hden : HasDerivAt (fun t : ℝ => 1+t*d) d 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).mul_const d).const_add 1)
  have hnum : HasDerivAt (fun t : ℝ => a+t*d*x) (d*x) 0 := by
    simpa using ((((hasDerivAt_id (0:ℝ)).mul_const d).mul_const x).const_add a)
  have hr : HasDerivAt (fun t : ℝ => (a+t*d*x)/(1+t*d)) (d*(x-a)) 0 := by
    convert! hnum.div hden (by simp) using 1; simp; ring
  have H := hden.mul (((hf _).hasDerivAt.comp (0:ℝ) hr).const_add (f a))
  convert! H using 1; simp; ring

private noncomputable def G (f : ℝ→ℝ) (a b p : ℝ) :=
  2*((1-p)*f a+p*f b-f ((1-p)*a+p*b))+p*(1-p)*(b-a)*(deriv f a-deriv f b)

private lemma G_nn (f : ℝ→ℝ) (hf : Differentiable ℝ f) (hg : FiniteGap f) (a b p : ℝ)
    (hab : a≠b) (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ G f a b p := by
  let q := 1-p
  let x := q*a+p*b
  let F (t : ℝ) := (1+t*q)*(f a+f ((a+t*q*x)/(1+t*q))) +
    (1+t*p)*(f b+f ((b+t*p*x)/(1+t*p)))-2*(f a+f b+t*f x)
  have hlast : HasDerivAt (fun t : ℝ => 2*(f a+f b+t*f x)) (2*f x) 0 := by
    simpa using ((((hasDerivAt_id (0:ℝ)).mul_const (f x)).const_add (f a+f b)).const_mul 2)
  have hF : HasDerivAt F (G f a b p) 0 := by
    convert! ((deriv_mixed f hf a q x).add (deriv_mixed f hf b p x)).sub hlast using 1
    dsimp [G,q,x]; ring
  apply right_deriv_nn hF
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hzero : F 0 = 0 := by simp [F]; ring
  rw [hzero]
  exact secant_aux f hg a b p t hab hp hp1 (show 0<t from ht).le

private lemma G_deriv (f : ℝ→ℝ) (hf : Differentiable ℝ f) (a b p : ℝ) :
    HasDerivAt (G f a b)
      (2*(f b-f a-(b-a)*deriv f ((1-p)*a+p*b))+(1-2*p)*(b-a)*(deriv f a-deriv f b)) p := by
  have hr := hasDerivAt_id p
  have hs := hr.const_sub 1
  have hx := (hs.mul_const a).add (hr.mul_const b)
  have hm := (hf _).hasDerivAt.comp p hx
  have H := ((((hs.mul_const (f a)).add (hr.mul_const (f b))).sub hm).const_mul 2).add
    (((hr.mul hs).mul_const (b-a)).mul_const (deriv f a-deriv f b))
  convert! H using 1; simp; ring

private lemma trapezoid (f : ℝ→ℝ) (hf : Differentiable ℝ f) (hg : FiniteGap f) (a b : ℝ) :
    2*(f b-f a)=(b-a)*(deriv f a+deriv f b) := by
  by_cases hab : a=b
  · simp [hab]
  let d := 2*(f b-f a)-(b-a)*(deriv f a+deriv f b)
  have hd0 : HasDerivAt (G f a b) d 0 := by
    convert! G_deriv f hf a b 0 using 1
    simp [d]; ring
  have hd1 : HasDerivAt (G f a b) d 1 := by
    convert! G_deriv f hf a b 1 using 1
    simp [d]; ring
  have hn : 0 ≤ d := by
    apply right_deriv_nn hd0
    filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t h0 h1
    simpa [G] using G_nn f hf hg a b t hab (show 0<t from h0).le h1.le
  have hp : d ≤ 0 := by
    apply le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hd1).1
    filter_upwards [self_mem_nhdsWithin,(lt_mem_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t h1 h0
    have hG := G_nn f hf hg a b t hab h0.le (show t<1 from h1).le
    have hzero : G f a b 1=0 := by simp [G]
    rw [slope_def_field,hzero,sub_zero]
    exact div_nonpos_of_nonneg_of_nonpos hG (by linarith [show t<1 from h1])
  dsimp [d] at hn hp
  linarith

private lemma smooth_shape (f : ℝ→ℝ) (hf : Differentiable ℝ f) (hg : FiniteGap f) :
    ∃ a b c : ℝ, ∀ x, f x=quadratic a b c x := by
  refine ⟨(deriv f 1-deriv f 0)/2,deriv f 0,f 0,fun x => ?_⟩
  have h1 := trapezoid f hf hg 0 1
  have hx := trapezoid f hf hg 0 x
  have hx' := trapezoid f hf hg x 1
  have hd : deriv f x=(1-x)*deriv f 0+x*deriv f 1 := by linarith only [h1,hx,hx']
  rw [hd] at hx
  unfold quadratic
  linarith only [hx]

end OMA.S_mo_451543
namespace OMA.S_mo_451543
open MeasureTheory Set Filter Finset
open scoped Topology

private lemma smear_gap (f : ℝ→ℝ) (hf : Continuous f) (hg : FiniteGap f) (r : ℝ) (hr : 0 ≤ r) :
    FiniteGap (fun x => ∫ t in (0:ℝ)..r, f (x+t)) := by
  intro n m w x y z hw hy hm hc
  have hiy (t : ℝ) : Function.Injective (fun i => y i+t) := fun i j h => hy (add_right_cancel h)
  have hfun (t : ℝ) : 0 ≤ ∑ i,∑ j,w i j*(f (y j+t)+f (z j+t)-2*f (x i+t)) :=
    hg n m w (fun i => x i+t) (fun j => y j+t) (fun j => z j+t) hw (hiy t)
      (fun i => by simpa using hm i) (fun j => by simpa using hc j)
  have he := intervalIntegral.integral_nonneg_of_forall (μ:=volume) hr hfun
  have hi (c : ℝ) : IntervalIntegrable (fun t => f (c+t)) volume 0 r :=
    (hf.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (fun i _ => (show Continuous (fun t : ℝ =>
    ∑ j, w i j*(f (y j+t)+f (z j+t)-2*f (x i+t))) by fun_prop).intervalIntegrable _ _)] at he
  convert! he using 1
  apply sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum (fun j _ => (show Continuous (fun t : ℝ =>
    w i j*(f (y j+t)+f (z j+t)-2*f (x i+t))) by fun_prop).intervalIntegrable _ _)]
  apply sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub ((hi _).add (hi _)) ((hi _).const_mul _),
    intervalIntegral.integral_add (hi _) (hi _),intervalIntegral.integral_const_mul]

private lemma continuous_shape (f : ℝ→ℝ) (hf : Continuous f) (hg : FiniteGap f) :
    ∃ a b c : ℝ, ∀ x, f x=quadratic a b c x := by
  let P (x : ℝ) := ∫ t in (0:ℝ)..x, f t
  let H (r x : ℝ) := P (x+r)-P x
  have hp (x : ℝ) : HasDerivAt P (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hcomp (r x : ℝ) : H r x = ∫ t in (0:ℝ)..r, f (x+t) := by
    rw [intervalIntegral.integral_comp_add_left]
    simpa [H,P] using intervalIntegral.integral_interval_sub_left (μ:=volume) (hf.intervalIntegrable 0 (x+r)) (hf.intervalIntegrable 0 x)
  have hshape (r : ℝ) (hr : 0 ≤ r) : ∃ a b c : ℝ, ∀ x, H r x=quadratic a b c x := by
    apply smooth_shape
    · intro x
      exact ((show HasDerivAt (fun y => P (y+r)) (f (x+r)) x by simpa [Function.comp_def] using (hp (x+r)).comp x ((hasDerivAt_id x).add_const r)).sub (hp x)).differentiableAt
    · simpa only [funext (hcomp r)] using smear_gap f hf hg r hr
  have hn (x : ℝ) : HasDerivAt (fun r => H r x) (f x) 0 := by
    simpa [H,Function.comp_def] using (((hp (x+0)).comp (0:ℝ) ((hasDerivAt_id 0).const_add x)).sub_const (P x))
  let A (x : ℝ) := (x^2-x)/2
  let B (x : ℝ) := 1-x^2
  let C (x : ℝ) := (x^2+x)/2
  have hkey (x : ℝ) : f x = A x * f (-1) + B x * f 0 + C x * f 1 := by
    let W (r : ℝ) := H r x - (A x*H r (-1)+B x*H r 0+C x*H r 1)
    have hw (r : ℝ) (hr : 0 ≤ r) : W r=0 := by
      obtain ⟨a,b,c,hh⟩ := hshape r hr
      simp only [W,hh,quadratic,A,B,C]
      ring
    have hd : HasDerivAt W (f x-(A x*f (-1)+B x*f 0+C x*f 1)) 0 :=
      (hn x).sub ((((hn (-1)).const_mul _).add ((hn 0).const_mul _)).add ((hn 1).const_mul _))
    have hh : ∀ᶠ r in 𝓝[>] (0:ℝ), W 0 ≤ W r ∧ -W 0 ≤ -W r := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [hw 0 (by norm_num),hw r (show 0<r from hr).le]
      exact ⟨le_rfl,le_rfl⟩
    have h₁ := right_deriv_nn hd (hh.mono fun r h => h.1)
    have h₂ := right_deriv_nn hd.neg (hh.mono fun r h => h.2)
    linarith
  refine ⟨(f (-1)+f 1)/2-f 0,(f 1-f (-1))/2,f 0,fun x => ?_⟩
  calc
    _ = _ := hkey x
    _ = _ := by dsimp [A,B,C,quadratic]; ring
end OMA.S_mo_451543
namespace OMA.S_mo_451543
open Finset

private lemma quad_suff (a b c : ℝ) (ha : 0 ≤ a) : FiniteGap (quadratic a b c) := by
  intro n m w x y z hw _ hm hc
  have H (i j) :
      w i j * (quadratic a b c (y j)+quadratic a b c (z j)-2*quadratic a b c (x i)) =
      w i j*(a*(y j-z j)^2)+(2*a*x i+b)*(w i j*(y j-x i))-(2*a*y j+b)*(w i j*(x i-z j)) := by
    unfold quadratic; ring
  simp_rw [H, sum_sub_distrib, sum_add_distrib]
  have hrow : (∑ i,∑ j,(2*a*x i+b)*(w i j*(y j-x i)))=0 := by
    simp only [← mul_sum,hm,mul_zero,sum_const_zero]
  have hcol : (∑ i,∑ j,(2*a*y j+b)*(w i j*(x i-z j)))=0 := by
    rw [sum_comm]
    simp only [← mul_sum,hc,mul_zero,sum_const_zero]
  rw [hrow,hcol,add_zero,sub_zero]
  exact sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (hw i j) (mul_nonneg ha (sq_nonneg _))

private lemma coeff_nn (a b c : ℝ) (hg : FiniteGap (quadratic a b c)) : 0 ≤ a := by
  let y : Fin 2→ℝ := ![-1,1]
  have hy : Function.Injective y := by intro i j h; fin_cases i <;> fin_cases j <;> norm_num [y] at *
  have h := hg 1 2 (fun _ _ => 1) (fun _ => 0) y (fun _ => 0) (by intros; norm_num) hy
    (by intro i; norm_num [y,Fin.sum_univ_two]) (by intro j; norm_num)
  norm_num [y,quadratic,Fin.sum_univ_two,Fin.sum_univ_one] at h
  linarith

private lemma shift_power_convex (n : ℕ) (hn : Even n) (z : ℝ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => (x-z)^n) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  have h := (hn.convexOn_pow (𝕜:=ℝ)).2 (Set.mem_univ (x-z)) (Set.mem_univ (y-z)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  rwa [show a*x+b*y-z=a*(x-z)+b*(y-z) by linear_combination z*hab]

private lemma bad :
    let f := fun x : ℝ => (x-3/8)^4
    ConvexOn ℝ Set.univ f ∧ ConvexOn ℝ Set.univ (deriv (deriv f)) ∧ ¬FiniteGap f := by
  let z : ℝ := 3/8
  let f := fun x : ℝ => (x-z)^4
  have d1 : deriv f = fun x => 4*(x-z)^3 := by
    funext x; convert! (((hasDerivAt_id x).sub_const z).pow 4).deriv using 1; norm_num
  have d2 : deriv (deriv f) = fun x => 12*(x-z)^2 := by
    rw [d1]
    funext x; convert! (((((hasDerivAt_id x).sub_const z).pow 3).const_mul 4)).deriv using 1; norm_num; ring
  refine ⟨shift_power_convex _ (by decide) _,?_,?_⟩
  · change ConvexOn ℝ Set.univ (deriv (deriv f))
    rw [d2]
    exact (shift_power_convex 2 (by decide) z).smul (show (0:ℝ) ≤ 12 by norm_num)
  · intro hg
    let X : Fin 2→ℝ := ![1,1/2]
    let Y : Fin 2→ℝ := ![0,1]
    let Z : Fin 2→ℝ := ![1/2,5/6]
    let w : Fin 2→Fin 2→ℝ := ![![0,2],![1,1]]
    have hy : Function.Injective Y := by intro i j h; fin_cases i <;> fin_cases j <;> norm_num [Y] at *
    have H := hg 2 2 w X Y Z (by intro i j; fin_cases i <;> fin_cases j <;> norm_num [w]) hy
      (by intro i; fin_cases i <;> norm_num [Fin.sum_univ_two,w,X,Y])
      (by intro j; fin_cases j <;> norm_num [Fin.sum_univ_two,w,X,Z])
    norm_num [Fin.sum_univ_two,w,X,Y,Z] at H

end OMA.S_mo_451543
namespace OMA.S_mo_451543
open MeasureTheory

private lemma law_gap {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (a b c : ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P)
    (h : P[Y | MeasurableSpace.comap X (borel ℝ)] =ᵐ[P] X) :
    let Z := P[X | MeasurableSpace.comap Y (borel ℝ)]
    (∫ ω, (quadratic a b c (Y ω)+quadratic a b c (Z ω)-2*quadratic a b c (X ω)) ∂P)
      = a * ∫ ω, (Y ω-Z ω)^2 ∂P := by
  let mX := MeasurableSpace.comap X (borel ℝ)
  let mY := MeasurableSpace.comap Y (borel ℝ)
  let Z := P[X|mY]
  have hmX : mX ≤ mΩ := hX.comap_le
  have hmY : mY ≤ mΩ := hY.comap_le
  have hx : Integrable X P := hX2.integrable (by norm_num)
  have hy : Integrable Y P := hY2.integrable (by norm_num)
  have hz : Integrable Z P := integrable_condExp
  have hZ2 : MemLp Z 2 P := hX2.condExp (by norm_num)
  have hxm : AEStronglyMeasurable[mX] X P := (Measurable.of_comap_le le_rfl).stronglyMeasurable.aestronglyMeasurable
  have hym : AEStronglyMeasurable[mY] Y P := (Measurable.of_comap_le le_rfl).stronglyMeasurable.aestronglyMeasurable
  have hxy : ∫ ω, X ω * Y ω ∂P = ∫ ω, X ω * X ω ∂P := calc
    _ = ∫ ω, P[X*Y|mX] ω ∂P := (integral_condExp (f:=X*Y) (μ:=P) hmX).symm
    _ = _ := integral_congr_ae ((condExp_mul_of_aestronglyMeasurable_left hxm (hX2.integrable_mul hY2) hy).trans
      (Filter.EventuallyEq.mul (Filter.EventuallyEq.rfl (f:=X)) h))
  have hzy : ∫ ω, Z ω * Y ω ∂P = ∫ ω, X ω * Y ω ∂P := calc
    _ = ∫ ω, P[X*Y|mY] ω ∂P := integral_congr_ae (condExp_mul_of_aestronglyMeasurable_right hym
      (hX2.integrable_mul hY2) hx).symm
    _ = _ := integral_condExp hmY
  have heY : ∫ ω,Y ω ∂P = ∫ ω,X ω ∂P := ((integral_condExp (f:=Y) (μ:=P) hmX).symm).trans (integral_congr_ae h)
  have heZ : ∫ ω,Z ω ∂P = ∫ ω,X ω ∂P := integral_condExp hmY
  have quad_int (W : Ω → ℝ) (hW : MemLp W 2 P) : Integrable (fun ω => quadratic a b c (W ω)) P := by
    simpa only [quadratic,sq,Pi.add_apply,Pi.mul_apply] using (((hW.integrable_mul hW).const_mul a).fun_add
      ((hW.integrable (by norm_num)).const_mul b)).fun_add (integrable_const c)
  have quad_ev (W : Ω → ℝ) (hW : MemLp W 2 P) :
      (∫ ω,quadratic a b c (W ω) ∂P) = a*(∫ ω,W ω*W ω ∂P)+b*(∫ ω,W ω ∂P)+c := by
    simp only [quadratic,sq]
    rw [integral_add (f:=fun ω => a*(W ω*W ω)+b*W ω) (g:=fun _ => c) (((hW.integrable_mul hW).const_mul a).add
      ((hW.integrable (by norm_num)).const_mul b)) (integrable_const c),
      integral_add (f:=fun ω => a*(W ω*W ω)) (g:=fun ω => b*W ω) ((hW.integrable_mul hW).const_mul a) ((hW.integrable (by norm_num)).const_mul b)]
    simp [integral_const_mul]
  have sqgap : (∫ ω, (Y ω-Z ω)^2 ∂P) =
      (∫ ω,Y ω*Y ω ∂P) + (∫ ω,Z ω*Z ω ∂P) - 2*(∫ ω,Z ω*Y ω ∂P) := by
    have he (ω : Ω) : (Y ω-Z ω)^2 = Y ω*Y ω+Z ω*Z ω-2*(Z ω*Y ω) := by ring
    simp_rw [he]
    rw [integral_sub (f:=fun ω => Y ω*Y ω+Z ω*Z ω) (g:=fun ω=>2*(Z ω*Y ω)) ((hY2.integrable_mul hY2).add (hZ2.integrable_mul hZ2))
        ((hZ2.integrable_mul hY2).const_mul 2),
      integral_add (f:=fun ω=>Y ω*Y ω) (g:=fun ω => Z ω*Z ω) (hY2.integrable_mul hY2) (hZ2.integrable_mul hZ2),integral_const_mul]
  change (∫ ω, quadratic a b c (Y ω)+quadratic a b c (Z ω)-2*quadratic a b c (X ω) ∂P)=_
  rw [integral_sub (f:=fun ω => quadratic a b c (Y ω)+quadratic a b c (Z ω)) (g:=fun ω => 2*quadratic a b c (X ω)) ((quad_int Y hY2).add (quad_int Z hZ2)) ((quad_int X hX2).const_mul 2),
    integral_add (f:=fun ω=>quadratic a b c (Y ω)) (g:=fun ω=>quadratic a b c (Z ω)) (quad_int Y hY2) (quad_int Z hZ2),integral_const_mul,quad_ev X hX2,quad_ev Y hY2,
    quad_ev Z hZ2,sqgap,heY,heZ,hzy,hxy]
  ring

end OMA.S_mo_451543
theorem OMA.solution : type_of% @OMA.S_mo_451543.main := by
  refine ⟨?_,OMA.S_mo_451543.bad,@OMA.S_mo_451543.law_gap⟩
  intro f hf
  constructor
  · intro hg
    obtain ⟨a,b,c,he⟩ := OMA.S_mo_451543.continuous_shape f hf hg
    exact ⟨a,b,c,OMA.S_mo_451543.coeff_nn a b c (funext he ▸ hg),he⟩
  · rintro ⟨a,b,c,ha,he⟩
    rw [funext he]
    exact OMA.S_mo_451543.quad_suff a b c ha
