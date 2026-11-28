import OMAStatements.S_mo_188611

namespace OMA.S_mo_188611
open Matrix Finset MeasureTheory Set Filter Polynomial
private noncomputable def arc (h t : ℝ) : ℂ := Complex.exp ((h*t:ℝ)*Complex.I)
private noncomputable def wave {n : ℕ} (w : Fin n→ℝ) (h t : ℝ) : ℂ :=
  ∑ i,(w i:ℂ)*arc h t ^ i.val

private lemma cont_wave {n : ℕ} (w : Fin n→ℝ) (h : ℝ) : Continuous (wave w h) := by
  unfold wave arc
  fun_prop

private lemma sinc_int (r : ℝ) :
    (∫ t in (0:ℝ)..1, Real.cos (r*t)) = Real.sinc r := by
  by_cases hr : r=0
  · simp [hr]
  rw [Real.sinc_of_ne_zero hr]
  rw [intervalIntegral.integral_comp_mul_left Real.cos hr,integral_cos]
  simp [div_eq_inv_mul]


private lemma arc_pair (h t : ℝ) (i j : ℕ) :
    (arc h t ^ i * star (arc h t ^ j)).re = Real.cos ((h*((i:ℝ)-j))*t) := by
  have he (k : ℕ) : arc h t^k=Complex.exp (((k:ℝ)*(h*t):ℝ)*Complex.I) := by
    rw [arc,←Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [he,he]
  change (Complex.exp _ * (starRingEnd ℂ) (Complex.exp _)).re=_
  rw [← Complex.exp_conj,←Complex.exp_add]
  push_cast
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,map_natCast]
  rw [show (i:ℂ)*(h*t)*Complex.I+(j:ℂ)*(h*t)* -Complex.I =
    (((h*((i:ℝ)-j))*t:ℝ):ℂ)*Complex.I by push_cast; ring,Complex.exp_ofReal_mul_I_re]

private lemma energy_gram {n : ℕ} (T : ℝ) (w : Fin n→ℝ) :
    w ⬝ᵥ (covariance T n *ᵥ w) = ∫ t in (0:ℝ)..1, ‖wave w (T/n) t‖^2 := by
  let h := T/(n:ℝ)
  have he (t : ℝ) : ‖wave w h t‖^2 =
      ∑ i, ∑ j, (w i*w j)*Real.cos ((h*((i.val:ℝ)-j.val))*t) := by
    have em : wave w h t * star (wave w h t) =
        ∑ i, ∑ j, ((w i*w j:ℝ):ℂ)*(arc h t^i.val*star (arc h t^j.val)) := by
      simp only [wave,star_sum,star_mul',Complex.star_def,Complex.conj_ofReal,
        Finset.sum_mul,Finset.mul_sum,Complex.ofReal_mul]
      conv_lhs => rw [Finset.sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    have hy := congrArg Complex.re em
    rw [show wave w h t * star (wave w h t) = ((‖wave w h t‖^2:ℝ):ℂ) by exact_mod_cast Complex.mul_conj' _] at hy
    simpa only [Complex.ofReal_re,Complex.re_sum,Complex.re_ofReal_mul,arc_pair] using hy
  change _ = ∫ t in (0:ℝ)..1, ‖wave w h t‖^2
  simp_rw [he]
  have hI (i j : Fin n) : IntervalIntegrable
      (fun t : ℝ => (w i*w j)*Real.cos ((h*((i.val:ℝ)-j.val))*t)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_finsetSum (f:=fun (i : Fin n) (t : ℝ) =>
      ∑ j, (w i*w j)*Real.cos ((h*((i.val:ℝ)-j.val))*t)) (fun i _ => by
        apply Continuous.intervalIntegrable; fun_prop)]
  simp only [intervalIntegral.integral_finsetSum (f:=fun (j : Fin n) (t : ℝ) => (w _*w j)*Real.cos ((h*((_:Fin n).val-j.val))*t)) (fun j _ => hI _ j),
    intervalIntegral.integral_const_mul,sinc_int]
  simp only [dotProduct,mulVec,Finset.mul_sum,covariance,h]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring
end OMA.S_mo_188611
namespace OMA.S_mo_188611
open Matrix Finset MeasureTheory Set Filter Polynomial
private lemma arc_inj {h : ℝ} (h0 : 0<h) (h1 : h≤1) : InjOn (arc h) (Icc 0 1) := by
  intro x hx y hy hxy
  have ha (r : ℝ) (hr : r∈Icc (0:ℝ) 1) :
      -Real.pi < (↑(h*r) * Complex.I).im ∧ (↑(h*r) * Complex.I).im ≤ Real.pi := by
    simp
    exact ⟨by nlinarith [mul_nonneg h0.le hr.1,Real.pi_pos],by
      nlinarith [mul_le_mul h1 hr.2 hr.1 (by norm_num : (0:ℝ)≤1), Real.pi_gt_three]⟩
  have e := Complex.exp_inj_of_neg_pi_lt_of_le_pi (ha x hx).1 (ha x hx).2 (ha y hy).1 (ha y hy).2 hxy
  have q := congrArg Complex.im e
  simpa [h0.ne'] using q

private lemma definite {n : ℕ} {T : ℝ} (hT : 0<T) (h1 : T<1) (hn : 0<n) :
    (covariance T n).PosDef := by
  let h := T/(n:ℝ)
  have h0 : 0<h := div_pos hT (by exact_mod_cast hn)
  have hh : h≤1 := (div_le_iff₀ (by exact_mod_cast hn : (0:ℝ)<n)).mpr (by
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    linarith)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    change Real.sinc (h*((j.val:ℝ)-i.val)) = Real.sinc (h*((i.val:ℝ)-j.val))
    rw [show h*((j.val:ℝ)-i.val) = -(h*((i.val:ℝ)-j.val)) by ring, Real.sinc_neg]
  intro w hw
  rw [star_trivial,energy_gram]
  change 0 < ∫ t in (0:ℝ)..1, ‖wave w h t‖^2
  let p : ℂ[X] := ∑ i,monomial i.val (w i:ℂ)
  have hep (t : ℝ) : p.eval (arc h t) = wave w h t := by
    simp [p,eval_finsetSum,wave]
  have hpn : p≠0 := by
    intro hp
    apply hw
    funext i
    have he := congrArg (fun q : ℂ[X] => q.coeff i.val) hp
    simp only [p,finsetSum_coeff,coeff_monomial,Fin.val_inj,Finset.sum_ite_eq',
      Finset.mem_univ,if_true,coeff_zero] at he
    change w i=0
    exact_mod_cast he
  have ha : ∃ x ∈ Icc (0:ℝ) 1,wave w h x≠0 := by
    by_contra! hz
    apply hpn
    apply p.eq_zero_of_infinite_isRoot
    apply ((Icc_infinite (by norm_num : (0:ℝ)<1)).image (arc_inj h0 hh)).mono
    rintro _ ⟨t,ht,rfl⟩
    exact (hep t).trans (hz t ht)
  simpa using intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f:=fun _ => (0:ℝ)) (g:=fun t => ‖wave w h t‖^2) (by norm_num : (0:ℝ)<1)
    continuousOn_const ((cont_wave w h).norm.pow 2).continuousOn
    (fun t _ => sq_nonneg _) (ha.imp fun t ht => ⟨ht.1,sq_pos_of_pos (norm_pos_iff.mpr ht.2)⟩)
end OMA.S_mo_188611
namespace OMA.S_mo_188611
open Matrix Finset MeasureTheory Set Filter Polynomial
private noncomputable def bump (h : ℝ) : ℝ[X] :=
  C ((2-2*Real.cos h)⁻¹) * (X^2 - C (2*Real.cos h)*X + 1)

private lemma bump_deg (h : ℝ) (m : ℕ) : ((bump h)^m).natDegree ≤ m*2 := by
  apply Polynomial.natDegree_pow_le.trans
  apply Nat.mul_le_mul_left
  apply (natDegree_C_mul_le _ _).trans
  apply (natDegree_add_le _ _).trans
  apply max_le _ (by simp)
  apply (natDegree_sub_le _ _).trans
  exact max_le (by simp) ((natDegree_C_mul_le ..).trans (by simp))

private lemma cos_gap {h : ℝ} (h0 : 0<h) (h1 : h≤1) : 0<1-Real.cos h := by
  have h := Real.strictAntiOn_cos (show (0:ℝ)∈Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩)
    (show h∈Icc 0 Real.pi from ⟨h0.le,by linarith [Real.pi_gt_three]⟩) h0
  simpa using sub_pos.mpr h

private lemma bump_eval_one {h : ℝ} (h0 : 0<h) (h1 : h≤1) : (bump h).eval 1=1 := by
  have hd : 2-2*Real.cos h≠0 := by linarith [cos_gap h0 h1]
  simp only [bump,eval_mul,eval_C,eval_add,eval_sub,eval_pow,eval_X,one_pow,mul_one,eval_one]
  rw [show 1-2*Real.cos h+1=2-2*Real.cos h by ring,inv_mul_cancel₀ hd]

private lemma bump_mod {h t : ℝ} (h0 : 0<h) (h1 : h≤1) (ht : t∈Icc (0:ℝ) 1) :
    ‖(bump h).aeval (arc h t)‖ ≤ 1-t^2 := by
  let z := arc h t
  let u := (Real.cos (h*t)-Real.cos h)/(1-Real.cos h)
  have hgap := cos_gap h0 h1
  have ht' : h*t∈Icc 0 Real.pi := ⟨mul_nonneg h0.le ht.1,by
    nlinarith [mul_le_mul_of_nonneg_left ht.2 h0.le, Real.pi_gt_three]⟩
  have hu : 0≤u := div_nonneg (sub_nonneg.mpr (Real.antitoneOn_cos ht'
    ⟨h0.le,by linarith [Real.pi_gt_three]⟩ (by nlinarith [mul_le_mul_of_nonneg_left ht.2 h0.le]))) hgap.le
  have hcos (s : ℝ) : Real.cos s=1-2*Real.sin (s/2)^2 := by
    convert Real.cos_two_mul_eq_one_sub (s/2) using 2; ring
  have hs : t*Real.sin (h/2) ≤ Real.sin (h*t/2) := by
    have hconc := strictConcaveOn_sin_Icc.concaveOn.2 (show (0:ℝ)∈Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩)
      (show h/2∈Icc 0 Real.pi from ⟨by positivity,by linarith [Real.pi_gt_three]⟩)
      (sub_nonneg.mpr ht.2) ht.1 (show 1-t+t=1 by ring)
    simpa [smul_eq_mul,show t*(h/2)=h*t/2 by ring] using hconc
  have hpos : 0≤t*Real.sin (h/2) := mul_nonneg ht.1 (Real.sin_nonneg_of_nonneg_of_le_pi
    (by positivity) (by linarith [Real.pi_gt_three]))
  have hs2 := (sq_le_sq₀ hpos (hpos.trans hs)).mpr hs
  have hle : u ≤ 1-t^2 := by
    apply (div_le_iff₀ hgap).mpr
    rw [hcos (h*t),hcos h]
    nlinarith only [hs2]
  have zn : ‖z‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hz : z^2+1=2*(Real.cos (h*t):ℂ)*z := by
    have hz' : z+star z=2*(Real.cos (h*t):ℂ) := by
      change z+(starRingEnd ℂ) z=_
      rw [Complex.add_conj]
      rw [show z.re=Real.cos (h*t) from Complex.exp_ofReal_mul_I_re _]
      push_cast
      ring
    have hzz : z*star z=1 := by rw [show z*star z=(‖z‖:ℂ)^2 from Complex.mul_conj' _,zn];norm_num
    rw [←hz']
    linear_combination -hzz
  have he : (bump h).aeval z = ↑u*z := by
    simp only [bump,map_mul,map_add,map_sub,map_pow,aeval_X,aeval_C,map_one]
    change (↑((2-2*Real.cos h)⁻¹):ℂ)*(z^2-2*(Real.cos h:ℂ)*z+1)=↑u*z
    rw [show z^2-2*(Real.cos h:ℂ)*z+1=(z^2+1)-2*(Real.cos h:ℂ)*z by ring,hz]
    simp only [u,Complex.ofReal_inv,Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_mul,
      Complex.ofReal_one,Complex.ofReal_ofNat]
    have hd' : (1:ℂ)-(Real.cos h:ℂ)≠0 := by exact_mod_cast hgap.ne'
    rw [show (2:ℂ)-2*(Real.cos h:ℂ)=2*(1-(Real.cos h:ℂ)) by ring]
    field_simp
  change ‖(bump h).aeval z‖ ≤ _
  rw [he,norm_mul,zn,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
  exact hle
end OMA.S_mo_188611
namespace OMA.S_mo_188611
open Matrix Finset MeasureTheory Set Filter Polynomial
open scoped Topology Interval
private noncomputable def integralCap (m : ℕ) : ℝ :=
  ∫ t in (0:ℝ)..1, (1-t^2)^m

private lemma integralCap_zero : Tendsto integralCap atTop (𝓝 0) := by
  have ha (t : ℝ) (ht : t∈Ι (0:ℝ) 1) : 0≤1-t^2 ∧ 1-t^2<1 := by
    rw [uIoc_of_le zero_le_one] at ht
    exact ⟨by nlinarith [(sq_le_one_iff_abs_le_one t).mpr (by rw [abs_of_pos ht.1]; exact ht.2)],
      by nlinarith [sq_pos_of_pos ht.1]⟩
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ:=volume) (a:=0) (b:=1) (l:=atTop) (F:=fun m : ℕ => fun t : ℝ => (1-t^2)^m)
    (f:=fun _ => (0:ℝ)) (fun _ => (1:ℝ))
    (.of_forall (fun n => (by fun_prop : Continuous (fun t : ℝ => (1-t^2)^n)).aestronglyMeasurable))
    (.of_forall (fun m => .of_forall (fun t ht => by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (ha t ht).1 _)]
      exact pow_le_one₀ (ha t ht).1 (ha t ht).2.le)))
    intervalIntegrable_const
    (.of_forall (fun t ht => tendsto_pow_atTop_nhds_zero_of_lt_one (ha t ht).1 (ha t ht).2))
  change Tendsto (fun m : ℕ => ∫ t in (0:ℝ)..1, (1-t^2)^m) atTop (𝓝 0)
  simpa only [intervalIntegral.integral_zero] using h

private lemma small_test {n m : ℕ} {T : ℝ} (hT : 0<T) (h1 : T<1) (hn : 2*m<n) :
    ∃ w : Fin n→ℝ, (∑ i,w i)=1 ∧ w ⬝ᵥ (covariance T n *ᵥ w) ≤ integralCap m := by
  let h := T/(n:ℝ)
  have h0 : 0<h := div_pos hT (by exact_mod_cast (show 0<n by omega))
  have hh : h≤1 := (div_le_iff₀ (by exact_mod_cast (show 0<n by omega) : (0:ℝ)<n)).mpr (by
    have : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
    linarith)
  let p := (bump h)^m
  have hp : p.natDegree<n := (bump_deg _ _).trans_lt (by omega)
  let w (i : Fin n) := p.coeff i.val
  have he : p.eval 1=1 := by rw [show p=(bump h)^m from rfl,eval_pow,bump_eval_one h0 hh,one_pow]
  refine ⟨w,?_,?_⟩
  · rw [eval_eq_sum_range' hp] at he
    simpa [w,Fin.sum_univ_eq_sum_range] using he
  · have hv (t : ℝ) : wave w h t = ((bump h).aeval (arc h t))^m := by
      rw [← map_pow]
      change _ = (aeval (arc h t)) p
      rw [aeval_eq_sum_range' hp]
      simp [wave,w,Algebra.smul_def]
      rw [← Fin.sum_univ_eq_sum_range]
    rw [energy_gram]
    apply intervalIntegral.integral_mono_on zero_le_one ((cont_wave w h).norm.pow 2 |>.intervalIntegrable _ _)
      (by apply Continuous.intervalIntegrable; fun_prop)
    intro t ht
    change ‖wave w h t‖^2 ≤ (1-t^2)^m
    rw [hv,norm_pow,←pow_mul, mul_comm m 2,pow_mul]
    apply pow_le_pow_left₀ (sq_nonneg _) _
    have hb := bump_mod h0 hh ht
    have hp := norm_nonneg ((bump h).aeval (arc h t))
    nlinarith [mul_nonneg hp (show 0 ≤ 1-‖(bump h).aeval (arc h t)‖ by nlinarith [sq_nonneg t])]

private lemma dual_test {n : ℕ} {T : ℝ} (ha : (covariance T n).PosDef)
    (w : Fin n→ℝ) (hw : (∑ i,w i)=1) :
    1 ≤ inverseSum T n * (w ⬝ᵥ (covariance T n *ᵥ w)) := by
  let A := covariance T n
  let e : Fin n→ℝ := fun _ => 1
  let v := A⁻¹ *ᵥ e
  have av : A*ᵥv=e := by
    change A*ᵥ(A⁻¹*ᵥe)=e
    rw [mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ha.det_pos.ne'),one_mulVec]
  have we : w ⬝ᵥ e=1 := by simpa only [dotProduct,e,mul_one] using hw
  have ve : v ⬝ᵥ e=inverseSum T n := by simp [v,e,A,dotProduct,mulVec,inverseSum]
  have sym : A.transpose=A := by exact ha.1
  have dwa : v ⬝ᵥ (A*ᵥw)=1 := by rw [←Matrix.dotProduct_transpose_mulVec,sym,av,we]
  let q := w ⬝ᵥ (A*ᵥw)
  have wn : w≠0 := by rintro rfl; simp at hw
  have qp : 0<q := by simpa [q,A] using ha.dotProduct_mulVec_pos wn
  have zz := ha.posSemidef.dotProduct_mulVec_nonneg (w-q•v)
  change 0 ≤ star (w-q•v) ⬝ᵥ (A*ᵥ(w-q•v)) at zz
  simp only [star_trivial,Matrix.mulVec_sub,Matrix.mulVec_smul,av,sub_dotProduct,dotProduct_sub,
    dotProduct_smul,smul_dotProduct,smul_eq_mul,dwa,we,ve,mul_one] at zz
  change 0 ≤ q-q-q*(1-q*inverseSum T n) at zz
  change 1 ≤ inverseSum T n*q
  by_contra! hf
  nlinarith [mul_pos qp (sub_pos.mpr hf)]

private lemma escape {T : ℝ} (hT : 0<T) (h1 : T<1) : Tendsto (inverseSum T) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  let c := max 1 (b+1)
  have hc : 0<c := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨m,hm⟩ := (integralCap_zero.eventually_lt_const (inv_pos.mpr hc)).exists
  filter_upwards [eventually_gt_atTop (2*m)] with n hn
  obtain ⟨w,hw,hs⟩ := small_test hT h1 hn
  have hd := dual_test (definite hT h1 (by omega)) w hw
  have hs' : w ⬝ᵥ (covariance T n *ᵥ w)<c⁻¹ := hs.trans_lt hm
  have qpos : 0 ≤ w ⬝ᵥ (covariance T n *ᵥ w) := by
    simpa using (definite hT h1 (by omega : 0<n)).posSemidef.dotProduct_mulVec_nonneg w
  have hmul : (w ⬝ᵥ (covariance T n *ᵥ w))*c < 1 := by
    rw [← one_div] at hs'
    exact (lt_div_iff₀ hc).mp hs'
  have hb : b ≤ c := (by linarith : b ≤ b+1).trans (le_max_right _ _)
  by_contra! h
  nlinarith [mul_nonneg (sub_nonneg.mpr (h.le.trans hb)) qpos]
end OMA.S_mo_188611

theorem OMA.solution : type_of% @OMA.S_mo_188611.main := by
  intro T hT h1
  exact ⟨fun _ hn => OMA.S_mo_188611.definite hT h1 hn, OMA.S_mo_188611.escape hT h1⟩
