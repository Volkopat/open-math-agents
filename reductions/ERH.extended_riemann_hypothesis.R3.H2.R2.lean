import OMAReductions.R_ERH_extended_riemann_hypothesis_R3
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Replace rational samples of a logarithmic circle mean by finite grid tests
for Taylor polynomials. The mesh is four to the negative degree and the
required lower bound is two to the negative degree. -/
namespace OMA.R_ERH_extended_riemann_hypothesis_R3_H2_R2
open Complex Set Metric Filter NumberField NumberField.InfinitePlace MeromorphicOn
open scoped Topology

/-- The pole-cleared completed Dirichlet series has an entire extension from
its germ at 2. No zero exclusion is needed in this analytic input. -/
def H1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    let G : ℂ → ℂ := fun s => s*(s-1)*(Complex.exp (s*(Real.log (discr K).natAbs/2 : ℝ))*
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K)*dedekindZeta K s
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F =ᶠ[𝓝 (2:ℂ)] G

/-- Each positive-width compact rectangle to the right of one half admits
arbitrarily large degrees passing a finite family of polynomial inequalities. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    let G : ℂ → ℂ := fun s => s*(s-1)*(Complex.exp (s*(Real.log (discr K).natAbs/2 : ℝ))*
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K)*dedekindZeta K s
    let a (k : ℕ) := (k.factorial : ℂ)⁻¹ * iteratedDeriv k G 2
    ∀ q : ℚ, (1/2 : ℝ) < q → ∀ T L : ℕ, ∃ n ≥ L, ∀ j k : ℤ,
      let D : ℝ := ((2:ℝ)^n)^2
      let x := (j : ℝ)/D
      let y := (k : ℝ)/D
      (q : ℝ) ≤ x → |x| ≤ T → |y| ≤ T →
        ((2:ℝ)^n)⁻¹ ≤ ‖∑ l ∈ Finset.range (n+1), a l*(((x : ℂ)+(y : ℂ)*I)-2)^l‖

theorem grid_round_up (x : ℝ) {D : ℝ} (hD : 0 < D) :
    x ≤ (⌈x*D⌉ : ℤ) / D ∧ ((⌈x*D⌉ : ℤ) : ℝ) / D ≤ x+D⁻¹ := by
  constructor
  · exact (le_div_iff₀ hD).mpr (Int.le_ceil _)
  · apply (div_le_iff₀ hD).mpr
    exact (Int.ceil_lt_add_one (x*D)).le.trans_eq (by field_simp)

theorem section_estimate (F : ℂ → ℂ) (hF : Differentiable ℂ F) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (z w : ℂ), ‖z‖ ≤ R → ‖w‖ ≤ R →
      ‖F z - ∑ k ∈ Finset.range (n+1), (k.factorial : ℂ)⁻¹ * iteratedDeriv k F 2 * (w-2)^k‖
        ≤ C*(‖z-w‖+(((2:ℝ)^n)^2)⁻¹) := by
  let a (k : ℕ) := (k.factorial : ℂ)⁻¹ * iteratedDeriv k F 2
  let u (w : ℂ) (k : ℕ) := a k * (w-2)^k
  have hsum (w : ℂ) : HasSum (u w) (F w) := by
    apply (Complex.hasSum_taylorSeries_of_entire hF (2:ℂ) w).congr_fun
    intro k
    simp only [u,a,smul_eq_mul]
    ring
  let S := 4*(R+2)
  have hR0 : 0 < R+2 := by linarith
  have hS : 0 < S := mul_pos (by norm_num) hR0
  let major (k : ℕ) := ‖a k‖ * S^k
  have hmajor : Summable major := by
    simpa only [major,u,add_sub_cancel_left,norm_mul,norm_pow,Complex.norm_of_nonneg hS.le] using
      (hsum (2+(S:ℂ))).summable.norm
  let M := ∑' k, major k
  have hnon (k : ℕ) : 0 ≤ major k := mul_nonneg (norm_nonneg _) (pow_nonneg hS.le _)
  have hM : 0 ≤ M := tsum_nonneg hnon
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:ℂ) R).bddAbove_image hF.deriv.continuous.norm.continuousOn
  let L := max B 0
  have hL : 0 ≤ L := le_max_right _ _
  refine ⟨L+M,add_nonneg hL hM,fun n z w hz hw => ?_⟩
  have hLip : ‖F z-F w‖ ≤ L*‖z-w‖ := by
    apply (convex_closedBall (0:ℂ) R).norm_image_sub_le_of_norm_deriv_le (fun v _ => hF v)
      (fun v hv => (hB (mem_image_of_mem _ hv)).trans (le_max_left _ _))
    · simpa using hw
    · simpa using hz
  have hw2 : ‖w-2‖ ≤ R+2 := (norm_sub_le _ _).trans (by simpa using add_le_add_right hw (2:ℝ))
  have hfour : ((2:ℝ)^n)^2 = (4:ℝ)^n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]; norm_num
  have hsTail := (summable_nat_add_iff (n+1)).mpr (hsum w).summable
  have hmTail := (summable_nat_add_iff (n+1)).mpr hmajor
  have hterm (i : ℕ) : ‖u w (i+(n+1))‖ ≤ major (i+(n+1)) / (4:ℝ)^n := by
    let k := i+(n+1)
    change ‖a k*(w-2)^k‖ ≤ major k / (4:ℝ)^n
    rw [norm_mul,norm_pow,le_div_iff₀ (by positivity : (0:ℝ)<4^n)]
    calc ‖a k‖*‖w-2‖^k*4^n ≤ ‖a k‖*(R+2)^k*4^k := by
           apply mul_le_mul (mul_le_mul_of_nonneg_left
             (pow_le_pow_left₀ (norm_nonneg _) hw2 _) (norm_nonneg _))
             (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) (by dsimp [k]; omega))
             (by positivity) (by positivity)
      _ = _ := by dsimp only [major,S]; rw [mul_pow]; ring
  have hmle : (∑' i, major (i+(n+1))) ≤ M := by
    have he := hmajor.sum_add_tsum_nat_add (n+1)
    have hp := Finset.sum_nonneg (s := Finset.range (n+1)) (fun k _ => hnon k)
    dsimp only [M]; linarith
  have htail : ‖F w-∑ k ∈ Finset.range (n+1), u w k‖ ≤ M/(4:ℝ)^n := by
    have hsplit := (hsum w).summable.sum_add_tsum_nat_add (n+1)
    rw [(hsum w).tsum_eq] at hsplit
    have he : F w-∑ k ∈ Finset.range (n+1), u w k = ∑' i, u w (i+(n+1)) := by
      linear_combination -hsplit
    rw [he]
    calc _ ≤ ∑' i, ‖u w (i+(n+1))‖ := norm_tsum_le_tsum_norm hsTail.norm
      _ ≤ ∑' i, major (i+(n+1)) / (4:ℝ)^n :=
        hsTail.norm.tsum_le_tsum hterm (by simpa only [div_eq_mul_inv] using hmTail.mul_right ((4:ℝ)^n)⁻¹)
      _ = (∑' i, major (i+(n+1)))/(4:ℝ)^n := by simp only [div_eq_mul_inv,tsum_mul_right]
      _ ≤ _ := div_le_div_of_nonneg_right hmle (by positivity)
  change ‖F z-∑ k ∈ Finset.range (n+1), u w k‖ ≤ _
  rw [hfour,mul_add]
  calc ‖F z-∑ k ∈ Finset.range (n+1), u w k‖
      ≤ ‖F z-F w‖+‖F w-∑ k ∈ Finset.range (n+1), u w k‖ :=
        by simpa only [dist_eq_norm] using dist_triangle (F z) (F w) (∑ k ∈ Finset.range (n+1), u w k)
    _ ≤ L*‖z-w‖ + M/(4:ℝ)^n := add_le_add hLip htail
    _ ≤ _ := by
      rw [div_eq_mul_inv]
      exact add_le_add (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hM) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hL) (by positivity))

theorem grid_excludes_zeros {F : ℂ → ℂ} {P : ℕ → ℂ → ℂ}
    (ha : ∀ R : ℝ, 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (z w : ℂ), ‖z‖ ≤ R → ‖w‖ ≤ R →
      ‖F z-P n w‖ ≤ C*(‖z-w‖+(((2:ℝ)^n)^2)⁻¹))
    (hg : ∀ q : ℚ, (1/2 : ℝ) < q → ∀ T L : ℕ, ∃ n ≥ L, ∀ j k : ℤ,
      let D : ℝ := ((2:ℝ)^n)^2
      let x := (j : ℝ)/D
      let y := (k : ℝ)/D
      (q : ℝ) ≤ x → |x| ≤ T → |y| ≤ T → ((2:ℝ)^n)⁻¹ ≤ ‖P n ((x:ℂ)+(y:ℂ)*I)‖)
    {z : ℂ} (hz : 1/2 < z.re) : F z ≠ 0 := by
  intro hzero
  obtain ⟨q,hq,hqz⟩ := exists_rat_btwn hz
  obtain ⟨T,hT⟩ := exists_nat_ge (‖z‖+3)
  obtain ⟨C,hC,he⟩ := ha T (by linarith [norm_nonneg z])
  obtain ⟨L,hL⟩ := exists_nat_gt (3*C)
  obtain ⟨n,hn,hgrid⟩ := hg q hq T L
  let d := (2:ℝ)^n
  let D := d^2
  have hd1 : 1 ≤ d := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  have hd : 0 < d := zero_lt_one.trans_le hd1
  have hD : 0 < D := sq_pos_of_pos hd
  have hDi : D⁻¹ ≤ 1 := by
    rw [inv_eq_one_div,div_le_one hD]; exact one_le_pow₀ hd1
  let j := ⌈z.re*D⌉
  let k := ⌈z.im*D⌉
  let x := (j:ℝ)/D
  let y := (k:ℝ)/D
  let w : ℂ := (x:ℂ)+(y:ℂ)*I
  obtain ⟨hx0,hx1⟩ : z.re ≤ x ∧ x ≤ z.re+D⁻¹ := grid_round_up _ hD
  obtain ⟨hy0,hy1⟩ : z.im ≤ y ∧ y ≤ z.im+D⁻¹ := grid_round_up _ hD
  have hwr : w.re = x := by simp [w]
  have hwi : w.im = y := by simp [w]
  have hzw : ‖z-w‖ ≤ 2*D⁻¹ := by
    apply (norm_le_abs_re_add_abs_im _).trans
    rw [sub_re,sub_im,hwr,hwi,abs_of_nonpos (sub_nonpos.mpr hx0),abs_of_nonpos (sub_nonpos.mpr hy0)]
    linarith
  have hw : ‖w‖ ≤ T := by
    have h := norm_add_le (w-z) z
    rw [sub_add_cancel,norm_sub_rev] at h
    linarith
  have hlarge : d⁻¹ ≤ ‖P n w‖ := hgrid j k (hqz.le.trans hx0)
    (by simpa only [hwr] using (abs_re_le_norm w).trans hw)
    (by simpa only [hwi] using (abs_im_le_norm w).trans hw)
  have hv := he n z w (by linarith) hw
  rw [hzero,zero_sub,norm_neg] at hv
  change ‖P n w‖ ≤ C*(‖z-w‖+D⁻¹) at hv
  have hbound : d⁻¹ ≤ 3*C/D := calc
    _ ≤ C*(‖z-w‖+D⁻¹) := hlarge.trans hv
    _ ≤ C*(2*D⁻¹+D⁻¹) := mul_le_mul_of_nonneg_left (by linarith only [hzw]) hC
    _ = _ := by ring
  have hfin := (le_div_iff₀ hD).mp hbound
  change d⁻¹*d^2 ≤ 3*C at hfin
  rw [pow_two, inv_mul_cancel_left₀ hd.ne'] at hfin
  have hnp : (n:ℝ) ≤ d := by dsimp [d]; exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have hLn : (L:ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem jensen_open {F : ℂ → ℂ} (hF : Differentiable ℂ F) {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hn : ∀ z ∈ ball c R, F z ≠ 0) :
    Real.circleAverage (fun z => Real.log ‖F z‖) c R = Real.log ‖F c‖ := by
  let U := closedBall c |R|
  have ha : AnalyticOnNhd ℂ F U :=
    (hF.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
  rw [ha.circleAverage_log_norm hR.ne' (hn c (mem_ball_self hR))]
  suffices h : (∑ᶠ z, (divisor F U z : ℝ)*Real.log (R*‖c-z‖⁻¹)) = 0 by
    change _ + _ = _; rw [h,zero_add]
  apply finsum_eq_zero_of_forall_eq_zero
  intro z
  by_cases hU : z ∈ U
  · by_cases hb : z ∈ ball c R
    · rw [ha.divisor_apply hU,(ha z hU).analyticOrderAt_eq_zero.mpr (hn z hb)]; simp
    · have hd : ‖c-z‖ = R := by
        have hc := mem_closedBall_iff_norm.mp hU
        rw [abs_of_pos hR] at hc
        have hl := not_lt.mp (fun h => hb (mem_ball_iff_norm.mpr h))
        rw [norm_sub_rev]; exact le_antisymm hc hl
      simp [hd,hR.ne']
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hU]

theorem main : H1 → H2 → OMA.R_ERH_extended_riemann_hypothesis_R3.H2 := by
  intro h1 h2 K _ _ G F a b hab ε hε
  obtain ⟨q,ha,hb⟩ := exists_between hab
  refine ⟨q,ha,hb,?_⟩
  obtain ⟨E,hd,hgerm⟩ := h1 K
  have hg : E =ᶠ[𝓝 (2:ℂ)] G := hgerm
  have hder (k : ℕ) : iteratedDeriv k G 2 = iteratedDeriv k E 2 := (hg.iteratedDeriv_eq k).symm
  let p (n : ℕ) (w : ℂ) := ∑ k ∈ Finset.range (n+1),
    (k.factorial:ℂ)⁻¹ * iteratedDeriv k G 2 * (w-2)^k
  have hseries : F = E := by
    funext z
    simpa only [F, hder] using
      (Complex.taylorSeries_eq_of_entire' (c := 2) (z := z) hd)
  have happrox (R : ℝ) (hR : 1 ≤ R) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (z w : ℂ), ‖z‖ ≤ R → ‖w‖ ≤ R →
        ‖E z-p n w‖ ≤ C*(‖z-w‖+(((2:ℝ)^n)^2)⁻¹) := by
    simpa only [p, hder] using section_estimate E hd R hR
  rw [hseries]
  have he := jensen_open (F := E) hd (c := 1+I*(q:ℝ)) (by norm_num : (0:ℝ)<1/2) (by
    intro z hz
    apply grid_excludes_zeros (P := p) happrox (h2 K)
    have hs := (abs_re_le_norm (z-(1+I*(q:ℝ)))).trans_lt (mem_ball_iff_norm.mp hz)
    have hre : |z.re-1| < 1/2 := by simpa using hs
    linarith [(abs_lt.mp hre).1])
  exact he.trans_lt (lt_add_of_pos_right _ hε)

end OMA.R_ERH_extended_riemann_hypothesis_R3_H2_R2
