import OMAReductions.R_ERH_extended_riemann_hypothesis_R1
import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Finite lower bounds for Taylor polynomials of the regularized ideal series.
Squaring the truncation parameter removes the unknown field constant from
the lattice inequalities. -/
namespace OMA.R_ERH_extended_riemann_hypothesis_R1_H2_R2
open Complex Filter Set Metric NumberField
open scoped Topology NNReal ENNReal

/-- A uniform Taylor remainder for the damped regularization. -/
def H1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    let T := fun w : ℂ => (2+w)/(1-w)
    let d := Module.finrank ℚ K + 5
    let F := fun w : ℂ => (1-w)^d * ((T w-1)*dedekindZeta K (T w))
    let a := fun j : ℕ => iteratedDeriv j F 0 / j.factorial
    let P := fun (l : ℕ) (w : ℂ) => ∑ j ∈ Finset.range l, a j*w^j
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧
      (∀ s : ℂ, 1 < s.re → W s = (s-1)*dedekindZeta K s) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ (N : ℕ) (w : ℂ), ‖w‖ < 1 →
        ‖(1-w)^d * W (T w) - P (N+2) w‖ ≤ M/((N:ℝ)+1)

/-- Arbitrarily late finite certificates with explicit margins, on a
sequence of disks exhausting the unit disk. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    let T := fun w : ℂ => (2+w)/(1-w)
    let d := Module.finrank ℚ K + 5
    let F := fun w : ℂ => (1-w)^d * ((T w-1)*dedekindZeta K (T w))
    let a := fun j : ℕ => iteratedDeriv j F 0 / j.factorial
    let P := fun (l : ℕ) (w : ℂ) => ∑ j ∈ Finset.range l, a j*w^j
    ∀ m L : ℕ, ∃ n D : ℕ, L ≤ n ∧ 0 < D ∧
      let l := (n+1)^2+2
      let B := ∑ j ∈ Finset.range l, ‖a j‖*(j:ℝ)
      ∀ j ∈ Finset.Icc (-(D:ℤ)) D, ∀ k ∈ Finset.Icc (-(D:ℤ)) D,
        let v : ℂ := ⟨(j:ℝ)/D,(k:ℝ)/D⟩
        ‖v‖ ≤ (m:ℝ)/(m+1) → 1/((n:ℝ)+1)+2*B/(D:ℝ) < ‖P l v‖

theorem round_axis (x : ℝ) {D : ℕ} (hD : 0 < D) :
    ∃ j : ℤ, |(j:ℝ)/D| ≤ |x| ∧ |x-(j:ℝ)/D| ≤ (D:ℝ)⁻¹ := by
  have hpos : 0 < (D:ℝ) := by exact_mod_cast hD
  have positive (y : ℝ) (hy : 0 ≤ y) :
      ∃ j : ℤ, |(j:ℝ)/D| ≤ |y| ∧ |y-(j:ℝ)/D| ≤ (D:ℝ)⁻¹ := by
    let j := ⌊y*(D:ℝ)⌋
    have hj : 0 ≤ (j:ℝ) := by exact_mod_cast (Int.floor_nonneg.mpr (mul_nonneg hy hpos.le))
    have hlo : (j:ℝ)/D ≤ y := (div_le_iff₀ hpos).mpr (Int.floor_le _)
    refine ⟨j,by simpa [abs_of_nonneg hy,abs_of_nonneg (div_nonneg hj hpos.le)] using hlo,?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hlo),inv_eq_one_div,sub_le_iff_le_add,← add_div]
    exact (le_div_iff₀ hpos).mpr (by linarith [Int.lt_floor_add_one (y*(D:ℝ))])
  by_cases hx : 0 ≤ x
  · exact positive x hx
  · obtain ⟨j,hlo,hhi⟩ := positive (-x) (neg_nonneg.mpr (le_of_not_ge hx))
    refine ⟨-j,by simpa [neg_div] using hlo,?_⟩
    have he : x-((-j:ℤ):ℝ)/D = -(-x-(j:ℝ)/D) := by push_cast; ring
    simpa only [he,abs_neg] using hhi

theorem inward_node {D : ℕ} (hD : 0 < D) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ∃ j ∈ Finset.Icc (-(D:ℤ)) D, ∃ k ∈ Finset.Icc (-(D:ℤ)) D,
      ‖(⟨(j:ℝ)/D,(k:ℝ)/D⟩ : ℂ)‖ ≤ ‖w‖ ∧ ‖w-(⟨(j:ℝ)/D,(k:ℝ)/D⟩ : ℂ)‖ ≤ 2/(D:ℝ) := by
  obtain ⟨j,hx,hdx⟩ := round_axis w.re hD
  obtain ⟨k,hy,hdy⟩ := round_axis w.im hD
  have hpos : 0 < (D:ℝ) := by exact_mod_cast hD
  have hbox (i : ℤ) (h : |(i:ℝ)/D| ≤ 1) : i ∈ Finset.Icc (-(D:ℤ)) D := by
    rw [abs_div,abs_of_pos hpos,(div_le_one hpos)] at h
    have hi : |i| ≤ (D:ℤ) := by exact_mod_cast h
    exact Finset.mem_Icc.mpr (abs_le.mp hi)
  refine ⟨j,hbox _ (hx.trans ((abs_re_le_norm w).trans hw)),
    k,hbox _ (hy.trans ((abs_im_le_norm w).trans hw)),?_,?_⟩
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
    have hx' := pow_le_pow_left₀ (abs_nonneg _) hx 2
    have hy' := pow_le_pow_left₀ (abs_nonneg _) hy 2
    simp only [sq_abs] at hx' hy'
    dsimp only
    nlinarith only [hx',hy']
  · apply (norm_le_abs_re_add_abs_im _).trans
    change |w.re-(j:ℝ)/D|+|w.im-(k:ℝ)/D| ≤ _
    exact (add_le_add hdx hdy).trans_eq (by ring)

theorem pow_lipschitz (n : ℕ) {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖u^n-v^n‖ ≤ (n:ℝ)*‖u-v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : u^(n+1)-v^(n+1) = (u^n-v^n)*u+v^n*(u-v) := by rw [pow_succ,pow_succ]; ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,norm_pow,Nat.cast_succ,add_mul,one_mul]
    exact add_le_add ((mul_le_of_le_one_right (norm_nonneg _) hu).trans ih)
      (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hv))

theorem section_lipschitz (a : ℕ → ℂ) (l : ℕ) {u v : ℂ}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖(∑ j ∈ Finset.range l, a j*u^j)-(∑ j ∈ Finset.range l, a j*v^j)‖ ≤
      (∑ j ∈ Finset.range l, ‖a j‖*(j:ℝ))*‖u-v‖ := by
  rw [← Finset.sum_sub_distrib,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [← mul_sub,norm_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (pow_lipschitz j hu hv) (norm_nonneg _)

theorem grid_lower (a : ℕ → ℂ) (l : ℕ) {D : ℕ} (hD : 0 < D) {r t : ℝ}
    (hr : r ≤ 1)
    (h : ∀ j ∈ Finset.Icc (-(D:ℤ)) D, ∀ k ∈ Finset.Icc (-(D:ℤ)) D,
      let v : ℂ := ⟨(j:ℝ)/D,(k:ℝ)/D⟩
      ‖v‖ ≤ r → t + 2*(∑ i ∈ Finset.range l, ‖a i‖*(i:ℝ))/(D:ℝ) <
        ‖∑ i ∈ Finset.range l, a i*v^i‖)
    {w : ℂ} (hw : ‖w‖ ≤ r) : t < ‖∑ i ∈ Finset.range l, a i*w^i‖ := by
  obtain ⟨j,hj,k,hk,hv,hnear⟩ := inward_node hD (hw.trans hr)
  let v : ℂ := ⟨(j:ℝ)/D,(k:ℝ)/D⟩
  let P := fun z : ℂ => ∑ i ∈ Finset.range l, a i*z^i
  let B := ∑ i ∈ Finset.range l, ‖a i‖*(i:ℝ)
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (by positivity)
  have hbig : t + 2*B/D < ‖P v‖ := h j hj k hk (hv.trans hw)
  have hvar : ‖P w-P v‖ ≤ B*‖w-v‖ := section_lipschitz a l (hw.trans hr) ((hv.trans hw).trans hr)
  have hdist : ‖w-v‖ ≤ 2/(D:ℝ) := hnear
  have hchange := mul_le_mul_of_nonneg_left hdist hB
  rw [show B*(2/(D:ℝ)) = 2*B/D by ring] at hchange
  have htri := norm_add_le (P v-P w) (P w)
  rw [sub_add_cancel,norm_sub_rev] at htri
  change t < ‖P w‖
  linarith only [hbig,hvar,hchange,htri]

theorem inverse_coordinate {s : ℂ} (hs : 1/2 < s.re) :
    let w := (s-2)/(s+1)
    ‖w‖ < 1 ∧ (2+w)/(1-w) = s := by
  let w := (s-2)/(s+1)
  have hd : s+1 ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    norm_num at h
    linarith
  have hlt : ‖s-2‖ < ‖s+1‖ := by
    rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),Complex.sq_norm,Complex.sq_norm]
    simp only [Complex.normSq_apply,sub_re,sub_im,add_re,add_im]
    norm_num
    nlinarith
  have hw : ‖w‖ < 1 := by
    rw [show ‖w‖ = ‖s-2‖/‖s+1‖ from norm_div _ _,div_lt_one (norm_pos_iff.mpr hd)]
    exact hlt
  have hw1 : 1-w ≠ 0 := sub_ne_zero.mpr (fun e => by rw [← e] at hw; simpa using hw)
  refine ⟨hw,(div_eq_iff hw1).mpr ?_⟩
  have hrel : w*(s+1) = s-2 := div_mul_cancel₀ _ hd
  change 2+w = s*(1-w)
  linear_combination hrel

theorem covers {r : ℝ} (hr : r < 1) : ∃ m : ℕ, r ≤ (m:ℝ)/(m+1) := by
  obtain ⟨m,hm⟩ := exists_nat_gt (1/(1-r))
  have h := (div_lt_iff₀ (sub_pos.mpr hr)).mp hm
  refine ⟨m,(le_div_iff₀ (by positivity : 0 < (m:ℝ)+1)).mpr ?_⟩
  nlinarith only [h,hr]

theorem square_margin {M : ℝ} {n : ℕ} (hn : M ≤ (n:ℝ)) :
    M/((((n+1)^2 : ℕ):ℝ)+1) ≤ 1/((n:ℝ)+1) := by
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h := mul_le_mul_of_nonneg_right hn (show 0 ≤ (n:ℝ)+1 by positivity)
  nlinarith only [h,Nat.cast_nonneg (α := ℝ) n]

theorem inverse_radius (K : Type) [Field K] [NumberField K]
    (W : ℂ → ℂ) (hW : Differentiable ℂ W)
    (ha : ∀ z : ℂ, 1 < z.re → W z = (z-1)*dedekindZeta K z)
    (hn : ∀ z : ℂ, 1/2 < z.re → W z ≠ 0) (t : ℝ) :
    let c : ℂ := ⟨2,t⟩
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (3/2) ≤ p.radius ∧
      ∀ᶠ z in 𝓝 c, ((z-1)*dedekindZeta K z)*p.sum (z-c) = 1 := by
  let c : ℂ := ⟨2,t⟩
  have hd : DifferentiableOn ℂ (fun z => (W z)⁻¹) (ball c (3/2:ℝ)) := by
    intro z hz
    have h := (re_le_norm (c-z)).trans_lt (mem_ball_iff_norm'.mp hz)
    change 2-z.re < 3/2 at h
    exact ((hW z).inv (hn z (by linarith))).differentiableWithinAt
  obtain ⟨p,r₀,hp⟩ := hd.analyticAt (ball_mem_nhds c (by norm_num))
  refine ⟨p,ENNReal.le_of_forall_pos_nnreal_lt ?_,?_⟩
  · intro r hr hlt
    have hsub := Metric.closedBall_subset_ball (x := c) (ENNReal.coe_lt_ofReal.mp hlt)
    exact (hp.exchange_radius ((hd.mono hsub).hasFPowerSeriesOnBall hr)).r_le
  · have hre : ∀ᶠ z in 𝓝 c, 1 < (z:ℂ).re :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num [c])
    filter_upwards [hre,hp.eventually_hasSum_sub] with z hz hsum
    have he : p.sum (z-c) = (W z)⁻¹ := hsum.tsum_eq
    rw [he,← ha z hz,mul_inv_cancel₀ (hn z (by linarith))]

theorem main : H1 → H2 → OMA.R_ERH_extended_riemann_hypothesis_R1.H2 := by
  intro h1 h2 K _ _ t
  let T := fun w : ℂ => (2+w)/(1-w)
  let d := Module.finrank ℚ K + 5
  let F := fun w : ℂ => (1-w)^d * ((T w-1)*dedekindZeta K (T w))
  let a := fun j : ℕ => iteratedDeriv j F 0 / j.factorial
  let P := fun (l : ℕ) (w : ℂ) => ∑ j ∈ Finset.range l, a j*w^j
  obtain ⟨W,hW,ha,M,_,he⟩ := h1 K
  apply inverse_radius K W hW ha _ t
  intro s hs
  obtain ⟨hw,hT⟩ := inverse_coordinate hs
  let w := (s-2)/(s+1)
  obtain ⟨m,hm⟩ := covers hw
  obtain ⟨L,hL⟩ := exists_nat_gt M
  obtain ⟨n,D,hLn,hD,hgrid⟩ := h2 K m L
  have hr : (m:ℝ)/(m+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hl : 1/((n:ℝ)+1) < ‖P ((n+1)^2+2) w‖ := grid_lower a _ hD hr hgrid hm
  have herr : ‖(1-w)^d*W (T w)-P ((n+1)^2+2) w‖ ≤ M/((((n+1)^2:ℕ):ℝ)+1) :=
    he _ _ hw
  have hMn : M ≤ (n:ℝ) := hL.le.trans (by exact_mod_cast hLn)
  intro hz
  have hzero : W (T w) = 0 := (congrArg W hT).trans hz
  rw [hzero,mul_zero,zero_sub,norm_neg] at herr
  exact hl.not_ge (herr.trans (square_margin hMn))

end OMA.R_ERH_extended_riemann_hypothesis_R1_H2_R2
