import FormalConjectures.Paper.DeGiorgi
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Nine-dimensional transition layers: monotonicity from the core, and ball exhaustion

Credit: @huurou
Reference: del Pino, Kowalczyk and Wei, Annals of Mathematics 174 (2011),
https://doi.org/10.4007/annals.2011.174.3.3, especially the monotonicity argument in §10.

The unconditional PDE result is `layer_positive`: for a bounded classical Allen–Cahn
solution it suffices to check a nonnegative vertical derivative on |u| ≤ 3/4 and a
strictly positive derivative at the origin. No third derivatives, global gradient
bounds or maximum at infinity are assumed. A finite difference satisfies a linear
equation. A downward difference must lie entirely on one side at its endpoints;
there the coefficient is positive. A quadratic penalization excludes such a
difference on the whole space. A Gaussian lower barrier, uniform in the step size,
then proves strict positivity of the limiting derivative, not just monotonicity.

The two open inputs are (H1) approximate transition layers on expanding balls in
nine dimensions, with a fixed nonflatness gap, and (H2) standard interior compactness
for bounded profiles with vanishing Allen–Cahn residual. The proof passes the gap and
core estimates to the limit, rules out an affine level set by its midpoint, and
extends the solution cylindrically to all higher dimensions. Sending a scale to zero
and obtaining a flat limit does not suffice for H1: the points and gap are fixed.
The curved minimal graph and the nonlinear gluing that would produce the profiles
are not assumed to have been formalized.
-/

namespace OMA.R_DeGiorgi_DeGiorgi_ge_nine_R2

open EuclideanGeometry InnerProductSpace Set Filter Metric
open scoped Laplacian Topology

/-- Trace the ordinary second derivatives on Euclidean basis lines. -/
private theorem trace_lines {n : ℕ} {f : ℝ^n → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ^n) :
    (Δ f) x = ∑ i, deriv (deriv (fun t : ℝ => f (x + t • (EuclideanSpace.basisFun (Fin n) ℝ i)))) 0 := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  let d := EuclideanSpace.basisFun (Fin n) ℝ i
  have hl (t : ℝ) : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using (((hasDerivAt_id t).smul_const d).const_add x)
  have h1 (t : ℝ) := (hf.differentiable (by norm_num) (x+t•d)).hasFDerivAt.comp_hasDerivAt t (hl t)
  have h2 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h3 := ((h2.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt 0 (hl 0)).clm_apply
    (hasDerivAt_const (0:ℝ) d)
  have he : deriv (fun t : ℝ => f (x+t•d)) = fun t => fderiv ℝ f (x+t•d) d := funext (fun t => (h1 t).deriv)
  change iteratedFDeriv ℝ 2 f x ![d,d] = deriv (deriv (fun t : ℝ => f (x+t•d))) 0
  rw [he, iteratedFDeriv_two_apply]
  simpa using h3.deriv.symm

private theorem laplacian_min {n : ℕ} {f : ℝ^n → ℝ} (hf : ContDiff ℝ 2 f) {x : ℝ^n}
    (hm : ∀ y, f x ≤ f y) : 0 ≤ (Δ f) x := by
  rw [trace_lines hf]
  refine Finset.sum_nonneg fun i _ => ?_
  let g (t : ℝ) := f (x + t • (EuclideanSpace.basisFun (Fin n) ℝ i))
  have hmin : IsLocalMin g 0 := Filter.Eventually.of_forall fun t => by simpa [g] using hm (x + t • _)
  by_contra! h
  have hc : Continuous g := hf.continuous.comp (by fun_prop)
  have hmax := isLocalMax_of_deriv_deriv_neg h hmin.deriv_eq_zero hc.continuousAt
  have eq : g =ᶠ[𝓝 0] fun _ => g 0 := (hmin.and hmax).mono fun t ht => le_antisymm ht.2 ht.1
  have hz : deriv (deriv g) 0 = 0 := by simpa using eq.deriv.deriv_eq
  exact (not_lt_of_ge hz.ge) h

private theorem radial_laplacian {n : ℕ} {g d dd : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (h1 : ∀ z, HasDerivAt g (d z) z) (h2 : ∀ z, HasDerivAt d (dd z) z) (x : ℝ^n) :
    (Δ (fun y : ℝ^n => g (‖y‖^2))) x = 4*‖x‖^2 * dd (‖x‖^2) + 2*n*d (‖x‖^2) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hf : ContDiff ℝ 2 (fun y : ℝ^n => g (‖y‖^2)) := hg.comp (contDiff_norm_sq ℝ)
  rw [trace_lines hf]
  have term (i : Fin n) : deriv (deriv (fun t : ℝ => g (‖x+t•b i‖^2))) 0 =
      4 * (inner ℝ x (b i))^2 * dd (‖x‖^2) + 2*d (‖x‖^2) := by
    let q (t : ℝ) := ‖x‖^2 + 2*inner ℝ x (b i)*t + t^2
    have eq (t : ℝ) : ‖x+t•b i‖^2 = q t := by
      rw [norm_add_sq_real, norm_smul, b.orthonormal.norm_eq_one, mul_one, Real.norm_eq_abs,
        sq_abs, real_inner_smul_right]
      dsimp [q]; ring
    have dq (t : ℝ) : HasDerivAt q (2*inner ℝ x (b i)+2*t) t := by
      apply ((((hasDerivAt_id t).const_mul (2*inner ℝ x (b i))).const_add (‖x‖^2)).add (hasDerivAt_pow 2 t)).congr_deriv
      simp
    have hfirst : deriv (fun t => g (q t)) = fun t => d (q t)*(2*inner ℝ x (b i)+2*t) :=
      funext fun t => ((h1 _).comp t (dq t)).deriv
    simp_rw [eq]; rw [hfirst]
    have h := ((h2 _).comp 0 (dq 0)).mul (((hasDerivAt_id (0:ℝ)).const_mul 2).const_add (2*inner ℝ x (b i)))
    exact h.deriv.trans (by simp [q]; ring)
  change (∑ i, deriv (deriv (fun t : ℝ => g (‖x+t•b i‖^2))) 0) = _
  simp_rw [term]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, b.sum_sq_inner_left]
  simp; ring

/-- A lower-bounded C² function cannot have a negative region with Δv ≤ c v there, c > 0. -/
theorem weak_maximum {n : ℕ} {v : ℝ^n → ℝ} (hv : ContDiff ℝ 2 v) {B c : ℝ}
    (hB : ∀ x, B ≤ v x) (hc : 0 < c) (hΔ : ∀ x, v x < 0 → (Δ v) x ≤ c*v x) : ∀ x, 0 ≤ v x := by
  intro x
  by_contra! hx
  let ε := -(c*v x)/(2*n + c*‖x‖^2 + 1)
  have hden : 0 < 2*(n:ℝ) + c*‖x‖^2 + 1 := by positivity
  have hε : 0 < ε := div_pos (neg_pos.mpr (mul_neg_of_pos_of_neg hc hx)) hden
  have heq : ε * (2*n + c*‖x‖^2 + 1) = -(c*v x) := by exact div_mul_cancel₀ _ hden.ne'
  let P (z : ℝ^n) := ε * ‖z‖^2
  have hP : ContDiff ℝ 2 P := contDiff_const.mul (contDiff_norm_sq ℝ)
  have hp : ∀ z, (Δ P) z = 2*n*ε := by
    intro z
    have h := radial_laplacian (g := fun t => ε*t) (d := fun _ => ε) (dd := fun _ => 0)
      (contDiff_const.mul contDiff_id) (fun t => by simpa using (hasDerivAt_id t).const_mul ε)
      (fun t => hasDerivAt_const t ε) z
    simpa only [mul_zero, zero_add] using h
  obtain ⟨y, hm⟩ := (hv.add hP).continuous.exists_forall_le' x (by
    have hlim : Tendsto (fun z : ℝ^n => ε * ‖z‖^2) (cocompact _) atTop :=
      (tendsto_norm_cocompact_atTop.atTop_mul_atTop₀ tendsto_norm_cocompact_atTop |>.const_mul_atTop hε).congr (fun _ => by rw [pow_two])
    filter_upwards [hlim.eventually_ge_atTop (v x + P x - B)] with z hz
    change v x + P x ≤ v z + P z
    change _ ≤ P z at hz
    linarith [hB z])
  have hmin := laplacian_min (hv.add hP) hm
  change 0 ≤ (Δ (v+P)) y at hmin
  rw [hv.contDiffAt.laplacian_add hP.contDiffAt, hp] at hmin
  have hy : v y ≤ v x + ε*‖x‖^2 := by
    have h := hm x
    change v y + ε*‖y‖^2 ≤ v x + ε*‖x‖^2 at h
    linarith [mul_nonneg hε.le (sq_nonneg ‖y‖)]
  have hs : c*(v x + ε*‖x‖^2) + 2*n*ε < 0 := by nlinarith only [heq,hε]
  have hneg : v y < 0 := by
    by_contra! h; nlinarith only [mul_nonneg hc.le (h.trans hy), hs, mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) hε.le]
  linarith [hΔ y hneg, mul_le_mul_of_nonneg_left hy hc.le]

/-- Propagate a strictly positive bound on a ball to all of space using a Gaussian.
The comparison constant does not depend on v, which permits passing to difference-quotient limits. -/
theorem gaussian_minorant {n : ℕ} {v : ℝ^n → ℝ} (hv : ContDiff ℝ 2 v) (hn : ∀ x, 0 ≤ v x)
    {K r m a : ℝ} (hK : 0 < K) (hr : 0 < r) (hm : 0 < m) (ha : 0 < a)
    (har : K ≤ 4*a^2*r^2 - 2*n*a) (hin : ∀ x, ‖x‖ < r → m ≤ v x)
    (hout : ∀ x, (Δ v) x ≤ K*v x) : ∀ x, m*Real.exp (-a*‖x‖^2) ≤ v x := by
  let g (z : ℝ) := m*Real.exp (-a*z)
  let b (x : ℝ^n) := g (‖x‖^2)
  have cg : ContDiff ℝ 2 g := by dsimp [g]; fun_prop
  have cb : ContDiff ℝ 2 b := cg.comp (contDiff_norm_sq ℝ)
  have dg (t : ℝ) : HasDerivAt g (-a*g t) t := by
    apply ((((hasDerivAt_id t).const_mul (-a)).exp).const_mul m).congr_deriv
    dsimp [g]; ring
  have ddg (t : ℝ) : HasDerivAt (fun z => -a*g z) (a^2*g t) t := by
    apply ((dg t).const_mul (-a)).congr_deriv; ring
  have hb (x : ℝ^n) : (Δ b) x = (4*a^2*‖x‖^2 - 2*n*a)*b x :=
    (radial_laplacian cg dg ddg x).trans (by dsimp [b]; ring)
  have bp (x : ℝ^n) : 0 < b x := mul_pos hm (Real.exp_pos _)
  have bmax (x : ℝ^n) : b x ≤ m := by
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ha.le (sq_nonneg ‖x‖)])) hm.le).trans_eq (mul_one m)
  have hh := weak_maximum (v := v-b) (hv.sub cb) (B := -m) (c := K)
    (fun x => by change -m ≤ v x - b x; linarith [bmax x, hn x]) hK (by
      intro x hx
      change v x - b x < 0 at hx
      have hxr : r ≤ ‖x‖ := by by_contra! h; linarith [hin x h, bmax x]
      have hsq : r^2 ≤ ‖x‖^2 := by gcongr
      have hcoef : K ≤ 4*a^2*‖x‖^2 - 2*n*a := by linarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 4*a^2)]
      rw [hv.contDiffAt.laplacian_sub cb.contDiffAt, hb]
      change _ ≤ K*(v x-b x)
      linarith [hout x, mul_le_mul_of_nonneg_right hcoef (bp x).le])
  exact fun x => sub_nonneg.mp (hh x)


/-- A decreasing pair on a line must be in one stable phase if the derivative points up
throughout the transition band. Integrating a nonnegative cutoff avoids endpoint cases. -/
private theorem same_tail {f d : ℝ → ℝ} (hd : ∀ t, HasDerivAt f (d t) t)
    (hcore : ∀ t, |f t| ≤ 3/4 → 0 ≤ d t) {h : ℝ} (hh : 0 < h) (hdec : f h < f 0) :
    3/4 ≤ f h ∨ f 0 ≤ -(3/4) := by
  let k (s : ℝ) := max 0 (3/4 - |s|)
  let F (s : ℝ) := ∫ t in (0:ℝ)..s, k t
  have hk : Continuous k := by dsimp [k]; fun_prop
  have dF (s : ℝ) : HasDerivAt F (k s) s := (hk.integral_hasStrictDerivAt 0 s).hasDerivAt
  have monoF := monotone_of_hasDerivAt_nonneg dF (fun t => le_max_left _ _)
  have strict : StrictMonoOn F (Set.Icc (-(3/4):ℝ) (3/4)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc ..) (fun t _ => (dF t).continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    exact (dF t).deriv ▸ lt_max_of_lt_right (sub_pos.mpr (abs_lt.mpr ht))
  have mono : Monotone (F ∘ f) := by
    apply monotone_of_hasDerivAt_nonneg (fun t => (dF _).comp t (hd t))
    intro t
    by_cases ht : |f t| ≤ 3/4
    · exact mul_nonneg (le_max_left _ _) (hcore t ht)
    · simp [k, max_eq_left (sub_nonpos.mpr (le_of_not_ge ht))]
  by_contra! bad
  obtain ⟨hlo,hhi⟩ := bad
  let l := max (f h) (-(3/4))
  let r := min (f 0) (3/4)
  have hlr : l < r := max_lt (lt_min hdec hlo) (lt_min hhi (by norm_num))
  have lmem : l ∈ Set.Icc (-(3/4):ℝ) (3/4) := ⟨le_max_right .., hlr.le.trans (min_le_right ..)⟩
  have rmem : r ∈ Set.Icc (-(3/4):ℝ) (3/4) := ⟨lmem.1.trans hlr.le, min_le_right ..⟩
  exact (not_lt_of_ge (mono hh.le)) <| (monoF (le_max_left ..)).trans_lt ((strict lmem rmem hlr).trans_le (monoF (min_le_left ..)))

private theorem vertical_jet {n : ℕ} {u : ℝ^n → ℝ} (hu : ContDiff ℝ 2 u) (e x : ℝ^n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => u (x+s•e)) (fderiv ℝ u (x+t•e) e) t :=
  (hu.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t
    (by simpa using ((hasDerivAt_id t).smul_const e).const_add x)

private theorem difference_control {n : ℕ} {u : ℝ^n → ℝ} (hu : ContDiff ℝ 2 u)
    {C : ℝ} (hC : ∀ x, |u x| ≤ C) (hpde : ∀ x, (Δ u) x + u x - (u x)^3 = 0)
    (e : ℝ^n) (hcore : ∀ x, |u x| ≤ 3/4 → 0 ≤ fderiv ℝ u x e) {h : ℝ} (hh : 0 < h) :
    let w := fun x => h⁻¹ * (u (x+h•e) - u x)
    ContDiff ℝ 2 w ∧ (∀ x, 0 ≤ w x) ∧ ∀ x, (Δ w) x ≤ (3*C^2+1)*w x := by
  let U := fun x => u (x+h•e)
  let w := fun x => h⁻¹ * (U x - u x)
  have hU : ContDiff ℝ 2 U := hu.comp (contDiff_id.add contDiff_const)
  have hw : ContDiff ℝ 2 w := contDiff_const.mul (hU.sub hu)
  have shift (x : ℝ^n) : (Δ U) x = (Δ u) (x+h•e) := by
    simp only [U, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_comp_add_right]
  have eq (x : ℝ^n) : (Δ w) x = ((U x)^2 + U x*u x + (u x)^2-1)*w x := by
    change (Δ (h⁻¹ • (U-u))) x = _
    have hsub : ContDiffAt ℝ 2 (U-u) x := (hU.sub hu).contDiffAt
    rw [laplacian_smul h⁻¹ hsub, hU.contDiffAt.laplacian_sub hu.contDiffAt, shift]
    have h1 := hpde (x+h•e)
    have h2 := hpde x
    change h⁻¹*((Δ u) (x+h•e) - (Δ u) x) = ((U x)^2 + U x*u x + (u x)^2-1)*(h⁻¹*(U x-u x))
    dsimp only [U]
    linear_combination h⁻¹ * (h1 - h2)
  have nonneg : ∀ x, 0 ≤ w x := by
    refine weak_maximum hw (B := h⁻¹ * (-2*C)) (c := 1/2) ?_ (by norm_num) ?_
    · intro x
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hh.le)
      linarith [(abs_le.mp (hC (x+h•e))).1, (abs_le.mp (hC x)).2, show U x = u (x+h•e) from rfl]
    · intro x hx
      have hdec : U x < u x := by
        by_contra! hn
        exact (not_lt_of_ge (mul_nonneg (inv_nonneg.mpr hh.le) (sub_nonneg.mpr hn))) hx
      have hd := same_tail (vertical_jet hu e x) (fun t => hcore (x+t•e)) hh (by simpa [U] using hdec)
      simp only [zero_smul, add_zero] at hd
      have tail (s t : ℝ) (hs : 3/4 ≤ s) (ht : 3/4 ≤ t) : 1/2 ≤ s^2+s*t+t^2-1 := by
        nlinarith [sq_nonneg (s-3/4), sq_nonneg (t-3/4), mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr ht)]
      rw [eq]
      apply mul_le_mul_of_nonpos_right _ hx.le
      rcases hd with h | h
      · exact tail _ _ h (h.trans hdec.le)
      · have := tail (-(U x)) (-(u x)) (by linarith) (by linarith)
        linarith
  refine ⟨hw,nonneg,fun x => ?_⟩
  rw [eq]
  apply mul_le_mul_of_nonneg_right _ (nonneg x)
  have h1 := hC (x+h•e); change |U x| ≤ C at h1
  have h2 := hC x
  have s1 : U x ^ 2 ≤ C^2 := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans h1)).2 h1 |>.trans_eq' (sq_abs _)
  have s2 : u x ^ 2 ≤ C^2 := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans h2)).2 h2 |>.trans_eq' (sq_abs _)
  nlinarith [sq_nonneg (U x - u x)]

/-- Local-to-global monotonicity for a bounded classical Allen–Cahn layer. Only the
transition band is tested, and no global derivative bound or third derivative is needed. -/
theorem layer_positive {n : ℕ} {u : ℝ^n → ℝ} (hu : ContDiff ℝ 2 u) {C : ℝ}
    (hC : ∀ x, |u x| ≤ C) (hpde : ∀ x, (Δ u) x + u x - (u x)^3 = 0)
    (e : ℝ^n) (he : ‖e‖ = 1) (hcore : ∀ x, |u x| ≤ 3/4 → 0 ≤ fderiv ℝ u x e)
    (hanchor : 0 < fderiv ℝ u 0 e) : ∀ x, 0 < fderiv ℝ u x e := by
  let V := fun x => fderiv ℝ u x e
  let m := V 0 / 2
  have hm : 0 < m := half_pos hanchor
  have hcont : Continuous V := hu.continuous_fderiv (by norm_num) |>.clm_apply continuous_const
  have hnh : ∀ᶠ x in 𝓝 (0:ℝ^n), m < V x := hcont.continuousAt (lt_mem_nhds (half_lt_self hanchor))
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp hnh
  let r := R/2
  have hr : 0 < r := half_pos hR
  let K := 3*C^2+1
  have hK : 0 < K := by dsimp [K]; positivity
  let a := 1+(2*n+K)/r^2
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : 1 ≤ a := le_add_of_nonneg_right (by positivity : 0 ≤ (2*(n:ℝ)+K)/r^2)
  have har : K ≤ 4*a^2*r^2-2*n*a := by
    have h := div_mul_cancel₀ (2*(n:ℝ)+K) (pow_ne_zero 2 hr.ne')
    have h1 : 2*n+K ≤ a*r^2 := by dsimp [a]; nlinarith only [h,sq_nonneg r]
    have h2 : K ≤ 4*a*r^2 - 2*n := by nlinarith [mul_nonneg ha.le (sq_nonneg r)]
    have h3 := mul_le_mul ha1 h2 hK.le ha.le
    nlinarith only [h3]
  intro x
  have hlim := (vertical_jet hu e x 0).tendsto_slope_zero_right
  have hlow : m*Real.exp (-a*‖x‖^2) ≤ V x := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds (by simpa [V, smul_eq_mul] using hlim)
    have pos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
    have small : ∀ᶠ h : ℝ in 𝓝[>] 0, h < r := nhdsWithin_le_nhds (Iio_mem_nhds hr)
    filter_upwards [pos, small] with h hh hhr
    let w := fun y : ℝ^n => h⁻¹*(u (y+h•e)-u y)
    obtain ⟨hw,hn,hΔ⟩ := difference_control hu hC hpde e hcore hh
    apply gaussian_minorant (v := w) hw hn hK hr hm ha har _ hΔ x
    intro y hy
    let f := fun t : ℝ => u (y+t•e)
    obtain ⟨t,ht,hd⟩ := exists_hasDerivAt_eq_slope f (fun t => V (y+t•e)) hh
      ((hu.continuous.comp (by fun_prop)).continuousOn) (fun t _ => vertical_jet hu e y t)
    have hn' : ‖y+t•e‖ < R := by
      have h := norm_add_le y (t•e)
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos ht.1] at h
      dsimp [r] at hy hhr; linarith [ht.2]
    have hm' : m < V (y+t•e) := hball (by rwa [Metric.mem_ball, dist_zero_right])
    change m ≤ h⁻¹*(u (y+h•e)-u y)
    simpa [f, div_eq_inv_mul] using (hm'.le.trans_eq hd)
  exact (mul_pos hm (Real.exp_pos _)).trans_le hlow

theorem coordinate_laplacian {m n : ℕ} (h : m ≤ n) (u : ℝ^m → ℝ) (hu : ContDiff ℝ 2 u) :
    let p := fun x : ℝ^n => WithLp.toLp 2 (fun i : Fin m => x (i.castLE h))
    ∀ x, (Δ (u ∘ p)) x = (Δ u) (p x) := by
  let P : ℝ^n →L[ℝ] ℝ^m :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i : Fin m => PiLp.proj 2 (fun _ : Fin n => ℝ) (i.castLE h))
  have hin (i : Fin m) : P (EuclideanSpace.single (i.castLE h) 1) = EuclideanSpace.single i 1 := by
    ext j
    change EuclideanSpace.single (i.castLE h) (1 : ℝ) (j.castLE h) = EuclideanSpace.single i (1 : ℝ) j
    simp only [EuclideanSpace.single, PiLp.single_apply, Fin.ext_iff, Fin.val_castLE]
  have hout (j : Fin n) (hj : j ∉ Set.range (Fin.castLE h)) : P (EuclideanSpace.single j 1) = 0 := by
    ext i
    have hij : i.castLE h ≠ j := fun he => hj ⟨i, he⟩
    change EuclideanSpace.single j (1 : ℝ) (i.castLE h) = 0
    simp only [EuclideanSpace.single, PiLp.single_apply, if_neg hij]
  change ∀ x : ℝ^n, (Δ (u ∘ P)) x = (Δ u) (P x)
  intro x
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (u ∘ P) (EuclideanSpace.basisFun (Fin n) ℝ),
      laplacian_eq_iteratedFDeriv_orthonormalBasis u (EuclideanSpace.basisFun (Fin m) ℝ)]
  simp only [EuclideanSpace.basisFun_apply, P.iteratedFDeriv_comp_right hu x (i := 2) (by norm_num),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  symm
  apply Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h)
  · intro j hj
    apply ContinuousMultilinearMap.map_coord_zero _ 0
    simpa using hout j hj
  · intro i
    congr 1
    funext k
    fin_cases k <;> simpa using (hin i).symm


lemma level_midpoint {n : ℕ} {u : ℝ^n → ℝ}
    (h : DeGiorgi.HasHyperplaneLevelSets u) {x z : ℝ^n} (hxz : u x = u z) :
    u (midpoint ℝ x z) = u x := by
  obtain ⟨S, hS, _⟩ := h (u x) ⟨x, rfl⟩
  have hx : x ∈ (S : Set (ℝ^n)) := hS ▸ (show x ∈ u ⁻¹' {u x} from rfl)
  have hz : z ∈ (S : Set (ℝ^n)) := hS ▸ (show z ∈ u ⁻¹' {u x} from hxz.symm)
  have hm := S.convex.midpoint_mem hx hz
  rwa [← hS] at hm

private theorem lift_midpoint {u : ℝ^9 → ℝ} (hu : DeGiorgi.IsBoundedSolution u)
    (hpos : DeGiorgi.HasPositiveDeriv u) {a b : ℝ^9} (ha : u a = u b)
    (hm : u (midpoint ℝ a b) ≠ u a) : type_of% @DeGiorgi.DeGiorgi_ge_nine := by
  intro n inst hn hflat
  let p : ℝ^n →L[ℝ] ℝ^9 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 9 => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i : Fin 9 => PiLp.proj 2 (fun _ : Fin n => ℝ) (i.castLE hn))
  have hp (x : ℝ^n) (i : Fin 9) : p x i = x (i.castLE hn) := rfl
  let v : ℝ^n → ℝ := u ∘ p
  have hv : DeGiorgi.IsBoundedSolution v := by
    refine ⟨hu.regular.comp p.contDiff, ?_, ?_⟩
    · obtain ⟨C, hC⟩ := hu.bounded
      exact ⟨C, fun x => hC (p x)⟩
    · intro x
      have hL : (Δ v) x = (Δ u) (p x) := coordinate_laplacian hn u hu.regular x
      exact (congrArg (fun r : ℝ => r + u (p x) - u (p x) ^ 3) hL).trans (hu.solution _)
  have hp0 : p (EuclideanSpace.single 0 1) = EuclideanSpace.single 0 1 := by
    ext i
    change EuclideanSpace.single (0 : Fin n) (1 : ℝ) (i.castLE hn) =
      EuclideanSpace.single (0 : Fin 9) (1 : ℝ) i
    simp only [EuclideanSpace.single, PiLp.single_apply, Fin.ext_iff, Fin.val_castLE, Fin.val_zero]
  have hvpos : DeGiorgi.HasPositiveDeriv v := by
    intro x
    have hd := hu.regular.differentiable (by norm_num) (p x)
    have hc := hd.hasFDerivAt.comp x p.hasFDerivAt
    rw [hc.differentiableAt.lineDeriv_eq_fderiv, hc.fderiv, ContinuousLinearMap.comp_apply, hp0]
    simpa only [hd.lineDeriv_eq_fderiv] using hpos (p x)
  let lift (w : ℝ^9) : ℝ^n := WithLp.toLp 2 fun j : Fin n => if h : j.val < 9 then w ⟨j.val, h⟩ else 0
  have hpLift (w : ℝ^9) : p (lift w) = w := by
    ext i
    simp [hp, lift, i.isLt]
  have hval (w : ℝ^9) : v (lift w) = u w := by simp [v, hpLift]
  have hmid := level_midpoint (hflat v ⟨hv, hvpos⟩)
    (x := lift a) (z := lift b) (by simpa only [hval] using ha)
  apply hm
  simpa [v, Function.comp_apply, midpoint_eq_smul_add, hpLift] using hmid



/-- Finite-ball construction at a fixed scale. The size of the midpoint gap and the
slope at the origin must not vanish as the radius increases. Nothing is required
of the sign of a vertical derivative outside the transition band. -/
def H1 : Prop := ∃ (C δ : ℝ) (p : ℝ^9), 0 < δ ∧ ∀ k : ℕ, ∃ v : ℝ^9 → ℝ,
    ContDiffOn ℝ 2 v (Metric.ball 0 ((k:ℝ)+1)) ∧
    (∀ x, ‖x‖ < (k:ℝ)+1 → |v x| ≤ C ∧ |(Δ v) x + v x - (v x)^3| ≤ 1/((k:ℝ)+1)) ∧
    |v p-v (-p)| ≤ 1/((k:ℝ)+1) ∧ δ ≤ |v p-v 0| ∧
    δ ≤ fderiv ℝ v 0 (EuclideanSpace.single 0 1) ∧
    ∀ x, ‖x‖ < (k:ℝ)+1 → |v x| < 4/5 → 0 ≤ fderiv ℝ v x (EuclideanSpace.single 0 1)

/-- Interior elliptic compactness, independent of symmetry, monotonicity and nonflatness.
Pointwise convergence of the values and one derivative on a common subsequence is enough. -/
def H2 : Prop := ∀ (C : ℝ) (v : ℕ → ℝ^9 → ℝ),
    (∀ k, ContDiffOn ℝ 2 (v k) (Metric.ball 0 ((k:ℝ)+1))) →
    (∀ (k : ℕ) (x : ℝ^9), ‖x‖ < (k:ℝ)+1 → |v k x| ≤ C ∧ |(Δ (v k)) x + v k x - (v k x)^3| ≤ 1/((k:ℝ)+1)) →
    ∃ (u : ℝ^9 → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ DeGiorgi.IsBoundedSolution u ∧
      ∀ x, Tendsto (fun k => v (φ k) x) atTop (𝓝 (u x)) ∧
        Tendsto (fun k => fderiv ℝ (v (φ k)) x (EuclideanSpace.single 0 1)) atTop
          (𝓝 (fderiv ℝ u x (EuclideanSpace.single 0 1)))

theorem main : H1 → H2 → type_of% @DeGiorgi.DeGiorgi_ge_nine := by
  intro build compact
  obtain ⟨C,δ,p,hδ,hs⟩ := build
  choose v hv using hs
  obtain ⟨u,φ,hφ,hu,hconv⟩ := compact C v (fun k => (hv k).1) (fun k => (hv k).2.1)
  have hp : u p = u (-p) := by
    have h := le_of_tendsto_of_tendsto (((hconv p).1.sub (hconv (-p)).1).abs)
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
      (Eventually.of_forall fun k => (hv (φ k)).2.2.1)
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
  have gap : u p ≠ u 0 := by
    have h := ge_of_tendsto' (((hconv p).1.sub (hconv 0).1).abs) (fun k => (hv (φ k)).2.2.2.1)
    intro he
    rw [he, sub_self, abs_zero] at h
    linarith
  let e : ℝ^9 := EuclideanSpace.single 0 1
  have hanchor : 0 < fderiv ℝ u 0 e := hδ.trans_le (ge_of_tendsto' (hconv 0).2
    (fun k => (hv (φ k)).2.2.2.2.1))
  have hcore (x : ℝ^9) (hx : |u x| ≤ 3/4) : 0 ≤ fderiv ℝ u x e := by
    apply ge_of_tendsto (hconv x).2
    have hval := ((hconv x).1.abs).eventually_lt_const (by linarith : |u x| < 4/5)
    have hlarge : Tendsto (fun k => ((φ k:ℕ):ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
    filter_upwards [hval,hlarge.eventually_ge_atTop ‖x‖] with k hk hR
    exact (hv (φ k)).2.2.2.2.2 x (by linarith) hk
  obtain ⟨B,hB⟩ := hu.bounded
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.single]
  have hup : DeGiorgi.HasPositiveDeriv u := fun x => by
    rw [(hu.regular.differentiable (by norm_num) x).lineDeriv_eq_fderiv]
    exact layer_positive hu.regular hB hu.solution e he hcore hanchor x
  intro n _ hn
  exact lift_midpoint hu hup hp (by simpa only [midpoint_self_neg] using gap.symm) hn

end OMA.R_DeGiorgi_DeGiorgi_ge_nine_R2
