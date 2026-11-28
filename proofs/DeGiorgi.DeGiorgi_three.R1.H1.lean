import OMAReductions.R_DeGiorgi_DeGiorgi_three_R1
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Quadratic energy growth for monotone bounded Allen-Cahn solutions in dimension 3

Following Ambrosio and Cabre (2000) and Alberti, Ambrosio, and Cabre (2001):
1. A penalized maximum principle bounds every entire bounded solution by 1.
2. Lifting the 2D gradient estimate to dimension 3 and applying it three times
   (to u, to first finite differences, and to second finite differences) yields
   uniform C^{2,1} bounds without Schauder theory.
3. Arzela-Ascoli extracts a C^2_loc limit u_+ on R^2 as x_0 -> +infinity,
   inheriting stability from the positive derivative d_0 u > 0.
4. A regularized Sternberg-Zumbrun inequality with 2D logarithmic cutoffs forces
   u_+ to be either constant +-1 or a 1D heteroclinic kink, giving O(R) 2D energy.
5. A foliation calibration proves u minimizes the Allen-Cahn energy against
   slide competitors between u and u^t, yielding E(u; B_R) <= E(u_+; B_R) + C R^2 <= C' R^2.
-/

namespace OMA.DeGiorgiEnergy3

open EuclideanGeometry InnerProductSpace Metric Filter Set MeasureTheory
open scoped Gradient Laplacian Topology

private abbrev Space := ℝ^3
private abbrev Plane := ℝ^2

/-
## Section 1: Uniform bound |u| <= 1 and 3D gradient / C^{2,1} bootstrap
-/

private noncomputable def second3 (u : Space → ℝ) (x d : Space) : ℝ :=
  (fderiv ℝ (fderiv ℝ u) x d) d

private theorem line_deriv3 {u : Space → ℝ} (hu : ContDiff ℝ 2 u) (x d : Space) (t : ℝ) :
    HasDerivAt (fun s : ℝ => u (x + s • d)) (fderiv ℝ u (x + t • d) d) t :=
  (hu.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t
    (by simpa using (((hasDerivAt_id t).smul_const d).const_add x))

private theorem line_second3 {u : Space → ℝ} (hu : ContDiff ℝ 2 u) (x d : Space) :
    HasDerivAt (fun t : ℝ => fderiv ℝ u (x + t • d) d) (second3 u x d) 0 := by
  have hF : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hl : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x)
  have h := (hF.differentiable one_ne_zero (x + (0 : ℝ) • d)).hasFDerivAt.comp_hasDerivAt 0 hl
  have he := h.clm_apply (hasDerivAt_const (0 : ℝ) d)
  simpa [second3] using he

private theorem second3_neg_dir (u : Space → ℝ) (x d : Space) :
    second3 u x (-d) = second3 u x d := by simp [second3]

private theorem sum_second3 {u : Space → ℝ} (b : OrthonormalBasis (Fin 3) ℝ Space) (x : Space) :
    (Δ u) x = second3 u x (b 0) + second3 u x (b 1) + second3 u x (b 2) := by
  simp [laplacian_eq_iteratedFDeriv_orthonormalBasis u b, Fin.sum_univ_three,
    iteratedFDeriv_two_apply, second3, add_assoc]

private theorem quadratic_deriv (a b c t : ℝ) :
    HasDerivAt (fun s : ℝ => a + b * s + c * s ^ 2) (b + 2 * c * t) t := by
  have h := (((hasDerivAt_id t).const_mul b).const_add a).add
    ((hasDerivAt_pow 2 t).const_mul c)
  change HasDerivAt (fun s : ℝ => a + b * s + c * s ^ 2) _ t at h
  simpa [mul_comm c, mul_assoc, mul_left_comm] using h

private theorem affine_deriv (a b t : ℝ) :
    HasDerivAt (fun s : ℝ => a + b * s) b t := by
  simpa using (((hasDerivAt_id t).const_mul b).const_add a)

private theorem local_max_second_nonpos {f g : ℝ → ℝ} {s : ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : HasDerivAt g s 0)
    (hm : IsLocalMax f 0) : s ≤ 0 := by
  by_contra! hs
  let p (t : ℝ) := f t - (0 + 0 * t + (s / 4) * t ^ 2)
  let d (t : ℝ) := g t - (0 + 2 * (s / 4) * t)
  have hp (t : ℝ) : HasDerivAt p (d t) t := (hf t).sub (quadratic_deriv 0 0 (s / 4) t)
  have hd : HasDerivAt d (s - 2 * (s / 4)) 0 :=
    hg.sub (affine_deriv 0 (2 * (s / 4)) 0)
  have hpd : deriv p = d := funext fun t => (hp t).deriv
  have hg0 : g 0 = 0 := (hf 0).deriv.symm.trans hm.deriv_eq_zero
  have hd0 : deriv p 0 = 0 := by simp [hpd, d, hg0]
  have hpmin : IsLocalMin p 0 := by
    apply isLocalMin_of_deriv_deriv_pos _ hd0 (hp 0).continuousAt
    rw [hpd, hd.deriv]
    linarith
  have hs' : ∀ᶠ t in 𝓝[≠] (0 : ℝ), p 0 ≤ p t ∧ f t ≤ f 0 ∧ t ≠ 0 :=
    (hpmin.filter_mono nhdsWithin_le_nhds).and
      ((hm.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin)
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := hs'.exists
  have hpos : 0 < (s / 4) * t ^ 2 := mul_pos (by positivity) (sq_pos_of_ne_zero ht₃)
  dsimp [p] at ht₁
  linarith

private theorem basis3_with_first (d : Space) (hd : ‖d‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ Space, b 0 = d := by
  let v : Fin 3 → Space := fun _ => d
  let s : Set (Fin 3) := {0}
  have hs : Orthonormal ℝ (s.domRestrict v) := by
    let : Subsingleton s := ⟨fun i j => Subtype.ext
      (Set.subsingleton_singleton (a := (0 : Fin 3)) i.property j.property)⟩
    rw [orthonormal_subsingleton_iff]
    exact fun _ => hd
  obtain ⟨b, hb⟩ := hs.exists_orthonormalBasis_extension_of_card_eq
    (by simp [Space])
  exact ⟨b, hb 0 (by simp [s])⟩

private theorem le_one_of_solution {u : Space → ℝ} (hu : DeGiorgi.IsBoundedSolution u) (x₀ : Space) :
    u x₀ ≤ 1 := by
  by_contra! hgt
  obtain ⟨C, hC⟩ := hu.bounded
  have hCn : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  let δ := u x₀ - 1
  have hδ : 0 < δ := sub_pos.mpr hgt
  let ε := min (δ / (2 * (‖x₀‖ ^ 2 + 1))) (δ / 12)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  let F (x : Space) := u x - ε * ‖x‖ ^ 2
  have hFcont : Continuous F := by
    unfold F
    exact hu.regular.continuous.sub (continuous_const.mul (continuous_norm.pow 2))
  have hFx0 : 1 + δ / 2 ≤ F x₀ := by
    have h1 : ε * ‖x₀‖ ^ 2 ≤ δ / 2 := by
      calc
        ε * ‖x₀‖ ^ 2 ≤ ε * (‖x₀‖ ^ 2 + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
        _ ≤ (δ / (2 * (‖x₀‖ ^ 2 + 1))) * (‖x₀‖ ^ 2 + 1) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ = δ / 2 := by field_simp
    dsimp [F, δ] at h1 ⊢
    linarith
  let R := Real.sqrt ((C + 1) / ε)
  have hScomp : IsCompact (closedBall (0 : Space) R) := isCompact_closedBall _ _
  have h0mem : (0 : Space) ∈ closedBall (0 : Space) R := by
    rw [mem_closedBall, dist_self]
    exact Real.sqrt_nonneg _
  obtain ⟨x, _, hxmax⟩ := hScomp.exists_isMaxOn ⟨0, h0mem⟩ hFcont.continuousOn
  have hFglobal : ∀ y : Space, F y ≤ F x := by
    intro y
    by_cases hy : y ∈ closedBall (0 : Space) R
    · exact isMaxOn_iff.mp hxmax y hy
    · have hyn : R < ‖y‖ := by
        rw [mem_closedBall, dist_zero_right, not_le] at hy
        exact hy
      have hsq : (C + 1) / ε ≤ ‖y‖ ^ 2 := by
        have hR0 : 0 ≤ R := Real.sqrt_nonneg _
        have h1 : R ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ hR0 hyn.le 2
        rw [Real.sq_sqrt (by positivity)] at h1
        exact h1
      have hFy : F y ≤ -1 := by
        have h1 : C + 1 ≤ ε * ‖y‖ ^ 2 := by
          have := (div_le_iff₀ hε).mp hsq
          linarith
        have h2 : u y ≤ C := (abs_le.mp (hC y)).2
        dsimp [F]
        linarith
      have hx0mem : x₀ ∈ closedBall (0 : Space) R ∨ F x₀ ≤ -1 := by
        by_cases hx0 : x₀ ∈ closedBall (0 : Space) R
        · exact Or.inl hx0
        · right
          rw [mem_closedBall, dist_zero_right, not_le] at hx0
          have hsq0 : (C + 1) / ε ≤ ‖x₀‖ ^ 2 := by
            have h1 : R ^ 2 ≤ ‖x₀‖ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hx0.le 2
            rwa [Real.sq_sqrt (by positivity)] at h1
          have h1 : C + 1 ≤ ε * ‖x₀‖ ^ 2 := by
            have := (div_le_iff₀ hε).mp hsq0
            linarith
          have h2 : u x₀ ≤ C := (abs_le.mp (hC x₀)).2
          dsimp [F]
          linarith
      rcases hx0mem with hx0 | hbad
      · have hxge : 1 + δ / 2 ≤ F x := hFx0.trans (isMaxOn_iff.mp hxmax x₀ hx0)
        linarith
      · linarith
  have hux : 1 + δ / 2 ≤ u x := by
    have h1 : 1 + δ / 2 ≤ F x := hFx0.trans (hFglobal x₀)
    have h2 : 0 ≤ ε * ‖x‖ ^ 2 := by positivity
    dsimp [F] at h1
    linarith
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hsec (i : Fin 3) : second3 u x (b i) ≤ 2 * ε := by
    let d := b i
    have hd : ‖d‖ = 1 := b.orthonormal.norm_eq_one i
    let f (t : ℝ) := u (x + t • d) - (ε * ‖x‖ ^ 2 + (2 * ε * inner ℝ x d) * t + ε * t ^ 2)
    let g (t : ℝ) := fderiv ℝ u (x + t • d) d - (2 * ε * inner ℝ x d + 2 * ε * t)
    have hfeq (t : ℝ) : f t = F (x + t • d) := by
      dsimp [f, F]
      rw [norm_add_sq_real]
      simp only [norm_smul, hd, mul_one, Real.norm_eq_abs, sq_abs, real_inner_smul_right]
      ring
    have hloc : IsLocalMax f 0 :=
      Eventually.of_forall fun t => by rw [hfeq, hfeq]; simpa using hFglobal (x + t • d)
    have hf (t : ℝ) : HasDerivAt f (g t) t :=
      (line_deriv3 hu.regular x d t).sub (quadratic_deriv (ε * ‖x‖ ^ 2) (2 * ε * inner ℝ x d) ε t)
    have hg : HasDerivAt g (second3 u x d - 2 * ε) 0 :=
      (line_second3 hu.regular x d).sub (affine_deriv (2 * ε * inner ℝ x d) (2 * ε) 0)
    have hnp := local_max_second_nonpos hf hg hloc
    linarith
  have hlap : (Δ u) x ≤ 6 * ε := by
    rw [sum_second3 b x]
    linarith [hsec 0, hsec 1, hsec 2]
  have hcube : δ ≤ u x ^ 3 - u x := by
    have h1 : u x ^ 3 - u x = u x * (u x - 1) * (u x + 1) := by ring
    rw [h1]
    have ha : 1 ≤ u x := by linarith
    have hb : δ / 2 ≤ u x - 1 := by linarith
    have hc : 2 ≤ u x + 1 := by linarith
    have hab : δ / 2 ≤ u x * (u x - 1) := by nlinarith
    nlinarith
  have hpde : (Δ u) x = u x ^ 3 - u x := by linarith [hu.solution x]
  have h6ε : 6 * ε ≤ δ / 2 := by
    have := min_le_right (δ / (2 * (‖x₀‖ ^ 2 + 1))) (δ / 12)
    dsimp [ε]
    linarith
  linarith

private theorem abs_le_one_of_solution {u : Space → ℝ} (hu : DeGiorgi.IsBoundedSolution u)
    (x : Space) : |u x| ≤ 1 := by
  rw [abs_le]
  refine ⟨?_, le_one_of_solution hu x⟩
  have hneg : DeGiorgi.IsBoundedSolution (fun y => -u y) := by
    refine ⟨hu.regular.neg, ?_, ?_⟩
    · obtain ⟨C, hC⟩ := hu.bounded
      exact ⟨C, fun y => by simpa using hC y⟩
    · intro y
      have hlap : (Δ (fun z => -u z)) y = -(Δ u) y := by
        let b := EuclideanSpace.basisFun (Fin 3) ℝ
        rw [sum_second3 b y, sum_second3 b y]
        have hs (d : Space) : second3 (fun z => -u z) y d = -second3 u y d := by
          have h1 : fderiv ℝ (fun z => -u z) = fun z => -(fderiv ℝ u z) := by
            funext z
            exact fderiv_neg
          have h2 : fderiv ℝ (fderiv ℝ (fun z => -u z)) y = -(fderiv ℝ (fderiv ℝ u) y) := by
            rw [h1]
            exact fderiv_neg
          simp [second3, h2]
        rw [hs, hs, hs]
        ring
      rw [hlap]
      have := hu.solution y
      linarith
  have := le_one_of_solution hneg x
  linarith

private noncomputable def modulus (L r : ℝ) : ℝ := L * (2 * r - r ^ 2)

private noncomputable def gap3 (u : Space → ℝ) (L ε : ℝ) (p : Space × Space) : ℝ :=
  u p.2 - u p.1 - modulus L ‖p.2 - p.1‖ - ε * (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2)

private theorem gap3_continuous {u : Space → ℝ} (hu : Continuous u) (L ε : ℝ) :
    Continuous (gap3 u L ε) := by
  unfold gap3 modulus
  fun_prop

private theorem line_inequality3 {u : Space → ℝ} (hu : ContDiff ℝ 2 u)
    (L ε : ℝ) (x y d e : Space) (hd : ‖d‖ = 1) (he : ‖e‖ = 1)
    (k : ℝ)
    (hr : ∀ᶠ t : ℝ in 𝓝 0, ‖(y + t • e) - (x + t • d)‖ = ‖y - x‖ + k * t)
    (hm : IsLocalMax (fun t : ℝ => gap3 u L ε (x + t • d, y + t • e)) 0) :
    second3 u y e - second3 u x d ≤ 4 * ε - 2 * L * k ^ 2 := by
  let r := ‖y - x‖
  let a := modulus L r + ε * (‖x‖ ^ 2 + ‖y‖ ^ 2)
  let b := L * (2 * k - 2 * r * k) + ε * (2 * inner ℝ x d + 2 * inner ℝ y e)
  let c := 2 * ε - L * k ^ 2
  let F (t : ℝ) := u (y + t • e) - u (x + t • d) - (a + b * t + c * t ^ 2)
  let D (t : ℝ) := fderiv ℝ u (y + t • e) e - fderiv ℝ u (x + t • d) d - (b + 2 * c * t)
  have heq : (fun t : ℝ => gap3 u L ε (x + t • d, y + t • e)) =ᶠ[𝓝 0] F := by
    filter_upwards [hr] with t ht
    change u (y + t • e) - u (x + t • d) - modulus L ‖(y + t • e) - (x + t • d)‖ -
      ε * (‖x + t • d‖ ^ 2 + ‖y + t • e‖ ^ 2) = F t
    rw [ht, norm_add_sq_real, norm_add_sq_real]
    simp only [norm_smul, hd, he, mul_one, Real.norm_eq_abs, sq_abs, real_inner_smul_right]
    simp only [F, a, b, c, r, modulus]
    ring
  have hmF : IsLocalMax F 0 := hm.congr heq
  have hF (t : ℝ) : HasDerivAt F (D t) t :=
    ((line_deriv3 hu y e t).sub (line_deriv3 hu x d t)).sub (quadratic_deriv a b c t)
  have hD : HasDerivAt D (second3 u y e - second3 u x d - 2 * c) 0 :=
    ((line_second3 hu y e).sub (line_second3 hu x d)).sub
      (affine_deriv b (2 * c) 0)
  have hn := local_max_second_nonpos hF hD hmF
  dsimp [c] at hn
  linarith

private theorem gap3_nonpos {u : Space → ℝ} (hu : ContDiff ℝ 2 u)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hBound : ∀ x, |u x| ≤ C) (hLap : ∀ x, |(Δ u) x| ≤ M)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (p : Space × Space) (hp : ‖p.2 - p.1‖ ≤ 1) :
    gap3 u (2 * C + M + 2) ε p ≤ 0 := by
  let L := 2 * C + M + 2
  have hL : 0 < L := by dsimp [L]; linarith
  by_contra! hpos
  let S : Set (Space × Space) := {p | ‖p.2 - p.1‖ ≤ 1 ∧ 0 ≤ gap3 u L ε p}
  have hmem : p ∈ S := ⟨hp, hpos.le⟩
  have hdiff (x y : Space) : u y - u x ≤ 2 * C := by
    linarith [(abs_le.mp (hBound x)).1, (abs_le.mp (hBound y)).2]
  have hSclosed : IsClosed S :=
    (isClosed_le (continuous_snd.sub continuous_fst).norm continuous_const).inter
      (isClosed_le continuous_const (gap3_continuous hu.continuous L ε))
  let R := Real.sqrt (2 * C / ε)
  have hS : IsCompact S := by
    have hballs : IsCompact (closedBall (0 : Space) R ×ˢ closedBall (0 : Space) R) :=
      (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
    apply hballs.of_isClosed_subset hSclosed
    intro q hq
    rcases hq with ⟨hqd, hqg⟩
    have hr : 0 ≤ ‖q.2 - q.1‖ := norm_nonneg _
    have hmod : 0 ≤ modulus L ‖q.2 - q.1‖ :=
      mul_nonneg hL.le (by nlinarith)
    have hsum : ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 ≤ 2 * C / ε := by
      apply (le_div_iff₀ hε).2
      dsimp only [gap3] at hqg
      linarith [hdiff q.1 q.2]
    change q.1 ∈ closedBall 0 R ∧ q.2 ∈ closedBall 0 R
    constructor <;> rw [mem_closedBall, dist_zero_right] <;>
      apply Real.le_sqrt_of_sq_le <;> linarith [sq_nonneg ‖q.1‖, sq_nonneg ‖q.2‖]
  obtain ⟨⟨x, y⟩, ⟨hxy, _⟩, hmax⟩ := hS.exists_isMaxOn ⟨p, hmem⟩
    (gap3_continuous hu.continuous L ε).continuousOn
  have hpmax : 0 < gap3 u L ε (x, y) := hpos.trans_le (isMaxOn_iff.mp hmax p hmem)
  let r := ‖y - x‖
  have hr0 : 0 < r := by
    by_contra! hn
    have heq : y = x := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
    subst y
    have hpen : 0 ≤ ε * (‖x‖ ^ 2 + ‖x‖ ^ 2) := by positivity
    simp [gap3, modulus, not_lt_of_ge hpen] at hpmax
  have hr1 : r < 1 := by
    by_contra! hn
    have hr1 : r = 1 := le_antisymm hxy hn
    have hmod : modulus L ‖y - x‖ = L := by
      change modulus L r = L
      norm_num [modulus, hr1]
    have hp' : 0 < u y - u x - L - ε * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      simpa only [gap3, hmod] using hpmax
    have hpen : 0 ≤ ε * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by positivity
    dsimp [L] at hp'
    linarith [hdiff x y]
  have hlocal (d e : Space) :
      IsLocalMax (fun t : ℝ => gap3 u L ε (x + t • d, y + t • e)) 0 := by
    have hc : ContinuousAt (fun t : ℝ => ‖(y + t • e) - (x + t • d)‖) 0 := by fun_prop
    have hzero : ‖(y + (0 : ℝ) • e) - (x + (0 : ℝ) • d)‖ < 1 := by simpa using hr1
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, ‖(y + t • e) - (x + t • d)‖ < 1 :=
      hc (gt_mem_nhds hzero)
    change ∀ᶠ t : ℝ in 𝓝 0, gap3 u L ε (x + t • d, y + t • e) ≤
      gap3 u L ε (x + (0 : ℝ) • d, y + (0 : ℝ) • e)
    filter_upwards [hnear] with t ht
    simp only [zero_smul, add_zero]
    by_cases hg : 0 ≤ gap3 u L ε (x + t • d, y + t • e)
    · exact isMaxOn_iff.mp hmax _ ⟨ht.le, hg⟩
    · exact (lt_of_not_ge hg).le.trans hpmax.le
  let v : Space := r⁻¹ • (y - x)
  have hnv : ‖v‖ = 1 := by
    rw [show v = r⁻¹ • (y - x) by rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr0)]
    exact inv_mul_cancel₀ hr0.ne'
  have hvec : y - x = r • v := by
    simp [v, smul_smul, mul_inv_cancel₀ hr0.ne']
  obtain ⟨b, hb⟩ := basis3_with_first v hnv
  have hrad : ∀ᶠ t : ℝ in 𝓝 0, ‖(y + t • v) - (x + t • (-v))‖ = r + 2 * t := by
    have hC' : ContinuousAt (fun t : ℝ => r + 2 * t) 0 := by fun_prop
    have hpos0 : 0 < r + 2 * (0 : ℝ) := by simpa using hr0
    filter_upwards [hC' (lt_mem_nhds hpos0)] with t ht
    have he : (y + t • v) - (x + t • (-v)) = (y - x) + (2 * t) • v := by module
    rw [he, hvec, ← add_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hnv, mul_one]
  have hL0 := line_inequality3 hu L ε x y (-v) v (by simpa using hnv) hnv
    2 hrad (hlocal (-v) v)
  rw [second3_neg_dir, ← hb] at hL0
  have hparallel (k : Fin 3) :
      ∀ᶠ t : ℝ in 𝓝 0, ‖(y + t • b k) - (x + t • b k)‖ = ‖y - x‖ + 0 * t :=
    Eventually.of_forall fun t => by simp [add_sub_add_right_eq_sub]
  have hL1 := line_inequality3 hu L ε x y (b 1) (b 1) (b.orthonormal.norm_eq_one 1)
    (b.orthonormal.norm_eq_one 1) 0 (hparallel 1) (hlocal (b 1) (b 1))
  have hL2 := line_inequality3 hu L ε x y (b 2) (b 2) (b.orthonormal.norm_eq_one 2)
    (b.orthonormal.norm_eq_one 2) 0 (hparallel 2) (hlocal (b 2) (b 2))
  have htraceY := sum_second3 (u := u) b y
  have htraceX := sum_second3 (u := u) b x
  have htraceLower : -2 * M ≤ (Δ u) y - (Δ u) x := by
    linarith [(abs_le.mp (hLap y)).1, (abs_le.mp (hLap x)).2]
  norm_num at hL0 hL1 hL2
  dsimp only [L] at hL0
  linarith

private theorem modulus_bound3 {u : Space → ℝ} (hu : ContDiff ℝ 2 u)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hBound : ∀ x, |u x| ≤ C) (hLap : ∀ x, |(Δ u) x| ≤ M)
    (x y : Space) (hxy : ‖y - x‖ ≤ 1) :
    u y - u x ≤ (2 * (2 * C + M + 2)) * ‖y - x‖ := by
  let L := 2 * C + M + 2
  have hL : 0 ≤ L := by dsimp [L]; linarith
  suffices h : u y - u x ≤ modulus L ‖y - x‖ by
    have hs : 0 ≤ L * ‖y - x‖ ^ 2 := by positivity
    unfold modulus at h
    change u y - u x ≤ 2 * L * ‖y - x‖
    linarith
  by_contra! hh
  let δ := u y - u x - modulus L ‖y - x‖
  let E := ‖x‖ ^ 2 + ‖y‖ ^ 2
  have hδ : 0 < δ := sub_pos.mpr hh
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let ε := min 1 (δ / (E + 1) / 2)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεE : ε * E ≤ δ / 2 := by
    calc
      _ ≤ ε * (E + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ ≤ (δ / (E + 1) / 2) * (E + 1) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = _ := by field_simp
  have h := gap3_nonpos hu hC hM hBound hLap hε (min_le_left _ _) (x, y) hxy
  change δ - ε * E ≤ 0 at h
  linarith

private theorem grad_bound3 {u : Space → ℝ} (hu : ContDiff ℝ 2 u)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hBound : ∀ x, |u x| ≤ C) (hLap : ∀ x, |(Δ u) x| ≤ M) :
    ∀ x, ‖fderiv ℝ u x‖ ≤ 2 * (2 * C + M + 2) := by
  let D := 2 * (2 * C + M + 2)
  have hD : 0 ≤ D := by dsimp [D]; linarith
  intro x
  apply norm_fderiv_le_of_lip' ℝ hD
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
  have hyx : ‖y - x‖ ≤ 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hy.le
  have hxy : ‖x - y‖ ≤ 1 := by rwa [norm_sub_rev]
  have hp := modulus_bound3 hu hC hM hBound hLap x y hyx
  have hn := modulus_bound3 hu hC hM hBound hLap y x hxy
  rw [norm_sub_rev x y] at hn
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by dsimp [D]; linarith, hp⟩

private theorem lipschitz_of_fderiv_bound {u : Space → ℝ} (hu : Differentiable ℝ u)
    {D : ℝ} (hB : ∀ x, ‖fderiv ℝ u x‖ ≤ D) (x y : Space) :
    |u y - u x| ≤ D * ‖y - x‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ)
    (fun z _ => hu z) (fun z _ => hB z) convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa [Real.norm_eq_abs] using h

private theorem laplacian_shift {u : Space → ℝ} (hu : ContDiff ℝ 2 u) (s x : Space) :
    (Δ (fun y => u (y + s))) x = (Δ u) (x + s) := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  rw [sum_second3 b x, sum_second3 b (x + s)]
  have hs (d : Space) : second3 (fun y => u (y + s)) x d = second3 u (x + s) d := by
    have h1 : fderiv ℝ (fun y => u (y + s)) = fun y => fderiv ℝ u (y + s) := by
      funext y
      have hh := ((hu.differentiable (by norm_num) (y + s)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).add_const s)).fderiv
      change fderiv ℝ (fun z => u (z + s)) y =
        (fderiv ℝ u (y + s)).comp (ContinuousLinearMap.id ℝ Space) at hh
      simpa using hh
    have h2 : fderiv ℝ (fderiv ℝ (fun y => u (y + s))) x = fderiv ℝ (fderiv ℝ u) (x + s) := by
      rw [h1]
      have hF : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
      have hh := ((hF.differentiable one_ne_zero (x + s)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).add_const s)).fderiv
      change fderiv ℝ (fun z => fderiv ℝ u (z + s)) x =
        (fderiv ℝ (fderiv ℝ u) (x + s)).comp (ContinuousLinearMap.id ℝ Space) at hh
      simpa using hh
    simp [second3, h2]
  rw [hs, hs, hs]

private theorem laplacian_sub_smul {f g : Space → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (c : ℝ) (x : Space) :
    (Δ (fun y => c * (f y - g y))) x = c * ((Δ f) x - (Δ g) x) := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  rw [sum_second3 b x, sum_second3 b x, sum_second3 b x]
  have hs (d : Space) :
      second3 (fun y => c * (f y - g y)) x d = c * (second3 f x d - second3 g x d) := by
    have h1 : fderiv ℝ (fun y => c * (f y - g y)) =
        fun y => c • (fderiv ℝ f y - fderiv ℝ g y) := by
      funext y
      have hd1 := (hf.differentiable (by norm_num) y).hasFDerivAt
      have hd2 := (hg.differentiable (by norm_num) y).hasFDerivAt
      have hsm := (hd1.sub hd2).const_smul c
      change HasFDerivAt (fun z => c * (f z - g z)) (c • (fderiv ℝ f y - fderiv ℝ g y)) y at hsm
      exact hsm.fderiv
    have h2 : fderiv ℝ (fderiv ℝ (fun y => c * (f y - g y))) x =
        c • (fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x) := by
      rw [h1]
      have hF1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
      have hF2 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
      have hd1 := (hF1.differentiable one_ne_zero x).hasFDerivAt
      have hd2 := (hF2.differentiable one_ne_zero x).hasFDerivAt
      exact ((hd1.sub hd2).const_smul c).fderiv
    simp [second3, h2]
  rw [hs, hs, hs]
  ring

private noncomputable def e3 (i : Fin 3) : Space := EuclideanSpace.single i 1

private theorem norm_e3 (i : Fin 3) : ‖e3 i‖ = 1 := by
  simp [e3]

private noncomputable def part3 (u : Space → ℝ) (i : Fin 3) (x : Space) : ℝ :=
  fderiv ℝ u x (e3 i)

private noncomputable def part32 (u : Space → ℝ) (i j : Fin 3) (x : Space) : ℝ :=
  fderiv ℝ (part3 u i) x (e3 j)

private theorem solution_c21_bounds {u : Space → ℝ} (hu : DeGiorgi.IsBoundedSolution u) :
    ∃ D₁ D₂ D₃ : ℝ, 0 ≤ D₁ ∧ 0 ≤ D₂ ∧ 0 ≤ D₃ ∧
      (∀ x, |u x| ≤ 1) ∧
      (∀ x, ‖fderiv ℝ u x‖ ≤ D₁) ∧
      (∀ i x, |part3 u i x| ≤ D₁) ∧
      (∀ i x, ‖fderiv ℝ (part3 u i) x‖ ≤ D₂) ∧
      (∀ i j x, |part32 u i j x| ≤ D₂) ∧
      (∀ i j x y, |part32 u i j y - part32 u i j x| ≤ D₃ * ‖y - x‖) := by
  have h1 : ∀ x, |u x| ≤ 1 := abs_le_one_of_solution hu
  have hlap1 : ∀ x, |(Δ u) x| ≤ 2 := by
    intro x
    have hp : (Δ u) x = u x ^ 3 - u x := by linarith [hu.solution x]
    rw [hp]
    calc
      |u x ^ 3 - u x| ≤ |u x ^ 3| + |u x| := abs_sub _ _
      _ ≤ 1 ^ 3 + 1 := by
        rw [abs_pow]
        exact add_le_add (pow_le_pow_left₀ (abs_nonneg _) (h1 x) 3) (h1 x)
      _ = 2 := by norm_num
  let D₁ : ℝ := 2 * (2 * 1 + 2 + 2)
  have hD₁0 : 0 ≤ D₁ := by dsimp [D₁]; norm_num
  have hgrad1 : ∀ x, ‖fderiv ℝ u x‖ ≤ D₁ :=
    grad_bound3 hu.regular (by norm_num) (by norm_num) h1 hlap1
  have hlip1 : ∀ x y, |u y - u x| ≤ D₁ * ‖y - x‖ :=
    lipschitz_of_fderiv_bound (hu.regular.differentiable (by norm_num)) hgrad1
  have hpart1 (i : Fin 3) (x : Space) : |part3 u i x| ≤ D₁ := by
    calc
      |part3 u i x| = ‖fderiv ℝ u x (e3 i)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ u x‖ * ‖e3 i‖ := (fderiv ℝ u x).le_opNorm _
      _ ≤ D₁ := by rw [norm_e3, mul_one]; exact hgrad1 x
  -- First finite difference quotient w_h(x) = (u(x + h e_i) - u(x)) / h
  let D₂ : ℝ := 2 * (2 * D₁ + 4 * D₁ + 2)
  have hD₂0 : 0 ≤ D₂ := by dsimp [D₂]; linarith
  have hw1_bound (i : Fin 3) {h : ℝ} (hh : h ≠ 0) :
      let w := fun x : Space => h⁻¹ * (u (x + h • e3 i) - u x)
      (∀ x, |w x| ≤ D₁) ∧ (∀ x, |(Δ w) x| ≤ 4 * D₁) ∧
      (∀ x, ‖fderiv ℝ w x‖ ≤ D₂) ∧ (∀ x y, |w y - w x| ≤ D₂ * ‖y - x‖) := by
    intro w
    have hw_c2 : ContDiff ℝ 2 w :=
      contDiff_const.mul ((hu.regular.comp (contDiff_id.add contDiff_const)).sub hu.regular)
    have hwB : ∀ x, |w x| ≤ D₁ := by
      intro x
      dsimp [w]
      rw [abs_mul, abs_inv]
      have hsub := hlip1 x (x + h • e3 i)
      simp only [add_sub_cancel_left, norm_smul, norm_e3, mul_one, Real.norm_eq_abs] at hsub
      have hpos : 0 < |h| := abs_pos.mpr hh
      calc
        |h|⁻¹ * |u (x + h • e3 i) - u x| ≤ |h|⁻¹ * (D₁ * |h|) :=
          mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr hpos.le)
        _ = D₁ := by field_simp [hpos.ne']
    have hwLap : ∀ x, |(Δ w) x| ≤ 4 * D₁ := by
      intro x
      have hshift_c2 : ContDiff ℝ 2 (fun y : Space => u (y + h • e3 i)) :=
        hu.regular.comp (contDiff_id.add contDiff_const)
      have hL := laplacian_sub_smul hshift_c2 hu.regular h⁻¹ x
      rw [laplacian_shift hu.regular] at hL
      have hp1 : (Δ u) (x + h • e3 i) = u (x + h • e3 i) ^ 3 - u (x + h • e3 i) := by
        linarith [hu.solution (x + h • e3 i)]
      have hp2 : (Δ u) x = u x ^ 3 - u x := by linarith [hu.solution x]
      have hfac : (Δ w) x =
          (u (x + h • e3 i) ^ 2 + u (x + h • e3 i) * u x + u x ^ 2 - 1) * w x := by
        change (Δ (fun y => h⁻¹ * (u (y + h • e3 i) - u y))) x = _
        rw [hL, hp1, hp2]
        dsimp [w]
        ring
      rw [hfac, abs_mul]
      have hA : |u (x + h • e3 i) ^ 2 + u (x + h • e3 i) * u x + u x ^ 2 - 1| ≤ 4 := by
        have ha := h1 (x + h • e3 i)
        have hb := h1 x
        have hsqa : |u (x + h • e3 i) ^ 2| ≤ 1 := by
          rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) ha
        have hsqb : |u x ^ 2| ≤ 1 := by
          rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hb
        have hab : |u (x + h • e3 i) * u x| ≤ 1 := by
          rw [abs_mul]; exact mul_le_one₀ ha (abs_nonneg _) hb
        calc
          |u (x + h • e3 i) ^ 2 + u (x + h • e3 i) * u x + u x ^ 2 - 1|
              ≤ |u (x + h • e3 i) ^ 2 + u (x + h • e3 i) * u x + u x ^ 2| + |(1 : ℝ)| := abs_sub _ _
          _ ≤ |u (x + h • e3 i) ^ 2 + u (x + h • e3 i) * u x| + |u x ^ 2| + 1 := by
              rw [abs_one]
              linarith [abs_add_le (u (x + h • e3 i) ^ 2 + u (x + h • e3 i) * u x) (u x ^ 2)]
          _ ≤ |u (x + h • e3 i) ^ 2| + |u (x + h • e3 i) * u x| + |u x ^ 2| + 1 := by
              linarith [abs_add_le (u (x + h • e3 i) ^ 2) (u (x + h • e3 i) * u x)]
          _ ≤ 4 := by linarith
      exact mul_le_mul hA (hwB x) (abs_nonneg _) (by norm_num)
    have hwG : ∀ x, ‖fderiv ℝ w x‖ ≤ D₂ :=
      grad_bound3 hw_c2 hD₁0 (by positivity) hwB hwLap
    have hwL : ∀ x y, |w y - w x| ≤ D₂ * ‖y - x‖ :=
      lipschitz_of_fderiv_bound (hw_c2.differentiable (by norm_num)) hwG
    exact ⟨hwB, hwLap, hwG, hwL⟩
  have hpart1_lip (i : Fin 3) (x y : Space) : |part3 u i y - part3 u i x| ≤ D₂ * ‖y - x‖ := by
    have htend (z : Space) :
        Tendsto (fun h : ℝ => h⁻¹ * (u (z + h • e3 i) - u z)) (𝓝[≠] 0) (𝓝 (part3 u i z)) := by
      have hd := (line_deriv3 hu.regular z (e3 i) 0).tendsto_slope_zero
      simpa [part3, slope_def_field, div_eq_inv_mul, zero_smul, add_zero] using hd
    have hdiff : Tendsto (fun h : ℝ =>
        |h⁻¹ * (u (y + h • e3 i) - u y) - h⁻¹ * (u (x + h • e3 i) - u x)|)
        (𝓝[≠] 0) (𝓝 |part3 u i y - part3 u i x|) :=
      ((htend y).sub (htend x)).abs
    refine le_of_tendsto hdiff ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (hw1_bound i hh).2.2.2 x y
  have hgrad2 (i : Fin 3) (x : Space) : ‖fderiv ℝ (part3 u i) x‖ ≤ D₂ := by
    apply norm_fderiv_le_of_lip' ℝ hD₂0
    exact Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hpart1_lip i x y
  have hpart2 (i j : Fin 3) (x : Space) : |part32 u i j x| ≤ D₂ := by
    calc
      |part32 u i j x| = ‖fderiv ℝ (part3 u i) x (e3 j)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (part3 u i) x‖ * ‖e3 j‖ := (fderiv ℝ (part3 u i) x).le_opNorm _
      _ ≤ D₂ := by rw [norm_e3, mul_one]; exact hgrad2 i x
  -- Second finite difference quotient w_{h1, h2}
  let M₃ : ℝ := 6 * D₁ ^ 2 + 4 * D₂
  have hM₃0 : 0 ≤ M₃ := by dsimp [M₃]; positivity
  let D₃ : ℝ := 2 * (2 * D₂ + M₃ + 2)
  have hD₃0 : 0 ≤ D₃ := by dsimp [D₃]; linarith
  have hw2_lip (i j : Fin 3) {h₁ h₂ : ℝ} (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0) :
      let w1 := fun x : Space => h₁⁻¹ * (u (x + h₁ • e3 i) - u x)
      let w2 := fun x : Space => h₂⁻¹ * (w1 (x + h₂ • e3 j) - w1 x)
      ∀ x y, |w2 y - w2 x| ≤ D₃ * ‖y - x‖ := by
    intro w1 w2
    have hw1_c2 : ContDiff ℝ 2 w1 :=
      contDiff_const.mul ((hu.regular.comp (contDiff_id.add contDiff_const)).sub hu.regular)
    have hw2_c2 : ContDiff ℝ 2 w2 :=
      contDiff_const.mul ((hw1_c2.comp (contDiff_id.add contDiff_const)).sub hw1_c2)
    have ⟨hw1B, _, _, hw1L⟩ := hw1_bound i hh₁
    have hw2B : ∀ x, |w2 x| ≤ D₂ := by
      intro x
      dsimp [w2]
      rw [abs_mul, abs_inv]
      have hsub := hw1L x (x + h₂ • e3 j)
      simp only [add_sub_cancel_left, norm_smul, norm_e3, mul_one, Real.norm_eq_abs] at hsub
      have hpos : 0 < |h₂| := abs_pos.mpr hh₂
      calc
        |h₂|⁻¹ * |w1 (x + h₂ • e3 j) - w1 x| ≤ |h₂|⁻¹ * (D₂ * |h₂|) :=
          mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr hpos.le)
        _ = D₂ := by field_simp [hpos.ne']
    have hw2Lap : ∀ x, |(Δ w2) x| ≤ M₃ := by
      intro x
      let A := fun y : Space => u (y + h₁ • e3 i) ^ 2 + u (y + h₁ • e3 i) * u y + u y ^ 2 - 1
      have hΔw1 (y : Space) : (Δ w1) y = A y * w1 y := by
        have hsh : ContDiff ℝ 2 (fun z : Space => u (z + h₁ • e3 i)) :=
          hu.regular.comp (contDiff_id.add contDiff_const)
        have hL := laplacian_sub_smul hsh hu.regular h₁⁻¹ y
        rw [laplacian_shift hu.regular] at hL
        have hp1 : (Δ u) (y + h₁ • e3 i) = u (y + h₁ • e3 i) ^ 3 - u (y + h₁ • e3 i) := by
          linarith [hu.solution (y + h₁ • e3 i)]
        have hp2 : (Δ u) y = u y ^ 3 - u y := by linarith [hu.solution y]
        change (Δ (fun z => h₁⁻¹ * (u (z + h₁ • e3 i) - u z))) y = _
        rw [hL, hp1, hp2]
        dsimp [A, w1]
        ring
      have hsh2 : ContDiff ℝ 2 (fun z : Space => w1 (z + h₂ • e3 j)) :=
        hw1_c2.comp (contDiff_id.add contDiff_const)
      have hL2 := laplacian_sub_smul hsh2 hw1_c2 h₂⁻¹ x
      rw [laplacian_shift hw1_c2] at hL2
      have hfac : (Δ w2) x =
          h₂⁻¹ * (A (x + h₂ • e3 j) - A x) * w1 (x + h₂ • e3 j) + A x * w2 x := by
        change (Δ (fun z => h₂⁻¹ * (w1 (z + h₂ • e3 j) - w1 z))) x = _
        rw [hL2, hΔw1, hΔw1]
        dsimp [w2]
        ring
      have hAx : |A x| ≤ 4 := by
        have ha := h1 (x + h₁ • e3 i)
        have hb := h1 x
        have hsqa : |u (x + h₁ • e3 i) ^ 2| ≤ 1 := by
          rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) ha
        have hsqb : |u x ^ 2| ≤ 1 := by
          rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hb
        have hab : |u (x + h₁ • e3 i) * u x| ≤ 1 := by
          rw [abs_mul]; exact mul_le_one₀ ha (abs_nonneg _) hb
        dsimp [A]
        calc
          |u (x + h₁ • e3 i) ^ 2 + u (x + h₁ • e3 i) * u x + u x ^ 2 - 1|
              ≤ |u (x + h₁ • e3 i) ^ 2 + u (x + h₁ • e3 i) * u x + u x ^ 2| + |(1 : ℝ)| := abs_sub _ _
          _ ≤ |u (x + h₁ • e3 i) ^ 2| + |u (x + h₁ • e3 i) * u x| + |u x ^ 2| + 1 := by
              rw [abs_one]
              linarith [abs_add_le (u (x + h₁ • e3 i) ^ 2 + u (x + h₁ • e3 i) * u x) (u x ^ 2),
                abs_add_le (u (x + h₁ • e3 i) ^ 2) (u (x + h₁ • e3 i) * u x)]
          _ ≤ 4 := by linarith
      have hAdiff : |A (x + h₂ • e3 j) - A x| ≤ 6 * D₁ * |h₂| := by
        let a1 := u (x + h₂ • e3 j + h₁ • e3 i)
        let a0 := u (x + h₁ • e3 i)
        let b1 := u (x + h₂ • e3 j)
        let b0 := u x
        have ha_diff : |a1 - a0| ≤ D₁ * |h₂| := by
          have hs := hlip1 (x + h₁ • e3 i) (x + h₂ • e3 j + h₁ • e3 i)
          have heq : (x + h₂ • e3 j + h₁ • e3 i) - (x + h₁ • e3 i) = h₂ • e3 j := by module
          rw [heq, norm_smul, norm_e3, mul_one, Real.norm_eq_abs] at hs
          exact hs
        have hb_diff : |b1 - b0| ≤ D₁ * |h₂| := by
          have hs := hlip1 x (x + h₂ • e3 j)
          simp only [add_sub_cancel_left, norm_smul, norm_e3, mul_one, Real.norm_eq_abs] at hs
          exact hs
        have hident : A (x + h₂ • e3 j) - A x =
            (a1 + a0 + b1) * (a1 - a0) + (a0 + b1 + b0) * (b1 - b0) := by
          dsimp [A, a1, a0, b1, b0]
          ring
        rw [hident]
        have hc1 : |a1 + a0 + b1| ≤ 3 := by
          linarith [abs_add_le (a1 + a0) b1, abs_add_le a1 a0,
            h1 (x + h₂ • e3 j + h₁ • e3 i), h1 (x + h₁ • e3 i), h1 (x + h₂ • e3 j)]
        have hc2 : |a0 + b1 + b0| ≤ 3 := by
          linarith [abs_add_le (a0 + b1) b0, abs_add_le a0 b1,
            h1 (x + h₁ • e3 i), h1 (x + h₂ • e3 j), h1 x]
        calc
          |(a1 + a0 + b1) * (a1 - a0) + (a0 + b1 + b0) * (b1 - b0)|
              ≤ |(a1 + a0 + b1) * (a1 - a0)| + |(a0 + b1 + b0) * (b1 - b0)| := abs_add_le _ _
          _ = |a1 + a0 + b1| * |a1 - a0| + |a0 + b1 + b0| * |b1 - b0| := by rw [abs_mul, abs_mul]
          _ ≤ 3 * (D₁ * |h₂|) + 3 * (D₁ * |h₂|) :=
              add_le_add (mul_le_mul hc1 ha_diff (abs_nonneg _) (by norm_num))
                (mul_le_mul hc2 hb_diff (abs_nonneg _) (by norm_num))
          _ = 6 * D₁ * |h₂| := by ring
      have hpos2 : 0 < |h₂| := abs_pos.mpr hh₂
      have hterm1 : |h₂⁻¹ * (A (x + h₂ • e3 j) - A x) * w1 (x + h₂ • e3 j)| ≤ 6 * D₁ ^ 2 := by
        rw [abs_mul, abs_mul, abs_inv]
        have hq : |h₂|⁻¹ * |A (x + h₂ • e3 j) - A x| ≤ 6 * D₁ := by
          calc
            |h₂|⁻¹ * |A (x + h₂ • e3 j) - A x| ≤ |h₂|⁻¹ * (6 * D₁ * |h₂|) :=
              mul_le_mul_of_nonneg_left hAdiff (inv_nonneg.mpr hpos2.le)
            _ = 6 * D₁ := by field_simp [hpos2.ne']
        calc
          |h₂|⁻¹ * |A (x + h₂ • e3 j) - A x| * |w1 (x + h₂ • e3 j)|
              ≤ (6 * D₁) * D₁ := mul_le_mul hq (hw1B _) (abs_nonneg _) (by positivity)
          _ = 6 * D₁ ^ 2 := by ring
      have hterm2 : |A x * w2 x| ≤ 4 * D₂ := by
        rw [abs_mul]
        exact mul_le_mul hAx (hw2B x) (abs_nonneg _) (by norm_num)
      rw [hfac]
      calc
        _ ≤ |h₂⁻¹ * (A (x + h₂ • e3 j) - A x) * w1 (x + h₂ • e3 j)| + |A x * w2 x| := abs_add_le _ _
        _ ≤ M₃ := by dsimp [M₃]; linarith
    exact lipschitz_of_fderiv_bound (hw2_c2.differentiable (by norm_num))
      (grad_bound3 hw2_c2 hD₂0 hM₃0 hw2B hw2Lap)
  have hpart2_lip (i j : Fin 3) (x y : Space) :
      |part32 u i j y - part32 u i j x| ≤ D₃ * ‖y - x‖ := by
    have hstep1 {h₂ : ℝ} (hh₂ : h₂ ≠ 0) :
        |h₂⁻¹ * (part3 u i (y + h₂ • e3 j) - part3 u i y) -
         h₂⁻¹ * (part3 u i (x + h₂ • e3 j) - part3 u i x)| ≤ D₃ * ‖y - x‖ := by
      have htend (z : Space) :
          Tendsto (fun h₁ : ℝ => h₁⁻¹ * (u (z + h₁ • e3 i) - u z))
            (𝓝[≠] 0) (𝓝 (part3 u i z)) := by
        have hd := (line_deriv3 hu.regular z (e3 i) 0).tendsto_slope_zero
        simpa [part3, slope_def_field, div_eq_inv_mul, zero_smul, add_zero] using hd
      have ht : Tendsto (fun h₁ : ℝ =>
          |h₂⁻¹ * (h₁⁻¹ * (u (y + h₂ • e3 j + h₁ • e3 i) - u (y + h₂ • e3 j)) -
                   h₁⁻¹ * (u (y + h₁ • e3 i) - u y)) -
           h₂⁻¹ * (h₁⁻¹ * (u (x + h₂ • e3 j + h₁ • e3 i) - u (x + h₂ • e3 j)) -
                   h₁⁻¹ * (u (x + h₁ • e3 i) - u x))|)
          (𝓝[≠] 0)
          (𝓝 |h₂⁻¹ * (part3 u i (y + h₂ • e3 j) - part3 u i y) -
              h₂⁻¹ * (part3 u i (x + h₂ • e3 j) - part3 u i x)|) :=
        ((((htend (y + h₂ • e3 j)).sub (htend y)).const_mul h₂⁻¹).sub
         (((htend (x + h₂ • e3 j)).sub (htend x)).const_mul h₂⁻¹)).abs
      refine le_of_tendsto ht ?_
      filter_upwards [self_mem_nhdsWithin] with h₁ hh₁
      exact hw2_lip i j hh₁ hh₂ x y
    have hpart_c1 : ContDiff ℝ 1 (part3 u i) :=
      (hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
    have htend2 (z : Space) :
        Tendsto (fun h₂ : ℝ => h₂⁻¹ * (part3 u i (z + h₂ • e3 j) - part3 u i z))
          (𝓝[≠] 0) (𝓝 (part32 u i j z)) := by
      have hline : HasDerivAt (fun s : ℝ => part3 u i (z + s • e3 j)) (part32 u i j z) 0 := by
        have hl : HasDerivAt (fun s : ℝ => z + s • e3 j) (e3 j) 0 := by
          simpa using (((hasDerivAt_id (0 : ℝ)).smul_const (e3 j)).const_add z)
        have hd := (hpart_c1.differentiable one_ne_zero (z + (0 : ℝ) • e3 j)).hasFDerivAt.comp_hasDerivAt 0 hl
        rw [zero_smul, add_zero] at hd
        exact hd
      simpa [slope_def_field, div_eq_inv_mul, zero_smul, add_zero] using hline.tendsto_slope_zero
    have ht2 : Tendsto (fun h₂ : ℝ =>
        |h₂⁻¹ * (part3 u i (y + h₂ • e3 j) - part3 u i y) -
         h₂⁻¹ * (part3 u i (x + h₂ • e3 j) - part3 u i x)|)
        (𝓝[≠] 0) (𝓝 |part32 u i j y - part32 u i j x|) :=
      ((htend2 y).sub (htend2 x)).abs
    refine le_of_tendsto ht2 ?_
    filter_upwards [self_mem_nhdsWithin] with h₂ hh₂
    exact hstep1 hh₂
  exact ⟨D₁, D₂, D₃, hD₁0, hD₂0, hD₃0, h1, hgrad1, hpart1, hgrad2, hpart2, hpart2_lip⟩

/-
## Section 2: Diagonal Arzela-Ascoli and C^2_loc limit u_+ on R^2
-/

private theorem exists_subseq_compact_uniform_scalar
    {f : ℕ → Space → ℝ} {B L : ℝ} (_hB : 0 ≤ B) (hL : 0 ≤ L)
    (hBound : ∀ n x, |f n x| ≤ B)
    (hLip : ∀ n x y, |f n y - f n x| ≤ L * ‖y - x‖) :
    ∃ (φ : ℕ → ℕ) (g : Space → ℝ), StrictMono φ ∧ Continuous g ∧
      (∀ x, |g x| ≤ B) ∧ (∀ x y, |g y - g x| ≤ L * ‖y - x‖) ∧
      (∀ K : Set Space, IsCompact K → TendstoUniformlyOn (fun n => f (φ n)) g atTop K) := by
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq Space
  have hstep : ∀ (ψ : ℕ → ℕ) (k : ℕ), StrictMono ψ →
      ∃ (τ : ℕ → ℕ) (y : ℝ), StrictMono τ ∧
        Tendsto (fun n => f (ψ (τ n)) (q k)) atTop (𝓝 y) := by
    intro ψ k _
    have hmem : ∀ n, f (ψ n) (q k) ∈ Set.Icc (-B) B := fun n => abs_le.mp (hBound (ψ n) (q k))
    obtain ⟨y, _, τ, hτ, ht⟩ := isCompact_Icc.tendsto_subseq hmem
    exact ⟨τ, y, hτ, ht⟩
  let nextSub (ψ : ℕ → ℕ) (hψ : StrictMono ψ) (k : ℕ) :
      { τ : ℕ → ℕ // StrictMono τ ∧ ∃ y, Tendsto (fun n => f (ψ (τ n)) (q k)) atTop (𝓝 y) } :=
    ⟨Classical.choose (hstep ψ k hψ),
      (Classical.choose_spec (Classical.choose_spec (hstep ψ k hψ))).1,
      ⟨Classical.choose (Classical.choose_spec (hstep ψ k hψ)),
       (Classical.choose_spec (Classical.choose_spec (hstep ψ k hψ))).2⟩⟩
  let seq : ℕ → { ψ : ℕ → ℕ // StrictMono ψ } :=
    Nat.rec ⟨id, strictMono_id⟩ fun k prev =>
      let s := nextSub prev.1 prev.2 k
      ⟨prev.1 ∘ s.1, prev.2.comp s.2.1⟩
  have hseq_sub : ∀ k m, k ≤ m → ∃ τ : ℕ → ℕ, StrictMono τ ∧ (seq m).1 = (seq k).1 ∘ τ := by
    intro k m hkm
    induction hkm with
    | refl => exact ⟨id, strictMono_id, rfl⟩
    | @step m _ ih =>
      obtain ⟨τ, hτ, hEq⟩ := ih
      let s := nextSub (seq m).1 (seq m).2 m
      refine ⟨τ ∘ s.1, hτ.comp s.2.1, ?_⟩
      funext n
      change (seq m).1 (s.1 n) = (seq k).1 (τ (s.1 n))
      exact congrFun hEq (s.1 n)
  let φ : ℕ → ℕ := fun n => (seq n).1 n
  have hφ_mono : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    let s := nextSub (seq n).1 (seq n).2 n
    have h1 : n < s.1 (n + 1) := lt_of_lt_of_le (Nat.lt_succ_self n) (s.2.1.id_le (n + 1))
    exact (seq n).2 h1
  have hconv_q : ∀ k, ∃ y : ℝ, Tendsto (fun n => f (φ n) (q k)) atTop (𝓝 y) := by
    intro k
    let s := nextSub (seq k).1 (seq k).2 k
    obtain ⟨y, hy⟩ := s.2.2
    refine ⟨y, ?_⟩
    rw [Metric.tendsto_atTop] at hy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hy ε hε
    refine ⟨max N (k + 1), fun n hn => ?_⟩
    have hle : k + 1 ≤ n := le_of_max_le_right hn
    obtain ⟨τ, hτ, hEq⟩ := hseq_sub (k + 1) n hle
    have hval : φ n = (seq (k + 1)).1 (τ n) := by
      dsimp [φ]
      rw [hEq]
      rfl
    rw [hval]
    have hidx : N ≤ τ n := (le_of_max_le_left hn).trans (hτ.id_le n)
    exact hN (τ n) hidx
  have hcauchy : ∀ x : Space, CauchySeq (fun n => f (φ n) x) := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hδ : 0 < ε / (3 * (L + 1)) := by positivity
    obtain ⟨k, hk⟩ := hq.exists_dist_lt x hδ
    obtain ⟨y, hy⟩ := hconv_q k
    have hc : CauchySeq (fun n => f (φ n) (q k)) := hy.cauchySeq
    rw [Metric.cauchySeq_iff] at hc
    obtain ⟨N, hN⟩ := hc (ε / 3) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 : |f (φ m) x - f (φ m) (q k)| ≤ L * dist x (q k) := by
      simpa [dist_eq_norm, norm_sub_rev] using hLip (φ m) (q k) x
    have h2 : |f (φ n) x - f (φ n) (q k)| ≤ L * dist x (q k) := by
      simpa [dist_eq_norm, norm_sub_rev] using hLip (φ n) (q k) x
    have h3 : |f (φ m) (q k) - f (φ n) (q k)| < ε / 3 := by
      simpa [Real.dist_eq] using hN m hm n hn
    have hLdist : L * dist x (q k) < ε / 3 := by
      calc
        L * dist x (q k) ≤ (L + 1) * dist x (q k) :=
          mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
        _ < (L + 1) * (ε / (3 * (L + 1))) := by
          have hpos : 0 < L + 1 := by linarith
          exact mul_lt_mul_of_pos_left (by simpa [dist_comm] using hk) hpos
        _ = ε / 3 := by field_simp
    rw [Real.dist_eq]
    have htri : |f (φ m) x - f (φ n) x| ≤
        |f (φ m) x - f (φ m) (q k)| + |f (φ m) (q k) - f (φ n) (q k)| +
        |f (φ n) x - f (φ n) (q k)| := by
      calc
        |f (φ m) x - f (φ n) x| =
            |(f (φ m) x - f (φ m) (q k)) + ((f (φ m) (q k) - f (φ n) (q k)) -
              (f (φ n) x - f (φ n) (q k)))| := by ring_nf
        _ ≤ |f (φ m) x - f (φ m) (q k)| +
            |(f (φ m) (q k) - f (φ n) (q k)) - (f (φ n) x - f (φ n) (q k))| := abs_add_le _ _
        _ ≤ _ := by linarith [abs_sub (f (φ m) (q k) - f (φ n) (q k)) (f (φ n) x - f (φ n) (q k))]
    linarith
  let g : Space → ℝ := fun x => Classical.choose (cauchySeq_tendsto_of_complete (hcauchy x))
  have hg_tend : ∀ x, Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x)) :=
    fun x => Classical.choose_spec (cauchySeq_tendsto_of_complete (hcauchy x))
  have hgB : ∀ x, |g x| ≤ B := fun x =>
    le_of_tendsto (hg_tend x).abs (Eventually.of_forall fun n => hBound (φ n) x)
  have hgLip : ∀ x y, |g y - g x| ≤ L * ‖y - x‖ := fun x y =>
    le_of_tendsto ((hg_tend y).sub (hg_tend x)).abs (Eventually.of_forall fun n => hLip (φ n) x y)
  have hgCont : Continuous g := by
    rw [Metric.continuous_iff]
    intro x ε hε
    refine ⟨ε / (L + 1), by positivity, fun y hy => ?_⟩
    rw [Real.dist_eq]
    have h1 := hgLip x y
    rw [← dist_eq_norm] at h1
    calc
      |g y - g x| ≤ L * dist y x := h1
      _ ≤ (L + 1) * dist y x := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ < (L + 1) * (ε / (L + 1)) := mul_lt_mul_of_pos_left hy (by linarith)
      _ = ε := by field_simp
  refine ⟨φ, g, hφ_mono, hgCont, hgB, hgLip, ?_⟩
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ : 0 < ε / (3 * (L + 1)) := by positivity
  have hcov : K ⊆ ⋃ x ∈ K, Metric.ball x (ε / (3 * (L + 1))) :=
    fun x hx => Set.mem_biUnion hx (Metric.mem_ball_self hδ)
  obtain ⟨F, hFK, hFfin, hFcov⟩ := hK.elim_finite_subcover_image (fun x _ => Metric.isOpen_ball) hcov
  classical
  have hN_exists : ∀ x ∈ F, ∃ N : ℕ, ∀ n ≥ N, |g x - f (φ n) x| < ε / 3 := by
    intro x _
    have ht := (Metric.tendsto_atTop.mp (hg_tend x)) (ε / 3) (by linarith)
    obtain ⟨N, hN⟩ := ht
    exact ⟨N, fun n hn => by simpa [Real.dist_eq, abs_sub_comm] using hN n hn⟩
  let Nfin : Finset ℕ := hFfin.toFinset.image fun x =>
    if hx : x ∈ F then Classical.choose (hN_exists x hx) else 0
  let N := Nfin.sup id
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn x hxK => ?_⟩
  obtain ⟨y, hyF, hxy⟩ := Set.mem_iUnion₂.mp (hFcov hxK)
  have hNy : Classical.choose (hN_exists y hyF) ≤ N := by
    have hmem : Classical.choose (hN_exists y hyF) ∈ Nfin := by
      refine Finset.mem_image.mpr ⟨y, hFfin.mem_toFinset.mpr hyF, ?_⟩
      simp [hyF]
    exact Finset.le_sup (f := id) hmem
  have hcenter : |g y - f (φ n) y| < ε / 3 :=
    Classical.choose_spec (hN_exists y hyF) n (hNy.trans hn)
  have hdist : dist x y < ε / (3 * (L + 1)) := Metric.mem_ball.mp hxy
  have hLdist : L * dist x y < ε / 3 := by
    calc
      L * dist x y ≤ (L + 1) * dist x y := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ < (L + 1) * (ε / (3 * (L + 1))) := mul_lt_mul_of_pos_left hdist (by linarith)
      _ = ε / 3 := by field_simp
  have h1 : |g x - g y| ≤ L * dist x y := by simpa [dist_eq_norm] using hgLip y x
  have h2 : |f (φ n) x - f (φ n) y| ≤ L * dist x y := by
    simpa [dist_eq_norm] using hLip (φ n) y x
  rw [Real.dist_eq]
  have htri : |g x - f (φ n) x| ≤ |g x - g y| + |g y - f (φ n) y| + |f (φ n) x - f (φ n) y| := by
    calc
      |g x - f (φ n) x| = |(g x - g y) + ((g y - f (φ n) y) - (f (φ n) x - f (φ n) y))| := by
        ring_nf
      _ ≤ |g x - g y| + |(g y - f (φ n) y) - (f (φ n) x - f (φ n) y)| := abs_add_le _ _
      _ ≤ _ := by linarith [abs_sub (g y - f (φ n) y) (f (φ n) x - f (φ n) y)]
  linarith

private theorem exists_subseq_compact_uniform_fin :
    ∀ {m : ℕ} {f : ℕ → Fin m → Space → ℝ} {B L : ℝ}, 0 ≤ B → 0 ≤ L →
      (∀ n i x, |f n i x| ≤ B) →
      (∀ n i x y, |f n i y - f n i x| ≤ L * ‖y - x‖) →
      ∃ (φ : ℕ → ℕ) (g : Fin m → Space → ℝ), StrictMono φ ∧
        (∀ i, Continuous (g i)) ∧
        (∀ i x, |g i x| ≤ B) ∧
        (∀ i x y, |g i y - g i x| ≤ L * ‖y - x‖) ∧
        (∀ i (K : Set Space), IsCompact K →
          TendstoUniformlyOn (fun n => f (φ n) i) (g i) atTop K)
  | 0, _, _, _, _, _, _, _ =>
      ⟨id, Fin.elim0, strictMono_id, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0, fun i => i.elim0⟩
  | m + 1, f, B, L, hB, hL, hBound, hLip => by
      obtain ⟨φ₁, g₁, hφ₁, hg₁c, hg₁B, hg₁L, hg₁U⟩ :=
        exists_subseq_compact_uniform_fin (m := m) (f := fun n i => f n i.castSucc)
          hB hL (fun n i x => hBound n i.castSucc x) (fun n i x y => hLip n i.castSucc x y)
      obtain ⟨φ₂, g₂, hφ₂, hg₂c, hg₂B, hg₂L, hg₂U⟩ :=
        exists_subseq_compact_uniform_scalar hB hL
          (fun n x => hBound (φ₁ n) (Fin.last m) x)
          (fun n x y => hLip (φ₁ n) (Fin.last m) x y)
      refine ⟨φ₁ ∘ φ₂, Fin.snoc g₁ g₂, hφ₁.comp hφ₂, ?_, ?_, ?_, ?_⟩
      · intro i; refine Fin.lastCases ?_ ?_ i
        · simpa using hg₂c
        · intro j; simpa using hg₁c j
      · intro i x; refine Fin.lastCases ?_ ?_ i
        · simpa using hg₂B x
        · intro j; simpa using hg₁B j x
      · intro i x y; refine Fin.lastCases ?_ ?_ i
        · simpa using hg₂L x y
        · intro j; simpa using hg₁L j x y
      · intro i K hK; refine Fin.lastCases ?_ ?_ i
        · simpa using hg₂U K hK
        · intro j
          rw [Metric.tendstoUniformlyOn_iff]
          intro ε hε
          have h1 := Metric.tendstoUniformlyOn_iff.mp (hg₁U j K hK) ε hε
          simpa using hφ₂.tendsto_atTop.eventually h1

private noncomputable def e2 (i : Fin 2) : Plane := EuclideanSpace.single i 1

private theorem norm_e2 (i : Fin 2) : ‖e2 i‖ = 1 := by simp [e2]

private noncomputable def embed (t : ℝ) (y : Plane) : Space :=
  t • e3 0 + y 0 • e3 1 + y 1 • e3 2

private noncomputable def proj2 (x : Space) : Plane :=
  x 1 • e2 0 + x 2 • e2 1

private theorem embed_proj2 (x : Space) : embed (x 0) (proj2 x) = x := by
  ext i
  fin_cases i <;> simp [embed, proj2, e3, e2]

private theorem embed_add_e2 (t : ℝ) (y : Plane) (i : Fin 2) (s : ℝ) :
    embed t (y + s • e2 i) = embed t y + s • e3 i.succ := by
  ext k
  fin_cases i <;> fin_cases k <;> simp [embed, e3, e2]

private theorem embed_add_t (t s : ℝ) (y : Plane) :
    embed (t + s) y = embed t y + s • e3 0 := by
  ext k
  fin_cases k <;> simp [embed, e3]

private theorem continuous_embed_snd (t : ℝ) : Continuous (embed t) := by
  unfold embed
  fun_prop

private theorem norm_embed_sub (t₁ t₂ : ℝ) (y₁ y₂ : Plane) :
    ‖embed t₁ y₁ - embed t₂ y₂‖ ^ 2 = (t₁ - t₂) ^ 2 + ‖y₁ - y₂‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  have hc0 : (embed t₁ y₁ - embed t₂ y₂) 0 = t₁ - t₂ := by simp [embed, e3]
  have hc1 : (embed t₁ y₁ - embed t₂ y₂) 1 = (y₁ - y₂) 0 := by simp [embed, e3]
  have hc2 : (embed t₁ y₁ - embed t₂ y₂) 2 = (y₁ - y₂) 1 := by simp [embed, e3]
  rw [hc0, hc1, hc2]
  ring

private theorem contDiff_one_of_continuous_partials2 {f a₀ a₁ : Plane → ℝ}
    (ha₀ : Continuous a₀) (ha₁ : Continuous a₁)
    (hd₀ : ∀ y, HasDerivAt (fun s : ℝ => f (y + s • e2 0)) (a₀ y) 0)
    (hd₁ : ∀ y, HasDerivAt (fun s : ℝ => f (y + s • e2 1)) (a₁ y) 0) :
    ContDiff ℝ 1 f ∧
      ∀ y v, fderiv ℝ f y v = v 0 * a₀ y + v 1 * a₁ y := by
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  let c0 : Plane →L[ℝ] ℝ := (b.coord 0).toContinuousLinearMap
  let c1 : Plane →L[ℝ] ℝ := (b.coord 1).toContinuousLinearMap
  have hc0 (v : Plane) : c0 v = v 0 := by
    simp [c0, b, Module.Basis.coord_apply, EuclideanSpace.basisFun_repr]
  have hc1 (v : Plane) : c1 v = v 1 := by
    simp [c1, b, Module.Basis.coord_apply, EuclideanSpace.basisFun_repr]
  let L (y : Plane) : Plane →L[ℝ] ℝ := a₀ y • c0 + a₁ y • c1
  have hL_apply (y v : Plane) : L y v = v 0 * a₀ y + v 1 * a₁ y := by
    simp [L, hc0, hc1, mul_comm]
  have hshift0 (y : Plane) (t : ℝ) :
      HasDerivAt (fun s : ℝ => f (y + s • e2 0)) (a₀ (y + t • e2 0)) t := by
    have h2 : (fun s : ℝ => f (y + t • e2 0 + (s - t) • e2 0)) =
        fun s : ℝ => f (y + s • e2 0) := by
      funext s; congr 1; module
    have hsub : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
    have hd0' : HasDerivAt (fun s : ℝ => f (y + t • e2 0 + s • e2 0)) (a₀ (y + t • e2 0))
        (t - t) := by
      simpa [sub_self] using hd₀ (y + t • e2 0)
    have h3 := HasDerivAt.comp (h₂ := fun s : ℝ => f (y + t • e2 0 + s • e2 0))
      (h := fun s : ℝ => s - t) t hd0' hsub
    simpa [Function.comp_def, h2] using h3
  have hshift1 (y : Plane) (t : ℝ) :
      HasDerivAt (fun s : ℝ => f (y + s • e2 1)) (a₁ (y + t • e2 1)) t := by
    have h2 : (fun s : ℝ => f (y + t • e2 1 + (s - t) • e2 1)) =
        fun s : ℝ => f (y + s • e2 1) := by
      funext s; congr 1; module
    have hsub : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
    have hd1' : HasDerivAt (fun s : ℝ => f (y + t • e2 1 + s • e2 1)) (a₁ (y + t • e2 1))
        (t - t) := by
      simpa [sub_self] using hd₁ (y + t • e2 1)
    have h3 := HasDerivAt.comp (h₂ := fun s : ℝ => f (y + t • e2 1 + s • e2 1))
      (h := fun s : ℝ => s - t) t hd1' hsub
    simpa [Function.comp_def, h2] using h3
  have hFDeriv (y : Plane) : HasFDerivAt f (L y) y := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hcont0 : ContinuousAt a₀ y := ha₀.continuousAt
    have hcont1 : ContinuousAt a₁ y := ha₁.continuousAt
    obtain ⟨δ₀, hδ₀, hball0⟩ := Metric.continuousAt_iff.mp hcont0 (c / 2) (by linarith)
    obtain ⟨δ₁, hδ₁, hball1⟩ := Metric.continuousAt_iff.mp hcont1 (c / 2) (by linarith)
    let δ := min δ₀ δ₁
    have hδ : 0 < δ := lt_min hδ₀ hδ₁
    filter_upwards [Metric.ball_mem_nhds (0 : Plane) hδ] with v hv
    rw [Metric.mem_ball, dist_zero_right] at hv
    have hv0 : |v 0| ≤ ‖v‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v 0
    have hv1 : |v 1| ≤ ‖v‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v 1
    have hsplit : y + v = y + v 0 • e2 0 + v 1 • e2 1 := by
      ext i; fin_cases i <;> simp [e2]
    have hterm0 : |f (y + v 0 • e2 0) - f y - v 0 * a₀ y| ≤ (c / 2) * ‖v‖ := by
      by_cases h0 : v 0 = 0
      · simp [h0]; positivity
      · rcases lt_or_gt_of_ne h0 with hneg | hpos
        · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => f (y + s • e2 0))
            (fun s => a₀ (y + s • e2 0)) hneg
            (fun s _ => (hshift0 y s).continuousAt.continuousWithinAt)
            (fun s _ => hshift0 y s)
          have heq : f (y + v 0 • e2 0) - f y = v 0 * a₀ (y + ξ • e2 0) := by
            have hne : (0 : ℝ) - v 0 ≠ 0 := by linarith
            have := (eq_div_iff hne).mp hslope
            simp only [zero_smul, add_zero] at this
            linarith
          rw [heq, ← mul_sub, abs_mul]
          have hdist : dist (y + ξ • e2 0) y < δ₀ := by
            rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_e2, mul_one, Real.norm_eq_abs]
            have hξa : |ξ| ≤ |v 0| := by
              rw [abs_of_neg hneg, abs_le]
              exact ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
            exact lt_of_le_of_lt (hξa.trans hv0) (hv.trans_le (min_le_left _ _))
          have ha := hball0 hdist
          rw [Real.dist_eq] at ha
          calc
            |v 0| * |a₀ (y + ξ • e2 0) - a₀ y| ≤ ‖v‖ * (c / 2) :=
              mul_le_mul hv0 ha.le (abs_nonneg _) (norm_nonneg _)
            _ = (c / 2) * ‖v‖ := mul_comm _ _
        · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => f (y + s • e2 0))
            (fun s => a₀ (y + s • e2 0)) hpos
            (fun s _ => (hshift0 y s).continuousAt.continuousWithinAt)
            (fun s _ => hshift0 y s)
          have heq : f (y + v 0 • e2 0) - f y = v 0 * a₀ (y + ξ • e2 0) := by
            have hne : v 0 - 0 ≠ 0 := by linarith
            have := (eq_div_iff hne).mp hslope
            simp only [zero_smul, add_zero, sub_zero] at this
            linarith
          rw [heq, ← mul_sub, abs_mul]
          have hdist : dist (y + ξ • e2 0) y < δ₀ := by
            rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_e2, mul_one, Real.norm_eq_abs]
            have hξa : |ξ| ≤ |v 0| := by
              rw [abs_of_pos hpos, abs_of_pos hξ.1]
              exact hξ.2.le
            exact lt_of_le_of_lt (hξa.trans hv0) (hv.trans_le (min_le_left _ _))
          have ha := hball0 hdist
          rw [Real.dist_eq] at ha
          calc
            |v 0| * |a₀ (y + ξ • e2 0) - a₀ y| ≤ ‖v‖ * (c / 2) :=
              mul_le_mul hv0 ha.le (abs_nonneg _) (norm_nonneg _)
            _ = (c / 2) * ‖v‖ := mul_comm _ _
    have hterm1 : |f (y + v 0 • e2 0 + v 1 • e2 1) - f (y + v 0 • e2 0) - v 1 * a₁ y| ≤
        (c / 2) * ‖v‖ := by
      let y' := y + v 0 • e2 0
      by_cases h1 : v 1 = 0
      · simp [h1]; positivity
      · rcases lt_or_gt_of_ne h1 with hneg | hpos
        · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => f (y' + s • e2 1))
            (fun s => a₁ (y' + s • e2 1)) hneg
            (fun s _ => (hshift1 y' s).continuousAt.continuousWithinAt)
            (fun s _ => hshift1 y' s)
          have heq : f (y' + v 1 • e2 1) - f y' = v 1 * a₁ (y' + ξ • e2 1) := by
            have hne : (0 : ℝ) - v 1 ≠ 0 := by linarith
            have := (eq_div_iff hne).mp hslope
            simp only [zero_smul, add_zero] at this
            linarith
          change |f (y' + v 1 • e2 1) - f y' - v 1 * a₁ y| ≤ (c / 2) * ‖v‖
          rw [heq, ← mul_sub, abs_mul]
          have hdist : dist (y' + ξ • e2 1) y < δ₁ := by
            have hnorm_sq : ‖y' + ξ • e2 1 - y‖ ^ 2 ≤ ‖v‖ ^ 2 := by
              rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
              simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
              have hc0' : (y' + ξ • e2 1 - y) 0 = v 0 := by simp [y', e2]
              have hc1' : (y' + ξ • e2 1 - y) 1 = ξ := by simp [y', e2]
              rw [hc0', hc1']
              have hξsq : ξ ^ 2 ≤ v 1 ^ 2 := by nlinarith [hξ.1, hξ.2]
              linarith
            have hle : ‖y' + ξ • e2 1 - y‖ ≤ ‖v‖ := by
              nlinarith [norm_nonneg (y' + ξ • e2 1 - y), norm_nonneg v]
            rw [dist_eq_norm]
            exact lt_of_le_of_lt hle (hv.trans_le (min_le_right _ _))
          have ha := hball1 hdist
          rw [Real.dist_eq] at ha
          calc
            |v 1| * |a₁ (y' + ξ • e2 1) - a₁ y| ≤ ‖v‖ * (c / 2) :=
              mul_le_mul hv1 ha.le (abs_nonneg _) (norm_nonneg _)
            _ = (c / 2) * ‖v‖ := mul_comm _ _
        · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => f (y' + s • e2 1))
            (fun s => a₁ (y' + s • e2 1)) hpos
            (fun s _ => (hshift1 y' s).continuousAt.continuousWithinAt)
            (fun s _ => hshift1 y' s)
          have heq : f (y' + v 1 • e2 1) - f y' = v 1 * a₁ (y' + ξ • e2 1) := by
            have hne : v 1 - 0 ≠ 0 := by linarith
            have := (eq_div_iff hne).mp hslope
            simp only [zero_smul, add_zero, sub_zero] at this
            linarith
          change |f (y' + v 1 • e2 1) - f y' - v 1 * a₁ y| ≤ (c / 2) * ‖v‖
          rw [heq, ← mul_sub, abs_mul]
          have hdist : dist (y' + ξ • e2 1) y < δ₁ := by
            have hnorm_sq : ‖y' + ξ • e2 1 - y‖ ^ 2 ≤ ‖v‖ ^ 2 := by
              rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
              simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
              have hc0' : (y' + ξ • e2 1 - y) 0 = v 0 := by simp [y', e2]
              have hc1' : (y' + ξ • e2 1 - y) 1 = ξ := by simp [y', e2]
              rw [hc0', hc1']
              have hξsq : ξ ^ 2 ≤ v 1 ^ 2 := by nlinarith [hξ.1, hξ.2]
              linarith
            have hle : ‖y' + ξ • e2 1 - y‖ ≤ ‖v‖ := by
              nlinarith [norm_nonneg (y' + ξ • e2 1 - y), norm_nonneg v]
            rw [dist_eq_norm]
            exact lt_of_le_of_lt hle (hv.trans_le (min_le_right _ _))
          have ha := hball1 hdist
          rw [Real.dist_eq] at ha
          calc
            |v 1| * |a₁ (y' + ξ • e2 1) - a₁ y| ≤ ‖v‖ * (c / 2) :=
              mul_le_mul hv1 ha.le (abs_nonneg _) (norm_nonneg _)
            _ = (c / 2) * ‖v‖ := mul_comm _ _
    rw [Real.norm_eq_abs, hL_apply, hsplit]
    have htri : |f (y + v 0 • e2 0 + v 1 • e2 1) - f y - (v 0 * a₀ y + v 1 * a₁ y)| ≤
        |f (y + v 0 • e2 0 + v 1 • e2 1) - f (y + v 0 • e2 0) - v 1 * a₁ y| +
        |f (y + v 0 • e2 0) - f y - v 0 * a₀ y| := by
      calc
        |f (y + v 0 • e2 0 + v 1 • e2 1) - f y - (v 0 * a₀ y + v 1 * a₁ y)| =
            |(f (y + v 0 • e2 0 + v 1 • e2 1) - f (y + v 0 • e2 0) - v 1 * a₁ y) +
             (f (y + v 0 • e2 0) - f y - v 0 * a₀ y)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith
  have hfderiv_eq : fderiv ℝ f = L := funext fun y => (hFDeriv y).fderiv
  have hcontL : Continuous L := (ha₀.smul continuous_const).add (ha₁.smul continuous_const)
  have hc1' : ContDiff ℝ 1 f := by
    rw [contDiff_one_iff_fderiv]
    exact ⟨fun y => (hFDeriv y).differentiableAt, hfderiv_eq ▸ hcontL⟩
  exact ⟨hc1', fun y v => by rw [hfderiv_eq, hL_apply]⟩

private theorem contDiff_two_of_partials2 {f a₀ a₁ b₀₀ b₀₁ b₁₀ b₁₁ : Plane → ℝ}
    (hb₀₀ : Continuous b₀₀) (hb₀₁ : Continuous b₀₁)
    (hb₁₀ : Continuous b₁₀) (hb₁₁ : Continuous b₁₁)
    (hd₀ : ∀ y, HasDerivAt (fun s : ℝ => f (y + s • e2 0)) (a₀ y) 0)
    (hd₁ : ∀ y, HasDerivAt (fun s : ℝ => f (y + s • e2 1)) (a₁ y) 0)
    (hd₀₀ : ∀ y, HasDerivAt (fun s : ℝ => a₀ (y + s • e2 0)) (b₀₀ y) 0)
    (hd₀₁ : ∀ y, HasDerivAt (fun s : ℝ => a₀ (y + s • e2 1)) (b₀₁ y) 0)
    (hd₁₀ : ∀ y, HasDerivAt (fun s : ℝ => a₁ (y + s • e2 0)) (b₁₀ y) 0)
    (hd₁₁ : ∀ y, HasDerivAt (fun s : ℝ => a₁ (y + s • e2 1)) (b₁₁ y) 0) :
    ContDiff ℝ 2 f ∧
      (∀ y v, fderiv ℝ f y v = v 0 * a₀ y + v 1 * a₁ y) ∧
      (∀ y, (Δ f) y = b₀₀ y + b₁₁ y) := by
  obtain ⟨ha₀c1, ha₀fd⟩ := contDiff_one_of_continuous_partials2 hb₀₀ hb₀₁ hd₀₀ hd₀₁
  obtain ⟨ha₁c1, ha₁fd⟩ := contDiff_one_of_continuous_partials2 hb₁₀ hb₁₁ hd₁₀ hd₁₁
  obtain ⟨hfc1, hffd⟩ := contDiff_one_of_continuous_partials2 ha₀c1.continuous ha₁c1.continuous hd₀ hd₁
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  let c0 : Plane →L[ℝ] ℝ := (b.coord 0).toContinuousLinearMap
  let c1 : Plane →L[ℝ] ℝ := (b.coord 1).toContinuousLinearMap
  have hc0 (v : Plane) : c0 v = v 0 := by
    simp [c0, b, Module.Basis.coord_apply, EuclideanSpace.basisFun_repr]
  have hc1 (v : Plane) : c1 v = v 1 := by
    simp [c1, b, Module.Basis.coord_apply, EuclideanSpace.basisFun_repr]
  have hfd_eq : fderiv ℝ f = fun y => a₀ y • c0 + a₁ y • c1 := by
    funext y
    ext v
    simp [hffd y v, hc0, hc1, mul_comm]
  have hfc2 : ContDiff ℝ 2 f := by
    rw [show (2 : WithTop ℕ∞) = (1 : ℕ) + 1 by norm_num, contDiff_succ_iff_fderiv]
    refine ⟨hfc1.differentiable one_ne_zero, by simp, ?_⟩
    rw [hfd_eq]
    exact (ha₀c1.smul contDiff_const).add (ha₁c1.smul contDiff_const)
  have hlap (y : Plane) : (Δ f) y = b₀₀ y + b₁₁ y := by
    let ob := EuclideanSpace.basisFun (Fin 2) ℝ
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f ob]
    simp only [Fin.sum_univ_two, iteratedFDeriv_two_apply]
    have hob0 : ob 0 = e2 0 := EuclideanSpace.basisFun_apply (Fin 2) ℝ 0
    have hob1 : ob 1 = e2 1 := EuclideanSpace.basisFun_apply (Fin 2) ℝ 1
    rw [hob0, hob1]
    have h0 : (fderiv ℝ (fderiv ℝ f) y (e2 0)) (e2 0) = b₀₀ y := by
      have hpa : fderiv ℝ (fun z => fderiv ℝ f z (e2 0)) y (e2 0) =
          (fderiv ℝ (fderiv ℝ f) y (e2 0)) (e2 0) := by
        rw [fderiv_clm_apply ((hfc2.fderiv_right (by norm_num)).differentiable one_ne_zero y)
          (differentiableAt_const (e2 0))]
        simp
      rw [← hpa]
      have hfun : (fun z => fderiv ℝ f z (e2 0)) = a₀ := by
        funext z; rw [hffd z (e2 0)]; simp [e2]
      rw [hfun, ha₀fd y (e2 0)]
      simp [e2]
    have h1 : (fderiv ℝ (fderiv ℝ f) y (e2 1)) (e2 1) = b₁₁ y := by
      have hpa : fderiv ℝ (fun z => fderiv ℝ f z (e2 1)) y (e2 1) =
          (fderiv ℝ (fderiv ℝ f) y (e2 1)) (e2 1) := by
        rw [fderiv_clm_apply ((hfc2.fderiv_right (by norm_num)).differentiable one_ne_zero y)
          (differentiableAt_const (e2 1))]
        simp
      rw [← hpa]
      have hfun : (fun z => fderiv ℝ f z (e2 1)) = a₁ := by
        funext z; rw [hffd z (e2 1)]; simp [e2]
      rw [hfun, ha₁fd y (e2 1)]
      simp [e2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h0, h1]
  exact ⟨hfc2, hffd, hlap⟩

private noncomputable def doubleWell (s : ℝ) : ℝ := (1 - s ^ 2) ^ 2 / 4

private theorem doubleWell_nonneg (s : ℝ) : 0 ≤ doubleWell s := by
  unfold doubleWell
  positivity

private theorem doubleWell_le_quarter {s : ℝ} (hs : |s| ≤ 1) : doubleWell s ≤ 1 / 4 := by
  unfold doubleWell
  have hsq : s ^ 2 ≤ 1 := by
    have := sq_le_sq.mpr (show |s| ≤ |1| by simpa using hs)
    simpa using this
  have h0 : 0 ≤ 1 - s ^ 2 := by linarith
  have h1 : 1 - s ^ 2 ≤ 1 := by nlinarith
  nlinarith

private theorem exists_limit_profile {u : Space → ℝ}
    (hu : DeGiorgi.IsBoundedSolution u) (hup : DeGiorgi.HasPositiveDeriv u) :
    ∃ (t : ℕ → ℝ) (u_plus : Plane → ℝ),
      (∀ n, 0 < t n) ∧
      Tendsto t atTop atTop ∧
      DeGiorgi.IsBoundedSolution u_plus ∧
      (∀ y, |u_plus y| ≤ 1) ∧
      (∀ K : Set Space, IsCompact K →
        TendstoUniformlyOn (fun n x => u (x + t n • e3 0)) (fun x => u_plus (proj2 x)) atTop K) ∧
      (∀ i : Fin 2, ∀ K : Set Space, IsCompact K →
        TendstoUniformlyOn (fun n x => part3 u i.succ (x + t n • e3 0))
          (fun x => fderiv ℝ u_plus (proj2 x) (e2 i)) atTop K) ∧
      (∀ K : Set Space, IsCompact K →
        TendstoUniformlyOn (fun n x => part3 u 0 (x + t n • e3 0)) (fun _ => (0 : ℝ)) atTop K) := by
  obtain ⟨D₁, D₂, D₃, hD₁, hD₂, hD₃, h1, hgrad1, hpart1, hgrad2, hpart2, hpart2_lip⟩ :=
    solution_c21_bounds hu
  have hlip1 : ∀ x y, |u y - u x| ≤ D₁ * ‖y - x‖ :=
    lipschitz_of_fderiv_bound (hu.regular.differentiable (by norm_num)) hgrad1
  have hlip_p1 (i : Fin 3) : ∀ x y, |part3 u i y - part3 u i x| ≤ D₂ * ‖y - x‖ :=
    lipschitz_of_fderiv_bound
      (((hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const).differentiable one_ne_zero)
      (hgrad2 i)
  let B := max 1 (max D₁ D₂)
  let L := max D₁ (max D₂ D₃)
  have hB : 0 ≤ B := le_trans (by norm_num) (le_max_left _ _)
  have hL : 0 ≤ L := le_trans hD₁ (le_max_left _ _)
  -- Pack u (0), part3 u 0..2 (1..3), part32 u i j (4 + 3*i + j)
  let pack (n : ℕ) (idx : Fin 13) (x : Space) : ℝ :=
    let s := ((n + 1 : ℕ) : ℝ) • e3 0
    match idx.val with
    | 0 => u (x + s)
    | 1 => part3 u 0 (x + s)
    | 2 => part3 u 1 (x + s)
    | 3 => part3 u 2 (x + s)
    | 4 => part32 u 0 0 (x + s)
    | 5 => part32 u 0 1 (x + s)
    | 6 => part32 u 0 2 (x + s)
    | 7 => part32 u 1 0 (x + s)
    | 8 => part32 u 1 1 (x + s)
    | 9 => part32 u 1 2 (x + s)
    | 10 => part32 u 2 0 (x + s)
    | 11 => part32 u 2 1 (x + s)
    | _ => part32 u 2 2 (x + s)
  have hpackB : ∀ n idx x, |pack n idx x| ≤ B := by
    intro n idx x
    fin_cases idx <;> dsimp [pack, B]
    · exact (h1 _).trans (le_max_left _ _)
    · exact (hpart1 0 _).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hpart1 1 _).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hpart1 2 _).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hpart2 0 0 _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (hpart2 0 1 _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (hpart2 0 2 _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (hpart2 1 0 _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (hpart2 1 1 _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (hpart2 1 2 _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (hpart2 2 0 _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (hpart2 2 1 _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (hpart2 2 2 _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hpackL : ∀ n idx x y, |pack n idx y - pack n idx x| ≤ L * ‖y - x‖ := by
    intro n idx x y
    let s : Space := ((n + 1 : ℕ) : ℝ) • e3 0
    have hsub : (y + s) - (x + s) = y - x := by module
    have hL1 : D₁ ≤ L := le_max_left _ _
    have hL2 : D₂ ≤ L := (le_max_left _ _).trans (le_max_right _ _)
    have hL3 : D₃ ≤ L := (le_max_right _ _).trans (le_max_right _ _)
    fin_cases idx <;> dsimp [pack]
    · exact le_trans (by simpa [s, hsub] using hlip1 (x + s) (y + s))
        (mul_le_mul_of_nonneg_right hL1 (norm_nonneg _))
    · exact le_trans (by simpa [s, hsub] using hlip_p1 0 (x + s) (y + s))
        (mul_le_mul_of_nonneg_right hL2 (norm_nonneg _))
    · exact le_trans (by simpa [s, hsub] using hlip_p1 1 (x + s) (y + s))
        (mul_le_mul_of_nonneg_right hL2 (norm_nonneg _))
    · exact le_trans (by simpa [s, hsub] using hlip_p1 2 (x + s) (y + s))
        (mul_le_mul_of_nonneg_right hL2 (norm_nonneg _))
    · exact le_trans (by simpa [s, hsub] using hpart2_lip 0 0 (x + s) (y + s))
        (mul_le_mul_of_nonneg_right hL3 (norm_nonneg _))
    · exact le_trans (by simpa [s, hsub] using hpart2_lip 0 1 (x + s) (y + s))
        (mul_le_mul_of_nonneg_right hL3 (norm_nonneg _))
    · exact le_trans (by simpa [s, hsub] using hpart2_lip 0 2 (x + s) (y + s))
        (mul_le_mul_of_nonneg_right hL3 (norm_nonneg _))
    · exact le_trans (by simpa [s, hsub] using hpart2_lip 1 0 (x + s) (y + s))
        (mul_le_mul_of_nonneg_right hL3 (norm_nonneg _))
    · exact le_trans (by simpa [s, hsub] using hpart2_lip 1 1 (x + s) (y + s))
        (mul_le_mul_of_nonneg_right hL3 (norm_nonneg _))
    · exact le_trans (by simpa [s, hsub] using hpart2_lip 1 2 (x + s) (y + s))
        (mul_le_mul_of_nonneg_right hL3 (norm_nonneg _))
    · exact le_trans (by simpa [s, hsub] using hpart2_lip 2 0 (x + s) (y + s))
        (mul_le_mul_of_nonneg_right hL3 (norm_nonneg _))
    · exact le_trans (by simpa [s, hsub] using hpart2_lip 2 1 (x + s) (y + s))
        (mul_le_mul_of_nonneg_right hL3 (norm_nonneg _))
    · exact le_trans (by simpa [s, hsub] using hpart2_lip 2 2 (x + s) (y + s))
        (mul_le_mul_of_nonneg_right hL3 (norm_nonneg _))
  obtain ⟨φ, G, hφ, hGc, hGB, _, hGU⟩ :=
    exists_subseq_compact_uniform_fin hB hL hpackB hpackL
  let t : ℕ → ℝ := fun n => ((φ n + 1 : ℕ) : ℝ)
  have ht_pos : ∀ n, 0 < t n := fun n => by dsimp [t]; positivity
  have ht_top : Tendsto t atTop atTop := by
    have h1' : Tendsto (fun n => (φ n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
    simpa [t, Nat.cast_add, Nat.cast_one] using h1'.atTop_add tendsto_const_nhds
  -- Monotonicity in e3 0 implies G 0 x is independent of x 0
  have hmono_x0 (y : Plane) : StrictMono (fun s : ℝ => u (embed s y)) := by
    apply strictMono_of_deriv_pos
    intro s
    have hderiv : HasDerivAt (fun r : ℝ => u (embed r y)) (part3 u 0 (embed s y)) s := by
      have h1' := (line_deriv3 hu.regular (embed 0 y) (e3 0) s)
      have heq : (fun r : ℝ => u (embed 0 y + r • e3 0)) = fun r => u (embed r y) := by
        funext r; congr 1; rw [← embed_add_t, zero_add]
      rw [heq] at h1'
      simpa [part3, ← embed_add_t, zero_add] using h1'
    rw [hderiv.deriv]
    have hpos := hup (embed s y)
    rw [(hu.regular.differentiable (by norm_num) (embed s y)).lineDeriv_eq_fderiv] at hpos
    exact hpos
  have hG0_indep (x : Space) : G 0 x = G 0 (embed 0 (proj2 x)) := by
    let y := proj2 x
    have hbdd : BddAbove (Set.range fun s : ℝ => u (embed s y)) :=
      ⟨1, by rintro _ ⟨s, rfl⟩; exact (abs_le.mp (h1 _)).2⟩
    have htend_sup : Tendsto (fun s : ℝ => u (embed s y)) atTop (𝓝 (⨆ s : ℝ, u (embed s y))) :=
      tendsto_atTop_ciSup (hmono_x0 y).monotone hbdd
    have h1' : Tendsto (fun n => u (x + t n • e3 0)) atTop (𝓝 (G 0 x)) :=
      (hGU 0 {x} isCompact_singleton).tendsto_at (Set.mem_singleton x)
    have h2' : Tendsto (fun n => u (embed 0 y + t n • e3 0)) atTop (𝓝 (G 0 (embed 0 y))) :=
      (hGU 0 {embed 0 y} isCompact_singleton).tendsto_at (Set.mem_singleton _)
    have h1'' : Tendsto (fun n => u (x + t n • e3 0)) atTop (𝓝 (⨆ s : ℝ, u (embed s y))) := by
      have heq : (fun n => u (x + t n • e3 0)) = fun n => u (embed (x 0 + t n) y) := by
        funext n
        congr 1
        rw [embed_add_t, embed_proj2]
      rw [heq]
      exact htend_sup.comp (tendsto_const_nhds.add_atTop ht_top)
    have h2'' : Tendsto (fun n => u (embed 0 y + t n • e3 0)) atTop
        (𝓝 (⨆ s : ℝ, u (embed s y))) := by
      have heq : (fun n => u (embed 0 y + t n • e3 0)) = fun n => u (embed (t n) y) := by
        funext n; congr 1; rw [← embed_add_t, zero_add]
      rw [heq]
      exact htend_sup.comp ht_top
    exact (tendsto_nhds_unique h1' h1'').trans (tendsto_nhds_unique h2' h2'').symm
  -- Helper: uniform convergence on lines gives directional derivatives of limits
  have hline_deriv_lim (idx₀ idx₁ : Fin 13) (d : Space)
      (hfn : ∀ n (x : Space) (s : ℝ),
        HasDerivAt (fun r : ℝ => pack (φ n) idx₀ (x + r • d)) (pack (φ n) idx₁ (x + s • d)) s)
      (x : Space) :
      HasDerivAt (fun r : ℝ => G idx₀ (x + r • d)) (G idx₁ x) 0 := by
    have hloc : TendstoLocallyUniformlyOn
        (fun n (r : ℝ) => pack (φ n) idx₁ (x + r • d))
        (fun r : ℝ => G idx₁ (x + r • d)) atTop Set.univ := by
      rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
      intro K _ hK
      have hKimg : IsCompact ((fun r : ℝ => x + r • d) '' K) :=
        hK.image (continuous_const.add (continuous_id.smul continuous_const))
      have huK := hGU idx₁ _ hKimg
      rw [Metric.tendstoUniformlyOn_iff] at huK ⊢
      intro ε hε
      filter_upwards [huK ε hε] with n hn r hr
      exact hn (x + r • d) ⟨r, hr, rfl⟩
    have hpt : ∀ r ∈ (Set.univ : Set ℝ),
        Tendsto (fun n => pack (φ n) idx₀ (x + r • d)) atTop (𝓝 (G idx₀ (x + r • d))) :=
      fun r _ => (hGU idx₀ {x + r • d} isCompact_singleton).tendsto_at (Set.mem_singleton _)
    have h := hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ hloc
      (Eventually.of_forall fun n r _ => hfn n x r) hpt (Set.mem_univ (0 : ℝ))
    have h0 : x + (0 : ℝ) • d = x := by simp
    rwa [h0] at h
  -- G 1 = 0 everywhere, and G 4 = 0 everywhere
  have hG1_zero : ∀ x : Space, G 1 x = 0 := by
    intro x
    have hd := hline_deriv_lim 0 1 (e3 0) (fun n z s => by
      have h := line_deriv3 hu.regular (z + t n • e3 0) (e3 0) s
      have heq : (fun r : ℝ => u (z + t n • e3 0 + r • e3 0)) =
          fun r => u (z + r • e3 0 + t n • e3 0) := by
        funext r; congr 1; module
      rw [heq] at h
      have heq2 : z + t n • e3 0 + s • e3 0 = z + s • e3 0 + t n • e3 0 := by module
      rw [heq2] at h
      exact h) x
    have hconst : (fun r : ℝ => G 0 (x + r • e3 0)) = fun _ => G 0 (embed 0 (proj2 x)) := by
      funext r
      rw [hG0_indep]
      congr 2
      ext k; fin_cases k <;> simp [proj2, e3, e2]
    rw [hconst] at hd
    exact hd.unique (hasDerivAt_const (0 : ℝ) (G 0 (embed 0 (proj2 x))))
  have hG4_zero : ∀ x : Space, G 4 x = 0 := by
    intro x
    have hd := hline_deriv_lim 1 4 (e3 0) (fun n z s => by
      have hpc : ContDiff ℝ 1 (part3 u 0) :=
        (hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
      have hl : HasDerivAt (fun r : ℝ => z + r • e3 0 + t n • e3 0) (e3 0) s := by
        have h1' := (((hasDerivAt_id s).smul_const (e3 0)).const_add z).add_const (t n • e3 0)
        simpa using h1'
      exact (hpc.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt s hl) x
    have hconst : (fun r : ℝ => G 1 (x + r • e3 0)) = fun _ => (0 : ℝ) :=
      funext fun r => hG1_zero _
    rw [hconst] at hd
    exact hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  -- Define u_plus on Plane and its partials
  let u_plus : Plane → ℝ := fun y => G 0 (embed 0 y)
  let a₀ : Plane → ℝ := fun y => G 2 (embed 0 y)
  let a₁ : Plane → ℝ := fun y => G 3 (embed 0 y)
  let b₀₀ : Plane → ℝ := fun y => G 8 (embed 0 y)
  let b₀₁ : Plane → ℝ := fun y => G 9 (embed 0 y)
  let b₁₀ : Plane → ℝ := fun y => G 11 (embed 0 y)
  let b₁₁ : Plane → ℝ := fun y => G 12 (embed 0 y)
  have hpart_deriv (idx₀ idx₁ : Fin 13) (i : Fin 2)
      (hfn : ∀ n (x : Space) (s : ℝ),
        HasDerivAt (fun r : ℝ => pack (φ n) idx₀ (x + r • e3 i.succ))
          (pack (φ n) idx₁ (x + s • e3 i.succ)) s)
      (y : Plane) :
      HasDerivAt (fun r : ℝ => G idx₀ (embed 0 (y + r • e2 i))) (G idx₁ (embed 0 y)) 0 := by
    have h := hline_deriv_lim idx₀ idx₁ (e3 i.succ) hfn (embed 0 y)
    have heq : (fun r : ℝ => G idx₀ (embed 0 y + r • e3 i.succ)) =
        fun r => G idx₀ (embed 0 (y + r • e2 i)) := by
      funext r; rw [embed_add_e2]
    rwa [heq] at h
  have hd_u_p (idx₁ : Fin 13) (i : Fin 2)
      (hidx : ∀ n z, pack (φ n) idx₁ z = part3 u i.succ (z + t n • e3 0))
      (y : Plane) :
      HasDerivAt (fun r : ℝ => u_plus (y + r • e2 i)) (G idx₁ (embed 0 y)) 0 :=
    hpart_deriv 0 idx₁ i (fun n z s => by
      rw [hidx n]
      have h := line_deriv3 hu.regular (z + t n • e3 0) (e3 i.succ) s
      have heq : (fun r : ℝ => u (z + t n • e3 0 + r • e3 i.succ)) =
          fun r => u (z + r • e3 i.succ + t n • e3 0) := by funext r; congr 1; module
      rw [heq] at h
      have heq2 : z + t n • e3 0 + s • e3 i.succ = z + s • e3 i.succ + t n • e3 0 := by module
      rwa [heq2] at h) y
  have hd_p1_p2 (idx₀ idx₁ : Fin 13) (j : Fin 3) (i : Fin 2)
      (hidx0 : ∀ n z, pack (φ n) idx₀ z = part3 u j (z + t n • e3 0))
      (hidx1 : ∀ n z, pack (φ n) idx₁ z = part32 u j i.succ (z + t n • e3 0))
      (y : Plane) :
      HasDerivAt (fun r : ℝ => G idx₀ (embed 0 (y + r • e2 i))) (G idx₁ (embed 0 y)) 0 :=
    hpart_deriv idx₀ idx₁ i (fun n z s => by
      have hfun : (fun r : ℝ => pack (φ n) idx₀ (z + r • e3 i.succ)) =
          fun r => part3 u j (z + r • e3 i.succ + t n • e3 0) :=
        funext fun r => hidx0 n _
      rw [hfun, hidx1 n]
      have hpc : ContDiff ℝ 1 (part3 u j) :=
        (hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
      have hl : HasDerivAt (fun r : ℝ => z + r • e3 i.succ + t n • e3 0) (e3 i.succ) s := by
        have h1' := (((hasDerivAt_id s).smul_const (e3 i.succ)).const_add z).add_const (t n • e3 0)
        simpa using h1'
      exact (hpc.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt s hl) y
  obtain ⟨hup_c2, hup_fd, hup_lap⟩ := contDiff_two_of_partials2
    ((hGc 8).comp (continuous_embed_snd 0))
    ((hGc 9).comp (continuous_embed_snd 0))
    ((hGc 11).comp (continuous_embed_snd 0))
    ((hGc 12).comp (continuous_embed_snd 0))
    (hd_u_p 2 0 (fun _ _ => rfl))
    (hd_u_p 3 1 (fun _ _ => rfl))
    (hd_p1_p2 2 8 1 0 (fun _ _ => rfl) (fun _ _ => rfl))
    (hd_p1_p2 2 9 1 1 (fun _ _ => rfl) (fun _ _ => rfl))
    (hd_p1_p2 3 11 2 0 (fun _ _ => rfl) (fun _ _ => rfl))
    (hd_p1_p2 3 12 2 1 (fun _ _ => rfl) (fun _ _ => rfl))
  have hup_abs : ∀ y, |u_plus y| ≤ 1 := by
    intro y
    have ht := (hGU 0 {embed 0 y} isCompact_singleton).tendsto_at (Set.mem_singleton _)
    exact le_of_tendsto ht.abs (Eventually.of_forall fun n => h1 _)
  have hup_pde : ∀ y, (Δ u_plus) y + u_plus y - (u_plus y) ^ 3 = 0 := by
    intro y
    rw [hup_lap y]
    let x := embed 0 y
    have ht0 := (hGU 0 {x} isCompact_singleton).tendsto_at (Set.mem_singleton _)
    have ht4 := (hGU 4 {x} isCompact_singleton).tendsto_at (Set.mem_singleton _)
    have ht8 := (hGU 8 {x} isCompact_singleton).tendsto_at (Set.mem_singleton _)
    have ht12 := (hGU 12 {x} isCompact_singleton).tendsto_at (Set.mem_singleton _)
    have hsum : Tendsto (fun n => pack (φ n) 4 x + pack (φ n) 8 x + pack (φ n) 12 x +
        pack (φ n) 0 x - (pack (φ n) 0 x) ^ 3) atTop
        (𝓝 (G 4 x + G 8 x + G 12 x + G 0 x - (G 0 x) ^ 3)) :=
      (((ht4.add ht8).add ht12).add ht0).sub (ht0.pow 3)
    have hzero : (fun n => pack (φ n) 4 x + pack (φ n) 8 x + pack (φ n) 12 x +
        pack (φ n) 0 x - (pack (φ n) 0 x) ^ 3) = fun _ => (0 : ℝ) := by
      funext n
      let b := EuclideanSpace.basisFun (Fin 3) ℝ
      have hlap_eq : (Δ u) (x + t n • e3 0) =
          part32 u 0 0 (x + t n • e3 0) + part32 u 1 1 (x + t n • e3 0) +
          part32 u 2 2 (x + t n • e3 0) := by
        rw [sum_second3 b (x + t n • e3 0)]
        have hs (k : Fin 3) : second3 u (x + t n • e3 0) (b k) =
            part32 u k k (x + t n • e3 0) := by
          have hbk : b k = e3 k := EuclideanSpace.basisFun_apply (Fin 3) ℝ k
          rw [hbk]
          unfold part32 part3 second3
          rw [fderiv_clm_apply ((hu.regular.fderiv_right (by norm_num)).differentiable one_ne_zero _)
            (differentiableAt_const (e3 k))]
          simp
        rw [hs 0, hs 1, hs 2]
      have hsol := hu.solution (x + t n • e3 0)
      rw [hlap_eq] at hsol
      exact hsol
    rw [hzero] at hsum
    have heq := tendsto_nhds_unique hsum tendsto_const_nhds
    rw [hG4_zero x, zero_add] at heq
    exact heq
  have hG2_indep (x : Space) : G 2 x = a₀ (proj2 x) := by
    have hd := hline_deriv_lim 0 2 (e3 1) (fun n z s => by
      have h := line_deriv3 hu.regular (z + t n • e3 0) (e3 1) s
      have heq : (fun r : ℝ => u (z + t n • e3 0 + r • e3 1)) =
          fun r => u (z + r • e3 1 + t n • e3 0) := by funext r; congr 1; module
      rw [heq] at h
      have heq2 : z + t n • e3 0 + s • e3 1 = z + s • e3 1 + t n • e3 0 := by module
      rwa [heq2] at h) x
    have hfun : (fun r : ℝ => G 0 (x + r • e3 1)) =
        fun r => u_plus (proj2 x + r • e2 0) := by
      funext r
      rw [hG0_indep]
      congr 2
      ext k; fin_cases k <;> simp [proj2, e3, e2]
    rw [hfun] at hd
    exact hd.unique (hd_u_p 2 0 (fun _ _ => rfl) (proj2 x))
  have hG3_indep (x : Space) : G 3 x = a₁ (proj2 x) := by
    have hd := hline_deriv_lim 0 3 (e3 2) (fun n z s => by
      have h := line_deriv3 hu.regular (z + t n • e3 0) (e3 2) s
      have heq : (fun r : ℝ => u (z + t n • e3 0 + r • e3 2)) =
          fun r => u (z + r • e3 2 + t n • e3 0) := by funext r; congr 1; module
      rw [heq] at h
      have heq2 : z + t n • e3 0 + s • e3 2 = z + s • e3 2 + t n • e3 0 := by module
      rwa [heq2] at h) x
    have hfun : (fun r : ℝ => G 0 (x + r • e3 2)) =
        fun r => u_plus (proj2 x + r • e2 1) := by
      funext r
      rw [hG0_indep]
      congr 2
      ext k; fin_cases k <;> simp [proj2, e3, e2]
    rw [hfun] at hd
    exact hd.unique (hd_u_p 3 1 (fun _ _ => rfl) (proj2 x))
  refine ⟨t, u_plus, ht_pos, ht_top, ⟨hup_c2, ⟨1, hup_abs⟩, hup_pde⟩, hup_abs, ?_, ?_, ?_⟩
  · intro K hK
    have h := hGU 0 K hK
    have heq : G 0 = fun x => u_plus (proj2 x) := funext hG0_indep
    rwa [heq] at h
  · intro i K hK
    fin_cases i
    · have h := hGU 2 K hK
      have heq : G 2 = fun x => fderiv ℝ u_plus (proj2 x) (e2 0) := by
        funext x; rw [hG2_indep, hup_fd]; simp [e2, a₀]
      rwa [heq] at h
    · have h := hGU 3 K hK
      have heq : G 3 = fun x => fderiv ℝ u_plus (proj2 x) (e2 1) := by
        funext x; rw [hG3_indep, hup_fd]; simp [e2, a₁]
      rwa [heq] at h
  · intro K hK
    have h := hGU 1 K hK
    have heq : G 1 = fun _ => (0 : ℝ) := funext hG1_zero
    rwa [heq] at h

/-
## Section 3: Fubini for R^3 = R x R^2, weak partial equation, and 2D stability of u_+
-/

private noncomputable def spaceIsoProd : Space ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Plane) where
  toFun x := WithLp.toLp 2 (x 0, proj2 x)
  invFun p := embed (WithLp.ofLp p).1 (WithLp.ofLp p).2
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    refine Prod.ext (by simp) ?_
    ext i; fin_cases i <;> simp [proj2, e2]
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    refine Prod.ext (by simp) ?_
    ext i; fin_cases i <;> simp [proj2, e2]
  left_inv x := embed_proj2 x
  right_inv p := by
    apply WithLp.ofLp_injective 2
    refine Prod.ext (by simp [embed, e3]) ?_
    ext i; fin_cases i <;> simp [proj2, embed, e3, e2]
  norm_map' x := by
    change ‖WithLp.toLp 2 (x 0, proj2 x)‖ = ‖x‖
    have hsq : ‖WithLp.toLp 2 (x 0, proj2 x)‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp only [Fin.sum_univ_three, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
      change (x 0) ^ 2 + ((proj2 x) 0 ^ 2 + (proj2 x) 1 ^ 2) =
        (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2
      have h0 : (proj2 x) 0 = x 1 := by simp [proj2, e2]
      have h1 : (proj2 x) 1 = x 2 := by simp [proj2, e2]
      rw [h0, h1]
      ring
    nlinarith [norm_nonneg (WithLp.toLp 2 (x 0, proj2 x)), norm_nonneg x]

private noncomputable def spaceHomeoProd : Space ≃ₜ ℝ × Plane where
  toFun x := (x 0, proj2 x)
  invFun p := embed p.1 p.2
  left_inv := embed_proj2
  right_inv p := by
    refine Prod.ext (by simp [embed, e3]) ?_
    ext i; fin_cases i <;> simp [proj2, embed, e3, e2]
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0)
    · unfold proj2
      exact ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1).smul continuous_const).add
        ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).smul continuous_const)
  continuous_invFun := by
    unfold embed
    exact ((continuous_fst.smul continuous_const).add
      (((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp continuous_snd).smul
        continuous_const)).add
      (((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp continuous_snd).smul
        continuous_const)

private noncomputable def spaceMeasEquivProd : Space ≃ᵐ ℝ × Plane :=
  spaceHomeoProd.toMeasurableEquiv

private theorem volume_preserving_spaceMeasEquivProd :
    MeasurePreserving spaceMeasEquivProd volume (volume.prod volume) := by
  have hcomp : (spaceMeasEquivProd : Space → ℝ × Plane) =
      WithLp.ofLp ∘ (spaceIsoProd : Space → WithLp 2 (ℝ × Plane)) := rfl
  rw [hcomp]
  exact (WithLp.volume_preserving_ofLp ℝ Plane).comp spaceIsoProd.measurePreserving

private theorem integral_space_eq_prod {f : Space → ℝ} (hf : Integrable f) :
    (∫ x : Space, f x) = ∫ t : ℝ, ∫ y : Plane, f (embed t y) := by
  let g : ℝ × Plane → ℝ := fun p => f (embed p.1 p.2)
  have hcomp : (fun x : Space => g (spaceMeasEquivProd x)) = f := by
    funext x
    change f (embed (x 0) (proj2 x)) = f x
    rw [embed_proj2]
  have hmp := volume_preserving_spaceMeasEquivProd
  have hg_int : Integrable g (volume.prod volume) := by
    have h1 := (hmp.integrable_comp_emb spaceMeasEquivProd.measurableEmbedding (g := g))
    rw [Function.comp_def, hcomp] at h1
    exact h1.mp hf
  calc
    (∫ x : Space, f x) = ∫ x : Space, g (spaceMeasEquivProd x) := by rw [hcomp]
    _ = ∫ p : ℝ × Plane, g p ∂(volume.prod volume) := hmp.integral_comp' g
    _ = ∫ t : ℝ, ∫ y : Plane, f (embed t y) := integral_prod g hg_int

private theorem integral_ball3_le_cylinder {f : Space → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in Metric.ball (0 : Space) R, f x) ≤
      ∫ t in Set.Icc (-R) R, ∫ y in Metric.ball (0 : Plane) R, f (embed t y) := by
  let S : Set Space := spaceMeasEquivProd ⁻¹' (Set.Icc (-R) R ×ˢ Metric.ball (0 : Plane) R)
  have hS_mem (x : Space) : x ∈ S ↔ x 0 ∈ Set.Icc (-R) R ∧ proj2 x ∈ Metric.ball (0 : Plane) R :=
    Iff.rfl
  have hS_meas : MeasurableSet S :=
    (measurableSet_Icc.prod measurableSet_ball).preimage spaceMeasEquivProd.measurable
  have hsub : Metric.ball (0 : Space) R ⊆ S := by
    intro x hx
    rw [hS_mem]
    rw [Metric.mem_ball, dist_zero_right] at hx
    have hsq : (x 0) ^ 2 + ‖proj2 x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp only [Fin.sum_univ_three, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
      have h0 : (proj2 x) 0 = x 1 := by simp [proj2, e2]
      have h1 : (proj2 x) 1 = x 2 := by simp [proj2, e2]
      rw [h0, h1]; ring
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Icc]
      have h0 : (x 0) ^ 2 ≤ R ^ 2 := by nlinarith [sq_nonneg ‖proj2 x‖, norm_nonneg x]
      constructor <;> nlinarith
    · rw [Metric.mem_ball, dist_zero_right]
      have h1 : ‖proj2 x‖ ^ 2 < R ^ 2 := by nlinarith [sq_nonneg (x 0), norm_nonneg x]
      nlinarith [norm_nonneg (proj2 x)]
  have hS_comp : IsCompact (closure S) := by
    have hbd : S ⊆ closedBall (0 : Space) (2 * R) := by
      intro x hx
      rw [hS_mem] at hx
      rw [mem_closedBall, dist_zero_right]
      have hsq : (x 0) ^ 2 + ‖proj2 x‖ ^ 2 = ‖x‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        simp only [Fin.sum_univ_three, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
        have h0 : (proj2 x) 0 = x 1 := by simp [proj2, e2]
        have h1 : (proj2 x) 1 = x 2 := by simp [proj2, e2]
        rw [h0, h1]; ring
      have h0 : (x 0) ^ 2 ≤ R ^ 2 := by
        have := hx.1; rw [Set.mem_Icc] at this; nlinarith
      have h1 : ‖proj2 x‖ ^ 2 ≤ R ^ 2 := by
        have := Metric.mem_ball.mp hx.2; rw [dist_zero_right] at this
        nlinarith [norm_nonneg (proj2 x)]
      nlinarith [norm_nonneg x]
    exact (isCompact_closedBall (0 : Space) (2 * R)).of_isClosed_subset isClosed_closure
      (closure_minimal hbd isClosed_closedBall)
  have hS_int : IntegrableOn f S :=
    (hf.continuousOn.integrableOn_compact hS_comp).mono_set subset_closure
  have hmono : (∫ x in Metric.ball (0 : Space) R, f x) ≤ ∫ x in S, f x :=
    setIntegral_mono_set hS_int (Eventually.of_forall hf0) (Eventually.of_forall hsub)
  have hind_eq : (∫ x in S, f x) =
      ∫ t in Set.Icc (-R) R, ∫ y in Metric.ball (0 : Plane) R, f (embed t y) := by
    rw [← integral_indicator hS_meas, integral_space_eq_prod (hS_int.integrable_indicator hS_meas)]
    have hpt (t : ℝ) : (∫ y : Plane, S.indicator f (embed t y)) =
        (Set.Icc (-R) R).indicator (fun s => ∫ y in Metric.ball (0 : Plane) R, f (embed s y)) t := by
      by_cases ht : t ∈ Set.Icc (-R) R
      · rw [Set.indicator_of_mem ht]
        rw [← integral_indicator measurableSet_ball]
        congr 1; funext y
        by_cases hy : y ∈ Metric.ball (0 : Plane) R
        · have hmem : embed t y ∈ S := by
            rw [hS_mem]
            refine ⟨?_, ?_⟩
            · simpa [embed, e3] using ht
            · have hp : proj2 (embed t y) = y := by
                ext k; fin_cases k <;> simp [proj2, embed, e3, e2]
              rwa [hp]
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hy]
        · have hnmem : embed t y ∉ S := by
            rw [hS_mem]
            intro hm
            have hp : proj2 (embed t y) = y := by
              ext k; fin_cases k <;> simp [proj2, embed, e3, e2]
            exact hy (hp ▸ hm.2)
          rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hy]
      · rw [Set.indicator_of_notMem ht]
        have hzero : (fun y : Plane => S.indicator f (embed t y)) = fun _ => 0 := by
          funext y
          have hnmem : embed t y ∉ S := by
            rw [hS_mem]
            intro hm
            have ht0 : (embed t y) 0 = t := by simp [embed, e3]
            exact ht (ht0 ▸ hm.1)
          exact Set.indicator_of_notMem hnmem _
        rw [hzero, integral_zero]
    simp_rw [hpt]
    exact integral_indicator measurableSet_Icc
  exact hmono.trans_eq hind_eq

private theorem integral_fderiv_eq_zero_of_compact3
    {g : Space → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (v : Space) :
    (∫ x : Space, fderiv ℝ g x v) = 0 := by
  have h1 : Integrable (fun x : Space => (fderiv ℝ (fun _ : Space => (1 : ℝ)) x v) * g x) := by
    simp
  have h2 : Integrable (fun x : Space => (1 : ℝ) * fderiv ℝ g x v) := by
    have hc : Continuous (fun x : Space => fderiv ℝ g x v) :=
      (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hcs : HasCompactSupport (fun x : Space => fderiv ℝ g x v) := hgc.fderiv_apply ℝ v
    simpa using hc.integrable_of_hasCompactSupport hcs
  have h3 : Integrable (fun x : Space => (1 : ℝ) * g x) := by
    simpa using hg.continuous.integrable_of_hasCompactSupport hgc
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => differentiableAt_const (1 : ℝ)) (fun x _ => hg.differentiable one_ne_zero x)
  simpa using h

-- Weak partial equation in R^3 (ported from DeGiorgi_three.R1.H2)
private theorem integrate_compact_mul3 {a b : Space → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hs : HasCompactSupport a) :
    Integrable (fun x => a x * b x) :=
  (ha.mul hb).integrable_of_hasCompactSupport (hs.mul_right (f' := b))

private theorem shifted_integral_deriv3 {a f : Space → ℝ}
    (ha : Continuous a) (hc : HasCompactSupport a) (hf : ContDiff ℝ 1 f) (e : Space) :
    HasDerivAt (fun t : ℝ => ∫ x, a x * f (x + t • e))
      (∫ x, a x * fderiv ℝ f x e) 0 := by
  let F := fun (t : ℝ) (x : Space) => a x * f (x + t • e)
  let D := fun (t : ℝ) (x : Space) => a x * fderiv ℝ f (x + t • e) e
  let S := tsupport a
  let T : Set ℝ := Set.Icc (-1) 1
  have hT : T ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hS : MeasurableSet S := (isClosed_tsupport a).measurableSet
  have hpc : Continuous (fun x : Space => fderiv ℝ f x e) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hjoint : Continuous (fun p : ℝ × Space => D p.1 p.2) :=
    (ha.comp continuous_snd).mul
      (hpc.comp (continuous_snd.add (continuous_fst.smul continuous_const)))
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hc).exists_bound_of_continuousOn hjoint.continuousOn
  let bound := S.indicator fun _ => M
  have hBound : Integrable bound :=
    (integrableOn_const (μ := volume) (C := M)
      (hs := hc.measure_lt_top.ne) (hC := by simp)).integrable_indicator hS
  have hDom : ∀ᵐ x : Space ∂volume, ∀ t ∈ T, ‖D t x‖ ≤ bound x := by
    refine ae_of_all _ fun x t ht => ?_
    by_cases hx : x ∈ S
    · rw [show bound x = M from Set.indicator_of_mem hx _]
      exact hM (t, x) ⟨ht, hx⟩
    · have he : a x = 0 := by
        by_contra h
        exact hx (subset_closure h)
      rw [show bound x = 0 from Set.indicator_of_notMem hx _]
      simp [D, he]
  have hF (t : ℝ) : Continuous (F t) :=
    ha.mul (hf.continuous.comp (continuous_id.add continuous_const))
  have hD (t : ℝ) : Continuous (D t) :=
    ha.mul (hpc.comp (continuous_id.add continuous_const))
  have hFint : Integrable (F 0) := integrate_compact_mul3 ha
    (hf.continuous.comp (continuous_id.add continuous_const)) hc
  have hd (x : Space) (t : ℝ) : HasDerivAt (F · x) (D t x) t := by
    have h1 : HasDerivAt (fun s : ℝ => f (x + s • e)) (fderiv ℝ f (x + t • e) e) t :=
      (hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
        (by simpa using (((hasDerivAt_id t).smul_const e).const_add x))
    exact h1.const_mul (a x)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hT
    (Eventually.of_forall fun t => (hF t).aestronglyMeasurable) hFint
    (hD 0).aestronglyMeasurable hDom hBound
    (ae_of_all _ fun x t _ => hd x t)).2
  simpa only [F, D, zero_smul, add_zero] using h

private theorem integrate_shifted_by_parts3 {g η : Space → ℝ} (hg : ContDiff ℝ 1 g)
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (s e : Space) :
    (∫ x, fderiv ℝ η x e * g (x + s)) =
      -∫ x, η x * fderiv ℝ g (x + s) e := by
  let g' := fun x : Space => g (x + s)
  have hg' : ContDiff ℝ 1 g' := hg.comp (contDiff_id.add contDiff_const)
  have hgp (x : Space) : fderiv ℝ g' x e = fderiv ℝ g (x + s) e := by
    have hh := ((hg.differentiable one_ne_zero (x + s)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).add_const s)).fderiv
    change fderiv ℝ g' x = (fderiv ℝ g (x + s)).comp (ContinuousLinearMap.id ℝ Space) at hh
    rw [ContinuousLinearMap.comp_id] at hh
    exact congrArg (fun L : Space →L[ℝ] ℝ => L e) hh
  have h1 := integrate_compact_mul3 (a := η) (b := fun x => fderiv ℝ g' x e) hη.continuous
    ((hg'.continuous_fderiv one_ne_zero).clm_apply continuous_const) hηc
  have h2 := integrate_compact_mul3 (a := fun x => fderiv ℝ η x e) (b := g')
    ((hη.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    hg'.continuous (hηc.fderiv_apply ℝ e)
  have h3 := integrate_compact_mul3 (a := η) (b := g') hη.continuous hg'.continuous hηc
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h2 h1 h3
    (fun x _ => hη.differentiable one_ne_zero x)
    (fun x _ => hg'.differentiable one_ne_zero x)
  simp only [g', hgp] at h ⊢
  linarith

private theorem weak_partial3 {u : Space → ℝ} (hu : DeGiorgi.IsBoundedSolution u)
    (e : Space) {η : Space → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    (∫ x, inner ℝ (∇ (fun y => fderiv ℝ u y e) x) (∇ η x)) +
      (∫ x, η x * ((3 * (u x) ^ 2 - 1) * fderiv ℝ u x e)) = 0 := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let g (i : Fin 3) := fun x : Space => fderiv ℝ u x (b i)
  let a (i : Fin 3) := fun x : Space => fderiv ℝ η x (b i)
  let F (x : Space) := u x ^ 3 - u x
  let W (t : ℝ) := (∑ i : Fin 3, ∫ x, a i x * g i (x + t • e)) + ∫ x, η x * F (x + t • e)
  have hg (i : Fin 3) : ContDiff ℝ 1 (g i) :=
    (hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
  have ha (i : Fin 3) : Continuous (a i) :=
    (hη.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hac (i : Fin 3) : HasCompactSupport (a i) := hηc.fderiv_apply ℝ (b i)
  have hU : ContDiff ℝ 1 u := hu.regular.of_le (by norm_num)
  have hF : ContDiff ℝ 1 F := (hU.pow 3).sub hU
  have hW : W = fun _ => 0 := by
    funext t
    have hLi (i : Fin 3) : Integrable (fun x => η x * fderiv ℝ (g i) (x + t • e) (b i)) :=
      integrate_compact_mul3 hη.continuous
        (((hg i).continuous_fderiv one_ne_zero).clm_apply continuous_const |>.comp
          (continuous_id.add continuous_const)) hηc
    have hsum : (∑ i : Fin 3, ∫ x, a i x * g i (x + t • e)) = -(∫ x, η x * F (x + t • e)) := by
      calc
        _ = ∑ i : Fin 3, -(∫ x, η x * fderiv ℝ (g i) (x + t • e) (b i)) :=
          Finset.sum_congr rfl fun i _ => integrate_shifted_by_parts3 (hg i) hη hηc _ _
        _ = -(∫ x, ∑ i : Fin 3, η x * fderiv ℝ (g i) (x + t • e) (b i)) := by
          rw [Finset.sum_neg_distrib, integral_finsetSum _ (fun i _ => hLi i)]
        _ = _ := by
          congr 1
          apply integral_congr_ae
          filter_upwards [] with x
          rw [← Finset.mul_sum]
          have hlap : (∑ i : Fin 3, fderiv ℝ (g i) (x + t • e) (b i)) = (Δ u) (x + t • e) := by
            rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u b]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [iteratedFDeriv_two_apply]
            have hpa : fderiv ℝ (g i) (x + t • e) (b i) =
                (fderiv ℝ (fderiv ℝ u) (x + t • e) (b i)) (b i) := by
              unfold g
              rw [fderiv_clm_apply ((hu.regular.fderiv_right (by norm_num)).differentiable
                one_ne_zero _) (differentiableAt_const (b i))]
              simp
            simpa [Matrix.cons_val_zero, Matrix.cons_val_one] using hpa
          rw [hlap]
          have hsol := hu.solution (x + t • e)
          have hFeq : (Δ u) (x + t • e) = F (x + t • e) := by dsimp [F]; linarith
          rw [hFeq]
    dsimp [W]
    linarith
  have hd_sum : HasDerivAt (fun t : ℝ => ∑ i : Fin 3, ∫ x, a i x * g i (x + t • e))
      (∑ i : Fin 3, ∫ x, a i x * fderiv ℝ (g i) x e) 0 :=
    HasDerivAt.fun_sum (u := Finset.univ) fun i _ => shifted_integral_deriv3 (ha i) (hac i) (hg i) e
  have hd_F : HasDerivAt (fun t : ℝ => ∫ x, η x * F (x + t • e))
      (∫ x, η x * fderiv ℝ F x e) 0 :=
    shifted_integral_deriv3 hη.continuous hηc hF e
  have hd_W : HasDerivAt W
      ((∑ i : Fin 3, ∫ x, a i x * fderiv ℝ (g i) x e) + ∫ x, η x * fderiv ℝ F x e) 0 :=
    hd_sum.add hd_F
  rw [hW] at hd_W
  have hzero := hd_W.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have hF_deriv (x : Space) : fderiv ℝ F x e = (3 * (u x) ^ 2 - 1) * fderiv ℝ u x e := by
    have h := (hu.regular.differentiable (by norm_num) x).hasFDerivAt
    have he := congrArg (fun L : Space →L[ℝ] ℝ => L e) ((h.pow 3).sub h).fderiv
    simp only [sub_apply, smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at he
    change fderiv ℝ F x e = 3 * u x ^ (3 - 1) * fderiv ℝ u x e - fderiv ℝ u x e at he
    rw [he]; norm_num; ring
  have hcomm (i : Fin 3) (x : Space) :
      fderiv ℝ (g i) x e = fderiv ℝ (fun y => fderiv ℝ u y e) x (b i) := by
    have h1 : fderiv ℝ (g i) x e = (fderiv ℝ (fderiv ℝ u) x e) (b i) := by
      unfold g
      rw [fderiv_clm_apply ((hu.regular.fderiv_right (by norm_num)).differentiable
        one_ne_zero x) (differentiableAt_const (b i))]
      simp
    have h2 : fderiv ℝ (fun y => fderiv ℝ u y e) x (b i) =
        (fderiv ℝ (fderiv ℝ u) x (b i)) e := by
      rw [fderiv_clm_apply ((hu.regular.fderiv_right (by norm_num)).differentiable
        one_ne_zero x) (differentiableAt_const e)]
      simp
    rw [h1, h2]
    exact (hu.regular.contDiffAt.isSymmSndFDerivAt (by simp)) e (b i)
  have hgrad_sum :
      (∑ i : Fin 3, ∫ x, a i x * fderiv ℝ (g i) x e) =
      ∫ x, inner ℝ (∇ (fun y => fderiv ℝ u y e) x) (∇ η x) := by
    have hint (i : Fin 3) : Integrable (fun x => a i x * fderiv ℝ (g i) x e) :=
      integrate_compact_mul3 (ha i)
        (((hg i).continuous_fderiv one_ne_zero).clm_apply continuous_const) (hac i)
    rw [← integral_finsetSum _ (fun i _ => hint i)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdu (f : Space → ℝ) : inner ℝ (∇ f x) (b i) = fderiv ℝ f x (b i) := by
      rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]
    rw [hcomm i x, hdu, real_inner_comm (∇ η x) (b i), hdu]
    dsimp [a]
    ring
  rw [← hgrad_sum]
  simp_rw [← hF_deriv]
  exact hzero

private theorem stability3 {u : Space → ℝ}
    (hu : DeGiorgi.IsBoundedSolution u) (hup : DeGiorgi.HasPositiveDeriv u)
    {φ : Space → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    0 ≤ ∫ x : Space, (‖∇ φ x‖ ^ 2 + (3 * (u x) ^ 2 - 1) * (φ x) ^ 2) := by
  let v := fun x : Space => fderiv ℝ u x (e3 0)
  have hv_pos : ∀ x, 0 < v x := by
    intro x
    have h := hup x
    rwa [(hu.regular.differentiable (by norm_num) x).lineDeriv_eq_fderiv] at h
  have hv_c1 : ContDiff ℝ 1 v :=
    (hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
  let η := fun x : Space => (φ x) ^ 2 / v x
  have hη_c1 : ContDiff ℝ 1 η := (hφ.pow 2).div hv_c1 fun x => (hv_pos x).ne'
  have hηc : HasCompactSupport η := by
    apply hφc.mono'
    intro x hx
    apply subset_closure
    change φ x ≠ 0
    intro h0
    exact hx (by simp [η, h0])
  have hweak := weak_partial3 hu (e3 0) hη_c1 hηc
  have hgrad_η (x : Space) :
      ∇ η x = (2 * φ x / v x) • ∇ φ x - ((φ x) ^ 2 / (v x) ^ 2) • ∇ v x := by
    have hφd := (hφ.differentiable one_ne_zero x).hasFDerivAt
    have hvd := (hv_c1.differentiable one_ne_zero x).hasFDerivAt
    have hsq : HasFDerivAt (fun y => (φ y) ^ 2) ((2 * φ x) • fderiv ℝ φ x) x := by
      have h := hφd.pow 2
      simpa [show 2 - 1 = 1 by decide, pow_one, nsmul_eq_mul, mul_comm, smul_smul] using h
    have hinv := (hasDerivAt_inv (hv_pos x).ne').comp_hasFDerivAt x hvd
    have hm := hsq.mul hinv
    have hη_eq : ((fun y : Space => (φ y) ^ 2) * ((fun z : ℝ => z⁻¹) ∘ v)) = η := by
      funext y; simp [η, div_eq_mul_inv]
    have hfd : fderiv ℝ η x =
        (2 * φ x / v x) • fderiv ℝ φ x - ((φ x) ^ 2 / (v x) ^ 2) • fderiv ℝ v x := by
      have hm' : HasFDerivAt η _ x := hη_eq ▸ hm
      rw [hm'.fderiv]
      ext w
      simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, Function.comp_apply]
      field_simp [(hv_pos x).ne']
      ring
    unfold gradient
    rw [hfd, map_sub, map_smul, map_smul]
  have hpt (x : Space) :
      inner ℝ (∇ v x) (∇ η x) ≤ ‖∇ φ x‖ ^ 2 := by
    rw [hgrad_η x, inner_sub_right, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have hsq_nn : 0 ≤ ‖∇ φ x - (φ x / v x) • ∇ v x‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, real_inner_smul_right,
      mul_pow, sq_abs] at hsq_nn
    have hcomm : inner ℝ (∇ v x) (∇ φ x) = inner ℝ (∇ φ x) (∇ v x) := real_inner_comm _ _
    rw [hcomm]
    have hne := (hv_pos x).ne'
    have hid : (2 * φ x / v x) * inner ℝ (∇ φ x) (∇ v x) -
        ((φ x) ^ 2 / (v x) ^ 2) * ‖∇ v x‖ ^ 2 =
        ‖∇ φ x‖ ^ 2 - (‖∇ φ x‖ ^ 2 - 2 * (φ x / v x * inner ℝ (∇ φ x) (∇ v x)) +
          (φ x / v x) ^ 2 * ‖∇ v x‖ ^ 2) := by
      field_simp [hne]; ring
    linarith
  have hpot (x : Space) :
      η x * ((3 * (u x) ^ 2 - 1) * v x) = (3 * (u x) ^ 2 - 1) * (φ x) ^ 2 := by
    dsimp [η]
    field_simp [(hv_pos x).ne']
  have hcont_grad {f : Space → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (∇ f) :=
    (InnerProductSpace.toDual ℝ Space).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
  have hcomp_grad {f : Space → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (∇ f) := by
    apply hf.mono'
    intro x hx
    apply support_fderiv_subset ℝ
    intro h0
    exact hx (by simp [gradient, h0])
  have hint1 : Integrable (fun x => inner ℝ (∇ v x) (∇ η x)) :=
    ((hcont_grad hv_c1).inner (hcont_grad hη_c1)).integrable_of_hasCompactSupport
      (by
        apply (hcomp_grad hηc).mono'
        intro x hx; apply subset_closure
        intro h0; exact hx (by change inner ℝ (∇ v x) (∇ η x) = 0; rw [h0]; simp))
  have hint2 : Integrable (fun x => ‖∇ φ x‖ ^ 2) :=
    ((hcont_grad hφ).norm.pow 2).integrable_of_hasCompactSupport
      (by
        apply (hcomp_grad hφc).mono'
        intro x hx; apply subset_closure
        intro h0; exact hx (by change ‖∇ φ x‖ ^ 2 = 0; rw [h0]; simp))
  have hint3 : Integrable (fun x => (3 * (u x) ^ 2 - 1) * (φ x) ^ 2) :=
    (((continuous_const.mul (hu.regular.continuous.pow 2)).sub continuous_const).mul
      (hφ.continuous.pow 2)).integrable_of_hasCompactSupport
      (by
        apply hφc.mono'
        intro x hx; apply subset_closure
        intro h0; exact hx (by change (3 * (u x) ^ 2 - 1) * (φ x) ^ 2 = 0; rw [h0]; simp))
  have hle : (∫ x, inner ℝ (∇ v x) (∇ η x)) ≤ ∫ x, ‖∇ φ x‖ ^ 2 :=
    integral_mono hint1 hint2 hpt
  rw [integral_add hint2 hint3]
  have hweak' : (∫ x, inner ℝ (∇ v x) (∇ η x)) + (∫ x, (3 * (u x) ^ 2 - 1) * (φ x) ^ 2) = 0 := by
    have heq : (fun x => η x * ((3 * (u x) ^ 2 - 1) * fderiv ℝ u x (e3 0))) =
        fun x => (3 * (u x) ^ 2 - 1) * (φ x) ^ 2 := funext hpot
    rwa [heq] at hweak
  linarith

private noncomputable def bump1 : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

private theorem bump1_scaled_bounds :
    ∃ Mχ : ℝ, 0 ≤ Mχ ∧ ∀ L : ℝ, 1 ≤ L →
      2 * L ≤ (∫ s : ℝ, (bump1 (L⁻¹ * s)) ^ 2) ∧
      (∫ s : ℝ, (deriv (fun r : ℝ => bump1 (L⁻¹ * r)) s) ^ 2) ≤ 4 * Mχ ^ 2 / L := by
  obtain ⟨Mχ, hMχ⟩ := (bump1.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    ((bump1.contDiff (n := 1)).continuous_fderiv one_ne_zero)
  have hMχ0 : 0 ≤ Mχ := (norm_nonneg _).trans (hMχ 0)
  refine ⟨Mχ, hMχ0, fun L hL => ?_⟩
  have hL0 : 0 < L := by linarith
  let χ : ℝ → ℝ := fun s => bump1 (L⁻¹ * s)
  have hχ_c1 : ContDiff ℝ 1 χ := bump1.contDiff.comp (contDiff_const.mul contDiff_id)
  have hχc : HasCompactSupport χ := by
    simpa [χ, smul_eq_mul] using bump1.hasCompactSupport.comp_smul (inv_ne_zero hL0.ne')
  have hχ2_int : Integrable (fun s : ℝ => (χ s) ^ 2) :=
    (hχ_c1.continuous.pow 2).integrable_of_hasCompactSupport
      (by apply hχc.mono'; intro s hs; apply subset_closure; intro h0; exact hs (by change (χ s) ^ 2 = 0; rw [h0]; simp))
  have hχ_ge : 2 * L ≤ ∫ s : ℝ, (χ s) ^ 2 := by
    have h1 : (∫ s in Set.Icc (-L) L, (1 : ℝ)) = 2 * L := by
      rw [setIntegral_const, Measure.real_def, Real.volume_Icc]
      have hnn : 0 ≤ L - (-L) := by linarith
      rw [ENNReal.toReal_ofReal hnn]
      ring
    rw [← h1]
    calc
      (∫ s in Set.Icc (-L) L, (1 : ℝ)) ≤ ∫ s in Set.Icc (-L) L, (χ s) ^ 2 := by
        apply setIntegral_mono_on (integrableOn_const (hs := measure_Icc_lt_top.ne))
          hχ2_int.integrableOn measurableSet_Icc
        intro s hs
        have hmem : L⁻¹ * s ∈ closedBall (0 : ℝ) 1 := by
          rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_mul, abs_inv,
            abs_of_pos hL0, inv_mul_eq_div, div_le_one hL0, abs_le]
          exact hs
        have hEq : χ s = 1 := bump1.one_of_mem_closedBall hmem
        simp [hEq]
      _ ≤ ∫ s : ℝ, (χ s) ^ 2 :=
        setIntegral_le_integral hχ2_int (Eventually.of_forall fun _ => sq_nonneg _)
  have hχd_le : (∫ s : ℝ, (deriv χ s) ^ 2) ≤ 4 * Mχ ^ 2 / L := by
    have hχd_cont : Continuous (deriv χ) := hχ_c1.continuous_deriv le_rfl
    have hχd_comp : HasCompactSupport (deriv χ) := hχc.deriv
    have hχd2_int : Integrable (fun s : ℝ => (deriv χ s) ^ 2) :=
      (hχd_cont.pow 2).integrable_of_hasCompactSupport
        (by apply hχd_comp.mono'; intro s hs; apply subset_closure; intro h0; exact hs (by change (deriv χ s) ^ 2 = 0; rw [h0]; simp))
    have hzero_out : ∀ s ∉ Set.Icc (-(2 * L)) (2 * L), deriv χ s = 0 := by
      intro s hs
      have hgt : 2 * L < |s| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
        rcases hs with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have hout : χ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        have hopen : IsOpen {r : ℝ | 2 * L < |r|} :=
          isOpen_lt continuous_const continuous_abs
        filter_upwards [hopen.mem_nhds hgt] with r hr
        apply bump1.zero_of_le_dist
        change 2 ≤ dist (L⁻¹ * r) 0
        rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hL0,
          inv_mul_eq_div, le_div_iff₀ hL0]
        exact hr.le
      exact hout.deriv_eq.trans (deriv_const s (0 : ℝ))
    have hderiv_bd (s : ℝ) : |deriv χ s| ≤ Mχ / L := by
      have hfd : HasDerivAt χ (deriv (fun r : ℝ => bump1 r) (L⁻¹ * s) * L⁻¹) s := by
        have h1 := ((bump1.contDiff (n := 1)).differentiable one_ne_zero (L⁻¹ * s)).hasDerivAt
        have h2 : HasDerivAt (fun r : ℝ => L⁻¹ * r) L⁻¹ s := by
          simpa using (hasDerivAt_id s).const_mul L⁻¹
        exact HasDerivAt.comp (h₂ := fun r : ℝ => bump1 r) (h := fun r : ℝ => L⁻¹ * r) s h1 h2
      rw [hfd.deriv, abs_mul, abs_inv, abs_of_pos hL0, mul_comm, inv_mul_eq_div]
      apply div_le_div_of_nonneg_right _ hL0.le
      have hnd : |deriv (fun r : ℝ => bump1 r) (L⁻¹ * s)| =
          ‖fderiv ℝ (fun r : ℝ => bump1 r) (L⁻¹ * s)‖ := by
        rw [← Real.norm_eq_abs, norm_deriv_eq_norm_fderiv]
      rw [hnd]
      exact hMχ (L⁻¹ * s)
    calc
      (∫ s : ℝ, (deriv χ s) ^ 2) = ∫ s in Set.Icc (-(2 * L)) (2 * L), (deriv χ s) ^ 2 := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro s hs
        rw [hzero_out s hs]; simp
      _ ≤ ∫ s in Set.Icc (-(2 * L)) (2 * L), (Mχ / L) ^ 2 := by
        apply setIntegral_mono_on hχd2_int.integrableOn
          (integrableOn_const (hs := measure_Icc_lt_top.ne)) measurableSet_Icc
        intro s _
        have := hderiv_bd s
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = 4 * Mχ ^ 2 / L := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Icc]
        have hnn : 0 ≤ 2 * L - -(2 * L) := by linarith
        rw [ENNReal.toReal_ofReal hnn]
        have hne : L ≠ 0 := hL0.ne'
        change (2 * L - -(2 * L)) * (Mχ / L) ^ 2 = 4 * Mχ ^ 2 / L
        field_simp [hne]
        ring
  exact ⟨hχ_ge, hχd_le⟩

private theorem stability2_of_limit {u : Space → ℝ}
    (hu : DeGiorgi.IsBoundedSolution u) (hup : DeGiorgi.HasPositiveDeriv u)
    {t : ℕ → ℝ} {u_plus : Plane → ℝ}
    (hu_unif : ∀ K : Set Space, IsCompact K →
      TendstoUniformlyOn (fun n x => u (x + t n • e3 0)) (fun x => u_plus (proj2 x)) atTop K)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    0 ≤ ∫ y : Plane, (‖∇ ψ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (ψ y) ^ 2) := by
  obtain ⟨Mχ, hMχ0, hMχ_bd⟩ := bump1_scaled_bounds
  let I := ∫ y : Plane, (‖∇ ψ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (ψ y) ^ 2)
  let J := ∫ y : Plane, (ψ y) ^ 2
  have hJ0 : 0 ≤ J := integral_nonneg fun y => sq_nonneg _
  have hcont_grad2 : Continuous (∇ ψ) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hψ.continuous_fderiv one_ne_zero)
  have hcomp_grad2 : HasCompactSupport (∇ ψ) := by
    apply hψc.mono'
    intro y hy; apply support_fderiv_subset ℝ
    intro h0; exact hy (by simp [gradient, h0])
  have hψ2_int : Integrable (fun y => (ψ y) ^ 2) :=
    (hψ.continuous.pow 2).integrable_of_hasCompactSupport
      (by apply hψc.mono'; intro y hy; apply subset_closure; intro h0; exact hy (by change (ψ y) ^ 2 = 0; rw [h0]; simp))
  have hgrad2_int : Integrable (fun y => ‖∇ ψ y‖ ^ 2) :=
    (hcont_grad2.norm.pow 2).integrable_of_hasCompactSupport
      (by apply hcomp_grad2.mono'; intro y hy; apply subset_closure; intro h0; exact hy (by change ‖∇ ψ y‖ ^ 2 = 0; rw [h0]; simp))
  have hup_cont : Continuous u_plus := by
    rw [continuous_iff_continuousAt]
    intro y
    have hK : IsCompact (closedBall (embed 0 y) 1) := isCompact_closedBall _ _
    have huc := (hu_unif _ hK).continuousOn
      (Eventually.frequently (Eventually.of_forall fun n =>
        (hu.regular.continuous.comp (continuous_id.add continuous_const)).continuousOn))
    have hca : ContinuousAt (fun x : Space => u_plus (proj2 x)) (embed 0 y) :=
      huc.continuousAt (closedBall_mem_nhds (embed 0 y) (by norm_num))
    have hcomp : u_plus = (fun x => u_plus (proj2 x)) ∘ embed 0 := by
      funext z; dsimp; congr 1; ext k; fin_cases k <;> simp [proj2, embed, e3, e2]
    rw [hcomp]
    exact hca.comp (continuous_embed_snd 0).continuousAt
  have hpot2_int : Integrable (fun y => (3 * (u_plus y) ^ 2 - 1) * (ψ y) ^ 2) :=
    (((continuous_const.mul (hup_cont.pow 2)).sub continuous_const).mul
      (hψ.continuous.pow 2)).integrable_of_hasCompactSupport
      (by apply hψc.mono'; intro y hy; apply subset_closure; intro h0; exact hy (by change (3 * (u_plus y) ^ 2 - 1) * (ψ y) ^ 2 = 0; rw [h0]; simp))
  have hL_est : ∀ L : ℝ, 1 ≤ L →
      0 ≤ (∫ s : ℝ, (bump1 (L⁻¹ * s)) ^ 2) * I +
        (∫ s : ℝ, (deriv (fun r : ℝ => bump1 (L⁻¹ * r)) s) ^ 2) * J := by
    intro L hL
    have hL0 : 0 < L := by linarith
    let χ : ℝ → ℝ := fun s => bump1 (L⁻¹ * s)
    have hχ_c1 : ContDiff ℝ 1 χ := bump1.contDiff.comp (contDiff_const.mul contDiff_id)
    have hχc : HasCompactSupport χ := by
      simpa [χ, smul_eq_mul] using bump1.hasCompactSupport.comp_smul (inv_ne_zero hL0.ne')
    let φ : Space → ℝ := fun x => χ (x 0) * ψ (proj2 x)
    have hcoord0 : ContDiff ℝ 1 (fun x : Space => x 0) :=
      (((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.coord 0).toContinuousLinearMap).contDiff
    have hproj2_c : ContDiff ℝ 1 proj2 := by
      unfold proj2
      have h1 : ContDiff ℝ 1 (fun x : Space => x 1) :=
        (((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.coord 1).toContinuousLinearMap).contDiff
      have h2 : ContDiff ℝ 1 (fun x : Space => x 2) :=
        (((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.coord 2).toContinuousLinearMap).contDiff
      exact (h1.smul contDiff_const).add (h2.smul contDiff_const)
    have hφ_c1 : ContDiff ℝ 1 φ := (hχ_c1.comp hcoord0).mul (hψ.comp hproj2_c)
    have hφc : HasCompactSupport φ := by
      have hK : IsCompact (spaceHomeoProd.symm '' (tsupport χ ×ˢ tsupport ψ)) :=
        (hχc.prod hψc).image spaceHomeoProd.symm.continuous
      apply HasCompactSupport.of_support_subset_isCompact hK
      intro x hx
      refine ⟨(x 0, proj2 x), ⟨?_, ?_⟩, embed_proj2 x⟩
      · apply subset_closure
        intro h0; exact hx (by simp [φ, h0])
      · apply subset_closure
        intro h0; exact hx (by simp [φ, h0])
    have hgrad_φ_sq (x : Space) :
        ‖∇ φ x‖ ^ 2 = (deriv χ (x 0)) ^ 2 * (ψ (proj2 x)) ^ 2 +
          (χ (x 0)) ^ 2 * ‖∇ ψ (proj2 x)‖ ^ 2 := by
      let b3 := EuclideanSpace.basisFun (Fin 3) ℝ
      let b2 := EuclideanSpace.basisFun (Fin 2) ℝ
      have hnorm3 : ‖∇ φ x‖ ^ 2 = ∑ i : Fin 3, (fderiv ℝ φ x (e3 i)) ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, ← b3.sum_inner_mul_inner]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hi : b3 i = e3 i := EuclideanSpace.basisFun_apply (Fin 3) ℝ i
        have hdu1 : inner ℝ (∇ φ x) (e3 i) = fderiv ℝ φ x (e3 i) := by
          rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]
        have hdu2 : inner ℝ (e3 i) (∇ φ x) = fderiv ℝ φ x (e3 i) :=
          (real_inner_comm _ _).trans hdu1
        rw [hi, hdu1, hdu2]; ring
      have hnorm2 : ‖∇ ψ (proj2 x)‖ ^ 2 = ∑ i : Fin 2, (fderiv ℝ ψ (proj2 x) (e2 i)) ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, ← b2.sum_inner_mul_inner]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hi : b2 i = e2 i := EuclideanSpace.basisFun_apply (Fin 2) ℝ i
        have hdu1 : inner ℝ (∇ ψ (proj2 x)) (e2 i) = fderiv ℝ ψ (proj2 x) (e2 i) := by
          rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]
        have hdu2 : inner ℝ (e2 i) (∇ ψ (proj2 x)) = fderiv ℝ ψ (proj2 x) (e2 i) :=
          (real_inner_comm _ _).trans hdu1
        rw [hi, hdu1, hdu2]; ring
      have hp0 : fderiv ℝ φ x (e3 0) = deriv χ (x 0) * ψ (proj2 x) := by
        have h1 : HasDerivAt (fun r : ℝ => φ (x + r • e3 0)) (fderiv ℝ φ x (e3 0)) 0 := by
          have hl : HasDerivAt (fun r : ℝ => x + r • e3 0) (e3 0) 0 := by
            simpa using (((hasDerivAt_id (0 : ℝ)).smul_const (e3 0)).const_add x)
          have hd := (hφ_c1.differentiable one_ne_zero (x + (0 : ℝ) • e3 0)).hasFDerivAt.comp_hasDerivAt 0 hl
          rw [zero_smul, add_zero] at hd
          exact hd
        have h2 : HasDerivAt (fun r : ℝ => φ (x + r • e3 0)) (deriv χ (x 0) * ψ (proj2 x)) 0 := by
          have heq : (fun r : ℝ => φ (x + r • e3 0)) = fun r => χ (x 0 + r) * ψ (proj2 x) := by
            funext r
            dsimp [φ]
            congr 1
            · simp [e3]
            · congr 1; ext k; fin_cases k <;> simp [proj2, e3, e2]
          rw [heq]
          have hχd : HasDerivAt (fun r : ℝ => χ (x 0 + r)) (deriv χ (x 0)) 0 := by
            have hadd : HasDerivAt (fun r : ℝ => x 0 + r) 1 0 := by
              simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 0)
            have h0d : HasDerivAt χ (deriv χ (x 0)) (x 0 + (0 : ℝ)) := by
              simpa using (hχ_c1.differentiable one_ne_zero (x 0)).hasDerivAt
            have h := HasDerivAt.comp (h₂ := χ) (h := fun r : ℝ => x 0 + r) 0 h0d hadd
            simpa [Function.comp_def] using h
          exact hχd.mul_const (ψ (proj2 x))
        exact h1.unique h2
      have hpi (i : Fin 2) : fderiv ℝ φ x (e3 i.succ) = χ (x 0) * fderiv ℝ ψ (proj2 x) (e2 i) := by
        have h1 : HasDerivAt (fun r : ℝ => φ (x + r • e3 i.succ)) (fderiv ℝ φ x (e3 i.succ)) 0 := by
          have hl : HasDerivAt (fun r : ℝ => x + r • e3 i.succ) (e3 i.succ) 0 := by
            simpa using (((hasDerivAt_id (0 : ℝ)).smul_const (e3 i.succ)).const_add x)
          have hd := (hφ_c1.differentiable one_ne_zero (x + (0 : ℝ) • e3 i.succ)).hasFDerivAt.comp_hasDerivAt 0 hl
          rw [zero_smul, add_zero] at hd
          exact hd
        have h2 : HasDerivAt (fun r : ℝ => φ (x + r • e3 i.succ))
            (χ (x 0) * fderiv ℝ ψ (proj2 x) (e2 i)) 0 := by
          have heq : (fun r : ℝ => φ (x + r • e3 i.succ)) =
              fun r => χ (x 0) * ψ (proj2 x + r • e2 i) := by
            funext r
            dsimp [φ]
            congr 1
            · congr 1; fin_cases i <;> simp [e3]
            · congr 1; ext k; fin_cases i <;> fin_cases k <;> simp [proj2, e3, e2]
          rw [heq]
          have hψd : HasDerivAt (fun r : ℝ => ψ (proj2 x + r • e2 i))
              (fderiv ℝ ψ (proj2 x) (e2 i)) 0 := by
            have hl : HasDerivAt (fun r : ℝ => proj2 x + r • e2 i) (e2 i) 0 := by
              simpa using (((hasDerivAt_id (0 : ℝ)).smul_const (e2 i)).const_add (proj2 x))
            have hd := (hψ.differentiable one_ne_zero (proj2 x + (0 : ℝ) • e2 i)).hasFDerivAt.comp_hasDerivAt 0 hl
            rw [zero_smul, add_zero] at hd
            exact hd
          exact hψd.const_mul (χ (x 0))
        exact h1.unique h2
      rw [hnorm3, hnorm2, Fin.sum_univ_three, Fin.sum_univ_two,
        show (1 : Fin 3) = Fin.succ 0 by decide, show (2 : Fin 3) = Fin.succ 1 by decide,
        hp0, hpi 0, hpi 1]
      ring
    have hstab_n (n : ℕ) :
        0 ≤ ∫ x : Space, (‖∇ φ x‖ ^ 2 + (3 * (u (x + t n • e3 0)) ^ 2 - 1) * (φ x) ^ 2) := by
      let φn : Space → ℝ := fun x => φ (x - t n • e3 0)
      have hφn_c1 : ContDiff ℝ 1 φn := hφ_c1.comp (contDiff_id.sub contDiff_const)
      have hφnc : HasCompactSupport φn := by
        have hEq : φn = φ ∘ Homeomorph.addRight (-(t n • e3 0)) := by
          funext x; simp [φn, sub_eq_add_neg]
        rw [hEq]
        exact hφc.comp_homeomorph (Homeomorph.addRight (-(t n • e3 0)))
      have hst := stability3 hu hup hφn_c1 hφnc
      have hgrad_shift (x : Space) : ∇ φn x = ∇ φ (x - t n • e3 0) := by
        have hfd : fderiv ℝ φn x = fderiv ℝ φ (x - t n • e3 0) := by
          have hh := ((hφ_c1.differentiable one_ne_zero (x - t n • e3 0)).hasFDerivAt.comp x
            ((hasFDerivAt_id x).sub_const (t n • e3 0))).fderiv
          change fderiv ℝ φn x = (fderiv ℝ φ (x - t n • e3 0)).comp
            (ContinuousLinearMap.id ℝ Space) at hh
          simpa using hh
        simp [gradient, hfd]
      simp_rw [hgrad_shift] at hst
      have htrans := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure Space))
        (fun x : Space => ‖∇ φ (x - t n • e3 0)‖ ^ 2 +
          (3 * (u x) ^ 2 - 1) * (φ (x - t n • e3 0)) ^ 2) (t n • e3 0)
      rw [← htrans] at hst
      simpa only [add_sub_cancel_right] using hst
    have hlim :
        Tendsto (fun n => ∫ x : Space,
            (‖∇ φ x‖ ^ 2 + (3 * (u (x + t n • e3 0)) ^ 2 - 1) * (φ x) ^ 2))
          atTop
          (𝓝 (∫ x : Space, (‖∇ φ x‖ ^ 2 + (3 * (u_plus (proj2 x)) ^ 2 - 1) * (φ x) ^ 2))) := by
      have hφcont : Continuous (∇ φ) :=
        (InnerProductSpace.toDual ℝ Space).symm.continuous.comp (hφ_c1.continuous_fderiv one_ne_zero)
      have hφg_comp : HasCompactSupport (∇ φ) := by
        apply hφc.mono'; intro x hx; apply support_fderiv_subset ℝ
        intro h0; exact hx (by simp [gradient, h0])
      obtain ⟨Mφ, hMφ⟩ := hφc.exists_bound_of_continuous hφ_c1.continuous
      obtain ⟨Mg, hMg⟩ := hφg_comp.exists_bound_of_continuous hφcont
      let K := tsupport φ
      have hK_meas : MeasurableSet K := (isClosed_tsupport φ).measurableSet
      let bound := K.indicator (fun _ => Mg ^ 2 + 4 * Mφ ^ 2)
      have hBound : Integrable bound :=
        (integrableOn_const (C := Mg ^ 2 + 4 * Mφ ^ 2) (hs := hφc.measure_lt_top.ne)
          (hC := by simp)).integrable_indicator hK_meas
      have h1_u := abs_le_one_of_solution hu
      refine tendsto_integral_of_dominated_convergence bound ?_ hBound ?_ ?_
      · intro n
        exact ((hφcont.norm.pow 2).add
          (((continuous_const.mul ((hu.regular.continuous.comp
            (continuous_id.add continuous_const)).pow 2)).sub continuous_const).mul
            (hφ_c1.continuous.pow 2))).aestronglyMeasurable
      · intro n
        refine ae_of_all _ fun x => ?_
        dsimp [bound]
        by_cases hx : x ∈ K
        · rw [Set.indicator_of_mem hx]
          have hgp : ‖∇ φ x‖ ^ 2 ≤ Mg ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hMg x) 2
          have hfp : (φ x) ^ 2 ≤ Mφ ^ 2 := by
            have := hMφ x; rw [Real.norm_eq_abs] at this
            nlinarith [sq_abs (φ x), abs_nonneg (φ x)]
          have hu2 : |3 * (u (x + t n • e3 0)) ^ 2 - 1| ≤ 4 := by
            have ha := h1_u (x + t n • e3 0)
            have hsq : (u (x + t n • e3 0)) ^ 2 ≤ 1 := by
              have := sq_le_sq.mpr (show |u (x + t n • e3 0)| ≤ |(1 : ℝ)| by simpa using ha)
              simpa using this
            rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u (x + t n • e3 0))]
          calc
            |‖∇ φ x‖ ^ 2 + (3 * (u (x + t n • e3 0)) ^ 2 - 1) * (φ x) ^ 2|
                ≤ |‖∇ φ x‖ ^ 2| + |(3 * (u (x + t n • e3 0)) ^ 2 - 1) * (φ x) ^ 2| := abs_add_le _ _
            _ = ‖∇ φ x‖ ^ 2 + |3 * (u (x + t n • e3 0)) ^ 2 - 1| * (φ x) ^ 2 := by
                rw [abs_of_nonneg (sq_nonneg ‖∇ φ x‖), abs_mul, abs_of_nonneg (sq_nonneg (φ x))]
            _ ≤ Mg ^ 2 + 4 * Mφ ^ 2 := by nlinarith [sq_nonneg (φ x)]
        · rw [Set.indicator_of_notMem hx]
          have hφ0 : φ x = 0 := by by_contra hne; exact hx (subset_closure hne)
          have hgrad0 : ∇ φ x = 0 := by
            by_contra hne
            have hmem : x ∈ tsupport (∇ φ) := subset_closure hne
            have hsub : tsupport (∇ φ) ⊆ K := by
              apply closure_minimal _ (isClosed_tsupport φ)
              intro z hz
              have : fderiv ℝ φ z ≠ 0 := fun h0 => hz (by simp [gradient, h0])
              exact support_fderiv_subset ℝ this
            exact hx (hsub hmem)
          simp [hφ0, hgrad0]
      · refine ae_of_all _ fun x => ?_
        have ht := (hu_unif {x} isCompact_singleton).tendsto_at (Set.mem_singleton x)
        exact tendsto_const_nhds.add
          ((((tendsto_const_nhds.mul (ht.pow 2)).sub tendsto_const_nhds).mul tendsto_const_nhds))
    have hstab_lim :
        0 ≤ ∫ x : Space, (‖∇ φ x‖ ^ 2 + (3 * (u_plus (proj2 x)) ^ 2 - 1) * (φ x) ^ 2) :=
      ge_of_tendsto hlim (Eventually.of_forall hstab_n)
    have hFint : Integrable (fun x : Space =>
        ‖∇ φ x‖ ^ 2 + (3 * (u_plus (proj2 x)) ^ 2 - 1) * (φ x) ^ 2) := by
      have hφcont : Continuous (∇ φ) :=
        (InnerProductSpace.toDual ℝ Space).symm.continuous.comp (hφ_c1.continuous_fderiv one_ne_zero)
      have hφg_comp : HasCompactSupport (∇ φ) := by
        apply hφc.mono'; intro x hx; apply support_fderiv_subset ℝ
        intro h0; exact hx (by simp [gradient, h0])
      have hcont : Continuous (fun x : Space =>
          ‖∇ φ x‖ ^ 2 + (3 * (u_plus (proj2 x)) ^ 2 - 1) * (φ x) ^ 2) :=
        (hφcont.norm.pow 2).add
          (((continuous_const.mul ((hup_cont.comp hproj2_c.continuous).pow 2)).sub
            continuous_const).mul (hφ_c1.continuous.pow 2))
      have hcs : HasCompactSupport (fun x : Space =>
          ‖∇ φ x‖ ^ 2 + (3 * (u_plus (proj2 x)) ^ 2 - 1) * (φ x) ^ 2) := by
        apply HasCompactSupport.of_support_subset_isCompact (hφg_comp.union hφc)
        intro x hx
        by_contra hn
        have h1 : x ∉ tsupport (∇ φ) := fun h => hn (Or.inl h)
        have h2 : x ∉ tsupport φ := fun h => hn (Or.inr h)
        have hgrad0 : ∇ φ x = 0 := by by_contra h; exact h1 (subset_closure h)
        have hφ0 : φ x = 0 := by by_contra h; exact h2 (subset_closure h)
        exact hx (by change ‖∇ φ x‖ ^ 2 + (3 * (u_plus (proj2 x)) ^ 2 - 1) * (φ x) ^ 2 = 0
                     rw [hgrad0, hφ0]; simp)
      exact hcont.integrable_of_hasCompactSupport hcs
    rw [integral_space_eq_prod hFint] at hstab_lim
    have hinner (s : ℝ) :
        (∫ y : Plane, (‖∇ φ (embed s y)‖ ^ 2 +
            (3 * (u_plus (proj2 (embed s y))) ^ 2 - 1) * (φ (embed s y)) ^ 2)) =
        (χ s) ^ 2 * I + (deriv χ s) ^ 2 * J := by
      have hpt (y : Plane) :
          ‖∇ φ (embed s y)‖ ^ 2 + (3 * (u_plus (proj2 (embed s y))) ^ 2 - 1) * (φ (embed s y)) ^ 2 =
          (χ s) ^ 2 * (‖∇ ψ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (ψ y) ^ 2) +
          (deriv χ s) ^ 2 * (ψ y) ^ 2 := by
        rw [hgrad_φ_sq (embed s y)]
        have h0 : (embed s y) 0 = s := by simp [embed, e3]
        have hp : proj2 (embed s y) = y := by ext k; fin_cases k <;> simp [proj2, embed, e3, e2]
        dsimp [φ]
        rw [h0, hp]
        ring
      simp_rw [hpt]
      have hsum2_int : Integrable (fun y : Plane =>
          ‖∇ ψ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (ψ y) ^ 2) := hgrad2_int.add hpot2_int
      rw [integral_add (hsum2_int.const_mul ((χ s) ^ 2))
          (hψ2_int.const_mul ((deriv χ s) ^ 2)),
        integral_const_mul, integral_const_mul]
    simp_rw [hinner] at hstab_lim
    have hχ2_int : Integrable (fun s : ℝ => (χ s) ^ 2) :=
      (hχ_c1.continuous.pow 2).integrable_of_hasCompactSupport
        (by apply hχc.mono'; intro s hs; apply subset_closure; intro h0; exact hs (by change (χ s) ^ 2 = 0; rw [h0]; simp))
    have hχd_cont : Continuous (deriv χ) := hχ_c1.continuous_deriv le_rfl
    have hχd_comp : HasCompactSupport (deriv χ) := hχc.deriv
    have hχd2_int : Integrable (fun s : ℝ => (deriv χ s) ^ 2) :=
      (hχd_cont.pow 2).integrable_of_hasCompactSupport
        (by apply hχd_comp.mono'; intro s hs; apply subset_closure; intro h0; exact hs (by change (deriv χ s) ^ 2 = 0; rw [h0]; simp))
    rw [integral_add (hχ2_int.mul_const I) (hχd2_int.mul_const J),
      integral_mul_const, integral_mul_const] at hstab_lim
    exact hstab_lim
  by_contra! hIneg
  let L : ℝ := max 1 (2 * Mχ ^ 2 * J / (-I) + 1)
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL0 : 0 < L := by linarith
  have hEst := hL_est L hL1
  obtain ⟨hχ_ge, hχd_le⟩ := hMχ_bd L hL1
  have h1 : (∫ s : ℝ, (bump1 (L⁻¹ * s)) ^ 2) * I ≤ (2 * L) * I := by nlinarith
  have h2 : (∫ s : ℝ, (deriv (fun r : ℝ => bump1 (L⁻¹ * r)) s) ^ 2) * J ≤
      (4 * Mχ ^ 2 / L) * J :=
    mul_le_mul_of_nonneg_right hχd_le hJ0
  have hL_big : 2 * Mχ ^ 2 * J / (-I) < L := by
    have : 2 * Mχ ^ 2 * J / (-I) + 1 ≤ L := le_max_right _ _
    linarith
  have hpos_negI : 0 < -I := by linarith
  have h3 : 4 * Mχ ^ 2 * J < 2 * L ^ 2 * (-I) := by
    have hmul : 2 * Mχ ^ 2 * J < L * (-I) := (div_lt_iff₀ hpos_negI).mp hL_big
    have hLsq : L ≤ L ^ 2 := by nlinarith
    have hLsqI : L * (-I) ≤ L ^ 2 * (-I) := mul_le_mul_of_nonneg_right hLsq hpos_negI.le
    linarith
  have h4 : (4 * Mχ ^ 2 / L) * J + (2 * L) * I < 0 := by
    have hmul : (4 * Mχ ^ 2 / L) * J + (2 * L) * I =
        (4 * Mχ ^ 2 * J - 2 * L ^ 2 * (-I)) / L := by
      field_simp [hL0.ne']; ring
    rw [hmul]
    exact div_neg_of_neg_of_pos (by linarith) hL0
  linarith

/-
## Section 4: 2D Regularized Sternberg-Zumbrun, log cutoffs, and O(R) energy of stable 2D solutions
-/

private theorem integrate_compact_mul2 {a b : Plane → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hs : HasCompactSupport a) :
    Integrable (fun y => a y * b y) :=
  (ha.mul hb).integrable_of_hasCompactSupport (hs.mul_right (f' := b))

private theorem shifted_integral_deriv2 {a f : Plane → ℝ}
    (ha : Continuous a) (hc : HasCompactSupport a) (hf : ContDiff ℝ 1 f) (e : Plane) :
    HasDerivAt (fun t : ℝ => ∫ y, a y * f (y + t • e))
      (∫ y, a y * fderiv ℝ f y e) 0 := by
  let F := fun (t : ℝ) (y : Plane) => a y * f (y + t • e)
  let D := fun (t : ℝ) (y : Plane) => a y * fderiv ℝ f (y + t • e) e
  let S := tsupport a
  let T : Set ℝ := Set.Icc (-1) 1
  have hT : T ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hS : MeasurableSet S := (isClosed_tsupport a).measurableSet
  have hpc : Continuous (fun y : Plane => fderiv ℝ f y e) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hjoint : Continuous (fun p : ℝ × Plane => D p.1 p.2) :=
    (ha.comp continuous_snd).mul
      (hpc.comp (continuous_snd.add (continuous_fst.smul continuous_const)))
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hc).exists_bound_of_continuousOn hjoint.continuousOn
  let bound := S.indicator fun _ => M
  have hBound : Integrable bound :=
    (integrableOn_const (μ := volume) (C := M)
      (hs := hc.measure_lt_top.ne) (hC := by simp)).integrable_indicator hS
  have hDom : ∀ᵐ y : Plane ∂volume, ∀ t ∈ T, ‖D t y‖ ≤ bound y := by
    refine ae_of_all _ fun y t ht => ?_
    by_cases hy : y ∈ S
    · rw [show bound y = M from Set.indicator_of_mem hy _]
      exact hM (t, y) ⟨ht, hy⟩
    · have he : a y = 0 := by by_contra h; exact hy (subset_closure h)
      rw [show bound y = 0 from Set.indicator_of_notMem hy _]
      simp [D, he]
  have hF (t : ℝ) : Continuous (F t) :=
    ha.mul (hf.continuous.comp (continuous_id.add continuous_const))
  have hD (t : ℝ) : Continuous (D t) :=
    ha.mul (hpc.comp (continuous_id.add continuous_const))
  have hFint : Integrable (F 0) := integrate_compact_mul2 ha
    (hf.continuous.comp (continuous_id.add continuous_const)) hc
  have hd (y : Plane) (t : ℝ) : HasDerivAt (F · y) (D t y) t := by
    have h1 : HasDerivAt (fun s : ℝ => f (y + s • e)) (fderiv ℝ f (y + t • e) e) t :=
      (hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
        (by simpa using (((hasDerivAt_id t).smul_const e).const_add y))
    exact h1.const_mul (a y)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hT
    (Eventually.of_forall fun t => (hF t).aestronglyMeasurable) hFint
    (hD 0).aestronglyMeasurable hDom hBound
    (ae_of_all _ fun y t _ => hd y t)).2
  simpa only [F, D, zero_smul, add_zero] using h

private theorem integrate_shifted_by_parts2 {g η : Plane → ℝ} (hg : ContDiff ℝ 1 g)
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (s e : Plane) :
    (∫ y, fderiv ℝ η y e * g (y + s)) =
      -∫ y, η y * fderiv ℝ g (y + s) e := by
  let g' := fun y : Plane => g (y + s)
  have hg' : ContDiff ℝ 1 g' := hg.comp (contDiff_id.add contDiff_const)
  have hgp (y : Plane) : fderiv ℝ g' y e = fderiv ℝ g (y + s) e := by
    have hh := ((hg.differentiable one_ne_zero (y + s)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).add_const s)).fderiv
    change fderiv ℝ g' y = (fderiv ℝ g (y + s)).comp (ContinuousLinearMap.id ℝ Plane) at hh
    rw [ContinuousLinearMap.comp_id] at hh
    exact congrArg (fun L : Plane →L[ℝ] ℝ => L e) hh
  have h1 := integrate_compact_mul2 (a := η) (b := fun y => fderiv ℝ g' y e) hη.continuous
    ((hg'.continuous_fderiv one_ne_zero).clm_apply continuous_const) hηc
  have h2 := integrate_compact_mul2 (a := fun y => fderiv ℝ η y e) (b := g')
    ((hη.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    hg'.continuous (hηc.fderiv_apply ℝ e)
  have h3 := integrate_compact_mul2 (a := η) (b := g') hη.continuous hg'.continuous hηc
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h2 h1 h3
    (fun y _ => hη.differentiable one_ne_zero y)
    (fun y _ => hg'.differentiable one_ne_zero y)
  simp only [g', hgp] at h ⊢
  linarith

private theorem weak_partial2 {v : Plane → ℝ} (hv : DeGiorgi.IsBoundedSolution v)
    (e : Plane) {η : Plane → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    (∫ y, inner ℝ (∇ (fun z => fderiv ℝ v z e) y) (∇ η y)) +
      (∫ y, η y * ((3 * (v y) ^ 2 - 1) * fderiv ℝ v y e)) = 0 := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let g (i : Fin 2) := fun y : Plane => fderiv ℝ v y (b i)
  let a (i : Fin 2) := fun y : Plane => fderiv ℝ η y (b i)
  let F (y : Plane) := v y ^ 3 - v y
  let W (t : ℝ) := (∑ i : Fin 2, ∫ y, a i y * g i (y + t • e)) + ∫ y, η y * F (y + t • e)
  have hg (i : Fin 2) : ContDiff ℝ 1 (g i) :=
    (hv.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
  have ha (i : Fin 2) : Continuous (a i) :=
    (hη.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hac (i : Fin 2) : HasCompactSupport (a i) := hηc.fderiv_apply ℝ (b i)
  have hV : ContDiff ℝ 1 v := hv.regular.of_le (by norm_num)
  have hF : ContDiff ℝ 1 F := (hV.pow 3).sub hV
  have hW : W = fun _ => 0 := by
    funext t
    have hLi (i : Fin 2) : Integrable (fun y => η y * fderiv ℝ (g i) (y + t • e) (b i)) :=
      integrate_compact_mul2 hη.continuous
        (((hg i).continuous_fderiv one_ne_zero).clm_apply continuous_const |>.comp
          (continuous_id.add continuous_const)) hηc
    have hsum : (∑ i : Fin 2, ∫ y, a i y * g i (y + t • e)) = -(∫ y, η y * F (y + t • e)) := by
      calc
        _ = ∑ i : Fin 2, -(∫ y, η y * fderiv ℝ (g i) (y + t • e) (b i)) :=
          Finset.sum_congr rfl fun i _ => integrate_shifted_by_parts2 (hg i) hη hηc _ _
        _ = -(∫ y, ∑ i : Fin 2, η y * fderiv ℝ (g i) (y + t • e) (b i)) := by
          rw [Finset.sum_neg_distrib, integral_finsetSum _ (fun i _ => hLi i)]
        _ = _ := by
          congr 1
          apply integral_congr_ae
          filter_upwards [] with y
          rw [← Finset.mul_sum]
          have hlap : (∑ i : Fin 2, fderiv ℝ (g i) (y + t • e) (b i)) = (Δ v) (y + t • e) := by
            rw [laplacian_eq_iteratedFDeriv_orthonormalBasis v b]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [iteratedFDeriv_two_apply]
            have hpa : fderiv ℝ (g i) (y + t • e) (b i) =
                (fderiv ℝ (fderiv ℝ v) (y + t • e) (b i)) (b i) := by
              unfold g
              rw [fderiv_clm_apply ((hv.regular.fderiv_right (by norm_num)).differentiable
                one_ne_zero _) (differentiableAt_const (b i))]
              simp
            simpa [Matrix.cons_val_zero, Matrix.cons_val_one] using hpa
          rw [hlap]
          have hsol := hv.solution (y + t • e)
          have hFeq : (Δ v) (y + t • e) = F (y + t • e) := by dsimp [F]; linarith
          rw [hFeq]
    dsimp [W]
    linarith
  have hd_sum : HasDerivAt (fun t : ℝ => ∑ i : Fin 2, ∫ y, a i y * g i (y + t • e))
      (∑ i : Fin 2, ∫ y, a i y * fderiv ℝ (g i) y e) 0 :=
    HasDerivAt.fun_sum (u := Finset.univ) fun i _ => shifted_integral_deriv2 (ha i) (hac i) (hg i) e
  have hd_F : HasDerivAt (fun t : ℝ => ∫ y, η y * F (y + t • e))
      (∫ y, η y * fderiv ℝ F y e) 0 :=
    shifted_integral_deriv2 hη.continuous hηc hF e
  have hd_W : HasDerivAt W
      ((∑ i : Fin 2, ∫ y, a i y * fderiv ℝ (g i) y e) + ∫ y, η y * fderiv ℝ F y e) 0 :=
    hd_sum.add hd_F
  rw [hW] at hd_W
  have hzero := hd_W.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have hF_deriv (y : Plane) : fderiv ℝ F y e = (3 * (v y) ^ 2 - 1) * fderiv ℝ v y e := by
    have h := (hv.regular.differentiable (by norm_num) y).hasFDerivAt
    have he := congrArg (fun L : Plane →L[ℝ] ℝ => L e) ((h.pow 3).sub h).fderiv
    simp only [sub_apply, smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at he
    change fderiv ℝ F y e = 3 * v y ^ (3 - 1) * fderiv ℝ v y e - fderiv ℝ v y e at he
    rw [he]; norm_num; ring
  have hcomm (i : Fin 2) (y : Plane) :
      fderiv ℝ (g i) y e = fderiv ℝ (fun z => fderiv ℝ v z e) y (b i) := by
    have h1 : fderiv ℝ (g i) y e = (fderiv ℝ (fderiv ℝ v) y e) (b i) := by
      unfold g
      rw [fderiv_clm_apply ((hv.regular.fderiv_right (by norm_num)).differentiable
        one_ne_zero y) (differentiableAt_const (b i))]
      simp
    have h2 : fderiv ℝ (fun z => fderiv ℝ v z e) y (b i) =
        (fderiv ℝ (fderiv ℝ v) y (b i)) e := by
      rw [fderiv_clm_apply ((hv.regular.fderiv_right (by norm_num)).differentiable
        one_ne_zero y) (differentiableAt_const e)]
      simp
    rw [h1, h2]
    exact (hv.regular.contDiffAt.isSymmSndFDerivAt (by simp)) e (b i)
  have hgrad_sum :
      (∑ i : Fin 2, ∫ y, a i y * fderiv ℝ (g i) y e) =
      ∫ y, inner ℝ (∇ (fun z => fderiv ℝ v z e) y) (∇ η y) := by
    have hint (i : Fin 2) : Integrable (fun y => a i y * fderiv ℝ (g i) y e) :=
      integrate_compact_mul2 (ha i)
        (((hg i).continuous_fderiv one_ne_zero).clm_apply continuous_const) (hac i)
    rw [← integral_finsetSum _ (fun i _ => hint i)]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdu (f : Plane → ℝ) : inner ℝ (∇ f y) (b i) = fderiv ℝ f y (b i) := by
      rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]
    rw [hcomm i y, hdu, real_inner_comm (∇ η y) (b i), hdu]
    dsimp [a]
    ring
  rw [← hgrad_sum]
  simp_rw [← hF_deriv]
  exact hzero

private noncomputable def part2 (v : Plane → ℝ) (i : Fin 2) (y : Plane) : ℝ :=
  fderiv ℝ v y (e2 i)

private noncomputable def part22 (v : Plane → ℝ) (i j : Fin 2) (y : Plane) : ℝ :=
  fderiv ℝ (part2 v i) y (e2 j)

private theorem sternberg_zumbrun2 {v : Plane → ℝ}
    (hv : DeGiorgi.IsBoundedSolution v)
    (hstab : ∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      0 ≤ ∫ y : Plane, (‖∇ ψ y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (ψ y) ^ 2))
    {η : Plane → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ y : Plane, (η y) ^ 2 *
        ((part2 v 0 y * part22 v 1 0 y - part2 v 1 y * part22 v 0 0 y) ^ 2 +
         (part2 v 0 y * part22 v 1 1 y - part2 v 1 y * part22 v 0 1 y) ^ 2) /
        ((part2 v 0 y) ^ 2 + (part2 v 1 y) ^ 2 + δ ^ 2)) ≤
      ∫ y : Plane, ‖∇ v y‖ ^ 2 * ‖∇ η y‖ ^ 2 := by
  let v0 := part2 v 0
  let v1 := part2 v 1
  have hv0_c1 : ContDiff ℝ 1 v0 :=
    (hv.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hv1_c1 : ContDiff ℝ 1 v1 :=
    (hv.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hcont_g2 {f : Plane → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (∇ f) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
  have hcomp_g2 {f : Plane → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (∇ f) := by
    apply hf.mono'; intro y hy; apply support_fderiv_subset ℝ
    intro h0; exact hy (by simp [gradient, h0])
  have hnorm_v (y : Plane) : ‖∇ v y‖ ^ 2 = (v0 y) ^ 2 + (v1 y) ^ 2 := by
    let b := EuclideanSpace.basisFun (Fin 2) ℝ
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner, Fin.sum_univ_two]
    have h0 : b 0 = e2 0 := EuclideanSpace.basisFun_apply (Fin 2) ℝ 0
    have h1 : b 1 = e2 1 := EuclideanSpace.basisFun_apply (Fin 2) ℝ 1
    have hd0 : inner ℝ (∇ v y) (e2 0) = v0 y := by
      rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]; rfl
    have hd0' : inner ℝ (e2 0) (∇ v y) = v0 y := (real_inner_comm _ _).trans hd0
    have hd1 : inner ℝ (∇ v y) (e2 1) = v1 y := by
      rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]; rfl
    have hd1' : inner ℝ (e2 1) (∇ v y) = v1 y := (real_inner_comm _ _).trans hd1
    rw [h0, h1, hd0, hd0', hd1, hd1']
    ring
  have hnorm_p (f : Plane → ℝ) (y : Plane) :
      ‖∇ f y‖ ^ 2 = (fderiv ℝ f y (e2 0)) ^ 2 + (fderiv ℝ f y (e2 1)) ^ 2 := by
    let b := EuclideanSpace.basisFun (Fin 2) ℝ
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner, Fin.sum_univ_two]
    have h0 : b 0 = e2 0 := EuclideanSpace.basisFun_apply (Fin 2) ℝ 0
    have h1 : b 1 = e2 1 := EuclideanSpace.basisFun_apply (Fin 2) ℝ 1
    have hd0 : inner ℝ (∇ f y) (e2 0) = fderiv ℝ f y (e2 0) := by
      rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]
    have hd0' : inner ℝ (e2 0) (∇ f y) = fderiv ℝ f y (e2 0) := (real_inner_comm _ _).trans hd0
    have hd1 : inner ℝ (∇ f y) (e2 1) = fderiv ℝ f y (e2 1) := by
      rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]
    have hd1' : inner ℝ (e2 1) (∇ f y) = fderiv ℝ f y (e2 1) := (real_inner_comm _ _).trans hd1
    rw [h0, h1, hd0, hd0', hd1, hd1']
    ring
  -- Weak identity for v0 * η^2 and v1 * η^2
  have hweak_v (i : Fin 2) :
      (∫ y, (η y) ^ 2 * ‖∇ (part2 v i) y‖ ^ 2 +
        2 * η y * part2 v i y * inner ℝ (∇ (part2 v i) y) (∇ η y) +
        (3 * (v y) ^ 2 - 1) * (part2 v i y) ^ 2 * (η y) ^ 2) = 0 := by
    let vi := part2 v i
    have hvi_c1 : ContDiff ℝ 1 vi :=
      (hv.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
    let ψ := fun y : Plane => vi y * (η y) ^ 2
    have hψ_c1 : ContDiff ℝ 1 ψ := hvi_c1.mul (hη.pow 2)
    have hψc : HasCompactSupport ψ := by
      apply hηc.mono'; intro y hy; apply subset_closure; intro h0
      exact hy (by change vi y * (η y) ^ 2 = 0; rw [h0]; simp)
    have hw := weak_partial2 hv (e2 i) hψ_c1 hψc
    have hgrad_ψ (y : Plane) :
        ∇ ψ y = (η y) ^ 2 • ∇ vi y + (2 * vi y * η y) • ∇ η y := by
      have hd1 := (hvi_c1.differentiable one_ne_zero y).hasFDerivAt
      have hd2 := (hη.differentiable one_ne_zero y).hasFDerivAt
      have hsq : HasFDerivAt (fun z => (η z) ^ 2) ((2 * η y) • fderiv ℝ η y) y := by
        have h := hd2.pow 2
        simpa [show 2 - 1 = 1 by decide, pow_one, nsmul_eq_mul, mul_comm, smul_smul] using h
      have hfd := (hd1.mul hsq).fderiv
      unfold gradient
      change (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ ((fun z => vi z) * (fun z => (η z) ^ 2)) y) = _
      rw [hfd, map_add, map_smul, map_smul, map_smul]
      rw [add_comm, smul_smul]
      congr 1; congr 1; ring
    have hint1 : Integrable (fun y => inner ℝ (∇ vi y) (∇ ψ y)) :=
      ((hcont_g2 hvi_c1).inner (hcont_g2 hψ_c1)).integrable_of_hasCompactSupport
        (by apply (hcomp_g2 hψc).mono'; intro y hy; apply subset_closure; intro h0
            exact hy (by change inner ℝ (∇ vi y) (∇ ψ y) = 0; rw [h0]; simp))
    have hint2 : Integrable (fun y => ψ y * ((3 * (v y) ^ 2 - 1) * vi y)) :=
      (hψ_c1.continuous.mul (((continuous_const.mul (hv.regular.continuous.pow 2)).sub
        continuous_const).mul hvi_c1.continuous)).integrable_of_hasCompactSupport
        (by apply hψc.mono'; intro y hy; apply subset_closure; intro h0
            exact hy (by change ψ y * ((3 * (v y) ^ 2 - 1) * vi y) = 0; rw [h0]; simp))
    change (∫ y, inner ℝ (∇ vi y) (∇ ψ y)) + (∫ y, ψ y * ((3 * (v y) ^ 2 - 1) * vi y)) = 0 at hw
    rw [← integral_add hint1 hint2] at hw
    convert hw using 2
    funext y
    rw [hgrad_ψ y, inner_add_right, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq]
    dsimp [ψ, vi]
    ring
  -- Regularized inequality for every 0 < ε <= δ
  have heps_ineq {ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) :
      (∫ y : Plane, (η y) ^ 2 *
          ((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
           (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) /
          ((v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2)) ≤
        (∫ y : Plane, ‖∇ v y‖ ^ 2 * ‖∇ η y‖ ^ 2) +
          ε ^ 2 * (∫ y : Plane, ‖∇ η y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (η y) ^ 2) := by
    let r2 : Plane → ℝ := fun y => (v0 y) ^ 2 + (v1 y) ^ 2 + ε ^ 2
    have hr2_pos : ∀ y, 0 < r2 y := fun y => by dsimp [r2]; positivity
    let w : Plane → ℝ := fun y => Real.sqrt (r2 y)
    have hw_pos : ∀ y, 0 < w y := fun y => Real.sqrt_pos.mpr (hr2_pos y)
    have hr2_c1 : ContDiff ℝ 1 r2 := ((hv0_c1.pow 2).add (hv1_c1.pow 2)).add contDiff_const
    have hw_c1 : ContDiff ℝ 1 w := hr2_c1.sqrt fun y => (hr2_pos y).ne'
    let φ : Plane → ℝ := fun y => w y * η y
    have hφ_c1 : ContDiff ℝ 1 φ := hw_c1.mul hη
    have hφc : HasCompactSupport φ := by
      apply hηc.mono'; intro y hy; apply subset_closure; intro h0
      exact hy (by change w y * η y = 0; rw [h0]; simp)
    have hst := hstab φ hφ_c1 hφc
    have hgrad_w (y : Plane) :
        w y • ∇ w y = v0 y • ∇ v0 y + v1 y • ∇ v1 y := by
      have hd0 := (hv0_c1.differentiable one_ne_zero y).hasFDerivAt
      have hd1 := (hv1_c1.differentiable one_ne_zero y).hasFDerivAt
      have hsq0 : HasFDerivAt (fun z => (v0 z) ^ 2) ((2 * v0 y) • fderiv ℝ v0 y) y := by
        simpa [show 2 - 1 = 1 by decide, pow_one, nsmul_eq_mul, mul_comm, smul_smul] using hd0.pow 2
      have hsq1 : HasFDerivAt (fun z => (v1 z) ^ 2) ((2 * v1 y) • fderiv ℝ v1 y) y := by
        simpa [show 2 - 1 = 1 by decide, pow_one, nsmul_eq_mul, mul_comm, smul_smul] using hd1.pow 2
      have hr2_fd : HasFDerivAt r2 ((2 * v0 y) • fderiv ℝ v0 y + (2 * v1 y) • fderiv ℝ v1 y) y :=
        (hsq0.add hsq1).add_const (ε ^ 2)
      have hdw : HasFDerivAt (fun z => (w z) ^ 2) ((2 * w y) • fderiv ℝ w y) y := by
        have h := (hw_c1.differentiable one_ne_zero y).hasFDerivAt.pow 2
        simpa [show 2 - 1 = 1 by decide, pow_one, nsmul_eq_mul, mul_comm, smul_smul] using h
      have hsq_eq : (fun z => (w z) ^ 2) = r2 := funext fun z => Real.sq_sqrt (hr2_pos z).le
      rw [hsq_eq] at hdw
      have heq := hdw.unique hr2_fd
      unfold gradient
      have h2 : (2 * w y) • (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ w y) =
          (2 * v0 y) • (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ v0 y) +
          (2 * v1 y) • (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ v1 y) := by
        rw [← map_smul, heq, map_add, map_smul, map_smul]
      have hhalf := congrArg (fun z : Plane => (2⁻¹ : ℝ) • z) h2
      simp only [smul_add, smul_smul] at hhalf
      convert hhalf using 1 <;> [congr 1; congr 1 <;> congr 1] <;> ring
    have hgrad_φ (y : Plane) : ∇ φ y = η y • ∇ w y + w y • ∇ η y := by
      have hd1 := (hw_c1.differentiable one_ne_zero y).hasFDerivAt
      have hd2 := (hη.differentiable one_ne_zero y).hasFDerivAt
      have hfd := (hd1.mul hd2).fderiv
      unfold gradient
      change (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ (w * η) y) = _
      rw [hfd, map_add, map_smul, map_smul, add_comm]
    -- Lagrange identity pointwise: ||grad v0||^2 + ||grad v1||^2 - ||grad w||^2 >= det^2 / (|grad v|^2 + delta^2)
    have hlagrange (y : Plane) :
        ((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
         (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) /
        ((v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2) ≤
        ‖∇ v0 y‖ ^ 2 + ‖∇ v1 y‖ ^ 2 - ‖∇ w y‖ ^ 2 := by
      have hgw_sq : r2 y * ‖∇ w y‖ ^ 2 =
          (v0 y * part22 v 0 0 y + v1 y * part22 v 1 0 y) ^ 2 +
          (v0 y * part22 v 0 1 y + v1 y * part22 v 1 1 y) ^ 2 := by
        have h1 : ‖w y • ∇ w y‖ ^ 2 = r2 y * ‖∇ w y‖ ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (hr2_pos y).le]
        rw [← h1, hgrad_w y]
        let b := EuclideanSpace.basisFun (Fin 2) ℝ
        rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner, Fin.sum_univ_two]
        have h0 : b 0 = e2 0 := EuclideanSpace.basisFun_apply (Fin 2) ℝ 0
        have h1' : b 1 = e2 1 := EuclideanSpace.basisFun_apply (Fin 2) ℝ 1
        have hdu (f : Plane → ℝ) (k : Fin 2) : inner ℝ (∇ f y) (e2 k) = fderiv ℝ f y (e2 k) := by
          rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]
        have hc (k : Fin 2) :
            inner ℝ (v0 y • ∇ v0 y + v1 y • ∇ v1 y) (e2 k) =
            v0 y * part22 v 0 k y + v1 y * part22 v 1 k y := by
          rw [inner_add_left, inner_smul_left, inner_smul_left, hdu, hdu]
          rfl
        have hc' (k : Fin 2) :
            inner ℝ (e2 k) (v0 y • ∇ v0 y + v1 y • ∇ v1 y) =
            v0 y * part22 v 0 k y + v1 y * part22 v 1 k y :=
          (real_inner_comm _ _).trans (hc k)
        rw [h0, h1', hc 0, hc' 0, hc 1, hc' 1]
        ring
      have hnum :
          r2 y * (‖∇ v0 y‖ ^ 2 + ‖∇ v1 y‖ ^ 2 - ‖∇ w y‖ ^ 2) =
          ε ^ 2 * (‖∇ v0 y‖ ^ 2 + ‖∇ v1 y‖ ^ 2) +
          (v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
          (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2 := by
        rw [mul_sub, hgw_sq, hnorm_p v0 y, hnorm_p v1 y]
        dsimp [r2, part22, v0, v1]
        ring
      have hge0 :
          ((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
           (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) / r2 y ≤
          ‖∇ v0 y‖ ^ 2 + ‖∇ v1 y‖ ^ 2 - ‖∇ w y‖ ^ 2 := by
        rw [div_le_iff₀ (hr2_pos y), mul_comm _ (r2 y), hnum]
        have hnn : 0 ≤ ε ^ 2 * (‖∇ v0 y‖ ^ 2 + ‖∇ v1 y‖ ^ 2) := by positivity
        linarith
      have hr2_le : r2 y ≤ (v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2 := by
        dsimp [r2]
        have : ε ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hε.le hεδ 2
        linarith
      exact le_trans (div_le_div_of_nonneg_left (by positivity) (hr2_pos y) hr2_le) hge0
    -- Pointwise identity combining stability and weak equations
    have hpt_ident (y : Plane) :
        (‖∇ φ y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (φ y) ^ 2) -
        ((η y) ^ 2 * ‖∇ v0 y‖ ^ 2 + 2 * η y * v0 y * inner ℝ (∇ v0 y) (∇ η y) +
          (3 * (v y) ^ 2 - 1) * (v0 y) ^ 2 * (η y) ^ 2) -
        ((η y) ^ 2 * ‖∇ v1 y‖ ^ 2 + 2 * η y * v1 y * inner ℝ (∇ v1 y) (∇ η y) +
          (3 * (v y) ^ 2 - 1) * (v1 y) ^ 2 * (η y) ^ 2) =
        -(η y) ^ 2 * (‖∇ v0 y‖ ^ 2 + ‖∇ v1 y‖ ^ 2 - ‖∇ w y‖ ^ 2) +
          ‖∇ v y‖ ^ 2 * ‖∇ η y‖ ^ 2 +
          ε ^ 2 * (‖∇ η y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (η y) ^ 2) := by
      have hφ_sq : ‖∇ φ y‖ ^ 2 =
          (η y) ^ 2 * ‖∇ w y‖ ^ 2 + 2 * η y * w y * inner ℝ (∇ w y) (∇ η y) +
          r2 y * ‖∇ η y‖ ^ 2 := by
        rw [hgrad_φ y, norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          mul_pow, mul_pow, sq_abs, sq_abs, Real.sq_sqrt (hr2_pos y).le,
          inner_smul_left, inner_smul_right]
        simp only [conj_trivial]
        ring
      have hcross : w y * inner ℝ (∇ w y) (∇ η y) =
          v0 y * inner ℝ (∇ v0 y) (∇ η y) + v1 y * inner ℝ (∇ v1 y) (∇ η y) := by
        have h1 : inner ℝ (w y • ∇ w y) (∇ η y) =
            inner ℝ (v0 y • ∇ v0 y + v1 y • ∇ v1 y) (∇ η y) := by rw [hgrad_w y]
        rw [inner_smul_left, inner_add_left, inner_smul_left, inner_smul_left] at h1
        simpa using h1
      have hφ_pot : (φ y) ^ 2 = r2 y * (η y) ^ 2 := by
        dsimp [φ]; rw [mul_pow, Real.sq_sqrt (hr2_pos y).le]
      rw [hφ_sq, hφ_pot, hnorm_v y]
      dsimp [r2]
      have hcross2 : 2 * η y * w y * inner ℝ (∇ w y) (∇ η y) =
          2 * η y * v0 y * inner ℝ (∇ v0 y) (∇ η y) +
          2 * η y * v1 y * inner ℝ (∇ v1 y) (∇ η y) := by
        linear_combination 2 * η y * hcross
      linarith [hcross2]
    -- Integrate the pointwise inequality
    have hint_stab : Integrable (fun y => ‖∇ φ y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (φ y) ^ 2) :=
      (((hcont_g2 hφ_c1).norm.pow 2).add
        (((continuous_const.mul (hv.regular.continuous.pow 2)).sub continuous_const).mul
          (hφ_c1.continuous.pow 2))).integrable_of_hasCompactSupport
        (by
          apply HasCompactSupport.of_support_subset_isCompact ((hcomp_g2 hφc).union hφc)
          intro y hy; by_contra hn
          have h1 : ∇ φ y = 0 := by by_contra h; exact hn (Or.inl (subset_closure h))
          have h2 : φ y = 0 := by by_contra h; exact hn (Or.inr (subset_closure h))
          exact hy (by change ‖∇ φ y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (φ y) ^ 2 = 0; rw [h1, h2]; simp))
    have hint_wi (i : Fin 2) :
        Integrable (fun y => (η y) ^ 2 * ‖∇ (part2 v i) y‖ ^ 2 +
          2 * η y * part2 v i y * inner ℝ (∇ (part2 v i) y) (∇ η y) +
          (3 * (v y) ^ 2 - 1) * (part2 v i y) ^ 2 * (η y) ^ 2) := by
      have hvi_c1 : ContDiff ℝ 1 (part2 v i) :=
        (hv.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
      refine ((((hη.continuous.pow 2).mul ((hcont_g2 hvi_c1).norm.pow 2)).add
        (((continuous_const.mul hη.continuous).mul hvi_c1.continuous).mul
          ((hcont_g2 hvi_c1).inner (hcont_g2 hη)))).add
        ((((continuous_const.mul (hv.regular.continuous.pow 2)).sub continuous_const).mul
          (hvi_c1.continuous.pow 2)).mul (hη.continuous.pow 2))).integrable_of_hasCompactSupport ?_
      apply hηc.mono'
      intro y hy
      apply subset_closure
      intro h0
      apply hy
      change (η y) ^ 2 * ‖∇ (part2 v i) y‖ ^ 2 +
        2 * η y * part2 v i y * inner ℝ (∇ (part2 v i) y) (∇ η y) +
        (3 * (v y) ^ 2 - 1) * (part2 v i y) ^ 2 * (η y) ^ 2 = 0
      rw [h0]
      simp
    have hint_lhs : Integrable (fun y : Plane => (η y) ^ 2 *
        ((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
         (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) /
        ((v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2)) := by
      have hp22c (i j : Fin 2) : Continuous (part22 v i j) :=
        (((hv.regular.fderiv_right (by norm_num)).clm_apply contDiff_const).continuous_fderiv
          one_ne_zero).clm_apply continuous_const
      have hcont : Continuous (fun y : Plane => (η y) ^ 2 *
          ((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
           (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) /
          ((v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2)) := by
        refine (((hη.continuous.pow 2).mul
          ((((hv0_c1.continuous.mul (hp22c 1 0)).sub (hv1_c1.continuous.mul (hp22c 0 0))).pow 2).add
           (((hv0_c1.continuous.mul (hp22c 1 1)).sub (hv1_c1.continuous.mul (hp22c 0 1))).pow 2)))).div
          (((hv0_c1.continuous.pow 2).add (hv1_c1.continuous.pow 2)).add continuous_const)
          fun y => by positivity
      refine hcont.integrable_of_hasCompactSupport ?_
      apply hηc.mono'; intro y hy; apply subset_closure; intro h0
      exact hy (by change (η y) ^ 2 * _ / _ = 0; rw [h0]; simp)
    have hint_r1 : Integrable (fun y : Plane => ‖∇ v y‖ ^ 2 * ‖∇ η y‖ ^ 2) :=
      (((hcont_g2 (hv.regular.of_le (by norm_num))).norm.pow 2).mul
        ((hcont_g2 hη).norm.pow 2)).integrable_of_hasCompactSupport
        (by apply (hcomp_g2 hηc).mono'; intro y hy; apply subset_closure; intro h0
            exact hy (by change ‖∇ v y‖ ^ 2 * ‖∇ η y‖ ^ 2 = 0; rw [h0]; simp))
    have hint_r2 : Integrable (fun y : Plane => ‖∇ η y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (η y) ^ 2) :=
      (((hcont_g2 hη).norm.pow 2).add
        (((continuous_const.mul (hv.regular.continuous.pow 2)).sub continuous_const).mul
          (hη.continuous.pow 2))).integrable_of_hasCompactSupport
        (by
          apply HasCompactSupport.of_support_subset_isCompact ((hcomp_g2 hηc).union hηc)
          intro y hy; by_contra hn
          have h1 : ∇ η y = 0 := by by_contra h; exact hn (Or.inl (subset_closure h))
          have h2 : η y = 0 := by by_contra h; exact hn (Or.inr (subset_closure h))
          exact hy (by change ‖∇ η y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (η y) ^ 2 = 0; rw [h1, h2]; simp))
    have hsub0 : Integrable (fun y : Plane =>
        (‖∇ φ y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (φ y) ^ 2) -
        ((η y) ^ 2 * ‖∇ v0 y‖ ^ 2 + 2 * η y * v0 y * inner ℝ (∇ v0 y) (∇ η y) +
          (3 * (v y) ^ 2 - 1) * (v0 y) ^ 2 * (η y) ^ 2)) :=
      hint_stab.sub (hint_wi 0)
    have hcomb_ge : 0 ≤ ∫ y : Plane,
        ((‖∇ φ y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (φ y) ^ 2) -
         ((η y) ^ 2 * ‖∇ v0 y‖ ^ 2 + 2 * η y * v0 y * inner ℝ (∇ v0 y) (∇ η y) +
           (3 * (v y) ^ 2 - 1) * (v0 y) ^ 2 * (η y) ^ 2) -
         ((η y) ^ 2 * ‖∇ v1 y‖ ^ 2 + 2 * η y * v1 y * inner ℝ (∇ v1 y) (∇ η y) +
           (3 * (v y) ^ 2 - 1) * (v1 y) ^ 2 * (η y) ^ 2)) := by
      rw [integral_sub hsub0 (hint_wi 1), integral_sub hint_stab (hint_wi 0)]
      linarith [hst, hweak_v 0, hweak_v 1]
    have hpt_le (y : Plane) :
        ((‖∇ φ y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (φ y) ^ 2) -
         ((η y) ^ 2 * ‖∇ v0 y‖ ^ 2 + 2 * η y * v0 y * inner ℝ (∇ v0 y) (∇ η y) +
           (3 * (v y) ^ 2 - 1) * (v0 y) ^ 2 * (η y) ^ 2) -
         ((η y) ^ 2 * ‖∇ v1 y‖ ^ 2 + 2 * η y * v1 y * inner ℝ (∇ v1 y) (∇ η y) +
           (3 * (v y) ^ 2 - 1) * (v1 y) ^ 2 * (η y) ^ 2)) ≤
        -(η y) ^ 2 *
          ((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
           (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) /
          ((v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2) +
          ‖∇ v y‖ ^ 2 * ‖∇ η y‖ ^ 2 +
          ε ^ 2 * (‖∇ η y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (η y) ^ 2) := by
      rw [hpt_ident y]
      have h1 := mul_le_mul_of_nonneg_left (hlagrange y) (sq_nonneg (η y))
      have hdiv_eq : -(η y) ^ 2 *
          ((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
           (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) /
          ((v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2) =
          -((η y) ^ 2 * (((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
           (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) /
          ((v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2))) := by ring
      rw [hdiv_eq]
      linarith
    have hint_rhs : Integrable (fun y : Plane =>
        -(η y) ^ 2 *
          ((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
           (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) /
          ((v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2) +
          ‖∇ v y‖ ^ 2 * ‖∇ η y‖ ^ 2 +
          ε ^ 2 * (‖∇ η y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (η y) ^ 2)) := by
      have hneg : Integrable (fun y : Plane => -(η y) ^ 2 *
          ((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
           (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) /
          ((v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2)) := by
        simpa [neg_mul, neg_div] using hint_lhs.neg
      exact (hneg.add hint_r1).add (hint_r2.const_mul (ε ^ 2))
    have hmon := integral_mono (hsub0.sub (hint_wi 1)) hint_rhs hpt_le
    have hneg_eq : (fun y : Plane => -(η y) ^ 2 *
        ((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
         (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) /
        ((v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2)) =
        fun y => -((η y) ^ 2 *
        ((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
         (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) /
        ((v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2)) := by
      funext y; ring
    have hrhs_eval : (∫ y : Plane,
        -(η y) ^ 2 *
          ((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
           (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) /
          ((v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2) +
          ‖∇ v y‖ ^ 2 * ‖∇ η y‖ ^ 2 +
          ε ^ 2 * (‖∇ η y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (η y) ^ 2)) =
        -(∫ y : Plane, (η y) ^ 2 *
          ((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
           (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) /
          ((v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2)) +
          (∫ y : Plane, ‖∇ v y‖ ^ 2 * ‖∇ η y‖ ^ 2) +
          ε ^ 2 * (∫ y : Plane, ‖∇ η y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (η y) ^ 2) := by
      have hneg_int : Integrable (fun y : Plane => -(η y) ^ 2 *
          ((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
           (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) /
          ((v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2)) := by
        rw [hneg_eq]; exact hint_lhs.neg
      have hadd1 : Integrable (fun y : Plane =>
          -(η y) ^ 2 *
            ((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
             (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) /
            ((v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2) +
          ‖∇ v y‖ ^ 2 * ‖∇ η y‖ ^ 2) := hneg_int.add hint_r1
      rw [integral_add hadd1 (hint_r2.const_mul (ε ^ 2)),
        integral_add hneg_int hint_r1, hneg_eq, integral_neg, integral_const_mul]
    rw [hrhs_eval] at hmon
    have hle0 : 0 ≤ -(∫ y : Plane, (η y) ^ 2 *
          ((v0 y * part22 v 1 0 y - v1 y * part22 v 0 0 y) ^ 2 +
           (v0 y * part22 v 1 1 y - v1 y * part22 v 0 1 y) ^ 2) /
          ((v0 y) ^ 2 + (v1 y) ^ 2 + δ ^ 2)) +
          (∫ y : Plane, ‖∇ v y‖ ^ 2 * ‖∇ η y‖ ^ 2) +
          ε ^ 2 * (∫ y : Plane, ‖∇ η y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (η y) ^ 2) :=
      hcomb_ge.trans hmon
    linarith
  -- Send ε -> 0+
  let Rterm := ∫ y : Plane, ‖∇ η y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (η y) ^ 2
  have htend : Tendsto (fun n : ℕ =>
      (∫ y : Plane, ‖∇ v y‖ ^ 2 * ‖∇ η y‖ ^ 2) +
        (min δ (1 / ((n : ℝ) + 1))) ^ 2 * Rterm) atTop
      (𝓝 (∫ y : Plane, ‖∇ v y‖ ^ 2 * ‖∇ η y‖ ^ 2)) := by
    have h0 : Tendsto (fun n : ℕ => min δ (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hmin := (tendsto_const_nhds (x := δ)).min hinv
      simpa [min_eq_right hδ.le] using hmin
    have hsq := (h0.pow 2).mul_const Rterm
    simpa using tendsto_const_nhds.add hsq
  refine ge_of_tendsto htend (Eventually.of_forall fun n => ?_)
  exact heps_ineq (lt_min hδ (by positivity)) (min_le_left _ _)

private noncomputable def smoothStep (t : ℝ) : ℝ :=
  if t ≤ 0 then 1 else bump1 (t + 1)

private theorem smoothStep_props :
    ContDiff ℝ 1 smoothStep ∧
    (∀ t, 0 ≤ smoothStep t ∧ smoothStep t ≤ 1) ∧
    (∀ t ≤ 0, smoothStep t = 1) ∧
    (∀ t ≥ 1, smoothStep t = 0) ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |deriv smoothStep t| ≤ M := by
  have hcont_at (t : ℝ) : ContDiffAt ℝ 1 smoothStep t := by
    by_cases ht : t < 0
    · have heq : smoothStep =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
        exact if_pos hs.le
      exact contDiffAt_const.congr_of_eventuallyEq heq
    · push Not at ht
      have hgt : (-1 : ℝ) < t := by linarith
      have heq : smoothStep =ᶠ[𝓝 t] fun s => bump1 (s + 1) := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with s hs
        by_cases hs0 : s ≤ 0
        · rw [smoothStep, if_pos hs0]
          symm
          apply bump1.one_of_mem_closedBall
          rw [Set.mem_Ioi] at hs
          rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le,
            show bump1.rIn = 1 from rfl]
          constructor <;> linarith
        · rw [smoothStep, if_neg hs0]
      exact ((bump1.contDiff (n := 1)).comp (contDiff_id.add contDiff_const)).contDiffAt.congr_of_eventuallyEq heq
  have hc1 : ContDiff ℝ 1 smoothStep := contDiff_iff_contDiffAt.mpr hcont_at
  have hbd (t : ℝ) : 0 ≤ smoothStep t ∧ smoothStep t ≤ 1 := by
    unfold smoothStep
    split_ifs
    · exact ⟨by norm_num, le_rfl⟩
    · exact ⟨bump1.nonneg, bump1.le_one⟩
  have hle0 (t : ℝ) (ht : t ≤ 0) : smoothStep t = 1 := if_pos ht
  have hge1 (t : ℝ) (ht : 1 ≤ t) : smoothStep t = 0 := by
    rw [smoothStep, if_neg (by linarith)]
    apply bump1.zero_of_le_dist
    change 2 ≤ dist (t + 1) 0
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  obtain ⟨M, hM⟩ := (bump1.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    ((bump1.contDiff (n := 1)).continuous_fderiv one_ne_zero)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hderiv_bd (t : ℝ) : |deriv smoothStep t| ≤ M := by
    by_cases ht : t < 0
    · have heq : smoothStep =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
        exact if_pos hs.le
      rw [heq.deriv_eq, deriv_const, abs_zero]
      exact hM0
    · push Not at ht
      have hgt : (-1 : ℝ) < t := by linarith
      have heq : smoothStep =ᶠ[𝓝 t] fun s => bump1 (s + 1) := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with s hs
        by_cases hs0 : s ≤ 0
        · rw [smoothStep, if_pos hs0]
          symm; apply bump1.one_of_mem_closedBall
          rw [Set.mem_Ioi] at hs
          rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le,
            show bump1.rIn = 1 from rfl]
          constructor <;> linarith
        · rw [smoothStep, if_neg hs0]
      rw [heq.deriv_eq]
      have hfd : HasDerivAt (fun s : ℝ => bump1 (s + 1)) (deriv (fun r : ℝ => bump1 r) (t + 1)) t := by
        have h1 := ((bump1.contDiff (n := 1)).differentiable one_ne_zero (t + 1)).hasDerivAt
        have h2 : HasDerivAt (fun s : ℝ => s + 1) 1 t := by
          simpa using (hasDerivAt_id t).add_const (1 : ℝ)
        simpa [Function.comp_def] using
          HasDerivAt.comp (h₂ := fun r : ℝ => bump1 r) (h := fun s : ℝ => s + 1) t h1 h2
      rw [hfd.deriv, ← Real.norm_eq_abs, norm_deriv_eq_norm_fderiv]
      exact hM (t + 1)
  exact ⟨hc1, hbd, hle0, hge1, M, hM0, hderiv_bd⟩

private noncomputable def planeIsoProd : Plane ≃ₗᵢ[ℝ] WithLp 2 (ℝ × ℝ) where
  toFun y := WithLp.toLp 2 (y 0, y 1)
  invFun p := (WithLp.ofLp p).1 • e2 0 + (WithLp.ofLp p).2 • e2 1
  map_add' x y := by apply WithLp.ofLp_injective 2; refine Prod.ext (by simp) (by simp)
  map_smul' c x := by apply WithLp.ofLp_injective 2; refine Prod.ext (by simp) (by simp)
  left_inv y := by ext i; fin_cases i <;> simp [e2]
  right_inv p := by
    apply WithLp.ofLp_injective 2
    refine Prod.ext (by simp [e2]) (by simp [e2])
  norm_map' y := by
    change ‖WithLp.toLp 2 (y 0, y 1)‖ = ‖y‖
    have hsq : ‖WithLp.toLp 2 (y 0, y 1)‖ ^ 2 = ‖y‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
      simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
      rfl
    nlinarith [norm_nonneg (WithLp.toLp 2 (y 0, y 1)), norm_nonneg y]

private noncomputable def planeHomeoProd : Plane ≃ₜ ℝ × ℝ where
  toFun y := (y 0, y 1)
  invFun p := p.1 • e2 0 + p.2 • e2 1
  left_inv y := by ext i; fin_cases i <;> simp [e2]
  right_inv p := by refine Prod.ext (by simp [e2]) (by simp [e2])
  continuous_toFun :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).prodMk
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)
  continuous_invFun :=
    (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)

private theorem integral_plane_eq_prod {f : Plane → ℝ} (hf : Integrable f) :
    (∫ y : Plane, f y) = ∫ s : ℝ, ∫ t : ℝ, f (s • e2 0 + t • e2 1) := by
  let e : Plane ≃ᵐ ℝ × ℝ := planeHomeoProd.toMeasurableEquiv
  have hmp : MeasurePreserving e volume (volume.prod volume) := by
    have hcomp : (e : Plane → ℝ × ℝ) = WithLp.ofLp ∘ (planeIsoProd : Plane → WithLp 2 (ℝ × ℝ)) := rfl
    rw [hcomp]
    exact (WithLp.volume_preserving_ofLp ℝ ℝ).comp planeIsoProd.measurePreserving
  let g : ℝ × ℝ → ℝ := fun p => f (p.1 • e2 0 + p.2 • e2 1)
  have hcomp : (fun y : Plane => g (e y)) = f := by
    funext y; change f (y 0 • e2 0 + y 1 • e2 1) = f y
    congr 1; ext i; fin_cases i <;> simp [e2]
  have hg_int : Integrable g (volume.prod volume) := by
    have h1 := hmp.integrable_comp_emb e.measurableEmbedding (g := g)
    rw [Function.comp_def, hcomp] at h1
    exact h1.mp hf
  calc
    (∫ y : Plane, f y) = ∫ y : Plane, g (e y) := by rw [hcomp]
    _ = ∫ p : ℝ × ℝ, g p ∂(volume.prod volume) := hmp.integral_comp' g
    _ = ∫ s : ℝ, ∫ t : ℝ, f (s • e2 0 + t • e2 1) := integral_prod g hg_int

private theorem volume_plane_box (a : ℝ) (ha : 0 ≤ a) :
    (volume ({y : Plane | |y 0| ≤ a ∧ |y 1| ≤ a})).toReal = 4 * a ^ 2 := by
  let S : Set Plane := {y | |y 0| ≤ a ∧ |y 1| ≤ a}
  have hS_eq : S = planeHomeoProd.toMeasurableEquiv ⁻¹' (Set.Icc (-a) a ×ˢ Set.Icc (-a) a) := by
    ext y
    change |y 0| ≤ a ∧ |y 1| ≤ a ↔ (-a ≤ y 0 ∧ y 0 ≤ a) ∧ (-a ≤ y 1 ∧ y 1 ≤ a)
    rw [abs_le, abs_le]
  have hmp : MeasurePreserving planeHomeoProd.toMeasurableEquiv volume (volume.prod volume) := by
    have hcomp : (planeHomeoProd.toMeasurableEquiv : Plane → ℝ × ℝ) =
        WithLp.ofLp ∘ (planeIsoProd : Plane → WithLp 2 (ℝ × ℝ)) := rfl
    rw [hcomp]
    exact (WithLp.volume_preserving_ofLp ℝ ℝ).comp planeIsoProd.measurePreserving
  change (volume S).toReal = 4 * a ^ 2
  rw [hS_eq, hmp.measure_preimage (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet,
    Measure.prod_prod, Real.volume_Icc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith)]
  ring

private theorem log_cutoff2_energy :
    ∃ C_log : ℝ, 0 ≤ C_log ∧ ∀ R : ℝ, 2 ≤ R →
      ∃ η : Plane → ℝ, ContDiff ℝ 1 η ∧ HasCompactSupport η ∧
        (∀ y ∈ closedBall (0 : Plane) R, η y = 1) ∧
        (∫ y : Plane, ‖∇ η y‖ ^ 2) ≤ C_log / Real.log (R ^ 2 + 1) := by
  obtain ⟨hζ_c1, _, hζ0, hζ1, Mζ, hMζ0, hMζ⟩ := smoothStep_props
  refine ⟨4 * Mζ ^ 2 * 84, by positivity, fun R hR => ?_⟩
  let L := Real.log (R ^ 2 + 1)
  have hR2_ge : 5 ≤ R ^ 2 + 1 := by nlinarith
  have hL_pos : 0 < L := Real.log_pos (by linarith)
  have hL_ge1 : 1 ≤ L := by
    have he : Real.exp 1 ≤ R ^ 2 + 1 := by
      have := Real.exp_one_lt_d9
      linarith
    exact (Real.le_log_iff_exp_le (by linarith)).mpr he
  let η : Plane → ℝ := fun y => smoothStep (Real.log (‖y‖ ^ 2 + 1) / L - 1)
  have hnorm_sq_c1 : ContDiff ℝ 1 (fun y : Plane => ‖y‖ ^ 2 + 1) := by
    have h1 : (fun y : Plane => ‖y‖ ^ 2 + 1) = fun y => (y 0) ^ 2 + (y 1) ^ 2 + 1 := by
      funext y
      rw [EuclideanSpace.norm_sq_eq]
      simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    rw [h1]
    have hc0 : ContDiff ℝ 1 (fun y : Plane => y 0) :=
      (((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.coord 0).toContinuousLinearMap).contDiff
    have hc1 : ContDiff ℝ 1 (fun y : Plane => y 1) :=
      (((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.coord 1).toContinuousLinearMap).contDiff
    exact ((hc0.pow 2).add (hc1.pow 2)).add contDiff_const
  have hlog_c1 : ContDiff ℝ 1 (fun y : Plane => Real.log (‖y‖ ^ 2 + 1) / L - 1) :=
    ((hnorm_sq_c1.log fun y => by positivity).div_const L).sub contDiff_const
  have hη_c1 : ContDiff ℝ 1 η := hζ_c1.comp hlog_c1
  have hη_one : ∀ y ∈ closedBall (0 : Plane) R, η y = 1 := by
    intro y hy
    rw [mem_closedBall, dist_zero_right] at hy
    have hsq : ‖y‖ ^ 2 + 1 ≤ R ^ 2 + 1 := by nlinarith [norm_nonneg y]
    have hlg : Real.log (‖y‖ ^ 2 + 1) ≤ L := Real.log_le_log (by positivity) hsq
    have harg : Real.log (‖y‖ ^ 2 + 1) / L - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hL_pos]; exact hlg
    exact hζ0 _ harg
  let A : ℝ := R ^ 2 + 1
  have hA1 : 1 ≤ A := by dsimp [A]; nlinarith
  have hη_zero_out : ∀ y : Plane, A ≤ ‖y‖ → η y = 0 := by
    intro y hy
    have hsq : (R ^ 2 + 1) ^ 2 ≤ ‖y‖ ^ 2 + 1 := by nlinarith
    have hlg : 2 * L ≤ Real.log (‖y‖ ^ 2 + 1) := by
      have h1 : Real.log ((R ^ 2 + 1) ^ 2) = 2 * L := by
        rw [Real.log_pow]; simp [L]
      rw [← h1]
      exact Real.log_le_log (by positivity) hsq
    have harg : 1 ≤ Real.log (‖y‖ ^ 2 + 1) / L - 1 := by
      rw [le_sub_iff_add_le, show (1 : ℝ) + 1 = 2 by norm_num, le_div_iff₀ hL_pos]
      linarith
    exact hζ1 _ harg
  have hηc : HasCompactSupport η := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Plane) A)
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    by_contra! hgt
    exact hy (hη_zero_out y hgt.le)
  have hgrad_bd (y : Plane) : ‖∇ η y‖ ^ 2 ≤ 4 * Mζ ^ 2 / (L ^ 2 * (‖y‖ ^ 2 + 1)) := by
    have hfd_sq : HasFDerivAt (fun z : Plane => ‖z‖ ^ 2 + 1)
        ((2 : ℝ) • InnerProductSpace.toDual ℝ Plane y) y := by
      have h1 : HasFDerivAt (fun z : Plane => inner ℝ z z)
          (InnerProductSpace.toDual ℝ Plane y + InnerProductSpace.toDual ℝ Plane y) y := by
        have h := (hasFDerivAt_id y).inner ℝ (hasFDerivAt_id y)
        have hf : fderiv ℝ (fun z : Plane => inner ℝ z z) y =
            InnerProductSpace.toDual ℝ Plane y + InnerProductSpace.toDual ℝ Plane y := by
          change fderiv ℝ (fun t : Plane => inner ℝ (id t) (id t)) y = _
          rw [h.fderiv]
          ext v; simp [InnerProductSpace.toDual_apply_apply, real_inner_comm v y]
        exact hf ▸ h.differentiableAt.hasFDerivAt
      have heq : (fun z : Plane => ‖z‖ ^ 2 + 1) = fun z => inner ℝ z z + 1 := by
        funext z; rw [real_inner_self_eq_norm_sq]
      rw [heq]
      have h2 := h1.add_const (1 : ℝ)
      have hLeq : InnerProductSpace.toDual ℝ Plane y + InnerProductSpace.toDual ℝ Plane y =
          (2 : ℝ) • InnerProductSpace.toDual ℝ Plane y := by
        ext v; simp; ring
      exact hLeq ▸ h2
    have hfd_arg : HasFDerivAt (fun z : Plane => Real.log (‖z‖ ^ 2 + 1) / L - 1)
        ((2 / (L * (‖y‖ ^ 2 + 1))) • InnerProductSpace.toDual ℝ Plane y) y := by
      have hlogd : HasDerivAt Real.log (‖y‖ ^ 2 + 1)⁻¹ (‖y‖ ^ 2 + 1) :=
        Real.hasDerivAt_log (by positivity)
      have h1 := hlogd.comp_hasFDerivAt y hfd_sq
      have h2 := (h1.const_smul L⁻¹).sub_const (1 : ℝ)
      have hfn : (fun z : Plane => (L⁻¹ • Real.log ∘ fun w : Plane => ‖w‖ ^ 2 + 1) z - 1) =
          fun z => Real.log (‖z‖ ^ 2 + 1) / L - 1 := by
        funext z; simp [div_eq_inv_mul]
      have hLeq : L⁻¹ • (‖y‖ ^ 2 + 1)⁻¹ • (2 : ℝ) • InnerProductSpace.toDual ℝ Plane y =
          (2 / (L * (‖y‖ ^ 2 + 1))) • InnerProductSpace.toDual ℝ Plane y := by
        ext v
        simp only [smul_apply, smul_eq_mul, InnerProductSpace.toDual_apply_apply]
        field_simp [hL_pos.ne', (show ‖y‖ ^ 2 + 1 ≠ 0 by positivity)]
      exact hLeq ▸ hfn ▸ h2
    have hfd_η : HasFDerivAt η
        ((deriv smoothStep (Real.log (‖y‖ ^ 2 + 1) / L - 1) * (2 / (L * (‖y‖ ^ 2 + 1)))) •
          InnerProductSpace.toDual ℝ Plane y) y := by
      have h1 := ((hζ_c1.differentiable one_ne_zero _).hasDerivAt).comp_hasFDerivAt y hfd_arg
      have hLeq : deriv smoothStep (Real.log (‖y‖ ^ 2 + 1) / L - 1) •
            (2 / (L * (‖y‖ ^ 2 + 1))) • InnerProductSpace.toDual ℝ Plane y =
          (deriv smoothStep (Real.log (‖y‖ ^ 2 + 1) / L - 1) * (2 / (L * (‖y‖ ^ 2 + 1)))) •
            InnerProductSpace.toDual ℝ Plane y := by
        rw [smul_smul]
      exact hLeq ▸ h1
    have hgn : ‖∇ η y‖ =
        |deriv smoothStep (Real.log (‖y‖ ^ 2 + 1) / L - 1)| * (2 * ‖y‖ / (L * (‖y‖ ^ 2 + 1))) := by
      unfold gradient
      rw [hfd_η.fderiv, map_smul, LinearIsometryEquiv.symm_apply_apply, norm_smul,
        Real.norm_eq_abs, abs_mul, abs_of_pos (show 0 < 2 / (L * (‖y‖ ^ 2 + 1)) by positivity)]
      ring
    have h1 : |deriv smoothStep (Real.log (‖y‖ ^ 2 + 1) / L - 1)| ≤ Mζ := hMζ _
    have h2 : 0 ≤ 2 * ‖y‖ / (L * (‖y‖ ^ 2 + 1)) := by positivity
    have h3 : ‖∇ η y‖ ^ 2 ≤ (Mζ * (2 * ‖y‖ / (L * (‖y‖ ^ 2 + 1)))) ^ 2 := by
      rw [hgn]
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h1 h2) 2
    have h4 : (Mζ * (2 * ‖y‖ / (L * (‖y‖ ^ 2 + 1)))) ^ 2 ≤
        4 * Mζ ^ 2 / (L ^ 2 * (‖y‖ ^ 2 + 1)) := by
      have hpos1 : 0 < ‖y‖ ^ 2 + 1 := by positivity
      have hposL : 0 < L ^ 2 := sq_pos_of_pos hL_pos
      have hsq_le : ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + 1 := by linarith
      have heq : (Mζ * (2 * ‖y‖ / (L * (‖y‖ ^ 2 + 1)))) ^ 2 =
          (4 * Mζ ^ 2 / (L ^ 2 * (‖y‖ ^ 2 + 1))) * (‖y‖ ^ 2 / (‖y‖ ^ 2 + 1)) := by
        field_simp [hL_pos.ne', hpos1.ne']; ring
      rw [heq]
      have hfrac : ‖y‖ ^ 2 / (‖y‖ ^ 2 + 1) ≤ 1 := (div_le_one hpos1).mpr hsq_le
      nlinarith [show 0 ≤ 4 * Mζ ^ 2 / (L ^ 2 * (‖y‖ ^ 2 + 1)) by positivity]
    exact h3.trans h4
  have hgrad_zero_out : ∀ y : Plane, y ∉ closedBall (0 : Plane) (A + 1) → ∇ η y = 0 := by
    intro y hy
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    have heq : η =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      have hopen : IsOpen {z : Plane | A < ‖z‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds (show A < ‖y‖ by linarith)] with z hz
      exact hη_zero_out z hz.le
    have hfd : fderiv ℝ η y = 0 := by
      rw [heq.fderiv_eq]; exact fderiv_const_apply (0 : ℝ)
    simp [gradient, hfd]
  let N : ℕ := Nat.ceil (L / Real.log 2) + 2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2N_ge : A + 1 ≤ (2 : ℝ) ^ N := by
    have h1 : L / Real.log 2 ≤ (Nat.ceil (L / Real.log 2) : ℝ) := Nat.le_ceil _
    have h2 : L ≤ (Nat.ceil (L / Real.log 2) : ℝ) * Real.log 2 := (div_le_iff₀ hlog2_pos).mp h1
    have h3 : A ≤ (2 : ℝ) ^ (Nat.ceil (L / Real.log 2)) := by
      have hexp := Real.exp_le_exp.mpr h2
      rw [Real.exp_log (by positivity), Real.exp_nat_mul, Real.exp_log (by norm_num)] at hexp
      exact hexp
    have h4 : (2 : ℝ) ^ N = 4 * (2 : ℝ) ^ (Nat.ceil (L / Real.log 2)) := by
      dsimp [N]; rw [pow_add]; ring
    linarith
  let box (r : ℝ) : Set Plane := {y | |y 0| ≤ r ∧ |y 1| ≤ r}
  have hbox_meas (r : ℝ) : MeasurableSet (box r) :=
    (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).abs continuous_const).inter
      (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).abs continuous_const)
      |>.measurableSet
  have hball_sub_box : closedBall (0 : Plane) (A + 1) ⊆ box ((2 : ℝ) ^ N) := by
    intro y hy
    rw [mem_closedBall, dist_zero_right] at hy
    have h0 : |y 0| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y 0
    have h1 : |y 1| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y 1
    exact ⟨h0.trans (hy.trans h2N_ge), h1.trans (hy.trans h2N_ge)⟩
  have hdyadic : ∀ n : ℕ,
      (∫ y in box ((2 : ℝ) ^ n), (1 : ℝ) / (‖y‖ ^ 2 + 1)) ≤ 4 + 16 * (n : ℝ) := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, Nat.cast_zero, mul_zero, add_zero]
      have hcomp : IsCompact (box 1) := by
        apply (isCompact_closedBall (0 : Plane) 2).of_isClosed_subset
        · exact (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).abs continuous_const).inter
            (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).abs continuous_const)
        · intro y hy
          rw [mem_closedBall, dist_zero_right]
          have hsq : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := by
            rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
          have h0 : (y 0) ^ 2 ≤ 1 := by nlinarith [abs_le.mp hy.1]
          have h1 : (y 1) ^ 2 ≤ 1 := by nlinarith [abs_le.mp hy.2]
          nlinarith [norm_nonneg y]
      have hint : IntegrableOn (fun y : Plane => (1 : ℝ) / (‖y‖ ^ 2 + 1)) (box 1) :=
        (continuous_const.div ((continuous_norm.pow 2).add continuous_const)
          fun y => (by positivity : ‖y‖ ^ 2 + 1 ≠ 0)).continuousOn.integrableOn_compact hcomp
      calc
        (∫ y in box 1, (1 : ℝ) / (‖y‖ ^ 2 + 1)) ≤ ∫ y in box 1, (1 : ℝ) := by
          apply setIntegral_mono_on hint (integrableOn_const (hs := hcomp.measure_lt_top.ne))
            (hbox_meas 1)
          intro y _
          exact (div_le_one (by positivity)).mpr (by linarith [sq_nonneg ‖y‖])
        _ = 4 := by
          rw [setIntegral_const, Measure.real_def, volume_plane_box 1 (by norm_num)]
          norm_num
    | succ k ih =>
      have hsub : box ((2 : ℝ) ^ k) ⊆ box ((2 : ℝ) ^ (k + 1)) := by
        intro y hy
        have hle : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) := by
          rw [pow_succ]; linarith [show (0 : ℝ) < (2 : ℝ) ^ k by positivity]
        exact ⟨hy.1.trans hle, hy.2.trans hle⟩
      have hcomp_next : IsCompact (box ((2 : ℝ) ^ (k + 1))) := by
        apply (isCompact_closedBall (0 : Plane) (2 * (2 : ℝ) ^ (k + 1))).of_isClosed_subset
        · exact (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).abs continuous_const).inter
            (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).abs continuous_const)
        · intro y hy
          rw [mem_closedBall, dist_zero_right]
          have hsq : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := by
            rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
          have h0 : (y 0) ^ 2 ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 := by nlinarith [abs_le.mp hy.1]
          have h1 : (y 1) ^ 2 ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 := by nlinarith [abs_le.mp hy.2]
          nlinarith [norm_nonneg y, show (0 : ℝ) ≤ (2 : ℝ) ^ (k + 1) by positivity]
      have hint_next : IntegrableOn (fun y : Plane => (1 : ℝ) / (‖y‖ ^ 2 + 1))
          (box ((2 : ℝ) ^ (k + 1))) :=
        (continuous_const.div ((continuous_norm.pow 2).add continuous_const)
          fun y => (by positivity : ‖y‖ ^ 2 + 1 ≠ 0)).continuousOn.integrableOn_compact hcomp_next
      have hsplit : (∫ y in box ((2 : ℝ) ^ (k + 1)), (1 : ℝ) / (‖y‖ ^ 2 + 1)) =
          (∫ y in box ((2 : ℝ) ^ k), (1 : ℝ) / (‖y‖ ^ 2 + 1)) +
          (∫ y in box ((2 : ℝ) ^ (k + 1)) \ box ((2 : ℝ) ^ k), (1 : ℝ) / (‖y‖ ^ 2 + 1)) := by
        rw [← setIntegral_union disjoint_sdiff_self_right
          ((hbox_meas _).diff (hbox_meas _)) (hint_next.mono_set hsub)
          (hint_next.mono_set Set.sdiff_subset), Set.union_sdiff_cancel hsub]
      have hshell : (∫ y in box ((2 : ℝ) ^ (k + 1)) \ box ((2 : ℝ) ^ k),
          (1 : ℝ) / (‖y‖ ^ 2 + 1)) ≤ 16 := by
        have hvol_le : (volume (box ((2 : ℝ) ^ (k + 1)) \ box ((2 : ℝ) ^ k))).toReal ≤
            4 * ((2 : ℝ) ^ (k + 1)) ^ 2 := by
          have hm := measure_mono (μ := volume)
            (show box ((2 : ℝ) ^ (k + 1)) \ box ((2 : ℝ) ^ k) ⊆ box ((2 : ℝ) ^ (k + 1)) from Set.sdiff_subset)
          have htr := ENNReal.toReal_mono hcomp_next.measure_lt_top.ne hm
          rwa [volume_plane_box _ (by positivity)] at htr
        have hpos_4k : 0 < ((2 : ℝ) ^ k) ^ 2 := by positivity
        calc
          (∫ y in box ((2 : ℝ) ^ (k + 1)) \ box ((2 : ℝ) ^ k), (1 : ℝ) / (‖y‖ ^ 2 + 1))
              ≤ ∫ y in box ((2 : ℝ) ^ (k + 1)) \ box ((2 : ℝ) ^ k),
                  (1 : ℝ) / ((2 : ℝ) ^ k) ^ 2 := by
                apply setIntegral_mono_on (hint_next.mono_set Set.sdiff_subset)
                  (integrableOn_const (hs := (measure_mono Set.sdiff_subset |>.trans_lt hcomp_next.measure_lt_top).ne))
                  ((hbox_meas _).diff (hbox_meas _))
                intro y hy
                have hout : ¬(|y 0| ≤ (2 : ℝ) ^ k ∧ |y 1| ≤ (2 : ℝ) ^ k) := hy.2
                have hsq : ((2 : ℝ) ^ k) ^ 2 ≤ ‖y‖ ^ 2 := by
                  have hns : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := by
                    rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
                  rw [not_and_or, not_le, not_le] at hout
                  rcases hout with h0 | h1
                  · have : ((2 : ℝ) ^ k) ^ 2 ≤ (y 0) ^ 2 := by
                      rw [← sq_abs (y 0)]; exact pow_le_pow_left₀ (by positivity) h0.le 2
                    linarith [sq_nonneg (y 1)]
                  · have : ((2 : ℝ) ^ k) ^ 2 ≤ (y 1) ^ 2 := by
                      rw [← sq_abs (y 1)]; exact pow_le_pow_left₀ (by positivity) h1.le 2
                    linarith [sq_nonneg (y 0)]
                exact div_le_div_of_nonneg_left (by norm_num) hpos_4k (by linarith)
          _ = (volume (box ((2 : ℝ) ^ (k + 1)) \ box ((2 : ℝ) ^ k))).toReal *
                ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) := by
              rw [setIntegral_const, Measure.real_def, smul_eq_mul]
          _ ≤ (4 * ((2 : ℝ) ^ (k + 1)) ^ 2) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) :=
              mul_le_mul_of_nonneg_right hvol_le (by positivity)
          _ = 16 := by
              rw [pow_succ]; field_simp [hpos_4k.ne']; ring
      rw [hsplit, Nat.cast_add, Nat.cast_one]
      linarith
  have hlog2_ge : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 2) ≤ 2 := by
      have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      have hlt : Real.exp 1 < 4 := by linarith
      nlinarith [Real.exp_pos (1 / 2)]
    exact (Real.le_log_iff_exp_le (by norm_num)).mpr h2
  have hN_le : (N : ℝ) ≤ 2 * L + 3 := by
    dsimp [N]
    push_cast
    have hceil : (Nat.ceil (L / Real.log 2) : ℝ) < L / Real.log 2 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hdiv : L / Real.log 2 ≤ 2 * L := by
      rw [div_le_iff₀ hlog2_pos]; nlinarith
    linarith
  have h4_16N : 4 + 16 * (N : ℝ) ≤ 84 * L := by nlinarith
  have hgrad_int : Integrable (fun y : Plane => ‖∇ η y‖ ^ 2) := by
    have hcont : Continuous (∇ η) :=
      (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hη_c1.continuous_fderiv one_ne_zero)
    have hcomp : HasCompactSupport (∇ η) := by
      apply hηc.mono'; intro y hy; apply support_fderiv_subset ℝ
      intro h0; exact hy (by simp [gradient, h0])
    exact (hcont.norm.pow 2).integrable_of_hasCompactSupport
      (by apply hcomp.mono'; intro y hy; apply subset_closure; intro h0
          exact hy (by change ‖∇ η y‖ ^ 2 = 0; rw [h0]; simp))
  have hboxN_comp : IsCompact (box ((2 : ℝ) ^ N)) := by
    apply (isCompact_closedBall (0 : Plane) (2 * (2 : ℝ) ^ N)).of_isClosed_subset
    · exact (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).abs continuous_const).inter
        (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).abs continuous_const)
    · intro y hy
      rw [mem_closedBall, dist_zero_right]
      have hsq : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
      have h0 : (y 0) ^ 2 ≤ ((2 : ℝ) ^ N) ^ 2 := by nlinarith [abs_le.mp hy.1]
      have h1 : (y 1) ^ 2 ≤ ((2 : ℝ) ^ N) ^ 2 := by nlinarith [abs_le.mp hy.2]
      nlinarith [norm_nonneg y, show (0 : ℝ) ≤ (2 : ℝ) ^ N by positivity]
  have hint_inv : IntegrableOn (fun y : Plane => (1 : ℝ) / (‖y‖ ^ 2 + 1)) (box ((2 : ℝ) ^ N)) :=
    (continuous_const.div ((continuous_norm.pow 2).add continuous_const)
      fun y => (by positivity : ‖y‖ ^ 2 + 1 ≠ 0)).continuousOn.integrableOn_compact hboxN_comp
  refine ⟨η, hη_c1, hηc, hη_one, ?_⟩
  calc
    (∫ y : Plane, ‖∇ η y‖ ^ 2) = ∫ y in box ((2 : ℝ) ^ N), ‖∇ η y‖ ^ 2 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hnout : y ∉ closedBall (0 : Plane) (A + 1) := fun h => hy (hball_sub_box h)
      rw [hgrad_zero_out y hnout]; simp
    _ ≤ ∫ y in box ((2 : ℝ) ^ N), (4 * Mζ ^ 2 / L ^ 2) * ((1 : ℝ) / (‖y‖ ^ 2 + 1)) := by
      apply setIntegral_mono_on hgrad_int.integrableOn (hint_inv.const_mul _) (hbox_meas _)
      intro y _
      have h := hgrad_bd y
      have heq : (4 * Mζ ^ 2 / L ^ 2) * ((1 : ℝ) / (‖y‖ ^ 2 + 1)) =
          4 * Mζ ^ 2 / (L ^ 2 * (‖y‖ ^ 2 + 1)) := by
        field_simp [hL_pos.ne', (show ‖y‖ ^ 2 + 1 ≠ 0 by positivity)]
      rwa [heq]
    _ = (4 * Mζ ^ 2 / L ^ 2) * ∫ y in box ((2 : ℝ) ^ N), (1 : ℝ) / (‖y‖ ^ 2 + 1) :=
      integral_const_mul _ _
    _ ≤ (4 * Mζ ^ 2 / L ^ 2) * (84 * L) :=
      mul_le_mul_of_nonneg_left ((hdyadic N).trans h4_16N) (by positivity)
    _ = 4 * Mζ ^ 2 * 84 / L := by
      field_simp [hL_pos.ne']

private theorem collinear_hessian_of_stable2 {v : Plane → ℝ}
    (hv : DeGiorgi.IsBoundedSolution v)
    {D : ℝ} (_hD : 0 ≤ D) (hgradB : ∀ y, ‖∇ v y‖ ≤ D)
    (hstab : ∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      0 ≤ ∫ y : Plane, (‖∇ ψ y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (ψ y) ^ 2)) :
    ∀ y : Plane,
      part2 v 0 y * part22 v 1 0 y - part2 v 1 y * part22 v 0 0 y = 0 ∧
      part2 v 0 y * part22 v 1 1 y - part2 v 1 y * part22 v 0 1 y = 0 := by
  obtain ⟨C_log, hC_log0, hcut⟩ := log_cutoff2_energy
  let F : Plane → ℝ := fun y =>
    ((part2 v 0 y * part22 v 1 0 y - part2 v 1 y * part22 v 0 0 y) ^ 2 +
     (part2 v 0 y * part22 v 1 1 y - part2 v 1 y * part22 v 0 1 y) ^ 2) /
    ((part2 v 0 y) ^ 2 + (part2 v 1 y) ^ 2 + 1 ^ 2)
  have hF_nn : ∀ y, 0 ≤ F y := fun y => by dsimp [F]; positivity
  have hF_cont : Continuous F := by
    have hv0_c1 : ContDiff ℝ 1 (part2 v 0) :=
      (hv.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hv1_c1 : ContDiff ℝ 1 (part2 v 1) :=
      (hv.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hp22c (i j : Fin 2) : Continuous (part22 v i j) :=
      (((hv.regular.fderiv_right (by norm_num)).clm_apply contDiff_const).continuous_fderiv
        one_ne_zero).clm_apply continuous_const
    exact ((((hv0_c1.continuous.mul (hp22c 1 0)).sub (hv1_c1.continuous.mul (hp22c 0 0))).pow 2).add
      (((hv0_c1.continuous.mul (hp22c 1 1)).sub (hv1_c1.continuous.mul (hp22c 0 1))).pow 2)).div
      (((hv0_c1.continuous.pow 2).add (hv1_c1.continuous.pow 2)).add continuous_const)
      fun y => by positivity
  have hball_zero : ∀ r : ℝ, 2 ≤ r → (∫ y in Metric.ball (0 : Plane) r, F y) = 0 := by
    intro r hr
    apply le_antisymm _ (setIntegral_nonneg measurableSet_ball fun y _ => hF_nn y)
    have hbound : ∀ R : ℝ, r ≤ R →
        (∫ y in Metric.ball (0 : Plane) r, F y) ≤ D ^ 2 * C_log / Real.log (R ^ 2 + 1) := by
      intro R hR
      obtain ⟨η, hη_c1, hηc, hη1, hηE⟩ := hcut R (hr.trans hR)
      have hsz := sternberg_zumbrun2 hv hstab hη_c1 hηc (δ := 1) (by norm_num)
      have hcont_g : Continuous (∇ η) :=
        (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hη_c1.continuous_fderiv one_ne_zero)
      have hcomp_g : HasCompactSupport (∇ η) := by
        apply hηc.mono'; intro y hy; apply support_fderiv_subset ℝ
        intro h0; exact hy (by simp [gradient, h0])
      have hint_g2 : Integrable (fun y : Plane => ‖∇ η y‖ ^ 2) :=
        (hcont_g.norm.pow 2).integrable_of_hasCompactSupport
          (by apply hcomp_g.mono'; intro y hy; apply subset_closure; intro h0
              exact hy (by change ‖∇ η y‖ ^ 2 = 0; rw [h0]; simp))
      have hint_vg : Integrable (fun y : Plane => ‖∇ v y‖ ^ 2 * ‖∇ η y‖ ^ 2) :=
        ((((InnerProductSpace.toDual ℝ Plane).symm.continuous.comp
            ((hv.regular.of_le (by norm_num)).continuous_fderiv one_ne_zero)).norm.pow 2).mul
          (hcont_g.norm.pow 2)).integrable_of_hasCompactSupport
          (by apply hcomp_g.mono'; intro y hy; apply subset_closure; intro h0
              exact hy (by change ‖∇ v y‖ ^ 2 * ‖∇ η y‖ ^ 2 = 0; rw [h0]; simp))
      have hint_ηF : Integrable (fun y : Plane => (η y) ^ 2 * F y) :=
        ((hη_c1.continuous.pow 2).mul hF_cont).integrable_of_hasCompactSupport
          (by apply hηc.mono'; intro y hy; apply subset_closure; intro h0
              exact hy (by change (η y) ^ 2 * F y = 0; rw [h0]; simp))
      have hball_int : IntegrableOn F (Metric.ball (0 : Plane) r) :=
        (hF_cont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set
          ball_subset_closedBall
      calc
        (∫ y in Metric.ball (0 : Plane) r, F y)
            = ∫ y in Metric.ball (0 : Plane) r, (η y) ^ 2 * F y := by
              apply setIntegral_congr_fun measurableSet_ball
              intro y hy
              have hmem : y ∈ closedBall (0 : Plane) R := by
                rw [Metric.mem_ball, dist_zero_right] at hy
                rw [mem_closedBall, dist_zero_right]; linarith
              dsimp only
              rw [hη1 y hmem]; ring
        _ ≤ ∫ y : Plane, (η y) ^ 2 * F y :=
            setIntegral_le_integral hint_ηF (Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (hF_nn y))
        _ ≤ ∫ y : Plane, ‖∇ v y‖ ^ 2 * ‖∇ η y‖ ^ 2 := by
            have heq : (fun y : Plane => (η y) ^ 2 * F y) = fun y => (η y) ^ 2 *
                ((part2 v 0 y * part22 v 1 0 y - part2 v 1 y * part22 v 0 0 y) ^ 2 +
                 (part2 v 0 y * part22 v 1 1 y - part2 v 1 y * part22 v 0 1 y) ^ 2) /
                ((part2 v 0 y) ^ 2 + (part2 v 1 y) ^ 2 + 1 ^ 2) := by
              funext y; dsimp [F]; ring
            rwa [heq]
        _ ≤ ∫ y : Plane, D ^ 2 * ‖∇ η y‖ ^ 2 := by
            apply integral_mono hint_vg (hint_g2.const_mul (D ^ 2))
            intro y
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (norm_nonneg _) (hgradB y) 2) (sq_nonneg _)
        _ = D ^ 2 * ∫ y : Plane, ‖∇ η y‖ ^ 2 := integral_const_mul _ _
        _ ≤ D ^ 2 * (C_log / Real.log (R ^ 2 + 1)) :=
            mul_le_mul_of_nonneg_left hηE (sq_nonneg D)
        _ = D ^ 2 * C_log / Real.log (R ^ 2 + 1) := by ring
    have htend : Tendsto (fun n : ℕ => D ^ 2 * C_log / Real.log (((r + (n : ℝ)) ^ 2 + 1)))
        atTop (𝓝 0) := by
      have harg : Tendsto (fun n : ℕ => (r + (n : ℝ)) ^ 2 + 1) atTop atTop := by
        have h1 : Tendsto (fun n : ℕ => r + (n : ℝ)) atTop atTop :=
          tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
        have h2 : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
        exact (h2.comp h1).atTop_add tendsto_const_nhds
      have hlg : Tendsto (fun n : ℕ => Real.log ((r + (n : ℝ)) ^ 2 + 1)) atTop atTop :=
        Real.tendsto_log_atTop.comp harg
      exact tendsto_const_nhds.div_atTop hlg
    refine ge_of_tendsto htend (Eventually.of_forall fun n => ?_)
    exact hbound (r + (n : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  intro y
  have hFy0 : F y = 0 := by
    by_contra hne
    have hpos : 0 < F y := lt_of_le_of_ne (hF_nn y) (Ne.symm hne)
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hF_cont.continuousAt (F y / 2) (by linarith)
    let r := max 2 (‖y‖ + δ)
    have hr2 : 2 ≤ r := le_max_left _ _
    have hsub : Metric.ball y δ ⊆ Metric.ball (0 : Plane) r := by
      intro z hz
      rw [Metric.mem_ball, dist_zero_right]
      have h1 : dist z y < δ := Metric.mem_ball.mp hz
      have h2 : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := norm_le_norm_sub_add z y
      rw [← dist_eq_norm] at h2
      have h3 : ‖y‖ + δ ≤ r := le_max_right _ _
      linarith
    have hint_r : IntegrableOn F (Metric.ball (0 : Plane) r) :=
      (hF_cont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set
        ball_subset_closedBall
    have hpos_int : 0 < ∫ z in Metric.ball y δ, F z := by
      have hvol : 0 < (volume (Metric.ball y δ)).toReal :=
        ENNReal.toReal_pos (Metric.measure_ball_pos volume y hδ).ne'
          (measure_ball_lt_top).ne
      have hge : (F y / 2) * (volume (Metric.ball y δ)).toReal ≤ ∫ z in Metric.ball y δ, F z := by
        calc
          (F y / 2) * (volume (Metric.ball y δ)).toReal =
              ∫ _ in Metric.ball y δ, (F y / 2) := by
            rw [setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
          _ ≤ ∫ z in Metric.ball y δ, F z := by
            apply setIntegral_mono_on (integrableOn_const (hs := measure_ball_lt_top.ne))
              (hint_r.mono_set hsub) measurableSet_ball
            intro z hz
            have := hball hz
            rw [Real.dist_eq, abs_lt] at this
            linarith
      nlinarith
    have hle := setIntegral_mono_set hint_r (Eventually.of_forall hF_nn) (Eventually.of_forall hsub)
    rw [hball_zero r hr2] at hle
    change (∫ z in Metric.ball y δ, F z) ≤ 0 at hle
    linarith
  have hden : 0 < (part2 v 0 y) ^ 2 + (part2 v 1 y) ^ 2 + 1 ^ 2 := by positivity
  have hnum0 : (part2 v 0 y * part22 v 1 0 y - part2 v 1 y * part22 v 0 0 y) ^ 2 +
      (part2 v 0 y * part22 v 1 1 y - part2 v 1 y * part22 v 0 1 y) ^ 2 = 0 := by
    dsimp [F] at hFy0
    exact (div_eq_zero_iff.mp hFy0).resolve_right hden.ne'
  have h1 : (part2 v 0 y * part22 v 1 0 y - part2 v 1 y * part22 v 0 0 y) ^ 2 = 0 := by
    nlinarith [sq_nonneg (part2 v 0 y * part22 v 1 0 y - part2 v 1 y * part22 v 0 0 y),
      sq_nonneg (part2 v 0 y * part22 v 1 1 y - part2 v 1 y * part22 v 0 1 y)]
  have h2 : (part2 v 0 y * part22 v 1 1 y - part2 v 1 y * part22 v 0 1 y) ^ 2 = 0 := by
    linarith
  exact ⟨sq_eq_zero_iff.mp h1, sq_eq_zero_iff.mp h2⟩

/-
## Section 4b: 1D rigidity and O(R) energy growth for bounded stable 2D solutions
-/

private noncomputable def bump2 : ContDiffBump (0 : Plane) :=
  ⟨1, 2, by norm_num, by norm_num⟩

private theorem const_zero_unstable2 :
    ¬ (∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      0 ≤ ∫ y : Plane, (‖∇ ψ y‖ ^ 2 + (3 * (0 : ℝ) ^ 2 - 1) * (ψ y) ^ 2)) := by
  intro hstab
  obtain ⟨M, hM⟩ := (bump2.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    ((bump2.contDiff (n := 1)).continuous_fderiv one_ne_zero)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hvol1 : 0 < (volume (Metric.ball (0 : Plane) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : Plane) (by norm_num)).ne'
      measure_ball_lt_top.ne
  let R : ℝ := max 1 (3 * M + 1)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := by linarith
  let ψ : Plane → ℝ := fun y => bump2 (R⁻¹ • y)
  have hψ_c1 : ContDiff ℝ 1 ψ := bump2.contDiff.comp (contDiff_id.const_smul R⁻¹)
  have hψc : HasCompactSupport ψ := bump2.hasCompactSupport.comp_smul (inv_ne_zero hR0.ne')
  have hst := hstab ψ hψ_c1 hψc
  have hcont_g : Continuous (∇ ψ) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hψ_c1.continuous_fderiv one_ne_zero)
  have hcomp_g : HasCompactSupport (∇ ψ) := by
    apply hψc.mono'; intro y hy; apply support_fderiv_subset ℝ
    intro h0; exact hy (by simp [gradient, h0])
  have hint_g : Integrable (fun y : Plane => ‖∇ ψ y‖ ^ 2) :=
    (hcont_g.norm.pow 2).integrable_of_hasCompactSupport
      (by apply hcomp_g.mono'; intro y hy; apply subset_closure; intro h0
          exact hy (by change ‖∇ ψ y‖ ^ 2 = 0; rw [h0]; simp))
  have hint_p : Integrable (fun y : Plane => (ψ y) ^ 2) :=
    (hψ_c1.continuous.pow 2).integrable_of_hasCompactSupport
      (by apply hψc.mono'; intro y hy; apply subset_closure; intro h0
          exact hy (by change (ψ y) ^ 2 = 0; rw [h0]; simp))
  have hst' : (∫ y : Plane, (ψ y) ^ 2) ≤ ∫ y : Plane, ‖∇ ψ y‖ ^ 2 := by
    have heq : (fun y : Plane => ‖∇ ψ y‖ ^ 2 + (3 * (0 : ℝ) ^ 2 - 1) * (ψ y) ^ 2) =
        fun y => ‖∇ ψ y‖ ^ 2 - (ψ y) ^ 2 := by funext y; ring
    rw [heq, integral_sub hint_g hint_p] at hst
    linarith
  have hvol_ball (r : ℝ) (hr : 0 ≤ r) :
      (volume (Metric.ball (0 : Plane) r)).toReal = r ^ 2 * (volume (Metric.ball (0 : Plane) 1)).toReal := by
    rw [MeasureTheory.Measure.addHaar_ball volume (0 : Plane) hr, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg r)]
  have hlower : R ^ 2 * (volume (Metric.ball (0 : Plane) 1)).toReal ≤ ∫ y : Plane, (ψ y) ^ 2 := by
    calc
      R ^ 2 * (volume (Metric.ball (0 : Plane) 1)).toReal
          = ∫ _ in Metric.ball (0 : Plane) R, (1 : ℝ) := by
            rw [setIntegral_const, Measure.real_def, hvol_ball R hR0.le, smul_eq_mul, mul_one]
      _ ≤ ∫ y in Metric.ball (0 : Plane) R, (ψ y) ^ 2 := by
            apply setIntegral_mono_on (integrableOn_const (hs := measure_ball_lt_top.ne))
              hint_p.integrableOn measurableSet_ball
            intro y hy
            rw [Metric.mem_ball, dist_zero_right] at hy
            have hmem : R⁻¹ • y ∈ closedBall (0 : Plane) bump2.rIn := by
              rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
                abs_of_pos hR0, inv_mul_eq_div, div_le_iff₀ hR0, show bump2.rIn = 1 from rfl,
                one_mul]
              exact hy.le
            rw [show ψ y = 1 from bump2.one_of_mem_closedBall hmem]; norm_num
      _ ≤ ∫ y : Plane, (ψ y) ^ 2 :=
            setIntegral_le_integral hint_p (Eventually.of_forall fun _ => sq_nonneg _)
  have hupper : (∫ y : Plane, ‖∇ ψ y‖ ^ 2) ≤ 9 * M ^ 2 * (volume (Metric.ball (0 : Plane) 1)).toReal := by
    have hgrad_bd (y : Plane) : ‖∇ ψ y‖ ≤ M / R := by
      have hfd : fderiv ℝ ψ y = (fderiv ℝ (fun z : Plane => bump2 z) (R⁻¹ • y)).comp
          (R⁻¹ • ContinuousLinearMap.id ℝ Plane) := by
        have hd := ((bump2.contDiff (n := 1)).differentiable one_ne_zero (R⁻¹ • y)).hasFDerivAt
        exact (hd.comp y (R⁻¹ • ContinuousLinearMap.id ℝ Plane).hasFDerivAt).fderiv
      have hn : ‖∇ ψ y‖ = ‖fderiv ℝ ψ y‖ := (InnerProductSpace.toDual ℝ Plane).symm.norm_map _
      rw [hn, hfd]
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR0, ContinuousLinearMap.norm_id,
        mul_one, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hM _) (inv_nonneg.mpr hR0.le)
    have hzero_out : ∀ y ∉ Metric.ball (0 : Plane) (3 * R), ∇ ψ y = 0 := by
      intro y hy
      rw [Metric.mem_ball, dist_zero_right, not_lt] at hy
      have heq : ψ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        have hopen : IsOpen {z : Plane | 2 * R < ‖z‖} := isOpen_lt continuous_const continuous_norm
        filter_upwards [hopen.mem_nhds (show 2 * R < ‖y‖ by linarith)] with z hz
        apply bump2.zero_of_le_dist
        change 2 ≤ dist (R⁻¹ • z) 0
        rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR0,
          inv_mul_eq_div, le_div_iff₀ hR0]
        exact hz.le
      have hfd : fderiv ℝ ψ y = 0 := by rw [heq.fderiv_eq]; exact fderiv_const_apply (0 : ℝ)
      simp [gradient, hfd]
    calc
      (∫ y : Plane, ‖∇ ψ y‖ ^ 2) = ∫ y in Metric.ball (0 : Plane) (3 * R), ‖∇ ψ y‖ ^ 2 := by
        symm; apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy; rw [hzero_out y hy]; simp
      _ ≤ ∫ _ in Metric.ball (0 : Plane) (3 * R), (M / R) ^ 2 := by
        apply setIntegral_mono_on hint_g.integrableOn
          (integrableOn_const (hs := measure_ball_lt_top.ne)) measurableSet_ball
        intro y _
        exact pow_le_pow_left₀ (norm_nonneg _) (hgrad_bd y) 2
      _ = 9 * M ^ 2 * (volume (Metric.ball (0 : Plane) 1)).toReal := by
        rw [setIntegral_const, Measure.real_def, hvol_ball (3 * R) (by positivity), smul_eq_mul]
        field_simp [hR0.ne']; ring
  have hR_big : 3 * M < R := by
    have : 3 * M + 1 ≤ R := le_max_right _ _
    linarith
  have hsq_lt : 9 * M ^ 2 < R ^ 2 := by nlinarith
  have hcontra : 9 * M ^ 2 * (volume (Metric.ball (0 : Plane) 1)).toReal <
      R ^ 2 * (volume (Metric.ball (0 : Plane) 1)).toReal :=
    mul_lt_mul_of_pos_right hsq_lt hvol1
  linarith

private noncomputable def rot2 (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) : Plane ≃ₗᵢ[ℝ] Plane where
  toFun y := (a * y 0 - b * y 1) • e2 0 + (b * y 0 + a * y 1) • e2 1
  invFun y := (a * y 0 + b * y 1) • e2 0 + (-b * y 0 + a * y 1) • e2 1
  map_add' x y := by ext i; fin_cases i <;> simp [e2] <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp [e2] <;> ring
  left_inv y := by
    ext i; fin_cases i <;> simp [e2]
    · calc
        a * (a * y 0 - b * y 1) + b * (b * y 0 + a * y 1) = (a ^ 2 + b ^ 2) * y 0 := by ring
        _ = y 0 := by rw [hab, one_mul]
    · calc
        -(b * (a * y 0 - b * y 1)) + a * (b * y 0 + a * y 1) = (a ^ 2 + b ^ 2) * y 1 := by ring
        _ = y 1 := by rw [hab, one_mul]
  right_inv y := by
    ext i; fin_cases i <;> simp [e2]
    · calc
        a * (a * y 0 + b * y 1) - b * (-(b * y 0) + a * y 1) = (a ^ 2 + b ^ 2) * y 0 := by ring
        _ = y 0 := by rw [hab, one_mul]
    · calc
        b * (a * y 0 + b * y 1) + a * (-(b * y 0) + a * y 1) = (a ^ 2 + b ^ 2) * y 1 := by ring
        _ = y 1 := by rw [hab, one_mul]
  norm_map' y := by
    change ‖(a * y 0 - b * y 1) • e2 0 + (b * y 0 + a * y 1) • e2 1‖ = ‖y‖
    have hsq : ‖(a * y 0 - b * y 1) • e2 0 + (b * y 0 + a * y 1) • e2 1‖ ^ 2 = ‖y‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
      have h0 : ((a * y 0 - b * y 1) • e2 0 + (b * y 0 + a * y 1) • e2 1) 0 =
          a * y 0 - b * y 1 := by simp [e2]
      have h1 : ((a * y 0 - b * y 1) • e2 0 + (b * y 0 + a * y 1) • e2 1) 1 =
          b * y 0 + a * y 1 := by simp [e2]
      rw [h0, h1]
      calc
        (a * y 0 - b * y 1) ^ 2 + (b * y 0 + a * y 1) ^ 2 =
            (a ^ 2 + b ^ 2) * (y 0 ^ 2 + y 1 ^ 2) := by ring
        _ = y 0 ^ 2 + y 1 ^ 2 := by rw [hab, one_mul]
    nlinarith [norm_nonneg ((a * y 0 - b * y 1) • e2 0 + (b * y 0 + a * y 1) • e2 1), norm_nonneg y]

private theorem isometry2_preserves_solution {v : Plane → ℝ}
    (hv : DeGiorgi.IsBoundedSolution v)
    (h1 : ∀ y, |v y| ≤ 1)
    {D : ℝ} (hgradB : ∀ y, ‖∇ v y‖ ≤ D)
    (hstab : ∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      0 ≤ ∫ y : Plane, (‖∇ ψ y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (ψ y) ^ 2))
    (Q : Plane ≃ₗᵢ[ℝ] Plane) :
    let v' := fun y : Plane => v (Q y)
    DeGiorgi.IsBoundedSolution v' ∧
    (∀ y, |v' y| ≤ 1) ∧
    (∀ y, ‖∇ v' y‖ = ‖∇ v (Q y)‖) ∧
    (∀ y, ‖∇ v' y‖ ≤ D) ∧
    (∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      0 ≤ ∫ y : Plane, (‖∇ ψ y‖ ^ 2 + (3 * (v' y) ^ 2 - 1) * (ψ y) ^ 2)) ∧
    (∀ R : ℝ, (∫ y in Metric.ball (0 : Plane) R, (1 / 2 * ‖∇ v y‖ ^ 2 + doubleWell (v y))) =
      ∫ y in Metric.ball (0 : Plane) R, (1 / 2 * ‖∇ v' y‖ ^ 2 + doubleWell (v' y))) := by
  intro v'
  have hv'_c2 : ContDiff ℝ 2 v' := hv.regular.comp Q.toContinuousLinearEquiv.contDiff
  have hv'_fd (y : Plane) : fderiv ℝ v' y = (fderiv ℝ v (Q y)).comp Q.toContinuousLinearMap := by
    exact ((hv.regular.differentiable (by norm_num) (Q y)).hasFDerivAt.comp y
      Q.toContinuousLinearMap.hasFDerivAt).fderiv
  have hv'_grad_norm (y : Plane) : ‖∇ v' y‖ = ‖∇ v (Q y)‖ := by
    have h1' : ‖∇ v' y‖ = ‖fderiv ℝ v' y‖ := (InnerProductSpace.toDual ℝ Plane).symm.norm_map _
    have h2' : ‖∇ v (Q y)‖ = ‖fderiv ℝ v (Q y)‖ := (InnerProductSpace.toDual ℝ Plane).symm.norm_map _
    rw [h1', h2', hv'_fd y]
    apply le_antisymm
    · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
        have hQ : ‖Q.toContinuousLinearMap‖ ≤ 1 :=
          ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by simp [Q.norm_map]
        nlinarith [norm_nonneg (fderiv ℝ v (Q y))])
    · have hinv : fderiv ℝ v (Q y) = (fderiv ℝ v' y).comp Q.symm.toContinuousLinearMap := by
        rw [hv'_fd y]; ext w; simp
      calc
        ‖fderiv ℝ v (Q y)‖ = ‖(fderiv ℝ v' y).comp Q.symm.toContinuousLinearMap‖ := by rw [hinv]
        _ ≤ ‖fderiv ℝ v' y‖ * ‖Q.symm.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖fderiv ℝ v' y‖ * 1 := by
            have hQ : ‖Q.symm.toContinuousLinearMap‖ ≤ 1 :=
              ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by simp [Q.symm.norm_map]
            exact mul_le_mul_of_nonneg_left hQ (norm_nonneg _)
        _ = ‖fderiv ℝ v' y‖ := mul_one _
        _ = ‖(fderiv ℝ v (Q y)).comp Q.toContinuousLinearMap‖ := by rw [hv'_fd y]
  have hv'_lap (y : Plane) : (Δ v') y = (Δ v) (Q y) := by
    let ob := EuclideanSpace.basisFun (Fin 2) ℝ
    let obQ := ob.map Q
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis v' ob,
      laplacian_eq_iteratedFDeriv_orthonormalBasis v obQ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, obQ, OrthonormalBasis.map_apply]
    have h2 : fderiv ℝ (fderiv ℝ v') y =
        ((ContinuousLinearMap.compL ℝ Plane Plane ℝ).flip Q.toContinuousLinearMap).comp
          ((fderiv ℝ (fderiv ℝ v) (Q y)).comp Q.toContinuousLinearMap) := by
      have hF : ContDiff ℝ 1 (fderiv ℝ v) := hv.regular.fderiv_right (by norm_num)
      have hcomp_fd : HasFDerivAt (fun z => fderiv ℝ v (Q z))
          ((fderiv ℝ (fderiv ℝ v) (Q y)).comp Q.toContinuousLinearMap) y :=
        (hF.differentiable one_ne_zero (Q y)).hasFDerivAt.comp y Q.toContinuousLinearMap.hasFDerivAt
      have hL := (((ContinuousLinearMap.compL ℝ Plane Plane ℝ).flip
        Q.toContinuousLinearMap).hasFDerivAt.comp y hcomp_fd).fderiv
      have heq : (((ContinuousLinearMap.compL ℝ Plane Plane ℝ).flip Q.toContinuousLinearMap) ∘
          fun z => fderiv ℝ v (Q z)) = fderiv ℝ v' := by
        funext z; exact (hv'_fd z).symm
      rwa [heq] at hL
    rw [h2]
    rfl
  have hv'_sol : DeGiorgi.IsBoundedSolution v' :=
    ⟨hv'_c2, ⟨1, fun y => h1 (Q y)⟩, fun y => by rw [hv'_lap y]; exact hv.solution (Q y)⟩
  have hv'_stab : ∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      0 ≤ ∫ y : Plane, (‖∇ ψ y‖ ^ 2 + (3 * (v' y) ^ 2 - 1) * (ψ y) ^ 2) := by
    intro ψ hψ hψc
    let ψ' : Plane → ℝ := fun z => ψ (Q.symm z)
    have hψ'_c1 : ContDiff ℝ 1 ψ' := hψ.comp Q.symm.toContinuousLinearEquiv.contDiff
    have hψ'c : HasCompactSupport ψ' := hψc.comp_homeomorph Q.symm.toHomeomorph
    have hst := hstab ψ' hψ'_c1 hψ'c
    have hgn' (z : Plane) : ‖∇ ψ' z‖ = ‖∇ ψ (Q.symm z)‖ := by
      have hfd : fderiv ℝ ψ' z = (fderiv ℝ ψ (Q.symm z)).comp Q.symm.toContinuousLinearMap :=
        ((hψ.differentiable one_ne_zero (Q.symm z)).hasFDerivAt.comp z
          Q.symm.toContinuousLinearMap.hasFDerivAt).fderiv
      have h1' : ‖∇ ψ' z‖ = ‖fderiv ℝ ψ' z‖ := (InnerProductSpace.toDual ℝ Plane).symm.norm_map _
      have h2' : ‖∇ ψ (Q.symm z)‖ = ‖fderiv ℝ ψ (Q.symm z)‖ :=
        (InnerProductSpace.toDual ℝ Plane).symm.norm_map _
      rw [h1', h2', hfd]
      apply le_antisymm
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
          have hQ : ‖Q.symm.toContinuousLinearMap‖ ≤ 1 :=
            ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by simp [Q.symm.norm_map]
          nlinarith [norm_nonneg (fderiv ℝ ψ (Q.symm z))])
      · have hinv : fderiv ℝ ψ (Q.symm z) = (fderiv ℝ ψ' z).comp Q.toContinuousLinearMap := by
          rw [hfd]; ext w; simp
        calc
          ‖fderiv ℝ ψ (Q.symm z)‖ = ‖(fderiv ℝ ψ' z).comp Q.toContinuousLinearMap‖ := by rw [hinv]
          _ ≤ ‖fderiv ℝ ψ' z‖ * ‖Q.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖fderiv ℝ ψ' z‖ * 1 := by
              have hQ : ‖Q.toContinuousLinearMap‖ ≤ 1 :=
                ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by simp [Q.norm_map]
              exact mul_le_mul_of_nonneg_left hQ (norm_nonneg _)
          _ = ‖fderiv ℝ ψ' z‖ := mul_one _
          _ = ‖(fderiv ℝ ψ (Q.symm z)).comp Q.symm.toContinuousLinearMap‖ := by rw [hfd]
    have hmp := Q.measurePreserving
    have hcomp := hmp.integral_comp' (f := Q.toHomeomorph.toMeasurableEquiv)
      (fun z : Plane => ‖∇ ψ' z‖ ^ 2 + (3 * (v z) ^ 2 - 1) * (ψ' z) ^ 2)
    have hpt (y : Plane) :
        ‖∇ ψ' (Q y)‖ ^ 2 + (3 * (v (Q y)) ^ 2 - 1) * (ψ' (Q y)) ^ 2 =
        ‖∇ ψ y‖ ^ 2 + (3 * (v' y) ^ 2 - 1) * (ψ y) ^ 2 := by
      rw [hgn' (Q y)]; simp [ψ', v']
    change (∫ y : Plane, ‖∇ ψ' (Q y)‖ ^ 2 + (3 * (v (Q y)) ^ 2 - 1) * (ψ' (Q y)) ^ 2) = _ at hcomp
    simp_rw [hpt] at hcomp
    linarith
  have hv'_energy (R : ℝ) :
      (∫ y in Metric.ball (0 : Plane) R, (1 / 2 * ‖∇ v y‖ ^ 2 + doubleWell (v y))) =
      ∫ y in Metric.ball (0 : Plane) R, (1 / 2 * ‖∇ v' y‖ ^ 2 + doubleWell (v' y)) := by
    let e := Q.toHomeomorph.toMeasurableEquiv
    have hmp : MeasurePreserving e volume volume := Q.measurePreserving
    have hpre : e ⁻¹' Metric.ball (0 : Plane) R = Metric.ball (0 : Plane) R := by
      ext y; change dist (Q y) 0 < R ↔ dist y 0 < R
      rw [dist_zero_right, dist_zero_right, Q.norm_map]
    rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
    symm
    have hcomp := hmp.integral_comp' (f := e)
      ((Metric.ball (0 : Plane) R).indicator fun z => 1 / 2 * ‖∇ v z‖ ^ 2 + doubleWell (v z))
    rw [← hcomp]
    congr 1; funext y
    by_cases hy : y ∈ Metric.ball (0 : Plane) R
    · have hQy : e y ∈ Metric.ball (0 : Plane) R := by rwa [← Set.mem_preimage, hpre]
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hQy]
      change 1 / 2 * ‖∇ v' y‖ ^ 2 + doubleWell (v' y) = 1 / 2 * ‖∇ v (Q y)‖ ^ 2 + doubleWell (v (Q y))
      rw [hv'_grad_norm y]
    · have hQy : e y ∉ Metric.ball (0 : Plane) R := by rwa [← Set.mem_preimage, hpre]
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hQy]
  exact ⟨hv'_sol, fun y => h1 (Q y), hv'_grad_norm, fun y => (hv'_grad_norm y).le.trans (hgradB (Q y)),
    hv'_stab, hv'_energy⟩

private theorem eq_of_hasDerivAt_zero_on_uIcc {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ r ∈ Set.uIcc a b, HasDerivAt f 0 r) : f b = f a := by
  by_contra hne
  have hab : a ≠ b := fun h => hne (by rw [h])
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f (fun _ => (0 : ℝ)) hlt
      (fun r hr => (hf r (Set.uIcc_of_le hlt.le ▸ hr)).continuousAt.continuousWithinAt)
      (fun r hr => hf r (Set.uIcc_of_le hlt.le ▸ ⟨hr.1.le, hr.2.le⟩))
    have hnum := (div_eq_zero_iff.mp hslope.symm).resolve_right (sub_ne_zero.mpr hlt.ne')
    exact hne (sub_eq_zero.mp hnum)
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f (fun _ => (0 : ℝ)) hlt
      (fun r hr => (hf r (Set.uIcc_of_ge hlt.le ▸ hr)).continuousAt.continuousWithinAt)
      (fun r hr => hf r (Set.uIcc_of_ge hlt.le ▸ ⟨hr.1.le, hr.2.le⟩))
    have hnum := (div_eq_zero_iff.mp hslope.symm).resolve_right (sub_ne_zero.mpr hlt.ne')
    exact hne (sub_eq_zero.mp hnum).symm

private theorem strip_of_pos_part0 {v : Plane → ℝ}
    (hv : DeGiorgi.IsBoundedSolution v)
    (hcol : ∀ y : Plane,
      part2 v 0 y * part22 v 1 0 y - part2 v 1 y * part22 v 0 0 y = 0 ∧
      part2 v 0 y * part22 v 1 1 y - part2 v 1 y * part22 v 0 1 y = 0)
    (s₀ t₀ : ℝ)
    (hv1_0 : part2 v 1 (s₀ • e2 0 + t₀ • e2 1) = 0)
    (s : ℝ) (hs : ∀ r ∈ Set.uIcc s₀ s, 0 < part2 v 0 (r • e2 0 + t₀ • e2 1)) :
    ∀ t : ℝ,
      v (s • e2 0 + t • e2 1) = v (s • e2 0 + t₀ • e2 1) ∧
      part2 v 0 (s • e2 0 + t • e2 1) = part2 v 0 (s • e2 0 + t₀ • e2 1) ∧
      part2 v 1 (s • e2 0 + t • e2 1) = 0 := by
  have hpc0 : ContDiff ℝ 1 (part2 v 0) :=
    (hv.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hsymm (y : Plane) : part22 v 0 1 y = part22 v 1 0 y := by
    have h1 : part22 v 0 1 y = (fderiv ℝ (fderiv ℝ v) y (e2 1)) (e2 0) := by
      unfold part22 part2
      rw [fderiv_clm_apply ((hv.regular.fderiv_right (by norm_num)).differentiable one_ne_zero y)
        (differentiableAt_const (e2 0))]; simp
    have h2 : part22 v 1 0 y = (fderiv ℝ (fderiv ℝ v) y (e2 0)) (e2 1) := by
      unfold part22 part2
      rw [fderiv_clm_apply ((hv.regular.fderiv_right (by norm_num)).differentiable one_ne_zero y)
        (differentiableAt_const (e2 1))]; simp
    rw [h1, h2]
    exact (hv.regular.contDiffAt.isSymmSndFDerivAt (by simp)) (e2 1) (e2 0)
  have hline_p (i j : Fin 2) (y : Plane) (r : ℝ) :
      HasDerivAt (fun τ : ℝ => part2 v i (y + τ • e2 j))
        (part22 v i j (y + r • e2 j)) r := by
    have hpi : ContDiff ℝ 1 (part2 v i) :=
      (hv.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hl : HasDerivAt (fun τ : ℝ => y + τ • e2 j) (e2 j) r := by
      simpa using (((hasDerivAt_id r).smul_const (e2 j)).const_add y)
    exact (hpi.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt r hl
  have hline_v (j : Fin 2) (y : Plane) (r : ℝ) :
      HasDerivAt (fun τ : ℝ => v (y + τ • e2 j)) (part2 v j (y + r • e2 j)) r := by
    have hl : HasDerivAt (fun τ : ℝ => y + τ • e2 j) (e2 j) r := by
      simpa using (((hasDerivAt_id r).smul_const (e2 j)).const_add y)
    exact (hv.regular.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt r hl
  -- Step 1: On the horizontal segment uIcc s₀ s at height t₀, part2 v 1 = 0
  have hv1_horiz : part2 v 1 (s • e2 0 + t₀ • e2 1) = 0 := by
    let q : ℝ → ℝ := fun r => part2 v 1 (r • e2 0 + t₀ • e2 1) / part2 v 0 (r • e2 0 + t₀ • e2 1)
    have hq_deriv (r : ℝ) (hr : r ∈ Set.uIcc s₀ s) : HasDerivAt q 0 r := by
      have hpos := hs r hr
      have heq (i : Fin 2) : (fun τ : ℝ => part2 v i (τ • e2 0 + t₀ • e2 1)) =
          fun τ => part2 v i (t₀ • e2 1 + τ • e2 0) := by funext τ; congr 1; module
      have hd1 : HasDerivAt (fun τ => part2 v 1 (τ • e2 0 + t₀ • e2 1))
          (part22 v 1 0 (r • e2 0 + t₀ • e2 1)) r := by
        rw [heq 1]; simpa [add_comm] using hline_p 1 0 (t₀ • e2 1) r
      have hd0 : HasDerivAt (fun τ => part2 v 0 (τ • e2 0 + t₀ • e2 1))
          (part22 v 0 0 (r • e2 0 + t₀ • e2 1)) r := by
        rw [heq 0]; simpa [add_comm] using hline_p 0 0 (t₀ • e2 1) r
      have hdiv : HasDerivAt q
          ((part22 v 1 0 (r • e2 0 + t₀ • e2 1) * part2 v 0 (r • e2 0 + t₀ • e2 1) -
            part2 v 1 (r • e2 0 + t₀ • e2 1) * part22 v 0 0 (r • e2 0 + t₀ • e2 1)) /
            (part2 v 0 (r • e2 0 + t₀ • e2 1)) ^ 2) r := hd1.div hd0 hpos.ne'
      have hnum0 : part22 v 1 0 (r • e2 0 + t₀ • e2 1) * part2 v 0 (r • e2 0 + t₀ • e2 1) -
          part2 v 1 (r • e2 0 + t₀ • e2 1) * part22 v 0 0 (r • e2 0 + t₀ • e2 1) = 0 := by
        have := (hcol (r • e2 0 + t₀ • e2 1)).1; linarith
      rwa [hnum0, zero_div] at hdiv
    have hconst := eq_of_hasDerivAt_zero_on_uIcc hq_deriv
    have hq0 : q s₀ = 0 := by simp [q, hv1_0]
    rw [hq0] at hconst
    exact (div_eq_zero_iff.mp hconst).resolve_right (hs s Set.right_mem_uIcc).ne'
  -- Step 2: Along the vertical line at s, part2 v 0 stays equal to c0 > 0 and part2 v 1 = 0
  let c0 := part2 v 0 (s • e2 0 + t₀ • e2 1)
  have hc0 : 0 < c0 := hs s Set.right_mem_uIcc
  let J : Set ℝ := {t : ℝ | ∀ τ ∈ Set.uIcc t₀ t, 0 < part2 v 0 (s • e2 0 + τ • e2 1)}
  have hJ_const (t : ℝ) (ht : t ∈ J) :
      part2 v 1 (s • e2 0 + t • e2 1) = 0 ∧
      part2 v 0 (s • e2 0 + t • e2 1) = c0 := by
    have hv1_on (τ : ℝ) (hτ : τ ∈ Set.uIcc t₀ t) : part2 v 1 (s • e2 0 + τ • e2 1) = 0 := by
      let q : ℝ → ℝ := fun r => part2 v 1 (s • e2 0 + r • e2 1) / part2 v 0 (s • e2 0 + r • e2 1)
      have hq_d (r : ℝ) (hr : r ∈ Set.uIcc t₀ τ) : HasDerivAt q 0 r := by
        have hmem : r ∈ Set.uIcc t₀ t := Set.uIcc_subset_uIcc Set.left_mem_uIcc hτ hr
        have hpos := ht r hmem
        have hd1 := hline_p 1 1 (s • e2 0) r
        have hd0 := hline_p 0 1 (s • e2 0) r
        have hdiv : HasDerivAt q
            ((part22 v 1 1 (s • e2 0 + r • e2 1) * part2 v 0 (s • e2 0 + r • e2 1) -
              part2 v 1 (s • e2 0 + r • e2 1) * part22 v 0 1 (s • e2 0 + r • e2 1)) /
              (part2 v 0 (s • e2 0 + r • e2 1)) ^ 2) r := hd1.div hd0 hpos.ne'
        have hnum0 : part22 v 1 1 (s • e2 0 + r • e2 1) * part2 v 0 (s • e2 0 + r • e2 1) -
            part2 v 1 (s • e2 0 + r • e2 1) * part22 v 0 1 (s • e2 0 + r • e2 1) = 0 := by
          have := (hcol (s • e2 0 + r • e2 1)).2; linarith
        rwa [hnum0, zero_div] at hdiv
      have hconst := eq_of_hasDerivAt_zero_on_uIcc hq_d
      have hq0 : q t₀ = 0 := by simp [q, hv1_horiz]
      rw [hq0] at hconst
      exact (div_eq_zero_iff.mp hconst).resolve_right (ht τ hτ).ne'
    have hv0_d (τ : ℝ) (hτ : τ ∈ Set.uIcc t₀ t) :
        HasDerivAt (fun r : ℝ => part2 v 0 (s • e2 0 + r • e2 1)) 0 τ := by
      have hd := hline_p 0 1 (s • e2 0) τ
      have hv10 : part2 v 1 (s • e2 0 + τ • e2 1) = 0 := hv1_on τ hτ
      have hcol1 := (hcol (s • e2 0 + τ • e2 1)).1
      rw [hv10, zero_mul, sub_zero] at hcol1
      have hp10 : part22 v 1 0 (s • e2 0 + τ • e2 1) = 0 :=
        (mul_eq_zero.mp hcol1).resolve_left (ht τ hτ).ne'
      have hp01 : part22 v 0 1 (s • e2 0 + τ • e2 1) = 0 := (hsymm _).trans hp10
      rwa [hp01] at hd
    exact ⟨hv1_on t Set.right_mem_uIcc, eq_of_hasDerivAt_zero_on_uIcc hv0_d⟩
  have hJ_univ : ∀ t : ℝ, t ∈ J := by
    have hcont0 : Continuous (fun τ : ℝ => part2 v 0 (s • e2 0 + τ • e2 1)) :=
      hpc0.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
    have hJ_open : IsOpen J := by
      rw [Metric.isOpen_iff]
      intro t ht
      have hpos : 0 < part2 v 0 (s • e2 0 + t • e2 1) := ht t Set.right_mem_uIcc
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont0.continuousAt
        (part2 v 0 (s • e2 0 + t • e2 1) / 2) (by linarith)
      refine ⟨δ, hδ, fun t' ht' τ hτ => ?_⟩
      by_cases h1 : τ ∈ Set.uIcc t₀ t
      · exact ht τ h1
      · have hdist : dist τ t < δ := by
          have hmem' : τ ∈ Set.uIcc t t' := by
            rw [Set.mem_uIcc] at hτ h1 ⊢
            rcases hτ with ⟨ha, hb⟩ | ⟨ha, hb⟩
            · left; constructor
              · by_contra! hlt; exact h1 (Or.inl ⟨ha, hlt.le⟩)
              · exact hb
            · right; constructor
              · exact ha
              · by_contra! hlt; exact h1 (Or.inr ⟨hlt.le, hb⟩)
          have ht'_d : |t' - t| < δ := by simpa [Real.dist_eq] using Metric.mem_ball.mp ht'
          rw [Real.dist_eq]
          rw [Set.mem_uIcc] at hmem'
          rcases hmem' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
          · rw [abs_of_nonneg (by linarith)]
            have : t' - t ≤ |t' - t| := le_abs_self _
            linarith
          · rw [abs_of_nonpos (by linarith)]
            have : -(t' - t) ≤ |t' - t| := neg_le_abs _
            linarith
        have hb := hball hdist
        rw [Real.dist_eq, abs_lt] at hb
        linarith
    have hJ_closed : IsClosed J := by
      rw [← isOpen_compl_iff, Metric.isOpen_iff]
      intro t ht
      -- If t ∉ J, then ∃ τ ∈ uIcc t₀ t with part2 v 0 ≤ 0; in fact since J is connected around t₀
      -- and part2 v 0 = c0 > 0 on J, we must have part2 v 0 (s, τ) ≤ 0 at some τ strictly between t₀ and t or at t
      by_contra hnot
      -- Even simpler: prove J = univ directly by connectedness of ℝ? Need IsClosed J.
      -- If t ∈ closure J, then ∀ ε > 0, ∃ t' ∈ J with |t' - t| < ε.
      -- Wait: if t ∈ closure J, then every τ strictly between t₀ and t lies in uIcc t₀ t' for some t' ∈ J!
      -- And at τ = t, part2 v 0 (s, t) = lim part2 v 0 (s, t') = c0 > 0!
      have hclos : t ∈ closure J := by
        rw [Metric.mem_closure_iff]
        intro ε hε
        by_contra hno
        push Not at hno
        exact hnot ⟨ε, hε, fun t' ht' hJ' => (hno t' hJ').not_gt (by simpa [dist_comm] using Metric.mem_ball.mp ht')⟩
      have ht_in : t ∈ J := by
        intro τ hτ
        by_cases hτt : τ = t
        · rw [hτt]
          have hseq : ∀ n : ℕ, ∃ t' ∈ J, dist t' t < 1 / ((n : ℝ) + 1) := fun n => by
            obtain ⟨b, hbJ, hbd⟩ := Metric.mem_closure_iff.mp hclos (1 / ((n : ℝ) + 1)) (by positivity)
            exact ⟨b, hbJ, by rwa [dist_comm]⟩
          let tn : ℕ → ℝ := fun n => Classical.choose (hseq n)
          have htnJ (n : ℕ) : tn n ∈ J := (Classical.choose_spec (hseq n)).1
          have htn_t : Tendsto tn atTop (𝓝 t) := by
            rw [Metric.tendsto_atTop]
            intro ε hε
            obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
            refine ⟨N, fun n hn => (Classical.choose_spec (hseq n)).2.trans_le ?_⟩
            calc
              1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
                apply one_div_le_one_div_of_le (by positivity)
                linarith [show (N : ℝ) ≤ (n : ℝ) from Nat.cast_le.mpr hn]
              _ ≤ ε := hN.le
          have hval : Tendsto (fun n => part2 v 0 (s • e2 0 + tn n • e2 1)) atTop
              (𝓝 (part2 v 0 (s • e2 0 + t • e2 1))) := hcont0.continuousAt.tendsto.comp htn_t
          have hconst_n : (fun n => part2 v 0 (s • e2 0 + tn n • e2 1)) = fun _ => c0 :=
            funext fun n => (hJ_const (tn n) (htnJ n)).2
          rw [hconst_n] at hval
          have heq := tendsto_nhds_unique hval tendsto_const_nhds
          linarith
        · -- τ is strictly between t₀ and t (or τ = t₀), so pick t' ∈ J close enough to t
          by_cases hτ0 : τ = t₀
          · subst hτ0; exact hc0
          · have hdist_pos : 0 < dist τ t := dist_pos.mpr hτt
            obtain ⟨t', ht'J, ht'_close⟩ := Metric.mem_closure_iff.mp hclos (dist τ t) hdist_pos
            have hmem : τ ∈ Set.uIcc t₀ t' := by
              rw [Real.dist_eq, Real.dist_eq] at ht'_close
              rw [Set.mem_uIcc] at hτ ⊢
              rcases hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · have hlt : τ < t := lt_of_le_of_ne h2 hτt
                have hgt : τ < t' := by
                  have h1' := (abs_lt.mp ht'_close).2
                  rw [abs_of_neg (by linarith)] at h1'
                  linarith
                exact Or.inl ⟨h1, hgt.le⟩
              · have hgt : t < τ := lt_of_le_of_ne h1 (Ne.symm hτt)
                have hlt' : t' < τ := by
                  have h1' := (abs_lt.mp ht'_close).1
                  rw [abs_of_pos (by linarith)] at h1'
                  linarith
                exact Or.inr ⟨hlt'.le, h2⟩
            exact ht'J τ hmem
      exact ht ht_in
    have ht0J : t₀ ∈ J := by
      intro τ hτ
      have : τ = t₀ := by simpa [Set.uIcc_self] using hτ
      subst this; exact hc0
    have hclopen : J = Set.univ :=
      isClopen_iff.mp ⟨hJ_closed, hJ_open⟩ |>.resolve_left (Set.nonempty_iff_ne_empty.mp ⟨t₀, ht0J⟩)
    intro t
    rw [hclopen]; trivial
  intro t
  have ⟨hv1_t, hv0_t⟩ := hJ_const t (hJ_univ t)
  have hv_eq : v (s • e2 0 + t • e2 1) = v (s • e2 0 + t₀ • e2 1) := by
    apply eq_of_hasDerivAt_zero_on_uIcc (f := fun τ : ℝ => v (s • e2 0 + τ • e2 1))
    intro τ _
    have hd := hline_v 1 (s • e2 0) τ
    rwa [(hJ_const τ (hJ_univ τ)).1] at hd
  exact ⟨hv_eq, hv0_t, hv1_t⟩

-- Quadratic C^1 cap contradiction for a 1D interval (a, b) with g'(a)=g'(b)=0, g''(a)>0, g''(b)<0
set_option maxHeartbeats 1000000 in
private theorem quadratic_cap_contradiction {v : Plane → ℝ}
    (hv : DeGiorgi.IsBoundedSolution v)
    (h1 : ∀ y, |v y| ≤ 1)
    (hstab : ∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      0 ≤ ∫ y : Plane, (‖∇ ψ y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (ψ y) ^ 2))
    {g : ℝ → ℝ} (hg_c2 : ContDiff ℝ 2 g)
    {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    (hstrip : ∀ s ∈ Set.Ioo (a - δ) (b + δ), ∀ t : ℝ, v (s • e2 0 + t • e2 1) = g s)
    (hode : ∀ s ∈ Set.Ioo (a - δ) (b + δ), deriv (deriv g) s = (g s) ^ 3 - g s)
    (hgp_pos : ∀ s ∈ Set.Ioo a b, 0 < deriv g s)
    (hgpa : deriv g a = 0) (hgpb : deriv g b = 0)
    (hgppa : 0 < deriv (deriv g) a) (hgppb : deriv (deriv g) b < 0) :
    False := by
  have hgp_cont : Continuous (deriv g) := hg_c2.continuous_deriv (by norm_num)
  have hgpp_cont : Continuous (deriv (deriv g)) := by
    have h1' : ContDiff ℝ 1 (deriv g) := by
      rw [show (2 : WithTop ℕ∞) = (1 : ℕ) + 1 by norm_num, contDiff_succ_iff_deriv] at hg_c2
      exact hg_c2.2.2
    exact h1'.continuous_deriv le_rfl
  -- Choose small ε > 0 at both endpoints simultaneously
  have hlim_a : Tendsto (fun ε : ℝ => (deriv g (a + ε), deriv (deriv g) (a + ε)))
      (𝓝 0) (𝓝 (0, deriv (deriv g) a)) := by
    have h1' : Tendsto (fun ε : ℝ => a + ε) (𝓝 (0 : ℝ)) (𝓝 a) := by
      simpa using (tendsto_const_nhds (x := a)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
    have h2' := (hgp_cont.continuousAt.tendsto.comp h1').prodMk_nhds
      (hgpp_cont.continuousAt.tendsto.comp h1')
    simpa [Function.comp_def, hgpa] using h2'
  have hlim_b : Tendsto (fun ε : ℝ => (deriv g (b - ε), -deriv (deriv g) (b - ε)))
      (𝓝 0) (𝓝 (0, -deriv (deriv g) b)) := by
    have h1' : Tendsto (fun ε : ℝ => b - ε) (𝓝 (0 : ℝ)) (𝓝 b) := by
      simpa using (tendsto_const_nhds (x := b)).sub (tendsto_id (x := 𝓝 (0 : ℝ)))
    have h2' := (hgp_cont.continuousAt.tendsto.comp h1').prodMk_nhds
      ((hgpp_cont.continuousAt.tendsto.comp h1').neg)
    simpa [Function.comp_def, hgpb] using h2'
  let ma := deriv (deriv g) a
  let mb := -deriv (deriv g) b
  have hma : 0 < ma := hgppa
  have hmb : 0 < mb := by dsimp [mb]; linarith
  have hev_a : ∀ᶠ ε in 𝓝 (0 : ℝ),
      deriv (deriv g) (a + ε) > ma / 2 ∧
      deriv g (a + ε) < min (ma / 10) (ma * δ / 8) := by
    have hopen : IsOpen {p : ℝ × ℝ | p.2 > ma / 2 ∧ p.1 < min (ma / 10) (ma * δ / 8)} :=
      (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_fst continuous_const)
    have hmem : ((0 : ℝ), ma) ∈ {p : ℝ × ℝ | p.2 > ma / 2 ∧ p.1 < min (ma / 10) (ma * δ / 8)} :=
      ⟨by linarith, lt_min (by positivity) (by positivity)⟩
    exact hlim_a (hopen.mem_nhds hmem)
  have hev_b : ∀ᶠ ε in 𝓝 (0 : ℝ),
      -deriv (deriv g) (b - ε) > mb / 2 ∧
      deriv g (b - ε) < min (mb / 10) (mb * δ / 8) := by
    have hopen : IsOpen {p : ℝ × ℝ | p.2 > mb / 2 ∧ p.1 < min (mb / 10) (mb * δ / 8)} :=
      (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_fst continuous_const)
    have hmem : ((0 : ℝ), mb) ∈ {p : ℝ × ℝ | p.2 > mb / 2 ∧ p.1 < min (mb / 10) (mb * δ / 8)} :=
      ⟨by linarith, lt_min (by positivity) (by positivity)⟩
    exact hlim_b (hopen.mem_nhds hmem)
  have hev_small : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < min ((b - a) / 4) (δ / 4) :=
    isOpen_Iio.mem_nhds (show (0 : ℝ) < min ((b - a) / 4) (δ / 4) from
      lt_min (by linarith) (by linarith))
  have hall := (hev_a.and (hev_b.and hev_small)).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  obtain ⟨ε, ⟨⟨hm1_gt, hy1_lt⟩, ⟨hm2_gt, hy2_lt⟩, hε_lt⟩, hε_pos⟩ :=
    (hall.and (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  have hε0 : 0 < ε := hε_pos
  have haε_lt : a + ε < b - ε := by linarith [hε_lt.trans_le (min_le_left _ _)]
  have hε_δ : ε < δ / 4 := hε_lt.trans_le (min_le_right _ _)
  let y₁ := deriv g (a + ε)
  let m₁ := deriv (deriv g) (a + ε)
  let y₂ := deriv g (b - ε)
  let m₂ := -deriv (deriv g) (b - ε)
  have hy₁ : 0 < y₁ := hgp_pos (a + ε) ⟨by linarith, by linarith⟩
  have hy₂ : 0 < y₂ := hgp_pos (b - ε) ⟨by linarith, by linarith⟩
  have hm₁ : 0 < m₁ := by linarith
  have hm₂ : 0 < m₂ := by linarith
  let L₁ := 2 * y₁ / m₁
  let L₂ := 2 * y₂ / m₂
  have hL₁ : 0 < L₁ := by dsimp [L₁]; positivity
  have hL₂ : 0 < L₂ := by dsimp [L₂]; positivity
  let x₀ := a + ε - L₁
  let x₁ := b - ε + L₂
  have hx₀_gt : a - δ < x₀ := by
    have hL1_le : L₁ < δ / 2 := by
      dsimp [L₁]; rw [div_lt_iff₀ hm₁]
      have h1' : y₁ < ma * δ / 8 := hy1_lt.trans_le (min_le_right _ _)
      nlinarith
    dsimp [x₀]; linarith
  have hx₁_lt : x₁ < b + δ := by
    have hL2_le : L₂ < δ / 2 := by
      dsimp [L₂]; rw [div_lt_iff₀ hm₂]
      have h2' : y₂ < mb * δ / 8 := hy2_lt.trans_le (min_le_right _ _)
      nlinarith
    dsimp [x₁]; linarith
  let A₁ := m₁ ^ 2 / (4 * y₁)
  let A₂ := m₂ ^ 2 / (4 * y₂)
  -- Piecewise C^1 test function h and its continuous derivative dh
  let h : ℝ → ℝ := fun s =>
    if s ≤ x₀ then 0
    else if s ≤ a + ε then A₁ * (s - x₀) ^ 2
    else if s ≤ b - ε then deriv g s
    else if s ≤ x₁ then A₂ * (x₁ - s) ^ 2
    else 0
  let dh : ℝ → ℝ := fun s =>
    if s ≤ x₀ then 0
    else if s ≤ a + ε then 2 * A₁ * (s - x₀)
    else if s ≤ b - ε then deriv (deriv g) s
    else if s ≤ x₁ then -2 * A₂ * (x₁ - s)
    else 0
  -- Boundary match identities
  have hA1_val : A₁ * (a + ε - x₀) ^ 2 = y₁ := by
    dsimp [A₁, x₀, L₁]; field_simp [hm₁.ne', hy₁.ne']; ring
  have hA1_der : 2 * A₁ * (a + ε - x₀) = m₁ := by
    dsimp [A₁, x₀, L₁]; field_simp [hm₁.ne', hy₁.ne']; ring
  have hA2_val : A₂ * (x₁ - (b - ε)) ^ 2 = y₂ := by
    dsimp [A₂, x₁, L₂]; field_simp [hm₂.ne', hy₂.ne']; ring
  have hA2_der : -2 * A₂ * (x₁ - (b - ε)) = -m₂ := by
    dsimp [A₂, x₁, L₂]; field_simp [hm₂.ne', hy₂.ne']; ring
  have hgp_c1 : ContDiff ℝ 1 (deriv g) := by
    rw [show (2 : WithTop ℕ∞) = (1 : ℕ) + 1 by norm_num, contDiff_succ_iff_deriv] at hg_c2
    exact hg_c2.2.2
  have hdh_cont : Continuous dh := by
    have hx0_le : x₀ ≤ a + ε := by dsimp [x₀]; linarith
    have hx1_ge : b - ε ≤ x₁ := by dsimp [x₁]; linarith
    have hc4 : Continuous (fun s : ℝ => if s ≤ x₁ then -2 * A₂ * (x₁ - s) else 0) :=
      Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const fun s hs => by
        rw [hs, sub_self, mul_zero]
    have hc3 : Continuous (fun s : ℝ =>
        if s ≤ b - ε then deriv (deriv g) s else if s ≤ x₁ then -2 * A₂ * (x₁ - s) else 0) :=
      Continuous.if_le hgpp_cont hc4 continuous_id continuous_const fun s hs => by
        rw [hs, if_pos hx1_ge, hA2_der]; dsimp [m₂]; ring
    have hc2 : Continuous (fun s : ℝ =>
        if s ≤ a + ε then 2 * A₁ * (s - x₀)
        else if s ≤ b - ε then deriv (deriv g) s
        else if s ≤ x₁ then -2 * A₂ * (x₁ - s) else 0) :=
      Continuous.if_le (by fun_prop) hc3 continuous_id continuous_const fun s hs => by
        rw [hs, if_pos haε_lt.le, hA1_der]
    exact Continuous.if_le continuous_const hc2 continuous_id continuous_const fun s hs => by
      rw [hs, if_pos hx0_le, sub_self, mul_zero]
  -- Prove h s = ∫ r in x₀..s, dh r (giving HasDerivAt h (dh s) s everywhere via FTC!)
  have hh_eq_int (s : ℝ) : h s = ∫ r in x₀..s, dh r := by
    have hx0_le : x₀ ≤ a + ε := by dsimp [x₀]; linarith
    have hx1_ge : b - ε ≤ x₁ := by dsimp [x₁]; linarith
    have hdh_int (p q : ℝ) : IntervalIntegrable dh volume p q :=
      hdh_cont.intervalIntegrable p q
    have hseg1 (r : ℝ) (hr1 : x₀ ≤ r) (hr2 : r ≤ a + ε) :
        (∫ τ in x₀..r, dh τ) = A₁ * (r - x₀) ^ 2 := by
      have heq : Set.EqOn dh (fun τ => 2 * A₁ * (τ - x₀)) (Set.Ioc x₀ r) := by
        intro τ hτ; simp [dh, not_le.mpr hτ.1, hτ.2.trans hr2]
      have hcongr : (∫ τ in x₀..r, dh τ) = ∫ τ in x₀..r, 2 * A₁ * (τ - x₀) :=
        intervalIntegral.integral_congr_ae (ae_of_all _ fun τ hτ =>
          heq (Set.uIoc_of_le hr1 ▸ hτ))
      rw [hcongr]
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := x₀) (b := r)
        (f := fun τ : ℝ => A₁ * (τ - x₀) ^ 2) (f' := fun τ : ℝ => 2 * A₁ * (τ - x₀))
        (fun τ _ => by
          have h2 := (((hasDerivAt_id τ).sub_const x₀).pow 2).const_mul A₁
          have hval : A₁ * (2 * (τ - x₀) ^ (2 - 1) * 1) = 2 * A₁ * (τ - x₀) := by norm_num; ring
          exact hval ▸ h2)
        ((by fun_prop : Continuous fun τ : ℝ => 2 * A₁ * (τ - x₀)).intervalIntegrable x₀ r)
      simpa using hftc
    have hseg2 (r : ℝ) (hr1 : a + ε ≤ r) (hr2 : r ≤ b - ε) :
        (∫ τ in (a + ε)..r, dh τ) = deriv g r - y₁ := by
      have heq : Set.EqOn dh (deriv (deriv g)) (Set.Ioc (a + ε) r) := by
        intro τ hτ
        have h0 : ¬ τ ≤ x₀ := by linarith [hτ.1]
        simp [dh, h0, not_le.mpr hτ.1, hτ.2.trans hr2]
      have hcongr : (∫ τ in (a + ε)..r, dh τ) = ∫ τ in (a + ε)..r, deriv (deriv g) τ :=
        intervalIntegral.integral_congr_ae (ae_of_all _ fun τ hτ =>
          heq (Set.uIoc_of_le hr1 ▸ hτ))
      rw [hcongr]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun τ _ => (hgp_c1.differentiable one_ne_zero τ).hasDerivAt)
        (hgpp_cont.intervalIntegrable _ _)
    have hseg3 (r : ℝ) (hr1 : b - ε ≤ r) (hr2 : r ≤ x₁) :
        (∫ τ in (b - ε)..r, dh τ) = A₂ * (x₁ - r) ^ 2 - y₂ := by
      have heq : Set.EqOn dh (fun τ => -2 * A₂ * (x₁ - τ)) (Set.Ioc (b - ε) r) := by
        intro τ hτ
        have h0 : ¬ τ ≤ x₀ := by linarith [hτ.1]
        have h1' : ¬ τ ≤ a + ε := by linarith [hτ.1]
        simp [dh, h0, h1', not_le.mpr hτ.1, hτ.2.trans hr2]
      have hcongr : (∫ τ in (b - ε)..r, dh τ) = ∫ τ in (b - ε)..r, (-2 * A₂ * (x₁ - τ)) :=
        intervalIntegral.integral_congr_ae (ae_of_all _ fun τ hτ =>
          heq (Set.uIoc_of_le hr1 ▸ hτ))
      rw [hcongr]
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := b - ε) (b := r)
        (f := fun τ : ℝ => A₂ * (x₁ - τ) ^ 2) (f' := fun τ : ℝ => -2 * A₂ * (x₁ - τ))
        (fun τ _ => by
          have h2 := (((hasDerivAt_id τ).const_sub x₁).pow 2).const_mul A₂
          have hval : A₂ * (2 * (x₁ - τ) ^ (2 - 1) * (-1)) = -2 * A₂ * (x₁ - τ) := by norm_num; ring
          exact hval ▸ h2)
        ((by fun_prop : Continuous fun τ : ℝ => -2 * A₂ * (x₁ - τ)).intervalIntegrable (b - ε) r)
      rw [hftc, hA2_val]
    by_cases h1 : s ≤ x₀
    · rw [show h s = 0 from if_pos h1]
      symm
      rw [intervalIntegral.integral_of_ge h1]
      have hz : Set.EqOn dh (fun _ => (0 : ℝ)) (Set.Ioc s x₀) := fun τ hτ => if_pos hτ.2
      rw [setIntegral_congr_fun measurableSet_Ioc hz, integral_zero, neg_zero]
    · push Not at h1
      by_cases h2 : s ≤ a + ε
      · simp only [h, not_le.mpr h1, ↓reduceIte, h2]
        exact (hseg1 s h1.le h2).symm
      · push Not at h2
        by_cases h3 : s ≤ b - ε
        · simp only [h, not_le.mpr h1, not_le.mpr h2, ↓reduceIte, h3]
          rw [← intervalIntegral.integral_add_adjacent_intervals (hdh_int x₀ (a + ε)) (hdh_int (a + ε) s),
            hseg1 (a + ε) hx0_le le_rfl, hA1_val, hseg2 s h2.le h3]
          ring
        · push Not at h3
          by_cases h4 : s ≤ x₁
          · simp only [h, not_le.mpr h1, not_le.mpr h2, not_le.mpr h3, ↓reduceIte, h4]
            rw [← intervalIntegral.integral_add_adjacent_intervals (hdh_int x₀ (b - ε)) (hdh_int (b - ε) s),
              ← intervalIntegral.integral_add_adjacent_intervals (hdh_int x₀ (a + ε)) (hdh_int (a + ε) (b - ε)),
              hseg1 (a + ε) hx0_le le_rfl, hA1_val,
              hseg2 (b - ε) haε_lt.le le_rfl, hseg3 s h3.le h4]
            ring
          · push Not at h4
            simp only [h, not_le.mpr h1, not_le.mpr h2, not_le.mpr h3, not_le.mpr h4, ↓reduceIte]
            have hseg4 : (∫ τ in x₁..s, dh τ) = 0 := by
              have heq : Set.EqOn dh (fun _ => (0 : ℝ)) (Set.Ioc x₁ s) := by
                intro τ hτ
                have hr0 : ¬ τ ≤ x₀ := by linarith [hτ.1]
                have hr1 : ¬ τ ≤ a + ε := by linarith [hτ.1]
                have hr2 : ¬ τ ≤ b - ε := by linarith [hτ.1]
                simp [dh, hr0, hr1, hr2, not_le.mpr hτ.1]
              have hcongr : (∫ τ in x₁..s, dh τ) = ∫ _ in x₁..s, (0 : ℝ) :=
                intervalIntegral.integral_congr_ae (ae_of_all _ fun τ hτ =>
                  heq (Set.uIoc_of_le h4.le ▸ hτ))
              rw [hcongr, intervalIntegral.integral_zero]
            rw [← intervalIntegral.integral_add_adjacent_intervals (hdh_int x₀ x₁) (hdh_int x₁ s),
              ← intervalIntegral.integral_add_adjacent_intervals (hdh_int x₀ (b - ε)) (hdh_int (b - ε) x₁),
              ← intervalIntegral.integral_add_adjacent_intervals (hdh_int x₀ (a + ε)) (hdh_int (a + ε) (b - ε)),
              hseg1 (a + ε) hx0_le le_rfl, hA1_val,
              hseg2 (b - ε) haε_lt.le le_rfl, hseg3 x₁ hx1_ge le_rfl, hseg4]
            ring
  have hh_deriv (s : ℝ) : HasDerivAt h (dh s) s := by
    have heq : h = fun r => ∫ τ in x₀..r, dh τ := funext hh_eq_int
    rw [heq]
    exact intervalIntegral.integral_hasDerivAt_right (hdh_cont.intervalIntegrable x₀ s)
      hdh_cont.stronglyMeasurable.stronglyMeasurableAtFilter hdh_cont.continuousAt
  have hh_c1 : ContDiff ℝ 1 h := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun s => (hh_deriv s).differentiableAt, ?_⟩
    have heq : deriv h = dh := funext fun s => (hh_deriv s).deriv
    rwa [heq]
  have hx0_le : x₀ ≤ a + ε := by dsimp [x₀]; linarith
  have hx1_ge : b - ε ≤ x₁ := by dsimp [x₁]; linarith
  have hh_supp : HasCompactSupport h := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := x₀) (b := x₁))
    intro s hs
    by_contra hout
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hout
    rcases hout with hlt | hgt
    · exact hs (if_pos hlt.le)
    · have hr0 : ¬ s ≤ x₀ := by linarith
      have hr1 : ¬ s ≤ a + ε := by linarith
      have hr2 : ¬ s ≤ b - ε := by linarith
      exact hs (by simp [h, hr0, hr1, hr2, not_le.mpr hgt])
  -- Compute the 1D energy integral I_1D < 0
  have h1d_neg : (∫ s : ℝ, ((dh s) ^ 2 + (3 * (g s) ^ 2 - 1) * (h s) ^ 2)) < 0 := by
    let Q := fun s : ℝ => (dh s) ^ 2 + (3 * (g s) ^ 2 - 1) * (h s) ^ 2
    have hQ_cont : Continuous Q :=
      (hdh_cont.pow 2).add (((continuous_const.mul (hg_c2.continuous.pow 2)).sub continuous_const).mul
        (hh_c1.continuous.pow 2))
    have hQ_zero_out : ∀ s ∉ Set.Ioc x₀ x₁, Q s = 0 := by
      intro s hs
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hs
      rcases hs with hle | hgt
      · simp [Q, h, dh, hle]
      · have hr0 : ¬ s ≤ x₀ := by linarith
        have hr1 : ¬ s ≤ a + ε := by linarith
        have hr2 : ¬ s ≤ b - ε := by linarith
        simp [Q, h, dh, hr0, hr1, hr2, not_le.mpr hgt]
    have hQ_eq_int : (∫ s : ℝ, Q s) = ∫ s in x₀..x₁, Q s := by
      have h1' := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := Set.Ioc x₀ x₁)
        (f := Q) hQ_zero_out
      rw [← h1', intervalIntegral.integral_of_le (by linarith)]
    have hQ_int (p q : ℝ) : IntervalIntegrable Q volume p q := hQ_cont.intervalIntegrable p q
    -- Piece 2 (middle): FTC on [a+ε, b-ε] gives -y₂ m₂ - y₁ m₁
    have hmid : (∫ s in (a + ε)..(b - ε), Q s) = -(y₂ * m₂) - y₁ * m₁ := by
      have heq : Set.EqOn Q (fun s => (deriv (deriv g) s) ^ 2 + (3 * (g s) ^ 2 - 1) * (deriv g s) ^ 2)
          (Set.Ioc (a + ε) (b - ε)) := by
        intro s hs
        have h0 : ¬ s ≤ x₀ := by linarith [hs.1]
        simp [Q, h, dh, h0, not_le.mpr hs.1, hs.2]
      have hcongr : (∫ s in (a + ε)..(b - ε), Q s) =
          ∫ s in (a + ε)..(b - ε), ((deriv (deriv g) s) ^ 2 + (3 * (g s) ^ 2 - 1) * (deriv g s) ^ 2) :=
        intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs =>
          heq (Set.uIoc_of_le haε_lt.le ▸ hs))
      rw [hcongr]
      have hftc : (∫ s in (a + ε)..(b - ε),
          ((deriv (deriv g) s) ^ 2 + (3 * (g s) ^ 2 - 1) * (deriv g s) ^ 2)) =
          deriv g (b - ε) * deriv (deriv g) (b - ε) - deriv g (a + ε) * deriv (deriv g) (a + ε) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun s : ℝ => deriv g s * deriv (deriv g) s)
        · intro s hs
          rw [Set.uIcc_of_le haε_lt.le] at hs
          have hs_in : s ∈ Set.Ioo (a - δ) (b + δ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
          have hd1 : HasDerivAt (deriv g) (deriv (deriv g) s) s :=
            (hgp_c1.differentiable one_ne_zero s).hasDerivAt
          have hd2 : HasDerivAt (deriv (deriv g)) ((3 * (g s) ^ 2 - 1) * deriv g s) s := by
            have hev : deriv (deriv g) =ᶠ[𝓝 s] fun r => (g r) ^ 3 - g r := by
              filter_upwards [isOpen_Ioo.mem_nhds hs_in] with r hr
              exact hode r hr
            have hgd : HasDerivAt g (deriv g s) s :=
              (hg_c2.differentiable (by norm_num) s).hasDerivAt
            have hpoly : HasDerivAt (fun r => (g r) ^ 3 - g r)
                ((3 * (g s) ^ 2 - 1) * deriv g s) s := by
              have hp := (hgd.pow 3).sub hgd
              have hval : 3 * g s ^ (3 - 1) * deriv g s - deriv g s =
                  (3 * (g s) ^ 2 - 1) * deriv g s := by norm_num; ring
              exact hval ▸ hp
            exact hpoly.congr_of_eventuallyEq hev
          have hmul := hd1.mul hd2
          have hval : deriv (deriv g) s * deriv (deriv g) s +
              deriv g s * ((3 * (g s) ^ 2 - 1) * deriv g s) =
              (deriv (deriv g) s) ^ 2 + (3 * (g s) ^ 2 - 1) * (deriv g s) ^ 2 := by ring
          exact hval ▸ hmul
        · exact ((hgpp_cont.pow 2).add (((continuous_const.mul (hg_c2.continuous.pow 2)).sub
            continuous_const).mul (hgp_cont.pow 2))).intervalIntegrable _ _
      rw [hftc]
      dsimp [y₁, m₁, y₂, m₂]
      ring
    -- Piece 1 (left cap): <= (2/3) y₁ m₁ + 2 L₁ y₁^2
    have hleft_cap : (∫ s in x₀..(a + ε), Q s) ≤ (2 / 3) * (y₁ * m₁) + 2 * L₁ * y₁ ^ 2 := by
      have hdom : ∀ s ∈ Set.Ioc x₀ (a + ε),
          Q s ≤ (2 * A₁ * (s - x₀)) ^ 2 + 2 * y₁ ^ 2 := by
        intro s hs
        have hhs : h s = A₁ * (s - x₀) ^ 2 := by simp [h, not_le.mpr hs.1, hs.2]
        have hdhs : dh s = 2 * A₁ * (s - x₀) := by simp [dh, not_le.mpr hs.1, hs.2]
        have hhs_nn : 0 ≤ h s := by rw [hhs]; dsimp [A₁]; positivity
        have hhs_le : h s ≤ y₁ := by
          rw [hhs, ← hA1_val]
          apply mul_le_mul_of_nonneg_left _ (by dsimp [A₁]; positivity)
          exact pow_le_pow_left₀ (by linarith [hs.1]) (by linarith [hs.2]) 2
        have hgs_bd : |g s| ≤ 1 := by
          have hs_in : s ∈ Set.Ioo (a - δ) (b + δ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
          rw [← hstrip s hs_in 0]
          exact h1 _
        have hpot_le : 3 * (g s) ^ 2 - 1 ≤ 2 := by
          have hsq : (g s) ^ 2 ≤ 1 := by
            have := sq_le_sq.mpr (show |g s| ≤ |(1 : ℝ)| by simpa using hgs_bd)
            simpa using this
          linarith
        dsimp [Q]
        rw [hdhs]
        have hsq_le : (h s) ^ 2 ≤ y₁ ^ 2 := pow_le_pow_left₀ hhs_nn hhs_le 2
        nlinarith [sq_nonneg (h s)]
      have hint_dom : IntervalIntegrable (fun s : ℝ => (2 * A₁ * (s - x₀)) ^ 2 + 2 * y₁ ^ 2)
          volume x₀ (a + ε) :=
        (by fun_prop : Continuous fun s : ℝ => (2 * A₁ * (s - x₀)) ^ 2 + 2 * y₁ ^ 2).intervalIntegrable _ _
      have hmono : (∫ s in x₀..(a + ε), Q s) ≤
          ∫ s in x₀..(a + ε), ((2 * A₁ * (s - x₀)) ^ 2 + 2 * y₁ ^ 2) :=
        intervalIntegral.integral_mono_on hx0_le (hQ_int x₀ (a + ε)) hint_dom fun s hs =>
          if hse : s = x₀ then by
            subst hse; simp [Q, h, dh]; positivity
          else hdom s ⟨lt_of_le_of_ne hs.1 (Ne.symm hse), hs.2⟩
      have heval : (∫ s in x₀..(a + ε), ((2 * A₁ * (s - x₀)) ^ 2 + 2 * y₁ ^ 2)) =
          (2 / 3) * (y₁ * m₁) + 2 * L₁ * y₁ ^ 2 := by
        have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun s : ℝ => (4 / 3) * A₁ ^ 2 * (s - x₀) ^ 3 + 2 * y₁ ^ 2 * (s - x₀))
          (f' := fun s : ℝ => (2 * A₁ * (s - x₀)) ^ 2 + 2 * y₁ ^ 2)
          (fun s _ => by
            have hd1 := (((hasDerivAt_id s).sub_const x₀).pow 3).const_mul ((4 / 3) * A₁ ^ 2)
            have hd2 := ((hasDerivAt_id s).sub_const x₀).const_mul (2 * y₁ ^ 2)
            have hval : 4 / 3 * A₁ ^ 2 * (3 * (s - x₀) ^ (3 - 1) * 1) + 2 * y₁ ^ 2 * 1 =
                (2 * A₁ * (s - x₀)) ^ 2 + 2 * y₁ ^ 2 := by norm_num; ring
            exact hval ▸ hd1.add hd2)
          hint_dom
        rw [hftc]
        have hdiff : a + ε - x₀ = L₁ := by dsimp [x₀]; ring
        rw [sub_self, zero_pow (by norm_num), mul_zero, mul_zero, add_zero, sub_zero, hdiff]
        dsimp [A₁, L₁]
        field_simp [hm₁.ne', hy₁.ne']
        ring
      exact hmono.trans_eq heval
    -- Piece 3 (right cap): <= (2/3) y₂ m₂ + 2 L₂ y₂^2
    have hright_cap : (∫ s in (b - ε)..x₁, Q s) ≤ (2 / 3) * (y₂ * m₂) + 2 * L₂ * y₂ ^ 2 := by
      have hdom : ∀ s ∈ Set.Ioc (b - ε) x₁,
          Q s ≤ (-2 * A₂ * (x₁ - s)) ^ 2 + 2 * y₂ ^ 2 := by
        intro s hs
        have hr0 : ¬ s ≤ x₀ := by linarith [hs.1]
        have hr1 : ¬ s ≤ a + ε := by linarith [hs.1]
        have hhs : h s = A₂ * (x₁ - s) ^ 2 := by simp [h, hr0, hr1, not_le.mpr hs.1, hs.2]
        have hdhs : dh s = -2 * A₂ * (x₁ - s) := by simp [dh, hr0, hr1, not_le.mpr hs.1, hs.2]
        have hhs_nn : 0 ≤ h s := by rw [hhs]; dsimp [A₂]; positivity
        have hhs_le : h s ≤ y₂ := by
          rw [hhs, ← hA2_val]
          apply mul_le_mul_of_nonneg_left _ (by dsimp [A₂]; positivity)
          exact pow_le_pow_left₀ (by linarith [hs.2]) (by linarith [hs.1]) 2
        have hgs_bd : |g s| ≤ 1 := by
          have hs_in : s ∈ Set.Ioo (a - δ) (b + δ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
          rw [← hstrip s hs_in 0]
          exact h1 _
        have hpot_le : 3 * (g s) ^ 2 - 1 ≤ 2 := by
          have hsq : (g s) ^ 2 ≤ 1 := by
            have := sq_le_sq.mpr (show |g s| ≤ |(1 : ℝ)| by simpa using hgs_bd)
            simpa using this
          linarith
        dsimp [Q]
        rw [hdhs]
        have hsq_le : (h s) ^ 2 ≤ y₂ ^ 2 := pow_le_pow_left₀ hhs_nn hhs_le 2
        nlinarith [sq_nonneg (h s)]
      have hint_dom : IntervalIntegrable (fun s : ℝ => (-2 * A₂ * (x₁ - s)) ^ 2 + 2 * y₂ ^ 2)
          volume (b - ε) x₁ :=
        (by fun_prop : Continuous fun s : ℝ => (-2 * A₂ * (x₁ - s)) ^ 2 + 2 * y₂ ^ 2).intervalIntegrable _ _
      have hmono : (∫ s in (b - ε)..x₁, Q s) ≤
          ∫ s in (b - ε)..x₁, ((-2 * A₂ * (x₁ - s)) ^ 2 + 2 * y₂ ^ 2) :=
        intervalIntegral.integral_mono_on hx1_ge (hQ_int (b - ε) x₁) hint_dom fun s hs =>
          if hse : s = b - ε then by
            subst hse
            have hr0 : ¬ b - ε ≤ x₀ := by linarith
            have hr1 : ¬ b - ε ≤ a + ε := not_le.mpr haε_lt
            have hhs : h (b - ε) = y₂ := by simp [h, hr0, hr1, y₂]
            have hdhs : dh (b - ε) = -m₂ := by simp [dh, hr0, hr1, m₂]
            have hgs_bd : |g (b - ε)| ≤ 1 := by
              rw [← hstrip (b - ε) ⟨by linarith, by linarith⟩ 0]; exact h1 _
            have hpot_le : 3 * (g (b - ε)) ^ 2 - 1 ≤ 2 := by
              have hsq : (g (b - ε)) ^ 2 ≤ 1 := by
                have := sq_le_sq.mpr (show |g (b - ε)| ≤ |(1 : ℝ)| by simpa using hgs_bd)
                simpa using this
              linarith
            dsimp [Q]; rw [hhs, hdhs, hA2_der]; nlinarith [sq_nonneg y₂]
          else hdom s ⟨lt_of_le_of_ne hs.1 (Ne.symm hse), hs.2⟩
      have heval : (∫ s in (b - ε)..x₁, ((-2 * A₂ * (x₁ - s)) ^ 2 + 2 * y₂ ^ 2)) =
          (2 / 3) * (y₂ * m₂) + 2 * L₂ * y₂ ^ 2 := by
        have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun s : ℝ => -(4 / 3) * A₂ ^ 2 * (x₁ - s) ^ 3 + 2 * y₂ ^ 2 * s)
          (f' := fun s : ℝ => (-2 * A₂ * (x₁ - s)) ^ 2 + 2 * y₂ ^ 2)
          (fun s _ => by
            have hd1 := (((hasDerivAt_id s).const_sub x₁).pow 3).const_mul (-(4 / 3) * A₂ ^ 2)
            have hd2 := (hasDerivAt_id s).const_mul (2 * y₂ ^ 2)
            have hval : -(4 / 3) * A₂ ^ 2 * (3 * (x₁ - s) ^ (3 - 1) * (-1)) + 2 * y₂ ^ 2 * 1 =
                (-2 * A₂ * (x₁ - s)) ^ 2 + 2 * y₂ ^ 2 := by norm_num; ring
            exact hval ▸ hd1.add hd2)
          hint_dom
        rw [hftc]
        have hdiff : x₁ - (b - ε) = L₂ := by dsimp [x₁]; ring
        have heq1 : -(4 / 3) * A₂ ^ 2 * (x₁ - x₁) ^ 3 + 2 * y₂ ^ 2 * x₁ -
            (-(4 / 3) * A₂ ^ 2 * (x₁ - (b - ε)) ^ 3 + 2 * y₂ ^ 2 * (b - ε)) =
            (4 / 3) * A₂ ^ 2 * L₂ ^ 3 + 2 * y₂ ^ 2 * L₂ := by
          rw [sub_self, hdiff]; linear_combination 2 * y₂ ^ 2 * hdiff
        rw [heq1]
        dsimp [A₂, L₂]
        field_simp [hm₂.ne', hy₂.ne']
        ring
      exact hmono.trans_eq heval
    have htotal : (∫ s : ℝ, Q s) =
        (∫ s in x₀..(a + ε), Q s) + (∫ s in (a + ε)..(b - ε), Q s) + (∫ s in (b - ε)..x₁, Q s) := by
      rw [hQ_eq_int, ← intervalIntegral.integral_add_adjacent_intervals (hQ_int x₀ (b - ε)) (hQ_int (b - ε) x₁),
        ← intervalIntegral.integral_add_adjacent_intervals (hQ_int x₀ (a + ε)) (hQ_int (a + ε) (b - ε))]
    have hneg1 : 2 * L₁ * y₁ ^ 2 < (1 / 3) * (y₁ * m₁) := by
      have h1' : y₁ < ma / 10 := hy1_lt.trans_le (min_le_left _ _)
      have hm1' : ma / 2 < m₁ := hm1_gt
      have hsq : 12 * y₁ ^ 2 < m₁ ^ 2 := by nlinarith only [hy₁, hm₁, h1', hm1']
      dsimp [L₁]
      have heq : 2 * (2 * y₁ / m₁) * y₁ ^ 2 = (4 * y₁ ^ 3) / m₁ := by ring
      rw [heq, div_lt_iff₀ hm₁]
      nlinarith only [hsq, hy₁, hm₁]
    have hneg2 : 2 * L₂ * y₂ ^ 2 < (1 / 3) * (y₂ * m₂) := by
      have h2' : y₂ < mb / 10 := hy2_lt.trans_le (min_le_left _ _)
      have hm2' : mb / 2 < m₂ := hm2_gt
      have hsq : 12 * y₂ ^ 2 < m₂ ^ 2 := by nlinarith only [hy₂, hm₂, h2', hm2']
      dsimp [L₂]
      have heq : 2 * (2 * y₂ / m₂) * y₂ ^ 2 = (4 * y₂ ^ 3) / m₂ := by ring
      rw [heq, div_lt_iff₀ hm₂]
      nlinarith only [hsq, hy₂, hm₂]
    linarith only [htotal, hmid, hleft_cap, hright_cap, hneg1, hneg2]
  -- Now contradict 2D stability of v using ψ_L(s, t) = h(s) * bump1(L⁻¹ * t)
  obtain ⟨Mχ, hMχ0, hMχ_bd⟩ := bump1_scaled_bounds
  let I := ∫ s : ℝ, ((dh s) ^ 2 + (3 * (g s) ^ 2 - 1) * (h s) ^ 2)
  let J := ∫ s : ℝ, (h s) ^ 2
  have hJ0 : 0 ≤ J := integral_nonneg fun _ => sq_nonneg _
  have hIneg : I < 0 := h1d_neg
  let L : ℝ := max 1 (2 * Mχ ^ 2 * J / (-I) + 1)
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL0 : 0 < L := by linarith
  let χ : ℝ → ℝ := fun t => bump1 (L⁻¹ * t)
  have hχ_c1 : ContDiff ℝ 1 χ := bump1.contDiff.comp (contDiff_const.mul contDiff_id)
  have hχc : HasCompactSupport χ := by
    simpa [χ, smul_eq_mul] using bump1.hasCompactSupport.comp_smul (inv_ne_zero hL0.ne')
  let ψ : Plane → ℝ := fun y => h (y 0) * χ (y 1)
  have hc0 : ContDiff ℝ 1 (fun y : Plane => y 0) :=
    (((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.coord 0).toContinuousLinearMap).contDiff
  have hc1 : ContDiff ℝ 1 (fun y : Plane => y 1) :=
    (((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.coord 1).toContinuousLinearMap).contDiff
  have hψ_c1 : ContDiff ℝ 1 ψ := (hh_c1.comp hc0).mul (hχ_c1.comp hc1)
  have hψc : HasCompactSupport ψ := by
    have hK : IsCompact (planeHomeoProd.symm '' (tsupport h ×ˢ tsupport χ)) :=
      (hh_supp.prod hχc).image planeHomeoProd.symm.continuous
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro y hy
    refine ⟨(y 0, y 1), ⟨?_, ?_⟩, by ext i; fin_cases i <;> simp [planeHomeoProd, e2]⟩
    · apply subset_closure; intro h0; exact hy (by simp [ψ, h0])
    · apply subset_closure; intro h0; exact hy (by simp [ψ, h0])
  have hst := hstab ψ hψ_c1 hψc
  have hgrad_ψ (y : Plane) : ‖∇ ψ y‖ ^ 2 = (dh (y 0)) ^ 2 * (χ (y 1)) ^ 2 + (h (y 0)) ^ 2 * (deriv χ (y 1)) ^ 2 := by
    let b2 := EuclideanSpace.basisFun (Fin 2) ℝ
    have hnorm2 : ‖∇ ψ y‖ ^ 2 = (fderiv ℝ ψ y (e2 0)) ^ 2 + (fderiv ℝ ψ y (e2 1)) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← b2.sum_inner_mul_inner, Fin.sum_univ_two]
      have h0 : b2 0 = e2 0 := EuclideanSpace.basisFun_apply (Fin 2) ℝ 0
      have h1' : b2 1 = e2 1 := EuclideanSpace.basisFun_apply (Fin 2) ℝ 1
      have hd0 : inner ℝ (∇ ψ y) (e2 0) = fderiv ℝ ψ y (e2 0) := by
        rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]
      have hd1 : inner ℝ (∇ ψ y) (e2 1) = fderiv ℝ ψ y (e2 1) := by
        rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]
      rw [h0, h1', real_inner_comm (∇ ψ y) (e2 0), real_inner_comm (∇ ψ y) (e2 1), hd0, hd1]; ring
    have hp0 : fderiv ℝ ψ y (e2 0) = dh (y 0) * χ (y 1) := by
      have h1' : HasDerivAt (fun r : ℝ => ψ (y + r • e2 0)) (fderiv ℝ ψ y (e2 0)) 0 := by
        have hl : HasDerivAt (fun r : ℝ => y + r • e2 0) (e2 0) 0 := by
          simpa using (((hasDerivAt_id (0 : ℝ)).smul_const (e2 0)).const_add y)
        have hd := (hψ_c1.differentiable one_ne_zero (y + (0 : ℝ) • e2 0)).hasFDerivAt.comp_hasDerivAt 0 hl
        rw [zero_smul, add_zero] at hd; exact hd
      have h2' : HasDerivAt (fun r : ℝ => ψ (y + r • e2 0)) (dh (y 0) * χ (y 1)) 0 := by
        have heq : (fun r : ℝ => ψ (y + r • e2 0)) = fun r => h (y 0 + r) * χ (y 1) := by
          funext r; dsimp [ψ]; simp [e2]
        rw [heq]
        have hadd : HasDerivAt (fun r : ℝ => y 0 + r) 1 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).const_add (y 0)
        have hd0 : HasDerivAt h (dh (y 0)) (y 0 + (0 : ℝ)) := by simpa using hh_deriv (y 0)
        have hcomp := HasDerivAt.comp (h₂ := h) (h := fun r : ℝ => y 0 + r) 0 hd0 hadd
        simpa [Function.comp_def] using hcomp.mul_const (χ (y 1))
      exact h1'.unique h2'
    have hp1 : fderiv ℝ ψ y (e2 1) = h (y 0) * deriv χ (y 1) := by
      have h1' : HasDerivAt (fun r : ℝ => ψ (y + r • e2 1)) (fderiv ℝ ψ y (e2 1)) 0 := by
        have hl : HasDerivAt (fun r : ℝ => y + r • e2 1) (e2 1) 0 := by
          simpa using (((hasDerivAt_id (0 : ℝ)).smul_const (e2 1)).const_add y)
        have hd := (hψ_c1.differentiable one_ne_zero (y + (0 : ℝ) • e2 1)).hasFDerivAt.comp_hasDerivAt 0 hl
        rw [zero_smul, add_zero] at hd; exact hd
      have h2' : HasDerivAt (fun r : ℝ => ψ (y + r • e2 1)) (h (y 0) * deriv χ (y 1)) 0 := by
        have heq : (fun r : ℝ => ψ (y + r • e2 1)) = fun r => h (y 0) * χ (y 1 + r) := by
          funext r; dsimp [ψ]; simp [e2]
        rw [heq]
        have hadd : HasDerivAt (fun r : ℝ => y 1 + r) 1 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).const_add (y 1)
        have hd0 : HasDerivAt χ (deriv χ (y 1)) (y 1 + (0 : ℝ)) := by
          simpa using (hχ_c1.differentiable one_ne_zero (y 1)).hasDerivAt
        have hcomp := HasDerivAt.comp (h₂ := χ) (h := fun r : ℝ => y 1 + r) 0 hd0 hadd
        simpa [Function.comp_def] using hcomp.const_mul (h (y 0))
      exact h1'.unique h2'
    rw [hnorm2, hp0, hp1]; ring
  have hF_int : Integrable (fun y : Plane => ‖∇ ψ y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (ψ y) ^ 2) := by
    have hcg : Continuous (∇ ψ) :=
      (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hψ_c1.continuous_fderiv one_ne_zero)
    have hcomp_g : HasCompactSupport (∇ ψ) := by
      apply hψc.mono'; intro y hy; apply support_fderiv_subset ℝ
      intro h0; exact hy (by simp [gradient, h0])
    have hcont : Continuous (fun y : Plane => ‖∇ ψ y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (ψ y) ^ 2) :=
      (hcg.norm.pow 2).add (((continuous_const.mul (hv.regular.continuous.pow 2)).sub
        continuous_const).mul (hψ_c1.continuous.pow 2))
    refine hcont.integrable_of_hasCompactSupport ?_
    apply HasCompactSupport.of_support_subset_isCompact (hcomp_g.union hψc)
    intro y hy; by_contra hn
    have h1' : ∇ ψ y = 0 := by by_contra h0; exact hn (Or.inl (subset_closure h0))
    have h2' : ψ y = 0 := by by_contra h0; exact hn (Or.inr (subset_closure h0))
    exact hy (by change ‖∇ ψ y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (ψ y) ^ 2 = 0; rw [h1', h2']; simp)
  rw [integral_plane_eq_prod hF_int] at hst
  have hpt_prod (s t : ℝ) :
      ‖∇ ψ (s • e2 0 + t • e2 1)‖ ^ 2 + (3 * (v (s • e2 0 + t • e2 1)) ^ 2 - 1) * (ψ (s • e2 0 + t • e2 1)) ^ 2 =
      ((dh s) ^ 2 + (3 * (g s) ^ 2 - 1) * (h s) ^ 2) * (χ t) ^ 2 + (h s) ^ 2 * (deriv χ t) ^ 2 := by
    rw [hgrad_ψ (s • e2 0 + t • e2 1)]
    have hc0' : (s • e2 0 + t • e2 1) 0 = s := by simp [e2]
    have hc1' : (s • e2 0 + t • e2 1) 1 = t := by simp [e2]
    dsimp only [ψ]; rw [hc0', hc1']
    by_cases hs : s ∈ Set.Ioo (a - δ) (b + δ)
    · rw [hstrip s hs t]; ring
    · have hh0 : h s = 0 := by
        rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hs
        rcases hs with hle | hge
        · exact if_pos (by linarith)
        · have hr0 : ¬ s ≤ x₀ := by linarith
          have hr1 : ¬ s ≤ a + ε := by linarith
          have hr2 : ¬ s ≤ b - ε := by linarith
          have hr3 : ¬ s ≤ x₁ := by linarith
          simp [h, hr0, hr1, hr2, hr3]
      rw [hh0]; ring
  simp_rw [hpt_prod] at hst
  have hχ2_int : Integrable (fun t : ℝ => (χ t) ^ 2) :=
    (hχ_c1.continuous.pow 2).integrable_of_hasCompactSupport
      (by apply hχc.mono'; intro t ht; apply subset_closure; intro h0
          exact ht (by change (χ t) ^ 2 = 0; rw [h0]; simp))
  have hχd2_int : Integrable (fun t : ℝ => (deriv χ t) ^ 2) :=
    ((hχ_c1.continuous_deriv le_rfl).pow 2).integrable_of_hasCompactSupport
      (by apply hχc.deriv.mono'; intro t ht; apply subset_closure; intro h0
          exact ht (by change (deriv χ t) ^ 2 = 0; rw [h0]; simp))
  have hinner (s : ℝ) :
      (∫ t : ℝ, (((dh s) ^ 2 + (3 * (g s) ^ 2 - 1) * (h s) ^ 2) * (χ t) ^ 2 +
        (h s) ^ 2 * (deriv χ t) ^ 2)) =
      ((dh s) ^ 2 + (3 * (g s) ^ 2 - 1) * (h s) ^ 2) * (∫ t : ℝ, (χ t) ^ 2) +
      (h s) ^ 2 * (∫ t : ℝ, (deriv χ t) ^ 2) := by
    rw [integral_add (hχ2_int.const_mul _) (hχd2_int.const_mul _),
      integral_const_mul, integral_const_mul]
  simp_rw [hinner] at hst
  have h1d_int1 : Integrable (fun s : ℝ => (dh s) ^ 2 + (3 * (g s) ^ 2 - 1) * (h s) ^ 2) := by
    have hdh_supp : HasCompactSupport dh := by
      have heq : deriv h = dh := funext fun s => (hh_deriv s).deriv
      rw [← heq]; exact hh_supp.deriv
    refine ((hdh_cont.pow 2).add (((continuous_const.mul (hg_c2.continuous.pow 2)).sub
      continuous_const).mul (hh_c1.continuous.pow 2))).integrable_of_hasCompactSupport ?_
    apply HasCompactSupport.of_support_subset_isCompact (hdh_supp.union hh_supp)
    intro s hs; by_contra hn
    have h1' : dh s = 0 := by by_contra h0; exact hn (Or.inl (subset_closure h0))
    have h2' : h s = 0 := by by_contra h0; exact hn (Or.inr (subset_closure h0))
    exact hs (by change (dh s) ^ 2 + (3 * (g s) ^ 2 - 1) * (h s) ^ 2 = 0; rw [h1', h2']; simp)
  have h1d_int2 : Integrable (fun s : ℝ => (h s) ^ 2) :=
    (hh_c1.continuous.pow 2).integrable_of_hasCompactSupport
      (by apply hh_supp.mono'; intro s hs; apply subset_closure; intro h0
          exact hs (by change (h s) ^ 2 = 0; rw [h0]; simp))
  rw [integral_add (h1d_int1.mul_const _) (h1d_int2.mul_const _),
    integral_mul_const, integral_mul_const] at hst
  obtain ⟨hχ_ge, hχd_le⟩ := hMχ_bd L hL1
  have h1' : I * (∫ t : ℝ, (χ t) ^ 2) ≤ I * (2 * L) := by nlinarith
  have h2' : J * (∫ t : ℝ, (deriv χ t) ^ 2) ≤ J * (4 * Mχ ^ 2 / L) :=
    mul_le_mul_of_nonneg_left hχd_le hJ0
  have hL_big : 2 * Mχ ^ 2 * J / (-I) < L := by
    have : 2 * Mχ ^ 2 * J / (-I) + 1 ≤ L := le_max_right _ _
    linarith
  have hpos_negI : 0 < -I := by linarith
  have h3' : 4 * Mχ ^ 2 * J < 2 * L ^ 2 * (-I) := by
    have hmul : 2 * Mχ ^ 2 * J < L * (-I) := (div_lt_iff₀ hpos_negI).mp hL_big
    have hLsq : L ≤ L ^ 2 := by nlinarith
    have hLsqI : L * (-I) ≤ L ^ 2 * (-I) := mul_le_mul_of_nonneg_right hLsq hpos_negI.le
    linarith
  have h4' : J * (4 * Mχ ^ 2 / L) + I * (2 * L) < 0 := by
    have hmul : J * (4 * Mχ ^ 2 / L) + I * (2 * L) =
        (4 * Mχ ^ 2 * J - 2 * L ^ 2 * (-I)) / L := by
      field_simp [hL0.ne']; ring
    rw [hmul]
    exact div_neg_of_neg_of_pos (by linarith) hL0
  linarith

private theorem neg_solution2 {v : Plane → ℝ}
    (hv : DeGiorgi.IsBoundedSolution v)
    (hcol : ∀ y : Plane,
      part2 v 0 y * part22 v 1 0 y - part2 v 1 y * part22 v 0 0 y = 0 ∧
      part2 v 0 y * part22 v 1 1 y - part2 v 1 y * part22 v 0 1 y = 0) :
    let w := fun y : Plane => -v y
    DeGiorgi.IsBoundedSolution w ∧
    (∀ i y, part2 w i y = -part2 v i y) ∧
    (∀ i j y, part22 w i j y = -part22 v i j y) ∧
    (∀ y : Plane,
      part2 w 0 y * part22 w 1 0 y - part2 w 1 y * part22 w 0 0 y = 0 ∧
      part2 w 0 y * part22 w 1 1 y - part2 w 1 y * part22 w 0 1 y = 0) := by
  intro w
  have hw_c2 : ContDiff ℝ 2 w := hv.regular.neg
  have hw_p (i : Fin 2) (y : Plane) : part2 w i y = -part2 v i y := by
    unfold part2
    have hfd := ((hv.regular.differentiable (by norm_num) y).hasFDerivAt.neg).fderiv
    change fderiv ℝ (-v) y (e2 i) = _
    rw [hfd]; simp
  have hw_p2 (i j : Fin 2) (y : Plane) : part22 w i j y = -part22 v i j y := by
    unfold part22
    have heq : part2 w i = -part2 v i := funext (hw_p i)
    rw [heq]
    have hpi : ContDiff ℝ 1 (part2 v i) :=
      (hv.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hfd := ((hpi.differentiable one_ne_zero y).hasFDerivAt.neg).fderiv
    rw [hfd]; simp
  have hw_lap (y : Plane) : (Δ w) y = -(Δ v) y := by
    let ob := EuclideanSpace.basisFun (Fin 2) ℝ
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis w ob,
      laplacian_eq_iteratedFDeriv_orthonormalBasis v ob, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hbi : ob i = e2 i := EuclideanSpace.basisFun_apply (Fin 2) ℝ i
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hbi]
    have h1 (f : Plane → ℝ) (hf : ContDiff ℝ 2 f) :
        (fderiv ℝ (fderiv ℝ f) y (e2 i)) (e2 i) = part22 f i i y := by
      unfold part22 part2
      rw [fderiv_clm_apply ((hf.fderiv_right (by norm_num)).differentiable one_ne_zero y)
        (differentiableAt_const (e2 i))]; simp
    rw [h1 w hw_c2, h1 v hv.regular, hw_p2 i i y]
  have hw_sol : DeGiorgi.IsBoundedSolution w := by
    obtain ⟨M, hM⟩ := hv.bounded
    refine ⟨hw_c2, ⟨M, fun y => by simpa [w] using hM y⟩, fun y => ?_⟩
    rw [hw_lap y]
    have h := hv.solution y
    dsimp [w]
    linarith [show (-v y) ^ 3 = -(v y) ^ 3 by ring]
  have hw_col (y : Plane) :
      part2 w 0 y * part22 w 1 0 y - part2 w 1 y * part22 w 0 0 y = 0 ∧
      part2 w 0 y * part22 w 1 1 y - part2 w 1 y * part22 w 0 1 y = 0 := by
    rw [hw_p 0 y, hw_p 1 y, hw_p2 1 0 y, hw_p2 0 0 y, hw_p2 1 1 y, hw_p2 0 1 y]
    have hc := hcol y
    constructor <;> linarith
  exact ⟨hw_sol, hw_p, hw_p2, hw_col⟩

private theorem contra_finite_ab {v' : Plane → ℝ}
    (hv' : DeGiorgi.IsBoundedSolution v')
    (hv'1 : ∀ y, |v' y| ≤ 1)
    (hv'_stab : ∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      0 ≤ ∫ y : Plane, (‖∇ ψ y‖ ^ 2 + (3 * (v' y) ^ 2 - 1) * (ψ y) ^ 2))
    (hcol : ∀ y : Plane,
      part2 v' 0 y * part22 v' 1 0 y - part2 v' 1 y * part22 v' 0 0 y = 0 ∧
      part2 v' 0 y * part22 v' 1 1 y - part2 v' 1 y * part22 v' 0 1 y = 0)
    (t₀ : ℝ)
    {g : ℝ → ℝ} (hg_def : ∀ s, g s = v' (s • e2 0 + t₀ • e2 1))
    (hg_c2 : ContDiff ℝ 2 g)
    (hdg_eq : ∀ s, deriv g s = part2 v' 0 (s • e2 0 + t₀ • e2 1))
    (hdg_deriv : ∀ s, HasDerivAt (deriv g) (part22 v' 0 0 (s • e2 0 + t₀ • e2 1)) s)
    (hddg_eq : ∀ s, deriv (deriv g) s = part22 v' 0 0 (s • e2 0 + t₀ • e2 1))
    (hode_of_strip : ∀ s, (∀ t : ℝ, part2 v' 1 (s • e2 0 + t • e2 1) = 0) →
      deriv (deriv g) s = (g s) ^ 3 - g s)
    {a b C0 : ℝ} (hab : a < b) (hC0_gt : -(1 / 2 : ℝ) < C0) (hC0_neg : C0 < 0)
    (hgp_ab : ∀ s ∈ Set.Ioo a b, 0 < deriv g s)
    (hstrip_ab : ∀ s ∈ Set.Ioo a b, ∀ t : ℝ,
      v' (s • e2 0 + t • e2 1) = g s ∧ part2 v' 1 (s • e2 0 + t • e2 1) = 0)
    (hE1_ab : ∀ s ∈ Set.Ioo a b, (deriv g s) ^ 2 - (1 / 2) * (1 - (g s) ^ 2) ^ 2 = C0)
    (hdga : deriv g a = 0) (hdgb : deriv g b = 0) : False := by
  have hba : 0 < b - a := by linarith
  have hstep_pos (n : ℕ) : 0 < (b - a) / ((n : ℝ) + 2) := by positivity
  have hstep_lt (n : ℕ) : (b - a) / ((n : ℝ) + 2) < b - a := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hstep_tend : Tendsto (fun n : ℕ => (b - a) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hmem_a (n : ℕ) : a + (b - a) / ((n : ℝ) + 2) ∈ Set.Ioo a b :=
    ⟨by linarith [hstep_pos n], by linarith [hstep_lt n]⟩
  have hmem_b (n : ℕ) : b - (b - a) / ((n : ℝ) + 2) ∈ Set.Ioo a b :=
    ⟨by linarith [hstep_lt n], by linarith [hstep_pos n]⟩
  let E1 : ℝ → ℝ := fun s => (deriv g s) ^ 2 - (1 / 2) * (1 - (g s) ^ 2) ^ 2
  have hE1_cont : Continuous E1 :=
    ((hg_c2.continuous_deriv (by norm_num)).pow 2).sub
      (((continuous_const.sub (hg_c2.continuous.pow 2)).pow 2).const_mul (1 / 2 : ℝ))
  have hE1_a : E1 a = C0 := by
    have hlim : Tendsto (fun n : ℕ => E1 (a + (b - a) / ((n : ℝ) + 2))) atTop (𝓝 (E1 a)) :=
      hE1_cont.continuousAt.tendsto.comp (by simpa using tendsto_const_nhds.add hstep_tend)
    have heq : (fun n : ℕ => E1 (a + (b - a) / ((n : ℝ) + 2))) = fun _ => C0 :=
      funext fun n => hE1_ab _ (hmem_a n)
    rw [heq] at hlim; exact tendsto_nhds_unique hlim tendsto_const_nhds
  have hE1_b : E1 b = C0 := by
    have hlim : Tendsto (fun n : ℕ => E1 (b - (b - a) / ((n : ℝ) + 2))) atTop (𝓝 (E1 b)) :=
      hE1_cont.continuousAt.tendsto.comp (by simpa using tendsto_const_nhds.sub hstep_tend)
    have heq : (fun n : ℕ => E1 (b - (b - a) / ((n : ℝ) + 2))) = fun _ => C0 :=
      funext fun n => hE1_ab _ (hmem_b n)
    rw [heq] at hlim; exact tendsto_nhds_unique hlim tendsto_const_nhds
  have hpc1 : ContDiff ℝ 1 (part2 v' 1) :=
    (hv'.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hp1_a (t : ℝ) : part2 v' 1 (a • e2 0 + t • e2 1) = 0 := by
    have hlim : Tendsto (fun n : ℕ => part2 v' 1 ((a + (b - a) / ((n : ℝ) + 2)) • e2 0 + t • e2 1))
        atTop (𝓝 (part2 v' 1 (a • e2 0 + t • e2 1))) :=
      hpc1.continuous.continuousAt.tendsto.comp (by
        have h1' : Tendsto (fun n : ℕ => a + (b - a) / ((n : ℝ) + 2)) atTop (𝓝 a) := by
          simpa using tendsto_const_nhds.add hstep_tend
        exact (h1'.smul tendsto_const_nhds).add tendsto_const_nhds)
    have heq : (fun n : ℕ => part2 v' 1 ((a + (b - a) / ((n : ℝ) + 2)) • e2 0 + t • e2 1)) = fun _ => 0 :=
      funext fun n => (hstrip_ab _ (hmem_a n) t).2
    rw [heq] at hlim; exact tendsto_nhds_unique hlim tendsto_const_nhds
  have hp1_b (t : ℝ) : part2 v' 1 (b • e2 0 + t • e2 1) = 0 := by
    have hlim : Tendsto (fun n : ℕ => part2 v' 1 ((b - (b - a) / ((n : ℝ) + 2)) • e2 0 + t • e2 1))
        atTop (𝓝 (part2 v' 1 (b • e2 0 + t • e2 1))) :=
      hpc1.continuous.continuousAt.tendsto.comp (by
        have h1' : Tendsto (fun n : ℕ => b - (b - a) / ((n : ℝ) + 2)) atTop (𝓝 b) := by
          simpa using tendsto_const_nhds.sub hstep_tend
        exact (h1'.smul tendsto_const_nhds).add tendsto_const_nhds)
    have heq : (fun n : ℕ => part2 v' 1 ((b - (b - a) / ((n : ℝ) + 2)) • e2 0 + t • e2 1)) = fun _ => 0 :=
      funext fun n => (hstrip_ab _ (hmem_b n) t).2
    rw [heq] at hlim; exact tendsto_nhds_unique hlim tendsto_const_nhds
  have hode_a : deriv (deriv g) a = (g a) ^ 3 - g a := hode_of_strip a hp1_a
  have hode_b : deriv (deriv g) b = (g b) ^ 3 - g b := hode_of_strip b hp1_b
  have hddg_a_nn : 0 ≤ deriv (deriv g) a := by
    have hlim : Tendsto (fun n : ℕ => (deriv g (a + (b - a) / ((n : ℝ) + 2)) - deriv g a) /
        ((b - a) / ((n : ℝ) + 2))) atTop (𝓝 (deriv (deriv g) a)) := by
      have hd := (hdg_deriv a).tendsto_slope_zero_right
      rw [← hddg_eq a] at hd
      have h0 : Tendsto (fun n : ℕ => (b - a) / ((n : ℝ) + 2)) atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.mpr ⟨hstep_tend, Eventually.of_forall hstep_pos⟩
      simpa [Function.comp_def, smul_eq_mul, inv_mul_eq_div] using hd.comp h0
    exact ge_of_tendsto hlim (Eventually.of_forall fun n => by
      rw [hdga, sub_zero]
      exact div_nonneg (hgp_ab _ (hmem_a n)).le (hstep_pos n).le)
  have hddg_b_np : deriv (deriv g) b ≤ 0 := by
    have hlim : Tendsto (fun n : ℕ => (deriv g (b + (-(b - a) / ((n : ℝ) + 2))) - deriv g b) /
        (-(b - a) / ((n : ℝ) + 2))) atTop (𝓝 (deriv (deriv g) b)) := by
      have hd := (hdg_deriv b).tendsto_slope_zero_left
      rw [← hddg_eq b] at hd
      have hneg_tend : Tendsto (fun n : ℕ => -(b - a) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have h := hstep_tend.neg
        rw [neg_zero] at h
        exact h.congr fun n => by ring
      have h0 : Tendsto (fun n : ℕ => -(b - a) / ((n : ℝ) + 2)) atTop (𝓝[<] 0) :=
        tendsto_nhdsWithin_iff.mpr ⟨hneg_tend,
          Eventually.of_forall fun n => div_neg_of_neg_of_pos (by linarith : -(b - a) < 0)
            (by positivity : (0 : ℝ) < (n : ℝ) + 2)⟩
      simpa [Function.comp_def, smul_eq_mul, inv_mul_eq_div] using hd.comp h0
    exact le_of_tendsto hlim (Eventually.of_forall fun n => by
      rw [hdgb, sub_zero, show b + -(b - a) / ((n : ℝ) + 2) = b - (b - a) / ((n : ℝ) + 2) by ring]
      exact div_nonpos_of_nonneg_of_nonpos (hgp_ab _ (hmem_b n)).le
        (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)))
  have hga_sq : 0 < (g a) ^ 2 ∧ (g a) ^ 2 < 1 := by
    dsimp [E1] at hE1_a; rw [hdga] at hE1_a
    constructor
    · by_contra! hle; have h0 : (g a) ^ 2 = 0 := le_antisymm hle (sq_nonneg _); rw [h0] at hE1_a; linarith
    · have h1a : (g a) ^ 2 ≤ 1 := by
        have := sq_le_sq.mpr (show |g a| ≤ |(1 : ℝ)| by rw [hg_def]; simpa using hv'1 (a • e2 0 + t₀ • e2 1))
        simpa using this
      by_contra! hge; have h1' : (g a) ^ 2 = 1 := le_antisymm h1a hge; rw [h1'] at hE1_a; linarith
  have hgb_sq : 0 < (g b) ^ 2 ∧ (g b) ^ 2 < 1 := by
    dsimp [E1] at hE1_b; rw [hdgb] at hE1_b
    constructor
    · by_contra! hle; have h0 : (g b) ^ 2 = 0 := le_antisymm hle (sq_nonneg _); rw [h0] at hE1_b; linarith
    · have h1b : (g b) ^ 2 ≤ 1 := by
        have := sq_le_sq.mpr (show |g b| ≤ |(1 : ℝ)| by rw [hg_def]; simpa using hv'1 (b • e2 0 + t₀ • e2 1))
        simpa using this
      by_contra! hge; have h1' : (g b) ^ 2 = 1 := le_antisymm h1b hge; rw [h1'] at hE1_b; linarith
  have hddg_a_pos : 0 < deriv (deriv g) a := by
    have hne : g a ≠ 0 := fun h => by rw [h] at hga_sq; norm_num at hga_sq
    have : (g a) ^ 3 - g a = g a * ((g a) ^ 2 - 1) := by ring
    have hnz : deriv (deriv g) a ≠ 0 := by rw [hode_a, this]; exact mul_ne_zero hne (by linarith [hga_sq.2])
    exact lt_of_le_of_ne hddg_a_nn hnz.symm
  have hddg_b_neg : deriv (deriv g) b < 0 := by
    have hne : g b ≠ 0 := fun h => by rw [h] at hgb_sq; norm_num at hgb_sq
    have : (g b) ^ 3 - g b = g b * ((g b) ^ 2 - 1) := by ring
    have hnz : deriv (deriv g) b ≠ 0 := by rw [hode_b, this]; exact mul_ne_zero hne (by linarith [hgb_sq.2])
    exact lt_of_le_of_ne hddg_b_np hnz
  have hgp_c1 : ContDiff ℝ 1 (deriv g) := by
    have h := hg_c2
    rw [show (2 : WithTop ℕ∞) = (1 : ℕ) + 1 by norm_num, contDiff_succ_iff_deriv] at h
    exact h.2.2
  have hddg_cont : Continuous (deriv (deriv g)) := hgp_c1.continuous_deriv le_rfl
  obtain ⟨δ₁, hδ₁, hda_pos⟩ := Metric.continuousAt_iff.mp (hddg_cont.continuousAt (x := a))
    (deriv (deriv g) a / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, hdb_neg⟩ := Metric.continuousAt_iff.mp (hddg_cont.continuousAt (x := b))
    (-deriv (deriv g) b / 2) (by linarith)
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hdg_neg_left : ∀ s ∈ Set.Ioo (a - δ) a, deriv g s < 0 := by
    intro s hs
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (deriv g) (fun r => deriv (deriv g) r) hs.2
      (fun r _ => hgp_c1.continuous.continuousAt.continuousWithinAt)
      (fun r _ => by rw [hddg_eq r]; exact hdg_deriv r)
    have hcd : dist c a < δ₁ := by
      rw [Real.dist_eq, abs_of_neg (by linarith [hc.2])]; linarith [hc.1, hs.1, min_le_left δ₁ δ₂]
    have hcpos : 0 < deriv (deriv g) c := by
      have := hda_pos hcd; rw [Real.dist_eq, abs_lt] at this; linarith
    rw [hslope, hdga, zero_sub] at hcpos
    have := (div_pos_iff_of_pos_right (by linarith [hs.2] : 0 < a - s)).mp hcpos
    linarith
  have hdg_neg_right : ∀ s ∈ Set.Ioo b (b + δ), deriv g s < 0 := by
    intro s hs
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (deriv g) (fun r => deriv (deriv g) r) hs.1
      (fun r _ => hgp_c1.continuous.continuousAt.continuousWithinAt)
      (fun r _ => by rw [hddg_eq r]; exact hdg_deriv r)
    have hcd : dist c b < δ₂ := by
      rw [Real.dist_eq, abs_of_pos (by linarith [hc.1])]; linarith [hc.2, hs.2, min_le_right δ₁ δ₂]
    have hcneg : deriv (deriv g) c < 0 := by
      have := hdb_neg hcd; rw [Real.dist_eq, abs_lt] at this; linarith
    rw [hslope, hdgb, sub_zero] at hcneg
    have := (div_neg_iff.mp hcneg).resolve_left (fun h => by linarith [hs.1, h.2])
    exact this.1
  have hp10_a : part22 v' 1 0 (a • e2 0 + t₀ • e2 1) = 0 := by
    have hcont : Continuous (fun s : ℝ => part22 v' 1 0 (s • e2 0 + t₀ • e2 1)) :=
      ((hpc1.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
        ((continuous_id.smul (continuous_const (y := e2 0))).add (continuous_const (y := t₀ • e2 1)))
    have hlim : Tendsto (fun n : ℕ => part22 v' 1 0 ((a + (b - a) / ((n : ℝ) + 2)) • e2 0 + t₀ • e2 1))
        atTop (𝓝 (part22 v' 1 0 (a • e2 0 + t₀ • e2 1))) :=
      hcont.continuousAt.tendsto.comp (by simpa using tendsto_const_nhds.add hstep_tend)
    have heq : (fun n : ℕ => part22 v' 1 0 ((a + (b - a) / ((n : ℝ) + 2)) • e2 0 + t₀ • e2 1)) = fun _ => 0 := by
      funext n
      let sn := a + (b - a) / ((n : ℝ) + 2)
      have hd : HasDerivAt (fun r => part2 v' 1 (r • e2 0 + t₀ • e2 1))
          (part22 v' 1 0 (sn • e2 0 + t₀ • e2 1)) sn := by
        have hl : HasDerivAt (fun r : ℝ => r • e2 0 + t₀ • e2 1) (e2 0) sn := by
          simpa using ((hasDerivAt_id sn).smul_const (e2 0)).add_const (t₀ • e2 1)
        exact (hpc1.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt sn hl
      have hev : (fun r => part2 v' 1 (r • e2 0 + t₀ • e2 1)) =ᶠ[𝓝 sn] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Ioo.mem_nhds (hmem_a n)] with r hr
        exact (hstrip_ab r hr t₀).2
      exact (hd.congr_of_eventuallyEq hev.symm).unique (hasDerivAt_const sn (0 : ℝ))
    rw [heq] at hlim; exact tendsto_nhds_unique hlim tendsto_const_nhds
  have hp10_b : part22 v' 1 0 (b • e2 0 + t₀ • e2 1) = 0 := by
    have hcont : Continuous (fun s : ℝ => part22 v' 1 0 (s • e2 0 + t₀ • e2 1)) :=
      ((hpc1.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
        ((continuous_id.smul (continuous_const (y := e2 0))).add (continuous_const (y := t₀ • e2 1)))
    have hlim : Tendsto (fun n : ℕ => part22 v' 1 0 ((b - (b - a) / ((n : ℝ) + 2)) • e2 0 + t₀ • e2 1))
        atTop (𝓝 (part22 v' 1 0 (b • e2 0 + t₀ • e2 1))) :=
      hcont.continuousAt.tendsto.comp (by simpa using tendsto_const_nhds.sub hstep_tend)
    have heq : (fun n : ℕ => part22 v' 1 0 ((b - (b - a) / ((n : ℝ) + 2)) • e2 0 + t₀ • e2 1)) = fun _ => 0 := by
      funext n
      let sn := b - (b - a) / ((n : ℝ) + 2)
      have hd : HasDerivAt (fun r => part2 v' 1 (r • e2 0 + t₀ • e2 1))
          (part22 v' 1 0 (sn • e2 0 + t₀ • e2 1)) sn := by
        have hl : HasDerivAt (fun r : ℝ => r • e2 0 + t₀ • e2 1) (e2 0) sn := by
          simpa using ((hasDerivAt_id sn).smul_const (e2 0)).add_const (t₀ • e2 1)
        exact (hpc1.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt sn hl
      have hev : (fun r => part2 v' 1 (r • e2 0 + t₀ • e2 1)) =ᶠ[𝓝 sn] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Ioo.mem_nhds (hmem_b n)] with r hr
        exact (hstrip_ab r hr t₀).2
      exact (hd.congr_of_eventuallyEq hev.symm).unique (hasDerivAt_const sn (0 : ℝ))
    rw [heq] at hlim; exact tendsto_nhds_unique hlim tendsto_const_nhds
  let qh : ℝ → ℝ := fun r => part2 v' 1 (r • e2 0 + t₀ • e2 1) / deriv g r
  have hqh_const (s₁ s₂ : ℝ) (hne : ∀ r ∈ Set.uIcc s₁ s₂, deriv g r ≠ 0) : qh s₂ = qh s₁ := by
    apply eq_of_hasDerivAt_zero_on_uIcc
    intro r hr
    have hd1 : HasDerivAt (fun τ => part2 v' 1 (τ • e2 0 + t₀ • e2 1))
        (part22 v' 1 0 (r • e2 0 + t₀ • e2 1)) r := by
      have hl : HasDerivAt (fun τ : ℝ => τ • e2 0 + t₀ • e2 1) (e2 0) r := by
        simpa using ((hasDerivAt_id r).smul_const (e2 0)).add_const (t₀ • e2 1)
      exact (hpc1.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt r hl
    have hd0 := hdg_deriv r
    have hdiv : HasDerivAt qh
        ((part22 v' 1 0 (r • e2 0 + t₀ • e2 1) * deriv g r -
          part2 v' 1 (r • e2 0 + t₀ • e2 1) * part22 v' 0 0 (r • e2 0 + t₀ • e2 1)) /
          (deriv g r) ^ 2) r := hd1.div hd0 (hne r hr)
    have hnum0 : part22 v' 1 0 (r • e2 0 + t₀ • e2 1) * deriv g r -
        part2 v' 1 (r • e2 0 + t₀ • e2 1) * part22 v' 0 0 (r • e2 0 + t₀ • e2 1) = 0 := by
      rw [hdg_eq r]; have := (hcol (r • e2 0 + t₀ • e2 1)).1; linarith
    rwa [hnum0, zero_div] at hdiv
  have hp1_left (s : ℝ) (hs : s ∈ Set.Ioo (a - δ) a) : part2 v' 1 (s • e2 0 + t₀ • e2 1) = 0 := by
    have has_pos : 0 < a - s := by linarith [hs.2]
    have hlim : Tendsto (fun n : ℕ => qh (a - (a - s) / ((n : ℝ) + 2))) atTop (𝓝 0) := by
      have h1d : HasDerivAt (fun r => part2 v' 1 (r • e2 0 + t₀ • e2 1)) 0 a := by
        rw [← hp10_a]
        have hl : HasDerivAt (fun r : ℝ => r • e2 0 + t₀ • e2 1) (e2 0) a := by
          simpa using ((hasDerivAt_id a).smul_const (e2 0)).add_const (t₀ • e2 1)
        exact (hpc1.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt a hl
      have h0d : HasDerivAt (deriv g) (deriv (deriv g) a) a := by rw [hddg_eq a]; exact hdg_deriv a
      have ht0 : Tendsto (fun n : ℕ => -(a - s) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        (tendsto_const_nhds (x := -(a - s))).div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have ht : Tendsto (fun n : ℕ => -(a - s) / ((n : ℝ) + 2)) atTop (𝓝[<] 0) :=
        tendsto_nhdsWithin_iff.mpr ⟨ht0,
          Eventually.of_forall fun n => div_neg_of_neg_of_pos (by linarith : -(a - s) < 0)
            (by positivity : (0 : ℝ) < (n : ℝ) + 2)⟩
      have hnum := h1d.tendsto_slope_zero_left.comp ht
      have hden := h0d.tendsto_slope_zero_left.comp ht
      have hq := hnum.div hden hddg_a_pos.ne'
      rw [zero_div] at hq
      refine hq.congr fun n => ?_
      have htnz : (-(a - s) / ((n : ℝ) + 2)) ≠ 0 :=
        (div_neg_of_neg_of_pos (by linarith : -(a - s) < 0) (by positivity : (0 : ℝ) < (n : ℝ) + 2)).ne
      dsimp [qh]
      have hpt_eq : a + -(a - s) / ((n : ℝ) + 2) = a - (a - s) / ((n : ℝ) + 2) := by ring
      simp only [hpt_eq, hp1_a t₀, hdga, sub_zero]
      field_simp [htnz]
    have hconst_n : (fun n : ℕ => qh (a - (a - s) / ((n : ℝ) + 2))) = fun _ => qh s := by
      funext n
      apply hqh_const s (a - (a - s) / ((n : ℝ) + 2))
      intro r hr
      have hs_le : s ≤ a - (a - s) / ((n : ℝ) + 2) := by
        have hlt : (a - s) / ((n : ℝ) + 2) < a - s := by
          rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
        linarith
      rw [Set.uIcc_of_le hs_le] at hr
      have hstep : 0 < (a - s) / ((n : ℝ) + 2) := by positivity
      have hr_in : r ∈ Set.Ioo (a - δ) a := ⟨by linarith [hs.1, hr.1], by linarith [hr.2]⟩
      exact (hdg_neg_left r hr_in).ne
    rw [hconst_n] at hlim
    have hqs0 : qh s = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
    exact (div_eq_zero_iff.mp hqs0).resolve_right (hdg_neg_left s hs).ne
  have hp1_right (s : ℝ) (hs : s ∈ Set.Ioo b (b + δ)) : part2 v' 1 (s • e2 0 + t₀ • e2 1) = 0 := by
    have hsb_pos : 0 < s - b := by linarith [hs.1]
    have hlim : Tendsto (fun n : ℕ => qh (b + (s - b) / ((n : ℝ) + 2))) atTop (𝓝 0) := by
      have h1d : HasDerivAt (fun r => part2 v' 1 (r • e2 0 + t₀ • e2 1)) 0 b := by
        rw [← hp10_b]
        have hl : HasDerivAt (fun r : ℝ => r • e2 0 + t₀ • e2 1) (e2 0) b := by
          simpa using ((hasDerivAt_id b).smul_const (e2 0)).add_const (t₀ • e2 1)
        exact (hpc1.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt b hl
      have h0d : HasDerivAt (deriv g) (deriv (deriv g) b) b := by rw [hddg_eq b]; exact hdg_deriv b
      have ht0 : Tendsto (fun n : ℕ => (s - b) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have ht : Tendsto (fun n : ℕ => (s - b) / ((n : ℝ) + 2)) atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.mpr ⟨ht0, Eventually.of_forall fun n =>
          show (0 : ℝ) < (s - b) / ((n : ℝ) + 2) by positivity⟩
      have hnum := h1d.tendsto_slope_zero_right.comp ht
      have hden := h0d.tendsto_slope_zero_right.comp ht
      have hq := hnum.div hden hddg_b_neg.ne
      rw [zero_div] at hq
      refine hq.congr fun n => ?_
      have htnz : ((s - b) / ((n : ℝ) + 2)) ≠ 0 := (by positivity : 0 < (s - b) / ((n : ℝ) + 2)).ne'
      dsimp [qh]
      simp only [hp1_b t₀, hdgb, sub_zero]
      field_simp [htnz]
    have hconst_n : (fun n : ℕ => qh (b + (s - b) / ((n : ℝ) + 2))) = fun _ => qh s := by
      funext n
      apply hqh_const s (b + (s - b) / ((n : ℝ) + 2))
      intro r hr
      have hle_s : b + (s - b) / ((n : ℝ) + 2) ≤ s := by
        have hlt : (s - b) / ((n : ℝ) + 2) < s - b := by
          rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
        linarith
      rw [Set.uIcc_of_ge hle_s] at hr
      have hstep : 0 < (s - b) / ((n : ℝ) + 2) := by positivity
      have hr_in : r ∈ Set.Ioo b (b + δ) := ⟨by linarith [hr.1], by linarith [hs.2, hr.2]⟩
      exact (hdg_neg_right r hr_in).ne
    rw [hconst_n] at hlim
    have hqs0 : qh s = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
    exact (div_eq_zero_iff.mp hqs0).resolve_right (hdg_neg_right s hs).ne
  obtain ⟨hneg_sol, hneg_p, _, hneg_col⟩ := neg_solution2 hv' hcol
  have hstrip_all : ∀ s ∈ Set.Ioo (a - δ) (b + δ), ∀ t : ℝ,
      v' (s • e2 0 + t • e2 1) = g s ∧ part2 v' 1 (s • e2 0 + t • e2 1) = 0 := by
    intro s hs t
    by_cases hlt_a : s < a
    · have hsL : s ∈ Set.Ioo (a - δ) a := ⟨hs.1, hlt_a⟩
      have h := strip_of_pos_part0 hneg_sol hneg_col s t₀
        (by rw [hneg_p 1, hp1_left s hsL, neg_zero]) s
        (fun r hr => by
          have hrs : r = s := by simpa [Set.uIcc_self] using hr
          rw [hrs, hneg_p 0, ← hdg_eq s]; linarith [hdg_neg_left s hsL]) t
      refine ⟨by have h1' := h.1; rw [hg_def s]; linarith,
        by have h2' := h.2.2; rw [hneg_p 1] at h2'; linarith⟩
    · push Not at hlt_a
      by_cases heq_a : s = a
      · rw [heq_a]
        have hv_eq : v' (a • e2 0 + t • e2 1) = g a := by
          have hlim : Tendsto (fun n : ℕ => v' ((a + (b - a) / ((n : ℝ) + 2)) • e2 0 + t • e2 1))
              atTop (𝓝 (v' (a • e2 0 + t • e2 1))) :=
            hv'.regular.continuous.continuousAt.tendsto.comp (by
              have h1' : Tendsto (fun n : ℕ => a + (b - a) / ((n : ℝ) + 2)) atTop (𝓝 a) := by
                simpa using tendsto_const_nhds.add hstep_tend
              exact (h1'.smul tendsto_const_nhds).add tendsto_const_nhds)
          have hlim2 : Tendsto (fun n : ℕ => g (a + (b - a) / ((n : ℝ) + 2))) atTop (𝓝 (g a)) :=
            hg_c2.continuous.continuousAt.tendsto.comp (by simpa using tendsto_const_nhds.add hstep_tend)
          have heq : (fun n : ℕ => v' ((a + (b - a) / ((n : ℝ) + 2)) • e2 0 + t • e2 1)) =
              fun n : ℕ => g (a + (b - a) / ((n : ℝ) + 2)) :=
            funext fun n => (hstrip_ab _ (hmem_a n) t).1
          rw [heq] at hlim; exact tendsto_nhds_unique hlim hlim2
        exact ⟨hv_eq, hp1_a t⟩
      · by_cases hlt_b : s < b
        · exact hstrip_ab s ⟨lt_of_le_of_ne hlt_a (Ne.symm heq_a), hlt_b⟩ t
        · push Not at hlt_b
          by_cases heq_b : s = b
          · rw [heq_b]
            have hv_eq : v' (b • e2 0 + t • e2 1) = g b := by
              have hlim : Tendsto (fun n : ℕ => v' ((b - (b - a) / ((n : ℝ) + 2)) • e2 0 + t • e2 1))
                  atTop (𝓝 (v' (b • e2 0 + t • e2 1))) :=
                hv'.regular.continuous.continuousAt.tendsto.comp (by
                  have h1' : Tendsto (fun n : ℕ => b - (b - a) / ((n : ℝ) + 2)) atTop (𝓝 b) := by
                    simpa using tendsto_const_nhds.sub hstep_tend
                  exact (h1'.smul tendsto_const_nhds).add tendsto_const_nhds)
              have hlim2 : Tendsto (fun n : ℕ => g (b - (b - a) / ((n : ℝ) + 2))) atTop (𝓝 (g b)) :=
                hg_c2.continuous.continuousAt.tendsto.comp (by simpa using tendsto_const_nhds.sub hstep_tend)
              have heq : (fun n : ℕ => v' ((b - (b - a) / ((n : ℝ) + 2)) • e2 0 + t • e2 1)) =
                  fun n : ℕ => g (b - (b - a) / ((n : ℝ) + 2)) :=
                funext fun n => (hstrip_ab _ (hmem_b n) t).1
              rw [heq] at hlim; exact tendsto_nhds_unique hlim hlim2
            exact ⟨hv_eq, hp1_b t⟩
          · have hsR : s ∈ Set.Ioo b (b + δ) := ⟨lt_of_le_of_ne hlt_b (Ne.symm heq_b), hs.2⟩
            have h := strip_of_pos_part0 hneg_sol hneg_col s t₀
              (by rw [hneg_p 1, hp1_right s hsR, neg_zero]) s
              (fun r hr => by
                have hrs : r = s := by simpa [Set.uIcc_self] using hr
                rw [hrs, hneg_p 0, ← hdg_eq s]; linarith [hdg_neg_right s hsR]) t
            refine ⟨by have h1' := h.1; rw [hg_def s]; linarith,
              by have h2' := h.2.2; rw [hneg_p 1] at h2'; linarith⟩
  exact quadratic_cap_contradiction hv' hv'1 hv'_stab hg_c2 hab hδ
    (fun s hs t => (hstrip_all s hs t).1)
    (fun s hs => hode_of_strip s fun t => (hstrip_all s hs t).2)
    hgp_ab hdga hdgb hddg_a_pos hddg_b_neg

private theorem no_pos_inf_of_neg_E1 {g : ℝ → ℝ}
    (hg_c2 : ContDiff ℝ 2 g) (hg_bd : ∀ s, |g s| ≤ 1)
    {s₀ C0 : ℝ} (hC0_gt : -(1 / 2 : ℝ) < C0) (hC0_neg : C0 < 0)
    (hgp : ∀ s, s₀ ≤ s → 0 < deriv g s)
    (hode : ∀ s, s₀ ≤ s → deriv (deriv g) s = (g s) ^ 3 - g s)
    (hE1 : ∀ s, s₀ ≤ s → (deriv g s) ^ 2 - (1 / 2) * (1 - (g s) ^ 2) ^ 2 = C0) : False := by
  have hgp_c1 : ContDiff ℝ 1 (deriv g) := by
    have h := hg_c2
    rw [show (2 : WithTop ℕ∞) = (1 : ℕ) + 1 by norm_num, contDiff_succ_iff_deriv] at h
    exact h.2.2
  have hmono : ∀ s₁ s₂, s₀ ≤ s₁ → s₁ < s₂ → g s₁ < g s₂ := by
    intro s₁ s₂ hs₁ hlt
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g (fun r => deriv g r) hlt
      (fun r _ => hg_c2.continuous.continuousAt.continuousWithinAt)
      (fun r _ => (hg_c2.differentiable (by norm_num) r).hasDerivAt)
    have hpos : 0 < deriv g c := hgp c (by linarith [hc.1])
    rw [hslope] at hpos
    have := (div_pos_iff_of_pos_right (by linarith : 0 < s₂ - s₁)).mp hpos
    linarith
  let S := {x : ℝ | ∃ s, s₀ ≤ s ∧ g s = x}
  have hSne : S.Nonempty := ⟨g s₀, s₀, le_rfl, rfl⟩
  have hSbdd : BddAbove S := ⟨1, fun x ⟨s, _, hx⟩ => by rw [← hx]; exact (abs_le.mp (hg_bd s)).2⟩
  let L := sSup S
  have hL_lim : Tendsto g atTop (𝓝 L) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨x, ⟨s₁, hs₁, rfl⟩, hxgt⟩ := exists_lt_of_lt_csSup hSne (by linarith : L - ε < L)
    refine ⟨s₁, fun s hs => ?_⟩
    rw [Real.dist_eq, abs_lt]
    have hle : g s ≤ L := le_csSup hSbdd ⟨s, hs₁.trans hs, rfl⟩
    have hge : g s₁ ≤ g s := if h : s₁ = s then by rw [h] else (hmono s₁ s hs₁ (lt_of_le_of_ne hs h)).le
    constructor <;> linarith
  have hmv (n : ℕ) : ∃ c ∈ Set.Ioo (s₀ + n) (s₀ + n + 1),
      deriv g c = g (s₀ + n + 1) - g (s₀ + n) := by
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g (fun r => deriv g r) (by linarith : s₀ + n < s₀ + n + 1)
      (fun r _ => hg_c2.continuous.continuousAt.continuousWithinAt)
      (fun r _ => (hg_c2.differentiable (by norm_num) r).hasDerivAt)
    refine ⟨c, hc, ?_⟩
    have hden : s₀ + n + 1 - (s₀ + n) = 1 := by ring
    rw [hden, div_one] at hslope; exact hslope
  let cn : ℕ → ℝ := fun n => Classical.choose (hmv n)
  have hcn_gt (n : ℕ) : s₀ + n < cn n := (Classical.choose_spec (hmv n)).1.1
  have hcn_top : Tendsto cn atTop atTop :=
    tendsto_atTop_mono (fun n => (hcn_gt n).le)
      (tendsto_atTop_add_const_left atTop s₀ tendsto_natCast_atTop_atTop)
  have hdg_zero : Tendsto (fun n => deriv g (cn n)) atTop (𝓝 0) := by
    have heq : (fun n : ℕ => deriv g (cn n)) = fun n : ℕ => g (s₀ + n + 1) - g (s₀ + n) :=
      funext fun n => (Classical.choose_spec (hmv n)).2
    rw [heq]
    have h1' : Tendsto (fun n : ℕ => g (s₀ + n + 1)) atTop (𝓝 L) :=
      hL_lim.comp ((tendsto_atTop_add_const_left atTop s₀ tendsto_natCast_atTop_atTop).atTop_add tendsto_const_nhds)
    have h2' : Tendsto (fun n : ℕ => g (s₀ + n)) atTop (𝓝 L) :=
      hL_lim.comp (tendsto_atTop_add_const_left atTop s₀ tendsto_natCast_atTop_atTop)
    simpa using h1'.sub h2'
  have hE1_lim : Tendsto (fun n => (deriv g (cn n)) ^ 2 - (1 / 2) * (1 - (g (cn n)) ^ 2) ^ 2)
      atTop (𝓝 (-(1 / 2) * (1 - L ^ 2) ^ 2)) := by
    have hg_cn : Tendsto (fun n => g (cn n)) atTop (𝓝 L) := hL_lim.comp hcn_top
    have h := (hdg_zero.pow 2).sub
      ((((tendsto_const_nhds (x := (1 : ℝ))).sub (hg_cn.pow 2)).pow 2).const_mul (1 / 2 : ℝ))
    simpa [Function.comp_def] using h
  have hE1_eq : (fun n => (deriv g (cn n)) ^ 2 - (1 / 2) * (1 - (g (cn n)) ^ 2) ^ 2) = fun _ => C0 :=
    funext fun n => hE1 (cn n) (by linarith [hcn_gt n, Nat.cast_nonneg (α := ℝ) n])
  rw [hE1_eq] at hE1_lim
  have hL_eq : -(1 / 2) * (1 - L ^ 2) ^ 2 = C0 := tendsto_nhds_unique hE1_lim tendsto_const_nhds
  have hL2_lt1 : L ^ 2 < 1 := by
    by_contra! hge
    have hL_le1 : L ≤ 1 := csSup_le hSne fun x ⟨s, _, hx⟩ => by rw [← hx]; exact (abs_le.mp (hg_bd s)).2
    have hL_ge_m1 : -1 ≤ L := le_trans (abs_le.mp (hg_bd s₀)).1 (le_csSup hSbdd ⟨s₀, le_rfl, rfl⟩)
    have hsq1 : L ^ 2 ≤ 1 := by nlinarith
    have : L ^ 2 = 1 := le_antisymm hsq1 hge
    rw [this] at hL_eq; linarith
  have hL2_pos : 0 < L ^ 2 := by
    by_contra! hle
    have : L ^ 2 = 0 := le_antisymm hle (sq_nonneg L)
    rw [this] at hL_eq; linarith
  have hL_ne0 : L ≠ 0 := fun h => by rw [h] at hL2_pos; norm_num at hL2_pos
  have hdd_ne : L ^ 3 - L ≠ 0 := by
    have : L ^ 3 - L = L * (L ^ 2 - 1) := by ring
    rw [this]; exact mul_ne_zero hL_ne0 (by linarith)
  have hdd_lim : Tendsto (fun s => (g s) ^ 3 - g s) atTop (𝓝 (L ^ 3 - L)) :=
    (hL_lim.pow 3).sub hL_lim
  rcases lt_or_gt_of_ne hdd_ne with hneg | hpos
  · obtain ⟨S₁, hS₁⟩ := (Metric.tendsto_atTop.mp hdd_lim) (-(L ^ 3 - L) / 2) (by linarith)
    let S₀ := max s₀ S₁
    have hstep : ∀ s ≥ S₀, deriv (deriv g) s ≤ (L ^ 3 - L) / 2 := by
      intro s hs
      rw [hode s ((le_max_left _ _).trans hs)]
      have hb := hS₁ s ((le_max_right _ _).trans hs)
      rw [Real.dist_eq, abs_lt] at hb; linarith
    let s_big := S₀ + (2 * (deriv g S₀ + 1)) / (-(L ^ 3 - L))
    have hs_big_gt : S₀ < s_big := by
      have hdg0 : 0 < deriv g S₀ := hgp S₀ (le_max_left _ _)
      have hneg' : 0 < -(L ^ 3 - L) := by linarith
      have hdiv : 0 < (2 * (deriv g S₀ + 1)) / (-(L ^ 3 - L)) := by positivity
      dsimp [s_big]; linarith
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (deriv g) (fun r => deriv (deriv g) r) hs_big_gt
      (fun r _ => hgp_c1.continuous.continuousAt.continuousWithinAt)
      (fun r _ => (hgp_c1.differentiable one_ne_zero r).hasDerivAt)
    have hcle := hstep c hc.1.le
    rw [hslope, div_le_iff₀ (by linarith)] at hcle
    have hdg_big : 0 < deriv g s_big := hgp s_big ((le_max_left _ _).trans hs_big_gt.le)
    have hs_diff : s_big - S₀ = (2 * (deriv g S₀ + 1)) / (-(L ^ 3 - L)) := by dsimp [s_big]; ring
    have hcalc : (L ^ 3 - L) / 2 * (s_big - S₀) = -(deriv g S₀ + 1) := by
      rw [hs_diff, mul_div_assoc']
      apply (div_eq_iff (by linarith : -(L ^ 3 - L) ≠ 0)).mpr
      ring
    linarith
  · obtain ⟨S₁, hS₁⟩ := (Metric.tendsto_atTop.mp hdd_lim) ((L ^ 3 - L) / 2) (by linarith)
    let S₀ := max s₀ S₁
    have hstep : ∀ s ≥ S₀, (L ^ 3 - L) / 2 ≤ deriv (deriv g) s := by
      intro s hs
      rw [hode s ((le_max_left _ _).trans hs)]
      have hb := hS₁ s ((le_max_right _ _).trans hs)
      rw [Real.dist_eq, abs_lt] at hb; linarith
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (tendsto_atTop.mp hcn_top (S₀ + 4 / (L ^ 3 - L)))
    obtain ⟨N', hN'⟩ := (Metric.tendsto_atTop.mp hdg_zero) 1 (by norm_num)
    let k := max N N'
    have hck_gt : S₀ + 4 / (L ^ 3 - L) ≤ cn k := hN k (le_max_left _ _)
    have hck_lt : S₀ < cn k := by
      have hdiv : 0 < 4 / (L ^ 3 - L) := by positivity
      linarith
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (deriv g) (fun r => deriv (deriv g) r) hck_lt
      (fun r _ => hgp_c1.continuous.continuousAt.continuousWithinAt)
      (fun r _ => (hgp_c1.differentiable one_ne_zero r).hasDerivAt)
    have hcge := hstep c hc.1.le
    rw [hslope, le_div_iff₀ (by linarith)] at hcge
    have hdg0 : 0 < deriv g S₀ := hgp S₀ (le_max_left _ _)
    have hdgk : deriv g (cn k) < 1 := by
      have := hN' k (le_max_right _ _); rw [Real.dist_eq, sub_zero, abs_lt] at this; exact this.2
    have hmul : 2 ≤ (L ^ 3 - L) / 2 * (cn k - S₀) := by
      have h1' : (L ^ 3 - L) / 2 * (4 / (L ^ 3 - L)) = 2 := by
        rw [div_mul_div_comm, mul_comm (L ^ 3 - L) 4, mul_div_mul_right _ _ hpos.ne']; norm_num
      have h2' : 4 / (L ^ 3 - L) ≤ cn k - S₀ := by linarith
      nlinarith
    linarith

private theorem no_neg_inf_of_neg_E1 {g : ℝ → ℝ}
    (hg_c2 : ContDiff ℝ 2 g) (hg_bd : ∀ s, |g s| ≤ 1)
    {s₀ C0 : ℝ} (hC0_gt : -(1 / 2 : ℝ) < C0) (hC0_neg : C0 < 0)
    (hgp : ∀ s, s ≤ s₀ → 0 < deriv g s)
    (hode : ∀ s, s ≤ s₀ → deriv (deriv g) s = (g s) ^ 3 - g s)
    (hE1 : ∀ s, s ≤ s₀ → (deriv g s) ^ 2 - (1 / 2) * (1 - (g s) ^ 2) ^ 2 = C0) : False := by
  -- Apply no_pos_inf_of_neg_E1 to g̃(s) = -g(-s) on [-s₀, ∞)!
  let g' : ℝ → ℝ := fun s => -g (-s)
  have hg'_c2 : ContDiff ℝ 2 g' := (hg_c2.comp contDiff_neg).neg
  have hg'_bd : ∀ s, |g' s| ≤ 1 := fun s => by dsimp [g']; rw [abs_neg]; exact hg_bd (-s)
  have hg'_deriv (s : ℝ) : deriv g' s = deriv g (-s) := by
    have h1 : HasDerivAt (fun r : ℝ => g (-r)) (deriv g (-s) * (-1)) s := by
      have hd := (hg_c2.differentiable (by norm_num) (-s)).hasDerivAt
      exact HasDerivAt.comp (h₂ := g) (h := fun r : ℝ => -r) s hd (hasDerivAt_id s).neg
    have h2 : HasDerivAt g' (deriv g (-s)) s := by
      have hn := h1.neg
      have hval : -(deriv g (-s) * -1) = deriv g (-s) := by ring
      exact hval ▸ hn
    exact h2.deriv
  have hg'_dderiv (s : ℝ) : deriv (deriv g') s = -deriv (deriv g) (-s) := by
    have hgp_c1 : ContDiff ℝ 1 (deriv g) := by
      have h := hg_c2
      rw [show (2 : WithTop ℕ∞) = (1 : ℕ) + 1 by norm_num, contDiff_succ_iff_deriv] at h
      exact h.2.2
    have heq : deriv g' = fun r => deriv g (-r) := funext hg'_deriv
    rw [heq]
    have h1 : HasDerivAt (fun r : ℝ => deriv g (-r)) (deriv (deriv g) (-s) * (-1)) s :=
      HasDerivAt.comp (h₂ := deriv g) (h := fun r : ℝ => -r) s
        (hgp_c1.differentiable one_ne_zero (-s)).hasDerivAt (hasDerivAt_id s).neg
    rw [h1.deriv]; ring
  exact no_pos_inf_of_neg_E1 hg'_c2 hg'_bd (s₀ := -s₀) hC0_gt hC0_neg
    (fun s hs => by rw [hg'_deriv s]; exact hgp (-s) (by linarith))
    (fun s hs => by
      rw [hg'_dderiv s, hode (-s) (by linarith)]; dsimp [g']; ring)
    (fun s hs => by
      rw [hg'_deriv s]; dsimp [g']
      have h := hE1 (-s) (by linarith)
      linarith [show (-g (-s)) ^ 2 = (g (-s)) ^ 2 by ring])

set_option maxHeartbeats 1000000 in
private theorem stable2_energy_linear_growth {v : Plane → ℝ}
    (hv : DeGiorgi.IsBoundedSolution v)
    (h1 : ∀ y, |v y| ≤ 1)
    {D : ℝ} (hD : 0 ≤ D) (hgradB : ∀ y, ‖∇ v y‖ ≤ D)
    (hstab : ∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      0 ≤ ∫ y : Plane, (‖∇ ψ y‖ ^ 2 + (3 * (v y) ^ 2 - 1) * (ψ y) ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      (∫ y in Metric.ball (0 : Plane) R, (1 / 2 * ‖∇ v y‖ ^ 2 + doubleWell (v y))) ≤ C * R := by
  by_cases hzero : ∀ y : Plane, ∇ v y = 0
  · -- Case 1: v is constant; stability rules out v ≡ 0, so v ≡ ±1 and energy is 0
    have hv_const : ∀ y : Plane, v y = v 0 := by
      intro y
      have hd (r : ℝ) (_ : r ∈ Set.uIcc (0 : ℝ) 1) :
          HasDerivAt (fun τ : ℝ => v (τ • y)) 0 r := by
        have hfd : HasDerivAt (fun τ : ℝ => v (τ • y)) (fderiv ℝ v (r • y) y) r :=
          (hv.regular.differentiable (by norm_num) (r • y)).hasFDerivAt.comp_hasDerivAt r
            (by simpa using (hasDerivAt_id r).smul_const y)
        have hf0 : fderiv ℝ v (r • y) = 0 := by
          have hg0 := hzero (r • y)
          unfold gradient at hg0
          exact (InnerProductSpace.toDual ℝ Plane).symm.injective (by simpa using hg0)
        rw [hf0, zero_apply] at hfd
        exact hfd
      simpa using eq_of_hasDerivAt_zero_on_uIcc hd
    have hlap0 : (Δ v) 0 = 0 := by
      have heq : v = fun _ => v 0 := funext hv_const
      rw [heq]
      let ob := EuclideanSpace.basisFun (Fin 2) ℝ
      rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ ob]
      simp [iteratedFDeriv_two_apply]
    have hsol0 := hv.solution 0
    rw [hlap0, zero_add] at hsol0
    have hcases : v 0 = 0 ∨ v 0 = 1 ∨ v 0 = -1 := by
      have hfac : v 0 * (1 - v 0) * (1 + v 0) = 0 := by linarith
      rcases mul_eq_zero.mp hfac with h12 | h3
      · rcases mul_eq_zero.mp h12 with h0 | h1'
        · exact Or.inl h0
        · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (by linarith))
    rcases hcases with hv0 | hv1 | hvm1
    · exfalso
      exact const_zero_unstable2 fun ψ hψ hψc => by
        simpa [fun y => (hv_const y).trans hv0] using hstab ψ hψ hψc
    · refine ⟨0, le_rfl, fun R _ => ?_⟩
      have hpt : ∀ y : Plane, 1 / 2 * ‖∇ v y‖ ^ 2 + doubleWell (v y) = 0 := by
        intro y; rw [hzero y, hv_const y, hv1]; simp [doubleWell]
      simp_rw [hpt, integral_zero]; linarith
    · refine ⟨0, le_rfl, fun R _ => ?_⟩
      have hpt : ∀ y : Plane, 1 / 2 * ‖∇ v y‖ ^ 2 + doubleWell (v y) = 0 := by
        intro y; rw [hzero y, hv_const y, hvm1]; simp [doubleWell]
      simp_rw [hpt, integral_zero]; linarith
  · -- Case 2: ∇ v y₀ ≠ 0 for some y₀; rotate so ∇ v' points along e2 0
    push Not at hzero
    obtain ⟨y₀, hy₀⟩ := hzero
    let g₀ := ∇ v y₀
    let r := ‖g₀‖
    have hr : 0 < r := norm_pos_iff.mpr hy₀
    let ca := g₀ 0 / r
    let sb := g₀ 1 / r
    have hcs : ca ^ 2 + sb ^ 2 = 1 := by
      have hsq : (g₀ 0) ^ 2 + (g₀ 1) ^ 2 = r ^ 2 := by
        dsimp [r]; rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
      dsimp [ca, sb]; field_simp [hr.ne']; exact hsq
    let Q := rot2 ca sb hcs
    let v' : Plane → ℝ := fun y => v (Q y)
    obtain ⟨hv', hv'1, hv'_gn, hv'_gB, hv'_stab, hv'_en⟩ :=
      isometry2_preserves_solution hv h1 hgradB hstab Q
    have hcol := collinear_hessian_of_stable2 hv' hD hv'_gB hv'_stab
    let ystar := Q.symm y₀
    let s₀ := ystar 0
    let t₀ := ystar 1
    have hystar_eq : s₀ • e2 0 + t₀ • e2 1 = ystar := by
      ext i; fin_cases i <;> simp [s₀, t₀, e2]
    have hv'p (y : Plane) (i : Fin 2) : part2 v' i y = inner ℝ (∇ v (Q y)) (Q (e2 i)) := by
      unfold part2
      have hfd := ((hv.regular.differentiable (by norm_num) (Q y)).hasFDerivAt.comp y
        Q.toContinuousLinearMap.hasFDerivAt).fderiv
      change fderiv ℝ (v ∘ Q) y (e2 i) = _
      rw [hfd]
      change fderiv ℝ v (Q y) (Q (e2 i)) = _
      rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]
    have hv'0_star : 0 < part2 v' 0 (s₀ • e2 0 + t₀ • e2 1) := by
      rw [hystar_eq, hv'p ystar 0]
      have hQy : Q ystar = y₀ := Q.apply_symm_apply y₀
      rw [hQy]
      have hQe0 : Q (e2 0) = ca • e2 0 + sb • e2 1 := by
        ext i; fin_cases i <;> simp [Q, rot2, e2]
      rw [hQe0, inner_add_right, inner_smul_right, inner_smul_right]
      have hi0 : inner ℝ (∇ v y₀) (e2 0) = g₀ 0 := by
        dsimp [g₀]; rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, e2]
      have hi1 : inner ℝ (∇ v y₀) (e2 1) = g₀ 1 := by
        dsimp [g₀]; rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, e2]
      rw [hi0, hi1]
      have hval : ca * g₀ 0 + sb * g₀ 1 = r := by
        have hsq : (g₀ 0) ^ 2 + (g₀ 1) ^ 2 = r ^ 2 := by
          dsimp [r]; rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
        dsimp [ca, sb]; field_simp [hr.ne']; linarith
      linarith
    have hv'1_star : part2 v' 1 (s₀ • e2 0 + t₀ • e2 1) = 0 := by
      rw [hystar_eq, hv'p ystar 1]
      have hQy : Q ystar = y₀ := Q.apply_symm_apply y₀
      rw [hQy]
      have hQe1 : Q (e2 1) = (-sb) • e2 0 + ca • e2 1 := by
        ext i; fin_cases i <;> simp [Q, rot2, e2]
      rw [hQe1, inner_add_right, inner_smul_right, inner_smul_right]
      have hi0 : inner ℝ (∇ v y₀) (e2 0) = g₀ 0 := by
        dsimp [g₀]; rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, e2]
      have hi1 : inner ℝ (∇ v y₀) (e2 1) = g₀ 1 := by
        dsimp [g₀]; rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, e2]
      rw [hi0, hi1]
      dsimp [ca, sb]; field_simp [hr.ne']; ring
    -- 1D slice g(s) = v'(s, t₀)
    let g : ℝ → ℝ := fun s => v' (s • e2 0 + t₀ • e2 1)
    have hg_c2 : ContDiff ℝ 2 g :=
      hv'.regular.comp ((contDiff_id.smul contDiff_const).add contDiff_const)
    have hg_deriv (s : ℝ) : HasDerivAt g (part2 v' 0 (s • e2 0 + t₀ • e2 1)) s := by
      have hl : HasDerivAt (fun r : ℝ => r • e2 0 + t₀ • e2 1) (e2 0) s := by
        simpa using ((hasDerivAt_id s).smul_const (e2 0)).add_const (t₀ • e2 1)
      exact (hv'.regular.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s hl
    have hdg_eq (s : ℝ) : deriv g s = part2 v' 0 (s • e2 0 + t₀ • e2 1) := (hg_deriv s).deriv
    have hdg_deriv (s : ℝ) : HasDerivAt (deriv g) (part22 v' 0 0 (s • e2 0 + t₀ • e2 1)) s := by
      have heq : deriv g = fun r => part2 v' 0 (r • e2 0 + t₀ • e2 1) := funext hdg_eq
      rw [heq]
      have hpc0 : ContDiff ℝ 1 (part2 v' 0) :=
        (hv'.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
      have hl : HasDerivAt (fun r : ℝ => r • e2 0 + t₀ • e2 1) (e2 0) s := by
        simpa using ((hasDerivAt_id s).smul_const (e2 0)).add_const (t₀ • e2 1)
      exact (hpc0.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt s hl
    have hddg_eq (s : ℝ) : deriv (deriv g) s = part22 v' 0 0 (s • e2 0 + t₀ • e2 1) := (hdg_deriv s).deriv
    have hlap_v' (y : Plane) : (Δ v') y = part22 v' 0 0 y + part22 v' 1 1 y := by
      let ob := EuclideanSpace.basisFun (Fin 2) ℝ
      rw [laplacian_eq_iteratedFDeriv_orthonormalBasis v' ob]
      dsimp only
      rw [Fin.sum_univ_two]
      have hterm (k : Fin 2) : iteratedFDeriv ℝ 2 v' y ![ob k, ob k] = part22 v' k k y := by
        have hbk : ob k = e2 k := EuclideanSpace.basisFun_apply (Fin 2) ℝ k
        rw [iteratedFDeriv_two_apply]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hbk]
        unfold part22 part2
        rw [fderiv_clm_apply ((hv'.regular.fderiv_right (by norm_num)).differentiable one_ne_zero y)
          (differentiableAt_const (e2 k))]; simp; rfl
      rw [hterm 0, hterm 1]
    have hode_of_strip (s : ℝ) (hvert : ∀ t : ℝ, part2 v' 1 (s • e2 0 + t • e2 1) = 0) :
        deriv (deriv g) s = (g s) ^ 3 - g s := by
      have hp11 : part22 v' 1 1 (s • e2 0 + t₀ • e2 1) = 0 := by
        have hpc1 : ContDiff ℝ 1 (part2 v' 1) :=
          (hv'.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
        have hl : HasDerivAt (fun r : ℝ => s • e2 0 + r • e2 1) (e2 1) t₀ := by
          simpa using ((hasDerivAt_id t₀).smul_const (e2 1)).const_add (s • e2 0)
        have hd : HasDerivAt (fun r : ℝ => part2 v' 1 (s • e2 0 + r • e2 1))
            (part22 v' 1 1 (s • e2 0 + t₀ • e2 1)) t₀ :=
          (hpc1.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t₀ hl
        have h0 : (fun r : ℝ => part2 v' 1 (s • e2 0 + r • e2 1)) = fun _ => (0 : ℝ) := funext hvert
        rw [h0] at hd
        exact hd.unique (hasDerivAt_const t₀ (0 : ℝ))
      have hsol := hv'.solution (s • e2 0 + t₀ • e2 1)
      rw [hlap_v', hp11, add_zero] at hsol
      rw [hddg_eq s]; dsimp [g]; linarith
    -- Positive-derivative maximal interval around s₀
    let Ipos : Set ℝ := {s : ℝ | ∀ r ∈ Set.uIcc s₀ s, 0 < deriv g r}
    have hs0_in : s₀ ∈ Ipos := by
      intro r hr
      have : r = s₀ := by simpa [Set.uIcc_self] using hr
      subst this; rw [hdg_eq]; exact hv'0_star
    have hstrip_Ipos (s : ℝ) (hs : s ∈ Ipos) (t : ℝ) :
        v' (s • e2 0 + t • e2 1) = g s ∧
        part2 v' 0 (s • e2 0 + t • e2 1) = deriv g s ∧
        part2 v' 1 (s • e2 0 + t • e2 1) = 0 := by
      have hs' : ∀ r ∈ Set.uIcc s₀ s, 0 < part2 v' 0 (r • e2 0 + t₀ • e2 1) := fun r hr => by
        rw [← hdg_eq r]; exact hs r hr
      have h := strip_of_pos_part0 hv' hcol s₀ t₀ hv'1_star s hs' t
      rw [← hdg_eq s] at h
      exact h
    have hode_Ipos (s : ℝ) (hs : s ∈ Ipos) : deriv (deriv g) s = (g s) ^ 3 - g s :=
      hode_of_strip s fun t => (hstrip_Ipos s hs t).2.2
    -- First integral E1(s) = (g'(s))^2 - 1/2 (1 - g(s)^2)^2 is constant C0 on Ipos
    let E1 : ℝ → ℝ := fun s => (deriv g s) ^ 2 - (1 / 2) * (1 - (g s) ^ 2) ^ 2
    let C0 := E1 s₀
    have hE1_const (s : ℝ) (hs : s ∈ Ipos) : E1 s = C0 := by
      apply eq_of_hasDerivAt_zero_on_uIcc
      intro r hr
      have hr_in : r ∈ Ipos := fun τ hτ => hs τ (Set.uIcc_subset_uIcc Set.left_mem_uIcc hr hτ)
      have hd1 := (hdg_deriv r).pow 2
      have hd2 := (((hg_deriv r).pow 2).const_sub (1 : ℝ)).pow 2 |>.const_mul (1 / 2 : ℝ)
      have hsub := hd1.sub hd2
      have hval : 2 * deriv g r ^ (2 - 1) * part22 v' 0 0 (r • e2 0 + t₀ • e2 1) -
          1 / 2 * (2 * (1 - g r ^ 2) ^ (2 - 1) * -(2 * g r ^ (2 - 1) * part2 v' 0 (r • e2 0 + t₀ • e2 1))) = 0 := by
        have hode := hode_Ipos r hr_in
        rw [← hddg_eq r, ← hdg_eq r, hode]
        norm_num; ring
      exact hval ▸ hsub
    have hC0_gt : -(1 / 2 : ℝ) < C0 := by
      dsimp [C0, E1]
      have hpos : 0 < deriv g s₀ := by rw [hdg_eq]; exact hv'0_star
      have h1s : |g s₀| ≤ 1 := hv'1 _
      have hsq : (g s₀) ^ 2 ≤ 1 := by
        have := sq_le_sq.mpr (show |g s₀| ≤ |(1 : ℝ)| by simpa using h1s); simpa using this
      have h0 : 0 ≤ 1 - (g s₀) ^ 2 := by linarith
      have hle1 : (1 - (g s₀) ^ 2) ^ 2 ≤ 1 := by nlinarith
      nlinarith
    -- Helper: if C0 < 0, g cannot stay strictly increasing to +∞ or -∞
    have hno_pos_inf (hC0_neg : C0 < 0) (hall : ∀ s, s₀ ≤ s → s ∈ Ipos) : False :=
      no_pos_inf_of_neg_E1 hg_c2 (fun s => hv'1 _) hC0_gt hC0_neg
        (fun s hs => (hall s hs) s Set.right_mem_uIcc)
        (fun s hs => hode_Ipos s (hall s hs))
        (fun s hs => hE1_const s (hall s hs))
    have hno_neg_inf (hC0_neg : C0 < 0) (hall : ∀ s, s ≤ s₀ → s ∈ Ipos) : False :=
      no_neg_inf_of_neg_E1 hg_c2 (fun s => hv'1 _) hC0_gt hC0_neg
        (fun s hs => (hall s hs) s Set.right_mem_uIcc)
        (fun s hs => hode_Ipos s (hall s hs))
        (fun s hs => hE1_const s (hall s hs))
    -- Helper: finite endpoints (a < s0 < b) with C0 < 0 lead to quadratic_cap_contradiction
    have hcontra_ab (a b : ℝ) (has0 : a < s₀) (hs0b : s₀ < b)
        (hIab : ∀ s ∈ Set.Ioo a b, s ∈ Ipos)
        (hdga : deriv g a = 0) (hdgb : deriv g b = 0) (hC0_neg : C0 < 0) : False :=
      contra_finite_ab hv' hv'1 hv'_stab hcol t₀ (fun _ => rfl) hg_c2 hdg_eq hdg_deriv hddg_eq
        hode_of_strip (has0.trans hs0b) hC0_gt hC0_neg
        (fun s hs => (hIab s hs) s Set.right_mem_uIcc)
        (fun s hs t => ⟨(hstrip_Ipos s (hIab s hs) t).1, (hstrip_Ipos s (hIab s hs) t).2.2⟩)
        (fun s hs => hE1_const s (hIab s hs)) hdga hdgb
    -- Prove Ipos = Set.univ (neither finite right endpoint nor finite left endpoint exists)
    have hIpos_right : ∀ s, s₀ ≤ s → s ∈ Ipos := by
      by_contra hnot
      push Not at hnot
      obtain ⟨s_bad, hs_bad_ge, hs_bad_not⟩ := hnot
      have hex_r : ∃ r, s₀ < r ∧ deriv g r ≤ 0 := by
        by_contra hno; push Not at hno
        apply hs_bad_not; intro r hr
        rw [Set.uIcc_of_le hs_bad_ge] at hr
        by_cases h0 : r = s₀
        · subst h0; rw [hdg_eq]; exact hv'0_star
        · exact hno r (lt_of_le_of_ne hr.1 (Ne.symm h0))
      let Sr := {r : ℝ | s₀ < r ∧ deriv g r ≤ 0}
      have hSr_ne : Sr.Nonempty := hex_r
      have hSr_bdd : BddBelow Sr := ⟨s₀, fun r hr => hr.1.le⟩
      let b := sInf Sr
      have hdg_cont : Continuous (deriv g) := hg_c2.continuous_deriv (by norm_num)
      have hs0b : s₀ < b := by
        obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp (hdg_cont.continuousAt (x := s₀))
          (deriv g s₀ / 2) (by rw [hdg_eq]; linarith)
        have hle : s₀ + ε / 2 ≤ b := le_csInf hSr_ne fun r hr => by
          by_contra! hlt
          have hd : dist r s₀ < ε := by
            rw [Real.dist_eq, abs_of_pos (by linarith [hr.1])]; linarith
          have hb := hball hd; rw [Real.dist_eq, abs_lt] at hb
          linarith [hr.2, show 0 < deriv g s₀ by rw [hdg_eq]; exact hv'0_star]
        linarith
      have hpos_on_Ico : ∀ s ∈ Set.Ico s₀ b, s ∈ Ipos := by
        intro s hs r hr
        rw [Set.uIcc_of_le hs.1] at hr
        by_cases h0 : r = s₀
        · subst h0; rw [hdg_eq]; exact hv'0_star
        · by_contra! hle
          have hr_sr : r ∈ Sr := ⟨lt_of_le_of_ne hr.1 (Ne.symm h0), hle⟩
          have := csInf_le hSr_bdd hr_sr
          linarith [hr.2, hs.2]
      have hdgb : deriv g b = 0 := by
        apply le_antisymm
        · by_contra! hpos
          obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp (hdg_cont.continuousAt (x := b))
            (deriv g b / 2) (by linarith)
          obtain ⟨r, hrSr, hrlt⟩ := exists_lt_of_csInf_lt hSr_ne (by linarith : b < b + ε)
          have hge : b ≤ r := csInf_le hSr_bdd hrSr
          have hd : dist r b < ε := by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
          have hb := hball hd; rw [Real.dist_eq, abs_lt] at hb; linarith [hrSr.2]
        · have hlim : Tendsto (fun n : ℕ => deriv g (b - (b - s₀) / ((n : ℝ) + 2))) atTop (𝓝 (deriv g b)) :=
            hdg_cont.continuousAt.tendsto.comp (by
              have h0 : Tendsto (fun n : ℕ => (b - s₀) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
                tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
              simpa using tendsto_const_nhds.sub h0)
          exact ge_of_tendsto hlim (Eventually.of_forall fun n => (hpos_on_Ico _ ⟨by
              have hbs0 : 0 < b - s₀ := by linarith
              have hlt : (b - s₀) / ((n : ℝ) + 2) < b - s₀ := by
                rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
                nlinarith [Nat.cast_nonneg (α := ℝ) n]
              linarith,
            by
              have hbs0 : 0 < b - s₀ := by linarith
              have hpos_div : 0 < (b - s₀) / ((n : ℝ) + 2) := by positivity
              linarith⟩ _ Set.right_mem_uIcc).le)
      have hE1_b : E1 b = C0 := by
        have hE1_cont : Continuous E1 :=
          (hdg_cont.pow 2).sub (((continuous_const.sub (hg_c2.continuous.pow 2)).pow 2).const_mul (1 / 2 : ℝ))
        have hlim : Tendsto (fun n : ℕ => E1 (b - (b - s₀) / ((n : ℝ) + 2))) atTop (𝓝 (E1 b)) :=
          hE1_cont.continuousAt.tendsto.comp (by
            have h0 : Tendsto (fun n : ℕ => (b - s₀) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
              tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
            simpa using tendsto_const_nhds.sub h0)
        have heq : (fun n : ℕ => E1 (b - (b - s₀) / ((n : ℝ) + 2))) = fun _ => C0 :=
          funext fun n => hE1_const _ (hpos_on_Ico _ ⟨by
              have hbs0 : 0 < b - s₀ := by linarith
              have hlt : (b - s₀) / ((n : ℝ) + 2) < b - s₀ := by
                rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
                nlinarith [Nat.cast_nonneg (α := ℝ) n]
              linarith,
            by
              have hbs0 : 0 < b - s₀ := by linarith
              have hpos_div : 0 < (b - s₀) / ((n : ℝ) + 2) := by positivity
              linarith⟩)
        rw [heq] at hlim; exact tendsto_nhds_unique hlim tendsto_const_nhds
      have hC0_le : C0 ≤ 0 := by rw [← hE1_b]; dsimp [E1]; rw [hdgb]; nlinarith [sq_nonneg (1 - (g b) ^ 2)]
      rcases eq_or_lt_of_le hC0_le with hC0_0 | hC0_neg
      · -- C0 = 0: g(b) = 1 ruled out by monotonicity of (1 - g s) * exp(2 s)
        have hgb2 : (g b) ^ 2 = 1 := by
          rw [hC0_0] at hE1_b; dsimp [E1] at hE1_b; rw [hdgb] at hE1_b
          have : (1 - (g b) ^ 2) ^ 2 = 0 := by linarith
          linarith [sq_eq_zero_iff.mp this]
        have hgs0_lt_gb : g s₀ < g b := by
          obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g (fun r => deriv g r) hs0b
            (fun r _ => hg_c2.continuous.continuousAt.continuousWithinAt)
            (fun r _ => (hg_c2.differentiable (by norm_num) r).hasDerivAt)
          have hpos := (hpos_on_Ico c ⟨hc.1.le, hc.2⟩) c Set.right_mem_uIcc
          rw [hslope] at hpos
          have := (div_pos_iff_of_pos_right (by linarith)).mp hpos
          linarith
        have hgb_eq1 : g b = 1 := by
          have hgs0_ge : -1 ≤ g s₀ := (abs_le.mp (hv'1 _)).1
          rcases sq_eq_one_iff.mp hgb2 with h1' | hm1
          · exact h1'
          · linarith
        let F : ℝ → ℝ := fun s => (1 - g s) * Real.exp (2 * s)
        have hF_mono : F s₀ ≤ F b := by
          by_contra! hlt
          obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope F
            (fun r => (-deriv g r + 2 * (1 - g r)) * Real.exp (2 * r)) hs0b
            (fun r _ => (((continuous_const.sub hg_c2.continuous).mul
              (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousAt).continuousWithinAt)
            (fun r _ => by
              have h1' : HasDerivAt (fun τ => 1 - g τ) (-deriv g r) r := by
                simpa using ((hg_c2.differentiable (by norm_num) r).hasDerivAt).const_sub (1 : ℝ)
              have h2' : HasDerivAt (fun τ => Real.exp (2 * τ)) (Real.exp (2 * r) * 2) r := by
                have hd := ((hasDerivAt_id r).const_mul (2 : ℝ)).exp
                simpa using hd
              have hm := h1'.mul h2'
              have hval : (-deriv g r + 2 * (1 - g r)) * Real.exp (2 * r) =
                  -deriv g r * Real.exp (2 * r) + (1 - g r) * (Real.exp (2 * r) * 2) := by ring
              exact hval.symm ▸ hm)
          have hneg : (-deriv g c + 2 * (1 - g c)) * Real.exp (2 * c) < 0 := by
            rw [hslope]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
          have hc_in : c ∈ Ipos := hpos_on_Ico c ⟨hc.1.le, hc.2⟩
          have hE1c : (deriv g c) ^ 2 = (1 / 2) * (1 - (g c) ^ 2) ^ 2 := by
            have := hE1_const c hc_in; dsimp [E1] at this; linarith
          have hgc1 : |g c| ≤ 1 := hv'1 _
          have h1m : 0 ≤ 1 - g c := by linarith [(abs_le.mp hgc1).2]
          have h1p : 1 + g c ≤ 2 := by linarith [(abs_le.mp hgc1).2]
          have hdgc_le : deriv g c ≤ 2 * (1 - g c) := by
            have hsq : (deriv g c) ^ 2 ≤ (2 * (1 - g c)) ^ 2 := by
              rw [hE1c]
              have hfac : (1 - (g c) ^ 2) ^ 2 = (1 - g c) ^ 2 * (1 + g c) ^ 2 := by ring
              rw [hfac]
              have h1p2 : (1 + g c) ^ 2 ≤ 4 := by nlinarith [(abs_le.mp hgc1).1, (abs_le.mp hgc1).2]
              nlinarith [sq_nonneg (1 - g c)]
            nlinarith [hc_in c Set.right_mem_uIcc]
          have hnn : 0 ≤ (-deriv g c + 2 * (1 - g c)) * Real.exp (2 * c) :=
            mul_nonneg (by linarith) (Real.exp_pos _).le
          linarith
        dsimp [F] at hF_mono; rw [hgb_eq1, sub_self, zero_mul] at hF_mono
        have hpos : 0 < (1 - g s₀) * Real.exp (2 * s₀) :=
          mul_pos (by linarith) (Real.exp_pos _)
        linarith
      · -- C0 < 0: left endpoint a < s₀ must also exist, then apply hcontra_ab
        have hex_l : ∃ r, r < s₀ ∧ deriv g r ≤ 0 := by
          by_contra hno; push Not at hno
          apply hno_neg_inf hC0_neg
          intro s hs r hr
          rw [Set.uIcc_of_ge hs] at hr
          by_cases h0 : r = s₀
          · subst h0; rw [hdg_eq]; exact hv'0_star
          · exact hno r (lt_of_le_of_ne hr.2 h0)
        let Sl := {r : ℝ | r < s₀ ∧ deriv g r ≤ 0}
        have hSl_ne : Sl.Nonempty := hex_l
        have hSl_bdd : BddAbove Sl := ⟨s₀, fun r hr => hr.1.le⟩
        let a := sSup Sl
        have has0 : a < s₀ := by
          obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp (hdg_cont.continuousAt (x := s₀))
            (deriv g s₀ / 2) (by rw [hdg_eq]; linarith)
          have hle : a ≤ s₀ - ε / 2 := csSup_le hSl_ne fun r hr => by
            by_contra! hgt
            have hd : dist r s₀ < ε := by
              rw [Real.dist_eq, abs_of_neg (by linarith [hr.1])]; linarith
            have hb := hball hd; rw [Real.dist_eq, abs_lt] at hb
            linarith [hr.2, show 0 < deriv g s₀ by rw [hdg_eq]; exact hv'0_star]
          linarith
        have hIab : ∀ s ∈ Set.Ioo a b, s ∈ Ipos := by
          intro s hs
          by_cases hge : s₀ ≤ s
          · exact hpos_on_Ico s ⟨hge, hs.2⟩
          · push Not at hge
            intro r hr
            rw [Set.uIcc_of_ge hge.le] at hr
            by_cases h0 : r = s₀
            · subst h0; rw [hdg_eq]; exact hv'0_star
            · by_contra! hle
              have hr_sl : r ∈ Sl := ⟨lt_of_le_of_ne hr.2 h0, hle⟩
              have := le_csSup hSl_bdd hr_sl
              linarith [hr.1, hs.1]
        have hdga : deriv g a = 0 := by
          apply le_antisymm
          · by_contra! hpos
            obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp (hdg_cont.continuousAt (x := a))
              (deriv g a / 2) (by linarith)
            obtain ⟨r, hrSl, hrgt⟩ := exists_lt_of_lt_csSup hSl_ne (by linarith : a - ε < a)
            have hle : r ≤ a := le_csSup hSl_bdd hrSl
            have hd : dist r a < ε := by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith
            have hb := hball hd; rw [Real.dist_eq, abs_lt] at hb; linarith [hrSl.2]
          · have hlim : Tendsto (fun n : ℕ => deriv g (a + (s₀ - a) / ((n : ℝ) + 2))) atTop (𝓝 (deriv g a)) :=
              hdg_cont.continuousAt.tendsto.comp (by
                have h0 : Tendsto (fun n : ℕ => (s₀ - a) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
                  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
                simpa using tendsto_const_nhds.add h0)
            exact ge_of_tendsto hlim (Eventually.of_forall fun n => (hIab _ ⟨by
                have hs0a : 0 < s₀ - a := by linarith
                have hpos_div : 0 < (s₀ - a) / ((n : ℝ) + 2) := by positivity
                linarith,
              by
                have hs0a : 0 < s₀ - a := by linarith
                have hlt : (s₀ - a) / ((n : ℝ) + 2) < s₀ - a := by
                  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
                  nlinarith [Nat.cast_nonneg (α := ℝ) n]
                linarith⟩ _ Set.right_mem_uIcc).le)
        exact hcontra_ab a b has0 hs0b hIab hdga hdgb hC0_neg
    -- Now prove Ipos_left similarly (note: C0 < 0 is already ruled out by hno_pos_inf!)
    have hC0_ge0 : 0 ≤ C0 := by
      by_contra! hneg; exact hno_pos_inf hneg hIpos_right
    have hC0_le0 : C0 ≤ 0 := by
      -- Since g is strictly increasing on [s₀, ∞) and bounded above by 1, g'(c_n) -> 0
      have hmono : ∀ s₁ s₂, s₀ ≤ s₁ → s₁ < s₂ → g s₁ < g s₂ := by
        intro s₁ s₂ hs₁ hlt
        obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g (fun r => deriv g r) hlt
          (fun r _ => hg_c2.continuous.continuousAt.continuousWithinAt)
          (fun r _ => (hg_c2.differentiable (by norm_num) r).hasDerivAt)
        have hpos := (hIpos_right c (by linarith [hc.1])) c Set.right_mem_uIcc
        rw [hslope] at hpos
        have := (div_pos_iff_of_pos_right (by linarith)).mp hpos
        linarith
      let S := {x : ℝ | ∃ s, s₀ ≤ s ∧ g s = x}
      have hSne : S.Nonempty := ⟨g s₀, s₀, le_rfl, rfl⟩
      have hSbdd : BddAbove S := ⟨1, fun x ⟨s, _, hx⟩ => by rw [← hx]; exact (abs_le.mp (hv'1 _)).2⟩
      let L := sSup S
      have hL_lim : Tendsto g atTop (𝓝 L) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨x, ⟨s₁, hs₁, rfl⟩, hxgt⟩ := exists_lt_of_lt_csSup hSne (by linarith : L - ε < L)
        refine ⟨s₁, fun s hs => ?_⟩
        rw [Real.dist_eq, abs_lt]
        have hle : g s ≤ L := le_csSup hSbdd ⟨s, hs₁.trans hs, rfl⟩
        have hge : g s₁ ≤ g s := if h : s₁ = s then by rw [h] else (hmono s₁ s hs₁ (lt_of_le_of_ne hs h)).le
        constructor <;> linarith
      have hmv (n : ℕ) : ∃ c ∈ Set.Ioo (s₀ + n) (s₀ + n + 1),
          deriv g c = g (s₀ + n + 1) - g (s₀ + n) := by
        obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g (fun r => deriv g r) (by linarith : s₀ + n < s₀ + n + 1)
          (fun r _ => hg_c2.continuous.continuousAt.continuousWithinAt)
          (fun r _ => (hg_c2.differentiable (by norm_num) r).hasDerivAt)
        refine ⟨c, hc, ?_⟩
        have hden : s₀ + n + 1 - (s₀ + n) = 1 := by ring
        rw [hden, div_one] at hslope; exact hslope
      let cn : ℕ → ℝ := fun n => Classical.choose (hmv n)
      have hcn_gt (n : ℕ) : s₀ + n < cn n := (Classical.choose_spec (hmv n)).1.1
      have hcn_top : Tendsto cn atTop atTop :=
        tendsto_atTop_mono (fun n => (hcn_gt n).le)
          (tendsto_atTop_add_const_left atTop s₀ tendsto_natCast_atTop_atTop)
      have hdg_zero : Tendsto (fun n => deriv g (cn n)) atTop (𝓝 0) := by
        have heq : (fun n : ℕ => deriv g (cn n)) = fun n : ℕ => g (s₀ + n + 1) - g (s₀ + n) :=
          funext fun n => (Classical.choose_spec (hmv n)).2
        rw [heq]
        have h1' := hL_lim.comp ((tendsto_atTop_add_const_left atTop s₀ tendsto_natCast_atTop_atTop).atTop_add
          (tendsto_const_nhds (x := (1 : ℝ))))
        have h2' := hL_lim.comp (tendsto_atTop_add_const_left atTop s₀ tendsto_natCast_atTop_atTop)
        simpa using h1'.sub h2'
      have hE1_lim : Tendsto (fun n => E1 (cn n)) atTop (𝓝 (-(1 / 2) * (1 - L ^ 2) ^ 2)) := by
        have hg_cn : Tendsto (fun n => g (cn n)) atTop (𝓝 L) := hL_lim.comp hcn_top
        have h := (hdg_zero.pow 2).sub
          ((((tendsto_const_nhds (x := (1 : ℝ))).sub (hg_cn.pow 2)).pow 2).const_mul (1 / 2 : ℝ))
        simpa [E1, Function.comp_def] using h
      have hE1_eq : (fun n => E1 (cn n)) = fun _ => C0 :=
        funext fun n => hE1_const (cn n) (hIpos_right (cn n) (by linarith [hcn_gt n, Nat.cast_nonneg (α := ℝ) n]))
      rw [hE1_eq] at hE1_lim
      have hL_eq : -(1 / 2) * (1 - L ^ 2) ^ 2 = C0 := tendsto_nhds_unique hE1_lim tendsto_const_nhds
      rw [← hL_eq]; nlinarith [sq_nonneg (1 - L ^ 2)]
    have hC0_eq0 : C0 = 0 := le_antisymm hC0_le0 hC0_ge0
    have hIpos_left : ∀ s, s ≤ s₀ → s ∈ Ipos := by
      by_contra hnot; push Not at hnot
      obtain ⟨s_bad, hs_bad_le, hs_bad_not⟩ := hnot
      have hex_l : ∃ r, r < s₀ ∧ deriv g r ≤ 0 := by
        by_contra hno; push Not at hno
        apply hs_bad_not; intro r hr
        rw [Set.uIcc_of_ge hs_bad_le] at hr
        by_cases h0 : r = s₀
        · subst h0; rw [hdg_eq]; exact hv'0_star
        · exact hno r (lt_of_le_of_ne hr.2 h0)
      let Sl := {r : ℝ | r < s₀ ∧ deriv g r ≤ 0}
      have hSl_ne : Sl.Nonempty := hex_l
      have hSl_bdd : BddAbove Sl := ⟨s₀, fun r hr => hr.1.le⟩
      let a := sSup Sl
      have hdg_cont : Continuous (deriv g) := hg_c2.continuous_deriv (by norm_num)
      have has0 : a < s₀ := by
        obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp (hdg_cont.continuousAt (x := s₀))
          (deriv g s₀ / 2) (by rw [hdg_eq]; linarith)
        have hle : a ≤ s₀ - ε / 2 := csSup_le hSl_ne fun r hr => by
          by_contra! hgt
          have hd : dist r s₀ < ε := by rw [Real.dist_eq, abs_of_neg (by linarith [hr.1])]; linarith
          have hb := hball hd; rw [Real.dist_eq, abs_lt] at hb
          linarith [hr.2, show 0 < deriv g s₀ by rw [hdg_eq]; exact hv'0_star]
        linarith
      have hpos_on_Ioc : ∀ s ∈ Set.Ioc a s₀, s ∈ Ipos := by
        intro s hs r hr
        rw [Set.uIcc_of_ge hs.2] at hr
        by_cases h0 : r = s₀
        · subst h0; rw [hdg_eq]; exact hv'0_star
        · by_contra! hle
          have hr_sl : r ∈ Sl := ⟨lt_of_le_of_ne hr.2 h0, hle⟩
          have := le_csSup hSl_bdd hr_sl
          linarith [hr.1, hs.1]
      have hdga : deriv g a = 0 := by
        apply le_antisymm
        · by_contra! hpos
          obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp (hdg_cont.continuousAt (x := a))
            (deriv g a / 2) (by linarith)
          obtain ⟨r, hrSl, hrgt⟩ := exists_lt_of_lt_csSup hSl_ne (by linarith : a - ε < a)
          have hle : r ≤ a := le_csSup hSl_bdd hrSl
          have hd : dist r a < ε := by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith
          have hb := hball hd; rw [Real.dist_eq, abs_lt] at hb; linarith [hrSl.2]
        · have hlim : Tendsto (fun n : ℕ => deriv g (a + (s₀ - a) / ((n : ℝ) + 2))) atTop (𝓝 (deriv g a)) :=
            hdg_cont.continuousAt.tendsto.comp (by
              have h0 : Tendsto (fun n : ℕ => (s₀ - a) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
                tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
              simpa using tendsto_const_nhds.add h0)
          exact ge_of_tendsto hlim (Eventually.of_forall fun n => (hpos_on_Ioc _ ⟨by
              have hs0a : 0 < s₀ - a := by linarith
              have hpos_div : 0 < (s₀ - a) / ((n : ℝ) + 2) := by positivity
              linarith,
            by
              have hs0a : 0 < s₀ - a := by linarith
              have hlt : (s₀ - a) / ((n : ℝ) + 2) < s₀ - a := by
                rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
                nlinarith [Nat.cast_nonneg (α := ℝ) n]
              linarith⟩ _ Set.right_mem_uIcc).le)
      have hE1_a : E1 a = 0 := by
        rw [← hC0_eq0]
        have hE1_cont : Continuous E1 :=
          (hdg_cont.pow 2).sub (((continuous_const.sub (hg_c2.continuous.pow 2)).pow 2).const_mul (1 / 2 : ℝ))
        have hlim : Tendsto (fun n : ℕ => E1 (a + (s₀ - a) / ((n : ℝ) + 2))) atTop (𝓝 (E1 a)) :=
          hE1_cont.continuousAt.tendsto.comp (by
            have h0 : Tendsto (fun n : ℕ => (s₀ - a) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
              tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
            simpa using tendsto_const_nhds.add h0)
        have heq : (fun n : ℕ => E1 (a + (s₀ - a) / ((n : ℝ) + 2))) = fun _ => C0 :=
          funext fun n => hE1_const _ (hpos_on_Ioc _ ⟨by
              have hs0a : 0 < s₀ - a := by linarith
              have hpos_div : 0 < (s₀ - a) / ((n : ℝ) + 2) := by positivity
              linarith,
            by
              have hs0a : 0 < s₀ - a := by linarith
              have hlt : (s₀ - a) / ((n : ℝ) + 2) < s₀ - a := by
                rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
                nlinarith [Nat.cast_nonneg (α := ℝ) n]
              linarith⟩)
        rw [heq] at hlim; exact tendsto_nhds_unique hlim tendsto_const_nhds
      have hga2 : (g a) ^ 2 = 1 := by
        dsimp [E1] at hE1_a; rw [hdga] at hE1_a
        have : (1 - (g a) ^ 2) ^ 2 = 0 := by linarith
        linarith [sq_eq_zero_iff.mp this]
      have hga_lt_gs0 : g a < g s₀ := by
        obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g (fun r => deriv g r) has0
          (fun r _ => hg_c2.continuous.continuousAt.continuousWithinAt)
          (fun r _ => (hg_c2.differentiable (by norm_num) r).hasDerivAt)
        have hpos := (hpos_on_Ioc c ⟨hc.1, hc.2.le⟩) c Set.right_mem_uIcc
        rw [hslope] at hpos
        have := (div_pos_iff_of_pos_right (by linarith)).mp hpos
        linarith
      have hga_eq_m1 : g a = -1 := by
        have hgs0_le : g s₀ ≤ 1 := (abs_le.mp (hv'1 _)).2
        rcases sq_eq_one_iff.mp hga2 with h1' | hm1
        · linarith
        · exact hm1
      let F : ℝ → ℝ := fun s => (1 + g s) * Real.exp (-2 * s)
      have hF_anti : F s₀ ≤ F a := by
        by_contra! hgt
        obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope F
          (fun r => (deriv g r - 2 * (1 + g r)) * Real.exp (-2 * r)) has0
          (fun r _ => (((continuous_const.add hg_c2.continuous).mul
            (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousAt).continuousWithinAt)
          (fun r _ => by
            have h1' : HasDerivAt (fun τ => 1 + g τ) (deriv g r) r := by
              simpa using ((hg_c2.differentiable (by norm_num) r).hasDerivAt).const_add (1 : ℝ)
            have h2' : HasDerivAt (fun τ => Real.exp (-2 * τ)) (Real.exp (-2 * r) * (-2)) r := by
              have hd := ((hasDerivAt_id r).const_mul (-2 : ℝ)).exp
              simpa using hd
            have hm := h1'.mul h2'
            have hval : (deriv g r - 2 * (1 + g r)) * Real.exp (-2 * r) =
                deriv g r * Real.exp (-2 * r) + (1 + g r) * (Real.exp (-2 * r) * (-2)) := by ring
            exact hval.symm ▸ hm)
        have hpos : 0 < (deriv g c - 2 * (1 + g c)) * Real.exp (-2 * c) := by
          rw [hslope]; exact div_pos (by linarith) (by linarith)
        have hc_in : c ∈ Ipos := hpos_on_Ioc c ⟨hc.1, hc.2.le⟩
        have hE1c : (deriv g c) ^ 2 = (1 / 2) * (1 - (g c) ^ 2) ^ 2 := by
          have := hE1_const c hc_in; dsimp [E1] at this; linarith
        have hgc1 : |g c| ≤ 1 := hv'1 _
        have h1p : 0 ≤ 1 + g c := by linarith [(abs_le.mp hgc1).1]
        have hdgc_le : deriv g c ≤ 2 * (1 + g c) := by
          have hsq : (deriv g c) ^ 2 ≤ (2 * (1 + g c)) ^ 2 := by
            rw [hE1c]
            have hfac : (1 - (g c) ^ 2) ^ 2 = (1 + g c) ^ 2 * (1 - g c) ^ 2 := by ring
            rw [hfac]
            have h1m2 : (1 - g c) ^ 2 ≤ 4 := by
              nlinarith only [(abs_le.mp hgc1).1, (abs_le.mp hgc1).2]
            nlinarith only [h1m2, sq_nonneg (1 + g c)]
          nlinarith only [hsq, h1p, hc_in c Set.right_mem_uIcc]
        have hnp : (deriv g c - 2 * (1 + g c)) * Real.exp (-2 * c) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
        linarith
      dsimp [F] at hF_anti; rw [hga_eq_m1] at hF_anti
      have hzero_a : (1 + (-1 : ℝ)) * Real.exp (-2 * a) = 0 := by ring
      rw [hzero_a] at hF_anti
      have hpos : 0 < (1 + g s₀) * Real.exp (-2 * s₀) := mul_pos (by linarith) (Real.exp_pos _)
      linarith
    -- Therefore Ipos = Set.univ and E1(s) = 0 everywhere, giving O(R) energy!
    have hIpos_all (s : ℝ) : s ∈ Ipos :=
      if h : s₀ ≤ s then hIpos_right s h else hIpos_left s (le_of_not_ge h)
    refine ⟨4, by norm_num, fun R hR => ?_⟩
    rw [hv'_en R]
    have hpt_en (y : Plane) :
        1 / 2 * ‖∇ v' y‖ ^ 2 + doubleWell (v' y) = (deriv g (y 0)) ^ 2 := by
      have hy_eq : y = y 0 • e2 0 + y 1 • e2 1 := by ext i; fin_cases i <;> simp [e2]
      have hst := hstrip_Ipos (y 0) (hIpos_all (y 0)) (y 1)
      have hgn : ‖∇ v' y‖ ^ 2 = (part2 v' 0 y) ^ 2 + (part2 v' 1 y) ^ 2 := by
        let b := EuclideanSpace.basisFun (Fin 2) ℝ
        rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner, Fin.sum_univ_two]
        have h0 : b 0 = e2 0 := EuclideanSpace.basisFun_apply (Fin 2) ℝ 0
        have h1' : b 1 = e2 1 := EuclideanSpace.basisFun_apply (Fin 2) ℝ 1
        have hd0 : inner ℝ (∇ v' y) (e2 0) = part2 v' 0 y := by
          rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]; rfl
        have hd0' : inner ℝ (e2 0) (∇ v' y) = part2 v' 0 y := (real_inner_comm _ _).trans hd0
        have hd1 : inner ℝ (∇ v' y) (e2 1) = part2 v' 1 y := by
          rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]; rfl
        have hd1' : inner ℝ (e2 1) (∇ v' y) = part2 v' 1 y := (real_inner_comm _ _).trans hd1
        rw [h0, h1', hd0, hd0', hd1, hd1']; ring
      conv_lhs => rw [hgn, hy_eq, hst.1, hst.2.1, hst.2.2]
      have hE := hE1_const (y 0) (hIpos_all (y 0))
      rw [hC0_eq0] at hE; dsimp [E1] at hE; unfold doubleWell
      rw [zero_pow two_ne_zero, add_zero]
      linarith only [hE]
    have hdg_sq_le (s : ℝ) : (deriv g s) ^ 2 ≤ deriv g s := by
      have hE := hE1_const s (hIpos_all s)
      rw [hC0_eq0] at hE; dsimp [E1] at hE
      have hgs1 : |g s| ≤ 1 := hv'1 _
      have hsq1 : (g s) ^ 2 ≤ 1 := by
        have := sq_le_sq.mpr (show |g s| ≤ |(1 : ℝ)| by simpa using hgs1); simpa using this
      have h0 : 0 ≤ 1 - (g s) ^ 2 := by linarith only [hsq1]
      have hle1 : (1 - (g s) ^ 2) ^ 2 ≤ 1 := by nlinarith only [h0, sq_nonneg (g s)]
      have hdg_pos : 0 < deriv g s := (hIpos_all s) s Set.right_mem_uIcc
      have hdg_le1 : deriv g s ≤ 1 := by nlinarith only [hE, hle1, hdg_pos]
      nlinarith only [hdg_pos, hdg_le1]
    let boxR : Set Plane := {y | |y 0| ≤ R ∧ |y 1| ≤ R}
    have hball_sub : Metric.ball (0 : Plane) R ⊆ boxR := by
      intro y hy
      rw [Metric.mem_ball, dist_zero_right] at hy
      have hsq : (y 0) ^ 2 + (y 1) ^ 2 = ‖y‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
      have h0 : (y 0) ^ 2 ≤ R ^ 2 := by nlinarith only [hsq, hy, sq_nonneg (y 1), norm_nonneg y]
      have h1' : (y 1) ^ 2 ≤ R ^ 2 := by nlinarith only [hsq, hy, sq_nonneg (y 0), norm_nonneg y]
      refine ⟨?_, ?_⟩
      · rw [abs_le]; constructor <;> nlinarith only [h0, hR]
      · rw [abs_le]; constructor <;> nlinarith only [h1', hR]
    have hbox_meas : MeasurableSet boxR :=
      (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).abs continuous_const).measurableSet.inter
        (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).abs continuous_const).measurableSet
    have hbox_comp : IsCompact boxR := by
      apply (isCompact_closedBall (0 : Plane) (2 * R)).of_isClosed_subset
      · exact (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).abs continuous_const).inter
          (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).abs continuous_const)
      · intro y hy
        rw [mem_closedBall, dist_zero_right]
        have hsq : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
        have h0 : (y 0) ^ 2 ≤ R ^ 2 := by nlinarith [abs_le.mp hy.1]
        have h1' : (y 1) ^ 2 ≤ R ^ 2 := by nlinarith [abs_le.mp hy.2]
        nlinarith [norm_nonneg y]
    have hcont_en : Continuous (fun y : Plane => 1 / 2 * ‖∇ v' y‖ ^ 2 + doubleWell (v' y)) := by
      simp_rw [hpt_en]
      exact ((hg_c2.continuous_deriv (by norm_num)).comp
        (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)).pow 2
    have hbox_int : IntegrableOn (fun y : Plane => 1 / 2 * ‖∇ v' y‖ ^ 2 + doubleWell (v' y)) boxR :=
      hcont_en.continuousOn.integrableOn_compact hbox_comp
    calc
      (∫ y in Metric.ball (0 : Plane) R, (1 / 2 * ‖∇ v' y‖ ^ 2 + doubleWell (v' y)))
          ≤ ∫ y in boxR, (1 / 2 * ‖∇ v' y‖ ^ 2 + doubleWell (v' y)) :=
            setIntegral_mono_set hbox_int
              (Eventually.of_forall fun y => by dsimp only; rw [hpt_en y]; exact sq_nonneg _)
              (Eventually.of_forall hball_sub)
      _ = ∫ y : Plane, boxR.indicator (fun z => (deriv g (z 0)) ^ 2) y := by
            rw [← integral_indicator hbox_meas]; congr 1; funext y; simp only [Set.indicator]
            split_ifs <;> [exact hpt_en y; rfl]
      _ = ∫ s : ℝ, ∫ t : ℝ, boxR.indicator (fun z => (deriv g (z 0)) ^ 2) (s • e2 0 + t • e2 1) := by
            apply integral_plane_eq_prod
            have heq : boxR.indicator (fun z : Plane => (deriv g (z 0)) ^ 2) =
                boxR.indicator (fun y => 1 / 2 * ‖∇ v' y‖ ^ 2 + doubleWell (v' y)) := by
              funext y; simp only [Set.indicator]; split_ifs <;> [exact (hpt_en y).symm; rfl]
            rw [heq]; exact hbox_int.integrable_indicator hbox_meas
      _ = ∫ s : ℝ, (Set.Icc (-R) R).indicator (fun r => (deriv g r) ^ 2 * (2 * R)) s := by
            congr 1; funext s
            by_cases hs : s ∈ Set.Icc (-R) R
            · rw [Set.indicator_of_mem hs]
              have habs : |s| ≤ R := abs_le.mpr hs
              have hpt (t : ℝ) : boxR.indicator (fun z => (deriv g (z 0)) ^ 2) (s • e2 0 + t • e2 1) =
                  (Set.Icc (-R) R).indicator (fun _ => (deriv g s) ^ 2) t := by
                by_cases ht : t ∈ Set.Icc (-R) R
                · have hmem : s • e2 0 + t • e2 1 ∈ boxR := by
                    refine ⟨by simpa [e2] using habs, by simpa [e2] using abs_le.mpr ht⟩
                  rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ht]; simp [e2]
                · have hnmem : s • e2 0 + t • e2 1 ∉ boxR := fun h =>
                    ht (abs_le.mp (by simpa [e2] using h.2))
                  rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem ht]
              simp_rw [hpt, integral_indicator measurableSet_Icc, setIntegral_const, Measure.real_def,
                Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ R - (-R)), smul_eq_mul]
              ring
            · rw [Set.indicator_of_notMem hs]
              have h0 (t : ℝ) : boxR.indicator (fun z => (deriv g (z 0)) ^ 2) (s • e2 0 + t • e2 1) = 0 := by
                apply Set.indicator_of_notMem; intro h; exact hs (abs_le.mp (by simpa [e2] using h.1))
              simp_rw [h0, integral_zero]
      _ = (∫ s in (-R)..R, (deriv g s) ^ 2) * (2 * R) := by
            rw [integral_indicator measurableSet_Icc, integral_mul_const,
              intervalIntegral.integral_of_le (by linarith : -R ≤ R),
              MeasureTheory.integral_Icc_eq_integral_Ioc]
      _ ≤ (∫ s in (-R)..R, deriv g s) * (2 * R) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            exact intervalIntegral.integral_mono_on (by linarith)
              ((hg_c2.continuous_deriv (by norm_num)).pow 2 |>.intervalIntegrable _ _)
              ((hg_c2.continuous_deriv (by norm_num)).intervalIntegrable _ _)
              fun s _ => hdg_sq_le s
      _ = (g R - g (-R)) * (2 * R) := by
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
              (fun s _ => (hg_c2.differentiable (by norm_num) s).hasDerivAt)
              ((hg_c2.continuous_deriv (by norm_num)).intervalIntegrable _ _)]
      _ ≤ 4 * R := by
            have hR1 := abs_le.mp (hv'1 (R • e2 0 + t₀ • e2 1))
            have hmR1 := abs_le.mp (hv'1 ((-R) • e2 0 + t₀ • e2 1))
            dsimp [g] at *; nlinarith

/-
## Section 5: 3D Foliation Calibration, Slide Competitor, and Final Theorem
-/

private noncomputable def energy3 (u : Space → ℝ) (x : Space) : ℝ :=
  1 / 2 * ‖∇ u x‖ ^ 2 + doubleWell (u x)

private theorem energy3_nonneg (u : Space → ℝ) (x : Space) : 0 ≤ energy3 u x := by
  unfold energy3
  linarith [sq_nonneg ‖∇ u x‖, doubleWell_nonneg (u x)]

private theorem norm_grad3_sq_eq (u : Space → ℝ) (x : Space) :
    ‖∇ u x‖ ^ 2 = (part3 u 0 x) ^ 2 + (part3 u 1 x) ^ 2 + (part3 u 2 x) ^ 2 := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner, Fin.sum_univ_three]
  have hi (k : Fin 3) : b k = e3 k := EuclideanSpace.basisFun_apply (Fin 3) ℝ k
  have hd (k : Fin 3) : inner ℝ (∇ u x) (e3 k) = part3 u k x := by
    rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]; rfl
  have hd' (k : Fin 3) : inner ℝ (e3 k) (∇ u x) = part3 u k x := (real_inner_comm _ _).trans (hd k)
  rw [hi 0, hi 1, hi 2, hd 0, hd' 0, hd 1, hd' 1, hd 2, hd' 2]
  ring

private theorem foliation_shift_c1 {u w : Space → ℝ}
    (hu : DeGiorgi.IsBoundedSolution u) (hup : DeGiorgi.HasPositiveDeriv u)
    (hw_c1 : ContDiff ℝ 1 w)
    {t : ℝ} (ht : 0 < t)
    (hsand : ∀ x : Space, u x ≤ w x ∧ w x ≤ u (x + t • e3 0))
    {M : ℝ} (hsupp : ∀ x : Space, M ≤ ‖x‖ → w x = u x) :
    ∃ φ : Space → ℝ,
      (∀ x, φ x ∈ Set.Icc (0 : ℝ) t) ∧
      (∀ x, u (x + φ x • e3 0) = w x) ∧
      (∀ x, M ≤ ‖x‖ → φ x = 0) ∧
      ContDiff ℝ 1 φ ∧
      ∀ x, fderiv ℝ φ x =
        (part3 u 0 (x + φ x • e3 0))⁻¹ • (fderiv ℝ w x - fderiv ℝ u (x + φ x • e3 0)) := by
  have hv_pos : ∀ x : Space, 0 < part3 u 0 x := by
    intro x
    have h := hup x
    rwa [(hu.regular.differentiable (by norm_num) x).lineDeriv_eq_fderiv] at h
  have hline_mono (x : Space) : StrictMono (fun s : ℝ => u (x + s • e3 0)) :=
    strictMono_of_deriv_pos fun s => by
      rw [(line_deriv3 hu.regular x (e3 0) s).deriv]
      exact hv_pos _
  have hφ_ex (x : Space) : ∃ s ∈ Set.Icc (0 : ℝ) t, u (x + s • e3 0) = w x := by
    have hcont : ContinuousOn (fun s : ℝ => u (x + s • e3 0)) (Set.Icc 0 t) :=
      (hu.regular.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
    have hmem : w x ∈ Set.Icc (u (x + (0 : ℝ) • e3 0)) (u (x + t • e3 0)) := by
      simpa using hsand x
    obtain ⟨s, hs, heq⟩ := intermediate_value_Icc ht.le hcont hmem
    exact ⟨s, hs, heq⟩
  let φ : Space → ℝ := fun x => Classical.choose (hφ_ex x)
  have hφ_mem (x : Space) : φ x ∈ Set.Icc (0 : ℝ) t := (Classical.choose_spec (hφ_ex x)).1
  have hφ_eq (x : Space) : u (x + φ x • e3 0) = w x := (Classical.choose_spec (hφ_ex x)).2
  have hφ_zero_out (x : Space) (hx : M ≤ ‖x‖) : φ x = 0 := by
    apply (hline_mono x).injective
    simp [hφ_eq x, hsupp x hx]
  have hφ_cont : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro x₀
    rw [Metric.continuousAt_iff]
    intro ε hε
    let s₀ := φ x₀
    have hlt1 : u (x₀ + (s₀ - ε) • e3 0) < w x₀ := by
      rw [← hφ_eq x₀]; exact hline_mono x₀ (by linarith)
    have hlt2 : w x₀ < u (x₀ + (s₀ + ε) • e3 0) := by
      rw [← hφ_eq x₀]; exact hline_mono x₀ (by linarith)
    have hopen1 : IsOpen {x : Space | u (x + (s₀ - ε) • e3 0) < w x} :=
      isOpen_lt (hu.regular.continuous.comp (continuous_id.add continuous_const)) hw_c1.continuous
    have hopen2 : IsOpen {x : Space | w x < u (x + (s₀ + ε) • e3 0)} :=
      isOpen_lt hw_c1.continuous (hu.regular.continuous.comp (continuous_id.add continuous_const))
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hopen1.inter hopen2) x₀ ⟨hlt1, hlt2⟩
    refine ⟨δ, hδ, fun x hx => ?_⟩
    obtain ⟨h1', h2'⟩ := hball hx
    change u (x + (s₀ - ε) • e3 0) < w x at h1'
    change w x < u (x + (s₀ + ε) • e3 0) at h2'
    rw [← hφ_eq x] at h1' h2'
    have hs1 : s₀ - ε < φ x := (hline_mono x).lt_iff_lt.mp h1'
    have hs2 : φ x < s₀ + ε := (hline_mono x).lt_iff_lt.mp h2'
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  let Lφ : Space → Space →L[ℝ] ℝ := fun x =>
    (part3 u 0 (x + φ x • e3 0))⁻¹ • (fderiv ℝ w x - fderiv ℝ u (x + φ x • e3 0))
  have hφ_hasFDeriv (x : Space) : HasFDerivAt φ (Lφ x) x := by
    let p := x + φ x • e3 0
    let a := part3 u 0 p
    have ha : 0 < a := hv_pos p
    have ha' : part3 u 0 (x + φ x • e3 0) ≠ 0 := ha.ne'
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    let δf : Space → ℝ := fun h => φ (x + h) - φ x
    let Δp : Space → Space := fun h => h + δf h • e3 0
    have hΔp_eq (h : Space) : x + h + φ (x + h) • e3 0 = p + Δp h := by
      dsimp [p, Δp, δf]; module
    have hδ_lim : Tendsto δf (𝓝 0) (𝓝 0) := by
      have hadd : Tendsto (fun h : Space => x + h) (𝓝 (0 : Space)) (𝓝 x) := by
        simpa using (tendsto_const_nhds (x := x)).add (tendsto_id (x := 𝓝 (0 : Space)))
      have h1' : Tendsto (fun h : Space => φ (x + h)) (𝓝 (0 : Space)) (𝓝 (φ x)) :=
        hφ_cont.continuousAt.tendsto.comp hadd
      simpa [δf] using h1'.sub (tendsto_const_nhds (x := φ x))
    have hΔp_lim : Tendsto Δp (𝓝 0) (𝓝 0) := by
      simpa [Δp] using (tendsto_id (x := 𝓝 (0 : Space))).add (hδ_lim.smul tendsto_const_nhds)
    have hu_o := hasFDerivAt_iff_isLittleO_nhds_zero.mp ((hu.regular.differentiable (by norm_num) p).hasFDerivAt)
    have hw_o := hasFDerivAt_iff_isLittleO_nhds_zero.mp ((hw_c1.differentiable one_ne_zero x).hasFDerivAt)
    have hrem (h : Space) :
        a * (δf h - Lφ x h) =
        (w (x + h) - w x - fderiv ℝ w x h) - (u (p + Δp h) - u p - fderiv ℝ u p (Δp h)) := by
      have hL : a * Lφ x h = fderiv ℝ w x h - fderiv ℝ u p h := by
        dsimp [Lφ, a, p]
        simp only [smul_apply, sub_apply, smul_eq_mul]
        field_simp [ha']
      have hu_eq : u (p + Δp h) = w (x + h) := by rw [← hΔp_eq h, hφ_eq]
      have hup_eq : u p = w x := hφ_eq x
      have hfd_eq : fderiv ℝ u p (Δp h) = fderiv ℝ u p h + δf h * a := by
        dsimp [Δp, a, part3]
        rw [map_add, map_smul, smul_eq_mul]
      rw [hu_eq, hup_eq, hfd_eq]
      linear_combination -hL
    have hu_half : ∀ᶠ h in 𝓝 (0 : Space), ‖u (p + Δp h) - u p - fderiv ℝ u p (Δp h)‖ ≤ a / 2 * ‖Δp h‖ :=
      hΔp_lim.eventually (Asymptotics.isLittleO_iff.mp hu_o (by positivity : 0 < a / 2))
    have hw_one := Asymptotics.isLittleO_iff.mp hw_o (by norm_num : (0 : ℝ) < 1)
    let C := (‖fderiv ℝ w x - fderiv ℝ u p‖ + 1 + a / 2) / (a / 2)
    have hC0 : 0 ≤ C := by dsimp [C]; positivity
    have hδ_bigO : ∀ᶠ h in 𝓝 (0 : Space), ‖Δp h‖ ≤ (1 + C) * ‖h‖ := by
      filter_upwards [hu_half, hw_one] with h hu_h hw_h
      have hΔ_le : ‖Δp h‖ ≤ ‖h‖ + |δf h| := by
        calc
          ‖h + δf h • e3 0‖ ≤ ‖h‖ + ‖δf h • e3 0‖ := norm_add_le _ _
          _ = ‖h‖ + |δf h| := by
            rw [norm_smul, Real.norm_eq_abs, show ‖e3 0‖ = 1 by
              simp [e3, PiLp.norm_single]]
            ring
      have h1' : a * |δf h| ≤ |a * Lφ x h| + ‖w (x + h) - w x - fderiv ℝ w x h‖ +
          ‖u (p + Δp h) - u p - fderiv ℝ u p (Δp h)‖ := by
        have htri : |a * δf h| ≤ |a * Lφ x h| + |a * (δf h - Lφ x h)| := by
          have : a * δf h = a * Lφ x h + a * (δf h - Lφ x h) := by ring
          conv_lhs => rw [this]
          exact abs_add_le _ _
        rw [abs_mul, abs_of_pos ha, hrem h] at htri
        have habs2 : |(w (x + h) - w x - fderiv ℝ w x h) -
            (u (p + Δp h) - u p - fderiv ℝ u p (Δp h))| ≤
            ‖w (x + h) - w x - fderiv ℝ w x h‖ + ‖u (p + Δp h) - u p - fderiv ℝ u p (Δp h)‖ := by
          rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact abs_sub _ _
        linarith
      have hL_bd : |a * Lφ x h| ≤ ‖fderiv ℝ w x - fderiv ℝ u p‖ * ‖h‖ := by
        have hL : a * Lφ x h = (fderiv ℝ w x - fderiv ℝ u p) h := by
          dsimp [Lφ, a, p]; simp only [smul_apply, sub_apply, smul_eq_mul]; field_simp [ha']
        rw [hL, ← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      have hu_h' : ‖u (p + Δp h) - u p - fderiv ℝ u p (Δp h)‖ ≤ a / 2 * (‖h‖ + |δf h|) :=
        le_trans hu_h (mul_le_mul_of_nonneg_left hΔ_le (by linarith))
      have hw_h' : ‖w (x + h) - w x - fderiv ℝ w x h‖ ≤ ‖h‖ := by simpa using hw_h
      have hδ_le : |δf h| ≤ C * ‖h‖ := by
        dsimp [C]; rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : 0 < a / 2)]
        nlinarith
      linarith
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hε1 : 0 < c * a / 2 := by positivity
    have hε2 : 0 < c * a / (2 * (1 + C)) := by positivity
    have hw_ev := Asymptotics.isLittleO_iff.mp hw_o hε1
    have hu_ev : ∀ᶠ h in 𝓝 (0 : Space),
        ‖u (p + Δp h) - u p - fderiv ℝ u p (Δp h)‖ ≤ c * a / (2 * (1 + C)) * ‖Δp h‖ :=
      hΔp_lim.eventually (Asymptotics.isLittleO_iff.mp hu_o hε2)
    filter_upwards [hw_ev, hu_ev, hδ_bigO] with h hwh huh hΔh
    have ha_mul : a * ‖δf h - Lφ x h‖ ≤ c * a * ‖h‖ := by
      conv_lhs => rw [Real.norm_eq_abs, ← abs_of_pos ha, ← abs_mul, hrem h]
      have hsub : |(w (x + h) - w x - fderiv ℝ w x h) -
          (u (p + Δp h) - u p - fderiv ℝ u p (Δp h))| ≤
          ‖w (x + h) - w x - fderiv ℝ w x h‖ + ‖u (p + Δp h) - u p - fderiv ℝ u p (Δp h)‖ := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact abs_sub _ _
      have hu_bd : ‖u (p + Δp h) - u p - fderiv ℝ u p (Δp h)‖ ≤ c * a / 2 * ‖h‖ := by
        calc
          ‖u (p + Δp h) - u p - fderiv ℝ u p (Δp h)‖ ≤ c * a / (2 * (1 + C)) * ‖Δp h‖ := huh
          _ ≤ c * a / (2 * (1 + C)) * ((1 + C) * ‖h‖) :=
              mul_le_mul_of_nonneg_left hΔh hε2.le
          _ = c * a / 2 * ‖h‖ := by field_simp [(by linarith : (1 + C) ≠ 0)]
      calc
        |(w (x + h) - w x - fderiv ℝ w x h) - (u (p + Δp h) - u p - fderiv ℝ u p (Δp h))|
            ≤ ‖w (x + h) - w x - fderiv ℝ w x h‖ + ‖u (p + Δp h) - u p - fderiv ℝ u p (Δp h)‖ := hsub
        _ ≤ c * a / 2 * ‖h‖ + c * a / 2 * ‖h‖ := add_le_add hwh hu_bd
        _ = c * a * ‖h‖ := by ring
    have hle := (mul_le_mul_iff_right₀ ha).mp (show a * ‖δf h - Lφ x h‖ ≤ a * (c * ‖h‖) by linarith)
    simpa [δf] using hle
  have hφ_c1 : ContDiff ℝ 1 φ := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun x => (hφ_hasFDeriv x).differentiableAt, ?_⟩
    have heq : fderiv ℝ φ = Lφ := funext fun x => (hφ_hasFDeriv x).fderiv
    rw [heq]
    have hpath : Continuous (fun x : Space => x + φ x • e3 0) :=
      continuous_id.add (hφ_cont.smul continuous_const)
    have hfd_u : ContDiff ℝ 1 (fderiv ℝ u) := hu.regular.fderiv_right (by norm_num)
    have hp0c : Continuous (fun x : Space => part3 u 0 (x + φ x • e3 0)) :=
      (hfd_u.clm_apply contDiff_const).continuous.comp hpath
    exact (hp0c.inv₀ fun x => (hv_pos _).ne').smul
      ((hw_c1.continuous_fderiv one_ne_zero).sub (hfd_u.continuous.comp hpath))
  exact ⟨φ, hφ_mem, hφ_eq, hφ_zero_out, hφ_c1, fun x => (hφ_hasFDeriv x).fderiv⟩

set_option maxHeartbeats 1000000 in
private theorem foliation_energy_comparison {u w : Space → ℝ}
    (hu : DeGiorgi.IsBoundedSolution u) (hup : DeGiorgi.HasPositiveDeriv u)
    (hw_c1 : ContDiff ℝ 1 w)
    {t : ℝ} (ht : 0 < t)
    (hsand : ∀ x : Space, u x ≤ w x ∧ w x ≤ u (x + t • e3 0))
    {M : ℝ} (hM : 0 < M) (hsupp : ∀ x : Space, M ≤ ‖x‖ → w x = u x) :
    0 ≤ ∫ x : Space, (energy3 w x - energy3 u x) := by
  have hv_pos : ∀ x : Space, 0 < part3 u 0 x := by
    intro x
    have h := hup x
    rwa [(hu.regular.differentiable (by norm_num) x).lineDeriv_eq_fderiv] at h
  obtain ⟨φ, hφ_mem, hφ_eq, hφ_zero_out, hφ_c1, hφ_fderiv⟩ :=
    foliation_shift_c1 hu hup hw_c1 ht hsand hsupp
  have hφ_cont : Continuous φ := hφ_c1.continuous
  -- Calibration vector field H j x = ∫ s in 0..(φ x), part3 u j (x + s e₀) * part3 u 0 (x + s e₀)
  let F : Fin 3 → Space → ℝ → ℝ := fun j x s =>
    part3 u j (x + s • e3 0) * part3 u 0 (x + s • e3 0)
  let DF : Fin 3 → Fin 3 → Space → ℝ → ℝ := fun j k x s =>
    part32 u j k (x + s • e3 0) * part3 u 0 (x + s • e3 0) +
    part3 u j (x + s • e3 0) * part32 u 0 k (x + s • e3 0)
  let H : Fin 3 → Space → ℝ := fun j x => ∫ s in (0 : ℝ)..(φ x), F j x s
  have hp_c1 (j : Fin 3) : ContDiff ℝ 1 (part3 u j) :=
    (hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hp2_cont (j k : Fin 3) : Continuous (part32 u j k) :=
    ((hp_c1 j).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hF_cont (j : Fin 3) : Continuous (fun p : Space × ℝ => F j p.1 p.2) :=
    ((hp_c1 j).continuous.comp (continuous_fst.add (continuous_snd.smul continuous_const))).mul
      ((hp_c1 0).continuous.comp (continuous_fst.add (continuous_snd.smul continuous_const)))
  have hDF_cont (j k : Fin 3) : Continuous (fun p : Space × ℝ => DF j k p.1 p.2) :=
    (((hp2_cont j k).comp (continuous_fst.add (continuous_snd.smul continuous_const))).mul
      ((hp_c1 0).continuous.comp (continuous_fst.add (continuous_snd.smul continuous_const)))).add
      (((hp_c1 j).continuous.comp (continuous_fst.add (continuous_snd.smul continuous_const))).mul
        ((hp2_cont 0 k).comp (continuous_fst.add (continuous_snd.smul continuous_const))))
  -- Helper: x ↦ ∫ s in 0..(φ x), G(x, s) is continuous for continuous G
  have hint_param_cont {G : Space → ℝ → ℝ} (hG : Continuous (fun p : Space × ℝ => G p.1 p.2)) :
      Continuous (fun x : Space => ∫ s in (0 : ℝ)..(φ x), G x s) := by
    rw [continuous_iff_continuousAt]
    intro x₀
    rw [Metric.continuousAt_iff]
    intro ε hε
    let K : Set (Space × ℝ) := closedBall x₀ 1 ×ˢ Set.Icc 0 t
    have hK : IsCompact K := (isCompact_closedBall x₀ 1).prod isCompact_Icc
    obtain ⟨MG, hMG⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
    have hMG0 : 0 ≤ MG := (norm_nonneg _).trans (hMG (x₀, 0) ⟨mem_closedBall_self zero_le_one, ⟨le_rfl, ht.le⟩⟩)
    have hunif := hK.uniformContinuousOn_of_continuous hG.continuousOn
    rw [Metric.uniformContinuousOn_iff] at hunif
    obtain ⟨δ₁, hδ₁, hδ₁_bd⟩ := hunif (ε / (2 * (t + 1))) (by positivity)
    obtain ⟨δ₂, hδ₂, hδ₂_bd⟩ := Metric.continuousAt_iff.mp (hφ_cont.continuousAt (x := x₀))
      (ε / (2 * (MG + 1))) (by positivity)
    refine ⟨min 1 (min δ₁ δ₂), lt_min zero_lt_one (lt_min hδ₁ hδ₂), fun x hx => ?_⟩
    have hx1 : dist x x₀ < 1 := hx.trans_le (min_le_left _ _)
    have hxδ1 : dist x x₀ < δ₁ := hx.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hxδ2 : dist x x₀ < δ₂ := hx.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hGint (z : Space) (a b : ℝ) : IntervalIntegrable (fun s => G z s) volume a b :=
      (hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
    have hsplit : (∫ s in (0 : ℝ)..(φ x), G x s) - (∫ s in (0 : ℝ)..(φ x₀), G x₀ s) =
        (∫ s in (φ x₀)..(φ x), G x s) + (∫ s in (0 : ℝ)..(φ x₀), (G x s - G x₀ s)) := by
      have h1' := intervalIntegral.integral_add_adjacent_intervals (hGint x 0 (φ x₀)) (hGint x (φ x₀) (φ x))
      have h2' := intervalIntegral.integral_sub (hGint x 0 (φ x₀)) (hGint x₀ 0 (φ x₀))
      linarith
    rw [Real.dist_eq, hsplit]
    have hbd1 : |∫ s in (φ x₀)..(φ x), G x s| ≤ MG * |φ x - φ x₀| := by
      rw [← Real.norm_eq_abs]
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
      have hs_Icc : s ∈ Set.Icc 0 t := by
        have hsub : Set.uIoc (φ x₀) (φ x) ⊆ Set.uIcc (φ x₀) (φ x) := Set.uIoc_subset_uIcc
        have hmem := hsub hs
        rw [Set.mem_uIcc] at hmem
        rcases hmem with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · exact ⟨(hφ_mem x₀).1.trans h1', h2'.trans (hφ_mem x).2⟩
        · exact ⟨(hφ_mem x).1.trans h1', h2'.trans (hφ_mem x₀).2⟩
      exact hMG (x, s) ⟨mem_closedBall.mpr hx1.le, hs_Icc⟩
    have hbd1' : |∫ s in (φ x₀)..(φ x), G x s| < ε / 2 := by
      have hφ_d : |φ x - φ x₀| < ε / (2 * (MG + 1)) := by simpa [Real.dist_eq] using hδ₂_bd hxδ2
      calc
        |∫ s in (φ x₀)..(φ x), G x s| ≤ MG * |φ x - φ x₀| := hbd1
        _ ≤ (MG + 1) * |φ x - φ x₀| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ < (MG + 1) * (ε / (2 * (MG + 1))) := mul_lt_mul_of_pos_left hφ_d (by linarith)
        _ = ε / 2 := by field_simp [(by linarith : MG + 1 ≠ 0)]
    have hbd2 : |∫ s in (0 : ℝ)..(φ x₀), (G x s - G x₀ s)| ≤ (ε / (2 * (t + 1))) * φ x₀ := by
      rw [← Real.norm_eq_abs]
      have hle := intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / (2 * (t + 1)))
        (a := (0 : ℝ)) (b := φ x₀) (f := fun s => G x s - G x₀ s) fun s hs => by
          rw [Set.uIoc_of_le (hφ_mem x₀).1] at hs
          have hs_Icc : s ∈ Set.Icc 0 t := ⟨hs.1.le, hs.2.trans (hφ_mem x₀).2⟩
          have hd : dist (x, s) (x₀, s) < δ₁ := by
            rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; exact hxδ1
          have hb := hδ₁_bd (x, s) ⟨mem_closedBall.mpr hx1.le, hs_Icc⟩
            (x₀, s) ⟨mem_closedBall_self zero_le_one, hs_Icc⟩ hd
          exact (Real.dist_eq _ _ ▸ hb).le
      simpa [abs_of_nonneg (hφ_mem x₀).1] using hle
    have hbd2' : |∫ s in (0 : ℝ)..(φ x₀), (G x s - G x₀ s)| < ε / 2 := by
      calc
        |∫ s in (0 : ℝ)..(φ x₀), (G x s - G x₀ s)| ≤ (ε / (2 * (t + 1))) * φ x₀ := hbd2
        _ ≤ (ε / (2 * (t + 1))) * t := mul_le_mul_of_nonneg_left (hφ_mem x₀).2 (by positivity)
        _ < (ε / (2 * (t + 1))) * (t + 1) := mul_lt_mul_of_pos_left (by linarith) (by positivity)
        _ = ε / 2 := by field_simp [(by linarith : t + 1 ≠ 0)]
    calc
      |(∫ s in (φ x₀)..(φ x), G x s) + ∫ s in (0 : ℝ)..(φ x₀), (G x s - G x₀ s)|
          ≤ |∫ s in (φ x₀)..(φ x), G x s| + |∫ s in (0 : ℝ)..(φ x₀), (G x s - G x₀ s)| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hbd1' hbd2'
      _ = ε := by ring
  -- Construct explicit continuous Fréchet derivative LH j x of H j
  let coord3 : Fin 3 → Space →L[ℝ] ℝ := fun k =>
    ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.coord k).toContinuousLinearMap
  have hcoord3 (k : Fin 3) (v : Space) : coord3 k v = v k := by
    simp [coord3, Module.Basis.coord_apply, EuclideanSpace.basisFun_repr]
  let LH : Fin 3 → Space → Space →L[ℝ] ℝ := fun j x =>
    ∑ k : Fin 3, (F j x (φ x) * fderiv ℝ φ x (e3 k) + ∫ s in (0 : ℝ)..(φ x), DF j k x s) • coord3 k
  have hLH_apply (j : Fin 3) (x v : Space) :
      LH j x v = F j x (φ x) * fderiv ℝ φ x v +
        ∫ s in (0 : ℝ)..(φ x), ∑ k : Fin 3, DF j k x s * v k := by
    have hbasis : v = ∑ k : Fin 3, v k • e3 k := by
      ext i; fin_cases i <;> simp [Fin.sum_univ_three, e3]
    have hφ_exp : fderiv ℝ φ x v = ∑ k : Fin 3, v k * fderiv ℝ φ x (e3 k) := by
      conv_lhs => rw [hbasis]
      rw [map_sum]; refine Finset.sum_congr rfl fun k _ => by rw [map_smul, smul_eq_mul]
    have hint_k (k : Fin 3) : IntervalIntegrable (fun s => DF j k x s * v k) volume 0 (φ x) :=
      (((hDF_cont j k).comp (continuous_const.prodMk continuous_id)).mul continuous_const).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum fun k _ => hint_k k]
    dsimp [LH]
    simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, hcoord3, smul_eq_mul]
    rw [hφ_exp, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_mul_const]; ring
  have hH_hasFDeriv (j : Fin 3) (x : Space) : HasFDerivAt (H j) (LH j x) x := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro c hc
    -- Compact neighborhood K = closedBall x 1 × [0, t]
    let K : Set (Space × ℝ) := closedBall x 1 ×ˢ Set.Icc 0 t
    have hK : IsCompact K := (isCompact_closedBall x 1).prod isCompact_Icc
    -- Bound |φ(x+h) - φ(x)| ≤ (‖fderiv φ x‖ + 1) ‖h‖
    let Cφ := ‖fderiv ℝ φ x‖ + 1
    have hCφ : 0 < Cφ := by dsimp [Cφ]; linarith [norm_nonneg (fderiv ℝ φ x)]
    have hφ_o := hasFDerivAt_iff_isLittleO_nhds_zero.mp (hφ_c1.differentiable one_ne_zero x).hasFDerivAt
    have hφ_ev1 := Asymptotics.isLittleO_iff.mp hφ_o (by norm_num : (0 : ℝ) < 1)
    have hF_bd_ev := Asymptotics.isLittleO_iff.mp hφ_o (by positivity : 0 < c / (3 * (|F j x (φ x)| + 1)))
    -- Continuity of F j at (x, φ x)
    obtain ⟨δF, hδF, hF_close⟩ := Metric.continuousAt_iff.mp
      ((hF_cont j).continuousAt (x := (x, φ x))) (c / (3 * Cφ)) (by positivity)
    obtain ⟨δφ, hδφ, hφ_close⟩ := Metric.continuousAt_iff.mp (hφ_cont.continuousAt (x := x)) δF hδF
    -- Uniform continuity of DF j k on K
    have hunif_k (k : Fin 3) : ∃ δ > 0, ∀ p₁ ∈ K, ∀ p₂ ∈ K, dist p₁ p₂ < δ →
        |DF j k p₁.1 p₁.2 - DF j k p₂.1 p₂.2| < c / (9 * (t + 1)) := by
      have hu' := Metric.uniformContinuousOn_iff.mp
        (hK.uniformContinuousOn_of_continuous (hDF_cont j k).continuousOn)
        (c / (9 * (t + 1))) (by positivity)
      obtain ⟨δ, hδ, h⟩ := hu'
      exact ⟨δ, hδ, fun p₁ hp₁ p₂ hp₂ hd => by simpa [Real.dist_eq] using h p₁ hp₁ p₂ hp₂ hd⟩
    obtain ⟨δ0, hδ0, hDF0⟩ := hunif_k 0
    obtain ⟨δ1, hδ1, hDF1⟩ := hunif_k 1
    obtain ⟨δ2, hδ2, hDF2⟩ := hunif_k 2
    let δ := min 1 (min δF (min δφ (min δ0 (min δ1 δ2))))
    have hδ : 0 < δ := lt_min zero_lt_one (lt_min hδF (lt_min hδφ (lt_min hδ0 (lt_min hδ1 hδ2))))
    filter_upwards [Metric.ball_mem_nhds (0 : Space) hδ, hφ_ev1, hF_bd_ev] with h hh hφ1 hφF
    have hnorm_h : ‖h‖ < δ := by simpa [Metric.mem_ball, dist_zero_right] using hh
    have hnorm_1 : ‖h‖ < 1 := hnorm_h.trans_le (min_le_left _ _)
    have hnorm_δF : ‖h‖ < δF := hnorm_h.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hnorm_δφ : ‖h‖ < δφ :=
      hnorm_h.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hnorm_δ0 : ‖h‖ < δ0 :=
      hnorm_h.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))))
    have hnorm_δ1 : ‖h‖ < δ1 :=
      hnorm_h.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
    have hnorm_δ2 : ‖h‖ < δ2 :=
      hnorm_h.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
    have hFint (z : Space) (a b : ℝ) : IntervalIntegrable (fun s => F j z s) volume a b :=
      ((hF_cont j).comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
    have hDFint : IntervalIntegrable (fun s => ∑ k : Fin 3, DF j k x s * h k) volume 0 (φ x) :=
      (continuous_finsetSum _ fun k _ =>
        ((hDF_cont j k).comp (continuous_const.prodMk continuous_id)).mul continuous_const).intervalIntegrable _ _
    have hsplit : H j (x + h) - H j x - LH j x h =
        F j x (φ x) * (φ (x + h) - φ x - fderiv ℝ φ x h) +
        (∫ s in (φ x)..(φ (x + h)), (F j (x + h) s - F j x (φ x))) +
        (∫ s in (0 : ℝ)..(φ x), (F j (x + h) s - F j x s - ∑ k : Fin 3, DF j k x s * h k)) := by
      dsimp [H]
      rw [hLH_apply j x h]
      have h1' := intervalIntegral.integral_add_adjacent_intervals
        (hFint (x + h) 0 (φ x)) (hFint (x + h) (φ x) (φ (x + h)))
      have h2' := intervalIntegral.integral_sub (hFint (x + h) (φ x) (φ (x + h)))
        (intervalIntegrable_const (c := F j x (φ x)))
      have h2c : (∫ _ in (φ x)..(φ (x + h)), F j x (φ x)) = (φ (x + h) - φ x) * F j x (φ x) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      have h3' := intervalIntegral.integral_sub
        ((hFint (x + h) 0 (φ x)).sub (hFint x 0 (φ x))) hDFint
      have h4' := intervalIntegral.integral_sub (hFint (x + h) 0 (φ x)) (hFint x 0 (φ x))
      linarith
    -- Term 1 ≤ (c/3) ‖h‖
    have hT1 : |F j x (φ x) * (φ (x + h) - φ x - fderiv ℝ φ x h)| ≤ c / 3 * ‖h‖ := by
      rw [abs_mul, ← Real.norm_eq_abs (φ (x + h) - φ x - fderiv ℝ φ x h)]
      calc
        |F j x (φ x)| * ‖φ (x + h) - φ x - fderiv ℝ φ x h‖
            ≤ (|F j x (φ x)| + 1) * (c / (3 * (|F j x (φ x)| + 1)) * ‖h‖) :=
              mul_le_mul (by linarith) hφF (norm_nonneg _) (by positivity)
        _ = c / 3 * ‖h‖ := by field_simp [(by positivity : |F j x (φ x)| + 1 ≠ 0)]
    -- Term 2 ≤ (c/3) ‖h‖
    have hφ_diff_le : |φ (x + h) - φ x| ≤ Cφ * ‖h‖ := by
      have htri : |φ (x + h) - φ x| ≤ |fderiv ℝ φ x h| + |φ (x + h) - φ x - fderiv ℝ φ x h| := by
        have : φ (x + h) - φ x = fderiv ℝ φ x h + (φ (x + h) - φ x - fderiv ℝ φ x h) := by ring
        conv_lhs => rw [this]
        exact abs_add_le _ _
      have h1' : |fderiv ℝ φ x h| ≤ ‖fderiv ℝ φ x‖ * ‖h‖ := by
        rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      have h2' : |φ (x + h) - φ x - fderiv ℝ φ x h| ≤ ‖h‖ := by
        rw [← Real.norm_eq_abs]; simpa using hφ1
      dsimp [Cφ]; nlinarith
    have hd_xh : dist (x + h) x = ‖h‖ := by rw [dist_eq_norm, add_sub_cancel_left]
    have hT2 : |∫ s in (φ x)..(φ (x + h)), (F j (x + h) s - F j x (φ x))| ≤ c / 3 * ‖h‖ := by
      rw [← Real.norm_eq_abs]
      have hle := intervalIntegral.norm_integral_le_of_norm_le_const (C := c / (3 * Cφ))
        (a := φ x) (b := φ (x + h)) (f := fun s => F j (x + h) s - F j x (φ x)) fun s hs => by
          have hs_close : dist s (φ x) < δF := by
            have hmem := Set.uIoc_subset_uIcc hs
            have hφ_d : |φ (x + h) - φ x| < δF := by
              have hb := hφ_close (hd_xh.symm ▸ hnorm_δφ)
              simpa [Real.dist_eq] using hb
            rw [Real.dist_eq]
            rw [Set.mem_uIcc] at hmem
            rcases hmem with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
            · rw [abs_of_nonneg (by linarith)]
              have : φ (x + h) - φ x ≤ |φ (x + h) - φ x| := le_abs_self _
              linarith
            · rw [abs_of_nonpos (by linarith)]
              have : -(φ (x + h) - φ x) ≤ |φ (x + h) - φ x| := neg_le_abs _
              linarith
          have hd : dist (x + h, s) (x, φ x) < δF := by
            rw [Prod.dist_eq, max_lt_iff]
            exact ⟨hd_xh.symm ▸ hnorm_δF, hs_close⟩
          exact (Real.dist_eq _ _ ▸ hF_close hd).le
      calc
        ‖∫ s in (φ x)..(φ (x + h)), (F j (x + h) s - F j x (φ x))‖
            ≤ c / (3 * Cφ) * |φ (x + h) - φ x| := hle
        _ ≤ c / (3 * Cφ) * (Cφ * ‖h‖) := mul_le_mul_of_nonneg_left hφ_diff_le (by positivity)
        _ = c / 3 * ‖h‖ := by field_simp [hCφ.ne']
    -- Term 3 ≤ (c/3) ‖h‖ via MVT along θ ↦ x + θ • h
    have hT3 : |∫ s in (0 : ℝ)..(φ x), (F j (x + h) s - F j x s - ∑ k : Fin 3, DF j k x s * h k)| ≤
        c / 3 * ‖h‖ := by
      rw [← Real.norm_eq_abs]
      have hle := intervalIntegral.norm_integral_le_of_norm_le_const (C := c / (3 * (t + 1)) * ‖h‖)
        (a := (0 : ℝ)) (b := φ x)
        (f := fun s => F j (x + h) s - F j x s - ∑ k : Fin 3, DF j k x s * h k) fun s hs => by
          rw [Set.uIoc_of_le (hφ_mem x).1] at hs
          have hs_Icc : s ∈ Set.Icc 0 t := ⟨hs.1.le, hs.2.trans (hφ_mem x).2⟩
          let q : ℝ → ℝ := fun θ => F j (x + θ • h) s - θ * ∑ k : Fin 3, DF j k x s * h k
          have hq_d (θ : ℝ) :
              HasDerivAt q (∑ k : Fin 3, (DF j k (x + θ • h) s - DF j k x s) * h k) θ := by
            have hl : HasDerivAt (fun τ : ℝ => x + τ • h + s • e3 0) h θ := by
              simpa using (((hasDerivAt_id θ).smul_const h).const_add x).add_const (s • e3 0)
            have hd1 := ((hp_c1 j).differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt θ hl
            have hd2 := ((hp_c1 0).differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt θ hl
            have hmul := hd1.mul hd2
            have hlin := (hasDerivAt_id θ).mul_const (∑ k : Fin 3, DF j k x s * h k)
            have hsub := hmul.sub hlin
            have hbasis : h = ∑ k : Fin 3, h k • e3 k := by
              ext i; fin_cases i <;> simp [Fin.sum_univ_three, e3]
            have hval : fderiv ℝ (part3 u j) (x + θ • h + s • e3 0) h * part3 u 0 (x + θ • h + s • e3 0) +
                part3 u j (x + θ • h + s • e3 0) * fderiv ℝ (part3 u 0) (x + θ • h + s • e3 0) h -
                1 * ∑ k : Fin 3, DF j k x s * h k =
                ∑ k : Fin 3, (DF j k (x + θ • h) s - DF j k x s) * h k := by
              have hexp (i : Fin 3) : fderiv ℝ (part3 u i) (x + θ • h + s • e3 0) h =
                  ∑ k : Fin 3, part32 u i k (x + θ • h + s • e3 0) * h k := by
                rw [congrArg (fderiv ℝ (part3 u i) (x + θ • h + s • e3 0)) hbasis, map_sum]
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [map_smul, smul_eq_mul]
                exact mul_comm (h k) (part32 u i k (x + θ • h + s • e3 0))
              rw [hexp j, hexp 0, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib,
                one_mul, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun k _ => by dsimp [DF]; ring
            exact hval ▸ hsub
          obtain ⟨θ, hθ, hslope⟩ := exists_hasDerivAt_eq_slope q
            (fun r => ∑ k : Fin 3, (DF j k (x + r • h) s - DF j k x s) * h k) zero_lt_one
            (fun r _ => (hq_d r).continuousAt.continuousWithinAt)
            (fun r _ => hq_d r)
          have hq10 : q 1 - q 0 = F j (x + h) s - F j x s - ∑ k : Fin 3, DF j k x s * h k := by
            simp only [q, one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_zero]; ring
          rw [sub_zero, div_one, hq10] at hslope
          rw [← hslope, Real.norm_eq_abs]
          have hθ_mem : x + θ • h ∈ closedBall x 1 := by
            rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
              abs_of_pos hθ.1]
            nlinarith only [hθ.2, norm_nonneg h, hnorm_1]
          have hθ_dist : dist (x + θ • h, s) (x, s) ≤ ‖h‖ := by
            rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_eq_norm,
              add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hθ.1]
            nlinarith only [hθ.2, norm_nonneg h]
          have hhk (k : Fin 3) : |h k| ≤ ‖h‖ := by
            simpa [Real.norm_eq_abs] using PiLp.norm_apply_le h k
          have hDFk (k : Fin 3) : |DF j k (x + θ • h) s - DF j k x s| < c / (9 * (t + 1)) := by
            fin_cases k
            · exact hDF0 (x + θ • h, s) ⟨hθ_mem, hs_Icc⟩ (x, s) ⟨mem_closedBall_self zero_le_one, hs_Icc⟩ (hθ_dist.trans_lt hnorm_δ0)
            · exact hDF1 (x + θ • h, s) ⟨hθ_mem, hs_Icc⟩ (x, s) ⟨mem_closedBall_self zero_le_one, hs_Icc⟩ (hθ_dist.trans_lt hnorm_δ1)
            · exact hDF2 (x + θ • h, s) ⟨hθ_mem, hs_Icc⟩ (x, s) ⟨mem_closedBall_self zero_le_one, hs_Icc⟩ (hθ_dist.trans_lt hnorm_δ2)
          calc
            |∑ k : Fin 3, (DF j k (x + θ • h) s - DF j k x s) * h k|
                ≤ ∑ k : Fin 3, |(DF j k (x + θ • h) s - DF j k x s) * h k| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _k : Fin 3, (c / (9 * (t + 1)) * ‖h‖) := by
                refine Finset.sum_le_sum fun k _ => ?_
                rw [abs_mul]
                exact mul_le_mul (hDFk k).le (hhk k) (abs_nonneg _) (by positivity)
            _ = c / (3 * (t + 1)) * ‖h‖ := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
                field_simp [(by linarith : t + 1 ≠ 0)]
                ring
      calc
        ‖∫ s in (0 : ℝ)..(φ x), (F j (x + h) s - F j x s - ∑ k : Fin 3, DF j k x s * h k)‖
            ≤ c / (3 * (t + 1)) * ‖h‖ * |φ x - 0| := hle
        _ ≤ c / (3 * (t + 1)) * ‖h‖ * (t + 1) := by
            rw [sub_zero, abs_of_nonneg (hφ_mem x).1]
            exact mul_le_mul_of_nonneg_left (by linarith [(hφ_mem x).2]) (by positivity)
        _ = c / 3 * ‖h‖ := by field_simp [(by linarith : t + 1 ≠ 0)]
    rw [Real.norm_eq_abs, hsplit]
    have htri1 := abs_add_le
      (F j x (φ x) * (φ (x + h) - φ x - fderiv ℝ φ x h) +
        ∫ s in (φ x)..(φ (x + h)), (F j (x + h) s - F j x (φ x)))
      (∫ s in (0 : ℝ)..(φ x), (F j (x + h) s - F j x s - ∑ k : Fin 3, DF j k x s * h k))
    have htri2 := abs_add_le
      (F j x (φ x) * (φ (x + h) - φ x - fderiv ℝ φ x h))
      (∫ s in (φ x)..(φ (x + h)), (F j (x + h) s - F j x (φ x)))
    linarith
  have hH_c1 (j : Fin 3) : ContDiff ℝ 1 (H j) := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun x => (hH_hasFDeriv j x).differentiableAt, ?_⟩
    have heq : fderiv ℝ (H j) = LH j := funext fun x => (hH_hasFDeriv j x).fderiv
    rw [heq]
    refine continuous_finsetSum _ fun k _ => ?_
    have h1' : Continuous (fun x => F j x (φ x)) :=
      (hF_cont j).comp (continuous_id.prodMk hφ_cont)
    have h2' : Continuous (fun x => fderiv ℝ φ x (e3 k)) :=
      (hφ_c1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have h3' : Continuous (fun x => ∫ s in (0 : ℝ)..(φ x), DF j k x s) :=
      hint_param_cont (hDF_cont j k)
    exact ((h1'.mul h2').add h3').smul continuous_const
  have hH_supp (j : Fin 3) : HasCompactSupport (H j) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) M)
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    by_contra! hgt
    exact hx (by dsimp [H]; rw [hφ_zero_out x hgt.le, intervalIntegral.integral_same])
  -- Compute div H(x) = ∑ j, fderiv (H j) x (e3 j) and prove div H(x) ≤ energy3 w x - energy3 u x
  have hdiv_le (x : Space) :
      (∑ j : Fin 3, fderiv ℝ (H j) x (e3 j)) ≤ energy3 w x - energy3 u x := by
    let p := x + φ x • e3 0
    have hterm (j : Fin 3) :
        fderiv ℝ (H j) x (e3 j) =
        F j x (φ x) * fderiv ℝ φ x (e3 j) + ∫ s in (0 : ℝ)..(φ x), DF j j x s := by
      rw [(hH_hasFDeriv j x).fderiv, hLH_apply j x (e3 j)]
      congr 1
      apply intervalIntegral.integral_congr
      intro s _
      simp [e3]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    have hDF_int (j : Fin 3) : IntervalIntegrable (fun s => DF j j x s) volume 0 (φ x) :=
      ((hDF_cont j j).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_finsetSum fun j _ => hDF_int j]
    -- Boundary sum = ∇ u(p) · ∇ w(x) - ‖∇ u(p)‖²
    have hbdry : (∑ j : Fin 3, F j x (φ x) * fderiv ℝ φ x (e3 j)) =
        (∑ j : Fin 3, part3 u j p * part3 w j x) - ‖∇ u p‖ ^ 2 := by
      rw [norm_grad3_sq_eq u p]
      have hφ_ej (j : Fin 3) : F j x (φ x) * fderiv ℝ φ x (e3 j) =
          part3 u j p * part3 w j x - (part3 u j p) ^ 2 := by
        rw [hφ_fderiv x]
        dsimp [F, p, part3]
        simp only [smul_apply, sub_apply, smul_eq_mul]
        have hne := (hv_pos (x + φ x • e3 0)).ne'
        unfold part3 at hne
        field_simp [hne]
      simp_rw [hφ_ej, Fin.sum_univ_three]; ring
    -- Integral sum = energy3 u p - energy3 u x by FTC!
    have hint_eq : (∫ s in (0 : ℝ)..(φ x), ∑ j : Fin 3, DF j j x s) =
        energy3 u p - energy3 u x := by
      have hftc : (∫ s in (0 : ℝ)..(φ x), ∑ j : Fin 3, DF j j x s) =
          energy3 u (x + φ x • e3 0) - energy3 u (x + (0 : ℝ) • e3 0) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun s : ℝ => energy3 u (x + s • e3 0))
        · intro s _
          have heq_e : (fun τ : ℝ => energy3 u (x + τ • e3 0)) =
              fun τ => 1 / 2 * ((part3 u 0 (x + τ • e3 0)) ^ 2 + (part3 u 1 (x + τ • e3 0)) ^ 2 +
                (part3 u 2 (x + τ • e3 0)) ^ 2) + (1 - (u (x + τ • e3 0)) ^ 2) ^ 2 / 4 := by
            funext τ; unfold energy3 doubleWell; rw [norm_grad3_sq_eq]
          rw [heq_e]
          have hl : HasDerivAt (fun τ : ℝ => x + τ • e3 0) (e3 0) s := by
            simpa using ((hasDerivAt_id s).smul_const (e3 0)).const_add x
          have hdu := (hu.regular.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s hl
          have hdp (k : Fin 3) := ((hp_c1 k).differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt s hl
          have hkin := (((hdp 0).pow 2).add ((hdp 1).pow 2) |>.add ((hdp 2).pow 2)).const_mul (1 / 2 : ℝ)
          have hpot := ((((hdu.pow 2).const_sub (1 : ℝ)).pow 2).div_const (4 : ℝ))
          have htot := hkin.add hpot
          have hsymm (j : Fin 3) : part32 u j 0 (x + s • e3 0) = part32 u 0 j (x + s • e3 0) := by
            have h1' : part32 u j 0 (x + s • e3 0) = (fderiv ℝ (fderiv ℝ u) (x + s • e3 0) (e3 0)) (e3 j) := by
              unfold part32 part3
              rw [fderiv_clm_apply ((hu.regular.fderiv_right (by norm_num)).differentiable one_ne_zero _)
                (differentiableAt_const (e3 j))]; simp
            have h2' : part32 u 0 j (x + s • e3 0) = (fderiv ℝ (fderiv ℝ u) (x + s • e3 0) (e3 j)) (e3 0) := by
              unfold part32 part3
              rw [fderiv_clm_apply ((hu.regular.fderiv_right (by norm_num)).differentiable one_ne_zero _)
                (differentiableAt_const (e3 0))]; simp
            rw [h1', h2']
            exact (hu.regular.contDiffAt.isSymmSndFDerivAt (by simp)) (e3 0) (e3 j)
          have hlap_eq : part32 u 0 0 (x + s • e3 0) + part32 u 1 1 (x + s • e3 0) +
              part32 u 2 2 (x + s • e3 0) = (u (x + s • e3 0)) ^ 3 - u (x + s • e3 0) := by
            let b := EuclideanSpace.basisFun (Fin 3) ℝ
            have hlap := sum_second3 (u := u) b (x + s • e3 0)
            have hs' (k : Fin 3) : second3 u (x + s • e3 0) (b k) = part32 u k k (x + s • e3 0) := by
              have hbk : b k = e3 k := EuclideanSpace.basisFun_apply (Fin 3) ℝ k
              rw [hbk]; unfold part32 part3 second3
              rw [fderiv_clm_apply ((hu.regular.fderiv_right (by norm_num)).differentiable one_ne_zero _)
                (differentiableAt_const (e3 k))]; simp
            rw [hs' 0, hs' 1, hs' 2] at hlap
            have hsol := hu.solution (x + s • e3 0)
            linarith
          have hval : 1 / 2 * (2 * part3 u 0 (x + s • e3 0) ^ (2 - 1) * part32 u 0 0 (x + s • e3 0) +
                2 * part3 u 1 (x + s • e3 0) ^ (2 - 1) * part32 u 1 0 (x + s • e3 0) +
                2 * part3 u 2 (x + s • e3 0) ^ (2 - 1) * part32 u 2 0 (x + s • e3 0)) +
              2 * (1 - u (x + s • e3 0) ^ 2) ^ (2 - 1) * -(2 * u (x + s • e3 0) ^ (2 - 1) * part3 u 0 (x + s • e3 0)) / 4 =
              ∑ j : Fin 3, DF j j x s := by
            rw [Fin.sum_univ_three]
            dsimp [DF]
            rw [hsymm 1, hsymm 2]
            norm_num
            linear_combination -part3 u 0 (x + s • e3 0) * hlap_eq
          exact hval ▸ htot
        · exact (continuous_finsetSum _ fun j _ =>
            (hDF_cont j j).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
      simpa [p] using hftc
    rw [hbdry, hint_eq]
    unfold energy3
    rw [hφ_eq x, norm_grad3_sq_eq u p, norm_grad3_sq_eq w x, Fin.sum_univ_three]
    nlinarith [sq_nonneg (part3 w 0 x - part3 u 0 p),
      sq_nonneg (part3 w 1 x - part3 u 1 p),
      sq_nonneg (part3 w 2 x - part3 u 2 p)]
  -- Integrate div H ≤ energy3 w - energy3 u over R^3
  have hdiv_int (j : Fin 3) : Integrable (fun x : Space => fderiv ℝ (H j) x (e3 j)) :=
    (((hH_c1 j).continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hH_supp j).fderiv_apply ℝ (e3 j))
  have hdiff_int : Integrable (fun x : Space => energy3 w x - energy3 u x) := by
    have hcg (f : Space → ℝ) (hf : ContDiff ℝ 1 f) : Continuous (∇ f) :=
      (InnerProductSpace.toDual ℝ Space).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
    have hcont : Continuous (fun x : Space => energy3 w x - energy3 u x) :=
      ((continuous_const.mul ((hcg w hw_c1).norm.pow 2)).add
        (((continuous_const.sub (hw_c1.continuous.pow 2)).pow 2).div_const 4)).sub
      ((continuous_const.mul ((hcg u (hu.regular.of_le (by norm_num))).norm.pow 2)).add
        (((continuous_const.sub (hu.regular.continuous.pow 2)).pow 2).div_const 4))
    refine hcont.integrable_of_hasCompactSupport ?_
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) (M + 1))
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    by_contra! hgt
    have hev : w =ᶠ[𝓝 x] u := by
      have hopen : IsOpen {z : Space | M < ‖z‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds (by linarith : M < ‖x‖)] with z hz
      exact hsupp z hz.le
    have hfd : fderiv ℝ w x = fderiv ℝ u x := hev.fderiv_eq
    have hgx : ∇ w x = ∇ u x := by simp [gradient, hfd]
    exact hx (by change energy3 w x - energy3 u x = 0; unfold energy3; rw [hgx, hsupp x (by linarith)]; ring)
  have hsum_zero : (∫ x : Space, ∑ j : Fin 3, fderiv ℝ (H j) x (e3 j)) = 0 := by
    rw [integral_finsetSum _ fun j _ => hdiv_int j]
    exact Finset.sum_eq_zero fun j _ => integral_fderiv_eq_zero_of_compact3 (hH_c1 j) (hH_supp j) (e3 j)
  rw [← hsum_zero]
  exact integral_mono (integrable_finsetSum _ fun j _ => hdiv_int j) hdiff_int hdiv_le

private theorem slide_energy_bound {u : Space → ℝ}
    (hu : DeGiorgi.IsBoundedSolution u) (hup : DeGiorgi.HasPositiveDeriv u) :
    ∃ C_ann : ℝ, 0 ≤ C_ann ∧ ∀ (R t : ℝ), 1 ≤ R → 0 < t →
      (∫ x in Metric.ball (0 : Space) R, energy3 u x) ≤
        (∫ x in Metric.ball (0 : Space) R, energy3 (fun z => u (z + t • e3 0)) x) + C_ann * R ^ 2 := by
  obtain ⟨D₁, _, _, hD₁, _, _, h1, hgrad1, _, _, _, _⟩ := solution_c21_bounds hu
  obtain ⟨hζ_c1, hζ_bd, hζ0, hζ1, Mζ, hMζ0, hMζ⟩ := smoothStep_props
  let K_ann : ℝ := 1 / 2 * (D₁ + 2 * Mζ) ^ 2 + 1 / 4
  have hK_ann : 0 ≤ K_ann := by dsimp [K_ann]; positivity
  let V1 : ℝ := (volume (Metric.ball (0 : Space) 1)).toReal
  have hV1 : 0 ≤ V1 := ENNReal.toReal_nonneg
  refine ⟨26 * K_ann * V1, by positivity, fun R t hR ht => ?_⟩
  -- Smooth radial cutoff η(x) = smoothStep (‖x‖ - R)
  let η : Space → ℝ := fun x => smoothStep (‖x‖ - R)
  have hη_c1 : ContDiff ℝ 1 η := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ‖x‖ < 1 / 2
    · have hev : η =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        have hopen : IsOpen {z : Space | ‖z‖ < 1 / 2} := isOpen_lt continuous_norm continuous_const
        filter_upwards [hopen.mem_nhds hx] with z hz
        exact hζ0 (‖z‖ - R) (by linarith)
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · push Not at hx
      have hne : x ≠ 0 := fun h => by rw [h, norm_zero] at hx; norm_num at hx
      have hnorm_c1 : ContDiffAt ℝ 1 (fun z : Space => ‖z‖) x := by
        have hsq : ContDiffAt ℝ 1 (fun z : Space => inner ℝ z z) x :=
          (contDiff_id.inner ℝ contDiff_id).contDiffAt
        have hpos : inner ℝ x x ≠ 0 := by
          rw [real_inner_self_eq_norm_sq]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
        have hsqrt := hsq.sqrt hpos
        have heq : (fun z : Space => Real.sqrt (inner ℝ z z)) = fun z => ‖z‖ :=
          funext fun z => by rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)]
        exact heq ▸ hsqrt
      exact hζ_c1.contDiffAt.comp x (hnorm_c1.sub contDiffAt_const)
  have hη_grad_bd (x : Space) : ‖∇ η x‖ ≤ Mζ := by
    by_cases hx : ‖x‖ < 1 / 2
    · have hev : η =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        have hopen : IsOpen {z : Space | ‖z‖ < 1 / 2} := isOpen_lt continuous_norm continuous_const
        filter_upwards [hopen.mem_nhds hx] with z hz
        exact hζ0 (‖z‖ - R) (by linarith)
      have hfd : fderiv ℝ η x = 0 := by rw [hev.fderiv_eq]; exact fderiv_const_apply (1 : ℝ)
      simp [gradient, hfd, hMζ0]
    · push Not at hx
      have hnx_pos : 0 < ‖x‖ := by linarith
      have hfd_norm : HasFDerivAt (fun z : Space => ‖z‖)
          ((‖x‖⁻¹ : ℝ) • InnerProductSpace.toDual ℝ Space x) x := by
        have h1' : HasFDerivAt (fun z : Space => inner ℝ z z)
            ((2 : ℝ) • InnerProductSpace.toDual ℝ Space x) x := by
          have h := (hasFDerivAt_id x).inner ℝ (hasFDerivAt_id x)
          have hf : fderiv ℝ (fun z : Space => inner ℝ z z) x =
              (2 : ℝ) • InnerProductSpace.toDual ℝ Space x := by
            change fderiv ℝ (fun z : Space => inner ℝ (id z) (id z)) x = _
            rw [h.fderiv]
            ext v
            simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
              ContinuousLinearMap.id_apply, fderivInnerCLM_apply, smul_apply,
              InnerProductSpace.toDual_apply_apply, smul_eq_mul, id_eq]
            rw [real_inner_comm v x]; ring
          exact hf ▸ h.differentiableAt.hasFDerivAt
        have hpos : inner ℝ x x ≠ 0 := by rw [real_inner_self_eq_norm_sq]; positivity
        have hsq := (Real.hasDerivAt_sqrt hpos).comp_hasFDerivAt (f := fun z : Space => inner ℝ z z) x h1'
        have heq : (Real.sqrt ∘ fun z : Space => inner ℝ z z) = fun z => ‖z‖ :=
          funext fun z => by simp [Real.sqrt_sq (norm_nonneg z)]
        have hLeq : (1 / (2 * Real.sqrt (inner ℝ x x))) • ((2 : ℝ) • InnerProductSpace.toDual ℝ Space x) =
            (‖x‖⁻¹ : ℝ) • InnerProductSpace.toDual ℝ Space x := by
          rw [smul_smul, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg x)]
          congr 1; field_simp [hnx_pos.ne']
        exact hLeq ▸ (heq ▸ hsq)
      have hfd_η : HasFDerivAt η
          ((deriv smoothStep (‖x‖ - R) * ‖x‖⁻¹) • InnerProductSpace.toDual ℝ Space x) x := by
        have h := ((hζ_c1.differentiable one_ne_zero (‖x‖ - R)).hasDerivAt).comp_hasFDerivAt x
          (hfd_norm.sub_const R)
        have hLeq : deriv smoothStep (‖x‖ - R) • ((‖x‖⁻¹ : ℝ) • InnerProductSpace.toDual ℝ Space x) =
            (deriv smoothStep (‖x‖ - R) * ‖x‖⁻¹) • InnerProductSpace.toDual ℝ Space x := by
          rw [smul_smul]
        exact hLeq ▸ h
      have hgn : ‖∇ η x‖ = ‖fderiv ℝ η x‖ := (InnerProductSpace.toDual ℝ Space).symm.norm_map _
      rw [hgn, hfd_η.fderiv, norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hnx_pos,
        (InnerProductSpace.toDual ℝ Space).norm_map]
      have hcancel : |deriv smoothStep (‖x‖ - R)| * ‖x‖⁻¹ * ‖x‖ = |deriv smoothStep (‖x‖ - R)| := by
        field_simp [hnx_pos.ne']
      rw [hcancel]; exact hMζ (‖x‖ - R)
  -- Slide competitor w(x) = (1 - η(x)) u(x) + η(x) u(x + t e₀)
  let ut : Space → ℝ := fun z => u (z + t • e3 0)
  let w : Space → ℝ := fun x => (1 - η x) * u x + η x * ut x
  have hut_c1 : ContDiff ℝ 1 ut :=
    (hu.regular.of_le (by norm_num)).comp (contDiff_id.add contDiff_const)
  have hw_c1 : ContDiff ℝ 1 w :=
    ((contDiff_const.sub hη_c1).mul (hu.regular.of_le (by norm_num))).add (hη_c1.mul hut_c1)
  have hu_le_ut (x : Space) : u x ≤ ut x := by
    have hmono : StrictMono (fun s : ℝ => u (x + s • e3 0)) :=
      strictMono_of_deriv_pos fun s => by
        rw [(line_deriv3 hu.regular x (e3 0) s).deriv]
        have h := hup (x + s • e3 0)
        rwa [(hu.regular.differentiable (by norm_num) _).lineDeriv_eq_fderiv] at h
    simpa [ut] using (hmono ht).le
  have hsand (x : Space) : u x ≤ w x ∧ w x ≤ ut x := by
    obtain ⟨h0, h1'⟩ := hζ_bd (‖x‖ - R)
    have hle := hu_le_ut x
    dsimp [w]; constructor <;> nlinarith
  have hw_out (x : Space) (hx : R + 1 ≤ ‖x‖) : w x = u x := by
    have hη0 : η x = 0 := hζ1 (‖x‖ - R) (by linarith)
    simp [w, hη0]
  have hw_in (x : Space) (hx : ‖x‖ ≤ R) : w x = ut x := by
    have hη1 : η x = 1 := hζ0 (‖x‖ - R) (by linarith)
    simp [w, hη1]
  have hcmp := foliation_energy_comparison hu hup hw_c1 ht hsand (M := R + 1) (by linarith) hw_out
  -- Bound energy3 w x ≤ K_ann everywhere
  have hw_en_le (x : Space) : energy3 w x ≤ K_ann := by
    have hw_abs : |w x| ≤ 1 := by
      have h1u := abs_le.mp (h1 x)
      have h1ut := abs_le.mp (h1 (x + t • e3 0))
      have hs := hsand x
      rw [abs_le]; constructor <;> linarith
    have hdw : doubleWell (w x) ≤ 1 / 4 := doubleWell_le_quarter hw_abs
    have hgw : ‖∇ w x‖ ≤ D₁ + 2 * Mζ := by
      have hdu := (hu.regular.differentiable (by norm_num) x).hasFDerivAt
      have hdut := (hut_c1.differentiable one_ne_zero x).hasFDerivAt
      have hdη := (hη_c1.differentiable one_ne_zero x).hasFDerivAt
      have hfd : fderiv ℝ w x =
          (1 - η x) • fderiv ℝ u x + η x • fderiv ℝ ut x + (ut x - u x) • fderiv ℝ η x := by
        have h := (((hdη.const_sub 1).mul hdu).add (hdη.mul hdut)).fderiv
        change fderiv ℝ w x = _ at h
        rw [h]; ext v; simp only [add_apply, smul_apply, neg_apply, smul_eq_mul]; ring
      have hfd_ut : fderiv ℝ ut x = fderiv ℝ u (x + t • e3 0) := by
        have h := ((hu.regular.differentiable (by norm_num) (x + t • e3 0)).hasFDerivAt.comp x
          ((hasFDerivAt_id x).add_const (t • e3 0))).fderiv
        change fderiv ℝ ut x = (fderiv ℝ u (x + t • e3 0)).comp (ContinuousLinearMap.id ℝ Space) at h
        simpa using h
      have hgn : ‖∇ w x‖ = ‖fderiv ℝ w x‖ := (InnerProductSpace.toDual ℝ Space).symm.norm_map _
      have hgn_η : ‖fderiv ℝ η x‖ = ‖∇ η x‖ := ((InnerProductSpace.toDual ℝ Space).symm.norm_map _).symm
      rw [hgn, hfd, hfd_ut]
      obtain ⟨hη0, hη1⟩ := hζ_bd (‖x‖ - R)
      have hdiff_le : |ut x - u x| ≤ 2 := by
        have h1u := abs_le.mp (h1 x)
        have h1ut := abs_le.mp (h1 (x + t • e3 0))
        rw [abs_le]; constructor <;> linarith
      calc
        ‖(1 - η x) • fderiv ℝ u x + η x • fderiv ℝ u (x + t • e3 0) + (ut x - u x) • fderiv ℝ η x‖
            ≤ ‖(1 - η x) • fderiv ℝ u x + η x • fderiv ℝ u (x + t • e3 0)‖ +
              ‖(ut x - u x) • fderiv ℝ η x‖ := norm_add_le _ _
        _ ≤ ‖(1 - η x) • fderiv ℝ u x‖ + ‖η x • fderiv ℝ u (x + t • e3 0)‖ +
              ‖(ut x - u x) • fderiv ℝ η x‖ :=
              add_le_add_left (norm_add_le _ _) _
        _ = (1 - η x) * ‖fderiv ℝ u x‖ + η x * ‖fderiv ℝ u (x + t • e3 0)‖ +
              |ut x - u x| * ‖∇ η x‖ := by
            rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by linarith), abs_of_nonneg hη0, hgn_η]
        _ ≤ (1 - η x) * D₁ + η x * D₁ + 2 * Mζ := by
            have h1' : (1 - η x) * ‖fderiv ℝ u x‖ ≤ (1 - η x) * D₁ :=
              mul_le_mul_of_nonneg_left (hgrad1 x) (by linarith)
            have h2' : η x * ‖fderiv ℝ u (x + t • e3 0)‖ ≤ η x * D₁ :=
              mul_le_mul_of_nonneg_left (hgrad1 _) hη0
            have h3' : |ut x - u x| * ‖∇ η x‖ ≤ 2 * Mζ :=
              mul_le_mul hdiff_le (hη_grad_bd x) (norm_nonneg _) (by norm_num)
            linarith
        _ = D₁ + 2 * Mζ := by ring
    unfold energy3; dsimp [K_ann]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hgw 2
    linarith
  -- Restrict integral of (energy3 w - energy3 u) to ball 0 (R + 2) and split at ball 0 R
  have hcg (f : Space → ℝ) (hf : ContDiff ℝ 1 f) : Continuous (∇ f) :=
    (InnerProductSpace.toDual ℝ Space).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
  have hen_cont (f : Space → ℝ) (hf : ContDiff ℝ 1 f) : Continuous (energy3 f) :=
    (continuous_const.mul ((hcg f hf).norm.pow 2)).add
      (((continuous_const.sub (hf.continuous.pow 2)).pow 2).div_const 4)
  have hzero_out : ∀ x ∉ Metric.ball (0 : Space) (R + 2), energy3 w x - energy3 u x = 0 := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hx
    have hev : w =ᶠ[𝓝 x] u := by
      have hopen : IsOpen {z : Space | R + 1 < ‖z‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds (by linarith : R + 1 < ‖x‖)] with z hz
      exact hw_out z hz.le
    have hgx : ∇ w x = ∇ u x := by simp [gradient, hev.fderiv_eq]
    unfold energy3; rw [hgx, hw_out x (by linarith)]; ring
  have hEq_ball : (∫ x : Space, (energy3 w x - energy3 u x)) =
      ∫ x in Metric.ball (0 : Space) (R + 2), (energy3 w x - energy3 u x) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero_out).symm
  rw [hEq_ball] at hcmp
  have hsub : Metric.ball (0 : Space) R ⊆ Metric.ball (0 : Space) (R + 2) :=
    Metric.ball_subset_ball (by linarith)
  have hint_big : IntegrableOn (fun x => energy3 w x - energy3 u x) (Metric.ball (0 : Space) (R + 2)) :=
    (((hen_cont w hw_c1).sub (hen_cont u (hu.regular.of_le (by norm_num)))).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have hsplit : (∫ x in Metric.ball (0 : Space) (R + 2), (energy3 w x - energy3 u x)) =
      (∫ x in Metric.ball (0 : Space) R, (energy3 w x - energy3 u x)) +
      (∫ x in Metric.ball (0 : Space) (R + 2) \ Metric.ball (0 : Space) R,
        (energy3 w x - energy3 u x)) := by
    have hun := Set.union_sdiff_cancel hsub
    conv_lhs => rw [← hun]
    exact setIntegral_union disjoint_sdiff_self_right
      (measurableSet_ball.diff measurableSet_ball)
      (hint_big.mono_set hsub) (hint_big.mono_set Set.sdiff_subset)
  have hinner : (∫ x in Metric.ball (0 : Space) R, (energy3 w x - energy3 u x)) =
      (∫ x in Metric.ball (0 : Space) R, energy3 ut x) -
      (∫ x in Metric.ball (0 : Space) R, energy3 u x) := by
    have hcongr : (∫ x in Metric.ball (0 : Space) R, (energy3 w x - energy3 u x)) =
        ∫ x in Metric.ball (0 : Space) R, (energy3 ut x - energy3 u x) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      have hopen : IsOpen (Metric.ball (0 : Space) R) := Metric.isOpen_ball
      have hev : w =ᶠ[𝓝 x] ut := by
        filter_upwards [hopen.mem_nhds hx] with z hz
        exact hw_in z (by rw [Metric.mem_ball, dist_zero_right] at hz; exact hz.le)
      have hgx : ∇ w x = ∇ ut x := by simp [gradient, hev.fderiv_eq]
      have hwx : w x = ut x := hw_in x (by rw [Metric.mem_ball, dist_zero_right] at hx; exact hx.le)
      dsimp only; unfold energy3; rw [hgx, hwx]
    rw [hcongr]
    exact integral_sub
      (((hen_cont ut hut_c1).continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set
        ball_subset_closedBall)
      (((hen_cont u (hu.regular.of_le (by norm_num))).continuousOn.integrableOn_compact
        (isCompact_closedBall _ _)).mono_set ball_subset_closedBall)
  have hann_le : (∫ x in Metric.ball (0 : Space) (R + 2) \ Metric.ball (0 : Space) R,
      (energy3 w x - energy3 u x)) ≤ 26 * K_ann * V1 * R ^ 2 := by
    have hvol_ball (r : ℝ) (hr : 0 ≤ r) :
        (volume (Metric.ball (0 : Space) r)).toReal = r ^ 3 * V1 := by
      have h := Measure.addHaar_ball (μ := (volume : Measure Space)) (x := (0 : Space)) (r := r)
      have hdim : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
      rw [hdim] at h
      rw [h hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ r ^ 3)]
    have hvol_ann : (volume (Metric.ball (0 : Space) (R + 2) \ Metric.ball (0 : Space) R)).toReal =
        ((R + 2) ^ 3 - R ^ 3) * V1 := by
      rw [measure_sdiff hsub measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne,
        ENNReal.toReal_sub_of_le (measure_mono hsub) measure_ball_lt_top.ne,
        hvol_ball (R + 2) (by linarith), hvol_ball R (by linarith)]
      ring
    calc
      (∫ x in Metric.ball (0 : Space) (R + 2) \ Metric.ball (0 : Space) R,
          (energy3 w x - energy3 u x))
          ≤ ∫ _ in Metric.ball (0 : Space) (R + 2) \ Metric.ball (0 : Space) R, K_ann := by
            apply setIntegral_mono_on (hint_big.mono_set Set.sdiff_subset)
              (integrableOn_const (hs := (measure_mono Set.sdiff_subset |>.trans_lt measure_ball_lt_top).ne))
              (measurableSet_ball.diff measurableSet_ball)
            intro x _
            linarith [hw_en_le x, energy3_nonneg u x]
      _ = ((R + 2) ^ 3 - R ^ 3) * V1 * K_ann := by
            rw [setIntegral_const, Measure.real_def, hvol_ann, smul_eq_mul]
      _ ≤ 26 * K_ann * V1 * R ^ 2 := by
            have hpoly : (R + 2) ^ 3 - R ^ 3 ≤ 26 * R ^ 2 := by nlinarith
            have hnn : 0 ≤ V1 * K_ann := mul_nonneg hV1 hK_ann
            nlinarith
  linarith

end OMA.DeGiorgiEnergy3

open EuclideanGeometry InnerProductSpace Metric Filter Set MeasureTheory OMA.DeGiorgiEnergy3 in
open scoped Gradient Laplacian Topology in
theorem OMA.solution : OMA.R_DeGiorgi_DeGiorgi_three_R1.H1 := by
  intro u i hu hup
  obtain ⟨D₁, _, _, hD₁, _, _, h1, hgrad1, _, _, _, _⟩ := solution_c21_bounds hu
  obtain ⟨t, u_plus, ht_pos, ht_top, hup_sol, hup_abs, hu_unif, hp_unif, hp0_unif⟩ :=
    exists_limit_profile hu hup
  have hup_grad_bd : ∀ y : Plane, ‖∇ u_plus y‖ ≤ D₁ := by
    intro y
    have hlim0 := (hp_unif 0 {embed 0 y} isCompact_singleton).tendsto_at (Set.mem_singleton _)
    have hlim1 := (hp_unif 1 {embed 0 y} isCompact_singleton).tendsto_at (Set.mem_singleton _)
    have hproj : proj2 (embed 0 y) = y := by ext k; fin_cases k <;> simp [proj2, embed, e3, e2]
    rw [hproj] at hlim0 hlim1
    have hnorm2 : ‖∇ u_plus y‖ ^ 2 = (fderiv ℝ u_plus y (e2 0)) ^ 2 + (fderiv ℝ u_plus y (e2 1)) ^ 2 := by
      let b := EuclideanSpace.basisFun (Fin 2) ℝ
      rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner, Fin.sum_univ_two]
      have h0 : b 0 = e2 0 := EuclideanSpace.basisFun_apply (Fin 2) ℝ 0
      have h1' : b 1 = e2 1 := EuclideanSpace.basisFun_apply (Fin 2) ℝ 1
      have hd0 : inner ℝ (∇ u_plus y) (e2 0) = fderiv ℝ u_plus y (e2 0) := by
        rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]
      have hd0' : inner ℝ (e2 0) (∇ u_plus y) = fderiv ℝ u_plus y (e2 0) := (real_inner_comm _ _).trans hd0
      have hd1 : inner ℝ (∇ u_plus y) (e2 1) = fderiv ℝ u_plus y (e2 1) := by
        rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]
      have hd1' : inner ℝ (e2 1) (∇ u_plus y) = fderiv ℝ u_plus y (e2 1) := (real_inner_comm _ _).trans hd1
      rw [h0, h1', hd0, hd0', hd1, hd1']; ring
    have hlim_sq : Tendsto (fun n => (part3 u 1 (embed 0 y + t n • e3 0)) ^ 2 +
        (part3 u 2 (embed 0 y + t n • e3 0)) ^ 2) atTop (𝓝 (‖∇ u_plus y‖ ^ 2)) := by
      rw [hnorm2]; exact (hlim0.pow 2).add (hlim1.pow 2)
    have hsq_le : ‖∇ u_plus y‖ ^ 2 ≤ D₁ ^ 2 := by
      apply le_of_tendsto hlim_sq
      refine Filter.Eventually.of_forall fun n => ?_
      have h3 := norm_grad3_sq_eq u (embed 0 y + t n • e3 0)
      have hgn : ‖∇ u (embed 0 y + t n • e3 0)‖ = ‖fderiv ℝ u (embed 0 y + t n • e3 0)‖ :=
        (InnerProductSpace.toDual ℝ Space).symm.norm_map _
      have hle : ‖∇ u (embed 0 y + t n • e3 0)‖ ^ 2 ≤ D₁ ^ 2 := by
        rw [hgn]; exact pow_le_pow_left₀ (norm_nonneg _) (hgrad1 _) 2
      linarith [sq_nonneg (part3 u 0 (embed 0 y + t n • e3 0))]
    nlinarith [norm_nonneg (∇ u_plus y)]
  have hup_stab : ∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      0 ≤ ∫ y : Plane, (‖∇ ψ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (ψ y) ^ 2) :=
    fun ψ hψ hψc => stability2_of_limit hu hup hu_unif hψ hψc
  obtain ⟨C₂, hC₂, hlin⟩ := stable2_energy_linear_growth hup_sol hup_abs hD₁ hup_grad_bd hup_stab
  obtain ⟨C_ann, hC_ann, hslide⟩ := slide_energy_bound hu hup
  refine ⟨2 * (2 * C₂ + C_ann), fun R hR => ?_⟩
  -- Pass to the limit t = t_n -> ∞ in slide_energy_bound
  let e_plus : Plane → ℝ := fun y => 1 / 2 * ‖∇ u_plus y‖ ^ 2 + doubleWell (u_plus y)
  have he_plus_cont : Continuous e_plus :=
    (continuous_const.mul (((InnerProductSpace.toDual ℝ Plane).symm.continuous.comp
      ((hup_sol.regular.of_le (by norm_num)).continuous_fderiv one_ne_zero)).norm.pow 2)).add
    (((continuous_const.sub (hup_sol.regular.continuous.pow 2)).pow 2).div_const 4)
  have hlim_ball :
      Filter.Tendsto (fun n => ∫ x in Metric.ball (0 : Space) R, energy3 (fun z => u (z + t n • e3 0)) x)
        Filter.atTop (nhds (∫ x in Metric.ball (0 : Space) R, e_plus (proj2 x))) := by
    let bound : Space → ℝ := fun _ => 1 / 2 * D₁ ^ 2 + 1 / 4
    refine MeasureTheory.tendsto_integral_of_dominated_convergence bound ?_
      (MeasureTheory.integrableOn_const (hs := measure_ball_lt_top.ne)) ?_ ?_
    · intro n
      have hcn : ContDiff ℝ 1 (fun z : Space => u (z + t n • e3 0)) :=
        (hu.regular.of_le (by norm_num)).comp (contDiff_id.add contDiff_const)
      exact ((continuous_const.mul (((InnerProductSpace.toDual ℝ Space).symm.continuous.comp
        (hcn.continuous_fderiv one_ne_zero)).norm.pow 2)).add
        (((continuous_const.sub (hcn.continuous.pow 2)).pow 2).div_const 4)).aestronglyMeasurable
    · intro n
      refine Filter.Eventually.of_forall fun x => ?_
      have hfd_shift : fderiv ℝ (fun z : Space => u (z + t n • e3 0)) x =
          fderiv ℝ u (x + t n • e3 0) := by
        have h := ((hu.regular.differentiable (by norm_num) (x + t n • e3 0)).hasFDerivAt.comp x
          ((hasFDerivAt_id x).add_const (t n • e3 0))).fderiv
        change fderiv ℝ (fun z : Space => u (z + t n • e3 0)) x =
          (fderiv ℝ u (x + t n • e3 0)).comp (ContinuousLinearMap.id ℝ Space) at h
        simpa using h
      have hgn : ‖∇ (fun z : Space => u (z + t n • e3 0)) x‖ ≤ D₁ := by
        have h1' : ‖∇ (fun z : Space => u (z + t n • e3 0)) x‖ =
            ‖fderiv ℝ (fun z : Space => u (z + t n • e3 0)) x‖ :=
          (InnerProductSpace.toDual ℝ Space).symm.norm_map _
        rw [h1', hfd_shift]; exact hgrad1 _
      have hdw : doubleWell (u (x + t n • e3 0)) ≤ 1 / 4 := doubleWell_le_quarter (h1 _)
      have hnn : 0 ≤ energy3 (fun z : Space => u (z + t n • e3 0)) x := energy3_nonneg _ _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      unfold energy3; dsimp [bound]
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hgn 2
      linarith
    · refine Filter.Eventually.of_forall fun x => ?_
      have hpt_u := (hu_unif {x} isCompact_singleton).tendsto_at (Set.mem_singleton x)
      have hpt_0 := (hp0_unif {x} isCompact_singleton).tendsto_at (Set.mem_singleton x)
      have hpt_1 := (hp_unif 0 {x} isCompact_singleton).tendsto_at (Set.mem_singleton x)
      have hpt_2 := (hp_unif 1 {x} isCompact_singleton).tendsto_at (Set.mem_singleton x)
      have hnorm2 : ‖∇ u_plus (proj2 x)‖ ^ 2 =
          (fderiv ℝ u_plus (proj2 x) (e2 0)) ^ 2 + (fderiv ℝ u_plus (proj2 x) (e2 1)) ^ 2 := by
        let b := EuclideanSpace.basisFun (Fin 2) ℝ
        rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner, Fin.sum_univ_two]
        have h0 : b 0 = e2 0 := EuclideanSpace.basisFun_apply (Fin 2) ℝ 0
        have h1' : b 1 = e2 1 := EuclideanSpace.basisFun_apply (Fin 2) ℝ 1
        have hd0 : inner ℝ (∇ u_plus (proj2 x)) (e2 0) = fderiv ℝ u_plus (proj2 x) (e2 0) := by
          rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]
        have hd0' : inner ℝ (e2 0) (∇ u_plus (proj2 x)) = fderiv ℝ u_plus (proj2 x) (e2 0) :=
          (real_inner_comm _ _).trans hd0
        have hd1 : inner ℝ (∇ u_plus (proj2 x)) (e2 1) = fderiv ℝ u_plus (proj2 x) (e2 1) := by
          rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]
        have hd1' : inner ℝ (e2 1) (∇ u_plus (proj2 x)) = fderiv ℝ u_plus (proj2 x) (e2 1) :=
          (real_inner_comm _ _).trans hd1
        rw [h0, h1', hd0, hd0', hd1, hd1']; ring
      have heq_n (n : ℕ) : energy3 (fun z => u (z + t n • e3 0)) x =
          1 / 2 * ((part3 u 0 (x + t n • e3 0)) ^ 2 + (part3 u 1 (x + t n • e3 0)) ^ 2 +
            (part3 u 2 (x + t n • e3 0)) ^ 2) + (1 - (u (x + t n • e3 0)) ^ 2) ^ 2 / 4 := by
        unfold energy3 doubleWell
        rw [norm_grad3_sq_eq]
        have hpk (k : Fin 3) : part3 (fun z => u (z + t n • e3 0)) k x = part3 u k (x + t n • e3 0) := by
          unfold part3
          have h := ((hu.regular.differentiable (by norm_num) (x + t n • e3 0)).hasFDerivAt.comp x
            ((hasFDerivAt_id x).add_const (t n • e3 0))).fderiv
          change fderiv ℝ (fun z => u (z + t n • e3 0)) x =
            (fderiv ℝ u (x + t n • e3 0)).comp (ContinuousLinearMap.id ℝ Space) at h
          rw [h]; rfl
        rw [hpk 0, hpk 1, hpk 2]
      simp_rw [heq_n]
      have hlim_en : Filter.Tendsto (fun n =>
          1 / 2 * ((part3 u 0 (x + t n • e3 0)) ^ 2 + (part3 u 1 (x + t n • e3 0)) ^ 2 +
            (part3 u 2 (x + t n • e3 0)) ^ 2) + (1 - (u (x + t n • e3 0)) ^ 2) ^ 2 / 4)
          Filter.atTop (nhds (1 / 2 * (0 ^ 2 + (fderiv ℝ u_plus (proj2 x) (e2 0)) ^ 2 +
            (fderiv ℝ u_plus (proj2 x) (e2 1)) ^ 2) + (1 - (u_plus (proj2 x)) ^ 2) ^ 2 / 4)) :=
        (((hpt_0.pow 2).add (hpt_1.pow 2) |>.add (hpt_2.pow 2)).const_mul (1 / 2 : ℝ)).add
          (((tendsto_const_nhds.sub (hpt_u.pow 2)).pow 2).div_const 4)
      have heq_lim : 1 / 2 * (0 ^ 2 + (fderiv ℝ u_plus (proj2 x) (e2 0)) ^ 2 +
          (fderiv ℝ u_plus (proj2 x) (e2 1)) ^ 2) + (1 - (u_plus (proj2 x)) ^ 2) ^ 2 / 4 =
          e_plus (proj2 x) := by
        dsimp [e_plus]; unfold doubleWell; rw [hnorm2]; ring
      rwa [heq_lim] at hlim_en
  have hen_u_le : (∫ x in Metric.ball (0 : Space) R, energy3 u x) ≤
      (∫ x in Metric.ball (0 : Space) R, e_plus (proj2 x)) + C_ann * R ^ 2 :=
    ge_of_tendsto (hlim_ball.add tendsto_const_nhds)
      (Filter.Eventually.of_forall fun n => hslide R (t n) hR (ht_pos n))
  have hcyl : (∫ x in Metric.ball (0 : Space) R, e_plus (proj2 x)) ≤ 2 * C₂ * R ^ 2 := by
    have hproj_cont : Continuous (proj2 : Space → Plane) := by
      unfold proj2
      exact ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1).smul continuous_const).add
        ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).smul continuous_const)
    have h1' := integral_ball3_le_cylinder (he_plus_cont.comp hproj_cont)
      (fun x => by dsimp [e_plus]; linarith [sq_nonneg ‖∇ u_plus (proj2 x)‖, doubleWell_nonneg (u_plus (proj2 x))])
      (by linarith : 0 ≤ R)
    have hinner_eq (s : ℝ) : (∫ y in Metric.ball (0 : Plane) R, e_plus (proj2 (embed s y))) =
        ∫ y in Metric.ball (0 : Plane) R, e_plus y := by
      congr 1; funext y
      have : proj2 (embed s y) = y := by ext k; fin_cases k <;> simp [proj2, embed, e3, e2]
      rw [this]
    dsimp only [Function.comp_apply] at h1'
    simp_rw [hinner_eq] at h1'
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ R - (-R)), smul_eq_mul] at h1'
    have hlinR := hlin R hR
    calc
      (∫ x in Metric.ball (0 : Space) R, e_plus (proj2 x))
          ≤ (R - -R) * ∫ y in Metric.ball (0 : Plane) R, e_plus y := h1'
      _ ≤ (R - -R) * (C₂ * R) := mul_le_mul_of_nonneg_left hlinR (by linarith)
      _ = 2 * C₂ * R ^ 2 := by ring
  have hpart_le : (∫ x in Metric.ball (0 : Space) R, (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) ≤
      2 * ∫ x in Metric.ball (0 : Space) R, energy3 u x := by
    rw [← MeasureTheory.integral_const_mul]
    have hp_cont : Continuous (fun x : Space => (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) :=
      (((hu.regular.of_le (by norm_num)).continuous_fderiv one_ne_zero).clm_apply continuous_const).pow 2
    have he_cont : Continuous (energy3 u) :=
      (continuous_const.mul (((InnerProductSpace.toDual ℝ Space).symm.continuous.comp
        ((hu.regular.of_le (by norm_num)).continuous_fderiv one_ne_zero)).norm.pow 2)).add
      (((continuous_const.sub (hu.regular.continuous.pow 2)).pow 2).div_const 4)
    apply MeasureTheory.setIntegral_mono_on
      ((hp_cont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall)
      (((he_cont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set
        ball_subset_closedBall).const_mul 2)
      measurableSet_ball
    intro x _
    have hsq := norm_grad3_sq_eq u x
    unfold energy3
    have hdw := doubleWell_nonneg (u x)
    have hp : (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2 = (part3 u i x) ^ 2 := rfl
    rw [hp, hsq]
    fin_cases i
    · change (part3 u 0 x) ^ 2 ≤ _
      linarith [hdw, sq_nonneg (part3 u 1 x), sq_nonneg (part3 u 2 x)]
    · change (part3 u 1 x) ^ 2 ≤ _
      linarith [hdw, sq_nonneg (part3 u 0 x), sq_nonneg (part3 u 2 x)]
    · change (part3 u 2 x) ^ 2 ≤ _
      linarith [hdw, sq_nonneg (part3 u 0 x), sq_nonneg (part3 u 1 x)]
  linarith
