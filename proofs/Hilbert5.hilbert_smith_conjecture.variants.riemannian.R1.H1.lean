import OMAReductions.R_Hilbert5_hilbert_smith_conjecture_variants_riemannian_R1

/-!
# Proof of `Hilbert5.hilbert_smith_conjecture.variants.riemannian.R1.H1`

Self-contained proof of local squared-distance strong convexity and stable local distance
coordinates on any connected smooth Riemannian manifold via Banach-space geodesic flow,
Gauss's Lemma, normal-ball distance equality, and 1D fundamental theorem of calculus.
-/

noncomputable section

-- Section 1: H1_M1_GeodesicEngine.lean
namespace Hilbert5H1

open Metric Set Filter Topology BoundedContinuousFunction intervalIntegral
open scoped RealInnerProductSpace Classical

abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

/- ### Part 1: Coordinate `LocalMetric`, Christoffel symbols, and Levi-Civita compatibility -/

structure LocalMetric (n : ℕ) where
  a₀ : Euc n
  r₁ : ℝ
  hr₁ : 0 < r₁
  g : Euc n → Fin n → Fin n → ℝ
  hg_smooth : ∀ i j, ContDiffOn ℝ 3 (fun y => g y i j) (ball a₀ r₁)
  hg_symm : ∀ y ∈ ball a₀ r₁, ∀ i j, g y i j = g y j i
  hg_pos : ∀ y ∈ ball a₀ r₁, ∀ v : Euc n, v ≠ 0 →
    0 < ∑ i, ∑ j, g y i j * v.ofLp i * v.ofLp j

namespace LocalMetric

variable {n : ℕ} (M : LocalMetric n)

def e (i : Fin n) : Euc n := EuclideanSpace.single i (1 : ℝ)

def inner (y u v : Euc n) : ℝ :=
  ∑ i, ∑ j, M.g y i j * u.ofLp i * v.ofLp j

lemma inner_symm {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (u v : Euc n) :
    M.inner y u v = M.inner y v u := by
  simp only [inner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [M.hg_symm y hy i j]; ring

lemma inner_pos {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) {v : Euc n} (hv : v ≠ 0) :
    0 < M.inner y v v := M.hg_pos y hy v hv

lemma inner_nonneg {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (v : Euc n) :
    0 ≤ M.inner y v v := by
  by_cases hv : v = 0
  · subst hv; simp [inner]
  · exact (M.inner_pos hy hv).le

lemma inner_add_left (y u₁ u₂ v : Euc n) :
    M.inner y (u₁ + u₂) v = M.inner y u₁ v + M.inner y u₂ v := by
  simp only [inner, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.add_apply]; ring

lemma inner_add_right (y u v₁ v₂ : Euc n) :
    M.inner y u (v₁ + v₂) = M.inner y u v₁ + M.inner y u v₂ := by
  simp only [inner, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.add_apply]; ring

lemma inner_smul_left (y : Euc n) (c : ℝ) (u v : Euc n) :
    M.inner y (c • u) v = c * M.inner y u v := by
  simp only [inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]; ring

lemma inner_smul_right (y : Euc n) (c : ℝ) (u v : Euc n) :
    M.inner y u (c • v) = c * M.inner y u v := by
  simp only [inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]; ring

lemma inner_sub_left (y u₁ u₂ v : Euc n) :
    M.inner y (u₁ - u₂) v = M.inner y u₁ v - M.inner y u₂ v := by
  rw [sub_eq_add_neg, M.inner_add_left, ← neg_one_smul ℝ u₂, M.inner_smul_left]; ring

lemma inner_sub_right (y u v₁ v₂ : Euc n) :
    M.inner y u (v₁ - v₂) = M.inner y u v₁ - M.inner y u v₂ := by
  rw [sub_eq_add_neg, M.inner_add_right, ← neg_one_smul ℝ v₂, M.inner_smul_right]; ring

lemma inner_neg_left (y u v : Euc n) : M.inner y (-u) v = -M.inner y u v := by
  rw [← neg_one_smul ℝ u, M.inner_smul_left]; ring

lemma inner_neg_right (y u v : Euc n) : M.inner y u (-v) = -M.inner y u v := by
  rw [← neg_one_smul ℝ v, M.inner_smul_right]; ring

lemma inner_zero_left (y v : Euc n) : M.inner y 0 v = 0 := by simp [inner]
lemma inner_zero_right (y u : Euc n) : M.inner y u 0 = 0 := by simp [inner]

lemma inner_sum_left {ι : Type*} (s : Finset ι) (y : Euc n) (f : ι → Euc n) (v : Euc n) :
    M.inner y (∑ k ∈ s, f k) v = ∑ k ∈ s, M.inner y (f k) v := by
  induction s using Finset.induction_on with
  | empty => simp [M.inner_zero_left]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, M.inner_add_left, ih, Finset.sum_insert ha]

lemma inner_cauchy_schwarz {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (u v : Euc n) :
    (M.inner y u v) ^ 2 ≤ M.inner y u u * M.inner y v v := by
  by_cases hu : M.inner y u u = 0
  · have hu0 : u = 0 := by
      by_contra hne; linarith [M.inner_pos hy hne]
    subst hu0; simp [inner]
  · have hpos : 0 < M.inner y u u := lt_of_le_of_ne (M.inner_nonneg hy u) (Ne.symm hu)
    let c : ℝ := M.inner y u v / M.inner y u u
    have h0 := M.inner_nonneg hy (v - c • u)
    rw [M.inner_sub_left, M.inner_sub_right, M.inner_sub_right, M.inner_smul_left,
      M.inner_smul_right, M.inner_smul_left, M.inner_smul_right, M.inner_symm hy v u] at h0
    have hkey : M.inner y v v - c * M.inner y u v - (c * M.inner y u v - c * (c * M.inner y u u)) =
        (M.inner y u u * M.inner y v v - (M.inner y u v) ^ 2) / M.inner y u u := by
      simp only [c]; field_simp [hpos.ne']; ring
    rw [hkey, div_nonneg_iff] at h0
    rcases h0 with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith

def gnorm (y v : Euc n) : ℝ := Real.sqrt (M.inner y v v)

lemma gnorm_nonneg (y v : Euc n) : 0 ≤ M.gnorm y v := Real.sqrt_nonneg _

lemma gnorm_sq {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (v : Euc n) :
    (M.gnorm y v) ^ 2 = M.inner y v v :=
  Real.sq_sqrt (M.inner_nonneg hy v)

lemma gnorm_zero (y : Euc n) : M.gnorm y 0 = 0 := by simp [gnorm, inner]

lemma inner_le_gnorm_mul {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (u v : Euc n) :
    |M.inner y u v| ≤ M.gnorm y u * M.gnorm y v := by
  have hsq : |M.inner y u v| ^ 2 ≤ (M.gnorm y u * M.gnorm y v) ^ 2 := by
    rw [sq_abs, mul_pow, M.gnorm_sq hy, M.gnorm_sq hy]
    exact M.inner_cauchy_schwarz hy u v
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (M.gnorm_nonneg _ _) (M.gnorm_nonneg _ _))).mp hsq

lemma exists_metric_bounds (hn : 0 < n) {r₂ : ℝ} (hr₂ : 0 < r₂) (hr₂_lt : r₂ < M.r₁) :
    ∃ m_g > 0, ∃ M_g > 0, ∃ L_g ≥ 0,
      (∀ y ∈ closedBall M.a₀ r₂, ∀ v : Euc n,
        m_g * ‖v‖ ≤ M.gnorm y v ∧ M.gnorm y v ≤ M_g * ‖v‖) ∧
      (∀ y₁ ∈ closedBall M.a₀ r₂, ∀ y₂ ∈ closedBall M.a₀ r₂, ∀ u v : Euc n,
        |M.inner y₁ u v - M.inner y₂ u v| ≤ L_g * ‖y₁ - y₂‖ * ‖u‖ * ‖v‖) := by
  have hsub : closedBall M.a₀ r₂ ⊆ ball M.a₀ M.r₁ := Metric.closedBall_subset_ball hr₂_lt
  have hK : IsCompact (closedBall M.a₀ r₂ ×ˢ sphere (0 : Euc n) 1) :=
    (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hne : (closedBall M.a₀ r₂ ×ˢ sphere (0 : Euc n) 1).Nonempty := by
    refine ⟨(M.a₀, e ⟨0, hn⟩), mem_closedBall_self hr₂.le, ?_⟩
    simp [e]
  have hcont : ContinuousOn (fun p : Euc n × Euc n => M.inner p.1 p.2 p.2)
      (closedBall M.a₀ r₂ ×ˢ sphere (0 : Euc n) 1) := by
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    have hg : ContinuousOn (fun p : Euc n × Euc n => M.g p.1 i j) (closedBall M.a₀ r₂ ×ˢ sphere (0 : Euc n) 1) :=
      (M.hg_smooth i j).continuousOn.comp continuousOn_fst fun p hp => hsub hp.1
    have hvi : ContinuousOn (fun p : Euc n × Euc n => p.2.ofLp i) (closedBall M.a₀ r₂ ×ˢ sphere (0 : Euc n) 1) :=
      ((EuclideanSpace.proj i).continuous.comp continuous_snd).continuousOn
    have hvj : ContinuousOn (fun p : Euc n × Euc n => p.2.ofLp j) (closedBall M.a₀ r₂ ×ˢ sphere (0 : Euc n) 1) :=
      ((EuclideanSpace.proj j).continuous.comp continuous_snd).continuousOn
    exact (hg.mul hvi).mul hvj
  obtain ⟨p_min, hp_min_mem, hp_min⟩ := hK.exists_isMinOn hne hcont
  obtain ⟨p_max, hp_max_mem, hp_max⟩ := hK.exists_isMaxOn hne hcont
  have hmin_pos : 0 < M.inner p_min.1 p_min.2 p_min.2 := by
    have hv0 : p_min.2 ≠ 0 := by
      intro h0; have h1 : ‖p_min.2‖ = 1 := by simpa [mem_sphere] using hp_min_mem.2
      rw [h0, norm_zero] at h1; norm_num at h1
    exact M.inner_pos (hsub hp_min_mem.1) hv0
  have hmax_pos : 0 < M.inner p_max.1 p_max.2 p_max.2 := lt_of_lt_of_le hmin_pos (hp_max hp_min_mem)
  let m_g : ℝ := Real.sqrt (M.inner p_min.1 p_min.2 p_min.2)
  let M_g : ℝ := Real.sqrt (M.inner p_max.1 p_max.2 p_max.2)
  have hm_pos : 0 < m_g := Real.sqrt_pos.mpr hmin_pos
  have hM_pos : 0 < M_g := Real.sqrt_pos.mpr hmax_pos
  have hbounds : ∀ y ∈ closedBall M.a₀ r₂, ∀ v : Euc n,
      m_g * ‖v‖ ≤ M.gnorm y v ∧ M.gnorm y v ≤ M_g * ‖v‖ := by
    intro y hy v
    by_cases hv : v = 0
    · subst hv; simp [gnorm, inner]
    · have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
      let u : Euc n := ‖v‖⁻¹ • v
      have hu_sph : u ∈ sphere (0 : Euc n) 1 := by
        simp [u, norm_smul, inv_mul_cancel₀ hnv.ne']
      have hscale : M.inner y v v = ‖v‖ ^ 2 * M.inner y u u := by
        have hv_eq : v = ‖v‖ • u := by simp [u, smul_smul, mul_inv_cancel₀ hnv.ne']
        conv_lhs => rw [hv_eq]
        rw [M.inner_smul_left, M.inner_smul_right]; ring
      have hlo : m_g ^ 2 ≤ M.inner y u u := by
        dsimp only [m_g]; rw [Real.sq_sqrt hmin_pos.le]
        exact isMinOn_iff.mp hp_min (y, u) ⟨hy, hu_sph⟩
      have hhi : M.inner y u u ≤ M_g ^ 2 := by
        dsimp only [M_g]; rw [Real.sq_sqrt hmax_pos.le]
        exact isMaxOn_iff.mp hp_max (y, u) ⟨hy, hu_sph⟩
      constructor
      · have hsq : (m_g * ‖v‖) ^ 2 ≤ (M.gnorm y v) ^ 2 := by
          rw [M.gnorm_sq (hsub hy), hscale, mul_pow, mul_comm (m_g ^ 2)]
          exact mul_le_mul_of_nonneg_left hlo (sq_nonneg ‖v‖)
        exact (sq_le_sq₀ (mul_nonneg hm_pos.le hnv.le) (M.gnorm_nonneg _ _)).mp hsq
      · have hsq : (M.gnorm y v) ^ 2 ≤ (M_g * ‖v‖) ^ 2 := by
          rw [M.gnorm_sq (hsub hy), hscale, mul_pow, mul_comm (M_g ^ 2)]
          exact mul_le_mul_of_nonneg_left hhi (sq_nonneg ‖v‖)
        exact (sq_le_sq₀ (M.gnorm_nonneg _ _) (mul_nonneg hM_pos.le hnv.le)).mp hsq
  -- Lipschitz bound on `g` over compact convex `closedBall M.a₀ r₂`
  have hlip_ij : ∀ i j : Fin n, ∃ L ≥ 0, ∀ y₁ ∈ closedBall M.a₀ r₂, ∀ y₂ ∈ closedBall M.a₀ r₂,
      |M.g y₁ i j - M.g y₂ i j| ≤ L * ‖y₁ - y₂‖ := by
    intro i j
    have hfd_cont : ContinuousOn (fun y => ‖fderiv ℝ (fun z => M.g z i j) y‖) (closedBall M.a₀ r₂) := by
      have hfd : ContDiffOn ℝ 2 (fun y => fderivWithin ℝ (fun z => M.g z i j) (ball M.a₀ M.r₁) y)
          (ball M.a₀ M.r₁) :=
        (M.hg_smooth i j).fderivWithin isOpen_ball.uniqueDiffOn (by norm_num)
      have hcongr : ContinuousOn (fun y => fderiv ℝ (fun z => M.g z i j) y) (closedBall M.a₀ r₂) :=
        (hfd.congr fun y hy => (fderivWithin_of_isOpen isOpen_ball hy).symm).continuousOn.mono hsub
      exact continuous_norm.comp_continuousOn hcongr
    obtain ⟨y_m, hy_m, hmax_fd⟩ := (isCompact_closedBall M.a₀ r₂).exists_isMaxOn
      ⟨M.a₀, mem_closedBall_self hr₂.le⟩ hfd_cont
    refine ⟨‖fderiv ℝ (fun z => M.g z i j) y_m‖, norm_nonneg _, fun y₁ hy₁ y₂ hy₂ => ?_⟩
    have hderiv : ∀ y ∈ closedBall M.a₀ r₂,
        HasFDerivWithinAt (fun z => M.g z i j) (fderiv ℝ (fun z => M.g z i j) y) (closedBall M.a₀ r₂) y :=
      fun y hy =>
        (((M.hg_smooth i j).contDiffAt (isOpen_ball.mem_nhds (hsub hy))).differentiableAt (by decide)).hasFDerivAt.hasFDerivWithinAt
    have hbd : ∀ y ∈ closedBall M.a₀ r₂, ‖fderiv ℝ (fun z => M.g z i j) y‖ ≤ ‖fderiv ℝ (fun z => M.g z i j) y_m‖ :=
      fun y hy => hmax_fd hy
    simpa [Real.norm_eq_abs] using
      (convex_closedBall M.a₀ r₂).norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbd hy₂ hy₁
  choose Lij hLij_nn hLij_bd using hlip_ij
  let L_g : ℝ := ∑ i : Fin n, ∑ j : Fin n, Lij i j
  have hLg_nn : 0 ≤ L_g := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hLij_nn i j
  refine ⟨m_g, hm_pos, M_g, hM_pos, L_g, hLg_nn, hbounds, fun y₁ hy₁ y₂ hy₂ u v => ?_⟩
  have hdiff : M.inner y₁ u v - M.inner y₂ u v =
      ∑ i, ∑ j, (M.g y₁ i j - M.g y₂ i j) * u.ofLp i * v.ofLp j := by
    simp only [inner, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hdiff]
  calc |∑ i, ∑ j, (M.g y₁ i j - M.g y₂ i j) * u.ofLp i * v.ofLp j|
      ≤ ∑ i, |∑ j, (M.g y₁ i j - M.g y₂ i j) * u.ofLp i * v.ofLp j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |(M.g y₁ i j - M.g y₂ i j) * u.ofLp i * v.ofLp j| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, (Lij i j * ‖y₁ - y₂‖) * ‖u‖ * ‖v‖ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul]
        have hui : |u.ofLp i| ≤ ‖u‖ := by
          simpa [Real.norm_eq_abs] using PiLp.norm_apply_le u i
        have hvj : |v.ofLp j| ≤ ‖v‖ := by
          simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v j
        exact mul_le_mul (mul_le_mul (hLij_bd i j y₁ hy₁ y₂ hy₂) hui (abs_nonneg _)
          (mul_nonneg (hLij_nn i j) (norm_nonneg _))) hvj (abs_nonneg _)
          (mul_nonneg (mul_nonneg (hLij_nn i j) (norm_nonneg _)) (norm_nonneg _))
    _ = L_g * ‖y₁ - y₂‖ * ‖u‖ * ‖v‖ := by
        simp only [L_g, Finset.sum_mul]

def mat (y : Euc n) : Matrix (Fin n) (Fin n) ℝ := Matrix.of (M.g y)

lemma mat_det_ne_zero {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) :
    (M.mat y).det ≠ 0 := by
  intro hdet
  have hker : ∃ v : Fin n → ℝ, v ≠ 0 ∧ (M.mat y).mulVec v = 0 := by
    by_contra h
    push Not at h
    have hinj : Function.Injective (Matrix.toLin' (M.mat y)) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro v hv
      by_contra hv0
      exact h v hv0 hv
    have hbij : Function.Bijective (Matrix.toLin' (M.mat y)) :=
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
    let hlin := LinearEquiv.ofBijective _ hbij
    have hcomp : (Matrix.toLin' (M.mat y)).comp hlin.symm.toLinearMap = LinearMap.id :=
      LinearMap.ext fun v => hlin.apply_symm_apply v
    have h1 := congrArg LinearMap.det hcomp
    rw [LinearMap.det_comp, LinearMap.det_id, LinearMap.det_toLin', hdet, zero_mul] at h1
    exact zero_ne_one h1
  rcases hker with ⟨v, hv0, hmul⟩
  let u : Euc n := WithLp.toLp 2 v
  have hu0 : u ≠ 0 := fun h => hv0 (congrArg WithLp.ofLp h)
  have hpos := M.inner_pos hy hu0
  have hzero : M.inner y u u = 0 := by
    change ∑ i, ∑ j, M.g y i j * v i * v j = 0
    have h1 : ∀ i, ∑ j, M.g y i j * v j = 0 := fun i => congrFun hmul i
    calc ∑ i, ∑ j, M.g y i j * v i * v j
        = ∑ i, v i * (∑ j, M.g y i j * v j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by simp [h1]
  linarith

def matInv (y : Euc n) : Matrix (Fin n) (Fin n) ℝ := (M.mat y)⁻¹

lemma mat_mul_inv {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (i j : Fin n) :
    ∑ k, M.g y i k * M.matInv y k j = if i = j then 1 else 0 := by
  have h := Matrix.mul_nonsing_inv (M.mat y) (M.mat_det_ne_zero hy).isUnit
  have hij := congrFun (congrFun h i) j
  simpa [Matrix.mul_apply, mat, matInv, Matrix.one_apply] using hij

private lemma contDiffOn_finset_prod {ι : Type*} {s : Finset ι} {k : ℕ}
    {f : ι → Euc n → ℝ} {S : Set (Euc n)}
    (hf : ∀ i ∈ s, ContDiffOn ℝ k (f i) S) :
    ContDiffOn ℝ k (fun y => ∏ i ∈ s, f i y) S := by
  induction s using Finset.induction_on with
  | empty => simpa using contDiffOn_const
  | insert a s ha ih =>
    have heq : (fun y => ∏ i ∈ insert a s, f i y) = fun y => f a y * ∏ i ∈ s, f i y := by
      ext y; exact Finset.prod_insert ha
    rw [heq]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma det_contDiffOn {k : ℕ} (A : Euc n → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, ContDiffOn ℝ k (fun y => A y i j) (ball M.a₀ M.r₁)) :
    ContDiffOn ℝ k (fun y => (A y).det) (ball M.a₀ M.r₁) := by
  have heq : (fun y => (A y).det) = fun y => ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A y (σ i) i := by
    ext y; simp [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  rw [heq]
  refine ContDiffOn.sum fun σ _ => ContDiffOn.mul contDiffOn_const ?_
  exact contDiffOn_finset_prod fun i _ => hA (σ i) i

lemma matInv_contDiffOn (l k : Fin n) :
    ContDiffOn ℝ 3 (fun y => M.matInv y l k) (ball M.a₀ M.r₁) := by
  have hdet : ContDiffOn ℝ 3 (fun y => (M.mat y).det) (ball M.a₀ M.r₁) :=
    M.det_contDiffOn M.mat M.hg_smooth
  have hadj : ContDiffOn ℝ 3 (fun y => (M.mat y).adjugate l k) (ball M.a₀ M.r₁) := by
    have heq : (fun y => (M.mat y).adjugate l k) =
        fun y => ((M.mat y).updateRow k (Pi.single l (1 : ℝ))).det := by
      ext y; exact Matrix.adjugate_apply (M.mat y) l k
    rw [heq]
    refine M.det_contDiffOn _ fun i j => ?_
    by_cases hik : i = k
    · subst hik; simp [Matrix.updateRow_self]; exact contDiffOn_const
    · simp [Matrix.updateRow_ne hik]; exact M.hg_smooth i j
  have hinv_eq : (fun y => M.matInv y l k) = fun y => (M.mat y).det⁻¹ * (M.mat y).adjugate l k := by
    ext y; simp [matInv, Matrix.inv_def]
  rw [hinv_eq]
  exact (hdet.inv fun y hy => M.mat_det_ne_zero hy).mul hadj

def dg (y : Euc n) (k i j : Fin n) : ℝ :=
  fderiv ℝ (fun z => M.g z i j) y (e k)

lemma dg_contDiffOn (k i j : Fin n) :
    ContDiffOn ℝ 2 (fun y => M.dg y k i j) (ball M.a₀ M.r₁) := by
  have hfd : ContDiffOn ℝ 2 (fun y => fderivWithin ℝ (fun z => M.g z i j) (ball M.a₀ M.r₁) y)
      (ball M.a₀ M.r₁) :=
    (M.hg_smooth i j).fderivWithin isOpen_ball.uniqueDiffOn (by norm_num)
  have hcongr : ContDiffOn ℝ 2 (fun y => fderiv ℝ (fun z => M.g z i j) y) (ball M.a₀ M.r₁) :=
    hfd.congr fun y hy => (fderivWithin_of_isOpen isOpen_ball hy).symm
  exact (ContinuousLinearMap.apply ℝ ℝ (e k)).contDiff.comp_contDiffOn hcongr

lemma dg_symm {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (k i j : Fin n) :
    M.dg y k i j = M.dg y k j i := by
  have heq : (fun z => M.g z i j) =ᶠ[𝓝 y] (fun z => M.g z j i) := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz using M.hg_symm z hz i j
  simp only [dg, heq.fderiv_eq]

lemma fderiv_g_apply {y : Euc n} (i j : Fin n) (u : Euc n) :
    fderiv ℝ (fun z => M.g z i j) y u = ∑ k, M.dg y k i j * u.ofLp k := by
  have hu : u = ∑ k, u.ofLp k • e k := by
    ext m; simp [e, Pi.single_apply]
  conv_lhs => rw [hu]
  simp only [map_sum, map_smul, smul_eq_mul, dg, mul_comm]

def Γ (y : Euc n) (l i j : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ k, M.matInv y l k * (M.dg y i j k + M.dg y j i k - M.dg y k i j)

lemma Γ_symm {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (l i j : Fin n) :
    M.Γ y l i j = M.Γ y l j i := by
  simp only [Γ]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [M.dg_symm hy k i j]; ring

lemma Γ_contDiffOn (l i j : Fin n) :
    ContDiffOn ℝ 2 (fun y => M.Γ y l i j) (ball M.a₀ M.r₁) := by
  refine ContDiffOn.mul contDiffOn_const (ContDiffOn.sum fun k _ => ContDiffOn.mul ?_ ?_)
  · exact (M.matInv_contDiffOn l k).of_le (by norm_num)
  · exact ((M.dg_contDiffOn i j k).add (M.dg_contDiffOn j i k)).sub (M.dg_contDiffOn k i j)

def ΓVec (y u v : Euc n) : Euc n :=
  WithLp.toLp 2 (fun l => ∑ i, ∑ j, M.Γ y l i j * u.ofLp i * v.ofLp j)

lemma ΓVec_symm {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (u v : Euc n) :
    M.ΓVec y u v = M.ΓVec y v u := by
  ext l
  simp only [ΓVec]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [M.Γ_symm hy l i j]; ring

lemma ΓVec_smul (y : Euc n) (c : ℝ) (u v : Euc n) :
    M.ΓVec y (c • u) (c • v) = (c * c) • M.ΓVec y u v := by
  ext l
  simp only [ΓVec, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma ΓVec_neg (y u v : Euc n) : M.ΓVec y (-u) (-v) = M.ΓVec y u v := by
  rw [← neg_one_smul ℝ u, ← neg_one_smul ℝ v, M.ΓVec_smul]; simp

lemma inner_ΓVec {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (u v w : Euc n) :
    M.inner y (M.ΓVec y u v) w =
      (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ m, (M.dg y i j m + M.dg y j i m - M.dg y m i j) *
        u.ofLp i * v.ofLp j * w.ofLp m := by
  simp only [inner, ΓVec]
  have h1 : ∀ m, ∑ l, M.g y l m * (∑ i, ∑ j, M.Γ y l i j * u.ofLp i * v.ofLp j) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, (M.dg y i j m + M.dg y j i m - M.dg y m i j) *
        u.ofLp i * v.ofLp j := by
    intro m
    calc ∑ l, M.g y l m * (∑ i, ∑ j, M.Γ y l i j * u.ofLp i * v.ofLp j)
        = ∑ i, ∑ j, (∑ l, M.g y l m * M.Γ y l i j) * u.ofLp i * v.ofLp j := by
            simp_rw [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
      _ = (1 / 2 : ℝ) * ∑ i, ∑ j, (M.dg y i j m + M.dg y j i m - M.dg y m i j) *
            u.ofLp i * v.ofLp j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            have hcol : ∑ l, M.g y l m * M.Γ y l i j =
                (1 / 2 : ℝ) * (M.dg y i j m + M.dg y j i m - M.dg y m i j) := by
              simp only [Γ]
              calc ∑ l, M.g y l m * ((1 / 2 : ℝ) * ∑ k, M.matInv y l k *
                      (M.dg y i j k + M.dg y j i k - M.dg y k i j))
                  = (1 / 2 : ℝ) * ∑ k, (∑ l, M.g y m l * M.matInv y l k) *
                      (M.dg y i j k + M.dg y j i k - M.dg y k i j) := by
                        simp_rw [Finset.mul_sum, Finset.sum_mul]
                        rw [Finset.sum_comm]
                        refine Finset.sum_congr rfl fun k _ => ?_
                        rw [Finset.mul_sum]
                        refine Finset.sum_congr rfl fun l _ => ?_
                        rw [M.hg_symm y hy l m]; ring
                _ = (1 / 2 : ℝ) * (M.dg y i j m + M.dg y j i m - M.dg y m i j) := by
                      congr 1; simp_rw [M.mat_mul_inv hy]; simp
            rw [hcol]; ring
  calc ∑ l, ∑ m, M.g y l m * (∑ i, ∑ j, M.Γ y l i j * u.ofLp i * v.ofLp j) * w.ofLp m
      = ∑ m, (∑ l, M.g y l m * (∑ i, ∑ j, M.Γ y l i j * u.ofLp i * v.ofLp j)) * w.ofLp m := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ => by rw [Finset.sum_mul]
    _ = ∑ m, ((1 / 2 : ℝ) * ∑ i, ∑ j, (M.dg y i j m + M.dg y j i m - M.dg y m i j) *
          u.ofLp i * v.ofLp j) * w.ofLp m := by
          refine Finset.sum_congr rfl fun m _ => by rw [h1 m]
    _ = (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ m, (M.dg y i j m + M.dg y j i m - M.dg y m i j) *
          u.ofLp i * v.ofLp j * w.ofLp m := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by ring

lemma dG_eq_ΓVec {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (u v w : Euc n) :
    ∑ i, ∑ j, (fderiv ℝ (fun z => M.g z i j) y u) * v.ofLp i * w.ofLp j =
      M.inner y (M.ΓVec y u v) w + M.inner y v (M.ΓVec y u w) := by
  rw [M.inner_symm hy v (M.ΓVec y u w), M.inner_ΓVec hy u v w, M.inner_ΓVec hy u w v]
  have hswap : ∑ i, ∑ j, ∑ m, (M.dg y i j m + M.dg y j i m - M.dg y m i j) *
        u.ofLp i * w.ofLp j * v.ofLp m =
      ∑ i, ∑ j, ∑ m, (M.dg y i m j + M.dg y m i j - M.dg y j i m) *
        u.ofLp i * v.ofLp j * w.ofLp m := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by ring
  rw [hswap]
  have hrhs : (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ m, (M.dg y i j m + M.dg y j i m - M.dg y m i j) *
        u.ofLp i * v.ofLp j * w.ofLp m +
      (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ m, (M.dg y i m j + M.dg y m i j - M.dg y j i m) *
        u.ofLp i * v.ofLp j * w.ofLp m =
      ∑ i, ∑ j, ∑ m, M.dg y i j m * u.ofLp i * v.ofLp j * w.ofLp m := by
    rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [M.dg_symm hy i m j]; ring
  rw [hrhs]
  simp_rw [M.fderiv_g_apply, Finset.sum_mul]
  calc ∑ i, ∑ j, ∑ k, M.dg y k i j * u.ofLp k * v.ofLp i * w.ofLp j
      = ∑ i, ∑ k, ∑ j, M.dg y k i j * u.ofLp k * v.ofLp i * w.ofLp j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, M.dg y k i j * u.ofLp k * v.ofLp i * w.ofLp j :=
          Finset.sum_comm

/-- Levi-Civita metric compatibility along any differentiable curve `(γ, u, v)`. -/
lemma hasDerivAt_inner {γ u v : ℝ → Euc n} {t : ℝ} {γ' u' v' : Euc n}
    (hγm : γ t ∈ ball M.a₀ M.r₁)
    (hγ : HasDerivAt γ γ' t) (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => M.inner (γ s) (u s) (v s))
      (M.inner (γ t) (u' + M.ΓVec (γ t) γ' (u t)) (v t) +
       M.inner (γ t) (u t) (v' + M.ΓVec (γ t) γ' (v t))) t := by
  have hcoord : ∀ i : Fin n, HasDerivAt (fun s => (u s).ofLp i) (u'.ofLp i) t :=
    fun i => by simpa [Function.comp_def] using (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t hu
  have hcoordv : ∀ j : Fin n, HasDerivAt (fun s => (v s).ofLp j) (v'.ofLp j) t :=
    fun j => by simpa [Function.comp_def] using (EuclideanSpace.proj j).hasFDerivAt.comp_hasDerivAt t hv
  have hterm : ∀ i j : Fin n,
      HasDerivAt (fun s => M.g (γ s) i j * (u s).ofLp i * (v s).ofLp j)
        ((fderiv ℝ (fun z => M.g z i j) (γ t) γ') * (u t).ofLp i * (v t).ofLp j +
          M.g (γ t) i j * u'.ofLp i * (v t).ofLp j +
          M.g (γ t) i j * (u t).ofLp i * v'.ofLp j) t := by
    intro i j
    have hg_diff : HasFDerivAt (fun z => M.g z i j) (fderiv ℝ (fun z => M.g z i j) (γ t)) (γ t) :=
      ((M.hg_smooth i j).contDiffAt (isOpen_ball.mem_nhds hγm)).differentiableAt (by decide)
        |>.hasFDerivAt
    have hg_t : HasDerivAt (fun s => M.g (γ s) i j) (fderiv ℝ (fun z => M.g z i j) (γ t) γ') t :=
      hg_diff.comp_hasDerivAt t hγ
    have hprod := (hg_t.mul (hcoord i)).mul (hcoordv j)
    have hval : ((fderiv ℝ (fun z => M.g z i j) (γ t) γ') * (u t).ofLp i +
        M.g (γ t) i j * u'.ofLp i) * (v t).ofLp j +
        M.g (γ t) i j * (u t).ofLp i * v'.ofLp j =
      (fderiv ℝ (fun z => M.g z i j) (γ t) γ') * (u t).ofLp i * (v t).ofLp j +
        M.g (γ t) i j * u'.ofLp i * (v t).ofLp j +
        M.g (γ t) i j * (u t).ofLp i * v'.ofLp j := by ring
    exact hval ▸ hprod
  have hsum : HasDerivAt (fun s => M.inner (γ s) (u s) (v s))
      (∑ i, ∑ j, ((fderiv ℝ (fun z => M.g z i j) (γ t) γ') * (u t).ofLp i * (v t).ofLp j +
          M.g (γ t) i j * u'.ofLp i * (v t).ofLp j +
          M.g (γ t) i j * (u t).ofLp i * v'.ofLp j)) t :=
    HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => hterm i j
  convert hsum using 1
  rw [M.inner_add_left, M.inner_add_right]
  have hsplit : ∑ i, ∑ j, ((fderiv ℝ (fun z => M.g z i j) (γ t) γ') * (u t).ofLp i * (v t).ofLp j +
        M.g (γ t) i j * u'.ofLp i * (v t).ofLp j +
        M.g (γ t) i j * (u t).ofLp i * v'.ofLp j) =
      (∑ i, ∑ j, (fderiv ℝ (fun z => M.g z i j) (γ t) γ') * (u t).ofLp i * (v t).ofLp j) +
      M.inner (γ t) u' (v t) + M.inner (γ t) (u t) v' := by
    simp only [inner, ← Finset.sum_add_distrib]
  rw [hsplit, M.dG_eq_ΓVec hγm γ' (u t) (v t)]
  ring

end LocalMetric

/- ### Part 2: Geodesic ODE via Inverse Function Theorem on `I01 →ᵇ (Euc n × Euc n)` -/

section GeodesicFlow

variable {n : ℕ}

abbrev I01 := Set.Icc (0 : ℝ) 1
abbrev PathOne (n : ℕ) := I01 →ᵇ Euc n
abbrev PathPair (n : ℕ) := I01 →ᵇ (Euc n × Euc n)

def proj01 (t : ℝ) : I01 := Set.projIcc 0 1 zero_le_one t

lemma continuous_proj01 : Continuous proj01 :=
  continuous_projIcc (h := zero_le_one)

def intFun (f : PathOne n) (t : ℝ) : Euc n :=
  ∫ s in (0 : ℝ)..t, f (proj01 s)

lemma intFun_hasDerivAt (f : PathOne n) (t : ℝ) :
    HasDerivAt (intFun f) (f (proj01 t)) t := by
  have hc : Continuous (fun s : ℝ => f (proj01 s)) := f.continuous.comp continuous_proj01
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

def intOp : PathOne n →L[ℝ] PathOne n :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        mkOfCompact ⟨fun t => intFun f t.1,
          (continuous_iff_continuousAt.mpr fun s => (intFun_hasDerivAt f s).continuousAt).comp
            continuous_subtype_val⟩
      map_add' := fun f g => BoundedContinuousFunction.ext fun t => by
        have hf : Continuous (fun s : ℝ => f (proj01 s)) := f.continuous.comp continuous_proj01
        have hg : Continuous (fun s : ℝ => g (proj01 s)) := g.continuous.comp continuous_proj01
        exact intervalIntegral.integral_add (hf.intervalIntegrable 0 t.1) (hg.intervalIntegrable 0 t.1)
      map_smul' := fun c f => BoundedContinuousFunction.ext fun t => by
        exact intervalIntegral.integral_smul c (fun s : ℝ => f (proj01 s)) }
    1 (fun f => by
      change ‖mkOfCompact (⟨fun t : I01 => intFun f t.1, _⟩ : C(I01, Euc n))‖ ≤ 1 * ‖f‖
      rw [one_mul, BoundedContinuousFunction.norm_le (norm_nonneg f)]
      intro t
      have hle : ∀ s ∈ Set.uIoc (0 : ℝ) t.1, ‖f (proj01 s)‖ ≤ ‖f‖ :=
        fun s _ => BoundedContinuousFunction.norm_coe_le_norm f (proj01 s)
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hle
      have h2 : |t.1 - 0| ≤ 1 := by
        rw [sub_zero, abs_of_nonneg t.2.1]; exact t.2.2
      calc ‖intFun f t.1‖ ≤ ‖f‖ * |t.1 - 0| := h1
        _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg f)
        _ = ‖f‖ := mul_one _)

lemma intOp_apply (f : PathOne n) (t : I01) :
    intOp f t = intFun f t.1 := rfl

lemma intOp_apply_zero (f : PathOne n) :
    intOp f ⟨0, left_mem_Icc.mpr zero_le_one⟩ = 0 := by
  simp [intOp_apply, intFun]

def proj1L : PathPair n →L[ℝ] PathOne n :=
  LinearMap.mkContinuous
    { toFun := fun z => mkOfCompact ⟨fun t => (z t).1, continuous_fst.comp z.continuous⟩
      map_add' := fun _ _ => BoundedContinuousFunction.ext fun _ => rfl
      map_smul' := fun _ _ => BoundedContinuousFunction.ext fun _ => rfl }
    1 (fun z => by
      change ‖mkOfCompact (⟨fun t : I01 => (z t).1, _⟩ : C(I01, Euc n))‖ ≤ 1 * ‖z‖
      rw [one_mul, BoundedContinuousFunction.norm_le (norm_nonneg z)]
      intro t
      exact (norm_fst_le (z t)).trans (BoundedContinuousFunction.norm_coe_le_norm z t))

def proj2L : PathPair n →L[ℝ] PathOne n :=
  LinearMap.mkContinuous
    { toFun := fun z => mkOfCompact ⟨fun t => (z t).2, continuous_snd.comp z.continuous⟩
      map_add' := fun _ _ => BoundedContinuousFunction.ext fun _ => rfl
      map_smul' := fun _ _ => BoundedContinuousFunction.ext fun _ => rfl }
    1 (fun z => by
      change ‖mkOfCompact (⟨fun t : I01 => (z t).2, _⟩ : C(I01, Euc n))‖ ≤ 1 * ‖z‖
      rw [one_mul, BoundedContinuousFunction.norm_le (norm_nonneg z)]
      intro t
      exact (norm_snd_le (z t)).trans (BoundedContinuousFunction.norm_coe_le_norm z t))

def pairL : PathOne n × PathOne n →L[ℝ] PathPair n :=
  LinearMap.mkContinuous
    { toFun := fun p => mkOfCompact ⟨fun t => (p.1 t, p.2 t), p.1.continuous.prodMk p.2.continuous⟩
      map_add' := fun _ _ => BoundedContinuousFunction.ext fun _ => rfl
      map_smul' := fun _ _ => BoundedContinuousFunction.ext fun _ => rfl }
    1 (fun p => by
      change ‖mkOfCompact (⟨fun t : I01 => (p.1 t, p.2 t), _⟩ : C(I01, Euc n × Euc n))‖ ≤ 1 * ‖p‖
      rw [one_mul, BoundedContinuousFunction.norm_le (norm_nonneg p)]
      intro t
      exact max_le ((BoundedContinuousFunction.norm_coe_le_norm p.1 t).trans (le_max_left _ _))
        ((BoundedContinuousFunction.norm_coe_le_norm p.2 t).trans (le_max_right _ _)))

def constPairL : Euc n × Euc n →L[ℝ] PathPair n :=
  LinearMap.mkContinuous
    { toFun := fun p => BoundedContinuousFunction.const I01 p
      map_add' := fun _ _ => BoundedContinuousFunction.ext fun _ => rfl
      map_smul' := fun _ _ => BoundedContinuousFunction.ext fun _ => rfl }
    1 (fun p => by
      change ‖BoundedContinuousFunction.const I01 p‖ ≤ 1 * ‖p‖
      rw [one_mul, BoundedContinuousFunction.norm_le (norm_nonneg p)]
      intro _; exact le_rfl)

def evalAtL (t : I01) : PathPair n →L[ℝ] Euc n × Euc n :=
  LinearMap.mkContinuous
    { toFun := fun z => z t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun z => by rw [one_mul]; exact BoundedContinuousFunction.norm_coe_le_norm z t)

def dpsi0Equiv : PathPair n ≃L[ℝ] PathPair n :=
  { toLinearEquiv :=
      { toFun := fun h => pairL (proj1L h - intOp (proj2L h), proj2L h)
        invFun := fun h => pairL (proj1L h + intOp (proj2L h), proj2L h)
        map_add' := fun h₁ h₂ => BoundedContinuousFunction.ext fun t => by
          apply Prod.ext
          · change (h₁ t).1 + (h₂ t).1 - intOp (proj2L h₁ + proj2L h₂) t =
              ((h₁ t).1 - intOp (proj2L h₁) t) + ((h₂ t).1 - intOp (proj2L h₂) t)
            rw [map_add]; simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]; abel
          · rfl
        map_smul' := fun c h => BoundedContinuousFunction.ext fun t => by
          apply Prod.ext
          · change c • (h t).1 - intOp (c • proj2L h) t = c • ((h t).1 - intOp (proj2L h) t)
            rw [map_smul]; simp only [BoundedContinuousFunction.coe_smul, smul_sub]
          · rfl
        left_inv := fun h => BoundedContinuousFunction.ext fun t => by
          apply Prod.ext
          · change (h t).1 - intOp (proj2L h) t + intOp (proj2L h) t = (h t).1
            abel
          · rfl
        right_inv := fun h => BoundedContinuousFunction.ext fun t => by
          apply Prod.ext
          · change (h t).1 + intOp (proj2L h) t - intOp (proj2L h) t = (h t).1
            abel
          · rfl }
    continuous_toFun :=
      (pairL.comp ((proj1L - intOp.comp proj2L).prod proj2L)).continuous
    continuous_invFun :=
      (pairL.comp ((proj1L + intOp.comp proj2L).prod proj2L)).continuous }

namespace LocalMetric

variable (M : LocalMetric n)

def quadF (x : Euc n × Euc n) : Euc n := M.ΓVec x.1 x.2 x.2

lemma quadF_contDiffOn : ContDiffOn ℝ 2 M.quadF (ball M.a₀ M.r₁ ×ˢ univ) := by
  have hpi : ContDiffOn ℝ 2 (fun x : Euc n × Euc n =>
      fun l : Fin n => ∑ i, ∑ j, M.Γ x.1 l i j * x.2.ofLp i * x.2.ofLp j) (ball M.a₀ M.r₁ ×ˢ univ) := by
    rw [contDiffOn_pi]
    intro l
    refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
    have hΓ : ContDiffOn ℝ 2 (fun x : Euc n × Euc n => M.Γ x.1 l i j) (ball M.a₀ M.r₁ ×ˢ univ) :=
      (M.Γ_contDiffOn l i j).comp contDiffOn_fst (fun x hx => hx.1)
    have hvi : ContDiffOn ℝ 2 (fun x : Euc n × Euc n => x.2.ofLp i) (ball M.a₀ M.r₁ ×ˢ univ) := by
      let piL : Euc n →L[ℝ] ℝ := EuclideanSpace.proj i
      exact (piL.contDiff.comp contDiff_snd).contDiffOn
    have hvj : ContDiffOn ℝ 2 (fun x : Euc n × Euc n => x.2.ofLp j) (ball M.a₀ M.r₁ ×ˢ univ) := by
      let pjL : Euc n →L[ℝ] ℝ := EuclideanSpace.proj j
      exact (pjL.contDiff.comp contDiff_snd).contDiffOn
    exact (hΓ.mul hvi).mul hvj
  exact ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toContinuousLinearEquiv.contDiff).comp_contDiffOn hpi

def dquadF (x : Euc n × Euc n) : (Euc n × Euc n) →L[ℝ] Euc n :=
  fderiv ℝ M.quadF x

lemma dquadF_continuousOn : ContinuousOn M.dquadF (ball M.a₀ M.r₁ ×ˢ univ) := by
  have hopen : IsOpen (ball M.a₀ M.r₁ ×ˢ (univ : Set (Euc n))) := isOpen_ball.prod isOpen_univ
  have hfd : ContDiffOn ℝ 1 (fun x => fderivWithin ℝ M.quadF (ball M.a₀ M.r₁ ×ˢ univ) x)
      (ball M.a₀ M.r₁ ×ˢ univ) :=
    M.quadF_contDiffOn.fderivWithin hopen.uniqueDiffOn (by norm_num)
  have hcongr : ContDiffOn ℝ 1 M.dquadF (ball M.a₀ M.r₁ ×ˢ univ) :=
    hfd.congr fun x hx => (fderivWithin_of_isOpen hopen hx).symm
  exact hcongr.continuousOn

lemma dquadF_zero (p : Euc n) (hp : p ∈ ball M.a₀ M.r₁) :
    M.dquadF (p, 0) = 0 := by
  have hdist : 0 < M.r₁ - dist p M.a₀ := sub_pos.mpr hp
  set ρ : ℝ := (M.r₁ - dist p M.a₀) / 2 with hρ_def
  have hρ : 0 < ρ := half_pos hdist
  have hKsub : closedBall p ρ ⊆ ball M.a₀ M.r₁ := fun y hy => by
    show dist y M.a₀ < M.r₁
    have h1 : dist y p ≤ ρ := hy
    linarith [dist_triangle y p M.a₀, hρ_def]
  have hΓ_bd : ∀ l i j : Fin n, ∃ C ≥ 0, ∀ y ∈ closedBall p ρ, |M.Γ y l i j| ≤ C := by
    intro l i j
    have hc : ContinuousOn (fun y => |M.Γ y l i j|) (closedBall p ρ) :=
      continuous_abs.comp_continuousOn ((M.Γ_contDiffOn l i j).continuousOn.mono hKsub)
    obtain ⟨y₀, _, hmax⟩ := (isCompact_closedBall p ρ).exists_isMaxOn ⟨p, mem_closedBall_self hρ.le⟩ hc
    exact ⟨|M.Γ y₀ l i j|, abs_nonneg _, fun y hy => hmax hy⟩
  choose CΓ hCΓ_nn hCΓ_bd using hΓ_bd
  let K : ℝ := ∑ l : Fin n, ∑ i : Fin n, ∑ j : Fin n, CΓ l i j
  have hK_nn : 0 ≤ K :=
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hCΓ_nn l i j
  have hquad_le : ∀ y ∈ closedBall p ρ, ∀ w : Euc n, ‖M.quadF (y, w)‖ ≤ K * ‖w‖ ^ 2 := by
    intro y hy w
    have hcoord : ∀ l : Fin n, |(M.quadF (y, w)).ofLp l| ≤ (∑ i, ∑ j, CΓ l i j) * ‖w‖ ^ 2 := by
      intro l
      change |∑ i, ∑ j, M.Γ y l i j * w.ofLp i * w.ofLp j| ≤ _
      calc |∑ i, ∑ j, M.Γ y l i j * w.ofLp i * w.ofLp j|
          ≤ ∑ i, |∑ j, M.Γ y l i j * w.ofLp i * w.ofLp j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ∑ j, |M.Γ y l i j * w.ofLp i * w.ofLp j| :=
            Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ∑ j, CΓ l i j * ‖w‖ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul, abs_mul, sq]
            have hwi : |w.ofLp i| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w i
            have hwj : |w.ofLp j| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w j
            have h1 := mul_le_mul (hCΓ_bd l i j y hy) hwi (abs_nonneg _) (hCΓ_nn l i j)
            have h2 := mul_le_mul h1 hwj (abs_nonneg _) (mul_nonneg (hCΓ_nn l i j) (norm_nonneg _))
            linarith
        _ = (∑ i, ∑ j, CΓ l i j) * ‖w‖ ^ 2 := by simp only [Finset.sum_mul]
    have hvec_exp : M.quadF (y, w) = ∑ l : Fin n, (M.quadF (y, w)).ofLp l • e l := by
      ext m; simp [e, Pi.single_apply]
    calc ‖M.quadF (y, w)‖
        = ‖∑ l : Fin n, (M.quadF (y, w)).ofLp l • e l‖ := congrArg norm hvec_exp
      _ ≤ ∑ l : Fin n, ‖(M.quadF (y, w)).ofLp l • e l‖ := norm_sum_le _ _
      _ = ∑ l : Fin n, |(M.quadF (y, w)).ofLp l| := by simp [e, norm_smul]
      _ ≤ ∑ l : Fin n, (∑ i, ∑ j, CΓ l i j) * ‖w‖ ^ 2 := Finset.sum_le_sum fun l _ => hcoord l
      _ = K * ‖w‖ ^ 2 := by simp only [K, Finset.sum_mul]
  have hfd0 : HasFDerivAt M.quadF (0 : (Euc n × Euc n) →L[ℝ] Euc n) (p, 0) := by
    rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    let δ : ℝ := min ρ (c / (K + 1))
    have hδ : 0 < δ := lt_min hρ (div_pos hc (by linarith))
    filter_upwards [ball_mem_nhds (p, (0 : Euc n)) hδ] with x hx
    have hx1 : x.1 ∈ closedBall p ρ := by
      have h1 : dist x.1 p ≤ dist x (p, (0 : Euc n)) := by
        simpa [dist_eq_norm] using norm_fst_le (x - (p, (0 : Euc n)))
      exact h1.trans (hx.le.trans (min_le_left _ _))
    have hx2 : ‖x.2‖ ≤ ‖x - (p, (0 : Euc n))‖ := by
      simpa using norm_snd_le (x - (p, (0 : Euc n)))
    have hx_norm : ‖x - (p, (0 : Euc n))‖ ≤ c / (K + 1) := by
      simpa [dist_eq_norm] using hx.le.trans (min_le_right _ _)
    have hq0 : M.quadF (p, 0) = 0 := by ext l; simp [quadF, ΓVec]
    rw [hq0, sub_zero, zero_apply, sub_zero]
    calc ‖M.quadF x‖
        ≤ K * ‖x.2‖ ^ 2 := hquad_le x.1 hx1 x.2
      _ ≤ K * ‖x - (p, (0 : Euc n))‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx2 2) hK_nn
      _ = (K * ‖x - (p, (0 : Euc n))‖) * ‖x - (p, (0 : Euc n))‖ := by ring
      _ ≤ c * ‖x - (p, (0 : Euc n))‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          calc K * ‖x - (p, (0 : Euc n))‖
              ≤ K * (c / (K + 1)) := mul_le_mul_of_nonneg_left hx_norm hK_nn
            _ ≤ (K + 1) * (c / (K + 1)) := mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hc.le (by linarith))
            _ = c := mul_div_cancel₀ c (by linarith)
  exact hfd0.fderiv

def U_V : Set (PathPair n) := {z | ∀ t : I01, (z t).1 ∈ ball M.a₀ M.r₁}

lemma isOpen_U_V : IsOpen M.U_V := by
  rw [Metric.isOpen_iff]
  intro z hz
  have hcomp : IsCompact (Set.univ : Set I01) := isCompact_univ
  have hcont : ContinuousOn (fun t : I01 => M.r₁ - dist (z t).1 M.a₀) univ :=
    (continuous_const.sub ((continuous_fst.comp z.continuous).dist continuous_const)).continuousOn
  obtain ⟨t₀, _, ht₀⟩ := hcomp.exists_isMinOn ⟨⟨0, left_mem_Icc.mpr zero_le_one⟩, trivial⟩ hcont
  have hpos : 0 < M.r₁ - dist (z t₀).1 M.a₀ := sub_pos.mpr (hz t₀)
  refine ⟨M.r₁ - dist (z t₀).1 M.a₀, hpos, fun w hw t => ?_⟩
  have h1 : dist (w t).1 (z t).1 < M.r₁ - dist (z t₀).1 M.a₀ :=
    calc dist (w t).1 (z t).1 ≤ dist (w t) (z t) := by
            simpa [dist_eq_norm] using norm_fst_le (w t - z t)
      _ ≤ dist w z := BoundedContinuousFunction.dist_coe_le_dist t
      _ < M.r₁ - dist (z t₀).1 M.a₀ := hw
  have h2 : M.r₁ - dist (z t₀).1 M.a₀ ≤ M.r₁ - dist (z t).1 M.a₀ := ht₀ trivial
  have htri : dist (w t).1 M.a₀ ≤ dist (w t).1 (z t).1 + dist (z t).1 M.a₀ := dist_triangle _ _ _
  show dist (w t).1 M.a₀ < M.r₁
  linarith

def quadOp (z : PathPair n) : PathOne n :=
  if h : Continuous (fun t : I01 => M.quadF (z t)) then mkOfCompact ⟨_, h⟩ else 0

lemma quadOp_apply {z : PathPair n} (hz : z ∈ M.U_V) (t : I01) :
    M.quadOp z t = M.quadF (z t) := by
  have hc : Continuous (fun s : I01 => M.quadF (z s)) :=
    M.quadF_contDiffOn.continuousOn.comp_continuous z.continuous fun s => ⟨hz s, trivial⟩
  simp [quadOp, hc]

def dquadOp (z : PathPair n) : PathPair n →L[ℝ] PathOne n :=
  if h : Continuous (fun t : I01 => M.dquadF (z t)) then
    let C : ℝ := ‖mkOfCompact (⟨fun t : I01 => M.dquadF (z t), h⟩ : C(I01, (Euc n × Euc n) →L[ℝ] Euc n))‖
    LinearMap.mkContinuous
      { toFun := fun u =>
          mkOfCompact ⟨fun t => M.dquadF (z t) (u t), h.clm_apply u.continuous⟩
        map_add' := fun u₁ u₂ => BoundedContinuousFunction.ext fun t => map_add (M.dquadF (z t)) (u₁ t) (u₂ t)
        map_smul' := fun c u => BoundedContinuousFunction.ext fun t => map_smul (M.dquadF (z t)) c (u t) }
      C (fun u => by
        change ‖mkOfCompact (⟨fun t : I01 => M.dquadF (z t) (u t), _⟩ : C(I01, Euc n))‖ ≤ C * ‖u‖
        have hC0 : 0 ≤ C := norm_nonneg (mkOfCompact (⟨fun s : I01 => M.dquadF (z s), h⟩ : C(I01, _)))
        refine (BoundedContinuousFunction.norm_le (mul_nonneg hC0 (norm_nonneg u))).mpr ?_
        intro t
        have h1 : ‖M.dquadF (z t)‖ ≤ C :=
          BoundedContinuousFunction.norm_coe_le_norm
            (mkOfCompact (⟨fun s : I01 => M.dquadF (z s), h⟩ : C(I01, _))) t
        calc ‖M.dquadF (z t) (u t)‖ ≤ ‖M.dquadF (z t)‖ * ‖u t‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ C * ‖u‖ := mul_le_mul h1 (BoundedContinuousFunction.norm_coe_le_norm u t) (norm_nonneg _) hC0)
  else 0

lemma dquadOp_apply {z : PathPair n} (hz : z ∈ M.U_V) (u : PathPair n) (t : I01) :
    M.dquadOp z u t = M.dquadF (z t) (u t) := by
  have hc : Continuous (fun s : I01 => M.dquadF (z s)) :=
    M.dquadF_continuousOn.comp_continuous z.continuous fun s => ⟨hz s, trivial⟩
  simp [dquadOp, hc]

private lemma exists_compact_box {z : PathPair n} (hz : z ∈ M.U_V) :
    ∃ ρ > 0, ∃ R > 0,
      let K : Set (Euc n × Euc n) := closedBall M.a₀ (M.r₁ - ρ) ×ˢ closedBall 0 (R + ρ)
      IsCompact K ∧ K ⊆ ball M.a₀ M.r₁ ×ˢ univ ∧ ∀ t : I01, closedBall (z t) ρ ⊆ K := by
  have hcomp : IsCompact (Set.univ : Set I01) := isCompact_univ
  have hcont1 : ContinuousOn (fun t : I01 => M.r₁ - dist (z t).1 M.a₀) univ :=
    (continuous_const.sub ((continuous_fst.comp z.continuous).dist continuous_const)).continuousOn
  obtain ⟨t₀, _, ht₀⟩ := hcomp.exists_isMinOn ⟨⟨0, left_mem_Icc.mpr zero_le_one⟩, trivial⟩ hcont1
  set ρ : ℝ := (M.r₁ - dist (z t₀).1 M.a₀) / 3 with hρ_def
  have hρ : 0 < ρ := by
    have hpos : 0 < M.r₁ - dist (z t₀).1 M.a₀ := sub_pos.mpr (hz t₀)
    linarith [hρ_def]
  set R : ℝ := ‖z‖ + 1 with hR_def
  have hR : 0 < R := by linarith [norm_nonneg z, hR_def]
  refine ⟨ρ, hρ, R, hR, (isCompact_closedBall _ _).prod (isCompact_closedBall _ _), ?_, ?_⟩
  · rintro ⟨x, y⟩ ⟨hx, _⟩
    refine ⟨?_, trivial⟩
    have hx' : dist x M.a₀ ≤ M.r₁ - ρ := hx
    show dist x M.a₀ < M.r₁
    linarith
  · intro t ⟨x, y⟩ hxy
    have hxy' : dist (x, y) (z t) ≤ ρ := hxy
    have hx1 : dist x (z t).1 ≤ ρ :=
      (by simpa [dist_eq_norm] using norm_fst_le ((x, y) - z t) : dist x (z t).1 ≤ dist (x, y) (z t)).trans hxy'
    have hy1 : dist y (z t).2 ≤ ρ :=
      (by simpa [dist_eq_norm] using norm_snd_le ((x, y) - z t) : dist y (z t).2 ≤ dist (x, y) (z t)).trans hxy'
    refine ⟨?_, ?_⟩
    · show dist x M.a₀ ≤ M.r₁ - ρ
      have hmin : M.r₁ - dist (z t₀).1 M.a₀ ≤ M.r₁ - dist (z t).1 M.a₀ := ht₀ trivial
      have htri := dist_triangle x (z t).1 M.a₀
      linarith
    · show dist y 0 ≤ R + ρ
      have hz2 : dist (z t).2 0 ≤ R := by
        rw [dist_zero_right]
        exact ((norm_snd_le (z t)).trans (BoundedContinuousFunction.norm_coe_le_norm z t)).trans (by linarith)
      linarith [dist_triangle y (z t).2 0]

lemma quadOp_hasStrictFDerivAt {z : PathPair n} (hz : z ∈ M.U_V) :
    HasStrictFDerivAt M.quadOp (M.dquadOp z) z := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨ρ, hρ, R, _, hKcomp, hKsub, hKball⟩ := M.exists_compact_box hz
  let K : Set (Euc n × Euc n) := closedBall M.a₀ (M.r₁ - ρ) ×ˢ closedBall 0 (R + ρ)
  have huc : UniformContinuousOn M.dquadF K :=
    hKcomp.uniformContinuousOn_of_continuous (M.dquadF_continuousOn.mono hKsub)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₁, hδ₁, hδ₁_spec⟩ := huc ε hε
  let δ : ℝ := min ρ δ₁
  have hδ : 0 < δ := lt_min hρ hδ₁
  have hmem : (ball z δ ×ˢ ball z δ) ∈ 𝓝 (z, z) :=
    (isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hδ, mem_ball_self hδ⟩
  filter_upwards [hmem] with ⟨z₁, z₂⟩ ⟨hz₁, hz₂⟩
  have hz₁U : z₁ ∈ M.U_V := fun t => by
    have h1 : z₁ t ∈ closedBall (z t) ρ :=
      mem_closedBall.mpr ((BoundedContinuousFunction.dist_coe_le_dist t).trans (hz₁.le.trans (min_le_left _ _)))
    exact (hKsub (hKball t h1)).1
  have hz₂U : z₂ ∈ M.U_V := fun t => by
    have h2 : z₂ t ∈ closedBall (z t) ρ :=
      mem_closedBall.mpr ((BoundedContinuousFunction.dist_coe_le_dist t).trans (hz₂.le.trans (min_le_left _ _)))
    exact (hKsub (hKball t h2)).1
  rw [BoundedContinuousFunction.norm_le (mul_nonneg hε.le (norm_nonneg _))]
  intro t
  simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply, M.quadOp_apply hz₁U, M.quadOp_apply hz₂U,
    M.dquadOp_apply hz]
  let g : (Euc n × Euc n) → Euc n := fun x => M.quadF x - M.dquadF (z t) x
  have hopen : IsOpen (ball M.a₀ M.r₁ ×ˢ (univ : Set (Euc n))) := isOpen_ball.prod isOpen_univ
  have hg_deriv : ∀ x ∈ ball (z t) δ, HasFDerivWithinAt g (M.dquadF x - M.dquadF (z t)) (ball (z t) δ) x := by
    intro x hx
    have hxK : x ∈ K := hKball t (mem_closedBall.mpr (hx.le.trans (min_le_left _ _)))
    have hq : HasFDerivAt M.quadF (M.dquadF x) x :=
      ((M.quadF_contDiffOn.contDiffAt (hopen.mem_nhds (hKsub hxK))).differentiableAt (by decide)).hasFDerivAt
    exact (hq.sub (M.dquadF (z t)).hasFDerivAt).hasFDerivWithinAt
  have hg_bound : ∀ x ∈ ball (z t) δ, ‖M.dquadF x - M.dquadF (z t)‖ ≤ ε := by
    intro x hx
    have hxK : x ∈ K := hKball t (mem_closedBall.mpr (hx.le.trans (min_le_left _ _)))
    have hzK : z t ∈ K := hKball t (mem_closedBall_self hρ.le)
    have hd : dist x (z t) < δ₁ := lt_of_lt_of_le hx (min_le_right _ _)
    simpa [dist_eq_norm] using (hδ₁_spec x hxK (z t) hzK hd).le
  have hz₁t : z₁ t ∈ ball (z t) δ := (BoundedContinuousFunction.dist_coe_le_dist t).trans_lt hz₁
  have hz₂t : z₂ t ∈ ball (z t) δ := (BoundedContinuousFunction.dist_coe_le_dist t).trans_lt hz₂
  have hmvt := (convex_ball (z t) δ).norm_image_sub_le_of_norm_hasFDerivWithin_le hg_deriv hg_bound hz₂t hz₁t
  have hge : g (z₁ t) - g (z₂ t) = M.quadF (z₁ t) - M.quadF (z₂ t) - M.dquadF (z t) (z₁ t - z₂ t) := by
    simp only [g, map_sub]; abel
  rw [hge] at hmvt
  calc ‖M.quadF (z₁ t) - M.quadF (z₂ t) - M.dquadF (z t) ((z₁ - z₂) t)‖
      ≤ ε * ‖z₁ t - z₂ t‖ := hmvt
    _ ≤ ε * ‖z₁ - z₂‖ := mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm (z₁ - z₂) t) hε.le

lemma dquadOp_norm_sub_lt {z : PathPair n} (hz : z ∈ M.U_V) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ w ∈ M.U_V, dist w z < δ → ‖M.dquadOp w - M.dquadOp z‖ < ε := by
  obtain ⟨ρ, hρ, R, _, hKcomp, hKsub, hKball⟩ := M.exists_compact_box hz
  let K : Set (Euc n × Euc n) := closedBall M.a₀ (M.r₁ - ρ) ×ˢ closedBall 0 (R + ρ)
  have huc : UniformContinuousOn M.dquadF K :=
    hKcomp.uniformContinuousOn_of_continuous (M.dquadF_continuousOn.mono hKsub)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₁, hδ₁, hδ₁_spec⟩ := huc (ε / 2) (half_pos hε)
  refine ⟨min ρ δ₁, lt_min hρ hδ₁, fun w hw hwd => ?_⟩
  refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le fun u => ?_) (half_lt_self hε)
  refine (BoundedContinuousFunction.norm_le (mul_nonneg (half_pos hε).le (norm_nonneg u))).mpr ?_
  intro t
  simp only [_root_.sub_apply, BoundedContinuousFunction.coe_sub, Pi.sub_apply,
    M.dquadOp_apply hw, M.dquadOp_apply hz]
  have hwt : dist (w t) (z t) < δ₁ := (BoundedContinuousFunction.dist_coe_le_dist t).trans_lt (lt_of_lt_of_le hwd (min_le_right _ _))
  have hwK : w t ∈ K := hKball t (mem_closedBall.mpr ((BoundedContinuousFunction.dist_coe_le_dist t).trans (hwd.le.trans (min_le_left _ _))))
  have hzK : z t ∈ K := hKball t (mem_closedBall_self hρ.le)
  have hd : ‖M.dquadF (w t) - M.dquadF (z t)‖ ≤ ε / 2 := by
    simpa [dist_eq_norm] using (hδ₁_spec (w t) hwK (z t) hzK hwt).le
  calc ‖M.dquadF (w t) (u t) - M.dquadF (z t) (u t)‖
      = ‖(M.dquadF (w t) - M.dquadF (z t)) (u t)‖ := rfl
    _ ≤ ‖M.dquadF (w t) - M.dquadF (z t)‖ * ‖u t‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (ε / 2) * ‖u‖ := mul_le_mul hd (BoundedContinuousFunction.norm_coe_le_norm u t) (norm_nonneg _) (half_pos hε).le

def psi (z : PathPair n) : PathPair n :=
  pairL (proj1L z - intOp (proj2L z), proj2L z + intOp (M.quadOp z))

def dpsi (z : PathPair n) : PathPair n →L[ℝ] PathPair n :=
  pairL.comp ((proj1L - intOp.comp proj2L).prod (proj2L + intOp.comp (M.dquadOp z)))

lemma psi_hasStrictFDerivAt {z : PathPair n} (hz : z ∈ M.U_V) :
    HasStrictFDerivAt M.psi (M.dpsi z) z := by
  have h1 : HasStrictFDerivAt (fun w => proj1L w - intOp (proj2L w)) (proj1L - intOp.comp proj2L) z :=
    (proj1L - intOp.comp proj2L).hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (fun w => proj2L w + intOp (M.quadOp w))
      (proj2L + intOp.comp (M.dquadOp z)) z :=
    proj2L.hasStrictFDerivAt.add (intOp.hasStrictFDerivAt.comp z (M.quadOp_hasStrictFDerivAt hz))
  exact pairL.hasStrictFDerivAt.comp z (h1.prodMk h2)

def z₀ : PathPair n := constPairL (M.a₀, 0)

lemma z₀_mem_U_V : M.z₀ ∈ M.U_V := fun _ => mem_ball_self M.hr₁

lemma dpsi_z₀_eq : M.dpsi M.z₀ = (dpsi0Equiv (n := n) : PathPair n →L[ℝ] PathPair n) := by
  have hd0 : M.dquadOp M.z₀ = 0 := by
    ext u s l
    have h1 : M.dquadOp M.z₀ u s = M.dquadF (M.z₀ s) (u s) := M.dquadOp_apply M.z₀_mem_U_V u s
    have h2 : M.z₀ s = (M.a₀, 0) := rfl
    rw [h1, h2, M.dquadF_zero M.a₀ (mem_ball_self M.hr₁)]
    rfl
  apply ContinuousLinearMap.ext
  intro h
  apply BoundedContinuousFunction.ext
  intro t
  apply Prod.ext
  · rfl
  · change (h t).2 + intOp (M.dquadOp M.z₀ h) t = (h t).2
    rw [hd0]; simp

lemma dpsi_norm_sub_le {w z : PathPair n} :
    ‖M.dpsi w - M.dpsi z‖ ≤ ‖M.dquadOp w - M.dquadOp z‖ := by
  have hnonneg : 0 ≤ ‖M.dquadOp w - M.dquadOp z‖ := ContinuousLinearMap.opNorm_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ hnonneg fun h => ?_
  refine (BoundedContinuousFunction.norm_le (mul_nonneg hnonneg (norm_nonneg h))).mpr fun t => ?_
  have h1 : ((M.dpsi w - M.dpsi z) h t).1 = 0 := by
    change ((h t).1 - intOp (proj2L h) t) - ((h t).1 - intOp (proj2L h) t) = 0
    exact sub_self _
  have h2 : ((M.dpsi w - M.dpsi z) h t).2 = intOp ((M.dquadOp w - M.dquadOp z) h) t := by
    change ((h t).2 + intOp (M.dquadOp w h) t) - ((h t).2 + intOp (M.dquadOp z h) t) = _
    rw [_root_.sub_apply, map_sub]
    simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply]
    abel
  have hnorm2 : ‖intOp ((M.dquadOp w - M.dquadOp z) h) t‖ ≤ ‖M.dquadOp w - M.dquadOp z‖ * ‖h‖ := by
    calc ‖intOp ((M.dquadOp w - M.dquadOp z) h) t‖
        ≤ ‖intOp ((M.dquadOp w - M.dquadOp z) h)‖ := BoundedContinuousFunction.norm_coe_le_norm _ t
      _ ≤ ‖intOp (n := n)‖ * ‖(M.dquadOp w - M.dquadOp z) h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (‖M.dquadOp w - M.dquadOp z‖ * ‖h‖) := by
          have hint : ‖intOp (n := n)‖ ≤ 1 := by
            refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
            rw [one_mul]
            refine (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr fun s => ?_
            have hle : ∀ u ∈ Set.uIoc (0 : ℝ) s.1, ‖f (proj01 u)‖ ≤ ‖f‖ :=
              fun u _ => BoundedContinuousFunction.norm_coe_le_norm f (proj01 u)
            calc ‖intFun f s.1‖ ≤ ‖f‖ * |s.1 - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hle
              _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left (by rw [sub_zero, abs_of_nonneg s.2.1]; exact s.2.2) (norm_nonneg f)
              _ = ‖f‖ := mul_one _
          exact mul_le_mul hint (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) zero_le_one
      _ = ‖M.dquadOp w - M.dquadOp z‖ * ‖h‖ := one_mul _
  exact max_le (by rw [h1, norm_zero]; positivity) (by rw [h2]; exact hnorm2)

lemma psi_z₀ : M.psi M.z₀ = M.z₀ := by
  apply BoundedContinuousFunction.ext
  intro t
  have hq : M.quadOp M.z₀ = 0 := by
    apply BoundedContinuousFunction.ext
    intro s
    rw [M.quadOp_apply M.z₀_mem_U_V]
    ext l
    simp [quadF, ΓVec, z₀, constPairL]
  apply Prod.ext
  · change M.a₀ - intFun (proj2L M.z₀) t.1 = M.a₀
    have h0 : intFun (proj2L M.z₀) t.1 = 0 := by
      simp [intFun, proj2L, z₀, constPairL]
    rw [h0, sub_zero]
  · change (0 : Euc n) + intOp (M.quadOp M.z₀) t = 0
    rw [hq]; simp

lemma psi_hasStrictFDerivAt_z₀ :
    HasStrictFDerivAt M.psi (dpsi0Equiv (n := n) : PathPair n →L[ℝ] PathPair n) M.z₀ := by
  rw [← M.dpsi_z₀_eq]; exact M.psi_hasStrictFDerivAt M.z₀_mem_U_V

def psiHomeo : OpenPartialHomeomorph (PathPair n) (PathPair n) :=
  M.psi_hasStrictFDerivAt_z₀.toOpenPartialHomeomorph M.psi

def geod (p v : Euc n) : PathPair n :=
  M.psiHomeo.symm (constPairL (p, v))

def exp (p v : Euc n) : Euc n :=
  (M.geod p v ⟨1, right_mem_Icc.mpr zero_le_one⟩).1

def scalePath (z : PathPair n) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : PathPair n :=
  mkOfCompact ⟨fun t =>
    ((z ⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩).1,
     s • (z ⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩).2),
    by
      have hs_map : Continuous (fun t : I01 =>
          (⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩ : I01)) :=
        Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _
      exact (continuous_fst.comp (z.continuous.comp hs_map)).prodMk
        ((continuous_snd.comp (z.continuous.comp hs_map)).const_smul s)⟩

def revPath (z : PathPair n) : PathPair n :=
  mkOfCompact ⟨fun t =>
    ((z ⟨1 - t.1, ⟨sub_nonneg.mpr t.2.2, sub_le_self 1 t.2.1⟩⟩).1,
     -(z ⟨1 - t.1, ⟨sub_nonneg.mpr t.2.2, sub_le_self 1 t.2.1⟩⟩).2),
    by
      have hr_map : Continuous (fun t : I01 =>
          (⟨1 - t.1, ⟨sub_nonneg.mpr t.2.2, sub_le_self 1 t.2.1⟩⟩ : I01)) :=
        Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) _
      exact (continuous_fst.comp (z.continuous.comp hr_map)).prodMk
        ((continuous_snd.comp (z.continuous.comp hr_map)).neg)⟩

lemma exists_geod_radius :
    ∃ r_g > 0,
      ∀ p ∈ ball M.a₀ r_g, ∀ v ∈ ball (0 : Euc n) r_g,
        constPairL (p, v) ∈ M.psiHomeo.target ∧
        M.geod p v ∈ M.U_V ∧
        (∃ L : PathPair n ≃L[ℝ] PathPair n,
          (L : PathPair n →L[ℝ] PathPair n) = M.dpsi (M.geod p v) ∧
          HasStrictFDerivAt M.psiHomeo.symm (L.symm : PathPair n →L[ℝ] PathPair n) (constPairL (p, v))) ∧
        (∀ s (hs : s ∈ Icc (0 : ℝ) 1), scalePath (M.geod p v) s hs ∈ M.psiHomeo.source) ∧
        revPath (M.geod p v) ∈ M.psiHomeo.source := by
  have hz₀_src : M.z₀ ∈ M.psiHomeo.source := M.psi_hasStrictFDerivAt_z₀.mem_toOpenPartialHomeomorph_source
  have hz₀_tgt : M.z₀ ∈ M.psiHomeo.target := by
    rw [← M.psi_z₀]; exact M.psi_hasStrictFDerivAt_z₀.image_mem_toOpenPartialHomeomorph_target
  let L0inv : PathPair n →L[ℝ] PathPair n := dpsi0Equiv (n := n).symm
  have hL0inv_pos : 0 < ‖L0inv‖ + 1 := by linarith [ContinuousLinearMap.opNorm_nonneg L0inv]
  let ε_u : ℝ := (‖L0inv‖ + 1)⁻¹
  have hε_u : 0 < ε_u := inv_pos.mpr hL0inv_pos
  obtain ⟨δ_u, hδ_u, hδ_u_spec⟩ := M.dquadOp_norm_sub_lt M.z₀_mem_U_V hε_u
  obtain ⟨δ_src, hδ_src, hδ_src_sub⟩ := Metric.isOpen_iff.mp (M.psiHomeo.open_source.inter M.isOpen_U_V) M.z₀ ⟨hz₀_src, M.z₀_mem_U_V⟩
  let δ : ℝ := min δ_src δ_u
  have hδ : 0 < δ := lt_min hδ_src hδ_u
  have hδ_good : ∀ z ∈ ball M.z₀ δ, z ∈ M.psiHomeo.source ∧ z ∈ M.U_V ∧ IsUnit (M.dpsi z) := by
    intro z hz
    have h1 := hδ_src_sub (Metric.ball_subset_ball (min_le_left _ _) hz)
    have h2 : dist z M.z₀ < δ_u := lt_of_lt_of_le hz (min_le_right _ _)
    have hnorm : ‖M.dpsi z - M.dpsi M.z₀‖ < ε_u := M.dpsi_norm_sub_le.trans_lt (hδ_u_spec z h1.2 h2)
    have hunit : IsUnit (M.dpsi z) := by
      have hprod_lt : ‖L0inv * (M.dpsi M.z₀ - M.dpsi z)‖ < 1 := by
        have hrev : ‖M.dpsi M.z₀ - M.dpsi z‖ = ‖M.dpsi z - M.dpsi M.z₀‖ := by
          rw [show M.dpsi M.z₀ - M.dpsi z = -(M.dpsi z - M.dpsi M.z₀) by abel,
            ContinuousLinearMap.opNorm_neg]
        calc ‖L0inv * (M.dpsi M.z₀ - M.dpsi z)‖
            ≤ ‖L0inv‖ * ‖M.dpsi M.z₀ - M.dpsi z‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ = ‖L0inv‖ * ‖M.dpsi z - M.dpsi M.z₀‖ := by rw [hrev]
          _ ≤ ‖L0inv‖ * ε_u := mul_le_mul_of_nonneg_left hnorm.le (ContinuousLinearMap.opNorm_nonneg _)
          _ < (‖L0inv‖ + 1) * ε_u := mul_lt_mul_of_pos_right (lt_add_one ‖L0inv‖) hε_u
          _ = 1 := mul_inv_cancel₀ hL0inv_pos.ne'
      have hu1 : IsUnit (1 - L0inv * (M.dpsi M.z₀ - M.dpsi z)) :=
        (Units.oneSub (L0inv * (M.dpsi M.z₀ - M.dpsi z)) hprod_lt).isUnit
      have hL0inv_mul : L0inv * M.dpsi M.z₀ = 1 := by
        rw [M.dpsi_z₀_eq]; exact ContinuousLinearMap.ext fun h => dpsi0Equiv.symm_apply_apply h
      have heq1 : 1 - L0inv * (M.dpsi M.z₀ - M.dpsi z) = L0inv * M.dpsi z := by
        refine ContinuousLinearMap.ext fun h => ?_
        have h1' : (L0inv * M.dpsi M.z₀) h = h := congrArg (fun f : PathPair n →L[ℝ] PathPair n => f h) hL0inv_mul
        change h - L0inv (M.dpsi M.z₀ h - M.dpsi z h) = L0inv (M.dpsi z h)
        rw [map_sub]
        have h2' : L0inv (M.dpsi M.z₀ h) = h := h1'
        rw [h2']; abel
      rw [heq1] at hu1
      have hL0u : IsUnit (M.dpsi M.z₀) := by
        rw [M.dpsi_z₀_eq]
        exact ⟨⟨(dpsi0Equiv (n := n) : PathPair n →L[ℝ] PathPair n), L0inv,
          ContinuousLinearMap.ext fun h => dpsi0Equiv.apply_symm_apply h,
          ContinuousLinearMap.ext fun h => dpsi0Equiv.symm_apply_apply h⟩, rfl⟩
      have heq2 : M.dpsi M.z₀ * (L0inv * M.dpsi z) = M.dpsi z := by
        rw [← mul_assoc, show M.dpsi M.z₀ * L0inv = 1 by
          rw [M.dpsi_z₀_eq]; exact ContinuousLinearMap.ext fun h => dpsi0Equiv.apply_symm_apply h, one_mul]
      rw [← heq2]
      exact hL0u.mul hu1
    exact ⟨h1.1, h1.2, hunit⟩
  have hcont_symm : ContinuousAt M.psiHomeo.symm M.z₀ := M.psiHomeo.continuousAt_symm hz₀_tgt
  have hsymm_z₀ : M.psiHomeo.symm M.z₀ = M.z₀ := by
    have h1 := M.psiHomeo.left_inv hz₀_src
    have h2 : M.psiHomeo M.z₀ = M.z₀ := by change M.psi M.z₀ = M.z₀; exact M.psi_z₀
    rwa [h2] at h1
  have hpre : M.psiHomeo.target ∩ M.psiHomeo.symm ⁻¹' (ball M.z₀ (δ / 2)) ∈ 𝓝 M.z₀ :=
    Filter.inter_mem (M.psiHomeo.open_target.mem_nhds hz₀_tgt)
      (hcont_symm.preimage_mem_nhds (by rw [hsymm_z₀]; exact ball_mem_nhds _ (half_pos hδ)))
  have hpre2 : constPairL ⁻¹' (M.psiHomeo.target ∩ M.psiHomeo.symm ⁻¹' (ball M.z₀ (δ / 2))) ∈ 𝓝 (M.a₀, (0 : Euc n)) :=
    constPairL.continuous.continuousAt.preimage_mem_nhds hpre
  obtain ⟨r_g, hr_g, hrg_sub⟩ := Metric.mem_nhds_iff.mp hpre2
  refine ⟨r_g, hr_g, fun p hp v hv => ?_⟩
  have hpv : (p, v) ∈ ball (M.a₀, (0 : Euc n)) r_g := by
    rw [Metric.mem_ball, Prod.dist_eq]; exact max_lt hp hv
  have hmem := hrg_sub hpv
  have htgt : constPairL (p, v) ∈ M.psiHomeo.target := hmem.1
  have hgeod_ball2 : M.geod p v ∈ ball M.z₀ (δ / 2) := hmem.2
  have hgeod_ball : M.geod p v ∈ ball M.z₀ δ := Metric.ball_subset_ball (half_le_self hδ.le) hgeod_ball2
  have hgeod_good := hδ_good (M.geod p v) hgeod_ball
  refine ⟨htgt, hgeod_good.2.1, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := hgeod_good.2.2
    let L : PathPair n ≃L[ℝ] PathPair n :=
      { toLinearEquiv :=
          { toFun := u.val
            invFun := u.inv
            map_add' := map_add _
            map_smul' := map_smul _
            left_inv := fun h => congrArg (fun f : PathPair n →L[ℝ] PathPair n => f h) u.inv_val
            right_inv := fun h => congrArg (fun f : PathPair n →L[ℝ] PathPair n => f h) u.val_inv }
        continuous_toFun := u.val.continuous
        continuous_invFun := u.inv.continuous }
    have hL : (L : PathPair n →L[ℝ] PathPair n) = M.dpsi (M.geod p v) :=
      ContinuousLinearMap.ext fun h => congrArg (fun f : PathPair n →L[ℝ] PathPair n => f h) hu
    refine ⟨L, hL, ?_⟩
    have hfd : HasStrictFDerivAt M.psi (L : PathPair n →L[ℝ] PathPair n) (M.geod p v) := by
      rw [hL]; exact M.psi_hasStrictFDerivAt hgeod_good.2.1
    exact M.psiHomeo.hasStrictFDerivAt_symm htgt hfd
  · intro s hs
    apply (hδ_good _ _).1
    rw [Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖M.geod p v - M.z₀‖ < δ / 2 := by simpa [dist_eq_norm] using hgeod_ball2
    refine lt_of_le_of_lt ((BoundedContinuousFunction.norm_le (half_pos hδ).le).mpr fun t => ?_) (half_lt_self hδ)
    let st : I01 := ⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩
    have hst : ‖M.geod p v st - M.z₀ st‖ ≤ δ / 2 :=
      ((BoundedContinuousFunction.norm_coe_le_norm (M.geod p v - M.z₀) st).trans_lt hnorm).le
    have h1 : ‖(M.geod p v st).1 - M.a₀‖ ≤ δ / 2 := (norm_fst_le (M.geod p v st - M.z₀ st)).trans hst
    have h2 : ‖s • (M.geod p v st).2 - 0‖ ≤ δ / 2 := by
      rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      calc s * ‖(M.geod p v st).2‖ ≤ 1 * ‖(M.geod p v st).2‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
        _ = ‖(M.geod p v st).2 - 0‖ := by simp
        _ ≤ δ / 2 := (norm_snd_le (M.geod p v st - M.z₀ st)).trans hst
    exact max_le h1 h2
  · apply (hδ_good _ _).1
    rw [Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖M.geod p v - M.z₀‖ < δ / 2 := by simpa [dist_eq_norm] using hgeod_ball2
    refine lt_of_le_of_lt ((BoundedContinuousFunction.norm_le (half_pos hδ).le).mpr fun t => ?_) (half_lt_self hδ)
    let rt : I01 := ⟨1 - t.1, ⟨sub_nonneg.mpr t.2.2, sub_le_self 1 t.2.1⟩⟩
    have hrt : ‖M.geod p v rt - M.z₀ rt‖ ≤ δ / 2 :=
      ((BoundedContinuousFunction.norm_coe_le_norm (M.geod p v - M.z₀) rt).trans_lt hnorm).le
    have h1 : ‖(M.geod p v rt).1 - M.a₀‖ ≤ δ / 2 := (norm_fst_le (M.geod p v rt - M.z₀ rt)).trans hrt
    have h2 : ‖-(M.geod p v rt).2 - 0‖ ≤ δ / 2 := by
      rw [sub_zero, norm_neg]
      simpa [z₀, constPairL] using (norm_snd_le (M.geod p v rt - M.z₀ rt)).trans hrt
    exact max_le h1 h2

/- ### Part 2B: Geodesic ODE, constant speed, homogeneity, reversal, and Gauss's Lemma -/

def γExt (p v : Euc n) (t : ℝ) : Euc n :=
  p + intFun (proj2L (M.geod p v)) t

def ξExt (p v : Euc n) (t : ℝ) : Euc n :=
  v - intFun (M.quadOp (M.geod p v)) t

lemma geod_eq_ext {p v : Euc n} (htgt : constPairL (p, v) ∈ M.psiHomeo.target) (t : I01) :
    (M.geod p v t).1 = M.γExt p v t.1 ∧ (M.geod p v t).2 = M.ξExt p v t.1 := by
  have hpsi : M.psi (M.geod p v) = constPairL (p, v) := M.psiHomeo.right_inv htgt
  have ht := congrArg (fun z : PathPair n => z t) hpsi
  have h1 : (M.geod p v t).1 - intFun (proj2L (M.geod p v)) t.1 = p := congrArg Prod.fst ht
  have h2 : (M.geod p v t).2 + intFun (M.quadOp (M.geod p v)) t.1 = v := congrArg Prod.snd ht
  exact ⟨by simp only [γExt]; exact eq_add_of_sub_eq h1,
    by simp only [ξExt]; exact eq_sub_of_add_eq h2⟩

lemma γExt_zero (p v : Euc n) : M.γExt p v 0 = p := by simp [γExt, intFun]
lemma ξExt_zero (p v : Euc n) : M.ξExt p v 0 = v := by simp [ξExt, intFun]

lemma γExt_one {p v : Euc n} (htgt : constPairL (p, v) ∈ M.psiHomeo.target) :
    M.γExt p v 1 = M.exp p v :=
  (M.geod_eq_ext htgt ⟨1, right_mem_Icc.mpr zero_le_one⟩).1.symm

lemma γExt_hasDerivAt {p v : Euc n} (htgt : constPairL (p, v) ∈ M.psiHomeo.target)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (M.γExt p v) (M.ξExt p v t) t := by
  have h := (hasDerivAt_const t p).add (intFun_hasDerivAt (proj2L (M.geod p v)) t)
  have hval : (0 : Euc n) + proj2L (M.geod p v) (proj01 t) = M.ξExt p v t := by
    rw [zero_add]
    have hproj : proj01 t = ⟨t, ht⟩ := Set.projIcc_of_mem zero_le_one ht
    rw [hproj]
    exact (M.geod_eq_ext htgt ⟨t, ht⟩).2
  exact hval ▸ h

lemma ξExt_hasDerivAt {p v : Euc n} (htgt : constPairL (p, v) ∈ M.psiHomeo.target)
    (hU : M.geod p v ∈ M.U_V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (M.ξExt p v) (-M.ΓVec (M.γExt p v t) (M.ξExt p v t) (M.ξExt p v t)) t := by
  have h := (hasDerivAt_const t v).sub (intFun_hasDerivAt (M.quadOp (M.geod p v)) t)
  have hval : (0 : Euc n) - M.quadOp (M.geod p v) (proj01 t) =
      -M.ΓVec (M.γExt p v t) (M.ξExt p v t) (M.ξExt p v t) := by
    rw [zero_sub]
    have hproj : proj01 t = ⟨t, ht⟩ := Set.projIcc_of_mem zero_le_one ht
    rw [hproj, M.quadOp_apply hU ⟨t, ht⟩]
    have he := M.geod_eq_ext htgt ⟨t, ht⟩
    simp only [quadF, he.1, he.2]
  exact hval ▸ h

lemma geod_const_speed {p v : Euc n} (htgt : constPairL (p, v) ∈ M.psiHomeo.target)
    (hU : M.geod p v ∈ M.U_V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    M.inner (M.γExt p v t) (M.ξExt p v t) (M.ξExt p v t) = M.inner p v v := by
  let f : ℝ → ℝ := fun s => M.inner (M.γExt p v s) (M.ξExt p v s) (M.ξExt p v s)
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t, HasDerivAt f 0 s := by
    intro s hs
    have hs01 : s ∈ Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le ht.1] at hs; exact ⟨hs.1, hs.2.trans ht.2⟩
    have hγm : M.γExt p v s ∈ ball M.a₀ M.r₁ := by
      rw [← (M.geod_eq_ext htgt ⟨s, hs01⟩).1]; exact hU ⟨s, hs01⟩
    have h1 := M.hasDerivAt_inner hγm (M.γExt_hasDerivAt htgt hs01)
      (M.ξExt_hasDerivAt htgt hU hs01) (M.ξExt_hasDerivAt htgt hU hs01)
    have h0 : M.inner (M.γExt p v s)
        (-M.ΓVec (M.γExt p v s) (M.ξExt p v s) (M.ξExt p v s) +
          M.ΓVec (M.γExt p v s) (M.ξExt p v s) (M.ξExt p v s)) (M.ξExt p v s) +
        M.inner (M.γExt p v s) (M.ξExt p v s)
        (-M.ΓVec (M.γExt p v s) (M.ξExt p v s) (M.ξExt p v s) +
          M.ΓVec (M.γExt p v s) (M.ξExt p v s) (M.ξExt p v s)) = 0 := by
      rw [neg_add_cancel, M.inner_zero_left, M.inner_zero_right, add_zero]
    exact h0 ▸ h1
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at hint
  have hf0 : f 0 = M.inner p v v := by simp only [f, M.γExt_zero, M.ξExt_zero]
  linarith

lemma geod_homog {p v : Euc n} (htgt : constPairL (p, v) ∈ M.psiHomeo.target)
    (hU : M.geod p v ∈ M.U_V) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hsrc : scalePath (M.geod p v) s hs ∈ M.psiHomeo.source) :
    M.exp p (s • v) = M.γExt p v s := by
  let z_s : PathPair n := scalePath (M.geod p v) s hs
  have hz_U : z_s ∈ M.U_V := fun t =>
    hU ⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩
  have hpsi_zs : M.psi z_s = constPairL (p, s • v) := by
    apply BoundedContinuousFunction.ext
    intro t
    have hst : s * t.1 ∈ Icc (0 : ℝ) 1 := ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩
    let st : I01 := ⟨s * t.1, hst⟩
    have hgeod_st := M.geod_eq_ext htgt st
    rcases hs.1.eq_or_lt with rfl | hs_pos
    · apply Prod.ext
      · change (M.geod p v ⟨0 * t.1, _⟩).1 - intFun (proj2L z_s) t.1 = p
        have h0 : intFun (proj2L z_s) t.1 = 0 := by simp [intFun, proj2L, z_s, scalePath]
        have hst0 : (⟨0 * t.1, hst⟩ : I01) = ⟨0, left_mem_Icc.mpr zero_le_one⟩ := by ext; simp
        rw [h0, sub_zero, hst0, (M.geod_eq_ext htgt _).1, M.γExt_zero]
      · change (0 : ℝ) • (M.geod p v ⟨0 * t.1, _⟩).2 + intFun (M.quadOp z_s) t.1 = (0 : ℝ) • v
        have hq0 : ∀ u : I01, M.quadOp z_s u = 0 := fun u => by
          rw [M.quadOp_apply hz_U u]
          change M.ΓVec (z_s u).1 ((0 : ℝ) • _) ((0 : ℝ) • _) = 0
          rw [M.ΓVec_smul]; simp
        simp [intFun, hq0]
    · apply Prod.ext
      · change (M.geod p v st).1 - intFun (proj2L z_s) t.1 = p
        have hint1 : intFun (proj2L z_s) t.1 = intFun (proj2L (M.geod p v)) (s * t.1) := by
          simp only [intFun]
          have hcongr : ∫ u in (0 : ℝ)..t.1, (proj2L z_s) (proj01 u) =
              ∫ u in (0 : ℝ)..t.1, s • (proj2L (M.geod p v)) (proj01 (s * u)) := by
            refine intervalIntegral.integral_congr fun u hu => ?_
            have hu01 : u ∈ Icc (0 : ℝ) 1 := by
              rw [Set.uIcc_of_le t.2.1] at hu; exact ⟨hu.1, hu.2.trans t.2.2⟩
            have hsu : s * u ∈ Icc (0 : ℝ) 1 := ⟨mul_nonneg hs.1 hu01.1, mul_le_one₀ hs.2 hu01.1 hu01.2⟩
            have hpsu : proj01 (s * u) = ⟨s * (proj01 u).1,
                ⟨mul_nonneg hs.1 (proj01 u).2.1, mul_le_one₀ hs.2 (proj01 u).2.1 (proj01 u).2.2⟩⟩ := by
              apply Subtype.ext
              simp only [proj01, Set.projIcc_of_mem zero_le_one hsu, Set.projIcc_of_mem zero_le_one hu01]
            change s • (M.geod p v _).2 = s • (M.geod p v (proj01 (s * u))).2
            rw [hpsu]
          rw [hcongr, intervalIntegral.integral_smul,
            intervalIntegral.integral_comp_mul_left (fun y => proj2L (M.geod p v) (proj01 y)) hs_pos.ne']
          rw [mul_zero, smul_smul, mul_inv_cancel₀ hs_pos.ne', one_smul]
        rw [hint1, hgeod_st.1, γExt]; abel
      · change s • (M.geod p v st).2 + intFun (M.quadOp z_s) t.1 = s • v
        have hint2 : intFun (M.quadOp z_s) t.1 = s • intFun (M.quadOp (M.geod p v)) (s * t.1) := by
          simp only [intFun]
          have hcongr : ∫ u in (0 : ℝ)..t.1, M.quadOp z_s (proj01 u) =
              ∫ u in (0 : ℝ)..t.1, (s * s) • M.quadOp (M.geod p v) (proj01 (s * u)) := by
            refine intervalIntegral.integral_congr fun u hu => ?_
            have hu01 : u ∈ Icc (0 : ℝ) 1 := by
              rw [Set.uIcc_of_le t.2.1] at hu; exact ⟨hu.1, hu.2.trans t.2.2⟩
            have hsu : s * u ∈ Icc (0 : ℝ) 1 := ⟨mul_nonneg hs.1 hu01.1, mul_le_one₀ hs.2 hu01.1 hu01.2⟩
            have hpsu : proj01 (s * u) = ⟨s * (proj01 u).1,
                ⟨mul_nonneg hs.1 (proj01 u).2.1, mul_le_one₀ hs.2 (proj01 u).2.1 (proj01 u).2.2⟩⟩ := by
              apply Subtype.ext
              simp only [proj01, Set.projIcc_of_mem zero_le_one hsu, Set.projIcc_of_mem zero_le_one hu01]
            rw [M.quadOp_apply hz_U, M.quadOp_apply hU, hpsu]
            change M.ΓVec _ (s • _) (s • _) = (s * s) • M.ΓVec _ _ _
            exact M.ΓVec_smul _ s _ _
          rw [hcongr, intervalIntegral.integral_smul,
            intervalIntegral.integral_comp_mul_left (fun y => M.quadOp (M.geod p v) (proj01 y)) hs_pos.ne']
          rw [mul_zero, smul_smul, show (s * s) * s⁻¹ = s by field_simp [hs_pos.ne']]
        rw [hint2, hgeod_st.2, ξExt, smul_sub]; abel
  have hleft : M.psiHomeo.symm (M.psiHomeo z_s) = z_s := M.psiHomeo.left_inv hsrc
  have hgeod_eq : M.geod p (s • v) = z_s := by
    change M.psiHomeo.symm (constPairL (p, s • v)) = z_s
    rw [← hpsi_zs]; exact hleft
  have h1 := congrArg (fun z : PathPair n => (z ⟨1, right_mem_Icc.mpr zero_le_one⟩).1) hgeod_eq
  change M.exp p (s • v) = (M.geod p v ⟨s * 1, _⟩).1 at h1
  rw [h1, (M.geod_eq_ext htgt _).1]
  change M.γExt p v (s * 1) = M.γExt p v s
  rw [mul_one]

/-- Geodesic reversal: reversing `geod p v` yields `geod (exp p v) (-ξExt p v 1)`. -/
lemma geod_reverse {p v : Euc n} (htgt : constPairL (p, v) ∈ M.psiHomeo.target)
    (hU : M.geod p v ∈ M.U_V) (hrev_src : revPath (M.geod p v) ∈ M.psiHomeo.source) :
    let q := M.exp p v
    let w := M.ξExt p v 1
    M.geod q (-w) = revPath (M.geod p v) ∧
    M.exp q (-w) = p ∧
    M.ξExt q (-w) 1 = -v := by
  intro q w
  let z_r : PathPair n := revPath (M.geod p v)
  have hzr_U : z_r ∈ M.U_V := fun t =>
    hU ⟨1 - t.1, ⟨sub_nonneg.mpr t.2.2, sub_le_self 1 t.2.1⟩⟩
  have hpsi_zr : M.psi z_r = constPairL (q, -w) := by
    apply BoundedContinuousFunction.ext
    intro t
    let rt : I01 := ⟨1 - t.1, ⟨sub_nonneg.mpr t.2.2, sub_le_self 1 t.2.1⟩⟩
    have hgeod_rt := M.geod_eq_ext htgt rt
    have hgeod_1 := M.geod_eq_ext htgt ⟨1, right_mem_Icc.mpr zero_le_one⟩
    have hc1 : Continuous (fun s : ℝ => (proj2L (M.geod p v)) (proj01 s)) :=
      (proj2L (M.geod p v)).continuous.comp continuous_proj01
    have hc2 : Continuous (fun s : ℝ => M.quadOp (M.geod p v) (proj01 s)) :=
      (M.quadOp (M.geod p v)).continuous.comp continuous_proj01
    apply Prod.ext
    · change (M.geod p v rt).1 - intFun (proj2L z_r) t.1 = q
      have hint1 : intFun (proj2L z_r) t.1 =
          -(intFun (proj2L (M.geod p v)) 1 - intFun (proj2L (M.geod p v)) (1 - t.1)) := by
        simp only [intFun]
        have hcongr : ∫ u in (0 : ℝ)..t.1, (proj2L z_r) (proj01 u) =
            ∫ u in (0 : ℝ)..t.1, -((proj2L (M.geod p v)) (proj01 (1 - u))) := by
          refine intervalIntegral.integral_congr fun u hu => ?_
          have hu01 : u ∈ Icc (0 : ℝ) 1 := by
            rw [Set.uIcc_of_le t.2.1] at hu; exact ⟨hu.1, hu.2.trans t.2.2⟩
          have h1u : 1 - u ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr hu01.2, sub_le_self 1 hu01.1⟩
          have hpu : proj01 (1 - u) = ⟨1 - (proj01 u).1,
              ⟨sub_nonneg.mpr (proj01 u).2.2, sub_le_self 1 (proj01 u).2.1⟩⟩ := by
            apply Subtype.ext
            simp only [proj01, Set.projIcc_of_mem zero_le_one h1u, Set.projIcc_of_mem zero_le_one hu01]
          change -(M.geod p v _).2 = -(M.geod p v (proj01 (1 - u))).2
          rw [hpu]
        rw [hcongr, intervalIntegral.integral_neg,
          intervalIntegral.integral_comp_sub_left (fun y => proj2L (M.geod p v) (proj01 y)) (1 : ℝ)]
        rw [sub_zero]
        congr 1
        have hadd := intervalIntegral.integral_add_adjacent_intervals
          (hc1.intervalIntegrable (μ := MeasureTheory.volume) 0 (1 - t.1))
          (hc1.intervalIntegrable (μ := MeasureTheory.volume) (1 - t.1) 1)
        rw [← hadd]; abel
      rw [hint1, hgeod_rt.1, show q = M.γExt p v 1 from (M.γExt_one htgt).symm]
      simp only [γExt]; abel
    · change -(M.geod p v rt).2 + intFun (M.quadOp z_r) t.1 = -w
      have hint2 : intFun (M.quadOp z_r) t.1 =
          intFun (M.quadOp (M.geod p v)) 1 - intFun (M.quadOp (M.geod p v)) (1 - t.1) := by
        simp only [intFun]
        have hcongr : ∫ u in (0 : ℝ)..t.1, M.quadOp z_r (proj01 u) =
            ∫ u in (0 : ℝ)..t.1, M.quadOp (M.geod p v) (proj01 (1 - u)) := by
          refine intervalIntegral.integral_congr fun u hu => ?_
          have hu01 : u ∈ Icc (0 : ℝ) 1 := by
            rw [Set.uIcc_of_le t.2.1] at hu; exact ⟨hu.1, hu.2.trans t.2.2⟩
          have h1u : 1 - u ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr hu01.2, sub_le_self 1 hu01.1⟩
          have hpu : proj01 (1 - u) = ⟨1 - (proj01 u).1,
              ⟨sub_nonneg.mpr (proj01 u).2.2, sub_le_self 1 (proj01 u).2.1⟩⟩ := by
            apply Subtype.ext
            simp only [proj01, Set.projIcc_of_mem zero_le_one h1u, Set.projIcc_of_mem zero_le_one hu01]
          rw [M.quadOp_apply hzr_U, M.quadOp_apply hU, hpu]
          change M.ΓVec _ (-(M.geod p v _).2) (-(M.geod p v _).2) = M.ΓVec _ _ _
          exact M.ΓVec_neg _ _ _
        rw [hcongr,
          intervalIntegral.integral_comp_sub_left (fun y => M.quadOp (M.geod p v) (proj01 y)) (1 : ℝ)]
        rw [sub_zero]
        have hadd := intervalIntegral.integral_add_adjacent_intervals
          (hc2.intervalIntegrable (μ := MeasureTheory.volume) 0 (1 - t.1))
          (hc2.intervalIntegrable (μ := MeasureTheory.volume) (1 - t.1) 1)
        rw [← hadd]; abel
      rw [hint2, hgeod_rt.2]
      simp only [w, ξExt]; abel
  have hgeod_eq : M.geod q (-w) = z_r := by
    change M.psiHomeo.symm (constPairL (q, -w)) = z_r
    rw [← hpsi_zr]
    exact M.psiHomeo.left_inv hrev_src
  have htgt_q : constPairL (q, -w) ∈ M.psiHomeo.target := by
    rw [← hpsi_zr]; exact M.psiHomeo.map_source hrev_src
  have hexp_q : M.exp q (-w) = p := by
    have h1 := congrArg (fun z : PathPair n => (z ⟨1, right_mem_Icc.mpr zero_le_one⟩).1) hgeod_eq
    have h0 : (⟨1 - (1 : ℝ), ⟨sub_nonneg.mpr le_rfl, sub_le_self 1 zero_le_one⟩⟩ : I01) =
        ⟨0, left_mem_Icc.mpr zero_le_one⟩ := by ext; simp
    change M.exp q (-w) = (M.geod p v ⟨1 - (1 : ℝ), ⟨sub_nonneg.mpr le_rfl, sub_le_self 1 zero_le_one⟩⟩).1 at h1
    rw [h1, h0, (M.geod_eq_ext htgt _).1, M.γExt_zero]
  have hξ_q : M.ξExt q (-w) 1 = -v := by
    have h1 := congrArg (fun z : PathPair n => (z ⟨1, right_mem_Icc.mpr zero_le_one⟩).2) hgeod_eq
    rw [(M.geod_eq_ext htgt_q ⟨1, right_mem_Icc.mpr zero_le_one⟩).2] at h1
    have h0 : (⟨1 - (1 : ℝ), ⟨sub_nonneg.mpr le_rfl, sub_le_self 1 zero_le_one⟩⟩ : I01) =
        ⟨0, left_mem_Icc.mpr zero_le_one⟩ := by ext; simp
    change M.ξExt q (-w) 1 = -(M.geod p v ⟨1 - (1 : ℝ), ⟨sub_nonneg.mpr le_rfl, sub_le_self 1 zero_le_one⟩⟩).2 at h1
    rw [h1, h0, (M.geod_eq_ext htgt _).2, M.ξExt_zero]
  exact ⟨hgeod_eq, hexp_q, hξ_q⟩

lemma gauss_lemma {r_g : ℝ}
    (hrg : ∀ p ∈ ball M.a₀ r_g, ∀ v ∈ ball (0 : Euc n) r_g,
      constPairL (p, v) ∈ M.psiHomeo.target ∧
      M.geod p v ∈ M.U_V ∧
      (∃ L : PathPair n ≃L[ℝ] PathPair n,
        (L : PathPair n →L[ℝ] PathPair n) = M.dpsi (M.geod p v) ∧
        HasStrictFDerivAt M.psiHomeo.symm (L.symm : PathPair n →L[ℝ] PathPair n) (constPairL (p, v))) ∧
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1), scalePath (M.geod p v) s hs ∈ M.psiHomeo.source) ∧
      revPath (M.geod p v) ∈ M.psiHomeo.source)
    {p v : Euc n} (hp : p ∈ ball M.a₀ r_g) (hv : v ∈ ball (0 : Euc n) r_g) (w : Euc n) :
    HasStrictFDerivAt (M.exp p) (fderiv ℝ (M.exp p) v) v ∧
    fderiv ℝ (M.exp p) v v = M.ξExt p v 1 ∧
    M.inner (M.exp p v) (fderiv ℝ (M.exp p) v v) (fderiv ℝ (M.exp p) v w) = M.inner p v w := by
  obtain ⟨htgt, hU, ⟨L, _, hL⟩, hhom, _⟩ := hrg p hp v hv
  let inR : Euc n →L[ℝ] PathPair n := constPairL.comp (ContinuousLinearMap.inr ℝ (Euc n) (Euc n))
  have hgeod_fd : HasStrictFDerivAt (fun u => M.geod p u) ((L.symm : PathPair n →L[ℝ] PathPair n).comp inR) v := by
    have haff : HasStrictFDerivAt (fun u : Euc n => constPairL (p, u)) inR v := by
      have heq : (fun u : Euc n => constPairL (p, u)) = fun u => constPairL (p, 0) + inR u := by
        funext u; apply BoundedContinuousFunction.ext; intro t; simp [inR, constPairL]
      rw [heq]
      have hsum := (hasStrictFDerivAt_const (constPairL (p, 0)) v).add inR.hasStrictFDerivAt
      rwa [zero_add] at hsum
    exact hL.comp v haff
  let Dgeod : Euc n →L[ℝ] PathPair n := (L.symm : PathPair n →L[ℝ] PathPair n).comp inR
  let eval1Fst : PathPair n →L[ℝ] Euc n :=
    (ContinuousLinearMap.fst ℝ (Euc n) (Euc n)).comp (evalAtL ⟨1, right_mem_Icc.mpr zero_le_one⟩)
  have hexp_fd : HasStrictFDerivAt (M.exp p) (eval1Fst.comp Dgeod) v :=
    eval1Fst.hasStrictFDerivAt.comp v hgeod_fd
  have hDexp_eq : fderiv ℝ (M.exp p) v = eval1Fst.comp Dgeod := hexp_fd.hasFDerivAt.fderiv
  have hexp_sfd : HasStrictFDerivAt (M.exp p) (fderiv ℝ (M.exp p) v) v := hDexp_eq ▸ hexp_fd
  have hrad : fderiv ℝ (M.exp p) v v = M.ξExt p v 1 := by
    have h1 : HasDerivWithinAt (fun s : ℝ => M.exp p (s • v)) (fderiv ℝ (M.exp p) v v) (Icc 0 1) 1 := by
      have hsmul : HasDerivAt (fun s : ℝ => s • v) v 1 := by
        have h := (hasDerivAt_id (1 : ℝ)).smul_const v; rwa [one_smul] at h
      have hf1 : HasFDerivAt (M.exp p) (fderiv ℝ (M.exp p) v) ((1 : ℝ) • v) := by
        rw [one_smul]; exact hexp_sfd.hasFDerivAt
      exact (hf1.comp_hasDerivAt 1 hsmul).hasDerivWithinAt
    have h2 : HasDerivWithinAt (M.γExt p v) (M.ξExt p v 1) (Icc 0 1) 1 :=
      (M.γExt_hasDerivAt htgt (right_mem_Icc.mpr zero_le_one)).hasDerivWithinAt
    have h2' : HasDerivWithinAt (fun s : ℝ => M.exp p (s • v)) (M.ξExt p v 1) (Icc 0 1) 1 :=
      h2.congr (fun s hs => M.geod_homog htgt hU hs (hhom s hs))
        (M.geod_homog htgt hU (right_mem_Icc.mpr zero_le_one) (hhom 1 (right_mem_Icc.mpr zero_le_one)))
    exact (uniqueDiffOn_Icc zero_lt_one 1 (right_mem_Icc.mpr zero_le_one)).eq_deriv _ h1 h2'
  refine ⟨hexp_sfd, hrad, ?_⟩
  rw [hrad]
  let Jpair : PathPair n := Dgeod w
  let Jext (t : ℝ) : Euc n := intFun (proj2L Jpair) t
  let J'ext (t : ℝ) : Euc n := (Jpair (proj01 t)).2
  have hJ_int : ∀ t : I01, (Jpair t).1 = Jext t.1 := by
    intro t
    have hEv : (fun u => proj1L (M.geod p u) - intOp (proj2L (M.geod p u))) =ᶠ[𝓝 v]
        (fun _ => BoundedContinuousFunction.const I01 p) := by
      filter_upwards [isOpen_ball.mem_nhds hv] with u hu
      have hu_tgt := (hrg p hp u hu).1
      apply BoundedContinuousFunction.ext
      intro s
      have he := (M.geod_eq_ext hu_tgt s).1
      change (M.geod p u s).1 - intFun (proj2L (M.geod p u)) s.1 = p
      rw [he, γExt]; abel
    have hd1 : HasFDerivAt (fun u => proj1L (M.geod p u) - intOp (proj2L (M.geod p u)))
        ((proj1L - intOp.comp proj2L).comp Dgeod) v :=
      (proj1L - intOp.comp proj2L).hasFDerivAt.comp v hgeod_fd.hasFDerivAt
    have hd2 : HasFDerivAt (fun u => proj1L (M.geod p u) - intOp (proj2L (M.geod p u)))
        (0 : Euc n →L[ℝ] PathOne n) v :=
      (hasFDerivAt_const _ v).congr_of_eventuallyEq hEv
    have h0 := congrArg (fun L : Euc n →L[ℝ] PathOne n => L w t) (hd1.unique hd2)
    change (Jpair t).1 - intFun (proj2L Jpair) t.1 = 0 at h0
    exact sub_eq_zero.mp h0
  have hJext_hasDerivAt : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt Jext (J'ext t) t := fun t _ =>
    intFun_hasDerivAt (proj2L Jpair) t
  have hkey : ∀ t ∈ Icc (0 : ℝ) 1,
      M.inner (M.γExt p v t) (M.ξExt p v t) (J'ext t + M.ΓVec (M.γExt p v t) (M.ξExt p v t) (Jext t)) =
        M.inner p v w := by
    intro t ht
    let tI : I01 := ⟨t, ht⟩
    have hline : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
      have h := (hasDerivAt_const (0 : ℝ) v).add ((hasDerivAt_id (0 : ℝ)).smul_const w)
      rwa [one_smul, zero_add] at h
    have hcurve : HasDerivAt (fun s : ℝ => M.geod p (v + s • w)) Jpair 0 := by
      have hgv : HasFDerivAt (fun u => M.geod p u) Dgeod (v + (0 : ℝ) • w) := by
        rw [zero_smul, add_zero]; exact hgeod_fd.hasFDerivAt
      exact hgv.comp_hasDerivAt 0 hline
    let γs : ℝ → Euc n := fun s => (M.geod p (v + s • w) tI).1
    let ξs : ℝ → Euc n := fun s => (M.geod p (v + s • w) tI).2
    have hγs : HasDerivAt γs (Jext t) 0 := by
      have h := ((ContinuousLinearMap.fst ℝ (Euc n) (Euc n)).comp (evalAtL tI)).hasFDerivAt.comp_hasDerivAt 0 hcurve
      exact (hJ_int tI) ▸ h
    have hξs : HasDerivAt ξs (J'ext t) 0 := by
      have h := ((ContinuousLinearMap.snd ℝ (Euc n) (Euc n)).comp (evalAtL tI)).hasFDerivAt.comp_hasDerivAt 0 hcurve
      have hpt : proj01 t = tI := Set.projIcc_of_mem zero_le_one ht
      have hjeq : (Jpair tI).2 = J'ext t := by simp only [J'ext, hpt]
      exact hjeq ▸ h
    have hγ0 : γs 0 ∈ ball M.a₀ M.r₁ := by
      change (M.geod p (v + (0 : ℝ) • w) tI).1 ∈ ball M.a₀ M.r₁
      rw [zero_smul, add_zero]; exact hU tI
    have hd_lhs := M.hasDerivAt_inner (γ := γs) (u := ξs) (v := ξs) hγ0 hγs hξs hξs
    have hev : (fun s : ℝ => M.inner (γs s) (ξs s) (ξs s)) =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ => M.inner p (v + s • w) (v + s • w)) := by
      have h0mem : (fun s : ℝ => v + s • w) ⁻¹' ball (0 : Euc n) r_g ∈ 𝓝 (0 : ℝ) :=
        hline.continuousAt.preimage_mem_nhds (by rw [zero_smul, add_zero]; exact isOpen_ball.mem_nhds hv)
      filter_upwards [h0mem] with s hs_ball
      have hstgt := (hrg p hp (v + s • w) hs_ball).1
      have hsU := (hrg p hp (v + s • w) hs_ball).2.1
      have he := M.geod_eq_ext hstgt tI
      change M.inner (M.geod p (v + s • w) tI).1 (M.geod p (v + s • w) tI).2 (M.geod p (v + s • w) tI).2 = _
      rw [he.1, he.2]
      exact M.geod_const_speed hstgt hsU ht
    have hd_rhs : HasDerivAt (fun s : ℝ => M.inner p (v + s • w) (v + s • w)) (2 * M.inner p v w) 0 := by
      have hpm : p ∈ ball M.a₀ M.r₁ := by
        have h0 := hU ⟨0, left_mem_Icc.mpr zero_le_one⟩
        rwa [(M.geod_eq_ext htgt ⟨0, left_mem_Icc.mpr zero_le_one⟩).1, M.γExt_zero] at h0
      have hpoly : (fun s : ℝ => M.inner p (v + s • w) (v + s • w)) =
          fun s => M.inner p v v + s * (2 * M.inner p v w) + s ^ 2 * M.inner p w w := by
        ext s
        rw [M.inner_add_left, M.inner_add_right, M.inner_add_right, M.inner_smul_left,
          M.inner_smul_right, M.inner_smul_left, M.inner_smul_right, M.inner_symm hpm w v]
        ring
      rw [hpoly]
      have h1 := ((hasDerivAt_const (0 : ℝ) (M.inner p v v)).add
        ((hasDerivAt_id (0 : ℝ)).mul_const (2 * M.inner p v w))).add
        (((hasDerivAt_pow 2 (0 : ℝ))).mul_const (M.inner p w w))
      exact h1.congr_deriv (by norm_num)
    have heq := (hd_lhs.congr_of_eventuallyEq hev.symm).unique hd_rhs
    have he0 := M.geod_eq_ext htgt tI
    simp only [γs, ξs, zero_smul, add_zero, he0.1, he0.2] at heq
    have hγm : M.γExt p v t ∈ ball M.a₀ M.r₁ := by rw [← he0.1]; exact hU tI
    rw [M.inner_symm hγm (J'ext t + M.ΓVec (M.γExt p v t) (Jext t) (M.ξExt p v t)) (M.ξExt p v t),
      M.ΓVec_symm hγm (Jext t) (M.ξExt p v t)] at heq
    linarith
  let hfun : ℝ → ℝ := fun t => M.inner (M.γExt p v t) (M.ξExt p v t) (Jext t) - t * M.inner p v w
  have hfun_deriv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt hfun 0 t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hγm : M.γExt p v t ∈ ball M.a₀ M.r₁ := by
      rw [← (M.geod_eq_ext htgt ⟨t, ht⟩).1]; exact hU ⟨t, ht⟩
    have h1 := M.hasDerivAt_inner hγm (M.γExt_hasDerivAt htgt ht)
      (M.ξExt_hasDerivAt htgt hU ht) (hJext_hasDerivAt t ht)
    have h2 := h1.sub ((hasDerivAt_id t).mul_const (M.inner p v w))
    have h0 : M.inner (M.γExt p v t)
        (-M.ΓVec (M.γExt p v t) (M.ξExt p v t) (M.ξExt p v t) +
          M.ΓVec (M.γExt p v t) (M.ξExt p v t) (M.ξExt p v t)) (Jext t) +
        M.inner (M.γExt p v t) (M.ξExt p v t)
          (J'ext t + M.ΓVec (M.γExt p v t) (M.ξExt p v t) (Jext t)) -
        1 * M.inner p v w = 0 := by
      rw [neg_add_cancel, M.inner_zero_left, zero_add, one_mul, hkey t ht, sub_self]
    exact h0 ▸ h2
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hfun_deriv intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at hint
  have hh0 : hfun 0 = 0 := by simp [hfun, Jext, intFun, M.inner_zero_right]
  have hh1 : hfun 1 = M.inner (M.exp p v) (M.ξExt p v 1) (fderiv ℝ (M.exp p) v w) - M.inner p v w := by
    simp only [hfun, one_mul, M.γExt_one htgt]
    congr 2
    rw [← hJ_int ⟨1, right_mem_Icc.mpr zero_le_one⟩, hDexp_eq]
    rfl
  linarith

/- ### Part 2C: Joint Exponential Diffeomorphism `E(p, v) = (p, exp p v)` and `log p q` -/

def EMap (x : Euc n × Euc n) : Euc n × Euc n := (x.1, M.exp x.1 x.2)

def eEquiv : (Euc n × Euc n) ≃L[ℝ] (Euc n × Euc n) :=
  { toLinearEquiv :=
      { toFun := fun x => (x.1, x.1 + x.2)
        invFun := fun x => (x.1, x.2 - x.1)
        map_add' := fun x y => by ext <;> simp [add_comm, add_left_comm]
        map_smul' := fun c x => by ext <;> simp [smul_add]
        left_inv := fun x => by ext <;> simp
        right_inv := fun x => by ext <;> simp }
    continuous_toFun := continuous_fst.prodMk (continuous_fst.add continuous_snd)
    continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_fst) }

lemma EMap_hasStrictFDerivAt_zero :
    HasStrictFDerivAt M.EMap (eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) (M.a₀, 0) := by
  have hz₀_src : M.z₀ ∈ M.psiHomeo.source := M.psi_hasStrictFDerivAt_z₀.mem_toOpenPartialHomeomorph_source
  have hz₀_tgt : M.z₀ ∈ M.psiHomeo.target := by
    rw [← M.psi_z₀]; exact M.psi_hasStrictFDerivAt_z₀.image_mem_toOpenPartialHomeomorph_target
  have hsymm_z₀ : M.psiHomeo.symm M.z₀ = M.z₀ := by
    have h1 := M.psiHomeo.left_inv hz₀_src
    have h2 : M.psiHomeo M.z₀ = M.z₀ := M.psi_z₀
    rwa [h2] at h1
  have hpsi_at : HasStrictFDerivAt M.psi (dpsi0Equiv (n := n) : PathPair n →L[ℝ] PathPair n) (M.psiHomeo.symm M.z₀) := by
    rw [hsymm_z₀]; exact M.psi_hasStrictFDerivAt_z₀
  have hsymm_fd : HasStrictFDerivAt M.psiHomeo.symm (dpsi0Equiv (n := n).symm : PathPair n →L[ℝ] PathPair n) M.z₀ :=
    M.psiHomeo.hasStrictFDerivAt_symm hz₀_tgt hpsi_at
  have hgeod_fd : HasStrictFDerivAt (fun x : Euc n × Euc n => M.geod x.1 x.2)
      ((dpsi0Equiv (n := n).symm : PathPair n →L[ℝ] PathPair n).comp constPairL) (M.a₀, 0) :=
    hsymm_fd.comp (M.a₀, 0) constPairL.hasStrictFDerivAt
  let eval1Fst : PathPair n →L[ℝ] Euc n :=
    (ContinuousLinearMap.fst ℝ (Euc n) (Euc n)).comp (evalAtL ⟨1, right_mem_Icc.mpr zero_le_one⟩)
  have hexp_fd : HasStrictFDerivAt (fun x : Euc n × Euc n => M.exp x.1 x.2)
      (eval1Fst.comp ((dpsi0Equiv (n := n).symm : PathPair n →L[ℝ] PathPair n).comp constPairL)) (M.a₀, 0) :=
    eval1Fst.hasStrictFDerivAt.comp (M.a₀, 0) hgeod_fd
  have hE_fd := (ContinuousLinearMap.fst ℝ (Euc n) (Euc n)).hasStrictFDerivAt.prodMk hexp_fd
  have hL_eq : (ContinuousLinearMap.fst ℝ (Euc n) (Euc n)).prod
      (eval1Fst.comp ((dpsi0Equiv (n := n).symm : PathPair n →L[ℝ] PathPair n).comp constPairL)) =
      (eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) := by
    refine ContinuousLinearMap.ext fun x => Prod.ext rfl ?_
    change x.1 + intFun (proj2L (constPairL x)) 1 = x.1 + x.2
    have hint : intFun (proj2L (constPairL x)) 1 = x.2 := by
      simp [intFun, proj2L, constPairL]
    rw [hint]
  rw [hL_eq] at hE_fd
  exact hE_fd

def EHomeo : OpenPartialHomeomorph (Euc n × Euc n) (Euc n × Euc n) :=
  M.EMap_hasStrictFDerivAt_zero.toOpenPartialHomeomorph M.EMap

def log (p q : Euc n) : Euc n := (M.EHomeo.symm (p, q)).2

lemma EMap_zero : M.EMap (M.a₀, 0) = (M.a₀, M.a₀) := by
  have hz₀_src : M.z₀ ∈ M.psiHomeo.source := M.psi_hasStrictFDerivAt_z₀.mem_toOpenPartialHomeomorph_source
  have hgeod0 : M.geod M.a₀ 0 = M.z₀ := by
    change M.psiHomeo.symm M.z₀ = M.z₀
    have h1 := M.psiHomeo.left_inv hz₀_src
    have h2 : M.psiHomeo M.z₀ = M.z₀ := M.psi_z₀
    rwa [h2] at h1
  refine Prod.ext rfl ?_
  change (M.geod M.a₀ 0 ⟨1, right_mem_Icc.mpr zero_le_one⟩).1 = M.a₀
  rw [hgeod0]; rfl

lemma EHomeo_symm_hasStrictFDerivAt_diag :
    HasStrictFDerivAt M.EHomeo.symm (eEquiv (n := n).symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) (M.a₀, M.a₀) := by
  have htgt : (M.a₀, M.a₀) ∈ M.EHomeo.target := by
    rw [← M.EMap_zero]; exact M.EMap_hasStrictFDerivAt_zero.image_mem_toOpenPartialHomeomorph_target
  have hsymm0 : M.EHomeo.symm (M.a₀, M.a₀) = (M.a₀, 0) := by
    have hsrc : (M.a₀, (0 : Euc n)) ∈ M.EHomeo.source :=
      M.EMap_hasStrictFDerivAt_zero.mem_toOpenPartialHomeomorph_source
    have h1 := M.EHomeo.left_inv hsrc
    have h2 : M.EHomeo (M.a₀, 0) = (M.a₀, M.a₀) := M.EMap_zero
    rwa [h2] at h1
  have hfd : HasStrictFDerivAt M.EMap (eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n))
      (M.EHomeo.symm (M.a₀, M.a₀)) := by
    rw [hsymm0]; exact M.EMap_hasStrictFDerivAt_zero
  exact M.EHomeo.hasStrictFDerivAt_symm htgt hfd

lemma log_hasStrictFDerivAt_diag :
    HasStrictFDerivAt (fun x : Euc n × Euc n => M.log x.1 x.2)
      (ContinuousLinearMap.snd ℝ (Euc n) (Euc n) - ContinuousLinearMap.fst ℝ (Euc n) (Euc n))
      (M.a₀, M.a₀) := by
  have h := (ContinuousLinearMap.snd ℝ (Euc n) (Euc n)).hasStrictFDerivAt.comp (M.a₀, M.a₀)
    M.EHomeo_symm_hasStrictFDerivAt_diag
  have hL : (ContinuousLinearMap.snd ℝ (Euc n) (Euc n)).comp (eEquiv (n := n).symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) =
      ContinuousLinearMap.snd ℝ (Euc n) (Euc n) - ContinuousLinearMap.fst ℝ (Euc n) (Euc n) :=
    ContinuousLinearMap.ext fun _ => rfl
  rw [hL] at h
  exact h

set_option maxHeartbeats 800000 in
/-- Uniform normal-coordinate neighborhood package around `M.a₀` (for `0 < n`). -/
lemma exists_normal_package (hn : 0 < n) :
    ∃ (r_g r_m r_e r_n ρ_0 m_g M_g L_g : ℝ),
      0 < r_g ∧ 0 < r_m ∧ 0 < r_e ∧ 0 < r_n ∧ 0 < ρ_0 ∧ 0 < m_g ∧ 0 < M_g ∧ 0 ≤ L_g ∧
      r_m < M.r₁ ∧ r_n ≤ r_e ∧ r_e ≤ r_m ∧ r_m ≤ r_g ∧
      (∀ y ∈ closedBall M.a₀ r_m, ∀ v : Euc n,
        m_g * ‖v‖ ≤ M.gnorm y v ∧ M.gnorm y v ≤ M_g * ‖v‖) ∧
      (∀ y₁ ∈ closedBall M.a₀ r_m, ∀ y₂ ∈ closedBall M.a₀ r_m, ∀ u v : Euc n,
        |M.inner y₁ u v - M.inner y₂ u v| ≤ L_g * ‖y₁ - y₂‖ * ‖u‖ * ‖v‖) ∧
      (∀ p ∈ ball M.a₀ r_g, ∀ v ∈ ball (0 : Euc n) r_g,
        constPairL (p, v) ∈ M.psiHomeo.target ∧
        M.geod p v ∈ M.U_V ∧
        (∃ L : PathPair n ≃L[ℝ] PathPair n,
          (L : PathPair n →L[ℝ] PathPair n) = M.dpsi (M.geod p v) ∧
          HasStrictFDerivAt M.psiHomeo.symm (L.symm : PathPair n →L[ℝ] PathPair n) (constPairL (p, v))) ∧
        (∀ s (hs : s ∈ Icc (0 : ℝ) 1), scalePath (M.geod p v) s hs ∈ M.psiHomeo.source) ∧
        revPath (M.geod p v) ∈ M.psiHomeo.source) ∧
      (∀ p ∈ ball M.a₀ r_e, ∀ v ∈ ball (0 : Euc n) r_e,
        (p, v) ∈ M.EHomeo.source ∧
        ∃ LE : (Euc n × Euc n) ≃L[ℝ] (Euc n × Euc n),
          HasStrictFDerivAt M.EMap (LE : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) (p, v)) ∧
      (∀ p ∈ ball M.a₀ r_n, ∀ v : Euc n, M.gnorm p v < ρ_0 →
        v ∈ ball (0 : Euc n) r_e ∧
        M.exp p v ∈ ball M.a₀ r_m ∧
        (p, M.exp p v) ∈ M.EHomeo.target ∧
        M.log p (M.exp p v) = v ∧
        (∃ LE : (Euc n × Euc n) ≃L[ℝ] (Euc n × Euc n),
          HasStrictFDerivAt M.EHomeo.symm (LE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) (p, M.exp p v)) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, M.γExt p v t ∈ ball M.a₀ r_m) ∧
      (∀ p ∈ ball M.a₀ r_n, ∀ q ∈ ball M.a₀ r_n,
        (p, q) ∈ M.EHomeo.target ∧
        M.log p q ∈ ball (0 : Euc n) r_e ∧
        M.gnorm p (M.log p q) < ρ_0 / 2 ∧
        M.exp p (M.log p q) = q ∧
        M.ξExt q (M.log q p) 1 = -M.log p q ∧
        ∃ LE : (Euc n × Euc n) ≃L[ℝ] (Euc n × Euc n),
          HasStrictFDerivAt M.EHomeo.symm (LE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) (p, q)) := by
  obtain ⟨r_g, hr_g, hrg⟩ := M.exists_geod_radius
  let r_m : ℝ := min (M.r₁ / 2) r_g
  have hr_m : 0 < r_m := lt_min (half_pos M.hr₁) hr_g
  have hrm_lt : r_m < M.r₁ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self M.hr₁)
  have hrm_rg : r_m ≤ r_g := min_le_right _ _
  obtain ⟨m_g, hm_g, M_g, hM_g, L_g, hL_g, hmbd, hmlip⟩ :=
    M.exists_metric_bounds hn hr_m hrm_lt
  have hE0_src : (M.a₀, (0 : Euc n)) ∈ M.EHomeo.source :=
    M.EMap_hasStrictFDerivAt_zero.mem_toOpenPartialHomeomorph_source
  obtain ⟨r_esrc, hr_esrc, hresrc_sub⟩ := Metric.isOpen_iff.mp M.EHomeo.open_source (M.a₀, 0) hE0_src
  let E0inv : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n) := eEquiv (n := n).symm
  let L0inv : PathPair n →L[ℝ] PathPair n := dpsi0Equiv (n := n).symm
  have hL0inv_nn : 0 ≤ ‖L0inv‖ := ContinuousLinearMap.opNorm_nonneg _
  have hE0inv_nn : 0 ≤ ‖E0inv‖ := ContinuousLinearMap.opNorm_nonneg _
  let ε_d : ℝ := min ((2 * (‖L0inv‖ + 1))⁻¹) ((4 * (‖L0inv‖ + 1) ^ 2 * (‖E0inv‖ + 1))⁻¹)
  have hε_d : 0 < ε_d := lt_min (inv_pos.mpr (by positivity)) (inv_pos.mpr (by positivity))
  obtain ⟨δ_d, hδ_d, hδ_d_spec⟩ := M.dquadOp_norm_sub_lt M.z₀_mem_U_V hε_d
  have hgeod_cont : ContinuousAt (fun x : Euc n × Euc n => M.geod x.1 x.2) (M.a₀, 0) := by
    have hz₀_tgt : constPairL (M.a₀, (0 : Euc n)) ∈ M.psiHomeo.target := by
      change M.z₀ ∈ M.psiHomeo.target
      rw [← M.psi_z₀]; exact M.psi_hasStrictFDerivAt_z₀.image_mem_toOpenPartialHomeomorph_target
    exact ContinuousAt.comp (g := M.psiHomeo.symm) (f := constPairL)
      (M.psiHomeo.continuousAt_symm hz₀_tgt) constPairL.continuous.continuousAt
  have hgeod0 : M.geod M.a₀ 0 = M.z₀ := by
    have h1 := M.psiHomeo.left_inv M.psi_hasStrictFDerivAt_z₀.mem_toOpenPartialHomeomorph_source
    have h2 : M.psiHomeo M.z₀ = M.z₀ := M.psi_z₀
    change M.psiHomeo.symm M.z₀ = M.z₀; rwa [h2] at h1
  obtain ⟨r_ed, hr_ed, hred_sub⟩ := Metric.continuousAt_iff.mp hgeod_cont δ_d hδ_d
  let r_e : ℝ := min (min r_m r_esrc) r_ed
  have hr_e : 0 < r_e := lt_min (lt_min hr_m hr_esrc) hr_ed
  have hre_rm : r_e ≤ r_m := (min_le_left _ _).trans (min_le_left _ _)
  have hre_rg : r_e ≤ r_g := hre_rm.trans hrm_rg
  have hE_inv : ∀ p ∈ ball M.a₀ r_e, ∀ v ∈ ball (0 : Euc n) r_e,
      (p, v) ∈ M.EHomeo.source ∧
      ∃ LE : (Euc n × Euc n) ≃L[ℝ] (Euc n × Euc n),
        HasStrictFDerivAt M.EMap (LE : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) (p, v) := by
    intro p hp v hv
    have hpv_re : (p, v) ∈ ball (M.a₀, (0 : Euc n)) r_e := by
      rw [Metric.mem_ball, Prod.dist_eq]; exact max_lt hp hv
    have hsrc : (p, v) ∈ M.EHomeo.source :=
      hresrc_sub (Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hpv_re)
    have hp_rg : p ∈ ball M.a₀ r_g := Metric.ball_subset_ball hre_rg hp
    have hv_rg : v ∈ ball (0 : Euc n) r_g := Metric.ball_subset_ball hre_rg hv
    obtain ⟨_, hU, ⟨L, hL_eq, hL_fd⟩, _, _⟩ := hrg p hp_rg v hv_rg
    let eval1Fst : PathPair n →L[ℝ] Euc n :=
      (ContinuousLinearMap.fst ℝ (Euc n) (Euc n)).comp (evalAtL ⟨1, right_mem_Icc.mpr zero_le_one⟩)
    let DE : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n) :=
      (ContinuousLinearMap.fst ℝ (Euc n) (Euc n)).prod
        (eval1Fst.comp ((L.symm : PathPair n →L[ℝ] PathPair n).comp constPairL))
    have hDE_fd : HasStrictFDerivAt M.EMap DE (p, v) := by
      have hgeod_fd : HasStrictFDerivAt (fun x : Euc n × Euc n => M.geod x.1 x.2)
          ((L.symm : PathPair n →L[ℝ] PathPair n).comp constPairL) (p, v) :=
        hL_fd.comp (p, v) constPairL.hasStrictFDerivAt
      exact (ContinuousLinearMap.fst ℝ (Euc n) (Euc n)).hasStrictFDerivAt.prodMk
        (eval1Fst.hasStrictFDerivAt.comp (p, v) hgeod_fd)
    -- Show `‖DE - eEquiv‖ < ‖E0inv‖⁻¹` so `DE` is a unit
    have hdist_z : dist (M.geod p v) M.z₀ < δ_d := by
      have hpv_lt : dist (p, v) (M.a₀, (0 : Euc n)) < r_ed := by
        rw [Prod.dist_eq]
        exact max_lt (lt_of_lt_of_le (Metric.mem_ball.mp hp) (min_le_right (min r_m r_esrc) r_ed))
          (lt_of_lt_of_le (Metric.mem_ball.mp hv) (min_le_right (min r_m r_esrc) r_ed))
      have h1 := @hred_sub (p, v) hpv_lt
      dsimp only at h1
      rwa [hgeod0] at h1
    have hdpsi_lt : ‖M.dpsi (M.geod p v) - M.dpsi M.z₀‖ < ε_d :=
      M.dpsi_norm_sub_le.trans_lt (hδ_d_spec (M.geod p v) hU hdist_z)
    have hL_diff : ‖(L : PathPair n →L[ℝ] PathPair n) - (dpsi0Equiv (n := n) : PathPair n →L[ℝ] PathPair n)‖ < ε_d := by
      rwa [hL_eq, ← M.dpsi_z₀_eq]
    have hLinv_norm : ‖(L.symm : PathPair n →L[ℝ] PathPair n)‖ ≤ 2 * (‖L0inv‖ + 1) := by
      have hsub_id : (L.symm : PathPair n →L[ℝ] PathPair n) =
          L0inv - (L.symm : PathPair n →L[ℝ] PathPair n) * ((L : PathPair n →L[ℝ] PathPair n) - (dpsi0Equiv (n := n) : PathPair n →L[ℝ] PathPair n)) * L0inv := by
        refine ContinuousLinearMap.ext fun h => ?_
        change L.symm h = dpsi0Equiv.symm h - L.symm (L (dpsi0Equiv.symm h) - dpsi0Equiv (dpsi0Equiv.symm h))
        rw [map_sub, L.symm_apply_apply, dpsi0Equiv.apply_symm_apply]; abel
      have hle1 : ‖(L.symm : PathPair n →L[ℝ] PathPair n)‖ ≤
          ‖L0inv‖ + ‖(L.symm : PathPair n →L[ℝ] PathPair n)‖ * (ε_d * ‖L0inv‖) := by
        calc ‖(L.symm : PathPair n →L[ℝ] PathPair n)‖
            ≤ ‖L0inv‖ + ‖(L.symm : PathPair n →L[ℝ] PathPair n) * ((L : PathPair n →L[ℝ] PathPair n) - (dpsi0Equiv (n := n) : PathPair n →L[ℝ] PathPair n)) * L0inv‖ := by
              conv_lhs => rw [hsub_id]
              exact norm_sub_le L0inv _
          _ ≤ ‖L0inv‖ + ‖(L.symm : PathPair n →L[ℝ] PathPair n)‖ * ‖(L : PathPair n →L[ℝ] PathPair n) - (dpsi0Equiv (n := n) : PathPair n →L[ℝ] PathPair n)‖ * ‖L0inv‖ := by
              gcongr
              exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
                (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) hL0inv_nn)
          _ ≤ ‖L0inv‖ + ‖(L.symm : PathPair n →L[ℝ] PathPair n)‖ * (ε_d * ‖L0inv‖) := by
              rw [← mul_assoc]
              gcongr
      have heps_half : ε_d * ‖L0inv‖ ≤ 1 / 2 := by
        calc ε_d * ‖L0inv‖ ≤ (2 * (‖L0inv‖ + 1))⁻¹ * (‖L0inv‖ + 1) :=
              mul_le_mul (min_le_left _ _) (by linarith) hL0inv_nn (by positivity)
          _ = 1 / 2 := by field_simp [show (‖L0inv‖ + 1 : ℝ) ≠ 0 by linarith]
      have h2 : ‖(L.symm : PathPair n →L[ℝ] PathPair n)‖ * (ε_d * ‖L0inv‖) ≤
          ‖(L.symm : PathPair n →L[ℝ] PathPair n)‖ * (1 / 2) :=
        mul_le_mul_of_nonneg_left heps_half (ContinuousLinearMap.opNorm_nonneg _)
      linarith
    have hLinv_diff : ‖(L.symm : PathPair n →L[ℝ] PathPair n) - L0inv‖ ≤
        2 * (‖L0inv‖ + 1) ^ 2 * ε_d := by
      have hid : (L.symm : PathPair n →L[ℝ] PathPair n) - L0inv =
          -((L.symm : PathPair n →L[ℝ] PathPair n) * ((L : PathPair n →L[ℝ] PathPair n) - (dpsi0Equiv (n := n) : PathPair n →L[ℝ] PathPair n)) * L0inv) := by
        refine ContinuousLinearMap.ext fun h => ?_
        change L.symm h - dpsi0Equiv.symm h = -(L.symm (L (dpsi0Equiv.symm h) - dpsi0Equiv (dpsi0Equiv.symm h)))
        rw [map_sub, L.symm_apply_apply, dpsi0Equiv.apply_symm_apply]; abel
      rw [hid, ContinuousLinearMap.opNorm_neg]
      calc ‖(L.symm : PathPair n →L[ℝ] PathPair n) * ((L : PathPair n →L[ℝ] PathPair n) - (dpsi0Equiv (n := n) : PathPair n →L[ℝ] PathPair n)) * L0inv‖
          ≤ ‖(L.symm : PathPair n →L[ℝ] PathPair n)‖ * ‖(L : PathPair n →L[ℝ] PathPair n) - (dpsi0Equiv (n := n) : PathPair n →L[ℝ] PathPair n)‖ * ‖L0inv‖ :=
            (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) hL0inv_nn)
        _ ≤ (2 * (‖L0inv‖ + 1)) * ε_d * (‖L0inv‖ + 1) := by
            refine mul_le_mul (mul_le_mul hLinv_norm hL_diff.le (ContinuousLinearMap.opNorm_nonneg _) (by positivity))
              (by linarith) hL0inv_nn (by positivity)
        _ = 2 * (‖L0inv‖ + 1) ^ 2 * ε_d := by ring
    have hDE_diff : ‖DE - (eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n))‖ ≤
        2 * (‖L0inv‖ + 1) ^ 2 * ε_d := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
      have h1 : ((DE - (eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n))) x).1 = 0 := sub_self _
      have h2 : ((DE - (eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n))) x).2 =
          ((((L.symm : PathPair n →L[ℝ] PathPair n) - L0inv) (constPairL x)) ⟨1, right_mem_Icc.mpr zero_le_one⟩).1 := by
        change (L.symm (constPairL x) ⟨1, _⟩).1 - (x.1 + x.2) =
          (L.symm (constPairL x) ⟨1, _⟩).1 - (L0inv (constPairL x) ⟨1, _⟩).1
        congr 1
        change x.1 + x.2 = x.1 + intFun (proj2L (constPairL x)) 1
        simp [intFun, proj2L, constPairL]
      have hnorm2 : ‖(((L.symm : PathPair n →L[ℝ] PathPair n) - L0inv) (constPairL x) ⟨1, right_mem_Icc.mpr zero_le_one⟩).1‖ ≤
          2 * (‖L0inv‖ + 1) ^ 2 * ε_d * ‖x‖ := by
        calc ‖(((L.symm : PathPair n →L[ℝ] PathPair n) - L0inv) (constPairL x) ⟨1, right_mem_Icc.mpr zero_le_one⟩).1‖
            ≤ ‖((L.symm : PathPair n →L[ℝ] PathPair n) - L0inv) (constPairL x) ⟨1, right_mem_Icc.mpr zero_le_one⟩‖ :=
              norm_fst_le _
          _ ≤ ‖((L.symm : PathPair n →L[ℝ] PathPair n) - L0inv) (constPairL x)‖ :=
              BoundedContinuousFunction.norm_coe_le_norm _ _
          _ ≤ ‖(L.symm : PathPair n →L[ℝ] PathPair n) - L0inv‖ * ‖constPairL x‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ (2 * (‖L0inv‖ + 1) ^ 2 * ε_d) * ‖x‖ := by
              have hc : ‖constPairL x‖ ≤ ‖x‖ := by
                refine (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr fun _ => le_rfl
              exact mul_le_mul hLinv_diff hc (norm_nonneg _) (by positivity)
      exact max_le (by rw [h1, norm_zero]; positivity) (by rw [h2]; exact hnorm2)
    have hprod_lt : ‖E0inv * ((eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) - DE)‖ < 1 := by
      have hrev : ‖(eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) - DE‖ =
          ‖DE - (eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n))‖ := by
        rw [show (eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) - DE =
          -(DE - (eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n))) by abel,
          ContinuousLinearMap.opNorm_neg]
      calc ‖E0inv * ((eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) - DE)‖
          ≤ ‖E0inv‖ * ‖(eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) - DE‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖E0inv‖ * ‖DE - (eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n))‖ := by rw [hrev]
        _ ≤ ‖E0inv‖ * (2 * (‖L0inv‖ + 1) ^ 2 * ε_d) := mul_le_mul_of_nonneg_left hDE_diff hE0inv_nn
        _ < (‖E0inv‖ + 1) * (2 * (‖L0inv‖ + 1) ^ 2 * ε_d) := by
            have : 0 < 2 * (‖L0inv‖ + 1) ^ 2 * ε_d := by positivity
            linarith
        _ ≤ (‖E0inv‖ + 1) * (2 * (‖L0inv‖ + 1) ^ 2 * (4 * (‖L0inv‖ + 1) ^ 2 * (‖E0inv‖ + 1))⁻¹) := by
            gcongr; exact min_le_right _ _
        _ = 1 / 2 := by
            have h1 : (‖L0inv‖ + 1 : ℝ) ≠ 0 := by linarith
            have h2 : (‖E0inv‖ + 1 : ℝ) ≠ 0 := by linarith
            field_simp [h1, h2]; ring
        _ < 1 := by norm_num
    have hu1 : IsUnit (1 - E0inv * ((eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) - DE)) :=
      (Units.oneSub _ hprod_lt).isUnit
    have heq1 : 1 - E0inv * ((eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) - DE) = E0inv * DE := by
      refine ContinuousLinearMap.ext fun x => ?_
      change x - eEquiv.symm (eEquiv x - DE x) = eEquiv.symm (DE x)
      rw [map_sub, eEquiv.symm_apply_apply]; abel
    rw [heq1] at hu1
    have hE0u : IsUnit (eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) :=
      ⟨⟨(eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)), E0inv,
        ContinuousLinearMap.ext fun h => eEquiv.apply_symm_apply h,
        ContinuousLinearMap.ext fun h => eEquiv.symm_apply_apply h⟩, rfl⟩
    have hDE_unit : IsUnit DE := by
      have heq2 : (eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) * (E0inv * DE) = DE := by
        rw [← mul_assoc, show (eEquiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) * E0inv = 1 by
          exact ContinuousLinearMap.ext fun h => eEquiv.apply_symm_apply h, one_mul]
      rw [← heq2]; exact hE0u.mul hu1
    obtain ⟨u, hu⟩ := hDE_unit
    let LE : (Euc n × Euc n) ≃L[ℝ] (Euc n × Euc n) :=
      { toLinearEquiv :=
          { toFun := u.val
            invFun := u.inv
            map_add' := map_add _
            map_smul' := map_smul _
            left_inv := fun h => congrArg (fun f : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n) => f h) u.inv_val
            right_inv := fun h => congrArg (fun f : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n) => f h) u.val_inv }
        continuous_toFun := u.val.continuous
        continuous_invFun := u.inv.continuous }
    refine ⟨hsrc, LE, ?_⟩
    have hLE : (LE : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) = DE :=
      ContinuousLinearMap.ext fun h => congrArg (fun f : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n) => f h) hu
    rw [hLE]; exact hDE_fd
  obtain ⟨r_b, hr_b, hrb_sub⟩ := Metric.continuousAt_iff.mp hgeod_cont r_m hr_m
  let r_v : ℝ := min r_e r_b
  have hr_v : 0 < r_v := lt_min hr_e hr_b
  let ρ_0 : ℝ := m_g * r_v
  have hρ_0 : 0 < ρ_0 := mul_pos hm_g hr_v
  have hE0_tgt : (M.a₀, M.a₀) ∈ M.EHomeo.target := by
    rw [← M.EMap_zero]; exact M.EMap_hasStrictFDerivAt_zero.image_mem_toOpenPartialHomeomorph_target
  have hsymm_cont : ContinuousAt M.EHomeo.symm (M.a₀, M.a₀) := M.EHomeo.continuousAt_symm hE0_tgt
  have hsymm0 : M.EHomeo.symm (M.a₀, M.a₀) = (M.a₀, 0) := by
    have h1 := M.EHomeo.left_inv hE0_src
    have h2 : M.EHomeo (M.a₀, 0) = (M.a₀, M.a₀) := M.EMap_zero
    rwa [h2] at h1
  let r_l : ℝ := min r_v (ρ_0 / (2 * M_g))
  have hr_l : 0 < r_l := lt_min hr_v (div_pos hρ_0 (by positivity))
  have hpre_E : M.EHomeo.target ∩ M.EHomeo.symm ⁻¹' (ball (M.a₀, (0 : Euc n)) r_l) ∈ 𝓝 (M.a₀, M.a₀) :=
    Filter.inter_mem (M.EHomeo.open_target.mem_nhds hE0_tgt)
      (hsymm_cont.preimage_mem_nhds (by rw [hsymm0]; exact ball_mem_nhds _ hr_l))
  obtain ⟨r_n0, hr_n0, hrn0_sub⟩ := Metric.mem_nhds_iff.mp hpre_E
  let r_n : ℝ := min r_v r_n0
  have hr_n : 0 < r_n := lt_min hr_v hr_n0
  have hrn_rv : r_n ≤ r_v := min_le_left _ _
  have hrn_re : r_n ≤ r_e := hrn_rv.trans (min_le_left _ _)
  have hrn_rm : r_n ≤ r_m := hrn_re.trans hre_rm
  have hball_exp : ∀ p ∈ ball M.a₀ r_n, ∀ v : Euc n, M.gnorm p v < ρ_0 →
      v ∈ ball (0 : Euc n) r_e ∧
      M.exp p v ∈ ball M.a₀ r_m ∧
      (p, M.exp p v) ∈ M.EHomeo.target ∧
      M.log p (M.exp p v) = v ∧
      (∃ LE : (Euc n × Euc n) ≃L[ℝ] (Euc n × Euc n),
        HasStrictFDerivAt M.EHomeo.symm (LE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) (p, M.exp p v)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, M.γExt p v t ∈ ball M.a₀ r_m := by
    intro p hp v hgn
    have hp_rm : p ∈ closedBall M.a₀ r_m :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball hrn_rm hp)
    have hnv_lt : ‖v‖ < r_v := by
      have h1 := (hmbd p hp_rm v).1
      have h2 : m_g * ‖v‖ < m_g * r_v := lt_of_le_of_lt h1 hgn
      exact (mul_lt_mul_iff_right₀ hm_g).mp h2
    have hv_rv : v ∈ ball (0 : Euc n) r_v := by simpa [Metric.mem_ball] using hnv_lt
    have hv_re : v ∈ ball (0 : Euc n) r_e := Metric.ball_subset_ball (min_le_left _ _) hv_rv
    have hp_re : p ∈ ball M.a₀ r_e := Metric.ball_subset_ball hrn_re hp
    obtain ⟨hsrc, LE, hLE⟩ := hE_inv p hp_re v hv_re
    have hpv_rb : (p, v) ∈ ball (M.a₀, (0 : Euc n)) r_b := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt (Metric.ball_subset_ball (hrn_rv.trans (min_le_right _ _)) hp)
        (Metric.ball_subset_ball (min_le_right _ _) hv_rv)
    have hgeod_rm : dist (M.geod p v) M.z₀ < r_m := by
      have h1 := @hrb_sub (p, v) (Metric.mem_ball.mp hpv_rb)
      dsimp only at h1
      rwa [hgeod0] at h1
    have htgt_geod := (hrg p (Metric.ball_subset_ball hre_rg hp_re) v (Metric.ball_subset_ball hre_rg hv_re)).1
    have hγ_ball : ∀ t ∈ Icc (0 : ℝ) 1, M.γExt p v t ∈ ball M.a₀ r_m := fun t ht => by
      have h1 := (M.geod_eq_ext htgt_geod ⟨t, ht⟩).1
      rw [← h1]
      show dist (M.geod p v ⟨t, ht⟩).1 M.a₀ < r_m
      calc dist (M.geod p v ⟨t, ht⟩).1 M.a₀
          ≤ dist (M.geod p v ⟨t, ht⟩) (M.z₀ ⟨t, ht⟩) := by
            simpa [dist_eq_norm, z₀, constPairL] using norm_fst_le (M.geod p v ⟨t, ht⟩ - M.z₀ ⟨t, ht⟩)
        _ ≤ dist (M.geod p v) M.z₀ := BoundedContinuousFunction.dist_coe_le_dist _
        _ < r_m := hgeod_rm
    have hexp_ball : M.exp p v ∈ ball M.a₀ r_m := by
      rw [← M.γExt_one htgt_geod]; exact hγ_ball 1 (right_mem_Icc.mpr zero_le_one)
    have htgt_E : (p, M.exp p v) ∈ M.EHomeo.target := M.EHomeo.map_source hsrc
    have hleft_E : M.EHomeo.symm (p, M.exp p v) = (p, v) := M.EHomeo.left_inv hsrc
    have hlog_eq : M.log p (M.exp p v) = v := congrArg Prod.snd hleft_E
    have hsymm_fd : HasStrictFDerivAt M.EHomeo.symm (LE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) (p, M.exp p v) := by
      have hfd' : HasStrictFDerivAt M.EMap (LE : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n))
          (M.EHomeo.symm (p, M.exp p v)) := by rw [hleft_E]; exact hLE
      exact M.EHomeo.hasStrictFDerivAt_symm htgt_E hfd'
    exact ⟨hv_re, hexp_ball, htgt_E, hlog_eq, ⟨LE, hsymm_fd⟩, hγ_ball⟩
  refine ⟨r_g, r_m, r_e, r_n, ρ_0, m_g, M_g, L_g,
    hr_g, hr_m, hr_e, hr_n, hρ_0, hm_g, hM_g, hL_g,
    hrm_lt, hrn_re, hre_rm, hrm_rg, hmbd, hmlip, hrg, hE_inv, hball_exp, ?_⟩
  intro p hp q hq
  have hpq_rn0 : (p, q) ∈ ball (M.a₀, M.a₀) r_n0 := by
    rw [Metric.mem_ball, Prod.dist_eq]
    exact max_lt (Metric.ball_subset_ball (min_le_right _ _) hp) (Metric.ball_subset_ball (min_le_right _ _) hq)
  obtain ⟨htgt_E, hsymm_ball⟩ := hrn0_sub hpq_rn0
  have hsymm_fst : (M.EHomeo.symm (p, q)).1 = p := by
    have h1 := M.EHomeo.right_inv htgt_E
    exact congrArg Prod.fst h1
  have hexp_log : M.exp p (M.log p q) = q := by
    have h1 := M.EHomeo.right_inv htgt_E
    have h2 : M.EHomeo.symm (p, q) = (p, M.log p q) := Prod.ext hsymm_fst rfl
    rw [h2] at h1
    exact congrArg Prod.snd h1
  have hlog_rl : M.log p q ∈ ball (0 : Euc n) r_l := by
    have h1 : dist (M.EHomeo.symm (p, q)).2 (0 : Euc n) < r_l :=
      (by simpa [dist_eq_norm] using norm_snd_le (M.EHomeo.symm (p, q) - (M.a₀, (0 : Euc n))) :
        dist (M.EHomeo.symm (p, q)).2 0 ≤ dist (M.EHomeo.symm (p, q)) (M.a₀, 0)).trans_lt hsymm_ball
    exact h1
  have hlog_re : M.log p q ∈ ball (0 : Euc n) r_e :=
    Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hlog_rl
  have hgn_half : M.gnorm p (M.log p q) < ρ_0 / 2 := by
    have hp_rm : p ∈ closedBall M.a₀ r_m :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball hrn_rm hp)
    have hnorm_lt : ‖M.log p q‖ < ρ_0 / (2 * M_g) := by
      have h1 : dist (M.log p q) 0 < ρ_0 / (2 * M_g) := Metric.ball_subset_ball (min_le_right _ _) hlog_rl
      simpa [dist_zero_right] using h1
    calc M.gnorm p (M.log p q) ≤ M_g * ‖M.log p q‖ := (hmbd p hp_rm _).2
      _ < M_g * (ρ_0 / (2 * M_g)) := mul_lt_mul_of_pos_left hnorm_lt hM_g
      _ = ρ_0 / 2 := by field_simp [hM_g.ne']
  -- Symmetrically, `M.ξExt q (M.log q p) 1 = -M.log p q` via geodesic reversal
  have hrev_eq : M.ξExt q (M.log q p) 1 = -M.log p q := by
    have hp_rg : p ∈ ball M.a₀ r_g := Metric.ball_subset_ball (hrn_rm.trans hrm_rg) hp
    have hv_rg : M.log p q ∈ ball (0 : Euc n) r_g := Metric.ball_subset_ball hre_rg hlog_re
    obtain ⟨htgt_g, hU_g, _, _, hrev_src⟩ := hrg p hp_rg (M.log p q) hv_rg
    obtain ⟨_, hexp_rev, hξ_rev⟩ := M.geod_reverse htgt_g hU_g hrev_src
    rw [hexp_log] at hexp_rev hξ_rev
    set w : Euc n := M.ξExt p (M.log p q) 1
    have hgn_w : M.gnorm q (-w) < ρ_0 := by
      have hcs := M.geod_const_speed htgt_g hU_g (right_mem_Icc.mpr zero_le_one)
      rw [M.γExt_one htgt_g, hexp_log] at hcs
      have hgn_eq : M.gnorm q (-w) = M.gnorm p (M.log p q) := by
        simp only [gnorm, M.inner_neg_left, M.inner_neg_right, neg_neg, w, hcs]
      rw [hgn_eq]
      linarith
    have hlog_qp : M.log q p = -w := by
      have h1 := (hball_exp q hq (-w) hgn_w).2.2.2.1
      rwa [hexp_rev] at h1
    rw [hlog_qp]
    exact hξ_rev
  obtain ⟨_, _, _, _, hsymm_fd, _⟩ := hball_exp p hp (M.log p q) (by linarith)
  rw [hexp_log] at hsymm_fd
  exact ⟨htgt_E, hlog_re, hgn_half, hexp_log, hrev_eq, hsymm_fd⟩

end LocalMetric
end GeodesicFlow

end Hilbert5H1

-- Section 2: H1_M2_RiemannianDist.lean
namespace Hilbert5H1

open Metric Set Filter Topology MeasureTheory Manifold intervalIntegral
open scoped Manifold ContDiff Bundle ENNReal RealInnerProductSpace Classical

section PullbackMetric

/-- Pull back a smooth Riemannian bundle on `chartAt (Euc n) x₀` into coordinate components `g`. -/
lemma pullback_metric_exists {n : ℕ} {X : Type} [MetricSpace X]
    [ChartedSpace (Euc n) X] [IsManifold (𝓡 n) ∞ X]
    [hRB : Bundle.RiemannianBundle (fun x : X => TangentSpace (𝓡 n) x)]
    [hCRB : IsContMDiffRiemannianBundle (𝓡 n) ∞ (Euc n) (fun x : X => TangentSpace (𝓡 n) x)]
    (x₀ : X) :
    let φ := chartAt (Euc n) x₀
    let a₀ := φ x₀
    let g : Euc n → Fin n → Fin n → ℝ := fun y i j =>
      ⟪(trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm y) (LocalMetric.e i),
       (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm y) (LocalMetric.e j)⟫
    ∃ r₁ > 0, ball a₀ r₁ ⊆ φ.target ∧
      (∀ i j, ContDiffOn ℝ 3 (fun y => g y i j) (ball a₀ r₁)) ∧
      (∀ y ∈ ball a₀ r₁, ∀ i j, g y i j = g y j i) ∧
      (∀ y ∈ ball a₀ r₁, ∀ u v : Euc n,
        ∑ i, ∑ j, g y i j * u.ofLp i * v.ofLp j =
          ⟪(trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm y) u,
           (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm y) v⟫) ∧
      (∀ y ∈ ball a₀ r₁, ∀ v : Euc n, v ≠ 0 →
        0 < ∑ i, ∑ j, g y i j * v.ofLp i * v.ofLp j) := by
  intro φ a₀ g
  obtain ⟨gX, hgX_mdiff, hgX_inner⟩ := hCRB.exists_contMDiff
  have hX := (contMDiffAt_hom_bundle _ (x₀ := x₀)).mp (hgX_mdiff x₀)
  let T := trivializationAt (Euc n →L[ℝ] ℝ) (fun b => TangentSpace (𝓡 n) b →L[ℝ] ℝ) x₀
  let Gchart : X → Euc n →L[ℝ] Euc n →L[ℝ] ℝ := fun x =>
    ContinuousLinearMap.inCoordinates (Euc n) (TangentSpace (𝓡 n))
      (Euc n →L[ℝ] ℝ) (fun b => TangentSpace (𝓡 n) b →L[ℝ] ℝ) x₀ x x₀ x (gX x)
  have hGchart_md : ContMDiffAt (𝓡 n) 𝓘(ℝ, Euc n →L[ℝ] Euc n →L[ℝ] ℝ) ∞ Gchart x₀ := hX.2
  have hGchart_val : ∀ x ∈ φ.source, ∀ u v : Euc n,
      Gchart x u v =
        ⟪(trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ x u,
         (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ x v⟫ := by
    intro x hx u v
    have hbx : x ∈ T.baseSet := by
      change x ∈ φ.source ∩ Set.univ
      exact ⟨hx, trivial⟩
    have hL : (T.continuousLinearMapAt ℝ x
        ((gX x) ((trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ x u))) v =
        (gX x) ((trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ x u)
          ((trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ x v) := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hbx]
      change (ContinuousLinearMap.inCoordinates (Euc n) (TangentSpace (𝓡 n)) ℝ (Bundle.Trivial X ℝ)
        x₀ x x₀ x ((gX x) ((trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ x u))) v = _
      simp [ContinuousLinearMap.inCoordinates]
    have hGeq : Gchart x u v =
        (T.continuousLinearMapAt ℝ x
          ((gX x) ((trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ x u))) v := by
      simp [Gchart, ContinuousLinearMap.inCoordinates, T]
    rw [hGeq, hL, ← hgX_inner]
  have hcomp_cd : ContDiffAt ℝ 3 (fun y : Euc n => Gchart (φ.symm y)) a₀ := by
    have hle : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
      change ((3 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top
    have h1 : ContMDiffAt (𝓡 n) 𝓘(ℝ, Euc n →L[ℝ] Euc n →L[ℝ] ℝ) 3 Gchart x₀ := hGchart_md.of_le hle
    have h2 : ContMDiffAt (𝓡 n) (𝓡 n) 3 φ.symm a₀ := by
      have ha₀ : a₀ ∈ (extChartAt (𝓡 n) x₀).target := mem_extChartAt_target x₀
      have hOn := contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := (∞ : WithTop ℕ∞)) x₀ a₀ ha₀
      have hmem : (extChartAt (𝓡 n) x₀).target ∈ 𝓝 a₀ := by
        simpa [extChartAt_target] using φ.open_target.mem_nhds (mem_chart_target (Euc n) x₀)
      exact (hOn.contMDiffAt hmem).of_le hle
    have h3 : ContMDiffAt (𝓡 n) 𝓘(ℝ, Euc n →L[ℝ] Euc n →L[ℝ] ℝ) 3 (Gchart ∘ φ.symm) a₀ := by
      have hsymm : φ.symm a₀ = x₀ := φ.left_inv (mem_chart_source (Euc n) x₀)
      exact (hsymm ▸ h1).comp a₀ h2
    exact contMDiffAt_iff_contDiffAt.mp h3
  obtain ⟨u, hu_nhds, hu_cd⟩ := hcomp_cd.contDiffOn le_rfl (by simp)
  have hmem : u ∩ φ.target ∈ 𝓝 a₀ :=
    Filter.inter_mem hu_nhds (φ.open_target.mem_nhds (mem_chart_target (Euc n) x₀))
  obtain ⟨r₁, hr₁, hr₁_sub⟩ := Metric.mem_nhds_iff.mp hmem
  have hr₁_tgt : ball a₀ r₁ ⊆ φ.target := fun y hy => (hr₁_sub hy).2
  have hr₁_u : ball a₀ r₁ ⊆ u := fun y hy => (hr₁_sub hy).1
  have hinner_eq : ∀ y ∈ ball a₀ r₁, ∀ u v : Euc n,
      ∑ i, ∑ j, g y i j * u.ofLp i * v.ofLp j =
        ⟪(trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm y) u,
         (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm y) v⟫ := by
    intro y hy u v
    have hu_exp : u = ∑ i, u.ofLp i • LocalMetric.e i := by ext m; simp [LocalMetric.e, Pi.single_apply]
    have hv_exp : v = ∑ j, v.ofLp j • LocalMetric.e j := by ext m; simp [LocalMetric.e, Pi.single_apply]
    conv_rhs => rw [hu_exp, hv_exp]
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, g]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine ⟨r₁, hr₁, hr₁_tgt, ?_, ?_, hinner_eq, ?_⟩
  · intro i j
    have heval : ContDiffOn ℝ 3 (fun y => Gchart (φ.symm y) (LocalMetric.e i) (LocalMetric.e j)) (ball a₀ r₁) :=
      ((hu_cd.mono hr₁_u).clm_apply contDiffOn_const).clm_apply contDiffOn_const
    refine heval.congr fun y hy => ?_
    exact (hGchart_val (φ.symm y) (φ.map_target (hr₁_tgt hy)) (LocalMetric.e i) (LocalMetric.e j)).symm
  · intro y _ i j; exact real_inner_comm _ _
  · intro y hy v hv
    rw [hinner_eq y hy v v]
    have hsrc : φ.symm y ∈ φ.source := φ.map_target (hr₁_tgt hy)
    have hne : (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm y) v ≠ 0 := by
      intro h0
      have hinv := (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).continuousLinearMapAt_symmL
        (R := ℝ) (by simpa [TangentBundle.trivializationAt_baseSet] using hsrc) v
      rw [h0, map_zero] at hinv
      exact hv hinv.symm
    exact real_inner_self_pos.mpr hne

/-- Tangent-vector norm of `φ.symm ∘ η` in the Riemannian metric equals `M.gnorm`. -/
lemma chart_curve_enorm_eq {n : ℕ} {X : Type} [MetricSpace X]
    [ChartedSpace (Euc n) X] [IsManifold (𝓡 n) ∞ X]
    [Bundle.RiemannianBundle (fun x : X => TangentSpace (𝓡 n) x)]
    (x₀ : X) (M : LocalMetric n)
    (_hMa : M.a₀ = chartAt (Euc n) x₀ x₀)
    (htgt : ball M.a₀ M.r₁ ⊆ (chartAt (Euc n) x₀).target)
    (hinner : ∀ y ∈ ball M.a₀ M.r₁, ∀ u v : Euc n,
      M.inner y u v =
        ⟪(trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ ((chartAt (Euc n) x₀).symm y) u,
         (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ ((chartAt (Euc n) x₀).symm y) v⟫)
    {a b : ℝ} (hab : a < b) {η : ℝ → Euc n}
    (hη_cd : ContDiffOn ℝ 1 η (Icc a b))
    (hη_ball : ∀ t ∈ Icc a b, η t ∈ ball M.a₀ M.r₁)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) ((chartAt (Euc n) x₀).symm ∘ η) (Icc a b) t 1‖ₑ =
      ENNReal.ofReal (M.gnorm (η t) (derivWithin η (Icc a b) t)) := by
  let φ := chartAt (Euc n) x₀
  have hηt : η t ∈ ball M.a₀ M.r₁ := hη_ball t ht
  have hηt_tgt : η t ∈ (extChartAt (𝓡 n) x₀).target := by
    simpa [extChartAt_target] using htgt hηt
  have hsrc : φ.symm (η t) ∈ φ.source := φ.map_target (htgt hηt)
  have hcomp : mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) ((extChartAt (𝓡 n) x₀).symm ∘ η) (Icc a b) t =
      (mfderivWithin (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x₀).symm (range (𝓡 n)) (η t)) ∘L
        (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) η (Icc a b) t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm hηt_tgt
    · rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
      exact hη_cd.differentiableOn one_ne_zero t ht
    · intro s _; simp
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc hab t ht
  have h1 : mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) (φ.symm ∘ η) (Icc a b) t 1 =
      (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm (η t)) (derivWithin η (Icc a b) t) := by
    have hcomp1 : mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) ((extChartAt (𝓡 n) x₀).symm ∘ η) (Icc a b) t 1 =
        (mfderivWithin (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x₀).symm (range (𝓡 n)) (η t))
          (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) η (Icc a b) t 1) := by
      rw [hcomp, ContinuousLinearMap.comp_apply]
    change mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) ((extChartAt (𝓡 n) x₀).symm ∘ η) (Icc a b) t 1 = _
    rw [hcomp1]
    have hη1 : mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) η (Icc a b) t 1 = derivWithin η (Icc a b) t := by
      rw [mfderivWithin_eq_fderivWithin, ← fderivWithin_derivWithin]; rfl
    rw [hη1]
    have hsymm_eq := TangentBundle.symmL_trivializationAt (I := 𝓡 n) (x₀ := x₀) (x := φ.symm (η t)) hsrc
    have hleft : extChartAt (𝓡 n) x₀ (φ.symm (η t)) = η t := by
      change φ (φ.symm (η t)) = η t; exact φ.right_inv (htgt hηt)
    rw [hleft] at hsymm_eq
    exact (congrArg (fun L : Euc n →L[ℝ] TangentSpace (𝓡 n) (φ.symm (η t)) =>
      L (derivWithin η (Icc a b) t)) hsymm_eq).symm
  rw [h1]
  have hnorm : ‖(trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm (η t))
      (derivWithin η (Icc a b) t)‖ = M.gnorm (η t) (derivWithin η (Icc a b) t) := by
    rw [norm_eq_sqrt_real_inner, ← hinner (η t) hηt _ _]; rfl
  rw [← ofReal_norm, hnorm]

/-- Normal-ball Riemannian distance equals `M.gnorm p (M.log p q)` on `ball M.a₀ r_n`. -/
lemma dist_eq_gnorm_log {n : ℕ} (_hn : 0 < n) {X : Type} [MetricSpace X]
    [ChartedSpace (Euc n) X] [IsManifold (𝓡 n) ∞ X]
    [Bundle.RiemannianBundle (fun x : X => TangentSpace (𝓡 n) x)]
    [IsContMDiffRiemannianBundle (𝓡 n) ∞ (Euc n) (fun x : X => TangentSpace (𝓡 n) x)]
    [hRM : IsRiemannianManifold (𝓡 n) X]
    (x₀ : X) (M : LocalMetric n)
    (hMa : M.a₀ = chartAt (Euc n) x₀ x₀)
    (htgt : ball M.a₀ M.r₁ ⊆ (chartAt (Euc n) x₀).target)
    (hinner : ∀ y ∈ ball M.a₀ M.r₁, ∀ u v : Euc n,
      M.inner y u v =
        ⟪(trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ ((chartAt (Euc n) x₀).symm y) u,
         (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ ((chartAt (Euc n) x₀).symm y) v⟫)
    {r_g r_m r_e r_n ρ_0 m_g M_g : ℝ}
    (hr_g : 0 < r_g) (_hr_m : 0 < r_m) (_hr_e : 0 < r_e) (_hr_n : 0 < r_n) (hρ_0 : 0 < ρ_0)
    (hrm_lt : r_m < M.r₁) (hrn_re : r_n ≤ r_e) (hre_rm : r_e ≤ r_m) (hrm_rg : r_m ≤ r_g)
    (hm_g : 0 < m_g)
    (hmbd : ∀ y ∈ closedBall M.a₀ r_m, ∀ w : Euc n, m_g * ‖w‖ ≤ M.gnorm y w ∧ M.gnorm y w ≤ M_g * ‖w‖)
    (hrg : ∀ p ∈ ball M.a₀ r_g, ∀ v ∈ ball (0 : Euc n) r_g,
      constPairL (p, v) ∈ M.psiHomeo.target ∧
      M.geod p v ∈ M.U_V ∧
      (∃ L : PathPair n ≃L[ℝ] PathPair n,
        (L : PathPair n →L[ℝ] PathPair n) = M.dpsi (M.geod p v) ∧
        HasStrictFDerivAt M.psiHomeo.symm (L.symm : PathPair n →L[ℝ] PathPair n) (constPairL (p, v))) ∧
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1), LocalMetric.scalePath (M.geod p v) s hs ∈ M.psiHomeo.source) ∧
      LocalMetric.revPath (M.geod p v) ∈ M.psiHomeo.source)
    (hball_exp : ∀ p ∈ ball M.a₀ r_n, ∀ v : Euc n, M.gnorm p v < ρ_0 →
      v ∈ ball (0 : Euc n) r_e ∧
      M.exp p v ∈ ball M.a₀ r_m ∧
      (p, M.exp p v) ∈ M.EHomeo.target ∧
      M.log p (M.exp p v) = v ∧
      (∃ LE : (Euc n × Euc n) ≃L[ℝ] (Euc n × Euc n),
        HasStrictFDerivAt M.EHomeo.symm (LE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) (p, M.exp p v)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, M.γExt p v t ∈ ball M.a₀ r_m)
    (hball_log : ∀ p ∈ ball M.a₀ r_n, ∀ q ∈ ball M.a₀ r_n,
      (p, q) ∈ M.EHomeo.target ∧
      M.log p q ∈ ball (0 : Euc n) r_e ∧
      M.gnorm p (M.log p q) < ρ_0 / 2 ∧
      M.exp p (M.log p q) = q ∧
      M.ξExt q (M.log q p) 1 = -M.log p q ∧
      ∃ LE : (Euc n × Euc n) ≃L[ℝ] (Euc n × Euc n),
        HasStrictFDerivAt M.EHomeo.symm (LE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) (p, q))
    {p q : Euc n} (hp : p ∈ ball M.a₀ r_n) (hq : q ∈ ball M.a₀ r_n) :
    dist ((chartAt (Euc n) x₀).symm p) ((chartAt (Euc n) x₀).symm q) = M.gnorm p (M.log p q) := by
  let φ := chartAt (Euc n) x₀
  obtain ⟨htgt_pq, hlog_re, hgn_half, hexp_log, _, _⟩ := hball_log p hp q hq
  set v : Euc n := M.log p q
  have hp_rm : p ∈ ball M.a₀ r_m := Metric.ball_subset_ball (hrn_re.trans hre_rm) hp
  have hp_r1 : p ∈ ball M.a₀ M.r₁ := Metric.ball_subset_ball hrm_lt.le hp_rm
  have hp_rg : p ∈ ball M.a₀ r_g := Metric.ball_subset_ball hrm_rg hp_rm
  have hv_rg : v ∈ ball (0 : Euc n) r_g := Metric.ball_subset_ball (hre_rm.trans hrm_rg) hlog_re
  obtain ⟨htgt_g, hU_g, _, _, _⟩ := hrg p hp_rg v hv_rg
  -- Part 1: Upper bound `dist (φ.symm p) (φ.symm q) ≤ M.gnorm p v` via the geodesic `φ.symm ∘ γExt p v`
  have hupper : dist (φ.symm p) (φ.symm q) ≤ M.gnorm p v := by
    have hγ_cd : ContDiffOn ℝ 1 (M.γExt p v) (Icc 0 1) := by
      rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc zero_lt_one)]
      refine ⟨fun t ht => (M.γExt_hasDerivAt htgt_g ht).differentiableAt.differentiableWithinAt, ?_⟩
      have heq : EqOn (derivWithin (M.γExt p v) (Icc 0 1)) (M.ξExt p v) (Icc 0 1) := fun t ht =>
        (M.γExt_hasDerivAt htgt_g ht).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one t ht)
      have hξ_cont : ContinuousOn (M.ξExt p v) (Icc 0 1) := by
        have hc : Continuous (M.ξExt p v) :=
          continuous_const.sub (continuous_iff_continuousAt.mpr fun s =>
            (intFun_hasDerivAt (M.quadOp (M.geod p v)) s).continuousAt)
        exact hc.continuousOn
      exact hξ_cont.congr heq
    have hγ_ball : ∀ t ∈ Icc (0 : ℝ) 1, M.γExt p v t ∈ ball M.a₀ M.r₁ := fun t ht =>
      Metric.ball_subset_ball hrm_lt.le ((hball_exp p hp v (by linarith)).2.2.2.2.2 t ht)
    have hcmd : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 (φ.symm ∘ M.γExt p v) (Icc 0 1) := by
      refine (contMDiffOn_extChartAt_symm (I := 𝓡 n) x₀).comp
        (contMDiffOn_iff_contDiffOn.mpr hγ_cd) fun t ht => ?_
      simpa [extChartAt_target] using htgt (hγ_ball t ht)
    have hed : edist (φ.symm p) (φ.symm q) ≤ pathELength (𝓡 n) (φ.symm ∘ M.γExt p v) 0 1 := by
      rw [hRM.out]
      exact riemannianEDist_le_pathELength hcmd
        (by simp [M.γExt_zero]) (by simp [M.γExt_one htgt_g, hexp_log]) zero_le_one
    have hlen : pathELength (𝓡 n) (φ.symm ∘ M.γExt p v) 0 1 = ENNReal.ofReal (M.gnorm p v) := by
      rw [pathELength_eq_lintegral_mfderivWithin_Icc]
      have hcongr : ∀ t ∈ Icc (0 : ℝ) 1,
          ‖mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) (φ.symm ∘ M.γExt p v) (Icc 0 1) t 1‖ₑ =
            ENNReal.ofReal (M.gnorm p v) := fun t ht => by
        rw [chart_curve_enorm_eq x₀ M hMa htgt hinner zero_lt_one hγ_cd hγ_ball ht]
        have hder : derivWithin (M.γExt p v) (Icc 0 1) t = M.ξExt p v t :=
          (M.γExt_hasDerivAt htgt_g ht).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one t ht)
        rw [hder]
        congr 1
        simp only [LocalMetric.gnorm, M.geod_const_speed htgt_g hU_g ht]
      rw [setLIntegral_congr_fun measurableSet_Icc hcongr, lintegral_const, Measure.restrict_apply_univ,
        Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
    rw [hlen, edist_dist] at hed
    exact (ENNReal.ofReal_le_ofReal_iff (M.gnorm_nonneg _ _)).mp hed
  -- Part 2: Lower bound `M.gnorm p v ≤ dist (φ.symm p) (φ.symm q)` via regularized Gauss Lemma
  have hlower : M.gnorm p v ≤ dist (φ.symm p) (φ.symm q) := by
    by_contra hlt
    push Not at hlt
    let L' : ℝ := (dist (φ.symm p) (φ.symm q) + M.gnorm p v) / 2
    have hL'_gt : dist (φ.symm p) (φ.symm q) < L' := by dsimp [L']; linarith
    have hL'_lt : L' < M.gnorm p v := by dsimp [L']; linarith
    have hL'_pos : 0 < L' := lt_of_le_of_lt dist_nonneg hL'_gt
    have hed_lt : riemannianEDist (𝓡 n) (φ.symm p) (φ.symm q) < ENNReal.ofReal L' := by
      rw [← hRM.out, edist_dist]
      exact ENNReal.ofReal_lt_ofReal_iff hL'_pos |>.mpr hL'_gt
    obtain ⟨γ, hγ0, hγ1, hγ_cmd_glob, hγ_len, -, -⟩ :=
      exists_lt_locally_constant_of_riemannianEDist_lt hed_lt zero_lt_one
    have hγ_cmd : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc 0 1) := hγ_cmd_glob.contMDiffOn
    -- Define the normal ball `V_p = exp p '' {w | M.gnorm p w < ρ_0}` in coordinates and `W_p = φ.symm '' V_p` in `X`
    let V_p : Set (Euc n) := M.exp p '' {w : Euc n | M.gnorm p w < ρ_0}
    let W_p : Set X := φ.symm '' V_p
    have hVp_sub : V_p ⊆ ball M.a₀ r_m := by
      rintro y ⟨w, hw, rfl⟩; exact (hball_exp p hp w hw).2.1
    have hVp_open : IsOpen V_p := by
      rw [isOpen_iff_mem_nhds]
      rintro y ⟨w, hw, rfl⟩
      obtain ⟨_, _, htgt_y, hlog_y, _, _⟩ := hball_exp p hp w hw
      have hcont_log : ContinuousAt (fun z : Euc n => M.gnorm p (M.log p z)) (M.exp p w) := by
        have h1 : ContinuousAt (fun z : Euc n => M.log p z) (M.exp p w) :=
          continuous_snd.continuousAt.comp
            ((M.EHomeo.continuousAt_symm htgt_y).comp (continuousAt_const.prodMk continuousAt_id))
        have h2 : Continuous (fun u : Euc n => M.gnorm p u) := by
          refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_)
          exact (continuous_const.mul (EuclideanSpace.proj i).continuous).mul (EuclideanSpace.proj j).continuous
        exact h2.continuousAt.comp h1
      have hnhds1 : (fun z : Euc n => (p, z)) ⁻¹' M.EHomeo.target ∈ 𝓝 (M.exp p w) :=
        (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds (M.EHomeo.open_target.mem_nhds htgt_y)
      have hnhds2 : (fun z : Euc n => M.gnorm p (M.log p z)) ⁻¹' Iio ρ_0 ∈ 𝓝 (M.exp p w) :=
        hcont_log.preimage_mem_nhds (isOpen_Iio.mem_nhds (by rwa [hlog_y]))
      filter_upwards [Filter.inter_mem hnhds1 hnhds2] with z ⟨hz_tgt, hz_gn⟩
      have hfst : (M.EHomeo.symm (p, z)).1 = p := congrArg Prod.fst (M.EHomeo.right_inv hz_tgt)
      have hexp_z : M.exp p (M.log p z) = z := by
        have h1 := M.EHomeo.right_inv hz_tgt
        have h2 : M.EHomeo.symm (p, z) = (p, M.log p z) := Prod.ext hfst rfl
        rw [h2] at h1
        exact congrArg Prod.snd h1
      exact ⟨M.log p z, hz_gn, hexp_z⟩
    have hWp_open : IsOpen W_p := by
      have hsub_tgt : V_p ⊆ φ.target := hVp_sub.trans ((Metric.ball_subset_ball hrm_lt.le).trans htgt)
      have heq : W_p = φ.source ∩ φ ⁻¹' V_p := by
        ext x; constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨φ.map_target (hsub_tgt hy), by simpa [φ.right_inv (hsub_tgt hy)] using hy⟩
        · rintro ⟨hx, hφx⟩
          exact ⟨φ x, hφx, φ.left_inv hx⟩
      rw [heq]
      exact φ.continuousOn_toFun.isOpen_inter_preimage φ.open_source hVp_open
    -- Key radial-speed bound on any `[0, b] ⊆ [0, 1]` where `γ(t) ∈ W_p` for all `t ∈ [0, b]`!
    have hradial_bound : ∀ b ∈ Icc (0 : ℝ) 1, (∀ t ∈ Icc (0 : ℝ) b, γ t ∈ W_p) →
        M.gnorm p (M.log p (φ (γ b))) ≤ L' := by
      intro b hb hγ_in
      rcases hb.1.eq_or_lt with rfl | hb_pos
      · have hφ0 : φ (γ 0) = p := by rw [hγ0]; exact φ.right_inv (htgt hp_r1)
        have hlog_pp : M.log p p = 0 := by
          have h1 := (hball_exp p hp 0 (by simpa [M.gnorm_zero] using hρ_0)).2.2.2.1
          have h0 : M.exp p 0 = p := by
            have htgt0 := (hrg p hp_rg 0 (mem_ball_self hr_g)).1
            have hU0 := (hrg p hp_rg 0 (mem_ball_self hr_g)).2.1
            have hhom := M.geod_homog htgt0 hU0 (left_mem_Icc.mpr zero_le_one)
              ((hrg p hp_rg 0 (mem_ball_self hr_g)).2.2.2.1 0 (left_mem_Icc.mpr zero_le_one))
            simpa [M.γExt_zero] using hhom
          rwa [h0] at h1
        rw [hφ0, hlog_pp, M.gnorm_zero]; exact hL'_pos.le
      let η : ℝ → Euc n := φ ∘ γ
      have hη_in_Vp : ∀ t ∈ Icc (0 : ℝ) b, η t ∈ V_p := fun t ht => by
        obtain ⟨y, hy, hxy⟩ := hγ_in t ht
        have hy_tgt : y ∈ φ.target := htgt (Metric.ball_subset_ball hrm_lt.le (hVp_sub hy))
        change φ (γ t) ∈ V_p; rw [← hxy, φ.right_inv hy_tgt]; exact hy
      have hη_ball : ∀ t ∈ Icc (0 : ℝ) b, η t ∈ ball M.a₀ M.r₁ := fun t ht =>
        Metric.ball_subset_ball hrm_lt.le (hVp_sub (hη_in_Vp t ht))
      have hγ_src : ∀ t ∈ Icc (0 : ℝ) b, γ t ∈ φ.source := fun t ht => by
        obtain ⟨y, hy, hxy⟩ := hγ_in t ht
        rw [← hxy]; exact φ.map_target (htgt (Metric.ball_subset_ball hrm_lt.le (hVp_sub hy)))
      have hη_cd : ContDiffOn ℝ 1 η (Icc 0 b) := by
        rw [← contMDiffOn_iff_contDiffOn]
        exact (contMDiffOn_extChartAt (I := 𝓡 n) (x := x₀)).comp
          (hγ_cmd.mono (Icc_subset_Icc_right hb.2)) fun t ht => by simpa [extChartAt_source] using hγ_src t ht
      let u : ℝ → Euc n := fun t => M.log p (η t)
      have hu_prop : ∀ t ∈ Icc (0 : ℝ) b, M.gnorm p (u t) < ρ_0 ∧ M.exp p (u t) = η t ∧
          (∃ LE : (Euc n × Euc n) ≃L[ℝ] (Euc n × Euc n),
            HasStrictFDerivAt M.EHomeo.symm (LE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) (p, η t)) := by
        intro t ht
        obtain ⟨w, hw, hwy⟩ := hη_in_Vp t ht
        obtain ⟨_, _, _, hlog_w, hsymm_w, _⟩ := hball_exp p hp w hw
        have huw : u t = w := by simp only [u, ← hwy, hlog_w]
        rw [huw]; exact ⟨hw, hwy, by rwa [hwy] at hsymm_w⟩
      -- Show `u` has derivative within `Icc 0 b` at every `t ∈ Icc 0 b` and satisfies `fderiv (exp p) (u t) (u' t) = η' t`
      have hu_deriv : ∀ t ∈ Icc (0 : ℝ) b, ∃ u' : Euc n,
          HasDerivWithinAt u u' (Icc 0 b) t ∧
          fderiv ℝ (M.exp p) (u t) u' = derivWithin η (Icc 0 b) t := by
        intro t ht
        obtain ⟨hu_gn, hu_exp, LE, hLE⟩ := hu_prop t ht
        have hη_d : HasDerivWithinAt η (derivWithin η (Icc 0 b) t) (Icc 0 b) t :=
          (hη_cd.differentiableOn one_ne_zero t ht).hasDerivWithinAt
        have hpair_d : HasDerivWithinAt (fun s => (p, η s)) ((0 : Euc n), derivWithin η (Icc 0 b) t) (Icc 0 b) t :=
          (hasDerivWithinAt_const t (Icc 0 b) p).prodMk hη_d
        have hlog_fd : HasFDerivAt (fun y : Euc n => M.log p y)
            ((ContinuousLinearMap.snd ℝ (Euc n) (Euc n)).comp
              ((LE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)).comp
                (ContinuousLinearMap.inr ℝ (Euc n) (Euc n)))) (η t) := by
          have h1 := hLE.hasFDerivAt.comp (η t)
            ((hasFDerivAt_const p (η t)).prodMk (hasFDerivAt_id (η t)))
          have h2 := (ContinuousLinearMap.snd ℝ (Euc n) (Euc n)).hasFDerivAt.comp (η t) h1
          have hL : ((ContinuousLinearMap.snd ℝ (Euc n) (Euc n)).comp
              ((LE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)).comp
                ((0 : Euc n →L[ℝ] Euc n).prod (ContinuousLinearMap.id ℝ (Euc n))))) =
              ((ContinuousLinearMap.snd ℝ (Euc n) (Euc n)).comp
                ((LE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)).comp
                  (ContinuousLinearMap.inr ℝ (Euc n) (Euc n)))) :=
            ContinuousLinearMap.ext fun _ => rfl
          rwa [hL] at h2
        let u' : Euc n := (LE.symm (0, derivWithin η (Icc 0 b) t)).2
        have hud : HasDerivWithinAt u u' (Icc 0 b) t := hlog_fd.comp_hasDerivWithinAt t hη_d
        refine ⟨u', hud, ?_⟩
        have hu_re : u t ∈ ball (0 : Euc n) r_e := (hball_exp p hp (u t) hu_gn).1
        have hu_rg : u t ∈ ball (0 : Euc n) r_g := Metric.ball_subset_ball (hre_rm.trans hrm_rg) hu_re
        have hexp_fd : HasFDerivAt (M.exp p) (fderiv ℝ (M.exp p) (u t)) (u t) :=
          (M.gauss_lemma hrg hp_rg hu_rg u').1.hasFDerivAt
        have hcomp_d : HasDerivWithinAt (fun s => M.exp p (u s)) (fderiv ℝ (M.exp p) (u t) u') (Icc 0 b) t :=
          hexp_fd.comp_hasDerivWithinAt t hud
        have hcomp_eq : HasDerivWithinAt η (fderiv ℝ (M.exp p) (u t) u') (Icc 0 b) t :=
          hcomp_d.congr (fun s hs => (hu_prop s hs).2.1.symm) (hu_exp.symm)
        exact (uniqueDiffOn_Icc hb_pos t ht).eq_deriv _ hcomp_eq hη_d
      -- Regularized radial function `ρ_ε(t) = √(M.inner p (u t) (u t) + ε^2)` for any `ε > 0`
      suffices hε_bd : ∀ ε > 0, M.gnorm p (u b) ≤ L' + ε by
        by_contra hgt; push Not at hgt
        change L' < M.gnorm p (u b) at hgt
        have h1 := hε_bd ((M.gnorm p (u b) - L') / 2) (by linarith)
        linarith
      intro ε hε
      let fε : ℝ → ℝ := fun t => Real.sqrt (M.inner p (u t) (u t) + ε ^ 2)
      -- Show `fε b - fε 0 ≤ ∫ t in (0 : ℝ)..b, M.gnorm (η t) (derivWithin η (Icc 0 b) t)`
      have hfε_deriv : ∀ t ∈ Icc (0 : ℝ) b, ∃ d : ℝ,
          HasDerivWithinAt fε d (Icc 0 b) t ∧ d ≤ M.gnorm (η t) (derivWithin η (Icc 0 b) t) := by
        intro t ht
        obtain ⟨u', hu', hexp_u'⟩ := hu_deriv t ht
        obtain ⟨hu_gn, hu_exp, _⟩ := hu_prop t ht
        have hu_re : u t ∈ ball (0 : Euc n) r_e := (hball_exp p hp (u t) hu_gn).1
        have hu_rg : u t ∈ ball (0 : Euc n) r_g := Metric.ball_subset_ball (hre_rm.trans hrm_rg) hu_re
        obtain ⟨_, hrad, hgauss⟩ := M.gauss_lemma hrg hp_rg hu_rg u'
        -- Derivative of `s ↦ M.inner p (u s) (u s) + ε^2` is `2 * M.inner p (u t) u'`
        have hinner_d : HasDerivWithinAt (fun s => M.inner p (u s) (u s) + ε ^ 2)
            (2 * M.inner p (u t) u') (Icc 0 b) t := by
          have hcoord : ∀ i : Fin n, HasDerivWithinAt (fun s => (u s).ofLp i) (u'.ofLp i) (Icc 0 b) t :=
            fun i => (EuclideanSpace.proj i : Euc n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t hu'
          have hsum : HasDerivWithinAt (fun s => M.inner p (u s) (u s))
              (∑ i, ∑ j, (M.g p i j * u'.ofLp i * (u t).ofLp j + M.g p i j * (u t).ofLp i * u'.ofLp j))
              (Icc 0 b) t := by
            refine HasDerivWithinAt.fun_sum fun i _ => HasDerivWithinAt.fun_sum fun j _ => ?_
            have h1 := ((hasDerivWithinAt_const t (Icc 0 b) (M.g p i j)).fun_mul (hcoord i)).fun_mul (hcoord j)
            refine h1.congr_deriv ?_; ring
          have hval : ∑ i, ∑ j, (M.g p i j * u'.ofLp i * (u t).ofLp j + M.g p i j * (u t).ofLp i * u'.ofLp j) =
              2 * M.inner p (u t) u' := by
            have h1 : ∑ i, ∑ j, (M.g p i j * u'.ofLp i * (u t).ofLp j + M.g p i j * (u t).ofLp i * u'.ofLp j) =
                M.inner p u' (u t) + M.inner p (u t) u' := by
              simp only [LocalMetric.inner, ← Finset.sum_add_distrib]
            rw [h1, M.inner_symm hp_r1 u' (u t)]; ring
          rw [hval] at hsum
          exact hsum.add_const (ε ^ 2)
        have hpos_arg : 0 < M.inner p (u t) (u t) + ε ^ 2 := by
          linarith [M.inner_nonneg hp_r1 (u t), sq_pos_of_pos hε]
        have hsqrt_d : HasDerivWithinAt fε ((2 * M.inner p (u t) u') / (2 * fε t)) (Icc 0 b) t :=
          hinner_d.sqrt hpos_arg.ne'
        refine ⟨(2 * M.inner p (u t) u') / (2 * fε t), hsqrt_d, ?_⟩
        -- Bound by Gauss's Lemma + Cauchy-Schwarz + constant speed!
        have hfε_pos : 0 < fε t := Real.sqrt_pos.mpr hpos_arg
        have hgn_le_fε : M.gnorm p (u t) ≤ fε t :=
          Real.sqrt_le_sqrt (by linarith [sq_nonneg ε])
        have hinner_eq_g : M.inner p (u t) u' =
            M.inner (η t) (M.ξExt p (u t) 1) (derivWithin η (Icc 0 b) t) := by
          rw [← hgauss, hrad, hu_exp, hexp_u']
        have hcs : M.inner p (u t) u' ≤ M.gnorm p (u t) * M.gnorm (η t) (derivWithin η (Icc 0 b) t) := by
          rw [hinner_eq_g]
          have h1 := (le_abs_self _).trans (M.inner_le_gnorm_mul (hη_ball t ht)
            (M.ξExt p (u t) 1) (derivWithin η (Icc 0 b) t))
          obtain ⟨htgt_u, hU_u, _, _, _⟩ := hrg p hp_rg (u t) hu_rg
          have hcs_u := M.geod_const_speed htgt_u hU_u (right_mem_Icc.mpr zero_le_one)
          rw [M.γExt_one htgt_u, hu_exp] at hcs_u
          have hgn_ξ : M.gnorm (η t) (M.ξExt p (u t) 1) = M.gnorm p (u t) := by
            simp only [LocalMetric.gnorm, hcs_u]
          rwa [hgn_ξ] at h1
        rw [div_le_iff₀ (by positivity : 0 < 2 * fε t)]
        calc 2 * M.inner p (u t) u'
            ≤ 2 * (M.gnorm p (u t) * M.gnorm (η t) (derivWithin η (Icc 0 b) t)) := by linarith
          _ ≤ 2 * (fε t * M.gnorm (η t) (derivWithin η (Icc 0 b) t)) := by
              gcongr; exact M.gnorm_nonneg _ _
          _ = M.gnorm (η t) (derivWithin η (Icc 0 b) t) * (2 * fε t) := by ring
      -- Integrate via `g(t) := ∫ s in 0..t, M.gnorm (η s) (derivWithin η (Icc 0 b) s)` and `monotoneOn_of_deriv_nonneg`!
      let spd : ℝ → ℝ := fun t => M.gnorm (η t) (derivWithin η (Icc 0 b) t)
      have hspd_cont : ContinuousOn spd (Icc 0 b) := by
        have hη'_cont : ContinuousOn (derivWithin η (Icc 0 b)) (Icc 0 b) :=
          ((contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hb_pos)).mp hη_cd).2
        refine Real.continuous_sqrt.comp_continuousOn ?_
        refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
        have hg_c : ContinuousOn (fun t => M.g (η t) i j) (Icc 0 b) :=
          (M.hg_smooth i j).continuousOn.comp hη_cd.continuousOn hη_ball
        have hvi : ContinuousOn (fun t => (derivWithin η (Icc 0 b) t).ofLp i) (Icc 0 b) :=
          (EuclideanSpace.proj i).continuous.comp_continuousOn hη'_cont
        have hvj : ContinuousOn (fun t => (derivWithin η (Icc 0 b) t).ofLp j) (Icc 0 b) :=
          (EuclideanSpace.proj j).continuous.comp_continuousOn hη'_cont
        exact (hg_c.mul hvi).mul hvj
      let spdExt : ℝ → ℝ := fun t => spd (Set.projIcc 0 b hb_pos.le t : ℝ)
      have hspdExt_cont : Continuous spdExt :=
        hspd_cont.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun t =>
          (Set.projIcc 0 b hb_pos.le t).2
      let G : ℝ → ℝ := fun t => (∫ s in (0 : ℝ)..t, spdExt s) - fε t
      have hG_mono : MonotoneOn G (Icc 0 b) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 b)
        · have h1 : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, spdExt s) (Icc 0 b) :=
            (continuous_iff_continuousAt.mpr fun t =>
              (intervalIntegral.integral_hasDerivAt_right (hspdExt_cont.intervalIntegrable 0 t)
                (hspdExt_cont.stronglyMeasurableAtFilter _ _) hspdExt_cont.continuousAt).continuousAt).continuousOn
          have h2 : ContinuousOn fε (Icc 0 b) := fun t ht =>
            let ⟨_, hd, _⟩ := hfε_deriv t ht; hd.continuousWithinAt
          exact h1.sub h2
        · intro t ht
          rw [interior_Icc] at ht
          have htI : t ∈ Icc (0 : ℝ) b := ⟨ht.1.le, ht.2.le⟩
          obtain ⟨d, hd, _⟩ := hfε_deriv t htI
          have hG_d : HasDerivAt G (spdExt t - d) t := by
            have h1 := intervalIntegral.integral_hasDerivAt_right (hspdExt_cont.intervalIntegrable 0 t)
              (hspdExt_cont.stronglyMeasurableAtFilter _ _) hspdExt_cont.continuousAt
            exact h1.sub ((hd.mono Ioo_subset_Icc_self).hasDerivAt (isOpen_Ioo.mem_nhds ht))
          exact hG_d.differentiableAt.differentiableWithinAt
        · intro t ht
          rw [interior_Icc] at ht
          have htI : t ∈ Icc (0 : ℝ) b := ⟨ht.1.le, ht.2.le⟩
          obtain ⟨d, hd, hd_le⟩ := hfε_deriv t htI
          have hG_d : HasDerivAt G (spdExt t - d) t := by
            have h1 := intervalIntegral.integral_hasDerivAt_right (hspdExt_cont.intervalIntegrable 0 t)
              (hspdExt_cont.stronglyMeasurableAtFilter _ _) hspdExt_cont.continuousAt
            exact h1.sub ((hd.mono Ioo_subset_Icc_self).hasDerivAt (isOpen_Ioo.mem_nhds ht))
          rw [hG_d.deriv]
          have hproj : spdExt t = spd t := by simp [spdExt, Set.projIcc_of_mem hb_pos.le htI]
          rw [hproj]; linarith
      have hG0b : G 0 ≤ G b := hG_mono (left_mem_Icc.mpr hb_pos.le) (right_mem_Icc.mpr hb_pos.le) hb_pos.le
      have hG0 : G 0 = -ε := by
        have hφ0 : φ (γ 0) = p := by rw [hγ0]; exact φ.right_inv (htgt hp_r1)
        have hu0 : u 0 = 0 := by
          change M.log p (φ (γ 0)) = 0; rw [hφ0]
          have h1 := (hball_exp p hp 0 (by simpa [M.gnorm_zero] using hρ_0)).2.2.2.1
          have h0 : M.exp p 0 = p := by
            have htgt0 := (hrg p hp_rg 0 (mem_ball_self hr_g)).1
            have hU0 := (hrg p hp_rg 0 (mem_ball_self hr_g)).2.1
            have hhom := M.geod_homog htgt0 hU0 (left_mem_Icc.mpr zero_le_one)
              ((hrg p hp_rg 0 (mem_ball_self hr_g)).2.2.2.1 0 (left_mem_Icc.mpr zero_le_one))
            simpa [M.γExt_zero] using hhom
          rwa [h0] at h1
        simp [G, fε, hu0, M.inner_zero_left, Real.sqrt_sq hε.le]
      -- Connect `∫ s in 0..b, spdExt s` to `pathELength (𝓡 n) γ 0 b ≤ pathELength (𝓡 n) γ 0 1 < ofReal L'`
      have hint_le_L' : ∫ s in (0 : ℝ)..b, spdExt s ≤ L' := by
        have hofReal : ENNReal.ofReal (∫ s in (0 : ℝ)..b, spdExt s) = pathELength (𝓡 n) γ 0 b := by
          have hcongr_γ : pathELength (𝓡 n) γ 0 b = pathELength (𝓡 n) (φ.symm ∘ η) 0 b := by
            refine pathELength_congr fun t ht => ?_
            exact (φ.left_inv (hγ_src t ht)).symm
          rw [hcongr_γ, pathELength_eq_lintegral_mfderivWithin_Icc]
          have h1 : ∀ t ∈ Icc (0 : ℝ) b,
              ‖mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) (φ.symm ∘ η) (Icc 0 b) t 1‖ₑ =
                ENNReal.ofReal (spdExt t) := fun t ht => by
            rw [chart_curve_enorm_eq x₀ M hMa htgt hinner hb_pos hη_cd hη_ball ht]
            simp [spdExt, spd, Set.projIcc_of_mem hb_pos.le ht]
          rw [setLIntegral_congr_fun measurableSet_Icc h1,
            ← ofReal_integral_eq_lintegral_ofReal (hspdExt_cont.integrableOn_Icc)
              (ae_restrict_of_forall_mem measurableSet_Icc fun t ht => by
                simp only [spdExt, spd, Set.projIcc_of_mem hb_pos.le ht]; exact M.gnorm_nonneg _ _),
            MeasureTheory.integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le hb_pos.le]
        have hle_e : ENNReal.ofReal (∫ s in (0 : ℝ)..b, spdExt s) ≤ ENNReal.ofReal L' := by
          rw [hofReal]
          exact (pathELength_mono le_rfl hb.2).trans hγ_len.le
        exact (ENNReal.ofReal_le_ofReal_iff hL'_pos.le).mp hle_e
      have hgn_le_fε : M.gnorm p (u b) ≤ fε b := Real.sqrt_le_sqrt (by linarith [sq_nonneg ε])
      dsimp [G] at hG0b
      linarith
    -- Step 2A: Show `∀ t ∈ Icc 0 1, γ t ∈ K_p ⊆ W_p` via `IsClosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset`!
    have hL'_lt_ρ : L' < ρ_0 := by linarith
    let B_L' : Set (Euc n) := {w : Euc n | M.gnorm p w ≤ L'}
    have hBL'_comp : IsCompact B_L' := by
      have hsub : B_L' ⊆ closedBall (0 : Euc n) (L' / m_g) := fun w hw => by
        rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hm_g, mul_comm]
        exact (hmbd p (Metric.ball_subset_closedBall hp_rm) w).1.trans hw
      have hclosed : IsClosed B_L' := by
        have hc : Continuous (fun w : Euc n => M.gnorm p w) := by
          refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_)
          exact (continuous_const.mul (EuclideanSpace.proj i).continuous).mul (EuclideanSpace.proj j).continuous
        exact isClosed_Iic.preimage hc
      exact (isCompact_closedBall (0 : Euc n) (L' / m_g)).of_isClosed_subset hclosed hsub
    let K_p : Set X := φ.symm '' (M.exp p '' B_L')
    have hKp_sub_Wp : K_p ⊆ W_p := by
      rintro x ⟨y, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨M.exp p w, ⟨w, lt_of_le_of_lt hw hL'_lt_ρ, rfl⟩, rfl⟩
    have hKp_closed : IsClosed K_p := by
      have hexp_cont : ContinuousOn (M.exp p) B_L' := fun w hw => by
        have hw_ρ : M.gnorm p w < ρ_0 := lt_of_le_of_lt hw hL'_lt_ρ
        have hw_re : w ∈ ball (0 : Euc n) r_e := (hball_exp p hp w hw_ρ).1
        have hw_rg : w ∈ ball (0 : Euc n) r_g := Metric.ball_subset_ball (hre_rm.trans hrm_rg) hw_re
        exact (M.gauss_lemma hrg hp_rg hw_rg 0).1.continuousAt.continuousWithinAt
      have hφs_cont : ContinuousOn φ.symm (M.exp p '' B_L') :=
        φ.continuousOn_invFun.mono fun y hy => by
          obtain ⟨w, hw, rfl⟩ := hy
          exact htgt (Metric.ball_subset_ball hrm_lt.le (hball_exp p hp w (lt_of_le_of_lt hw hL'_lt_ρ)).2.1)
      exact ((hBL'_comp.image_of_continuousOn hexp_cont).image_of_continuousOn hφs_cont).isClosed
    let A : Set ℝ := γ ⁻¹' K_p
    have h0_mem : 0 ∈ A := by
      show γ 0 ∈ K_p
      rw [hγ0]
      have h0 : M.exp p 0 = p := by
        have htgt0 := (hrg p hp_rg 0 (mem_ball_self hr_g)).1
        have hU0 := (hrg p hp_rg 0 (mem_ball_self hr_g)).2.1
        have hhom := M.geod_homog htgt0 hU0 (left_mem_Icc.mpr zero_le_one)
          ((hrg p hp_rg 0 (mem_ball_self hr_g)).2.2.2.1 0 (left_mem_Icc.mpr zero_le_one))
        simpa [M.γExt_zero] using hhom
      exact ⟨p, ⟨0, by simp [B_L', M.gnorm_zero, hL'_pos.le], h0⟩, rfl⟩
    have hA_closed : IsClosed (A ∩ Icc 0 1) :=
      (hKp_closed.preimage hγ_cmd_glob.continuous).inter isClosed_Icc
    have hIcc_sub_A : Icc (0 : ℝ) 1 ⊆ A := by
      apply hA_closed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset h0_mem
      intro t₁ ht₁ ht₁_mem
      have hγt₁_W : γ t₁ ∈ W_p := hKp_sub_Wp (ht₁_mem (right_mem_Icc.mpr ht₁.1))
      have hnhds : γ ⁻¹' W_p ∈ 𝓝 t₁ :=
        hγ_cmd_glob.continuous.continuousAt.preimage_mem_nhds (hWp_open.mem_nhds hγt₁_W)
      obtain ⟨δ, hδ, hδ_sub⟩ := Metric.mem_nhds_iff.mp hnhds
      have hmem_gt : Ioo t₁ (min 1 (t₁ + δ)) ∈ 𝓝[>] t₁ :=
        Ioo_mem_nhdsGT (lt_min ht₁.2 (by linarith))
      filter_upwards [hmem_gt] with b hb
      have hb01 : b ∈ Icc (0 : ℝ) 1 := ⟨ht₁.1.trans hb.1.le, hb.2.le.trans (min_le_left _ _)⟩
      have hγ_in_b : ∀ t ∈ Icc (0 : ℝ) b, γ t ∈ W_p := fun t ht => by
        by_cases hle : t ≤ t₁
        · exact hKp_sub_Wp (ht₁_mem ⟨ht.1, hle⟩)
        · push Not at hle
          have hdist : dist t t₁ < δ := by
            rw [Real.dist_eq, abs_of_pos (by linarith)]
            have hb_lt : b < t₁ + δ := lt_of_lt_of_le hb.2 (min_le_right _ _)
            linarith [ht.2]
          exact hδ_sub hdist
      have hgn_le := hradial_bound b hb01 hγ_in_b
      -- Since `γ b ∈ W_p` and `M.gnorm p (M.log p (φ (γ b))) ≤ L'`, we get `γ b ∈ K_p`!
      obtain ⟨y, ⟨w, hw, rfl⟩, hxy⟩ := hγ_in_b b (right_mem_Icc.mpr hb01.1)
      have hy_tgt : M.exp p w ∈ φ.target := htgt (Metric.ball_subset_ball hrm_lt.le (hball_exp p hp w hw).2.1)
      have hφb : φ (γ b) = M.exp p w := by rw [← hxy, φ.right_inv hy_tgt]
      have hlog_b : M.log p (φ (γ b)) = w := by rw [hφb]; exact (hball_exp p hp w hw).2.2.2.1
      rw [hlog_b] at hgn_le
      exact ⟨M.exp p w, ⟨w, hgn_le, rfl⟩, hxy⟩
    -- Step 2B: Apply `hradial_bound` at `b = 1`!
    have hγ_all_in : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ W_p := fun t ht => hKp_sub_Wp (hIcc_sub_A ht)
    have hb1 := hradial_bound 1 (right_mem_Icc.mpr zero_le_one) hγ_all_in
    have hφ1 : φ (γ 1) = q := by
      rw [hγ1]; exact φ.right_inv (htgt (Metric.ball_subset_ball hrm_lt.le (Metric.ball_subset_ball (hrn_re.trans hre_rm) hq)))
    rw [hφ1] at hb1
    linarith
  exact le_antisymm hupper hlower

end PullbackMetric

end Hilbert5H1

-- Section 3: H1_M3_MainTheorem.lean
namespace Hilbert5H1

open Metric Set Filter Topology MeasureTheory Manifold intervalIntegral
open scoped Manifold ContDiff Bundle ENNReal RealInnerProductSpace Classical

section MainProof

/-- First derivative of `s ↦ dist(φ.symm (x₀ + s • h), φ.symm q)^2` along a segment inside `ball M.a₀ r_n`. -/
lemma sq_dist_hasDerivAt_line {n : ℕ} (hn : 0 < n) {X : Type} [MetricSpace X]
    [ChartedSpace (Euc n) X] [IsManifold (𝓡 n) ∞ X]
    [Bundle.RiemannianBundle (fun x : X => TangentSpace (𝓡 n) x)]
    [IsContMDiffRiemannianBundle (𝓡 n) ∞ (Euc n) (fun x : X => TangentSpace (𝓡 n) x)]
    [IsRiemannianManifold (𝓡 n) X]
    (x₀ : X) (M : LocalMetric n)
    (hMa : M.a₀ = chartAt (Euc n) x₀ x₀)
    (htgt : ball M.a₀ M.r₁ ⊆ (chartAt (Euc n) x₀).target)
    (hinner : ∀ y ∈ ball M.a₀ M.r₁, ∀ u v : Euc n,
      M.inner y u v =
        ⟪(trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ ((chartAt (Euc n) x₀).symm y) u,
         (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ ((chartAt (Euc n) x₀).symm y) v⟫)
    {r_g r_m r_e r_n ρ_0 m_g M_g : ℝ}
    (hr_g : 0 < r_g) (hr_m : 0 < r_m) (hr_e : 0 < r_e) (hr_n : 0 < r_n) (hρ_0 : 0 < ρ_0)
    (hrm_lt : r_m < M.r₁) (hrn_re : r_n ≤ r_e) (hre_rm : r_e ≤ r_m) (hrm_rg : r_m ≤ r_g)
    (hm_g : 0 < m_g)
    (hmbd : ∀ y ∈ closedBall M.a₀ r_m, ∀ w : Euc n, m_g * ‖w‖ ≤ M.gnorm y w ∧ M.gnorm y w ≤ M_g * ‖w‖)
    (hrg : ∀ p ∈ ball M.a₀ r_g, ∀ v ∈ ball (0 : Euc n) r_g,
      constPairL (p, v) ∈ M.psiHomeo.target ∧
      M.geod p v ∈ M.U_V ∧
      (∃ L : PathPair n ≃L[ℝ] PathPair n,
        (L : PathPair n →L[ℝ] PathPair n) = M.dpsi (M.geod p v) ∧
        HasStrictFDerivAt M.psiHomeo.symm (L.symm : PathPair n →L[ℝ] PathPair n) (constPairL (p, v))) ∧
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1), LocalMetric.scalePath (M.geod p v) s hs ∈ M.psiHomeo.source) ∧
      LocalMetric.revPath (M.geod p v) ∈ M.psiHomeo.source)
    (hball_exp : ∀ p ∈ ball M.a₀ r_n, ∀ v : Euc n, M.gnorm p v < ρ_0 →
      v ∈ ball (0 : Euc n) r_e ∧
      M.exp p v ∈ ball M.a₀ r_m ∧
      (p, M.exp p v) ∈ M.EHomeo.target ∧
      M.log p (M.exp p v) = v ∧
      (∃ LE : (Euc n × Euc n) ≃L[ℝ] (Euc n × Euc n),
        HasStrictFDerivAt M.EHomeo.symm (LE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) (p, M.exp p v)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, M.γExt p v t ∈ ball M.a₀ r_m)
    (hball_log : ∀ p ∈ ball M.a₀ r_n, ∀ q ∈ ball M.a₀ r_n,
      (p, q) ∈ M.EHomeo.target ∧
      M.log p q ∈ ball (0 : Euc n) r_e ∧
      M.gnorm p (M.log p q) < ρ_0 / 2 ∧
      M.exp p (M.log p q) = q ∧
      M.ξExt q (M.log q p) 1 = -M.log p q ∧
      ∃ LE : (Euc n × Euc n) ≃L[ℝ] (Euc n × Euc n),
        HasStrictFDerivAt M.EHomeo.symm (LE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) (p, q))
    {q x h : Euc n} {t : ℝ} (hq : q ∈ ball M.a₀ r_n) (hpt : x + t • h ∈ ball M.a₀ r_n) :
    HasDerivAt (fun s : ℝ => dist ((chartAt (Euc n) x₀).symm (x + s • h)) ((chartAt (Euc n) x₀).symm q) ^ 2)
      (-2 * M.inner (x + t • h) (M.log (x + t • h) q) h) t := by
  let p : Euc n := x + t • h
  have hp : p ∈ ball M.a₀ r_n := hpt
  have hq_rm : q ∈ ball M.a₀ r_m := Metric.ball_subset_ball (hrn_re.trans hre_rm) hq
  have hq_r1 : q ∈ ball M.a₀ M.r₁ := Metric.ball_subset_ball hrm_lt.le hq_rm
  have hq_rg : q ∈ ball M.a₀ r_g := Metric.ball_subset_ball hrm_rg hq_rm
  obtain ⟨_, hlog_qp_re, _, hexp_qp, _, LE, hLE⟩ := hball_log q hq p hp
  have hrev_qp : M.ξExt q (M.log q p) 1 = -M.log p q := (hball_log p hp q hq).2.2.2.2.1
  have hline : HasDerivAt (fun s : ℝ => x + s • h) h t := by
    have h1 := (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const h)
    rwa [one_smul, zero_add] at h1
  have hlog_fd : HasFDerivAt (fun y : Euc n => M.log q y)
      ((ContinuousLinearMap.snd ℝ (Euc n) (Euc n)).comp
        ((LE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)).comp
          (ContinuousLinearMap.inr ℝ (Euc n) (Euc n)))) p := by
    have h1 := hLE.hasFDerivAt.comp p ((hasFDerivAt_const q p).prodMk (hasFDerivAt_id p))
    have h2 := (ContinuousLinearMap.snd ℝ (Euc n) (Euc n)).hasFDerivAt.comp p h1
    have hL : ((ContinuousLinearMap.snd ℝ (Euc n) (Euc n)).comp
        ((LE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)).comp
          ((0 : Euc n →L[ℝ] Euc n).prod (ContinuousLinearMap.id ℝ (Euc n))))) =
        ((ContinuousLinearMap.snd ℝ (Euc n) (Euc n)).comp
          ((LE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)).comp
            (ContinuousLinearMap.inr ℝ (Euc n) (Euc n)))) :=
      ContinuousLinearMap.ext fun _ => rfl
    rwa [hL] at h2
  let u' : Euc n := (LE.symm (0, h)).2
  have hu_d : HasDerivAt (fun s : ℝ => M.log q (x + s • h)) u' t := by
    simpa [Function.comp_def] using hlog_fd.comp_hasDerivAt t hline
  have hv_rg : M.log q p ∈ ball (0 : Euc n) r_g := Metric.ball_subset_ball (hre_rm.trans hrm_rg) hlog_qp_re
  obtain ⟨hexp_sfd, hrad, hgauss⟩ := M.gauss_lemma hrg hq_rg hv_rg u'
  have hexp_u' : fderiv ℝ (M.exp q) (M.log q p) u' = h := by
    have hcomp_d : HasDerivAt (fun s : ℝ => M.exp q (M.log q (x + s • h)))
        (fderiv ℝ (M.exp q) (M.log q p) u') t := by
      simpa [Function.comp_def] using hexp_sfd.hasFDerivAt.comp_hasDerivAt t hu_d
    have hev : (fun s : ℝ => M.exp q (M.log q (x + s • h))) =ᶠ[𝓝 t] (fun s : ℝ => x + s • h) := by
      have hmem : (fun s : ℝ => x + s • h) ⁻¹' ball M.a₀ r_n ∈ 𝓝 t :=
        hline.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hp)
      filter_upwards [hmem] with s hs
      exact (hball_log q hq (x + s • h) hs).2.2.2.1
    exact (hcomp_d.congr_of_eventuallyEq hev.symm).unique hline
  have hinner_d : HasDerivAt (fun s : ℝ => M.inner q (M.log q (x + s • h)) (M.log q (x + s • h)))
      (2 * M.inner q (M.log q p) u') t := by
    have hcoord : ∀ i : Fin n, HasDerivAt (fun s => (M.log q (x + s • h)).ofLp i) (u'.ofLp i) t :=
      fun i => (EuclideanSpace.proj i : Euc n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hu_d
    have hsum : HasDerivAt (fun s => M.inner q (M.log q (x + s • h)) (M.log q (x + s • h)))
        (∑ i, ∑ j, (M.g q i j * u'.ofLp i * (M.log q p).ofLp j +
          M.g q i j * (M.log q p).ofLp i * u'.ofLp j)) t := by
      refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
      have h1 := ((hasDerivAt_const t (M.g q i j)).fun_mul (hcoord i)).fun_mul (hcoord j)
      refine h1.congr_deriv ?_; ring
    have hval : ∑ i, ∑ j, (M.g q i j * u'.ofLp i * (M.log q p).ofLp j +
          M.g q i j * (M.log q p).ofLp i * u'.ofLp j) = 2 * M.inner q (M.log q p) u' := by
      have h1 : ∑ i, ∑ j, (M.g q i j * u'.ofLp i * (M.log q p).ofLp j +
            M.g q i j * (M.log q p).ofLp i * u'.ofLp j) =
          M.inner q u' (M.log q p) + M.inner q (M.log q p) u' := by
        simp only [LocalMetric.inner, ← Finset.sum_add_distrib]
      rw [h1, M.inner_symm hq_r1 u' (M.log q p)]; ring
    rwa [hval] at hsum
  have hval_eq : 2 * M.inner q (M.log q p) u' = -2 * M.inner p (M.log p q) h := by
    rw [← hgauss, hrad, hexp_qp, hexp_u', hrev_qp, M.inner_neg_left]; ring
  rw [hval_eq] at hinner_d
  have hev_F : (fun s : ℝ => dist ((chartAt (Euc n) x₀).symm (x + s • h)) ((chartAt (Euc n) x₀).symm q) ^ 2) =ᶠ[𝓝 t]
      (fun s : ℝ => M.inner q (M.log q (x + s • h)) (M.log q (x + s • h))) := by
    have hmem : (fun s : ℝ => x + s • h) ⁻¹' ball M.a₀ r_n ∈ 𝓝 t :=
      hline.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hp)
    filter_upwards [hmem] with s hs
    rw [dist_comm, dist_eq_gnorm_log hn x₀ M hMa htgt hinner hr_g hr_m hr_e hr_n hρ_0
      hrm_lt hrn_re hre_rm hrm_rg hm_g hmbd hrg hball_exp hball_log hq hs,
      M.gnorm_sq hq_r1]
  exact hinner_d.congr_of_eventuallyEq hev_F

/-- Proof of `H1` in dimension `n = 0`. -/
lemma h1_zero (X : Type) [MetricSpace X] [ConnectedSpace X]
    [ChartedSpace (Euc 0) X] :
    ∃ (k : ℕ) (p : Fin (k + 1) → X) (R c : Fin (k + 1) → ℝ) (δ : ℝ),
      (∀ i, 0 < R i) ∧ (∀ i, 0 < c i) ∧ 0 < δ ∧
      (∀ i, IsCompact (Metric.closedBall (p i) (R i))) ∧
      (∀ i, ∀ x ∈ Metric.closedBall (p i) (R i), ∀ y ∈ Metric.closedBall (p i) (R i),
        ∃ m : X, ∀ z ∈ Metric.closedBall (p i) (R i),
          (dist m z) ^ 2 ≤ ((dist x z) ^ 2 + (dist y z) ^ 2) / 2 - c i * (dist x y) ^ 2) ∧
      (∀ q : Fin (k + 1) → X, (∀ i, q i ∈ Metric.closedBall (p i) (R i)) →
        Set.InjOn (fun x : X ↦ fun i : Fin (k + 1) ↦ dist x (q i)) (Metric.ball (q 0) δ)) := by
  obtain ⟨x₀⟩ := ‹ConnectedSpace X›.toNonempty
  have hsub : ∀ x : X, x = x₀ := by
    have hopen : IsOpen ({x₀} : Set X) := by
      have heq : (chartAt (Euc 0) x₀).source = {x₀} := by
        ext x; constructor
        · intro hx
          have h1 : chartAt (Euc 0) x₀ x = chartAt (Euc 0) x₀ x₀ := Subsingleton.elim _ _
          exact (chartAt (Euc 0) x₀).injOn hx (mem_chart_source (Euc 0) x₀) h1
        · rintro rfl; exact mem_chart_source (Euc 0) _
      rw [← heq]; exact (chartAt (Euc 0) x₀).open_source
    have huniv : ({x₀} : Set X) = univ := IsClopen.eq_univ ⟨isClosed_singleton, hopen⟩ ⟨x₀, rfl⟩
    intro x
    have hx : x ∈ ({x₀} : Set X) := by rw [huniv]; trivial
    exact hx
  refine ⟨0, fun _ => x₀, fun _ => 1, fun _ => 1, 1,
    fun _ => zero_lt_one, fun _ => zero_lt_one, zero_lt_one, ?_, ?_, ?_⟩
  · intro _
    have heq : closedBall x₀ (1 : ℝ) = {x₀} := by
      ext x; simp [hsub x]
    rw [heq]; exact isCompact_singleton
  · intro _ x _ y _
    refine ⟨x₀, fun z _ => ?_⟩
    rw [hsub x, hsub y, hsub z]; simp
  · intro q _ x _ y _ _
    rw [hsub x, hsub y]

set_option maxHeartbeats 1200000 in
/-- Proof of `H1` in dimension `n ≥ 1`. -/
lemma h1_pos {n : ℕ} (hn : 0 < n) (X : Type) [MetricSpace X] [ConnectedSpace X]
    [ChartedSpace (Euc n) X] [IsManifold (𝓡 n) ∞ X]
    [Bundle.RiemannianBundle (fun x : X => TangentSpace (𝓡 n) x)]
    [IsContMDiffRiemannianBundle (𝓡 n) ∞ (Euc n) (fun x : X => TangentSpace (𝓡 n) x)]
    [IsRiemannianManifold (𝓡 n) X] :
    ∃ (k : ℕ) (p : Fin (k + 1) → X) (R c : Fin (k + 1) → ℝ) (δ : ℝ),
      (∀ i, 0 < R i) ∧ (∀ i, 0 < c i) ∧ 0 < δ ∧
      (∀ i, IsCompact (Metric.closedBall (p i) (R i))) ∧
      (∀ i, ∀ x ∈ Metric.closedBall (p i) (R i), ∀ y ∈ Metric.closedBall (p i) (R i),
        ∃ m : X, ∀ z ∈ Metric.closedBall (p i) (R i),
          (dist m z) ^ 2 ≤ ((dist x z) ^ 2 + (dist y z) ^ 2) / 2 - c i * (dist x y) ^ 2) ∧
      (∀ q : Fin (k + 1) → X, (∀ i, q i ∈ Metric.closedBall (p i) (R i)) →
        Set.InjOn (fun x : X ↦ fun i : Fin (k + 1) ↦ dist x (q i)) (Metric.ball (q 0) δ)) := by
  obtain ⟨x₀⟩ := ‹ConnectedSpace X›.toNonempty
  let φ := chartAt (Euc n) x₀
  obtain ⟨r₁, hr₁, hr₁_tgt, hg_sm, hg_symm, hinner_eq, hg_pos⟩ := pullback_metric_exists (n := n) x₀
  let M : LocalMetric n :=
    { a₀ := φ x₀
      r₁ := r₁
      hr₁ := hr₁
      g := fun y i j =>
        ⟪(trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm y) (LocalMetric.e i),
         (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm y) (LocalMetric.e j)⟫
      hg_smooth := hg_sm
      hg_symm := hg_symm
      hg_pos := hg_pos }
  obtain ⟨r_g, r_m, r_e, r_n, ρ_0, m_g, M_g, L_g,
    hr_g, hr_m, hr_e, hr_n, hρ_0, hm_g, hM_g, hL_g,
    hrm_lt, hrn_re, hre_rm, hrm_rg, hmbd, hmlip, hrg, _, hball_exp, hball_log⟩ :=
    M.exists_normal_package hn
  have hinner_M : ∀ y ∈ ball M.a₀ M.r₁, ∀ u v : Euc n,
      M.inner y u v =
        ⟪(trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm y) u,
         (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm y) v⟫ := hinner_eq
  -- Helper: `M.log p p = 0` for `p ∈ ball M.a₀ r_n`
  have hlog_diag : ∀ p ∈ ball M.a₀ r_n, M.log p p = 0 := fun p hp => by
    have hp_rg : p ∈ ball M.a₀ r_g := Metric.ball_subset_ball ((hrn_re.trans hre_rm).trans hrm_rg) hp
    have h1 := (hball_exp p hp 0 (by simpa [M.gnorm_zero] using hρ_0)).2.2.2.1
    have h0 : M.exp p 0 = p := by
      have htgt0 := (hrg p hp_rg 0 (mem_ball_self hr_g)).1
      have hU0 := (hrg p hp_rg 0 (mem_ball_self hr_g)).2.1
      have hhom := M.geod_homog htgt0 hU0 (left_mem_Icc.mpr zero_le_one)
        ((hrg p hp_rg 0 (mem_ball_self hr_g)).2.2.2.1 0 (left_mem_Icc.mpr zero_le_one))
      simpa [M.γExt_zero] using hhom
    rwa [h0] at h1
  -- Strict differentiability of `log` at `(M.a₀, M.a₀)`
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  let ε : ℝ := min (1 / 2) (m_g ^ 2 / (32 * (M_g ^ 2 + 1) * (n : ℝ)))
  have hε_pos : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε_half : ε ≤ 1 / 2 := min_le_left _ _
  have hε_small : ε ≤ m_g ^ 2 / (32 * (M_g ^ 2 + 1) * (n : ℝ)) := min_le_right _ _
  have hlo := (hasStrictFDerivAt_iff_isLittleO.mp M.log_hasStrictFDerivAt_diag).bound hε_pos
  obtain ⟨r_s, hr_s, hrs_sub⟩ := Metric.mem_nhds_iff.mp hlo
  let ρ : ℝ := min (min r_n r_s) (m_g ^ 2 / (32 * (L_g + 1)))
  have hρ_pos : 0 < ρ := lt_min (lt_min hr_n hr_s) (by positivity)
  have hρ_rn : ρ ≤ r_n := (min_le_left _ _).trans (min_le_left _ _)
  have hρ_rs : ρ ≤ r_s := (min_le_left _ _).trans (min_le_right _ _)
  have hρ_Lg : 16 * L_g * ρ ≤ m_g ^ 2 / 2 := by
    have h1 : ρ ≤ m_g ^ 2 / (32 * (L_g + 1)) := min_le_right _ _
    have h2 : 0 < L_g + 1 := by linarith
    calc 16 * L_g * ρ ≤ 16 * (L_g + 1) * (m_g ^ 2 / (32 * (L_g + 1))) :=
          mul_le_mul (by linarith) h1 hρ_pos.le (by positivity)
      _ = m_g ^ 2 / 2 := by field_simp [h2.ne']; ring
  have hρ_rm : ρ ≤ r_m := hρ_rn.trans (hrn_re.trans hre_rm)
  have hlog_approx : ∀ p₁ ∈ ball M.a₀ ρ, ∀ p₂ ∈ ball M.a₀ ρ, ∀ q₁ ∈ ball M.a₀ ρ, ∀ q₂ ∈ ball M.a₀ ρ,
      ‖(M.log p₁ q₁ - M.log p₂ q₂) - ((q₁ - p₁) - (q₂ - p₂))‖ ≤ ε * max ‖p₁ - p₂‖ ‖q₁ - q₂‖ := by
    intro p₁ hp₁ p₂ hp₂ q₁ hq₁ q₂ hq₂
    have hmem : ((p₁, q₁), (p₂, q₂)) ∈ ball ((M.a₀, M.a₀), (M.a₀, M.a₀)) r_s := by
      rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
      exact max_lt (max_lt (Metric.ball_subset_ball hρ_rs hp₁) (Metric.ball_subset_ball hρ_rs hq₁))
        (max_lt (Metric.ball_subset_ball hρ_rs hp₂) (Metric.ball_subset_ball hρ_rs hq₂))
    have h1 := hrs_sub hmem
    simpa [Prod.norm_def, sub_sub_sub_comm] using h1
  have hlog_bd : ∀ p ∈ ball M.a₀ ρ, ∀ q ∈ ball M.a₀ ρ, ‖M.log p q‖ ≤ 2 * ‖q - p‖ := by
    intro p hp q hq
    have h1 := hlog_approx p hp p hp q hq p hp
    rw [hlog_diag p (Metric.ball_subset_ball hρ_rn hp), sub_zero, sub_self, sub_zero,
      norm_zero, max_eq_right (norm_nonneg _)] at h1
    have htri : ‖M.log p q‖ ≤ ‖M.log p q - (q - p)‖ + ‖q - p‖ := by
      simpa using norm_add_le (M.log p q - (q - p)) (q - p)
    linarith [mul_le_mul_of_nonneg_right hε_half (norm_nonneg (q - p)), norm_nonneg (q - p)]
  -- Helper: `M.inner y u v ≤ M_g^2 * ‖u‖ * ‖v‖` and `m_g^2 * ‖u‖^2 ≤ M.inner y u u` on `ball M.a₀ ρ`
  have hinner_ub : ∀ y ∈ ball M.a₀ ρ, ∀ u v : Euc n, |M.inner y u v| ≤ M_g ^ 2 * ‖u‖ * ‖v‖ := by
    intro y hy u v
    have hy_rm : y ∈ closedBall M.a₀ r_m := Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ_rm hy)
    have hy_r1 : y ∈ ball M.a₀ M.r₁ := Metric.ball_subset_ball (hρ_rm.trans hrm_lt.le) hy
    calc |M.inner y u v| ≤ M.gnorm y u * M.gnorm y v := M.inner_le_gnorm_mul hy_r1 u v
      _ ≤ (M_g * ‖u‖) * (M_g * ‖v‖) :=
          mul_le_mul (hmbd y hy_rm u).2 (hmbd y hy_rm v).2 (M.gnorm_nonneg _ _) (mul_nonneg hM_g.le (norm_nonneg _))
      _ = M_g ^ 2 * ‖u‖ * ‖v‖ := by ring
  have hinner_lb : ∀ y ∈ ball M.a₀ ρ, ∀ u : Euc n, m_g ^ 2 * ‖u‖ ^ 2 ≤ M.inner y u u := by
    intro y hy u
    have hy_rm : y ∈ closedBall M.a₀ r_m := Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ_rm hy)
    have hy_r1 : y ∈ ball M.a₀ M.r₁ := Metric.ball_subset_ball (hρ_rm.trans hrm_lt.le) hy
    have h1 := pow_le_pow_left₀ (mul_nonneg hm_g.le (norm_nonneg u)) (hmbd y hy_rm u).1 2
    rwa [mul_pow, M.gnorm_sq hy_r1] at h1
  -- (A) Strong convexity on `ball M.a₀ ρ` with `c₀ = m_g^2 / (32 * M_g^2)`
  let c₀ : ℝ := m_g ^ 2 / (32 * M_g ^ 2)
  have hc₀_pos : 0 < c₀ := by positivity
  have hstrong_conv : ∀ x ∈ ball M.a₀ ρ, ∀ y ∈ ball M.a₀ ρ, ∀ z ∈ ball M.a₀ ρ,
      let m := (1 / 2 : ℝ) • (x + y)
      dist (φ.symm m) (φ.symm z) ^ 2 ≤
        (dist (φ.symm x) (φ.symm z) ^ 2 + dist (φ.symm y) (φ.symm z) ^ 2) / 2 -
          c₀ * dist (φ.symm x) (φ.symm y) ^ 2 := by
    intro x hx y hy z hz m
    have hm_ball : m ∈ ball M.a₀ ρ := by
      have h1 : m = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y := by simp [m, smul_add]
      rw [h1]
      exact (convex_ball M.a₀ ρ) hx hy (by norm_num) (by norm_num) (by norm_num)
    let h : Euc n := y - x
    have hseg : ∀ s ∈ Icc (0 : ℝ) (1 / 2), m + s • h ∈ ball M.a₀ ρ ∧ m - s • h ∈ ball M.a₀ ρ := by
      intro s hs
      have h1 : m + s • h = (1 / 2 - s) • x + (1 / 2 + s) • y := by
        simp only [m, h, smul_add, smul_sub, sub_smul, add_smul]; abel
      have h2 : m - s • h = (1 / 2 + s) • x + (1 / 2 - s) • y := by
        simp only [m, h, smul_add, smul_sub, sub_smul, add_smul]; abel
      exact ⟨h1 ▸ (convex_ball M.a₀ ρ) hx hy (by linarith [hs.2]) (by linarith [hs.1]) (by ring),
             h2 ▸ (convex_ball M.a₀ ρ) hx hy (by linarith [hs.1]) (by linarith [hs.2]) (by ring)⟩
    let g : ℝ → ℝ := fun s => dist (φ.symm (m + s • h)) (φ.symm z) ^ 2 +
      dist (φ.symm (m - s • h)) (φ.symm z) ^ 2
    let g' : ℝ → ℝ := fun s => 2 * (M.inner (m - s • h) (M.log (m - s • h) z) h -
      M.inner (m + s • h) (M.log (m + s • h) z) h)
    have hg_deriv : ∀ s ∈ uIcc (0 : ℝ) (1 / 2), HasDerivAt g (g' s) s := by
      intro s hs
      rw [Set.uIcc_of_le (by norm_num)] at hs
      have h1 := sq_dist_hasDerivAt_line hn x₀ M rfl hr₁_tgt hinner_M
        hr_g hr_m hr_e hr_n hρ_0 hrm_lt hrn_re hre_rm hrm_rg hm_g hmbd hrg hball_exp hball_log
        (Metric.ball_subset_ball hρ_rn hz) (Metric.ball_subset_ball hρ_rn (hseg s hs).1) (x := m) (h := h) (t := s)
      have h2 := sq_dist_hasDerivAt_line hn x₀ M rfl hr₁_tgt hinner_M
        hr_g hr_m hr_e hr_n hρ_0 hrm_lt hrn_re hre_rm hrm_rg hm_g hmbd hrg hball_exp hball_log
        (Metric.ball_subset_ball hρ_rn hz)
        (by simpa [sub_eq_add_neg, smul_neg] using Metric.ball_subset_ball hρ_rn (hseg s hs).2)
        (x := m) (h := -h) (t := s)
      have h2' : HasDerivAt (fun s => dist (φ.symm (m - s • h)) (φ.symm z) ^ 2)
          (2 * M.inner (m - s • h) (M.log (m - s • h) z) h) s := by
        have heq : (fun s : ℝ => dist (φ.symm (m + s • (-h))) (φ.symm z) ^ 2) =
            fun s => dist (φ.symm (m - s • h)) (φ.symm z) ^ 2 := by
          ext u; simp [sub_eq_add_neg, smul_neg]
        rw [heq] at h2
        refine h2.congr_deriv ?_
        simp only [sub_eq_add_neg, smul_neg, M.inner_neg_right]; ring
      exact (h1.add h2').congr_deriv (by dsimp [g']; ring)
    have hg'_cont : ContinuousOn g' (uIcc (0 : ℝ) (1 / 2)) := by
      rw [Set.uIcc_of_le (by norm_num)]
      have hterm : ∀ (sgn : ℝ) (hball_s : ∀ s ∈ Icc (0 : ℝ) (1 / 2), m + s • (sgn • h) ∈ ball M.a₀ ρ),
          ContinuousOn (fun s : ℝ => M.inner (m + s • (sgn • h)) (M.log (m + s • (sgn • h)) z) h) (Icc (0 : ℝ) (1 / 2)) := by
        intro sgn hball_s
        refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
        have hline_c : Continuous (fun s : ℝ => m + s • (sgn • h)) := continuous_const.add (continuous_id.smul continuous_const)
        have hg_c : ContinuousOn (fun s : ℝ => M.g (m + s • (sgn • h)) i j) (Icc (0 : ℝ) (1 / 2)) :=
          (M.hg_smooth i j).continuousOn.comp hline_c.continuousOn fun s hs =>
            Metric.ball_subset_ball (hρ_rm.trans hrm_lt.le) (hball_s s hs)
        have hlog_c : ContinuousOn (fun s : ℝ => M.log (m + s • (sgn • h)) z) (Icc (0 : ℝ) (1 / 2)) := fun s hs => by
          have htgt_sz := (hball_log (m + s • (sgn • h)) (Metric.ball_subset_ball hρ_rn (hball_s s hs)) z
            (Metric.ball_subset_ball hρ_rn hz)).1
          have h1 : ContinuousAt (fun u : ℝ => M.log (m + u • (sgn • h)) z) s :=
            continuous_snd.continuousAt.comp
              (ContinuousAt.comp (g := M.EHomeo.symm) (f := fun u : ℝ => (m + u • (sgn • h), z))
                (M.EHomeo.continuousAt_symm htgt_sz) (hline_c.continuousAt.prodMk continuousAt_const))
          exact h1.continuousWithinAt
        exact (hg_c.mul ((EuclideanSpace.proj i).continuous.comp_continuousOn hlog_c)).mul continuousOn_const
      have h1 := hterm (-1) fun s hs => by simpa [sub_eq_add_neg, smul_neg] using (hseg s hs).2
      have h2 := hterm 1 fun s hs => by simpa using (hseg s hs).1
      have h1' : ContinuousOn (fun s : ℝ => M.inner (m - s • h) (M.log (m - s • h) z) h) (Icc (0 : ℝ) (1 / 2)) := by
        have heq : (fun s : ℝ => M.inner (m + s • ((-1 : ℝ) • h)) (M.log (m + s • ((-1 : ℝ) • h)) z) h) =
            fun s : ℝ => M.inner (m - s • h) (M.log (m - s • h) z) h := by
          ext u; simp [sub_eq_add_neg, smul_neg]
        rwa [heq] at h1
      have h2' : ContinuousOn (fun s : ℝ => M.inner (m + s • h) (M.log (m + s • h) z) h) (Icc (0 : ℝ) (1 / 2)) := by
        have heq : (fun s : ℝ => M.inner (m + s • ((1 : ℝ) • h)) (M.log (m + s • ((1 : ℝ) • h)) z) h) =
            fun s : ℝ => M.inner (m + s • h) (M.log (m + s • h) z) h := by
          ext u; simp
        rwa [heq] at h2
      exact continuousOn_const.mul (h1'.sub h2')
    have hg'_lb : ∀ s ∈ Icc (0 : ℝ) (1 / 2), 2 * m_g ^ 2 * s * ‖h‖ ^ 2 ≤ g' s := by
      intro s hs
      set p₁ : Euc n := m + s • h
      set p₂ : Euc n := m - s • h
      have hp₁ : p₁ ∈ ball M.a₀ ρ := (hseg s hs).1
      have hp₂ : p₂ ∈ ball M.a₀ ρ := (hseg s hs).2
      have hdiff_p : p₁ - p₂ = (2 * s) • h := by
        simp only [p₁, p₂, two_mul, add_smul]; abel
      have hnorm_dp : ‖p₁ - p₂‖ = 2 * s * ‖h‖ := by
        rw [hdiff_p, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.1])]
      have hlog_err : ‖(M.log p₂ z - M.log p₁ z) - (p₁ - p₂)‖ ≤ ε * (2 * s * ‖h‖) := by
        have h1 := hlog_approx p₂ hp₂ p₁ hp₁ z hz z hz
        rw [sub_self, norm_zero, max_eq_left (norm_nonneg _), norm_sub_rev p₂ p₁, hnorm_dp] at h1
        have heq : (z - p₂) - (z - p₁) = p₁ - p₂ := by abel
        rwa [heq] at h1
      have hlog1_bd : ‖M.log p₁ z‖ ≤ 4 * ρ := by
        have h1 := hlog_bd p₁ hp₁ z hz
        have h2 : ‖z - p₁‖ ≤ 2 * ρ := by
          have hd1 : dist z M.a₀ < ρ := hz
          have hd2 : dist p₁ M.a₀ < ρ := hp₁
          have htri := dist_triangle z M.a₀ p₁
          rw [dist_comm M.a₀ p₁, dist_eq_norm] at htri
          linarith
        linarith
      have hsplit : g' s = 2 * M.inner p₂ ((2 * s) • h) h +
          2 * M.inner p₂ ((M.log p₂ z - M.log p₁ z) - (p₁ - p₂)) h +
          2 * (M.inner p₂ (M.log p₁ z) h - M.inner p₁ (M.log p₁ z) h) := by
        have h1 : M.inner p₂ ((M.log p₂ z - M.log p₁ z) - (p₁ - p₂)) h =
            M.inner p₂ (M.log p₂ z) h - M.inner p₂ (M.log p₁ z) h - M.inner p₂ (p₁ - p₂) h := by
          rw [M.inner_sub_left, M.inner_sub_left]
        rw [h1, hdiff_p]; dsimp [g', p₁, p₂]; ring
      rw [hsplit, M.inner_smul_left]
      have hs0 : 0 ≤ s := hs.1
      have hmain : 4 * m_g ^ 2 * s * ‖h‖ ^ 2 ≤ 2 * (2 * s * M.inner p₂ h h) := by
        have h1 := hinner_lb p₂ hp₂ h
        nlinarith
      have herr1 : |2 * M.inner p₂ ((M.log p₂ z - M.log p₁ z) - (p₁ - p₂)) h| ≤
          4 * M_g ^ 2 * ε * s * ‖h‖ ^ 2 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        calc 2 * |M.inner p₂ ((M.log p₂ z - M.log p₁ z) - (p₁ - p₂)) h|
            ≤ 2 * (M_g ^ 2 * ‖(M.log p₂ z - M.log p₁ z) - (p₁ - p₂)‖ * ‖h‖) := by
              gcongr; exact hinner_ub p₂ hp₂ _ _
          _ ≤ 2 * (M_g ^ 2 * (ε * (2 * s * ‖h‖)) * ‖h‖) := by
              gcongr
          _ = 4 * M_g ^ 2 * ε * s * ‖h‖ ^ 2 := by ring
      have herr2 : |2 * (M.inner p₂ (M.log p₁ z) h - M.inner p₁ (M.log p₁ z) h)| ≤
          16 * L_g * ρ * s * ‖h‖ ^ 2 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        have hp₂_rm : p₂ ∈ closedBall M.a₀ r_m := Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ_rm hp₂)
        have hp₁_rm : p₁ ∈ closedBall M.a₀ r_m := Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ_rm hp₁)
        calc 2 * |M.inner p₂ (M.log p₁ z) h - M.inner p₁ (M.log p₁ z) h|
            ≤ 2 * (L_g * ‖p₂ - p₁‖ * ‖M.log p₁ z‖ * ‖h‖) := by
              gcongr; exact hmlip p₂ hp₂_rm p₁ hp₁_rm _ _
          _ ≤ 2 * (L_g * (2 * s * ‖h‖) * (4 * ρ) * ‖h‖) := by
              rw [norm_sub_rev p₂ p₁, hnorm_dp]
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hlog1_bd (by positivity))
                  (norm_nonneg _))
                (by norm_num)
          _ = 16 * L_g * ρ * s * ‖h‖ ^ 2 := by ring
      have h4Mg_eps : 4 * M_g ^ 2 * ε ≤ m_g ^ 2 / 2 := by
        have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have h2 : 0 < (M_g ^ 2 + 1) * (n : ℝ) := by positivity
        calc 4 * M_g ^ 2 * ε
            ≤ 4 * ((M_g ^ 2 + 1) * (n : ℝ)) * (m_g ^ 2 / (32 * (M_g ^ 2 + 1) * (n : ℝ))) := by
              refine mul_le_mul ?_ hε_small hε_pos.le (by positivity)
              nlinarith [sq_nonneg M_g]
          _ = m_g ^ 2 / 8 := by field_simp [h2.ne']; ring
          _ ≤ m_g ^ 2 / 2 := by linarith [sq_nonneg m_g]
      have he1_neg : -(4 * M_g ^ 2 * ε * s * ‖h‖ ^ 2) ≤ 2 * M.inner p₂ ((M.log p₂ z - M.log p₁ z) - (p₁ - p₂)) h :=
        neg_le_of_abs_le herr1
      have he2_neg : -(16 * L_g * ρ * s * ‖h‖ ^ 2) ≤ 2 * (M.inner p₂ (M.log p₁ z) h - M.inner p₁ (M.log p₁ z) h) :=
        neg_le_of_abs_le herr2
      have hcomb_err : 4 * M_g ^ 2 * ε * s * ‖h‖ ^ 2 + 16 * L_g * ρ * s * ‖h‖ ^ 2 ≤ m_g ^ 2 * s * ‖h‖ ^ 2 := by
        have h1 := mul_le_mul_of_nonneg_right (by linarith : 4 * M_g ^ 2 * ε + 16 * L_g * ρ ≤ m_g ^ 2)
          (mul_nonneg hs0 (sq_nonneg ‖h‖))
        linarith
      have hnn : 0 ≤ m_g ^ 2 * s * ‖h‖ ^ 2 := by positivity
      linarith
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hg_deriv hg'_cont.intervalIntegrable
    have hmono : ∫ s in (0 : ℝ)..(1 / 2), 2 * m_g ^ 2 * s * ‖h‖ ^ 2 ≤ ∫ s in (0 : ℝ)..(1 / 2), g' s := by
      refine intervalIntegral.integral_mono_on (by norm_num) ?_ hg'_cont.intervalIntegrable hg'_lb
      exact ((continuous_const.mul continuous_id).mul continuous_const).intervalIntegrable _ _
    have hlhs_val : ∫ s in (0 : ℝ)..(1 / 2), 2 * m_g ^ 2 * s * ‖h‖ ^ 2 = (m_g ^ 2 / 4) * ‖h‖ ^ 2 := by
      have heq : (fun s : ℝ => 2 * m_g ^ 2 * s * ‖h‖ ^ 2) = fun s => (2 * m_g ^ 2 * ‖h‖ ^ 2) * s := by
        ext s; ring
      rw [heq, intervalIntegral.integral_const_mul, integral_id]
      ring
    have hg_diff : g (1 / 2) - g 0 =
        dist (φ.symm y) (φ.symm z) ^ 2 + dist (φ.symm x) (φ.symm z) ^ 2 - 2 * dist (φ.symm m) (φ.symm z) ^ 2 := by
      have hp1 : m + (1 / 2 : ℝ) • h = y := by
        simp only [m, h, smul_add, smul_sub]; ext i; simp; ring
      have hp2 : m - (1 / 2 : ℝ) • h = x := by
        simp only [m, h, smul_add, smul_sub]; ext i; simp; ring
      simp only [g, hp1, hp2, zero_smul, add_zero, sub_zero]; ring
    have hdist_xy : dist (φ.symm x) (φ.symm y) ≤ 2 * M_g * ‖h‖ := by
      rw [dist_eq_gnorm_log hn x₀ M rfl hr₁_tgt hinner_M hr_g hr_m hr_e hr_n hρ_0
        hrm_lt hrn_re hre_rm hrm_rg hm_g hmbd hrg hball_exp hball_log
        (Metric.ball_subset_ball hρ_rn hx) (Metric.ball_subset_ball hρ_rn hy)]
      have hx_rm : x ∈ closedBall M.a₀ r_m := Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ_rm hx)
      calc M.gnorm x (M.log x y) ≤ M_g * ‖M.log x y‖ := (hmbd x hx_rm _).2
        _ ≤ M_g * (2 * ‖y - x‖) := mul_le_mul_of_nonneg_left (hlog_bd x hx y hy) hM_g.le
        _ = 2 * M_g * ‖h‖ := by ring
    have hdist_sq : c₀ * dist (φ.symm x) (φ.symm y) ^ 2 ≤ (m_g ^ 2 / 8) * ‖h‖ ^ 2 := by
      have hsq : dist (φ.symm x) (φ.symm y) ^ 2 ≤ (2 * M_g * ‖h‖) ^ 2 :=
        pow_le_pow_left₀ dist_nonneg hdist_xy 2
      calc c₀ * dist (φ.symm x) (φ.symm y) ^ 2
          ≤ c₀ * (2 * M_g * ‖h‖) ^ 2 := mul_le_mul_of_nonneg_left hsq hc₀_pos.le
        _ = (m_g ^ 2 / 8) * ‖h‖ ^ 2 := by dsimp [c₀]; field_simp [hM_g.ne']; ring
    linarith
  -- (B) Construct `n + 1` landmarks `a i`, perturbation radius `r_q`, radii `R i`, and `δ`
  let s : ℝ := ρ / 4
  have hs_pos : 0 < s := by dsimp [s]; linarith
  let a : Fin (n + 1) → Euc n := Fin.cases M.a₀ (fun j => M.a₀ + s • LocalMetric.e j)
  let p : Fin (n + 1) → X := fun i => φ.symm (a i)
  have ha_ball : ∀ i : Fin (n + 1), a i ∈ ball M.a₀ (ρ / 2) := fun i => by
    refine Fin.cases ?_ ?_ i
    · simpa [a] using mem_ball_self (x := M.a₀) (half_pos hρ_pos)
    · intro j
      simp only [a, Fin.cases_succ, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
        norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos]
      have he1 : ‖LocalMetric.e j‖ = 1 := by simp [LocalMetric.e]
      rw [he1, mul_one]; dsimp [s]; linarith
  let r_q : ℝ := min (ρ / 8) (s * m_g ^ 2 / (16 * (M_g ^ 2 + 1) * (n : ℝ)))
  have hr_q : 0 < r_q := lt_min (by linarith) (by positivity)
  have hball_ai_sub : ∀ i : Fin (n + 1), ball (a i) r_q ⊆ closedBall M.a₀ (3 * ρ / 4) := by
    intro i y hy
    show dist y M.a₀ ≤ 3 * ρ / 4
    have h1 : dist y (a i) < r_q := hy
    have h2 : r_q ≤ ρ / 4 := (min_le_left _ _).trans (by linarith)
    have h3 : dist (a i) M.a₀ < ρ / 2 := ha_ball i
    linarith [dist_triangle y (a i) M.a₀]
  have hcb_sub_ball : closedBall M.a₀ (3 * ρ / 4) ⊆ ball M.a₀ ρ :=
    Metric.closedBall_subset_ball (by linarith)
  have hball_ρ_tgt : ball M.a₀ ρ ⊆ φ.target :=
    (Metric.ball_subset_ball (hρ_rm.trans hrm_lt.le)).trans hr₁_tgt
  have hopen_img : ∀ U : Set (Euc n), IsOpen U → U ⊆ ball M.a₀ ρ → IsOpen (φ.symm '' U) := by
    intro U hU hU_sub
    have hUtgt : U ⊆ φ.target := hU_sub.trans hball_ρ_tgt
    have heq : φ.symm '' U = φ.source ∩ φ ⁻¹' U := by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨φ.map_target (hUtgt hy), by simpa [φ.right_inv (hUtgt hy)] using hy⟩
      · rintro ⟨hx, hφx⟩
        exact ⟨φ x, hφx, φ.left_inv hx⟩
    rw [heq]
    exact φ.continuousOn_toFun.isOpen_inter_preimage φ.open_source hU
  have hR_ex : ∀ i : Fin (n + 1), ∃ R > 0, closedBall (p i) (2 * R) ⊆ φ.symm '' ball (a i) r_q := by
    intro i
    have hU_open : IsOpen (φ.symm '' ball (a i) r_q) :=
      hopen_img (ball (a i) r_q) isOpen_ball ((hball_ai_sub i).trans hcb_sub_ball)
    have hpi_mem : p i ∈ φ.symm '' ball (a i) r_q := ⟨a i, mem_ball_self hr_q, rfl⟩
    obtain ⟨r, hr, hr_sub⟩ := Metric.isOpen_iff.mp hU_open (p i) hpi_mem
    refine ⟨r / 3, by linarith, (Metric.closedBall_subset_ball (by linarith : 2 * (r / 3) < r)).trans hr_sub⟩
  choose R hR_pos hR_sub using hR_ex
  let δ : ℝ := R 0
  have hδ_pos : 0 < δ := hR_pos 0
  refine ⟨n, p, R, fun _ => c₀, δ, hR_pos, fun _ => hc₀_pos, hδ_pos, ?_, ?_, ?_⟩
  · -- Compactness of `closedBall (p i) (R i)`
    intro i
    have hcomp_big : IsCompact (φ.symm '' closedBall M.a₀ (3 * ρ / 4)) :=
      (isCompact_closedBall M.a₀ (3 * ρ / 4)).image_of_continuousOn
        (φ.continuousOn_invFun.mono (hcb_sub_ball.trans hball_ρ_tgt))
    have hsub : closedBall (p i) (R i) ⊆ φ.symm '' closedBall M.a₀ (3 * ρ / 4) :=
      (Metric.closedBall_subset_closedBall (by linarith [hR_pos i] : R i ≤ 2 * R i)).trans
        ((hR_sub i).trans (Set.image_mono (hball_ai_sub i)))
    exact hcomp_big.of_isClosed_subset isClosed_closedBall hsub
  · -- Local squared-distance midpoint inequality on `closedBall (p i) (R i)`
    intro i x hx y hy
    have hsub_ρ : closedBall (p i) (R i) ⊆ φ.symm '' ball M.a₀ ρ :=
      (Metric.closedBall_subset_closedBall (by linarith [hR_pos i] : R i ≤ 2 * R i)).trans
        ((hR_sub i).trans (Set.image_mono ((hball_ai_sub i).trans hcb_sub_ball)))
    obtain ⟨x', hx', rfl⟩ := hsub_ρ hx
    obtain ⟨y', hy', rfl⟩ := hsub_ρ hy
    refine ⟨φ.symm ((1 / 2 : ℝ) • (x' + y')), fun z hz => ?_⟩
    obtain ⟨z', hz', rfl⟩ := hsub_ρ hz
    exact hstrong_conv x' hx' y' hy' z' hz'
  · -- Stable local distance coordinates on `ball (q 0) δ`
    intro q hq x hx y hy hdist_eq
    have hq_coord : ∀ i : Fin (n + 1), ∃ q' ∈ ball (a i) r_q, φ.symm q' = q i := fun i =>
      hR_sub i (Metric.closedBall_subset_closedBall (by linarith [hR_pos i]) (hq i))
    choose q' hq'_ball hq'_eq using hq_coord
    have hq'_ρ : ∀ i : Fin (n + 1), q' i ∈ ball M.a₀ ρ := fun i =>
      hcb_sub_ball (hball_ai_sub i (hq'_ball i))
    have hball_q0 : ball (q 0) δ ⊆ φ.symm '' ball M.a₀ ρ := by
      intro w hw
      have hw_p0 : w ∈ closedBall (p 0) (2 * R 0) := by
        show dist w (p 0) ≤ 2 * R 0
        have h1 : dist w (q 0) < R 0 := hw
        have h2 : dist (q 0) (p 0) ≤ R 0 := hq 0
        linarith [dist_triangle w (q 0) (p 0)]
      exact Set.image_mono ((hball_ai_sub 0).trans hcb_sub_ball) (hR_sub 0 hw_p0)
    obtain ⟨x', hx', rfl⟩ := hball_q0 hx
    obtain ⟨y', hy', rfl⟩ := hball_q0 hy
    suffices hxy' : x' = y' by rw [hxy']
    let h : Euc n := y' - x'
    have hseg_xy : ∀ t ∈ Icc (0 : ℝ) 1, x' + t • h ∈ ball M.a₀ ρ := fun t ht => by
      have h1 : x' + t • h = (1 - t) • x' + t • y' := by
        simp only [h, smul_sub, sub_smul, one_smul]; abel
      rw [h1]
      exact (convex_ball M.a₀ ρ) hx' hy' (by linarith [ht.2]) ht.1 (by ring)
    -- For each `j : Fin n`, `0 = ∫_0^1 (-2) * M.inner (x' + t•h) (log (x' + t•h) (q' j.succ) - log (x' + t•h) (q' 0)) h`
    have hint_j : ∀ j : Fin n,
        ∫ t in (0 : ℝ)..1,
          M.inner (x' + t • h) (M.log (x' + t • h) (q' j.succ) - M.log (x' + t • h) (q' 0)) h = 0 := by
      intro j
      let ψ : ℝ → ℝ := fun t =>
        dist (φ.symm (x' + t • h)) (φ.symm (q' j.succ)) ^ 2 -
        dist (φ.symm (x' + t • h)) (φ.symm (q' 0)) ^ 2
      let ψ' : ℝ → ℝ := fun t =>
        (-2) * M.inner (x' + t • h) (M.log (x' + t • h) (q' j.succ) - M.log (x' + t • h) (q' 0)) h
      have hψ_deriv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt ψ (ψ' t) t := by
        intro t ht
        rw [Set.uIcc_of_le zero_le_one] at ht
        have h1 := sq_dist_hasDerivAt_line hn x₀ M rfl hr₁_tgt hinner_M
          hr_g hr_m hr_e hr_n hρ_0 hrm_lt hrn_re hre_rm hrm_rg hm_g hmbd hrg hball_exp hball_log
          (Metric.ball_subset_ball hρ_rn (hq'_ρ j.succ)) (Metric.ball_subset_ball hρ_rn (hseg_xy t ht))
          (x := x') (h := h) (t := t)
        have h2 := sq_dist_hasDerivAt_line hn x₀ M rfl hr₁_tgt hinner_M
          hr_g hr_m hr_e hr_n hρ_0 hrm_lt hrn_re hre_rm hrm_rg hm_g hmbd hrg hball_exp hball_log
          (Metric.ball_subset_ball hρ_rn (hq'_ρ 0)) (Metric.ball_subset_ball hρ_rn (hseg_xy t ht))
          (x := x') (h := h) (t := t)
        exact (h1.sub h2).congr_deriv (by dsimp [ψ']; rw [M.inner_sub_left]; ring)
      have hψ'_cont : ContinuousOn ψ' (uIcc (0 : ℝ) 1) := by
        rw [Set.uIcc_of_le zero_le_one]
        have hterm : ∀ i : Fin (n + 1),
            ContinuousOn (fun t : ℝ => M.inner (x' + t • h) (M.log (x' + t • h) (q' i)) h) (Icc (0 : ℝ) 1) := by
          intro i
          refine continuousOn_finsetSum _ fun a1 _ => continuousOn_finsetSum _ fun a2 _ => ?_
          have hline_c : Continuous (fun t : ℝ => x' + t • h) := continuous_const.add (continuous_id.smul continuous_const)
          have hg_c : ContinuousOn (fun t : ℝ => M.g (x' + t • h) a1 a2) (Icc (0 : ℝ) 1) :=
            (M.hg_smooth a1 a2).continuousOn.comp hline_c.continuousOn fun t ht =>
              Metric.ball_subset_ball (hρ_rm.trans hrm_lt.le) (hseg_xy t ht)
          have hlog_c : ContinuousOn (fun t : ℝ => M.log (x' + t • h) (q' i)) (Icc (0 : ℝ) 1) := fun t ht => by
            have htgt_tq := (hball_log (x' + t • h) (Metric.ball_subset_ball hρ_rn (hseg_xy t ht))
              (q' i) (Metric.ball_subset_ball hρ_rn (hq'_ρ i))).1
            have hc1 : ContinuousAt (fun u : ℝ => M.log (x' + u • h) (q' i)) t :=
              continuous_snd.continuousAt.comp
                (ContinuousAt.comp (g := M.EHomeo.symm) (f := fun u : ℝ => (x' + u • h, q' i))
                  (M.EHomeo.continuousAt_symm htgt_tq) (hline_c.continuousAt.prodMk continuousAt_const))
            exact hc1.continuousWithinAt
          exact (hg_c.mul ((EuclideanSpace.proj a1).continuous.comp_continuousOn hlog_c)).mul continuousOn_const
        have heq : ψ' = fun t : ℝ => (-2) * (M.inner (x' + t • h) (M.log (x' + t • h) (q' j.succ)) h -
            M.inner (x' + t • h) (M.log (x' + t • h) (q' 0)) h) := by
          ext t; dsimp [ψ']; rw [M.inner_sub_left]
        rw [heq]
        exact continuousOn_const.mul ((hterm j.succ).sub (hterm 0))
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hψ_deriv hψ'_cont.intervalIntegrable
      have hψ10 : ψ 1 - ψ 0 = 0 := by
        have h1 : x' + (1 : ℝ) • h = y' := by simp [h]
        have h0 : x' + (0 : ℝ) • h = x' := by simp
        have heq_j : dist (φ.symm x') (q j.succ) = dist (φ.symm y') (q j.succ) := congrFun hdist_eq j.succ
        have heq_0 : dist (φ.symm x') (q 0) = dist (φ.symm y') (q 0) := congrFun hdist_eq 0
        simp only [ψ, h1, h0, hq'_eq, heq_j, heq_0, sub_self]
      rw [hψ10] at hftc
      have hmul : (-2 : ℝ) * ∫ t in (0 : ℝ)..1,
          M.inner (x' + t • h) (M.log (x' + t • h) (q' j.succ) - M.log (x' + t • h) (q' 0)) h = 0 := by
        rw [← intervalIntegral.integral_const_mul]; exact hftc
      exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
    -- Weight by `h.ofLp j` and sum over `j : Fin n`
    let W : ℝ → Euc n := fun t =>
      ∑ j : Fin n, h.ofLp j • (M.log (x' + t • h) (q' j.succ) - M.log (x' + t • h) (q' 0))
    have hW_int_cont : ContinuousOn (fun t : ℝ => M.inner (x' + t • h) (W t) h) (Icc (0 : ℝ) 1) := by
      have hterm : ∀ j : Fin n,
          ContinuousOn (fun t : ℝ => h.ofLp j * M.inner (x' + t • h)
            (M.log (x' + t • h) (q' j.succ) - M.log (x' + t • h) (q' 0)) h) (Icc (0 : ℝ) 1) := by
        intro j
        refine continuousOn_const.mul ?_
        have hinner_c : ∀ i : Fin (n + 1),
            ContinuousOn (fun t : ℝ => M.inner (x' + t • h) (M.log (x' + t • h) (q' i)) h) (Icc (0 : ℝ) 1) := by
          intro i
          refine continuousOn_finsetSum _ fun a1 _ => continuousOn_finsetSum _ fun a2 _ => ?_
          have hline_c : Continuous (fun t : ℝ => x' + t • h) := continuous_const.add (continuous_id.smul continuous_const)
          have hg_c : ContinuousOn (fun t : ℝ => M.g (x' + t • h) a1 a2) (Icc (0 : ℝ) 1) :=
            (M.hg_smooth a1 a2).continuousOn.comp hline_c.continuousOn fun t ht =>
              Metric.ball_subset_ball (hρ_rm.trans hrm_lt.le) (hseg_xy t ht)
          have hlog_c : ContinuousOn (fun t : ℝ => M.log (x' + t • h) (q' i)) (Icc (0 : ℝ) 1) := fun t ht => by
            have htgt_tq := (hball_log (x' + t • h) (Metric.ball_subset_ball hρ_rn (hseg_xy t ht))
              (q' i) (Metric.ball_subset_ball hρ_rn (hq'_ρ i))).1
            have hc1 : ContinuousAt (fun u : ℝ => M.log (x' + u • h) (q' i)) t :=
              continuous_snd.continuousAt.comp
                (ContinuousAt.comp (g := M.EHomeo.symm) (f := fun u : ℝ => (x' + u • h, q' i))
                  (M.EHomeo.continuousAt_symm htgt_tq) (hline_c.continuousAt.prodMk continuousAt_const))
            exact hc1.continuousWithinAt
          exact (hg_c.mul ((EuclideanSpace.proj a1).continuous.comp_continuousOn hlog_c)).mul continuousOn_const
        have heq : (fun t : ℝ => M.inner (x' + t • h) (M.log (x' + t • h) (q' j.succ) - M.log (x' + t • h) (q' 0)) h) =
            fun t : ℝ => M.inner (x' + t • h) (M.log (x' + t • h) (q' j.succ)) h -
              M.inner (x' + t • h) (M.log (x' + t • h) (q' 0)) h := by
          ext t; rw [M.inner_sub_left]
        rw [heq]; exact (hinner_c j.succ).sub (hinner_c 0)
      have heq : (fun t : ℝ => M.inner (x' + t • h) (W t) h) =
          fun t : ℝ => ∑ j : Fin n, h.ofLp j * M.inner (x' + t • h)
            (M.log (x' + t • h) (q' j.succ) - M.log (x' + t • h) (q' 0)) h := by
        ext t; simp only [W, M.inner_sum_left, M.inner_smul_left]
      rw [heq]
      exact continuousOn_finsetSum _ fun j _ => hterm j
    have hW_int_zero : ∫ t in (0 : ℝ)..1, M.inner (x' + t • h) (W t) h = 0 := by
      have heq : (fun t : ℝ => M.inner (x' + t • h) (W t) h) =
          fun t : ℝ => ∑ j : Fin n, h.ofLp j * M.inner (x' + t • h)
            (M.log (x' + t • h) (q' j.succ) - M.log (x' + t • h) (q' 0)) h := by
        ext t; simp only [W, M.inner_sum_left, M.inner_smul_left]
      rw [heq, intervalIntegral.integral_finsetSum]
      · refine Finset.sum_eq_zero fun j _ => ?_
        rw [intervalIntegral.integral_const_mul, hint_j j, mul_zero]
      · intro j _
        have hinner_c : ∀ i : Fin (n + 1),
            ContinuousOn (fun t : ℝ => M.inner (x' + t • h) (M.log (x' + t • h) (q' i)) h) (uIcc (0 : ℝ) 1) := by
          intro i; rw [Set.uIcc_of_le zero_le_one]
          refine continuousOn_finsetSum _ fun a1 _ => continuousOn_finsetSum _ fun a2 _ => ?_
          have hline_c : Continuous (fun t : ℝ => x' + t • h) := continuous_const.add (continuous_id.smul continuous_const)
          have hg_c : ContinuousOn (fun t : ℝ => M.g (x' + t • h) a1 a2) (Icc (0 : ℝ) 1) :=
            (M.hg_smooth a1 a2).continuousOn.comp hline_c.continuousOn fun t ht =>
              Metric.ball_subset_ball (hρ_rm.trans hrm_lt.le) (hseg_xy t ht)
          have hlog_c : ContinuousOn (fun t : ℝ => M.log (x' + t • h) (q' i)) (Icc (0 : ℝ) 1) := fun t ht => by
            have htgt_tq := (hball_log (x' + t • h) (Metric.ball_subset_ball hρ_rn (hseg_xy t ht))
              (q' i) (Metric.ball_subset_ball hρ_rn (hq'_ρ i))).1
            have hc1 : ContinuousAt (fun u : ℝ => M.log (x' + u • h) (q' i)) t :=
              continuous_snd.continuousAt.comp
                (ContinuousAt.comp (g := M.EHomeo.symm) (f := fun u : ℝ => (x' + u • h, q' i))
                  (M.EHomeo.continuousAt_symm htgt_tq) (hline_c.continuousAt.prodMk continuousAt_const))
            exact hc1.continuousWithinAt
          exact (hg_c.mul ((EuclideanSpace.proj a1).continuous.comp_continuousOn hlog_c)).mul continuousOn_const
        have hc : ContinuousOn (fun t : ℝ => h.ofLp j * M.inner (x' + t • h)
            (M.log (x' + t • h) (q' j.succ) - M.log (x' + t • h) (q' 0)) h) (uIcc (0 : ℝ) 1) := by
          refine continuousOn_const.mul ?_
          have heq2 : (fun t : ℝ => M.inner (x' + t • h) (M.log (x' + t • h) (q' j.succ) - M.log (x' + t • h) (q' 0)) h) =
              fun t : ℝ => M.inner (x' + t • h) (M.log (x' + t • h) (q' j.succ)) h -
                M.inner (x' + t • h) (M.log (x' + t • h) (q' 0)) h := by
            ext t; rw [M.inner_sub_left]
          rw [heq2]; exact (hinner_c j.succ).sub (hinner_c 0)
        exact hc.intervalIntegrable
    -- Pointwise coercivity: `M.inner (x' + t • h) (W t) h ≥ (s * m_g^2 / 2) * ‖h‖^2` for all `t ∈ Icc 0 1`
    have hW_lb : ∀ t ∈ Icc (0 : ℝ) 1, (s * m_g ^ 2 / 2) * ‖h‖ ^ 2 ≤ M.inner (x' + t • h) (W t) h := by
      intro t ht
      set pt : Euc n := x' + t • h
      have hpt : pt ∈ ball M.a₀ ρ := hseg_xy t ht
      have hsh : s • h = ∑ j : Fin n, h.ofLp j • (s • LocalMetric.e j) := by
        ext m; simp [LocalMetric.e, Pi.single_apply]; ring
      have hW_err : ‖W t - s • h‖ ≤ (n : ℝ) * (2 * ε * s + 2 * r_q) * ‖h‖ := by
        have hsub_eq : W t - s • h =
            ∑ j : Fin n, h.ofLp j • ((M.log pt (q' j.succ) - M.log pt (q' 0)) - s • LocalMetric.e j) := by
          rw [hsh]; dsimp [W]; rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => (smul_sub _ _ _).symm
        rw [hsub_eq]
        calc ‖∑ j : Fin n, h.ofLp j • ((M.log pt (q' j.succ) - M.log pt (q' 0)) - s • LocalMetric.e j)‖
            ≤ ∑ j : Fin n, ‖h.ofLp j • ((M.log pt (q' j.succ) - M.log pt (q' 0)) - s • LocalMetric.e j)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ _j : Fin n, (2 * ε * s + 2 * r_q) * ‖h‖ := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [norm_smul, Real.norm_eq_abs]
              have hhj : |h.ofLp j| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le h j
              have hqj_err : ‖(q' j.succ - q' 0) - s • LocalMetric.e j‖ ≤ 2 * r_q := by
                have heq : (q' j.succ - q' 0) - s • LocalMetric.e j =
                    (q' j.succ - a j.succ) - (q' 0 - a 0) := by
                  simp only [a, Fin.cases_zero, Fin.cases_succ]; abel
                rw [heq]
                have h1 : ‖q' j.succ - a j.succ‖ < r_q := by simpa [dist_eq_norm] using hq'_ball j.succ
                have h2 : ‖q' 0 - a 0‖ < r_q := by simpa [dist_eq_norm] using hq'_ball 0
                linarith [norm_sub_le (q' j.succ - a j.succ) (q' 0 - a 0)]
              have hqj_norm : ‖q' j.succ - q' 0‖ ≤ 2 * s := by
                have htri : ‖q' j.succ - q' 0‖ ≤ ‖(q' j.succ - q' 0) - s • LocalMetric.e j‖ + ‖s • LocalMetric.e j‖ := by
                  simpa using norm_add_le ((q' j.succ - q' 0) - s • LocalMetric.e j) (s • LocalMetric.e j)
                have hse : ‖s • LocalMetric.e j‖ = s := by
                  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos]; simp [LocalMetric.e]
                have hrq_le : 2 * r_q ≤ s := by
                  have h1 : r_q ≤ ρ / 8 := min_le_left _ _
                  dsimp [s]; linarith
                linarith
              have hlog_err : ‖(M.log pt (q' j.succ) - M.log pt (q' 0)) - (q' j.succ - q' 0)‖ ≤ 2 * ε * s := by
                have h1 := hlog_approx pt hpt pt hpt (q' j.succ) (hq'_ρ j.succ) (q' 0) (hq'_ρ 0)
                rw [sub_self, norm_zero, max_eq_right (norm_nonneg _)] at h1
                have heq : (q' j.succ - pt) - (q' 0 - pt) = q' j.succ - q' 0 := by abel
                rw [heq] at h1
                calc ‖(M.log pt (q' j.succ) - M.log pt (q' 0)) - (q' j.succ - q' 0)‖
                    ≤ ε * ‖q' j.succ - q' 0‖ := h1
                  _ ≤ ε * (2 * s) := mul_le_mul_of_nonneg_left hqj_norm hε_pos.le
                  _ = 2 * ε * s := by ring
              have htot : ‖(M.log pt (q' j.succ) - M.log pt (q' 0)) - s • LocalMetric.e j‖ ≤ 2 * ε * s + 2 * r_q := by
                have hsplit : (M.log pt (q' j.succ) - M.log pt (q' 0)) - s • LocalMetric.e j =
                    ((M.log pt (q' j.succ) - M.log pt (q' 0)) - (q' j.succ - q' 0)) +
                    ((q' j.succ - q' 0) - s • LocalMetric.e j) := by abel
                rw [hsplit]
                exact (norm_add_le _ _).trans (add_le_add hlog_err hqj_err)
              calc |h.ofLp j| * ‖(M.log pt (q' j.succ) - M.log pt (q' 0)) - s • LocalMetric.e j‖
                  ≤ ‖h‖ * (2 * ε * s + 2 * r_q) :=
                    mul_le_mul hhj htot (norm_nonneg _) (norm_nonneg _)
                _ = (2 * ε * s + 2 * r_q) * ‖h‖ := mul_comm _ _
          _ = (n : ℝ) * (2 * ε * s + 2 * r_q) * ‖h‖ := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      have hsplit : M.inner pt (W t) h = s * M.inner pt h h + M.inner pt (W t - s • h) h := by
        have h1 : M.inner pt (W t - s • h) h = M.inner pt (W t) h - s * M.inner pt h h := by
          rw [M.inner_sub_left, M.inner_smul_left]
        linarith
      rw [hsplit]
      have hmain : s * m_g ^ 2 * ‖h‖ ^ 2 ≤ s * M.inner pt h h := by
        have h1 := hinner_lb pt hpt h
        nlinarith
      have herr : |M.inner pt (W t - s • h) h| ≤
          M_g ^ 2 * (n : ℝ) * (2 * ε * s + 2 * r_q) * ‖h‖ ^ 2 := by
        calc |M.inner pt (W t - s • h) h|
            ≤ M_g ^ 2 * ‖W t - s • h‖ * ‖h‖ := hinner_ub pt hpt _ _
          _ ≤ M_g ^ 2 * ((n : ℝ) * (2 * ε * s + 2 * r_q) * ‖h‖) * ‖h‖ := by gcongr
          _ = M_g ^ 2 * (n : ℝ) * (2 * ε * s + 2 * r_q) * ‖h‖ ^ 2 := by ring
      have hcoeff_small : M_g ^ 2 * (n : ℝ) * (2 * ε * s + 2 * r_q) ≤ s * m_g ^ 2 / 2 := by
        have hden_pos : 0 < (M_g ^ 2 + 1) * (n : ℝ) := by positivity
        have h1 : M_g ^ 2 * (n : ℝ) * (2 * ε * s) ≤ s * m_g ^ 2 / 4 := by
          calc M_g ^ 2 * (n : ℝ) * (2 * ε * s)
              ≤ (M_g ^ 2 + 1) * (n : ℝ) * (2 * (m_g ^ 2 / (32 * (M_g ^ 2 + 1) * (n : ℝ))) * s) := by
                refine mul_le_mul (by nlinarith) ?_ (by positivity) (by positivity)
                gcongr
            _ = s * m_g ^ 2 / 16 := by field_simp [hden_pos.ne']; ring
            _ ≤ s * m_g ^ 2 / 4 := by nlinarith [sq_nonneg m_g]
        have h2 : M_g ^ 2 * (n : ℝ) * (2 * r_q) ≤ s * m_g ^ 2 / 4 := by
          have hrq2 : r_q ≤ s * m_g ^ 2 / (16 * (M_g ^ 2 + 1) * (n : ℝ)) := min_le_right _ _
          calc M_g ^ 2 * (n : ℝ) * (2 * r_q)
              ≤ (M_g ^ 2 + 1) * (n : ℝ) * (2 * (s * m_g ^ 2 / (16 * (M_g ^ 2 + 1) * (n : ℝ)))) := by
                refine mul_le_mul (by nlinarith) ?_ (by positivity) (by positivity)
                gcongr
            _ = s * m_g ^ 2 / 8 := by field_simp [hden_pos.ne']; ring
            _ ≤ s * m_g ^ 2 / 4 := by nlinarith [sq_nonneg m_g]
        linarith
      have herr_neg : -(s * m_g ^ 2 / 2 * ‖h‖ ^ 2) ≤ M.inner pt (W t - s • h) h := by
        have h1 := neg_le_of_abs_le herr
        have h2 : M_g ^ 2 * (n : ℝ) * (2 * ε * s + 2 * r_q) * ‖h‖ ^ 2 ≤ (s * m_g ^ 2 / 2) * ‖h‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcoeff_small (sq_nonneg _)
        linarith
      linarith
    have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) zero_le_one
      intervalIntegrable_const
      ((by rwa [Set.uIcc_of_le zero_le_one] : ContinuousOn _ (uIcc (0 : ℝ) 1)).intervalIntegrable) hW_lb
    rw [intervalIntegral.integral_const, sub_zero, one_smul, hW_int_zero] at hmono
    have hnh0 : ‖h‖ = 0 := by
      have hpos_c : 0 < s * m_g ^ 2 / 2 := by positivity
      have hsq0 : ‖h‖ ^ 2 ≤ 0 := by nlinarith
      have hsq_eq : ‖h‖ ^ 2 = 0 := le_antisymm hsq0 (sq_nonneg _)
      exact sq_eq_zero_iff.mp hsq_eq
    exact (sub_eq_zero.mp (norm_eq_zero.mp hnh0)).symm

end MainProof

end Hilbert5H1

/-- Solution to `Hilbert5.hilbert_smith_conjecture.variants.riemannian.R1.H1`. -/
theorem OMA.solution : OMA.R_Hilbert5_hilbert_smith_conjecture_variants_riemannian_R1.H1 := by
  intro n X _ _ _ _ _ _ _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Hilbert5H1.h1_zero X
  · exact Hilbert5H1.h1_pos hn X
