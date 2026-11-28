import OMAReductions.R_Hilbert5_hilbert_smith_conjecture_variants_riemannian_R1
import Mathlib

/-!
# Unique Continuation of Riemannian Isometries

Proves `OMA.R_Hilbert5_hilbert_smith_conjecture_variants_riemannian_R1.H2`: a bijective
isometry of a connected smooth Riemannian manifold that fixes every point of a nonempty
open subset is the identity.
-/

noncomputable section

namespace OMA.Hilbert5H2

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

private def e (i : Fin n) : Euc n := EuclideanSpace.single i (1 : ℝ)

private def inner (y u v : Euc n) : ℝ :=
  ∑ i, ∑ j, M.g y i j * u.ofLp i * v.ofLp j

private lemma inner_symm {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (u v : Euc n) :
    M.inner y u v = M.inner y v u := by
  simp only [inner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [M.hg_symm y hy i j]; ring

private lemma inner_pos {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) {v : Euc n} (hv : v ≠ 0) :
    0 < M.inner y v v := M.hg_pos y hy v hv

private lemma inner_nonneg {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (v : Euc n) :
    0 ≤ M.inner y v v := by
  by_cases hv : v = 0
  · subst hv; simp [inner]
  · exact (M.inner_pos hy hv).le

private lemma inner_add_left (y u₁ u₂ v : Euc n) :
    M.inner y (u₁ + u₂) v = M.inner y u₁ v + M.inner y u₂ v := by
  simp only [inner, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.add_apply]; ring

private lemma inner_add_right (y u v₁ v₂ : Euc n) :
    M.inner y u (v₁ + v₂) = M.inner y u v₁ + M.inner y u v₂ := by
  simp only [inner, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.add_apply]; ring

private lemma inner_smul_left (y : Euc n) (c : ℝ) (u v : Euc n) :
    M.inner y (c • u) v = c * M.inner y u v := by
  simp only [inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]; ring

private lemma inner_smul_right (y : Euc n) (c : ℝ) (u v : Euc n) :
    M.inner y u (c • v) = c * M.inner y u v := by
  simp only [inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]; ring

private lemma inner_sub_left (y u₁ u₂ v : Euc n) :
    M.inner y (u₁ - u₂) v = M.inner y u₁ v - M.inner y u₂ v := by
  rw [sub_eq_add_neg, M.inner_add_left, ← neg_one_smul ℝ u₂, M.inner_smul_left]; ring

private lemma inner_sub_right (y u v₁ v₂ : Euc n) :
    M.inner y u (v₁ - v₂) = M.inner y u v₁ - M.inner y u v₂ := by
  rw [sub_eq_add_neg, M.inner_add_right, ← neg_one_smul ℝ v₂, M.inner_smul_right]; ring

private lemma inner_neg_left (y u v : Euc n) : M.inner y (-u) v = -M.inner y u v := by
  rw [← neg_one_smul ℝ u, M.inner_smul_left]; ring

private lemma inner_zero_left (y v : Euc n) : M.inner y 0 v = 0 := by simp [inner]
private lemma inner_zero_right (y u : Euc n) : M.inner y u 0 = 0 := by simp [inner]

private lemma inner_cauchy_schwarz {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (u v : Euc n) :
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

private def gnorm (y v : Euc n) : ℝ := Real.sqrt (M.inner y v v)

private lemma gnorm_sq {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (v : Euc n) :
    (M.gnorm y v) ^ 2 = M.inner y v v :=
  Real.sq_sqrt (M.inner_nonneg hy v)

private def mat (y : Euc n) : Matrix (Fin n) (Fin n) ℝ := Matrix.of (M.g y)

private lemma mat_det_ne_zero {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) :
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

private def matInv (y : Euc n) : Matrix (Fin n) (Fin n) ℝ := (M.mat y)⁻¹

private lemma mat_mul_inv {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (i j : Fin n) :
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

private lemma matInv_contDiffOn (l k : Fin n) :
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

private def dg (y : Euc n) (k i j : Fin n) : ℝ :=
  fderiv ℝ (fun z => M.g z i j) y (e k)

private lemma dg_contDiffOn (k i j : Fin n) :
    ContDiffOn ℝ 2 (fun y => M.dg y k i j) (ball M.a₀ M.r₁) := by
  have hfd : ContDiffOn ℝ 2 (fun y => fderivWithin ℝ (fun z => M.g z i j) (ball M.a₀ M.r₁) y)
      (ball M.a₀ M.r₁) :=
    (M.hg_smooth i j).fderivWithin isOpen_ball.uniqueDiffOn (by norm_num)
  have hcongr : ContDiffOn ℝ 2 (fun y => fderiv ℝ (fun z => M.g z i j) y) (ball M.a₀ M.r₁) :=
    hfd.congr fun y hy => (fderivWithin_of_isOpen isOpen_ball hy).symm
  exact (ContinuousLinearMap.apply ℝ ℝ (e k)).contDiff.comp_contDiffOn hcongr

private lemma dg_symm {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (k i j : Fin n) :
    M.dg y k i j = M.dg y k j i := by
  have heq : (fun z => M.g z i j) =ᶠ[𝓝 y] (fun z => M.g z j i) := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz using M.hg_symm z hz i j
  simp only [dg, heq.fderiv_eq]

private lemma fderiv_g_apply {y : Euc n} (i j : Fin n) (u : Euc n) :
    fderiv ℝ (fun z => M.g z i j) y u = ∑ k, M.dg y k i j * u.ofLp k := by
  have hu : u = ∑ k, u.ofLp k • e k := by
    ext m
    simp [e, Pi.single_apply]
  conv_lhs => rw [hu]
  simp only [map_sum, map_smul, smul_eq_mul, dg, mul_comm]

private def Γ (y : Euc n) (l i j : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ k, M.matInv y l k * (M.dg y i j k + M.dg y j i k - M.dg y k i j)

private lemma Γ_symm {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (l i j : Fin n) :
    M.Γ y l i j = M.Γ y l j i := by
  simp only [Γ]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [M.dg_symm hy k i j]; ring

private lemma Γ_contDiffOn (l i j : Fin n) :
    ContDiffOn ℝ 2 (fun y => M.Γ y l i j) (ball M.a₀ M.r₁) := by
  refine ContDiffOn.mul contDiffOn_const (ContDiffOn.sum fun k _ => ContDiffOn.mul ?_ ?_)
  · exact (M.matInv_contDiffOn l k).of_le (by norm_num)
  · exact ((M.dg_contDiffOn i j k).add (M.dg_contDiffOn j i k)).sub (M.dg_contDiffOn k i j)

private def ΓVec (y u v : Euc n) : Euc n :=
  WithLp.toLp 2 (fun l => ∑ i, ∑ j, M.Γ y l i j * u.ofLp i * v.ofLp j)

private lemma ΓVec_symm {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (u v : Euc n) :
    M.ΓVec y u v = M.ΓVec y v u := by
  ext l
  simp only [ΓVec]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [M.Γ_symm hy l i j]; ring

private lemma inner_ΓVec {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (u v w : Euc n) :
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
                      congr 1
                      simp_rw [M.mat_mul_inv hy]
                      simp
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

private lemma dG_eq_ΓVec {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) (u v w : Euc n) :
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
private lemma hasDerivAt_inner {γ u v : ℝ → Euc n} {t : ℝ} {γ' u' v' : Euc n}
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

private def proj01 (t : ℝ) : I01 := Set.projIcc 0 1 zero_le_one t

private lemma continuous_proj01 : Continuous proj01 :=
  continuous_projIcc (h := zero_le_one)

private def intFun (f : PathOne n) (t : ℝ) : Euc n :=
  ∫ s in (0 : ℝ)..t, f (proj01 s)

private lemma intFun_hasDerivAt (f : PathOne n) (t : ℝ) :
    HasDerivAt (intFun f) (f (proj01 t)) t := by
  have hc : Continuous (fun s : ℝ => f (proj01 s)) := f.continuous.comp continuous_proj01
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

private def intOp : PathOne n →L[ℝ] PathOne n :=
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

private lemma intOp_apply (f : PathOne n) (t : I01) :
    intOp f t = intFun f t.1 := rfl

private lemma intOp_apply_zero (f : PathOne n) :
    intOp f ⟨0, left_mem_Icc.mpr zero_le_one⟩ = 0 := by
  simp [intOp_apply, intFun]

private def proj1L : PathPair n →L[ℝ] PathOne n :=
  LinearMap.mkContinuous
    { toFun := fun z => mkOfCompact ⟨fun t => (z t).1, continuous_fst.comp z.continuous⟩
      map_add' := fun _ _ => BoundedContinuousFunction.ext fun _ => rfl
      map_smul' := fun _ _ => BoundedContinuousFunction.ext fun _ => rfl }
    1 (fun z => by
      change ‖mkOfCompact (⟨fun t : I01 => (z t).1, _⟩ : C(I01, Euc n))‖ ≤ 1 * ‖z‖
      rw [one_mul, BoundedContinuousFunction.norm_le (norm_nonneg z)]
      intro t
      exact (norm_fst_le (z t)).trans (BoundedContinuousFunction.norm_coe_le_norm z t))

private def proj2L : PathPair n →L[ℝ] PathOne n :=
  LinearMap.mkContinuous
    { toFun := fun z => mkOfCompact ⟨fun t => (z t).2, continuous_snd.comp z.continuous⟩
      map_add' := fun _ _ => BoundedContinuousFunction.ext fun _ => rfl
      map_smul' := fun _ _ => BoundedContinuousFunction.ext fun _ => rfl }
    1 (fun z => by
      change ‖mkOfCompact (⟨fun t : I01 => (z t).2, _⟩ : C(I01, Euc n))‖ ≤ 1 * ‖z‖
      rw [one_mul, BoundedContinuousFunction.norm_le (norm_nonneg z)]
      intro t
      exact (norm_snd_le (z t)).trans (BoundedContinuousFunction.norm_coe_le_norm z t))

private def pairL : PathOne n × PathOne n →L[ℝ] PathPair n :=
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

private def constPairL : Euc n × Euc n →L[ℝ] PathPair n :=
  LinearMap.mkContinuous
    { toFun := fun p => BoundedContinuousFunction.const I01 p
      map_add' := fun _ _ => BoundedContinuousFunction.ext fun _ => rfl
      map_smul' := fun _ _ => BoundedContinuousFunction.ext fun _ => rfl }
    1 (fun p => by
      change ‖BoundedContinuousFunction.const I01 p‖ ≤ 1 * ‖p‖
      rw [one_mul, BoundedContinuousFunction.norm_le (norm_nonneg p)]
      intro _; exact le_rfl)

private def evalAtL (t : I01) : PathPair n →L[ℝ] Euc n × Euc n :=
  LinearMap.mkContinuous
    { toFun := fun z => z t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun z => by rw [one_mul]; exact BoundedContinuousFunction.norm_coe_le_norm z t)

private def dpsi0Equiv : PathPair n ≃L[ℝ] PathPair n :=
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

private def quadF (x : Euc n × Euc n) : Euc n := M.ΓVec x.1 x.2 x.2

private lemma quadF_contDiffOn : ContDiffOn ℝ 2 M.quadF (ball M.a₀ M.r₁ ×ˢ univ) := by
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

private def dquadF (x : Euc n × Euc n) : (Euc n × Euc n) →L[ℝ] Euc n :=
  fderiv ℝ M.quadF x

private lemma dquadF_continuousOn : ContinuousOn M.dquadF (ball M.a₀ M.r₁ ×ˢ univ) := by
  have hopen : IsOpen (ball M.a₀ M.r₁ ×ˢ (univ : Set (Euc n))) := isOpen_ball.prod isOpen_univ
  have hfd : ContDiffOn ℝ 1 (fun x => fderivWithin ℝ M.quadF (ball M.a₀ M.r₁ ×ˢ univ) x)
      (ball M.a₀ M.r₁ ×ˢ univ) :=
    M.quadF_contDiffOn.fderivWithin hopen.uniqueDiffOn (by norm_num)
  have hcongr : ContDiffOn ℝ 1 M.dquadF (ball M.a₀ M.r₁ ×ˢ univ) :=
    hfd.congr fun x hx => (fderivWithin_of_isOpen hopen hx).symm
  exact hcongr.continuousOn

private lemma ΓVec_smul (y : Euc n) (c : ℝ) (u v : Euc n) :
    M.ΓVec y (c • u) (c • v) = (c * c) • M.ΓVec y u v := by
  ext l
  simp only [ΓVec, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma dquadF_zero (p : Euc n) (hp : p ∈ ball M.a₀ M.r₁) :
    M.dquadF (p, 0) = 0 := by
  have hnhds : ball M.a₀ M.r₁ ×ˢ (univ : Set (Euc n)) ∈ 𝓝 (p, (0 : Euc n)) := by
    rw [nhds_prod_eq]; exact Filter.prod_mem_prod (isOpen_ball.mem_nhds hp) Filter.univ_mem
  have hhd : HasFDerivAt M.quadF (M.dquadF (p, 0)) (p, 0) :=
    ((M.quadF_contDiffOn.contDiffAt hnhds).differentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
  refine ContinuousLinearMap.ext fun v => PiLp.ext fun l => ?_
  have hline : HasDerivAt (fun s : ℝ => (p + s • v.1, s • v.2)) v 0 := by
    have h1 : HasDerivAt (fun s : ℝ => p + s • v.1) v.1 0 := by
      have h := (hasDerivAt_const (0 : ℝ) p).add ((hasDerivAt_id (0 : ℝ)).smul_const v.1)
      rwa [one_smul, zero_add] at h
    have h2 : HasDerivAt (fun s : ℝ => s • v.2) v.2 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).smul_const v.2
      rwa [one_smul] at h
    exact h1.prodMk h2
  let projL : Euc n →L[ℝ] ℝ := EuclideanSpace.proj l
  have hhd_l : HasFDerivAt (fun x : Euc n × Euc n => (M.quadF x).ofLp l)
      (projL.comp (M.dquadF (p, 0))) (p + (0 : ℝ) • v.1, (0 : ℝ) • v.2) := by
    rw [zero_smul, zero_smul, add_zero]
    exact projL.hasFDerivAt.comp (p, 0) hhd
  have h1 : HasDerivAt (fun s : ℝ => (M.quadF (p + s • v.1, s • v.2)).ofLp l)
      ((M.dquadF (p, 0) v).ofLp l) 0 := by
    have hc := hhd_l.comp_hasDerivAt (0 : ℝ) hline
    simpa [Function.comp_def, projL] using hc
  have h2 : HasDerivAt (fun s : ℝ => (M.quadF (p + s • v.1, s • v.2)).ofLp l) 0 0 := by
    have heq : (fun s : ℝ => (M.quadF (p + s • v.1, s • v.2)).ofLp l) =
        fun s => (s * s) * (M.quadF (p + s • v.1, v.2)).ofLp l := by
      funext s
      have hs := congrArg (fun y : Euc n => y.ofLp l) (M.ΓVec_smul (p + s • v.1) s v.2 v.2)
      exact hs
    rw [heq]
    have hss : HasDerivAt (fun s : ℝ => s * s) 0 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))
      rwa [id_eq, mul_zero, zero_mul, add_zero] at h
    have hfv : DifferentiableAt ℝ (fun s : ℝ => (M.quadF (p + s • v.1, v.2)).ofLp l) 0 := by
      have hnhds2 : ball M.a₀ M.r₁ ×ˢ (univ : Set (Euc n)) ∈ 𝓝 (p, v.2) := by
        rw [nhds_prod_eq]; exact Filter.prod_mem_prod (isOpen_ball.mem_nhds hp) Filter.univ_mem
      have hq : DifferentiableAt ℝ (fun x : Euc n × Euc n => (M.quadF x).ofLp l) (p, v.2) :=
        projL.differentiableAt.comp (p, v.2)
          ((M.quadF_contDiffOn.contDiffAt hnhds2).differentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0))
      have hl : DifferentiableAt ℝ (fun s : ℝ => (p + s • v.1, v.2)) 0 :=
        ((differentiableAt_const p).add (differentiableAt_id.smul_const v.1)).prodMk (differentiableAt_const v.2)
      have hq' : DifferentiableAt ℝ (fun x : Euc n × Euc n => (M.quadF x).ofLp l) (p + (0 : ℝ) • v.1, v.2) := by
        rw [zero_smul, add_zero]; exact hq
      exact DifferentiableAt.comp (g := fun x : Euc n × Euc n => (M.quadF x).ofLp l)
        (f := fun s : ℝ => (p + s • v.1, v.2)) 0 hq' hl
    exact (hss.mul hfv.hasDerivAt).congr_deriv (by norm_num)
  exact h1.unique h2

private def U_V : Set (PathPair n) := {z | ∀ t : I01, (z t).1 ∈ ball M.a₀ M.r₁}

private lemma isOpen_U_V : IsOpen M.U_V := by
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

private def quadOp (z : PathPair n) : PathOne n :=
  if h : Continuous (fun t : I01 => M.quadF (z t)) then mkOfCompact ⟨_, h⟩ else 0

private lemma quadOp_apply {z : PathPair n} (hz : z ∈ M.U_V) (t : I01) :
    M.quadOp z t = M.quadF (z t) := by
  have hc : Continuous (fun s : I01 => M.quadF (z s)) :=
    M.quadF_contDiffOn.continuousOn.comp_continuous z.continuous fun s => ⟨hz s, trivial⟩
  simp [quadOp, hc]

private def dquadOp (z : PathPair n) : PathPair n →L[ℝ] PathOne n :=
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

private lemma dquadOp_apply {z : PathPair n} (hz : z ∈ M.U_V) (u : PathPair n) (t : I01) :
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
    linarith
  set R : ℝ := ‖z‖ + 1 with hR_def
  have hR : 0 < R := by linarith [norm_nonneg z]
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

private lemma quadOp_hasStrictFDerivAt {z : PathPair n} (hz : z ∈ M.U_V) :
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

private lemma dquadOp_norm_sub_lt {z : PathPair n} (hz : z ∈ M.U_V) {ε : ℝ} (hε : 0 < ε) :
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

private def psi (z : PathPair n) : PathPair n :=
  pairL (proj1L z - intOp (proj2L z), proj2L z + intOp (M.quadOp z))

private def dpsi (z : PathPair n) : PathPair n →L[ℝ] PathPair n :=
  pairL.comp ((proj1L - intOp.comp proj2L).prod (proj2L + intOp.comp (M.dquadOp z)))

private lemma psi_hasStrictFDerivAt {z : PathPair n} (hz : z ∈ M.U_V) :
    HasStrictFDerivAt M.psi (M.dpsi z) z := by
  have h1 : HasStrictFDerivAt (fun w => proj1L w - intOp (proj2L w)) (proj1L - intOp.comp proj2L) z :=
    (proj1L - intOp.comp proj2L).hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (fun w => proj2L w + intOp (M.quadOp w))
      (proj2L + intOp.comp (M.dquadOp z)) z :=
    proj2L.hasStrictFDerivAt.add (intOp.hasStrictFDerivAt.comp z (M.quadOp_hasStrictFDerivAt hz))
  exact pairL.hasStrictFDerivAt.comp z (h1.prodMk h2)

private def z₀ : PathPair n := constPairL (M.a₀, 0)

private lemma z₀_mem_U_V : M.z₀ ∈ M.U_V := fun _ => mem_ball_self M.hr₁

private lemma dpsi_z₀_eq : M.dpsi M.z₀ = (dpsi0Equiv (n := n) : PathPair n →L[ℝ] PathPair n) := by
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
    rw [hd0]
    simp

private lemma dpsi_norm_sub_le {w z : PathPair n} :
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

private lemma psi_z₀ : M.psi M.z₀ = M.z₀ := by
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

private lemma psi_hasStrictFDerivAt_z₀ :
    HasStrictFDerivAt M.psi (dpsi0Equiv (n := n) : PathPair n →L[ℝ] PathPair n) M.z₀ := by
  rw [← M.dpsi_z₀_eq]; exact M.psi_hasStrictFDerivAt M.z₀_mem_U_V

private def psiHomeo : OpenPartialHomeomorph (PathPair n) (PathPair n) :=
  M.psi_hasStrictFDerivAt_z₀.toOpenPartialHomeomorph M.psi

private def geod (p v : Euc n) : PathPair n :=
  M.psiHomeo.symm (constPairL (p, v))

private def exp (p v : Euc n) : Euc n :=
  (M.geod p v ⟨1, right_mem_Icc.mpr zero_le_one⟩).1

private lemma exists_geod_radius :
    ∃ r_g > 0,
      ∀ p ∈ ball M.a₀ r_g, ∀ v ∈ ball (0 : Euc n) r_g,
        constPairL (p, v) ∈ M.psiHomeo.target ∧
        M.geod p v ∈ M.U_V ∧
        (∃ L : PathPair n ≃L[ℝ] PathPair n,
          HasStrictFDerivAt M.psiHomeo.symm (L.symm : PathPair n →L[ℝ] PathPair n) (constPairL (p, v))) ∧
        (∀ s (hs : s ∈ Icc (0 : ℝ) 1),
          (mkOfCompact ⟨fun t => ((M.geod p v ⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩).1,
            s • (M.geod p v ⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩).2),
            by
              have hs_map : Continuous (fun t : I01 => (⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩ : I01)) :=
                Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _
              exact (continuous_fst.comp ((M.geod p v).continuous.comp hs_map)).prodMk
                ((continuous_snd.comp ((M.geod p v).continuous.comp hs_map)).const_smul s)⟩ : PathPair n)
          ∈ M.psiHomeo.source) := by
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
        have h1 : (L0inv * M.dpsi M.z₀) h = h := congrArg (fun f : PathPair n →L[ℝ] PathPair n => f h) hL0inv_mul
        change h - L0inv (M.dpsi M.z₀ h - M.dpsi z h) = L0inv (M.dpsi z h)
        rw [map_sub]
        have h2 : L0inv (M.dpsi M.z₀ h) = h := h1
        rw [h2]; abel
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
    have h2 : M.psiHomeo M.z₀ = M.z₀ := by
      change M.psi M.z₀ = M.z₀; exact M.psi_z₀
    rwa [h2] at h1
  have hpre : M.psiHomeo.target ∩ M.psiHomeo.symm ⁻¹' (ball M.z₀ (δ / 2)) ∈ 𝓝 M.z₀ :=
    Filter.inter_mem (M.psiHomeo.open_target.mem_nhds hz₀_tgt)
      (hcont_symm.preimage_mem_nhds (by rw [hsymm_z₀]; exact ball_mem_nhds _ (half_pos hδ)))
  have hconst_cont : ContinuousAt constPairL (M.a₀, (0 : Euc n)) := constPairL.continuous.continuousAt
  have hpre2 : constPairL ⁻¹' (M.psiHomeo.target ∩ M.psiHomeo.symm ⁻¹' (ball M.z₀ (δ / 2))) ∈ 𝓝 (M.a₀, (0 : Euc n)) :=
    hconst_cont.preimage_mem_nhds hpre
  obtain ⟨r_g, hr_g, hrg_sub⟩ := Metric.mem_nhds_iff.mp hpre2
  refine ⟨r_g, hr_g, fun p hp v hv => ?_⟩
  have hpv : (p, v) ∈ ball (M.a₀, (0 : Euc n)) r_g := by
    rw [Metric.mem_ball, Prod.dist_eq]
    exact max_lt hp hv
  have hmem := hrg_sub hpv
  have htgt : constPairL (p, v) ∈ M.psiHomeo.target := hmem.1
  have hgeod_ball2 : M.geod p v ∈ ball M.z₀ (δ / 2) := hmem.2
  have hgeod_ball : M.geod p v ∈ ball M.z₀ δ := Metric.ball_subset_ball (half_le_self hδ.le) hgeod_ball2
  have hgeod_good := hδ_good (M.geod p v) hgeod_ball
  refine ⟨htgt, hgeod_good.2.1, ?_, ?_⟩
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
    refine ⟨L, ?_⟩
    have hfd : HasStrictFDerivAt M.psi (L : PathPair n →L[ℝ] PathPair n) (M.geod p v) := by
      have hL : (L : PathPair n →L[ℝ] PathPair n) = M.dpsi (M.geod p v) :=
        ContinuousLinearMap.ext fun h => congrArg (fun f : PathPair n →L[ℝ] PathPair n => f h) hu
      rw [hL]
      exact M.psi_hasStrictFDerivAt hgeod_good.2.1
    exact M.psiHomeo.hasStrictFDerivAt_symm htgt hfd
  · intro s hs
    apply (hδ_good _ _).1
    rw [Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖M.geod p v - M.z₀‖ < δ / 2 := by simpa [dist_eq_norm] using hgeod_ball2
    refine lt_of_le_of_lt ((BoundedContinuousFunction.norm_le (half_pos hδ).le).mpr fun t => ?_) (half_lt_self hδ)
    let st : I01 := ⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩
    have hst : ‖M.geod p v st - M.z₀ st‖ ≤ δ / 2 :=
      ((BoundedContinuousFunction.norm_coe_le_norm (M.geod p v - M.z₀) st).trans_lt hnorm).le
    have h1 : ‖(M.geod p v st).1 - M.a₀‖ ≤ δ / 2 :=
      (norm_fst_le (M.geod p v st - M.z₀ st)).trans hst
    have h2 : ‖s • (M.geod p v st).2 - 0‖ ≤ δ / 2 := by
      rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      calc s * ‖(M.geod p v st).2‖ ≤ 1 * ‖(M.geod p v st).2‖ :=
              mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
        _ = ‖(M.geod p v st).2 - 0‖ := by simp
        _ ≤ δ / 2 := (norm_snd_le (M.geod p v st - M.z₀ st)).trans hst
    exact max_le h1 h2

/- ### Part 2B: Geodesic ODE, constant speed, homogeneity, Gauss's Lemma, normal balls -/

private def γExt (p v : Euc n) (t : ℝ) : Euc n :=
  p + intFun (proj2L (M.geod p v)) t

private def ξExt (p v : Euc n) (t : ℝ) : Euc n :=
  v - intFun (M.quadOp (M.geod p v)) t

private lemma geod_eq_ext {p v : Euc n} (htgt : constPairL (p, v) ∈ M.psiHomeo.target)
    (t : I01) :
    (M.geod p v t).1 = M.γExt p v t.1 ∧ (M.geod p v t).2 = M.ξExt p v t.1 := by
  have hpsi : M.psi (M.geod p v) = constPairL (p, v) := M.psiHomeo.right_inv htgt
  have ht := congrArg (fun z : PathPair n => z t) hpsi
  have h1 : (M.geod p v t).1 - intFun (proj2L (M.geod p v)) t.1 = p := congrArg Prod.fst ht
  have h2 : (M.geod p v t).2 + intFun (M.quadOp (M.geod p v)) t.1 = v := congrArg Prod.snd ht
  exact ⟨by simp only [γExt]; exact eq_add_of_sub_eq h1,
    by simp only [ξExt]; exact eq_sub_of_add_eq h2⟩

private lemma γExt_zero (p v : Euc n) : M.γExt p v 0 = p := by simp [γExt, intFun]
private lemma ξExt_zero (p v : Euc n) : M.ξExt p v 0 = v := by simp [ξExt, intFun]

private lemma γExt_one {p v : Euc n} (htgt : constPairL (p, v) ∈ M.psiHomeo.target) :
    M.γExt p v 1 = M.exp p v :=
  (M.geod_eq_ext htgt ⟨1, right_mem_Icc.mpr zero_le_one⟩).1.symm

private lemma γExt_hasDerivAt {p v : Euc n} (htgt : constPairL (p, v) ∈ M.psiHomeo.target)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (M.γExt p v) (M.ξExt p v t) t := by
  have h := (hasDerivAt_const t p).add (intFun_hasDerivAt (proj2L (M.geod p v)) t)
  have hval : (0 : Euc n) + proj2L (M.geod p v) (proj01 t) = M.ξExt p v t := by
    rw [zero_add]
    have hproj : proj01 t = ⟨t, ht⟩ := Set.projIcc_of_mem zero_le_one ht
    rw [hproj]
    exact (M.geod_eq_ext htgt ⟨t, ht⟩).2
  exact hval ▸ h

private lemma ξExt_hasDerivAt {p v : Euc n} (htgt : constPairL (p, v) ∈ M.psiHomeo.target)
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

private lemma geod_const_speed {p v : Euc n} (htgt : constPairL (p, v) ∈ M.psiHomeo.target)
    (hU : M.geod p v ∈ M.U_V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    M.inner (M.γExt p v t) (M.ξExt p v t) (M.ξExt p v t) = M.inner p v v := by
  let f : ℝ → ℝ := fun s => M.inner (M.γExt p v s) (M.ξExt p v s) (M.ξExt p v s)
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t, HasDerivAt f 0 s := by
    intro s hs
    have hs01 : s ∈ Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le ht.1] at hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
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

private lemma geod_homog {p v : Euc n} (htgt : constPairL (p, v) ∈ M.psiHomeo.target)
    (hU : M.geod p v ∈ M.U_V) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hsrc : (mkOfCompact ⟨fun t => ((M.geod p v ⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩).1,
        s • (M.geod p v ⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩).2),
        by
          have hs_map : Continuous (fun t : I01 => (⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩ : I01)) :=
            Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _
          exact (continuous_fst.comp ((M.geod p v).continuous.comp hs_map)).prodMk
            ((continuous_snd.comp ((M.geod p v).continuous.comp hs_map)).const_smul s)⟩ : PathPair n)
      ∈ M.psiHomeo.source) :
    M.exp p (s • v) = M.γExt p v s := by
  let z_s : PathPair n := mkOfCompact ⟨fun t =>
      ((M.geod p v ⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩).1,
        s • (M.geod p v ⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩).2),
      by
        have hs_map : Continuous (fun t : I01 => (⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩ : I01)) :=
          Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _
        exact (continuous_fst.comp ((M.geod p v).continuous.comp hs_map)).prodMk
          ((continuous_snd.comp ((M.geod p v).continuous.comp hs_map)).const_smul s)⟩
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
        have h0 : intFun (proj2L z_s) t.1 = 0 := by
          simp [intFun, proj2L, z_s]
        have hst0 : (⟨0 * t.1, hst⟩ : I01) = ⟨0, left_mem_Icc.mpr zero_le_one⟩ := by
          ext; simp
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
              rw [Set.uIcc_of_le t.2.1] at hu
              exact ⟨hu.1, hu.2.trans t.2.2⟩
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
        rw [hint1, hgeod_st.1, γExt]
        abel
      · change s • (M.geod p v st).2 + intFun (M.quadOp z_s) t.1 = s • v
        have hint2 : intFun (M.quadOp z_s) t.1 = s • intFun (M.quadOp (M.geod p v)) (s * t.1) := by
          simp only [intFun]
          have hcongr : ∫ u in (0 : ℝ)..t.1, M.quadOp z_s (proj01 u) =
              ∫ u in (0 : ℝ)..t.1, (s * s) • M.quadOp (M.geod p v) (proj01 (s * u)) := by
            refine intervalIntegral.integral_congr fun u hu => ?_
            have hu01 : u ∈ Icc (0 : ℝ) 1 := by
              rw [Set.uIcc_of_le t.2.1] at hu
              exact ⟨hu.1, hu.2.trans t.2.2⟩
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
        rw [hint2, hgeod_st.2, ξExt, smul_sub]
        abel
  have hleft : M.psiHomeo.symm (M.psiHomeo z_s) = z_s := M.psiHomeo.left_inv hsrc
  have hgeod_eq : M.geod p (s • v) = z_s := by
    change M.psiHomeo.symm (constPairL (p, s • v)) = z_s
    rw [← hpsi_zs]
    exact hleft
  have h1 := congrArg (fun z : PathPair n => (z ⟨1, right_mem_Icc.mpr zero_le_one⟩).1) hgeod_eq
  change M.exp p (s • v) = (M.geod p v ⟨s * 1, _⟩).1 at h1
  rw [h1, (M.geod_eq_ext htgt _).1]
  change M.γExt p v (s * 1) = M.γExt p v s
  rw [mul_one]

private lemma gauss_lemma {r_g : ℝ}
    (hrg : ∀ p ∈ ball M.a₀ r_g, ∀ v ∈ ball (0 : Euc n) r_g,
      constPairL (p, v) ∈ M.psiHomeo.target ∧
      M.geod p v ∈ M.U_V ∧
      (∃ L : PathPair n ≃L[ℝ] PathPair n,
        HasStrictFDerivAt M.psiHomeo.symm (L.symm : PathPair n →L[ℝ] PathPair n) (constPairL (p, v))) ∧
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1),
        (mkOfCompact ⟨fun t => ((M.geod p v ⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩).1,
          s • (M.geod p v ⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩).2),
          by
            have hs_map : Continuous (fun t : I01 => (⟨s * t.1, ⟨mul_nonneg hs.1 t.2.1, mul_le_one₀ hs.2 t.2.1 t.2.2⟩⟩ : I01)) :=
              Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _
            exact (continuous_fst.comp ((M.geod p v).continuous.comp hs_map)).prodMk
              ((continuous_snd.comp ((M.geod p v).continuous.comp hs_map)).const_smul s)⟩ : PathPair n)
        ∈ M.psiHomeo.source))
    {p v : Euc n} (hp : p ∈ ball M.a₀ r_g) (hv : v ∈ ball (0 : Euc n) r_g) (w : Euc n) :
    HasStrictFDerivAt (M.exp p) (fderiv ℝ (M.exp p) v) v ∧
    fderiv ℝ (M.exp p) v v = M.ξExt p v 1 ∧
    M.inner (M.exp p v) (fderiv ℝ (M.exp p) v v) (fderiv ℝ (M.exp p) v w) = M.inner p v w := by
  obtain ⟨htgt, hU, ⟨L, hL⟩, hhom⟩ := hrg p hp v hv
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
  -- Radial derivative: Dexp v = ξExt p v 1
  have hrad : fderiv ℝ (M.exp p) v v = M.ξExt p v 1 := by
    have h1 : HasDerivWithinAt (fun s : ℝ => M.exp p (s • v)) (fderiv ℝ (M.exp p) v v) (Icc 0 1) 1 := by
      have hsmul : HasDerivAt (fun s : ℝ => s • v) v 1 := by
        have h := (hasDerivAt_id (1 : ℝ)).smul_const v
        rwa [one_smul] at h
      have hf1 : HasFDerivAt (M.exp p) (fderiv ℝ (M.exp p) v) ((1 : ℝ) • v) := by
        rw [one_smul]; exact hexp_sfd.hasFDerivAt
      exact (hf1.comp_hasDerivAt 1 hsmul).hasDerivWithinAt
    have h2 : HasDerivWithinAt (M.γExt p v) (M.ξExt p v 1) (Icc 0 1) 1 :=
      (M.γExt_hasDerivAt htgt (right_mem_Icc.mpr zero_le_one)).hasDerivWithinAt
    have h2' : HasDerivWithinAt (fun s : ℝ => M.exp p (s • v)) (M.ξExt p v 1) (Icc 0 1) 1 :=
      h2.congr (fun s hs => M.geod_homog htgt hU hs (hhom s hs))
        (M.geod_homog htgt hU (right_mem_Icc.mpr zero_le_one) (hhom 1 (right_mem_Icc.mpr zero_le_one)))
    exact (uniqueDiffOn_Icc zero_lt_one 1 (right_mem_Icc.mpr zero_le_one)).eq_deriv _ h1 h2'
  -- Gauss inner product identity
  refine ⟨hexp_sfd, hrad, ?_⟩
  rw [hrad]
  let Jpair : PathPair n := Dgeod w
  let Jext (t : ℝ) : Euc n := intFun (proj2L Jpair) t
  let J'ext (t : ℝ) : Euc n := (Jpair (proj01 t)).2
  -- Show (Jpair t).1 = Jext t.1 by differentiating the integral equation in u at v
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
  -- Differentiate constant speed M.inner (γ(s,t)) (ξ(s,t)) (ξ(s,t)) = M.inner p (v + s•w) (v + s•w) at s=0
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
      refine h1.congr_deriv ?_
      norm_num
    have heq := (hd_lhs.congr_of_eventuallyEq hev.symm).unique hd_rhs
    have he0 := M.geod_eq_ext htgt tI
    simp only [γs, ξs, zero_smul, add_zero, he0.1, he0.2] at heq
    have hγm : M.γExt p v t ∈ ball M.a₀ M.r₁ := by rw [← he0.1]; exact hU tI
    rw [M.inner_symm hγm (J'ext t + M.ΓVec (M.γExt p v t) (Jext t) (M.ξExt p v t)) (M.ξExt p v t),
      M.ΓVec_symm hγm (Jext t) (M.ξExt p v t)] at heq
    linarith
  -- Integrate d/dt [M.inner (γ t) (ξ t) (J t) - t * M.inner p v w] = 0 on [0, 1]
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

/- ### Part 2C: Metric norm equivalence, normal balls, and annulus length lower bound -/

private lemma gnorm_smul {y : Euc n} (_hy : y ∈ ball M.a₀ M.r₁) (c : ℝ) (v : Euc n) :
    M.gnorm y (c • v) = |c| * M.gnorm y v := by
  simp only [gnorm, M.inner_smul_left, M.inner_smul_right]
  rw [← mul_assoc, Real.sqrt_mul (mul_self_nonneg c), Real.sqrt_mul_self_eq_abs]

private lemma gnorm_pos {y : Euc n} (hy : y ∈ ball M.a₀ M.r₁) {v : Euc n} (hv : v ≠ 0) :
    0 < M.gnorm y v :=
  Real.sqrt_pos.mpr (M.inner_pos hy hv)

private lemma gnorm_zero (y : Euc n) : M.gnorm y 0 = 0 := by
  simp [gnorm, M.inner_zero_left]

private lemma gnorm_continuousOn_vec {y : Euc n} : Continuous (fun v : Euc n => M.gnorm y v) := by
  refine Continuous.sqrt (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_)
  have hi : Continuous (fun v : Euc n => v.ofLp i) := (EuclideanSpace.proj i : Euc n →L[ℝ] ℝ).continuous
  have hj : Continuous (fun v : Euc n => v.ofLp j) := (EuclideanSpace.proj j : Euc n →L[ℝ] ℝ).continuous
  exact (continuous_const.mul hi).mul hj

private lemma metric_norm_bounds :
    ∃ r₂ > 0, r₂ ≤ M.r₁ ∧ ∃ m_g > 0, ∃ M_g > 0,
      ∀ y ∈ ball M.a₀ r₂, ∀ w : Euc n,
        m_g * ‖w‖ ≤ M.gnorm y w ∧ M.gnorm y w ≤ M_g * ‖w‖ := by
  have hsum_cont : ContinuousAt (fun y => ∑ i : Fin n, ∑ j : Fin n, |M.g y i j|) M.a₀ := by
    have hco : ContinuousOn (fun y => ∑ i : Fin n, ∑ j : Fin n, |M.g y i j|) (ball M.a₀ M.r₁) :=
      continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
        (M.hg_smooth i j).continuousOn.abs
    exact hco.continuousAt (isOpen_ball.mem_nhds (mem_ball_self M.hr₁))
  let C_u : ℝ := (∑ i : Fin n, ∑ j : Fin n, |M.g M.a₀ i j|) + 1
  have hCu_pos : 0 < C_u := by
    have hnn : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, |M.g M.a₀ i j| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    linarith
  obtain ⟨r_u, hr_u, hru_sub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (isOpen_ball.mem_nhds (mem_ball_self M.hr₁))
      (hsum_cont.eventually (gt_mem_nhds (lt_add_one _))))
  have hupper : ∀ y ∈ ball M.a₀ r_u, ∀ w : Euc n, M.inner y w w ≤ C_u * ‖w‖ ^ 2 := by
    intro y hy w
    have hsum_le : ∑ i : Fin n, ∑ j : Fin n, |M.g y i j| ≤ C_u := (hru_sub hy).2.le
    calc M.inner y w w
        ≤ ∑ i : Fin n, ∑ j : Fin n, |M.g y i j * w.ofLp i * w.ofLp j| :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => le_abs_self _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, |M.g y i j| * ‖w‖ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul, abs_mul, sq]
            have hi : |w.ofLp i| ≤ ‖w‖ := PiLp.norm_apply_le w i
            have hj : |w.ofLp j| ≤ ‖w‖ := PiLp.norm_apply_le w j
            have hij : |w.ofLp i| * |w.ofLp j| ≤ ‖w‖ * ‖w‖ :=
              mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)
            calc |M.g y i j| * |w.ofLp i| * |w.ofLp j|
                = |M.g y i j| * (|w.ofLp i| * |w.ofLp j|) := by ring
              _ ≤ |M.g y i j| * (‖w‖ * ‖w‖) := mul_le_mul_of_nonneg_left hij (abs_nonneg _)
      _ = (∑ i : Fin n, ∑ j : Fin n, |M.g y i j|) * ‖w‖ ^ 2 := by
            simp_rw [← Finset.sum_mul]
      _ ≤ C_u * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right hsum_le (sq_nonneg _)
  by_cases hn : n = 0
  · refine ⟨min r_u M.r₁, lt_min hr_u M.hr₁, min_le_right _ _, 1, zero_lt_one,
      Real.sqrt C_u, Real.sqrt_pos.mpr hCu_pos, fun y hy w => ?_⟩
    have hw0 : w = 0 := by ext i; exact False.elim (Nat.not_lt_zero i.1 (hn ▸ i.2))
    subst hw0
    simp [M.gnorm_zero]
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hS_ne : (Metric.sphere (0 : Euc n) 1).Nonempty :=
      ⟨e ⟨0, hn_pos⟩, by simp [e]⟩
    have hS_comp : IsCompact (Metric.sphere (0 : Euc n) 1) := isCompact_sphere 0 1
    have hQ_cont : Continuous (fun w : Euc n => M.inner M.a₀ w w) := by
      refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
      have hi : Continuous (fun w : Euc n => w.ofLp i) := (EuclideanSpace.proj i : Euc n →L[ℝ] ℝ).continuous
      have hj : Continuous (fun w : Euc n => w.ofLp j) := (EuclideanSpace.proj j : Euc n →L[ℝ] ℝ).continuous
      exact (continuous_const.mul hi).mul hj
    obtain ⟨w₀, hw₀S, hw₀_min⟩ := hS_comp.exists_isMinOn hS_ne hQ_cont.continuousOn
    have hw₀_ne : w₀ ≠ 0 := by
      intro h0
      have hnorm : ‖w₀‖ = 1 := by simpa using hw₀S
      rw [h0, norm_zero] at hnorm
      exact zero_ne_one hnorm
    set c_min : ℝ := M.inner M.a₀ w₀ w₀
    have hc_pos : 0 < c_min := M.inner_pos (mem_ball_self M.hr₁) hw₀_ne
    have hdiff_cont : ContinuousAt (fun y => ∑ i : Fin n, ∑ j : Fin n, |M.g y i j - M.g M.a₀ i j|) M.a₀ := by
      have hco : ContinuousOn (fun y => ∑ i : Fin n, ∑ j : Fin n, |M.g y i j - M.g M.a₀ i j|) (ball M.a₀ M.r₁) :=
        continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
          ((M.hg_smooth i j).continuousOn.sub continuousOn_const).abs
      exact hco.continuousAt (isOpen_ball.mem_nhds (mem_ball_self M.hr₁))
    have hdiff0 : (∑ i : Fin n, ∑ j : Fin n, |M.g M.a₀ i j - M.g M.a₀ i j|) = 0 := by simp
    have hdiff_lt : (fun y => ∑ i : Fin n, ∑ j : Fin n, |M.g y i j - M.g M.a₀ i j|) M.a₀ < c_min / 2 := by
      dsimp only; rw [hdiff0]; exact half_pos hc_pos
    obtain ⟨r_l, hr_l, hrl_sub⟩ := Metric.mem_nhds_iff.mp
      (hdiff_cont.eventually (gt_mem_nhds hdiff_lt))
    let r₂ : ℝ := min (min r_u r_l) M.r₁
    have hr₂_pos : 0 < r₂ := lt_min (lt_min hr_u hr_l) M.hr₁
    refine ⟨r₂, hr₂_pos, min_le_right _ _, Real.sqrt (c_min / 2), Real.sqrt_pos.mpr (half_pos hc_pos),
      Real.sqrt C_u, Real.sqrt_pos.mpr hCu_pos, fun y hy w => ?_⟩
    have hy_u : y ∈ ball M.a₀ r_u :=
      Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hy
    have hy_l : y ∈ ball M.a₀ r_l :=
      Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hy
    have hy_r1 : y ∈ ball M.a₀ M.r₁ := Metric.ball_subset_ball (min_le_right _ _) hy
    have hU_bd : M.gnorm y w ≤ Real.sqrt C_u * ‖w‖ := by
      rw [gnorm]
      calc Real.sqrt (M.inner y w w) ≤ Real.sqrt (C_u * ‖w‖ ^ 2) := Real.sqrt_le_sqrt (hupper y hy_u w)
        _ = Real.sqrt C_u * Real.sqrt (‖w‖ ^ 2) := Real.sqrt_mul hCu_pos.le _
        _ = Real.sqrt C_u * ‖w‖ := by rw [Real.sqrt_sq (norm_nonneg w)]
    have hL_bd : Real.sqrt (c_min / 2) * ‖w‖ ≤ M.gnorm y w := by
      by_cases hw : w = 0
      · subst hw; simp [M.gnorm_zero]
      · have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
        let u : Euc n := ‖w‖⁻¹ • w
        have huS : u ∈ Metric.sphere (0 : Euc n) 1 := by
          simp [u, norm_smul, inv_mul_cancel₀ hwn.ne']
        have hu_min : c_min ≤ M.inner M.a₀ u u := hw₀_min huS
        have hdiff_u : |M.inner y u u - M.inner M.a₀ u u| ≤ c_min / 2 := by
          have hsub : M.inner y u u - M.inner M.a₀ u u =
              ∑ i : Fin n, ∑ j : Fin n, (M.g y i j - M.g M.a₀ i j) * u.ofLp i * u.ofLp j := by
            simp only [inner, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
          rw [hsub]
          have h1 : |∑ i : Fin n, ∑ j : Fin n, (M.g y i j - M.g M.a₀ i j) * u.ofLp i * u.ofLp j| ≤
              ∑ i : Fin n, ∑ j : Fin n, |M.g y i j - M.g M.a₀ i j| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
                (Finset.sum_le_sum fun j _ => ?_))
            rw [abs_mul, abs_mul]
            have hun : ‖u‖ = 1 := by simpa using huS
            have hi : |u.ofLp i| ≤ 1 := by simpa [hun] using PiLp.norm_apply_le u i
            have hj : |u.ofLp j| ≤ 1 := by simpa [hun] using PiLp.norm_apply_le u j
            calc |M.g y i j - M.g M.a₀ i j| * |u.ofLp i| * |u.ofLp j|
                ≤ |M.g y i j - M.g M.a₀ i j| * 1 * 1 :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hi (abs_nonneg _)) hj (abs_nonneg _) (by positivity)
              _ = |M.g y i j - M.g M.a₀ i j| := by ring
          exact h1.trans (hrl_sub hy_l).le
        have hy_u_ge : c_min / 2 ≤ M.inner y u u := by
          have := (abs_sub_le_iff.mp hdiff_u).2; linarith
        have hscale : M.gnorm y w = ‖w‖ * M.gnorm y u := by
          have hw_eq : w = ‖w‖ • u := by simp [u, smul_smul, mul_inv_cancel₀ hwn.ne']
          conv_lhs => rw [hw_eq, M.gnorm_smul hy_r1, abs_of_pos hwn]
        rw [hscale, mul_comm (Real.sqrt (c_min / 2))]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hy_u_ge) hwn.le
    exact ⟨hL_bd, hU_bd⟩

private def expPair (x : Euc n × Euc n) : Euc n × Euc n := (x.1, M.exp x.1 x.2)

private def E0Equiv : (Euc n × Euc n) ≃L[ℝ] (Euc n × Euc n) :=
  { toLinearEquiv :=
      { toFun := fun x => (x.1, x.1 + x.2)
        invFun := fun x => (x.1, x.2 - x.1)
        map_add' := fun x y => Prod.ext rfl (by simp only [Prod.fst_add, Prod.snd_add]; abel)
        map_smul' := fun c x => by ext <;> simp [smul_add]
        left_inv := fun x => by ext <;> simp
        right_inv := fun x => by ext <;> simp }
    continuous_toFun := continuous_fst.prodMk (continuous_fst.add continuous_snd)
    continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_fst) }

private lemma expPair_hasStrictFDerivAt_zero :
    HasStrictFDerivAt M.expPair (E0Equiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) (M.a₀, 0) := by
  have hsymm : HasStrictFDerivAt M.psiHomeo.symm (dpsi0Equiv (n := n).symm : PathPair n →L[ℝ] PathPair n) M.z₀ := by
    have h := M.psi_hasStrictFDerivAt_z₀.to_localInverse
    rwa [M.psi_z₀] at h
  let eval1Fst : PathPair n →L[ℝ] Euc n :=
    (ContinuousLinearMap.fst ℝ (Euc n) (Euc n)).comp (evalAtL ⟨1, right_mem_Icc.mpr zero_le_one⟩)
  have hexp_sfd : HasStrictFDerivAt (fun x : Euc n × Euc n => M.exp x.1 x.2)
      (eval1Fst.comp ((dpsi0Equiv (n := n).symm : PathPair n →L[ℝ] PathPair n).comp constPairL)) (M.a₀, 0) :=
    eval1Fst.hasStrictFDerivAt.comp M.z₀ hsymm |>.comp (M.a₀, 0) constPairL.hasStrictFDerivAt
  have hpair := hasStrictFDerivAt_fst.prodMk hexp_sfd
  have hL_eq : (ContinuousLinearMap.fst ℝ (Euc n) (Euc n)).prod
      (eval1Fst.comp ((dpsi0Equiv (n := n).symm : PathPair n →L[ℝ] PathPair n).comp constPairL)) =
      (E0Equiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) := by
    refine ContinuousLinearMap.ext fun x => Prod.ext rfl ?_
    change x.1 + intFun (proj2L (constPairL x)) 1 = x.1 + x.2
    have hint : intFun (proj2L (constPairL x)) 1 = x.2 := by
      simp [intFun, proj2L, constPairL]
    rw [hint]
  exact hL_eq ▸ hpair

private def EHomeo : OpenPartialHomeomorph (Euc n × Euc n) (Euc n × Euc n) :=
  M.expPair_hasStrictFDerivAt_zero.toOpenPartialHomeomorph M.expPair

private def log (p q : Euc n) : Euc n := (M.EHomeo.symm (p, q)).2

set_option maxHeartbeats 1200000 in
private lemma exists_normal_ball :
    ∃ r_p > 0, ∃ r_v > 0, ∃ m_g > 0, ∃ M_g > 0, ∃ c₀ > 0,
      r_p ≤ M.r₁ ∧
      (∀ y ∈ ball M.a₀ r_p, ∀ w : Euc n, m_g * ‖w‖ ≤ M.gnorm y w ∧ M.gnorm y w ≤ M_g * ‖w‖) ∧
      ∀ p ∈ ball M.a₀ r_p,
        (∀ v, M.gnorm p v < r_v →
          M.exp p v ∈ ball M.a₀ M.r₁ ∧
          (∀ w : Euc n, m_g * ‖w‖ ≤ M.gnorm (M.exp p v) w ∧ M.gnorm (M.exp p v) w ≤ M_g * ‖w‖) ∧
          (p, v) ∈ M.EHomeo.source ∧
          (p, M.exp p v) ∈ M.EHomeo.target ∧
          M.log p (M.exp p v) = v ∧
          HasStrictFDerivAt (M.exp p) (fderiv ℝ (M.exp p) v) v ∧
          (∀ w : Euc n, M.inner (M.exp p v) (fderiv ℝ (M.exp p) v v) (fderiv ℝ (M.exp p) v w) = M.inner p v w) ∧
          (∀ w : Euc n, c₀ * M.gnorm p w ≤ M.gnorm (M.exp p v) (fderiv ℝ (M.exp p) v w)) ∧
          DifferentiableAt ℝ (M.log p) (M.exp p v) ∧
          ‖fderiv ℝ (M.log p) (M.exp p v)‖ ≤ 2 ∧
          (∀ s ∈ Icc (0 : ℝ) 1,
            M.exp p (s • v) = M.γExt p v s ∧
            M.γExt p v s ∈ ball M.a₀ M.r₁ ∧
            M.gnorm (M.γExt p v s) (M.ξExt p v s) = M.gnorm p v ∧
            HasDerivAt (M.γExt p v) (M.ξExt p v s) s)) ∧
        IsOpen (M.exp p '' {v | M.gnorm p v < r_v}) ∧
        ball M.a₀ r_p ⊆ M.exp p '' {v | M.gnorm p v < r_v} ∧
        (∀ r ∈ Ioo 0 r_v,
          IsOpen (M.exp p '' {v | M.gnorm p v < r}) ∧
          IsCompact (M.exp p '' {v | M.gnorm p v ≤ r})) ∧
        (∀ q ∈ M.exp p '' {v | M.gnorm p v < r_v},
          M.gnorm p (M.log p q) < r_v ∧ M.exp p (M.log p q) = q) := by
  obtain ⟨r₂, hr₂_pos, hr₂_le, m_g, hm_g, M_g, hM_g, hmet_bd⟩ := M.metric_norm_bounds
  obtain ⟨r_g, hr_g, hrg⟩ := M.exists_geod_radius
  -- Control ‖L.symm - L0inv‖ so D(expPair) is invertible and ‖D(exp p) v w‖ ≥ (1/2) ‖w‖
  let L0inv : PathPair n →L[ℝ] PathPair n := dpsi0Equiv (n := n).symm
  let E0inv : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n) := E0Equiv (n := n).symm
  have hL0n : 0 < ‖L0inv‖ + 1 := by linarith [ContinuousLinearMap.opNorm_nonneg L0inv]
  have hE0n : 0 < ‖E0inv‖ + 1 := by linarith [ContinuousLinearMap.opNorm_nonneg E0inv]
  let ε_op : ℝ := min (1 / (2 * (‖L0inv‖ + 1))) (min (1 / (4 * (‖L0inv‖ + 1) ^ 2)) (1 / (4 * (‖L0inv‖ + 1) ^ 2 * (‖E0inv‖ + 1))))
  have hε_op : 0 < ε_op := by
    refine lt_min (by positivity) (lt_min (by positivity) (by positivity))
  obtain ⟨δ_op, hδ_op, hδ_op_spec⟩ := M.dquadOp_norm_sub_lt M.z₀_mem_U_V hε_op
  have hgeod_cont0 : ContinuousAt (fun x : Euc n × Euc n => M.geod x.1 x.2) (M.a₀, 0) := by
    have hz₀_tgt : M.z₀ ∈ M.psiHomeo.target := by
      rw [← M.psi_z₀]; exact M.psi_hasStrictFDerivAt_z₀.image_mem_toOpenPartialHomeomorph_target
    have hcp0 : constPairL (M.a₀, (0 : Euc n)) = M.z₀ := rfl
    have h1 : ContinuousAt M.psiHomeo.symm (constPairL (M.a₀, (0 : Euc n))) := by
      rw [hcp0]; exact M.psiHomeo.continuousAt_symm hz₀_tgt
    exact h1.comp (constPairL.continuous.continuousAt (x := (M.a₀, (0 : Euc n))))
  have hgeod_z₀ : M.geod M.a₀ 0 = M.z₀ := by
    have hz₀_src : M.z₀ ∈ M.psiHomeo.source := M.psi_hasStrictFDerivAt_z₀.mem_toOpenPartialHomeomorph_source
    have h1 := M.psiHomeo.left_inv hz₀_src
    have h2 : M.psiHomeo M.z₀ = M.z₀ := by change M.psi M.z₀ = M.z₀; exact M.psi_z₀
    rwa [h2] at h1
  have hexp_z₀ : M.exp M.a₀ 0 = M.a₀ := by
    change (M.geod M.a₀ 0 ⟨1, right_mem_Icc.mpr zero_le_one⟩).1 = M.a₀
    rw [hgeod_z₀]; rfl
  have hexp_cont0 : ContinuousAt (fun x : Euc n × Euc n => M.exp x.1 x.2) (M.a₀, 0) := by
    let eval1Fst : PathPair n →L[ℝ] Euc n :=
      (ContinuousLinearMap.fst ℝ (Euc n) (Euc n)).comp (evalAtL ⟨1, right_mem_Icc.mpr zero_le_one⟩)
    exact eval1Fst.continuous.continuousAt.comp hgeod_cont0
  have hE_src : (M.a₀, (0 : Euc n)) ∈ M.EHomeo.source :=
    M.expPair_hasStrictFDerivAt_zero.mem_toOpenPartialHomeomorph_source
  have hE_tgt : (M.a₀, M.a₀) ∈ M.EHomeo.target := by
    dsimp only [EHomeo]
    have h := M.expPair_hasStrictFDerivAt_zero.image_mem_toOpenPartialHomeomorph_target
    simpa [expPair, hexp_z₀] using h
  have hgood_nhds :
      M.EHomeo.source ∩ (ball M.a₀ (min r_g r₂) ×ˢ ball (0 : Euc n) r_g) ∩
      (fun x : Euc n × Euc n => M.geod x.1 x.2) ⁻¹' ball M.z₀ δ_op ∩
      (fun x : Euc n × Euc n => M.exp x.1 x.2) ⁻¹' ball M.a₀ r₂ ∈ 𝓝 (M.a₀, (0 : Euc n)) := by
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem ?_ ?_) ?_) ?_
    · exact M.EHomeo.open_source.mem_nhds hE_src
    · rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (isOpen_ball.mem_nhds (mem_ball_self (lt_min hr_g hr₂_pos)))
        (isOpen_ball.mem_nhds (mem_ball_self hr_g))
    · exact hgeod_cont0.preimage_mem_nhds (by rw [hgeod_z₀]; exact ball_mem_nhds _ hδ_op)
    · exact hexp_cont0.preimage_mem_nhds (by rw [hexp_z₀]; exact ball_mem_nhds _ hr₂_pos)
  obtain ⟨r_e, hr_e, hre_sub⟩ := Metric.mem_nhds_iff.mp hgood_nhds
  let r_v : ℝ := m_g * r_e / 2
  have hr_v : 0 < r_v := by positivity
  -- Choose r_p small enough that ball a₀ r_p ×ˢ ball a₀ r_p ⊆ EHomeo.target and M.gnorm p (log p q) < r_v
  have hE_symm_a₀ : M.EHomeo.symm (M.a₀, M.a₀) = (M.a₀, 0) := by
    have h1 := M.EHomeo.left_inv hE_src
    have h2 : M.EHomeo (M.a₀, (0 : Euc n)) = (M.a₀, M.a₀) := by
      change M.expPair (M.a₀, 0) = (M.a₀, M.a₀); simp [expPair, hexp_z₀]
    rwa [h2] at h1
  have hlog_cont0 : ContinuousAt (fun x : Euc n × Euc n => M.log x.1 x.2) (M.a₀, M.a₀) :=
    continuous_snd.continuousAt.comp (M.EHomeo.continuousAt_symm hE_tgt)
  have hlog_a₀ : M.log M.a₀ M.a₀ = 0 := congrArg Prod.snd hE_symm_a₀
  have htarget_nhds :
      M.EHomeo.target ∩ (ball M.a₀ r_e ×ˢ univ) ∩
      (fun x : Euc n × Euc n => M.log x.1 x.2) ⁻¹' ball (0 : Euc n) (r_v / M_g) ∈ 𝓝 (M.a₀, M.a₀) := by
    refine Filter.inter_mem (Filter.inter_mem ?_ ?_) ?_
    · exact M.EHomeo.open_target.mem_nhds hE_tgt
    · rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (isOpen_ball.mem_nhds (mem_ball_self hr_e)) Filter.univ_mem
    · exact hlog_cont0.preimage_mem_nhds (by rw [hlog_a₀]; exact ball_mem_nhds _ (div_pos hr_v hM_g))
  obtain ⟨r_p0, hr_p0, hrp0_sub⟩ := Metric.mem_nhds_iff.mp htarget_nhds
  let r_p : ℝ := min (min r_p0 r_e) r₂
  have hr_p : 0 < r_p := lt_min (lt_min hr_p0 hr_e) hr₂_pos
  let c₀ : ℝ := m_g / (2 * M_g)
  have hc₀ : 0 < c₀ := by positivity
  have hrp_le_r₂ : r_p ≤ r₂ := min_le_right _ _
  have hrp_le_re : r_p ≤ r_e := (min_le_left _ _).trans (min_le_right _ _)
  have hrp_le_rp0 : r_p ≤ r_p0 := (min_le_left _ _).trans (min_le_left _ _)
  refine ⟨r_p, hr_p, r_v, hr_v, m_g, hm_g, M_g, hM_g, c₀, hc₀, hrp_le_r₂.trans hr₂_le,
    fun y hy w => hmet_bd y (Metric.ball_subset_ball hrp_le_r₂ hy) w, fun p hp => ?_⟩
  have hp_re : p ∈ ball M.a₀ r_e := Metric.ball_subset_ball hrp_le_re hp
  have hp_r₂ : p ∈ ball M.a₀ r₂ := Metric.ball_subset_ball hrp_le_r₂ hp
  -- Helper: any v with gnorm p v < r_v satisfies ‖v‖ < r_e and (p, v) ∈ ball (a₀, 0) r_e
  have hv_ball : ∀ v : Euc n, M.gnorm p v < r_v → (p, v) ∈ ball (M.a₀, (0 : Euc n)) r_e := by
    intro v hv
    have hvn : ‖v‖ < r_e := by
      have h1 := (hmet_bd p hp_r₂ v).1
      have h2 : m_g * ‖v‖ < m_g * (r_e / 2) := by
        have hrveq : m_g * (r_e / 2) = r_v := by dsimp only [r_v]; ring
        rw [hrveq]; exact h1.trans_lt hv
      have h3 : ‖v‖ < r_e / 2 := (mul_lt_mul_iff_right₀ hm_g).mp h2
      linarith
    rw [Metric.mem_ball, Prod.dist_eq]
    exact max_lt hp_re (by simpa [dist_zero_right] using hvn)
  -- Core properties on B_G p r_v
  have hcore : ∀ v : Euc n, M.gnorm p v < r_v →
      M.exp p v ∈ ball M.a₀ M.r₁ ∧
      (∀ w : Euc n, m_g * ‖w‖ ≤ M.gnorm (M.exp p v) w ∧ M.gnorm (M.exp p v) w ≤ M_g * ‖w‖) ∧
      (p, v) ∈ M.EHomeo.source ∧
      (p, M.exp p v) ∈ M.EHomeo.target ∧
      M.log p (M.exp p v) = v ∧
      HasStrictFDerivAt (M.exp p) (fderiv ℝ (M.exp p) v) v ∧
      (∀ w : Euc n, M.inner (M.exp p v) (fderiv ℝ (M.exp p) v v) (fderiv ℝ (M.exp p) v w) = M.inner p v w) ∧
      (∀ w : Euc n, c₀ * M.gnorm p w ≤ M.gnorm (M.exp p v) (fderiv ℝ (M.exp p) v w)) ∧
      DifferentiableAt ℝ (M.log p) (M.exp p v) ∧
      ‖fderiv ℝ (M.log p) (M.exp p v)‖ ≤ 2 ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        M.exp p (s • v) = M.γExt p v s ∧
        M.γExt p v s ∈ ball M.a₀ M.r₁ ∧
        M.gnorm (M.γExt p v s) (M.ξExt p v s) = M.gnorm p v ∧
        HasDerivAt (M.γExt p v) (M.ξExt p v s) s) := by
    intro v hv
    have hmem := hre_sub (hv_ball v hv)
    have hsrc : (p, v) ∈ M.EHomeo.source := hmem.1.1.1
    have hp_rg : p ∈ ball M.a₀ r_g := Metric.ball_subset_ball (min_le_left _ _) hmem.1.1.2.1
    have hv_rg : v ∈ ball (0 : Euc n) r_g := hmem.1.1.2.2
    have hgeod_d : dist (M.geod p v) M.z₀ < δ_op := hmem.1.2
    have hexp_r₂ : M.exp p v ∈ ball M.a₀ r₂ := hmem.2
    have hexp_r₁ : M.exp p v ∈ ball M.a₀ M.r₁ := Metric.ball_subset_ball hr₂_le hexp_r₂
    have htgt : (p, M.exp p v) ∈ M.EHomeo.target := M.EHomeo.map_source hsrc
    have hlog_eq : M.log p (M.exp p v) = v := congrArg Prod.snd (M.EHomeo.left_inv hsrc)
    obtain ⟨hpsi_tgt, hU, ⟨L, hL⟩, hhom⟩ := hrg p hp_rg v hv_rg
    -- Operator norm closeness: ‖L.symm - L0inv‖ ≤ 2 * (‖L0inv‖+1)^2 * ε_op
    have hL_eq : (L : PathPair n →L[ℝ] PathPair n) = M.dpsi (M.geod p v) := by
      have hfd1 := M.psi_hasStrictFDerivAt hU
      have hsrc_g : M.geod p v ∈ M.psiHomeo.source := M.psiHomeo.map_target hpsi_tgt
      have hpsi_g : M.psi (M.geod p v) = constPairL (p, v) := M.psiHomeo.right_inv hpsi_tgt
      have hchain : HasFDerivAt (fun x => M.psiHomeo.symm (M.psi x))
          ((L.symm : PathPair n →L[ℝ] PathPair n).comp (M.dpsi (M.geod p v))) (M.geod p v) :=
        (hpsi_g ▸ hL.hasFDerivAt).comp (M.geod p v) hfd1.hasFDerivAt
      have hev : id =ᶠ[𝓝 (M.geod p v)] (fun x => M.psiHomeo.symm (M.psi x)) := by
        filter_upwards [M.psiHomeo.open_source.mem_nhds hsrc_g] with x hx
        exact (M.psiHomeo.left_inv hx).symm
      have hid := (hchain.congr_of_eventuallyEq hev).unique (hasFDerivAt_id (M.geod p v))
      refine ContinuousLinearMap.ext fun x => ?_
      have h1 : L.symm (M.dpsi (M.geod p v) x) = x := congrArg (fun f : PathPair n →L[ℝ] PathPair n => f x) hid
      have h2 := congrArg L h1
      simpa using h2.symm
    have hdpsi_lt : ‖M.dpsi (M.geod p v) - M.dpsi M.z₀‖ < ε_op :=
      M.dpsi_norm_sub_le.trans_lt (hδ_op_spec (M.geod p v) hU hgeod_d)
    have hL_diff_lt : ‖(L : PathPair n →L[ℝ] PathPair n) - M.dpsi M.z₀‖ < ε_op := hL_eq ▸ hdpsi_lt
    have hLsymm_le : ‖(L.symm : PathPair n →L[ℝ] PathPair n)‖ ≤ 2 * (‖L0inv‖ + 1) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
      set h := L.symm y
      have hLh : L h = y := L.apply_symm_apply y
      have hL0h : L0inv (M.dpsi M.z₀ h) = h := by
        rw [M.dpsi_z₀_eq]; exact dpsi0Equiv.symm_apply_apply h
      have htri : ‖h‖ ≤ ‖L0inv‖ * ‖y‖ + ‖L0inv‖ * (ε_op * ‖h‖) := by
        calc ‖h‖ = ‖L0inv (M.dpsi M.z₀ h)‖ := by rw [hL0h]
          _ = ‖L0inv (L h) - L0inv ((L - M.dpsi M.z₀) h)‖ := by
                congr 1; rw [← map_sub]; congr 1
                change M.dpsi M.z₀ h = L h - (L h - M.dpsi M.z₀ h); abel
          _ ≤ ‖L0inv (L h)‖ + ‖L0inv ((L - M.dpsi M.z₀) h)‖ := norm_sub_le _ _
          _ ≤ ‖L0inv‖ * ‖y‖ + ‖L0inv‖ * ‖(L - M.dpsi M.z₀) h‖ := by
                rw [hLh]
                exact add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
          _ ≤ ‖L0inv‖ * ‖y‖ + ‖L0inv‖ * (ε_op * ‖h‖) := by
                gcongr
                exact (ContinuousLinearMap.le_opNorm _ _).trans
                  (mul_le_mul_of_nonneg_right hL_diff_lt.le (norm_nonneg h))
      have hhalf : ‖L0inv‖ * ε_op ≤ 1 / 2 := by
        have h1 : ε_op ≤ 1 / (2 * (‖L0inv‖ + 1)) := min_le_left _ _
        calc ‖L0inv‖ * ε_op ≤ (‖L0inv‖ + 1) * (1 / (2 * (‖L0inv‖ + 1))) :=
              mul_le_mul (le_add_of_nonneg_right zero_le_one) h1 hε_op.le hL0n.le
          _ = 1 / 2 := by field_simp [hL0n.ne']
      have htri2 : ‖h‖ ≤ ‖L0inv‖ * ‖y‖ + (1 / 2) * ‖h‖ := by
        have hmul : ‖L0inv‖ * (ε_op * ‖h‖) = (‖L0inv‖ * ε_op) * ‖h‖ := by ring
        rw [hmul] at htri
        linarith [mul_le_mul_of_nonneg_right hhalf (norm_nonneg h)]
      change ‖h‖ ≤ 2 * (‖L0inv‖ + 1) * ‖y‖
      linarith [norm_nonneg y]
    have hLsymm_diff : ‖(L.symm : PathPair n →L[ℝ] PathPair n) - L0inv‖ ≤
        2 * (‖L0inv‖ + 1) ^ 2 * ε_op := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
      have hid : (L.symm - L0inv) y = L.symm ((M.dpsi M.z₀ - L) (L0inv y)) := by
        have hL0y : M.dpsi M.z₀ (L0inv y) = y := by
          rw [M.dpsi_z₀_eq]; exact dpsi0Equiv.apply_symm_apply y
        change L.symm y - L0inv y = L.symm (M.dpsi M.z₀ (L0inv y) - L (L0inv y))
        rw [map_sub, hL0y, L.symm_apply_apply]
      rw [hid]
      have hrev : ‖M.dpsi M.z₀ - (L : PathPair n →L[ℝ] PathPair n)‖ =
          ‖(L : PathPair n →L[ℝ] PathPair n) - M.dpsi M.z₀‖ := by
        rw [show M.dpsi M.z₀ - (L : PathPair n →L[ℝ] PathPair n) = -((L : PathPair n →L[ℝ] PathPair n) - M.dpsi M.z₀) by abel,
          ContinuousLinearMap.opNorm_neg]
      calc ‖L.symm ((M.dpsi M.z₀ - L) (L0inv y))‖
          ≤ ‖(L.symm : PathPair n →L[ℝ] PathPair n)‖ * ‖(M.dpsi M.z₀ - L) (L0inv y)‖ :=
            (L.symm : PathPair n →L[ℝ] PathPair n).le_opNorm _
        _ ≤ (2 * (‖L0inv‖ + 1)) * (ε_op * ((‖L0inv‖ + 1) * ‖y‖)) := by
              refine mul_le_mul hLsymm_le ?_ (norm_nonneg _) (by positivity)
              calc ‖(M.dpsi M.z₀ - L) (L0inv y)‖
                  ≤ ‖M.dpsi M.z₀ - (L : PathPair n →L[ℝ] PathPair n)‖ * ‖L0inv y‖ := ContinuousLinearMap.le_opNorm _ _
                _ ≤ ε_op * ((‖L0inv‖ + 1) * ‖y‖) := by
                      rw [hrev]
                      refine mul_le_mul hL_diff_lt.le ?_ (norm_nonneg _) hε_op.le
                      exact (ContinuousLinearMap.le_opNorm _ _).trans
                        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg y))
        _ = 2 * (‖L0inv‖ + 1) ^ 2 * ε_op * ‖y‖ := by ring
    -- Strict derivative of expPair at (p, v) and its closeness to E0Equiv
    let eval1Fst : PathPair n →L[ℝ] Euc n :=
      (ContinuousLinearMap.fst ℝ (Euc n) (Euc n)).comp (evalAtL ⟨1, right_mem_Icc.mpr zero_le_one⟩)
    let DexpPair : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n) :=
      (ContinuousLinearMap.fst ℝ (Euc n) (Euc n)).prod
        (eval1Fst.comp ((L.symm : PathPair n →L[ℝ] PathPair n).comp constPairL))
    have hExpPair_sfd : HasStrictFDerivAt M.expPair DexpPair (p, v) :=
      hasStrictFDerivAt_fst.prodMk
        (eval1Fst.hasStrictFDerivAt.comp (constPairL (p, v)) hL |>.comp (p, v) constPairL.hasStrictFDerivAt)
    have hDexpPair_diff : ∀ x : Euc n × Euc n,
        ‖(DexpPair - (E0Equiv (n := n) : _)) x‖ ≤ 2 * (‖L0inv‖ + 1) ^ 2 * ε_op * ‖x‖ := by
      intro x
      have h1 : ((DexpPair - (E0Equiv (n := n) : _)) x).1 = 0 := sub_self x.1
      have h2 : ((DexpPair - (E0Equiv (n := n) : _)) x).2 =
          eval1Fst (((L.symm : PathPair n →L[ℝ] PathPair n) - L0inv) (constPairL x)) := by
        change ((L.symm (constPairL x)) ⟨1, _⟩).1 - (x.1 + x.2) =
          ((L.symm (constPairL x)) ⟨1, _⟩).1 - ((L0inv (constPairL x)) ⟨1, _⟩).1
        have h0 : ((L0inv (constPairL x)) ⟨1, right_mem_Icc.mpr zero_le_one⟩).1 = x.1 + x.2 := by
          change x.1 + intFun (proj2L (constPairL x)) 1 = x.1 + x.2
          simp [intFun, proj2L, constPairL]
        rw [h0]
      have hnorm2 : ‖eval1Fst (((L.symm : PathPair n →L[ℝ] PathPair n) - L0inv) (constPairL x))‖ ≤
          2 * (‖L0inv‖ + 1) ^ 2 * ε_op * ‖x‖ := by
        calc ‖(((L.symm : PathPair n →L[ℝ] PathPair n) - L0inv) (constPairL x) ⟨1, _⟩).1‖
            ≤ ‖((L.symm : PathPair n →L[ℝ] PathPair n) - L0inv) (constPairL x)‖ :=
              (norm_fst_le _).trans (BoundedContinuousFunction.norm_coe_le_norm _ _)
          _ ≤ ‖(L.symm : PathPair n →L[ℝ] PathPair n) - L0inv‖ * ‖constPairL x‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ (2 * (‖L0inv‖ + 1) ^ 2 * ε_op) * ‖x‖ := by
                refine mul_le_mul hLsymm_diff ?_ (norm_nonneg _) (by positivity)
                exact (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr fun _ => le_rfl
      exact max_le (by rw [h1, norm_zero]; positivity) (by rw [h2]; exact hnorm2)
    have hDexpPair_norm : ‖DexpPair - (E0Equiv (n := n) : _)‖ ≤ 2 * (‖L0inv‖ + 1) ^ 2 * ε_op :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) hDexpPair_diff
    -- Invertibility of DexpPair → HasStrictFDerivAt M.EHomeo.symm at (p, M.exp p v)
    have hDexpPair_unit : IsUnit DexpPair := by
      have hprod_lt : ‖E0inv * ((E0Equiv (n := n) : _) - DexpPair)‖ < 1 := by
        have hrev : ‖(E0Equiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) - DexpPair‖ =
            ‖DexpPair - (E0Equiv (n := n) : _)‖ := by
          rw [show (E0Equiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) - DexpPair =
              -(DexpPair - (E0Equiv (n := n) : _)) by abel, ContinuousLinearMap.opNorm_neg]
        have hε3 : ε_op ≤ 1 / (4 * (‖L0inv‖ + 1) ^ 2 * (‖E0inv‖ + 1)) :=
          (min_le_right _ _).trans (min_le_right _ _)
        calc ‖E0inv * ((E0Equiv (n := n) : _) - DexpPair)‖
            ≤ ‖E0inv‖ * ‖(E0Equiv (n := n) : _) - DexpPair‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ (‖E0inv‖ + 1) * (2 * (‖L0inv‖ + 1) ^ 2 * ε_op) := by
                rw [hrev]
                exact mul_le_mul (le_add_of_nonneg_right zero_le_one) hDexpPair_norm
                  (ContinuousLinearMap.opNorm_nonneg _) hE0n.le
          _ ≤ (‖E0inv‖ + 1) * (2 * (‖L0inv‖ + 1) ^ 2 * (1 / (4 * (‖L0inv‖ + 1) ^ 2 * (‖E0inv‖ + 1)))) := by
                gcongr
          _ = 1 / 2 := by field_simp [hL0n.ne', hE0n.ne']; ring
          _ < 1 := by norm_num
      have hu1 := (Units.oneSub (E0inv * ((E0Equiv (n := n) : _) - DexpPair)) hprod_lt).isUnit
      have heq1 : 1 - E0inv * ((E0Equiv (n := n) : _) - DexpPair) = E0inv * DexpPair := by
        refine ContinuousLinearMap.ext fun x => ?_
        change x - E0inv (E0Equiv x - DexpPair x) = E0inv (DexpPair x)
        rw [map_sub]
        have hcancel : E0inv (E0Equiv x) = x := E0Equiv.symm_apply_apply x
        rw [hcancel]; abel
      rw [Units.val_oneSub, heq1] at hu1
      have hE0u : IsUnit (E0Equiv (n := n) : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) :=
        ⟨⟨(E0Equiv (n := n) : _), E0inv,
          ContinuousLinearMap.ext fun x => E0Equiv.apply_symm_apply x,
          ContinuousLinearMap.ext fun x => E0Equiv.symm_apply_apply x⟩, rfl⟩
      have heq2 : (E0Equiv (n := n) : _) * (E0inv * DexpPair) = DexpPair := by
        refine ContinuousLinearMap.ext fun x => ?_
        exact E0Equiv.apply_symm_apply (DexpPair x)
      rw [← heq2]; exact hE0u.mul hu1
    obtain ⟨uE, huE⟩ := hDexpPair_unit
    let DE : (Euc n × Euc n) ≃L[ℝ] (Euc n × Euc n) :=
      { toLinearEquiv :=
          { toFun := uE.val
            invFun := uE.inv
            map_add' := map_add _
            map_smul' := map_smul _
            left_inv := fun x => congrArg (fun f : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n) => f x) uE.inv_val
            right_inv := fun x => congrArg (fun f : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n) => f x) uE.val_inv }
        continuous_toFun := uE.val.continuous
        continuous_invFun := uE.inv.continuous }
    have hDE_eq : (DE : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) = DexpPair :=
      ContinuousLinearMap.ext fun x => congrArg (fun f : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n) => f x) huE
    have hsymm_sfd : HasStrictFDerivAt M.EHomeo.symm (DE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) (p, M.exp p v) := by
      have hfd : HasStrictFDerivAt M.expPair (DE : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)) (M.EHomeo.symm (p, M.exp p v)) := by
        have hleft := M.EHomeo.left_inv hsrc
        have heq_src : M.EHomeo.symm (p, M.exp p v) = (p, v) := hleft
        rw [heq_src, hDE_eq]; exact hExpPair_sfd
      exact M.EHomeo.hasStrictFDerivAt_symm htgt hfd
    have hlog_sfd : HasStrictFDerivAt (M.log p)
        ((ContinuousLinearMap.snd ℝ (Euc n) (Euc n)).comp
          ((DE.symm : (Euc n × Euc n) →L[ℝ] (Euc n × Euc n)).comp
            (ContinuousLinearMap.inr ℝ (Euc n) (Euc n)))) (M.exp p v) := by
      have hinr : HasStrictFDerivAt (fun q : Euc n => (p, q)) (ContinuousLinearMap.inr ℝ (Euc n) (Euc n)) (M.exp p v) :=
        (hasStrictFDerivAt_const (𝕜 := ℝ) p (M.exp p v)).prodMk (hasStrictFDerivAt_id (M.exp p v))
      exact (hasStrictFDerivAt_snd (𝕜 := ℝ)).comp (M.exp p v) (hsymm_sfd.comp (M.exp p v) hinr)
    -- Lower bound ‖fderiv (exp p) v w‖ ≥ (1/2) ‖w‖ and ‖fderiv (log p) (exp p v)‖ ≤ 2
    have hgauss0 := M.gauss_lemma hrg hp_rg hv_rg (0 : Euc n)
    have hDexp_eq : ∀ w : Euc n, fderiv ℝ (M.exp p) v w = (DexpPair (0, w)).2 := by
      intro w
      have h1 : HasStrictFDerivAt (M.exp p)
          ((ContinuousLinearMap.snd ℝ (Euc n) (Euc n)).comp
            (DexpPair.comp (ContinuousLinearMap.inr ℝ (Euc n) (Euc n)))) v := by
        have hinr : HasStrictFDerivAt (fun u : Euc n => (p, u)) (ContinuousLinearMap.inr ℝ (Euc n) (Euc n)) v :=
          (hasStrictFDerivAt_const (𝕜 := ℝ) p v).prodMk (hasStrictFDerivAt_id v)
        exact (hasStrictFDerivAt_snd (𝕜 := ℝ)).comp v (hExpPair_sfd.comp v hinr)
      exact congrArg (fun f : Euc n →L[ℝ] Euc n => f w) (hgauss0.1.hasFDerivAt.unique h1.hasFDerivAt)
    have hDexp_lb : ∀ w : Euc n, (1 / 2 : ℝ) * ‖w‖ ≤ ‖fderiv ℝ (M.exp p) v w‖ := by
      intro w
      have hε2 : ε_op ≤ 1 / (4 * (‖L0inv‖ + 1) ^ 2) := (min_le_right _ _).trans (min_le_left _ _)
      have hdiff_w : ‖fderiv ℝ (M.exp p) v w - w‖ ≤ (1 / 2 : ℝ) * ‖w‖ := by
        have h1 := hDexpPair_diff (0, w)
        have h2 : ((DexpPair - (E0Equiv (n := n) : _)) (0, w)).2 = fderiv ℝ (M.exp p) v w - w := by
          rw [hDexp_eq w]; change (DexpPair (0, w)).2 - (0 + w) = _; rw [zero_add]
        have h3 : ‖fderiv ℝ (M.exp p) v w - w‖ ≤ 2 * (‖L0inv‖ + 1) ^ 2 * ε_op * ‖((0 : Euc n), w)‖ :=
          (h2 ▸ norm_snd_le _).trans h1
        have h0w : ‖((0 : Euc n), w)‖ = ‖w‖ := by simp [Prod.norm_def]
        rw [h0w] at h3
        calc ‖fderiv ℝ (M.exp p) v w - w‖ ≤ 2 * (‖L0inv‖ + 1) ^ 2 * ε_op * ‖w‖ := h3
          _ ≤ 2 * (‖L0inv‖ + 1) ^ 2 * (1 / (4 * (‖L0inv‖ + 1) ^ 2)) * ‖w‖ := by gcongr
          _ = (1 / 2 : ℝ) * ‖w‖ := by field_simp [hL0n.ne']; ring
      have htri := norm_sub_norm_le w (fderiv ℝ (M.exp p) v w)
      rw [norm_sub_rev] at htri
      linarith
    have hDlog_ub : ‖fderiv ℝ (M.log p) (M.exp p v)‖ ≤ 2 := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun y => ?_
      have hcomp_id : fderiv ℝ (M.exp p) v (fderiv ℝ (M.log p) (M.exp p v) y) = y := by
        have hev : (fun q => M.exp p (M.log p q)) =ᶠ[𝓝 (M.exp p v)] id := by
          have hq_open : (fun q : Euc n => (p, q)) ⁻¹' M.EHomeo.target ∈ 𝓝 (M.exp p v) :=
            ((continuous_const.prodMk continuous_id).continuousAt).preimage_mem_nhds
              (M.EHomeo.open_target.mem_nhds htgt)
          filter_upwards [hq_open] with q hqt
          have hr := M.EHomeo.right_inv hqt
          have h1 : (M.EHomeo.symm (p, q)).1 = p := congrArg Prod.fst hr
          have h2 : M.exp (M.EHomeo.symm (p, q)).1 (M.EHomeo.symm (p, q)).2 = q := congrArg Prod.snd hr
          simpa [log, h1] using h2
        have hchain := (hlog_eq ▸ hgauss0.1.hasFDerivAt).comp (M.exp p v) hlog_sfd.hasFDerivAt
        have heq := (hchain.congr_of_eventuallyEq hev.symm).unique (hasFDerivAt_id (M.exp p v))
        have hlog_fd : fderiv ℝ (M.log p) (M.exp p v) = _ := hlog_sfd.hasFDerivAt.fderiv
        rw [hlog_fd]
        simpa [hlog_eq] using congrArg (fun f : Euc n →L[ℝ] Euc n => f y) heq
      have hlb := hDexp_lb (fderiv ℝ (M.log p) (M.exp p v) y)
      rw [hcomp_id] at hlb
      linarith
    refine ⟨hexp_r₁, fun w => hmet_bd (M.exp p v) hexp_r₂ w, hsrc, htgt, hlog_eq,
      hgauss0.1, fun w => (M.gauss_lemma hrg hp_rg hv_rg w).2.2, ?_,
      hlog_sfd.hasFDerivAt.differentiableAt, hDlog_ub, ?_⟩
    · intro w
      calc c₀ * M.gnorm p w
          ≤ c₀ * (M_g * ‖w‖) := mul_le_mul_of_nonneg_left (hmet_bd p hp_r₂ w).2 hc₀.le
        _ = m_g * ((1 / 2 : ℝ) * ‖w‖) := by simp only [c₀]; field_simp [hM_g.ne']
        _ ≤ m_g * ‖fderiv ℝ (M.exp p) v w‖ := mul_le_mul_of_nonneg_left (hDexp_lb w) hm_g.le
        _ ≤ M.gnorm (M.exp p v) (fderiv ℝ (M.exp p) v w) := (hmet_bd (M.exp p v) hexp_r₂ _).1
    · intro s hs
      have hγm : M.γExt p v s ∈ ball M.a₀ M.r₁ := by
        rw [← (M.geod_eq_ext hpsi_tgt ⟨s, hs⟩).1]; exact hU ⟨s, hs⟩
      refine ⟨M.geod_homog hpsi_tgt hU hs (hhom s hs), hγm, ?_, M.γExt_hasDerivAt hpsi_tgt hs⟩
      simp only [gnorm, M.geod_const_speed hpsi_tgt hU hs]
  -- Openness of exp p '' {gnorm p v < r} and compactness of exp p '' {gnorm p v ≤ r}
  have hexp_open_ball : ∀ r ∈ Ioc 0 r_v, IsOpen (M.exp p '' {v | M.gnorm p v < r}) := by
    intro r ⟨hr0, hrrv⟩
    have heq : M.exp p '' {v | M.gnorm p v < r} =
        {q : Euc n | (p, q) ∈ M.EHomeo.target ∧ M.gnorm p (M.log p q) < r} := by
      ext q
      constructor
      · rintro ⟨v, hv, rfl⟩
        have hc := hcore v (hv.trans_le hrrv)
        exact ⟨hc.2.2.2.1, by rw [hc.2.2.2.2.1]; exact hv⟩
      · rintro ⟨hqt, hlt⟩
        have hr := M.EHomeo.right_inv hqt
        have h1 : (M.EHomeo.symm (p, q)).1 = p := congrArg Prod.fst hr
        have h2 : M.exp p (M.log p q) = q := by
          have h2' : M.exp (M.EHomeo.symm (p, q)).1 (M.EHomeo.symm (p, q)).2 = q := congrArg Prod.snd hr
          simpa [log, h1] using h2'
        exact ⟨M.log p q, hlt, h2⟩
    rw [heq]
    have hopen1 : IsOpen {q : Euc n | (p, q) ∈ M.EHomeo.target} :=
      M.EHomeo.open_target.preimage (continuous_const.prodMk continuous_id)
    have hcont_on : ContinuousOn (fun q : Euc n => M.gnorm p (M.log p q)) {q | (p, q) ∈ M.EHomeo.target} :=
      M.gnorm_continuousOn_vec.comp_continuousOn
        (continuous_snd.comp_continuousOn (M.EHomeo.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn
          fun q hq => hq))
    rw [isOpen_iff_mem_nhds]
    rintro q ⟨hqt, hlt⟩
    have h1 := hopen1.mem_nhds hqt
    have h2 : (fun q => M.gnorm p (M.log p q)) ⁻¹' Iio r ∈ 𝓝 q :=
      (hcont_on.continuousAt h1).preimage_mem_nhds (isOpen_Iio.mem_nhds hlt)
    exact Filter.inter_mem h1 h2
  refine ⟨hcore, hexp_open_ball r_v ⟨hr_v, le_rfl⟩, ?_, ?_, ?_⟩
  · intro q hq
    have hpq : (p, q) ∈ ball (M.a₀, M.a₀) r_p0 := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt (Metric.ball_subset_ball hrp_le_rp0 hp) (Metric.ball_subset_ball hrp_le_rp0 hq)
    have hmem := hrp0_sub hpq
    have hqt : (p, q) ∈ M.EHomeo.target := hmem.1.1
    have hlog_lt : ‖M.log p q‖ < r_v / M_g := by simpa [dist_zero_right] using hmem.2
    have hgn : M.gnorm p (M.log p q) < r_v :=
      (hmet_bd p hp_r₂ (M.log p q)).2.trans_lt (by rwa [← lt_div_iff₀' hM_g])
    have hr := M.EHomeo.right_inv hqt
    have h1 : (M.EHomeo.symm (p, q)).1 = p := congrArg Prod.fst hr
    have h2 : M.exp p (M.log p q) = q := by
      have h2' : M.exp (M.EHomeo.symm (p, q)).1 (M.EHomeo.symm (p, q)).2 = q := congrArg Prod.snd hr
      simpa [log, h1] using h2'
    exact ⟨M.log p q, hgn, h2⟩
  · intro r ⟨hr0, hrrv⟩
    refine ⟨hexp_open_ball r ⟨hr0, hrrv.le⟩, ?_⟩
    have hcomp_v : IsCompact {v : Euc n | M.gnorm p v ≤ r} := by
      refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Euc n) (r / m_g)) ?_ ?_
      · exact isClosed_Iic.preimage M.gnorm_continuousOn_vec
      · intro v hv
        rw [Metric.mem_closedBall, dist_zero_right]
        have h1 := (hmet_bd p hp_r₂ v).1
        rw [le_div_iff₀' hm_g]
        exact h1.trans hv
    have hcont_exp : ContinuousOn (M.exp p) {v : Euc n | M.gnorm p v ≤ r} :=
      fun v hv => ((hcore v (lt_of_le_of_lt hv hrrv)).2.2.2.2.2.1.hasFDerivAt.continuousAt).continuousWithinAt
    exact hcomp_v.image_of_continuousOn hcont_exp
  · rintro q ⟨v, hv, rfl⟩
    have hc := hcore v hv
    rw [hc.2.2.2.2.1]
    exact ⟨hv, rfl⟩

end LocalMetric

private lemma sqrt_sq_add_sq_le_integral {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b)
    (hfg : IntervalIntegrable (fun t => Real.sqrt ((f t) ^ 2 + (g t) ^ 2)) MeasureTheory.volume a b) :
    Real.sqrt ((∫ t in a..b, f t) ^ 2 + (∫ t in a..b, g t) ^ 2) ≤
      ∫ t in a..b, Real.sqrt ((f t) ^ 2 + (g t) ^ 2) := by
  set A : ℝ := ∫ t in a..b, f t
  set B : ℝ := ∫ t in a..b, g t
  set R : ℝ := Real.sqrt (A ^ 2 + B ^ 2)
  by_cases hR : R = 0
  · rw [hR]
    exact intervalIntegral.integral_nonneg hab fun t _ => Real.sqrt_nonneg _
  · have hR_pos : 0 < R := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hR)
    have hRsq : R ^ 2 = A ^ 2 + B ^ 2 := Real.sq_sqrt (by positivity)
    have hpt : ∀ t ∈ Icc a b, A * f t + B * g t ≤ R * Real.sqrt ((f t) ^ 2 + (g t) ^ 2) := by
      intro t _
      have hsq : (A * f t + B * g t) ^ 2 ≤ (R * Real.sqrt ((f t) ^ 2 + (g t) ^ 2)) ^ 2 := by
        rw [mul_pow, hRsq, Real.sq_sqrt (by positivity)]
        nlinarith [sq_nonneg (A * g t - B * f t)]
      have hnn : 0 ≤ R * Real.sqrt ((f t) ^ 2 + (g t) ^ 2) := mul_nonneg hR_pos.le (Real.sqrt_nonneg _)
      exact le_of_sq_le_sq hsq hnn
    have hint : ∫ t in a..b, (A * f t + B * g t) ≤
        ∫ t in a..b, (R * Real.sqrt ((f t) ^ 2 + (g t) ^ 2)) :=
      intervalIntegral.integral_mono_on hab ((hf.const_mul A).add (hg.const_mul B)) (hfg.const_mul R) hpt
    rw [intervalIntegral.integral_add (hf.const_mul A) (hg.const_mul B),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hint
    have hR2 : R * R ≤ R * ∫ t in a..b, Real.sqrt ((f t) ^ 2 + (g t) ^ 2) := by
      nlinarith [hRsq]
    exact le_of_mul_le_mul_left hR2 hR_pos

end GeodesicFlow

end OMA.Hilbert5H2


namespace OMA.Hilbert5H2

section ManifoldPullback

open Metric Set Filter Topology MeasureTheory Manifold
open scoped Manifold ContDiff Bundle ENNReal RealInnerProductSpace Classical

private def basisVec {n : ℕ} (i : Fin n) : Euc n := EuclideanSpace.single i (1 : ℝ)

private lemma pullback_metric_exists {n : ℕ} {X : Type} [MetricSpace X]
    [ChartedSpace (Euc n) X] [IsManifold (𝓡 n) ∞ X]
    [hRB : Bundle.RiemannianBundle (fun x : X => TangentSpace (𝓡 n) x)]
    [hCRB : IsContMDiffRiemannianBundle (𝓡 n) ∞ (Euc n) (fun x : X => TangentSpace (𝓡 n) x)]
    (x₀ : X) :
    let φ := chartAt (Euc n) x₀
    let a₀ := φ x₀
    let g : Euc n → Fin n → Fin n → ℝ := fun y i j =>
      ⟪(trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm y) (basisVec i),
       (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm y) (basisVec j)⟫
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
    have h1 : ContMDiffAt (𝓡 n) 𝓘(ℝ, Euc n →L[ℝ] Euc n →L[ℝ] ℝ) 3 Gchart x₀ :=
      hGchart_md.of_le hle
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
    have hu_exp : u = ∑ i, u.ofLp i • basisVec i := by ext m; simp [basisVec, Pi.single_apply]
    have hv_exp : v = ∑ j, v.ofLp j • basisVec j := by ext m; simp [basisVec, Pi.single_apply]
    conv_rhs => rw [hu_exp, hv_exp]
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, g]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine ⟨r₁, hr₁, hr₁_tgt, ?_, ?_, hinner_eq, ?_⟩
  · intro i j
    have heval : ContDiffOn ℝ 3 (fun y => Gchart (φ.symm y) (basisVec i) (basisVec j)) (ball a₀ r₁) :=
      ((hu_cd.mono hr₁_u).clm_apply contDiffOn_const).clm_apply contDiffOn_const
    refine heval.congr fun y hy => ?_
    exact (hGchart_val (φ.symm y) (φ.map_target (hr₁_tgt hy)) (basisVec i) (basisVec j)).symm
  · intro y _ i j
    exact real_inner_comm _ _
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

private lemma pathELength_eq_ofReal_integral {n : ℕ} {X : Type} [MetricSpace X]
    [ChartedSpace (Euc n) X] [IsManifold (𝓡 n) ∞ X]
    [hRB : Bundle.RiemannianBundle (fun x : X => TangentSpace (𝓡 n) x)]
    [_hCRB : IsContMDiffRiemannianBundle (𝓡 n) ∞ (Euc n) (fun x : X => TangentSpace (𝓡 n) x)]
    (x₀ : X) {r₁ : ℝ} (hr₁_tgt : ball (chartAt (Euc n) x₀ x₀) r₁ ⊆ (chartAt (Euc n) x₀).target)
    {g : Euc n → Fin n → Fin n → ℝ}
    (hg_smooth : ∀ i j, ContDiffOn ℝ 3 (fun y => g y i j) (ball (chartAt (Euc n) x₀ x₀) r₁))
    (hinner : ∀ y ∈ ball (chartAt (Euc n) x₀ x₀) r₁, ∀ u v : Euc n,
      ∑ i, ∑ j, g y i j * u.ofLp i * v.ofLp j =
        ⟪(trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ ((chartAt (Euc n) x₀).symm y) u,
         (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ ((chartAt (Euc n) x₀).symm y) v⟫)
    {a b : ℝ} (hab : a < b) {γ : ℝ → X} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b))
    (hγ_in : ∀ t ∈ Icc a b, γ t ∈ (chartAt (Euc n) x₀).symm '' ball (chartAt (Euc n) x₀ x₀) r₁) :
    let φ := chartAt (Euc n) x₀
    let η : ℝ → Euc n := φ ∘ γ
    ContDiffOn ℝ 1 η (Icc a b) ∧
    (∀ t ∈ Icc a b, η t ∈ ball (φ x₀) r₁ ∧ φ.symm (η t) = γ t) ∧
    pathELength (𝓡 n) γ a b =
      ENNReal.ofReal (∫ t in a..b, Real.sqrt (∑ i, ∑ j, g (η t) i j *
        (derivWithin η (Icc a b) t).ofLp i * (derivWithin η (Icc a b) t).ofLp j)) := by
  intro φ η
  have hη_mem : ∀ t ∈ Icc a b, η t ∈ ball (φ x₀) r₁ ∧ φ.symm (η t) = γ t := by
    intro t ht
    obtain ⟨y, hy, hyγ⟩ := hγ_in t ht
    have hy_tgt : y ∈ φ.target := hr₁_tgt hy
    have hηt : η t = y := by
      change φ (γ t) = y
      rw [← hyγ, φ.right_inv hy_tgt]
    rw [hηt]
    exact ⟨hy, hyγ⟩
  have hγ_src : MapsTo γ (Icc a b) φ.source := fun t ht => by
    obtain ⟨y, hy, hyγ⟩ := hγ_in t ht
    rw [← hyγ]
    exact φ.map_target (hr₁_tgt hy)
  have hη_cd : ContDiffOn ℝ 1 η (Icc a b) := by
    have hφ_md : ContMDiffOn (𝓡 n) (𝓡 n) 1 φ φ.source :=
      (contMDiffOn_chart (I := 𝓡 n) (H := Euc n) (x := x₀)).of_le (by
        change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
    have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 (φ ∘ γ) (Icc a b) := hφ_md.comp hγ hγ_src
    exact contMDiffOn_iff_contDiffOn.mp hcomp
  refine ⟨hη_cd, hη_mem, ?_⟩
  let speed : ℝ → ℝ := fun t => Real.sqrt (∑ i, ∑ j, g (η t) i j *
    (derivWithin η (Icc a b) t).ofLp i * (derivWithin η (Icc a b) t).ofLp j)
  have hspeed_cont : ContinuousOn speed (Icc a b) := by
    have hderiv_cont : ContinuousOn (derivWithin η (Icc a b)) (Icc a b) := by
      have hfd := hη_cd.continuousOn_fderivWithin (uniqueDiffOn_Icc hab) le_rfl
      have heq : EqOn (derivWithin η (Icc a b)) (fun t => fderivWithin ℝ η (Icc a b) t 1) (Icc a b) :=
        fun t _ => (fderivWithin_derivWithin (f := η) (s := Icc a b) (x := t)).symm
      exact ((ContinuousLinearMap.apply ℝ (Euc n) (1 : ℝ)).continuous.comp_continuousOn hfd).congr heq
    refine ContinuousOn.sqrt (continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_)
    have hg_c : ContinuousOn (fun t => g (η t) i j) (Icc a b) :=
      (hg_smooth i j).continuousOn.comp hη_cd.continuousOn (fun t ht => (hη_mem t ht).1)
    have hdi : ContinuousOn (fun t => (derivWithin η (Icc a b) t).ofLp i) (Icc a b) :=
      (EuclideanSpace.proj i : Euc n →L[ℝ] ℝ).continuous.comp_continuousOn hderiv_cont
    have hdj : ContinuousOn (fun t => (derivWithin η (Icc a b) t).ofLp j) (Icc a b) :=
      (EuclideanSpace.proj j : Euc n →L[ℝ] ℝ).continuous.comp_continuousOn hderiv_cont
    exact (hg_c.mul hdi).mul hdj
  have hspeed_int : IntegrableOn speed (Ioo a b) volume :=
    (hspeed_cont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hpt : ∀ t ∈ Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (φ.symm ∘ η) t 1‖ₑ = ENNReal.ofReal (speed t) := by
    intro t ht
    have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht
    have hnhds : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hη_da : DifferentiableAt ℝ η t :=
      (hη_cd.contDiffAt hnhds).differentiableAt (by simp)
    have hsymm_md : MDifferentiableAt (𝓡 n) (𝓡 n) φ.symm (η t) := by
      have hmem : (extChartAt (𝓡 n) x₀).target ∈ 𝓝 (η t) := by
        simpa [extChartAt_target] using φ.open_target.mem_nhds (hr₁_tgt (hη_mem t htI).1)
      exact ((contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := (∞ : WithTop ℕ∞)) x₀ (η t)
        (by simpa [extChartAt_target] using hr₁_tgt (hη_mem t htI).1)).contMDiffAt hmem).mdifferentiableAt (by simp)
    have hη_md : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) η t := mdifferentiableAt_iff_differentiableAt.mpr hη_da
    have hmf : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (φ.symm ∘ η) t =
        (mfderiv (𝓡 n) (𝓡 n) φ.symm (η t)).comp (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η t) :=
      mfderiv_comp t hsymm_md hη_md
    have hsymm_eq : mfderiv (𝓡 n) (𝓡 n) φ.symm (η t) =
        (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm (η t)) := by
      have hsrc : φ.symm (η t) ∈ φ.source := φ.map_target (hr₁_tgt (hη_mem t htI).1)
      have h1 := TangentBundle.symmL_trivializationAt (I := 𝓡 n) (x₀ := x₀) (x := φ.symm (η t)) hsrc
      have h2 : extChartAt (𝓡 n) x₀ (φ.symm (η t)) = η t := φ.right_inv (hr₁_tgt (hη_mem t htI).1)
      have h3 : mfderivWithin (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x₀).symm (range (𝓡 n)) (η t) =
          mfderiv (𝓡 n) (𝓡 n) φ.symm (η t) := by
        rw [show range (𝓡 n) = univ by simp, mfderivWithin_univ]; rfl
      rw [h1, h2, h3]
    have hη_d1 : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η t 1 = derivWithin η (Icc a b) t := by
      have hfd : fderiv ℝ η t 1 = deriv η t := rfl
      rw [mfderiv_eq_fderiv]
      exact hfd.trans (derivWithin_of_mem_nhds hnhds).symm
    have hvec : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (φ.symm ∘ η) t 1 =
        (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm (η t)) (derivWithin η (Icc a b) t) := by
      rw [hmf, ContinuousLinearMap.comp_apply, hsymm_eq, hη_d1]; rfl
    have hnorm : ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (φ.symm ∘ η) t 1‖ = speed t := by
      rw [hvec, norm_eq_sqrt_real_inner, ← hinner (η t) (hη_mem t htI).1]
    rw [← ofReal_norm, hnorm]
  rw [pathELength_congr_Ioo (γ' := φ.symm ∘ η) (fun t ht => (hη_mem t (Ioo_subset_Icc_self ht)).2.symm),
    pathELength_eq_lintegral_mfderiv_Ioo, setLIntegral_congr_fun measurableSet_Ioo hpt,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hspeed_int
      (Filter.Eventually.of_forall fun t => Real.sqrt_nonneg _),
    intervalIntegral.integral_of_le hab.le, MeasureTheory.restrict_Ioo_eq_restrict_Ioc]


end ManifoldPullback

end OMA.Hilbert5H2

/- ### Part 4: Annulus length lower bound, normal-ball distance, ray uniqueness, and unique continuation -/

namespace OMA.Hilbert5H2

section AnnulusAndContinuation

open Metric Set Filter Topology MeasureTheory Manifold
open scoped Manifold ContDiff Bundle ENNReal RealInnerProductSpace Classical

private lemma annulus_length_ge {n : ℕ} (M : LocalMetric n)
    {p : Euc n} (hp_r1 : p ∈ ball M.a₀ M.r₁) {r_v m_g M_g c₀ : ℝ}
    (_hrv : 0 < r_v) (hm_g : 0 < m_g) (hc₀ : 0 < c₀)
    (hmet_p : ∀ w : Euc n, m_g * ‖w‖ ≤ M.gnorm p w ∧ M.gnorm p w ≤ M_g * ‖w‖)
    (hcore : ∀ v, M.gnorm p v < r_v →
      M.exp p v ∈ ball M.a₀ M.r₁ ∧
      (∀ w : Euc n, m_g * ‖w‖ ≤ M.gnorm (M.exp p v) w ∧ M.gnorm (M.exp p v) w ≤ M_g * ‖w‖) ∧
      (p, v) ∈ M.EHomeo.source ∧
      (p, M.exp p v) ∈ M.EHomeo.target ∧
      M.log p (M.exp p v) = v ∧
      HasStrictFDerivAt (M.exp p) (fderiv ℝ (M.exp p) v) v ∧
      (∀ w : Euc n, M.inner (M.exp p v) (fderiv ℝ (M.exp p) v v) (fderiv ℝ (M.exp p) v w) = M.inner p v w) ∧
      (∀ w : Euc n, c₀ * M.gnorm p w ≤ M.gnorm (M.exp p v) (fderiv ℝ (M.exp p) v w)) ∧
      DifferentiableAt ℝ (M.log p) (M.exp p v) ∧
      ‖fderiv ℝ (M.log p) (M.exp p v)‖ ≤ 2 ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        M.exp p (s • v) = M.γExt p v s ∧
        M.γExt p v s ∈ ball M.a₀ M.r₁ ∧
        M.gnorm (M.γExt p v s) (M.ξExt p v s) = M.gnorm p v ∧
        HasDerivAt (M.γExt p v) (M.ξExt p v s) s))
    (hW_open : IsOpen (M.exp p '' {v | M.gnorm p v < r_v}))
    (hW_log : ∀ q ∈ M.exp p '' {v | M.gnorm p v < r_v},
      M.gnorm p (M.log p q) < r_v ∧ M.exp p (M.log p q) = q)
    {a b : ℝ} (hab : a ≤ b) {r_lo : ℝ} (hr_lo : 0 < r_lo)
    {η : ℝ → Euc n} (hη : ContDiffOn ℝ 1 η (Icc a b))
    (hη_in : ∀ t ∈ Icc a b, η t ∈ M.exp p '' {v | M.gnorm p v < r_v} ∧
      r_lo ≤ M.gnorm p (M.log p (η t))) :
    let v := fun t => M.log p (η t)
    let ρ := fun t => M.gnorm p (v t)
    let θ := fun t => (ρ t)⁻¹ • v t
    Real.sqrt ((ρ b - ρ a) ^ 2 + (c₀ * r_lo * m_g * ‖θ b - θ a‖) ^ 2) ≤
      ∫ t in a..b, M.gnorm (η t) (derivWithin η (Icc a b) t) := by
  intro v ρ θ
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  -- Core helpers on Icc a b
  have hv_lt : ∀ t ∈ Icc a b, M.gnorm p (v t) < r_v :=
    fun t ht => (hW_log (η t) (hη_in t ht).1).1
  have hexp_v : ∀ t ∈ Icc a b, M.exp p (v t) = η t :=
    fun t ht => (hW_log (η t) (hη_in t ht).1).2
  have hρ_ge : ∀ t ∈ Icc a b, r_lo ≤ ρ t := fun t ht => (hη_in t ht).2
  have hρ_pos : ∀ t ∈ Icc a b, 0 < ρ t := fun t ht => hr_lo.trans_le (hρ_ge t ht)
  -- Continuity of v, ρ, θ on Icc a b
  have hlog_ca : ∀ t ∈ Icc a b, ContinuousAt (M.log p) (η t) := by
    intro t ht
    have hc := hcore (v t) (hv_lt t ht)
    rw [hexp_v t ht] at hc
    exact hc.2.2.2.2.2.2.2.2.1.continuousAt
  have hv_cont : ContinuousOn v (Icc a b) := fun t ht =>
    (hlog_ca t ht).comp_continuousWithinAt (hη.continuousOn t ht)
  have hρ_cont : ContinuousOn ρ (Icc a b) := M.gnorm_continuousOn_vec.comp_continuousOn hv_cont
  have hθ_cont : ContinuousOn θ (Icc a b) :=
    (hρ_cont.inv₀ fun t ht => (hρ_pos t ht).ne').smul hv_cont
  -- Continuity and integrability of speed
  let speed : ℝ → ℝ := fun t => M.gnorm (η t) (derivWithin η (Icc a b) t)
  have hderiv_cont : ContinuousOn (derivWithin η (Icc a b)) (Icc a b) :=
    hη.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl
  have hη_r1 : ∀ t ∈ Icc a b, η t ∈ ball M.a₀ M.r₁ := by
    intro t ht
    have hc := hcore (v t) (hv_lt t ht)
    rw [hexp_v t ht] at hc
    exact hc.1
  have hspeed_cont : ContinuousOn speed (Icc a b) := by
    have hsum : ContinuousOn (fun t => M.inner (η t) (derivWithin η (Icc a b) t) (derivWithin η (Icc a b) t)) (Icc a b) := by
      refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
      have hg : ContinuousOn (fun t => M.g (η t) i j) (Icc a b) :=
        (M.hg_smooth i j).continuousOn.comp hη.continuousOn hη_r1
      have hd_i : ContinuousOn (fun t => (derivWithin η (Icc a b) t).ofLp i) (Icc a b) :=
        (EuclideanSpace.proj i : Euc n →L[ℝ] ℝ).continuous.comp_continuousOn hderiv_cont
      have hd_j : ContinuousOn (fun t => (derivWithin η (Icc a b) t).ofLp j) (Icc a b) :=
        (EuclideanSpace.proj j : Euc n →L[ℝ] ℝ).continuous.comp_continuousOn hderiv_cont
      exact (hg.mul hd_i).mul hd_j
    exact hsum.sqrt
  have hspeed_int : IntervalIntegrable speed MeasureTheory.volume a b :=
    hspeed_cont.intervalIntegrable_of_Icc hab
  -- Pointwise derivatives on Ioo a b and Gauss's Lemma bound
  let u : ℝ → Euc n := fun t => fderiv ℝ (M.log p) (η t) (derivWithin η (Icc a b) t)
  let ρ' : ℝ → ℝ := fun t => M.inner p (v t) (u t) / ρ t
  let u_tan : ℝ → Euc n := fun t => u t - (ρ' t / ρ t) • v t
  let θ' : ℝ → Euc n := fun t => (ρ t)⁻¹ • u_tan t
  have hpt_all : ∀ t ∈ Ioo a b,
      HasDerivAt v (u t) t ∧
      HasDerivAt ρ (ρ' t) t ∧
      HasDerivAt θ (θ' t) t ∧
      Real.sqrt ((ρ' t) ^ 2 + (c₀ * r_lo * m_g * ‖θ' t‖) ^ 2) ≤ speed t := by
    intro t ht
    have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht
    have hnhds : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hη_da : DifferentiableAt ℝ η t :=
      (hη.differentiableOn one_ne_zero).differentiableAt hnhds
    have hη_hd : HasDerivAt η (derivWithin η (Icc a b) t) t := by
      rw [derivWithin_of_mem_nhds hnhds]
      exact hη_da.hasDerivAt
    have hc := hcore (v t) (hv_lt t htI)
    have hlog_da : DifferentiableAt ℝ (M.log p) (η t) := by
      rw [← hexp_v t htI]; exact hc.2.2.2.2.2.2.2.2.1
    have hv_hd : HasDerivAt v (u t) t := hlog_da.hasFDerivAt.comp_hasDerivAt t hη_hd
    -- Differentiating exp p ∘ v = η near t gives Dexp (v t) (u t) = derivWithin η (Icc a b) t
    have hDexp_u : fderiv ℝ (M.exp p) (v t) (u t) = derivWithin η (Icc a b) t := by
      have hchain : HasDerivAt (fun s => M.exp p (v s)) (fderiv ℝ (M.exp p) (v t) (u t)) t :=
        hc.2.2.2.2.2.1.hasFDerivAt.comp_hasDerivAt t hv_hd
      have hev : (fun s => M.exp p (v s)) =ᶠ[𝓝 t] η := by
        have hopen_s : η ⁻¹' (M.exp p '' {w | M.gnorm p w < r_v}) ∈ 𝓝 t :=
          hη_da.continuousAt.preimage_mem_nhds (hW_open.mem_nhds (hη_in t htI).1)
        filter_upwards [hopen_s] with s hs
        exact (hW_log (η s) hs).2
      exact (hchain.congr_of_eventuallyEq hev.symm).unique hη_hd
    -- HasDerivAt for ρ
    have hinner_hd : HasDerivAt (fun s => M.inner p (v s) (v s)) (2 * M.inner p (v t) (u t)) t := by
      have hterm : ∀ i j : Fin n, HasDerivAt (fun s => M.g p i j * (v s).ofLp i * (v s).ofLp j)
          (M.g p i j * (u t).ofLp i * (v t).ofLp j + M.g p i j * (v t).ofLp i * (u t).ofLp j) t := by
        intro i j
        have hi : HasDerivAt (fun s => (v s).ofLp i) ((u t).ofLp i) t :=
          (EuclideanSpace.proj i : Euc n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hv_hd
        have hj : HasDerivAt (fun s => (v s).ofLp j) ((u t).ofLp j) t :=
          (EuclideanSpace.proj j : Euc n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hv_hd
        have hmul := (hi.const_mul (M.g p i j)).fun_mul hj
        simpa [mul_assoc, mul_left_comm, mul_comm, add_comm] using hmul
      have hsum := HasDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) =>
        HasDerivAt.fun_sum fun j (_ : j ∈ Finset.univ) => hterm i j
      have hsym : ∑ i : Fin n, ∑ j : Fin n, (M.g p i j * (u t).ofLp i * (v t).ofLp j +
          M.g p i j * (v t).ofLp i * (u t).ofLp j) = 2 * M.inner p (v t) (u t) := by
        simp only [Finset.sum_add_distrib]
        have h1 : ∑ i : Fin n, ∑ j : Fin n, M.g p i j * (u t).ofLp i * (v t).ofLp j =
            M.inner p (u t) (v t) := rfl
        have h2 : ∑ i : Fin n, ∑ j : Fin n, M.g p i j * (v t).ofLp i * (u t).ofLp j =
            M.inner p (v t) (u t) := rfl
        rw [h1, h2, M.inner_symm hp_r1]
        ring
      exact hsum.congr_deriv hsym
    have hρ_pos_t : 0 < ρ t := hρ_pos t htI
    have hinner_pos_t : 0 < M.inner p (v t) (v t) := by
      have hsq : ρ t ^ 2 = M.inner p (v t) (v t) := by
        dsimp only [ρ, LocalMetric.gnorm]
        exact Real.sq_sqrt (by
          by_contra hlt0
          have hle0 : M.inner p (v t) (v t) ≤ 0 := le_of_not_ge hlt0
          have h0 : Real.sqrt (M.inner p (v t) (v t)) = 0 := Real.sqrt_eq_zero_of_nonpos hle0
          exact hρ_pos_t.ne' h0)
      nlinarith
    have hρ_hd : HasDerivAt ρ (ρ' t) t := by
      have h1 := hinner_hd.sqrt hinner_pos_t.ne'
      have h2 : 2 * M.inner p (v t) (u t) / (2 * Real.sqrt (M.inner p (v t) (v t))) = ρ' t := by
        dsimp only [ρ', ρ, LocalMetric.gnorm]
        field_simp [hρ_pos_t.ne']
      exact h1.congr_deriv h2
    -- HasDerivAt for θ
    have hθ_hd : HasDerivAt θ (θ' t) t := by
      have hinv : HasDerivAt (fun s => (ρ s)⁻¹) (-(ρ' t) / (ρ t) ^ 2) t :=
        hρ_hd.inv hρ_pos_t.ne'
      have hsmul := hinv.smul hv_hd
      have heq : (ρ t)⁻¹ • u t + (-(ρ' t) / (ρ t) ^ 2) • v t = θ' t := by
        dsimp only [θ', u_tan]
        rw [smul_sub, smul_smul]
        have hcoef : (ρ t)⁻¹ * (ρ' t / ρ t) = ρ' t / (ρ t) ^ 2 := by field_simp [hρ_pos_t.ne']
        rw [hcoef, neg_div, neg_smul, sub_eq_add_neg]
      exact hsmul.congr_deriv heq
    -- Gauss's Lemma + Pythagoras + Coercivity
    have hgauss := hc.2.2.2.2.2.2.1
    have hcoerc := hc.2.2.2.2.2.2.2.1
    have hρsq : M.inner p (v t) (v t) = (ρ t) ^ 2 := by
      dsimp only [ρ, LocalMetric.gnorm]
      exact (Real.sq_sqrt (le_of_lt hinner_pos_t)).symm
    have horth : M.inner p (v t) (u_tan t) = 0 := by
      dsimp only [u_tan]
      rw [M.inner_sub_right, M.inner_smul_right, hρsq]
      dsimp only [ρ']
      field_simp [hρ_pos_t.ne']
      ring
    set D := fderiv ℝ (M.exp p) (v t)
    have hDu_split : derivWithin η (Icc a b) t = (ρ' t / ρ t) • D (v t) + D (u_tan t) := by
      rw [← hDexp_u]
      have hu_eq : u t = (ρ' t / ρ t) • v t + u_tan t := by dsimp only [u_tan]; abel
      rw [hu_eq, map_add, map_smul]
    have hinner_split : M.inner (η t) (derivWithin η (Icc a b) t) (derivWithin η (Icc a b) t) =
        (ρ' t) ^ 2 + M.inner (η t) (D (u_tan t)) (D (u_tan t)) := by
      rw [hDu_split, M.inner_add_left, M.inner_add_right, M.inner_add_right,
        M.inner_smul_left, M.inner_smul_right, M.inner_smul_left, M.inner_smul_right,
        ← hexp_v t htI]
      have hg1 : M.inner (M.exp p (v t)) (D (v t)) (D (v t)) = (ρ t) ^ 2 :=
        (hgauss (v t)).trans hρsq
      have hg2 : M.inner (M.exp p (v t)) (D (v t)) (D (u_tan t)) = 0 :=
        (hgauss (u_tan t)).trans horth
      have hg3 : M.inner (M.exp p (v t)) (D (u_tan t)) (D (v t)) = 0 := by
        rw [M.inner_symm hc.1]; exact hg2
      rw [hg1, hg2, hg3]
      field_simp [hρ_pos_t.ne']
      ring
    have htan_lb : c₀ * r_lo * m_g * ‖θ' t‖ ≤ M.gnorm (η t) (D (u_tan t)) := by
      have h1 : c₀ * M.gnorm p (u_tan t) ≤ M.gnorm (η t) (D (u_tan t)) := by
        rw [← hexp_v t htI]; exact hcoerc (u_tan t)
      have h2 : m_g * ‖u_tan t‖ ≤ M.gnorm p (u_tan t) := (hmet_p (u_tan t)).1
      have h3 : ‖u_tan t‖ = ρ t * ‖θ' t‖ := by
        dsimp only [θ']
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ_pos_t]
        field_simp [hρ_pos_t.ne']
      calc c₀ * r_lo * m_g * ‖θ' t‖
          ≤ c₀ * ρ t * m_g * ‖θ' t‖ := by
            gcongr; exact hρ_ge t htI
        _ = c₀ * (m_g * (ρ t * ‖θ' t‖)) := by ring
        _ = c₀ * (m_g * ‖u_tan t‖) := by rw [h3]
        _ ≤ c₀ * M.gnorm p (u_tan t) := mul_le_mul_of_nonneg_left h2 hc₀.le
        _ ≤ M.gnorm (η t) (D (u_tan t)) := h1
    have htan_sq : (c₀ * r_lo * m_g * ‖θ' t‖) ^ 2 ≤ M.inner (η t) (D (u_tan t)) (D (u_tan t)) := by
      have hsq := pow_le_pow_left₀ (by positivity) htan_lb 2
      have hgn_sq : M.gnorm (η t) (D (u_tan t)) ^ 2 = M.inner (η t) (D (u_tan t)) (D (u_tan t)) := by
        dsimp only [LocalMetric.gnorm]
        exact Real.sq_sqrt (by
          by_cases h0 : D (u_tan t) = 0
          · rw [h0, M.inner_zero_left]
          · exact (M.inner_pos (hη_r1 t htI) h0).le)
      rwa [hgn_sq] at hsq
    have hspeed_ge : Real.sqrt ((ρ' t) ^ 2 + (c₀ * r_lo * m_g * ‖θ' t‖) ^ 2) ≤ speed t := by
      dsimp only [speed, LocalMetric.gnorm]
      rw [hinner_split]
      exact Real.sqrt_le_sqrt (by linarith)
    exact ⟨hv_hd, hρ_hd, hθ_hd, hspeed_ge⟩
  -- AEStronglyMeasurable and IntervalIntegrable for ρ', θ', and √(...)
  let g_ang : ℝ → ℝ := fun t => c₀ * r_lo * m_g * ‖θ' t‖
  have hae_Ioo : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Ioc a b)), t ∈ Ioo a b := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    have hdiff : Ioc a b \ Ioo a b = {b} := by
      ext t; simp only [Set.mem_sdiff, mem_Ioc, mem_Ioo, mem_singleton_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact le_antisymm h2 (not_lt.mp fun hlt2 => h3 ⟨h1, hlt2⟩)
      · rintro rfl; exact ⟨⟨hlt, le_rfl⟩, fun h => h.2.false⟩
    have hnull : MeasureTheory.volume ({b} : Set ℝ) = 0 := MeasureTheory.measure_singleton b
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t ht htIoc
    by_contra hnot
    exact ht (by
      have : t ∈ Ioc a b \ Ioo a b := ⟨htIoc, hnot⟩
      rwa [hdiff] at this)
  have hρ'_ae_eq : ρ' =ᵐ[MeasureTheory.volume.restrict (Ioc a b)] deriv ρ := by
    filter_upwards [hae_Ioo] with t ht
    exact ((hpt_all t ht).2.1.deriv).symm
  have hθ'_ae_eq : θ' =ᵐ[MeasureTheory.volume.restrict (Ioc a b)] deriv θ := by
    filter_upwards [hae_Ioo] with t ht
    exact ((hpt_all t ht).2.2.1.deriv).symm
  have hρ'_asm : AEStronglyMeasurable ρ' (MeasureTheory.volume.restrict (Ioc a b)) :=
    (aestronglyMeasurable_deriv ρ _).congr hρ'_ae_eq.symm
  have hθ'_asm : AEStronglyMeasurable θ' (MeasureTheory.volume.restrict (Ioc a b)) :=
    (aestronglyMeasurable_deriv θ _).congr hθ'_ae_eq.symm
  have hspeed_int_Ioc : IntegrableOn speed (Ioc a b) MeasureTheory.volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hspeed_int
  have hρ'_int : IntervalIntegrable ρ' MeasureTheory.volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    refine hspeed_int_Ioc.mono' hρ'_asm ?_
    filter_upwards [hae_Ioo] with t ht
    have h1 := (hpt_all t ht).2.2.2
    have h2 : |ρ' t| ≤ Real.sqrt ((ρ' t) ^ 2 + (g_ang t) ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
    simpa [Real.norm_eq_abs] using h2.trans h1
  have hθ'_int : IntervalIntegrable θ' MeasureTheory.volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    have hconst_pos : 0 < c₀ * r_lo * m_g := by positivity
    refine (hspeed_int_Ioc.const_mul (c₀ * r_lo * m_g)⁻¹).mono' hθ'_asm ?_
    filter_upwards [hae_Ioo] with t ht
    have h1 := (hpt_all t ht).2.2.2
    have h2 : c₀ * r_lo * m_g * ‖θ' t‖ ≤ Real.sqrt ((ρ' t) ^ 2 + (g_ang t) ^ 2) := by
      have hnn : 0 ≤ c₀ * r_lo * m_g * ‖θ' t‖ := by positivity
      rw [← Real.sqrt_sq hnn]
      exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
    have h3 : c₀ * r_lo * m_g * ‖θ' t‖ ≤ speed t := h2.trans h1
    rw [le_inv_mul_iff₀ hconst_pos]
    exact h3
  have hg_int : IntervalIntegrable g_ang MeasureTheory.volume a b :=
    hθ'_int.norm.const_mul (c₀ * r_lo * m_g)
  have hsqrt_int : IntervalIntegrable (fun t => Real.sqrt ((ρ' t) ^ 2 + (g_ang t) ^ 2)) MeasureTheory.volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    have hasm : AEStronglyMeasurable (fun t => Real.sqrt ((ρ' t) ^ 2 + (g_ang t) ^ 2))
        (MeasureTheory.volume.restrict (Ioc a b)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable
        ((hρ'_asm.pow 2).add ((hθ'_asm.norm.const_mul (c₀ * r_lo * m_g)).pow 2))
    refine hspeed_int_Ioc.mono' hasm ?_
    filter_upwards [hae_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (hpt_all t ht).2.2.2
  -- FTC for ρ and θ
  have hFTC_ρ : ∫ t in a..b, ρ' t = ρ b - ρ a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hρ_cont
      (fun t ht => (hpt_all t ht).2.1) hρ'_int
  have hFTC_θ : ∫ t in a..b, θ' t = θ b - θ a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hθ_cont
      (fun t ht => (hpt_all t ht).2.2.1) hθ'_int
  have hang_le : c₀ * r_lo * m_g * ‖θ b - θ a‖ ≤ ∫ t in a..b, g_ang t := by
    have h1 : ‖θ b - θ a‖ ≤ ∫ t in a..b, ‖θ' t‖ := by
      rw [← hFTC_θ]
      exact intervalIntegral.norm_integral_le_integral_norm hab
    have h2 : ∫ t in a..b, g_ang t = c₀ * r_lo * m_g * ∫ t in a..b, ‖θ' t‖ :=
      intervalIntegral.integral_const_mul _ _
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hmono_int : ∫ t in a..b, Real.sqrt ((ρ' t) ^ 2 + (g_ang t) ^ 2) ≤ ∫ t in a..b, speed t := by
    refine intervalIntegral.integral_mono_ae_restrict hab hsqrt_int hspeed_int ?_
    change ∀ᵐ t ∂(MeasureTheory.volume.restrict (Icc a b)), Real.sqrt ((ρ' t) ^ 2 + (g_ang t) ^ 2) ≤ speed t
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    have hnull_ab : MeasureTheory.volume ({a, b} : Set ℝ) = 0 :=
      MeasureTheory.measure_union_null (MeasureTheory.measure_singleton a) (MeasureTheory.measure_singleton b)
    filter_upwards [compl_mem_ae_iff.mpr hnull_ab] with t ht htIcc
    have ht_oo : t ∈ Ioo a b := ⟨lt_of_le_of_ne htIcc.1 (fun h => ht (Or.inl h.symm)),
      lt_of_le_of_ne htIcc.2 (fun h => ht (Or.inr h))⟩
    exact (hpt_all t ht_oo).2.2.2
  calc Real.sqrt ((ρ b - ρ a) ^ 2 + (c₀ * r_lo * m_g * ‖θ b - θ a‖) ^ 2)
      ≤ Real.sqrt ((∫ t in a..b, ρ' t) ^ 2 + (∫ t in a..b, g_ang t) ^ 2) := by
        rw [hFTC_ρ]
        exact Real.sqrt_le_sqrt (add_le_add le_rfl (pow_le_pow_left₀ (by positivity) hang_le 2))
    _ ≤ ∫ t in a..b, Real.sqrt ((ρ' t) ^ 2 + (g_ang t) ^ 2) :=
        sqrt_sq_add_sq_le_integral hab hρ'_int hg_int hsqrt_int
    _ ≤ ∫ t in a..b, speed t := hmono_int

end AnnulusAndContinuation

end OMA.Hilbert5H2

namespace OMA.Hilbert5H2

section UniqueContinuation

open Metric Set Filter Topology MeasureTheory Manifold
open scoped Manifold ContDiff Bundle ENNReal RealInnerProductSpace Classical

private lemma local_unique_continuation {n : ℕ} {X : Type} [MetricSpace X]
    [ChartedSpace (Euc n) X] [IsManifold (𝓡 n) ∞ X]
    [hRB : Bundle.RiemannianBundle (fun x : X => TangentSpace (𝓡 n) x)]
    [hCRB : IsContMDiffRiemannianBundle (𝓡 n) ∞ (Euc n) (fun x : X => TangentSpace (𝓡 n) x)]
    [hRM : IsRiemannianManifold (𝓡 n) X]
    (e : Equiv.Perm X) (he : Isometry (e : X → X))
    (x₀ : X) (hx₀ : x₀ ∈ closure (interior {x : X | e x = x})) :
    x₀ ∈ interior {x : X | e x = x} := by
  let S : Set X := interior {x : X | e x = x}
  let φ := chartAt (Euc n) x₀
  let a₀ := φ x₀
  let g : Euc n → Fin n → Fin n → ℝ := fun y i j =>
    ⟪(trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm y) (basisVec i),
     (trivializationAt (Euc n) (TangentSpace (𝓡 n)) x₀).symmL ℝ (φ.symm y) (basisVec j)⟫
  obtain ⟨r₁, hr₁, hr₁_tgt, hg_smooth, hg_symm, hinner, hg_pos⟩ := pullback_metric_exists (n := n) x₀
  let M : LocalMetric n := ⟨a₀, r₁, hr₁, g, hg_smooth, hg_symm, hg_pos⟩
  obtain ⟨r_p, hr_p, r_v, hr_v, m_g, hm_g, M_g, hM_g, c₀, hc₀, hrp_le, hmet_rp, hnb⟩ :=
    M.exists_normal_ball
  -- Open image helper: any open subset of ball a₀ r₁ maps via φ.symm to an open set in X
  have hsymm_open : ∀ U : Set (Euc n), IsOpen U → U ⊆ ball a₀ r₁ → IsOpen (φ.symm '' U) := by
    intro U hU hU_sub
    have heq : φ.symm '' U = φ.source ∩ φ ⁻¹' U := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hyt : y ∈ φ.target := hr₁_tgt (hU_sub hy)
        exact ⟨φ.map_target hyt, by change φ (φ.symm y) ∈ U; rwa [φ.right_inv hyt]⟩
      · rintro ⟨hxs, hxu⟩
        exact ⟨φ x, hxu, φ.left_inv hxs⟩
    rw [heq]
    exact φ.continuousOn_toFun.isOpen_inter_preimage φ.open_source hU
  have hsymm_mem : ∀ {U : Set (Euc n)}, U ⊆ ball a₀ r₁ → ∀ {x : X},
      x ∈ φ.symm '' U ↔ x ∈ φ.source ∧ φ x ∈ U := by
    intro U hU_sub x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyt : y ∈ φ.target := hr₁_tgt (hU_sub hy)
      exact ⟨φ.map_target hyt, by rwa [φ.right_inv hyt]⟩
    · rintro ⟨hxs, hxu⟩
      exact ⟨φ x, hxu, φ.left_inv hxs⟩
  -- Pick p' ∈ S ∩ (φ.symm '' ball a₀ r_p)
  let B₀ : Set X := φ.symm '' ball a₀ r_p
  have hB₀_open : IsOpen B₀ := hsymm_open _ isOpen_ball (ball_subset_ball hrp_le)
  have hx₀_B₀ : x₀ ∈ B₀ := ⟨a₀, mem_ball_self hr_p, φ.left_inv (mem_chart_source (Euc n) x₀)⟩
  obtain ⟨p', hp'_B₀, hp'_S⟩ := mem_closure_iff.mp hx₀ B₀ hB₀_open hx₀_B₀
  obtain ⟨p, hp, rfl⟩ := hp'_B₀
  have hp_r1 : p ∈ ball M.a₀ M.r₁ := ball_subset_ball hrp_le hp
  have hp_tgt : p ∈ φ.target := hr₁_tgt hp_r1
  have hp_src : φ.symm p ∈ φ.source := φ.map_target hp_tgt
  obtain ⟨hcore, hW_open, hB0_sub, hshells, hW_log⟩ := hnb p hp
  let W : Set (Euc n) := M.exp p '' {v | M.gnorm p v < r_v}
  have hW_sub_r1 : W ⊆ ball a₀ r₁ := by
    rintro _ ⟨v, hv, rfl⟩; exact (hcore v hv).1
  let W_X : Set X := φ.symm '' W
  have hWX_open : IsOpen W_X := hsymm_open W hW_open hW_sub_r1
  have hx₀_WX : x₀ ∈ W_X :=
    ⟨a₀, hB0_sub (mem_ball_self hr_p), φ.left_inv (mem_chart_source (Euc n) x₀)⟩
  -- Basic facts about exp p 0 = p
  have hexp0 : M.exp p 0 = p := by
    have hgn0 : M.gnorm p 0 < r_v := by rw [M.gnorm_zero]; exact hr_v
    have h0 := (hcore 0 hgn0).2.2.2.2.2.2.2.2.2.2 0 (left_mem_Icc.mpr zero_le_one)
    rw [zero_smul] at h0
    exact h0.1.trans (M.γExt_zero p 0)
  -- Upper bound on distance along any radial geodesic segment
  have hray_le : ∀ v : Euc n, M.gnorm p v < r_v → ∀ s₁ s₂ : ℝ,
      0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ 1 →
      dist (φ.symm (M.exp p (s₁ • v))) (φ.symm (M.exp p (s₂ • v))) ≤ (s₂ - s₁) * M.gnorm p v := by
    intro v hv s₁ s₂ hs₁ hs₁₂ hs₂
    rcases eq_or_lt_of_le hs₁₂ with rfl | hlt
    · simp
    have hc := hcore v hv
    have hray := hc.2.2.2.2.2.2.2.2.2.2
    have hsub01 : Icc s₁ s₂ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs₁ hs₂
    have hγ_hd : ∀ s ∈ Icc s₁ s₂, HasDerivAt (M.γExt p v) (M.ξExt p v s) s :=
      fun s hs => (hray s (hsub01 hs)).2.2.2
    have hξ_cont : ContinuousOn (M.ξExt p v) (Icc s₁ s₂) :=
      (continuous_const.sub (continuous_iff_continuousAt.mpr fun t =>
        (intFun_hasDerivAt (M.quadOp (M.geod p v)) t).continuousAt)).continuousOn
    have hγ_cd : ContDiffOn ℝ 1 (M.γExt p v) (Icc s₁ s₂) := by
      rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hlt)]
      refine ⟨fun s hs => (hγ_hd s hs).differentiableAt.differentiableWithinAt, ?_⟩
      refine hξ_cont.congr fun s hs => ?_
      exact (hγ_hd s hs).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hlt s hs)
    have hγ_in_r1 : ∀ s ∈ Icc s₁ s₂, M.γExt p v s ∈ ball a₀ r₁ :=
      fun s hs => (hray s (hsub01 hs)).2.1
    have hγ_cmd : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 (φ.symm ∘ M.γExt p v) (Icc s₁ s₂) := by
      have h1 : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 (M.γExt p v) (Icc s₁ s₂) :=
        contMDiffOn_iff_contDiffOn.mpr hγ_cd
      have h2 : ContMDiffOn (𝓡 n) (𝓡 n) 1 φ.symm (ball a₀ r₁) := by
        have hle : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
          change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
          exact WithTop.coe_le_coe.mpr le_top
        have hOn := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := (∞ : WithTop ℕ∞)) x₀).mono
          (by simpa [extChartAt_target] using hr₁_tgt)
        exact hOn.of_le hle
      exact h2.comp h1 hγ_in_r1
    have hle_edist : edist (φ.symm (M.exp p (s₁ • v))) (φ.symm (M.exp p (s₂ • v))) ≤
        pathELength (𝓡 n) (φ.symm ∘ M.γExt p v) s₁ s₂ := by
      rw [hRM.out]
      refine riemannianEDist_le_pathELength hγ_cmd ?_ ?_ hs₁₂
      · simp [Function.comp_apply, (hray s₁ (hsub01 (left_mem_Icc.mpr hs₁₂))).1]
      · simp [Function.comp_apply, (hray s₂ (hsub01 (right_mem_Icc.mpr hs₁₂))).1]
    have hlen_eq := pathELength_eq_ofReal_integral x₀ hr₁_tgt hg_smooth hinner hlt hγ_cmd
      (fun s hs => ⟨M.γExt p v s, hγ_in_r1 s hs, rfl⟩)
    have hη_eq : ∀ s ∈ Icc s₁ s₂, (φ ∘ (φ.symm ∘ M.γExt p v)) s = M.γExt p v s :=
      fun s hs => φ.right_inv (hr₁_tgt (hγ_in_r1 s hs))
    have hderiv_eq : ∀ s ∈ Ioo s₁ s₂,
        derivWithin (φ ∘ (φ.symm ∘ M.γExt p v)) (Icc s₁ s₂) s = M.ξExt p v s := by
      intro s hs
      have hnhds : Icc s₁ s₂ ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
      rw [derivWithin_of_mem_nhds hnhds]
      have hev : (φ ∘ (φ.symm ∘ M.γExt p v)) =ᶠ[𝓝 s] M.γExt p v := by
        filter_upwards [hnhds] with t ht using hη_eq t ht
      exact (hev.deriv_eq).trans (hγ_hd s (Ioo_subset_Icc_self hs)).deriv
    have hint_eq : ∫ t in s₁..s₂,
        Real.sqrt (∑ i, ∑ j, g ((φ ∘ (φ.symm ∘ M.γExt p v)) t) i j *
          (derivWithin (φ ∘ (φ.symm ∘ M.γExt p v)) (Icc s₁ s₂) t).ofLp i *
          (derivWithin (φ ∘ (φ.symm ∘ M.γExt p v)) (Icc s₁ s₂) t).ofLp j) =
        (s₂ - s₁) * M.gnorm p v := by
      have hcongr : ∫ t in s₁..s₂,
          Real.sqrt (∑ i, ∑ j, g ((φ ∘ (φ.symm ∘ M.γExt p v)) t) i j *
            (derivWithin (φ ∘ (φ.symm ∘ M.γExt p v)) (Icc s₁ s₂) t).ofLp i *
            (derivWithin (φ ∘ (φ.symm ∘ M.γExt p v)) (Icc s₁ s₂) t).ofLp j) =
          ∫ _t in s₁..s₂, M.gnorm p v := by
        refine intervalIntegral.integral_congr_ae ?_
        have hnull : MeasureTheory.volume ({s₁, s₂} : Set ℝ) = 0 :=
          MeasureTheory.measure_union_null (MeasureTheory.measure_singleton s₁) (MeasureTheory.measure_singleton s₂)
        filter_upwards [compl_mem_ae_iff.mpr hnull] with t ht htIoc
        rw [Set.uIoc_of_le hs₁₂] at htIoc
        have ht_oo : t ∈ Ioo s₁ s₂ := ⟨htIoc.1, lt_of_le_of_ne htIoc.2 (fun h => ht (Or.inr h))⟩
        have ht_cc := Ioo_subset_Icc_self ht_oo
        rw [hη_eq t ht_cc, hderiv_eq t ht_oo]
        exact (hray t (hsub01 ht_cc)).2.2.1
      rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
    rw [hlen_eq.2.2, hint_eq, edist_dist] at hle_edist
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sub_nonneg.mpr hs₁₂) (Real.sqrt_nonneg _))).mp hle_edist
  -- Continuity of ρ_X(x) = gnorm p (log p (φ x)) on W_X
  have hρW_cont : ContinuousOn (fun q : Euc n => M.gnorm p (M.log p q)) W := by
    refine M.gnorm_continuousOn_vec.comp_continuousOn fun q hq => ?_
    have hlogq := hW_log q hq
    have hc := hcore (M.log p q) hlogq.1
    rw [hlogq.2] at hc
    exact hc.2.2.2.2.2.2.2.2.1.continuousAt.continuousWithinAt
  -- Lower bound for any C^1 path starting at φ.symm p and leaving the open normal ball of radius r
  have hpath_cross : ∀ (r : ℝ), r ∈ Ioo 0 r_v → ∀ (γ : ℝ → X),
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc 0 1) → γ 0 = φ.symm p →
      γ 1 ∉ φ.symm '' (M.exp p '' {v | M.gnorm p v < r}) →
      ENNReal.ofReal r ≤ pathELength (𝓡 n) γ 0 1 := by
    intro r hr γ hγ hγ0 hγ1
    let U_r : Set (Euc n) := M.exp p '' {v | M.gnorm p v < r}
    let K_r : Set (Euc n) := M.exp p '' {v | M.gnorm p v ≤ r}
    have hU_sub : U_r ⊆ ball a₀ r₁ := fun _ ⟨v, hv, hv_eq⟩ => hv_eq ▸ (hcore v (hv.trans hr.2)).1
    have hK_sub : K_r ⊆ ball a₀ r₁ := fun _ ⟨v, hv, hv_eq⟩ => hv_eq ▸ (hcore v (hv.trans_lt hr.2)).1
    have hK_sub_W : K_r ⊆ W := fun _ ⟨v, hv, hv_eq⟩ => ⟨v, hv.trans_lt hr.2, hv_eq⟩
    let U_X : Set X := φ.symm '' U_r
    let K_X : Set X := φ.symm '' K_r
    have hUX_open : IsOpen U_X := hsymm_open U_r (hshells r hr).1 hU_sub
    have hKX_closed : IsClosed K_X :=
      ((hshells r hr).2.image_of_continuousOn
        (φ.continuousOn_symm.mono (hK_sub.trans hr₁_tgt))).isClosed
    have hUX_sub_KX : U_X ⊆ K_X :=
      image_mono (image_mono fun (v : Euc n) (hv : M.gnorm p v < r) => hv.le)
    let E : Set ℝ := {t ∈ Icc (0 : ℝ) 1 | γ t ∉ U_X}
    have hE_closed : IsClosed E :=
      hγ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hUX_open.isClosed_compl
    have h1_E : (1 : ℝ) ∈ E := ⟨right_mem_Icc.mpr zero_le_one, hγ1⟩
    have hE_bdd : BddBelow E := ⟨0, fun t ht => ht.1.1⟩
    set t_hi : ℝ := sInf E
    have ht_hi_E : t_hi ∈ E := hE_closed.csInf_mem ⟨1, h1_E⟩ hE_bdd
    have h0_UX : γ 0 ∈ U_X := by
      rw [hγ0]
      exact ⟨p, ⟨0, by change M.gnorm p 0 < r; rw [M.gnorm_zero]; exact hr.1, hexp0⟩, rfl⟩
    have ht_hi_pos : 0 < t_hi := by
      by_contra hle
      have h0 : t_hi = 0 := le_antisymm (not_lt.mp hle) ht_hi_E.1.1
      exact ht_hi_E.2 (h0 ▸ h0_UX)
    have hbefore_UX : ∀ t ∈ Ico (0 : ℝ) t_hi, γ t ∈ U_X := by
      intro t ht
      by_contra hnot
      have ht_E : t ∈ E := ⟨⟨ht.1, ht.2.le.trans ht_hi_E.1.2⟩, hnot⟩
      exact (csInf_le hE_bdd ht_E).not_gt ht.2
    -- γ t_hi ∈ K_X by continuity from [0, t_hi)
    have hγ_thi_KX : γ t_hi ∈ K_X := by
      have ht_cl : t_hi ∈ closure (Ico (0 : ℝ) t_hi) := by
        rw [closure_Ico ht_hi_pos.ne]
        exact right_mem_Icc.mpr ht_hi_pos.le
      have hmem : γ t_hi ∈ closure (γ '' Ico (0 : ℝ) t_hi) := by
        have hcont_at : ContinuousWithinAt γ (Ico 0 t_hi) t_hi :=
          (hγ.continuousOn t_hi ht_hi_E.1).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc_right ht_hi_E.1.2))
        exact hcont_at.mem_closure_image ht_cl
      have hsub : γ '' Ico (0 : ℝ) t_hi ⊆ K_X := by
        rintro _ ⟨t, ht, rfl⟩; exact hUX_sub_KX (hbefore_UX t ht)
      exact hKX_closed.closure_subset_iff.mpr hsub hmem
    have hγ_sub_KX : ∀ t ∈ Icc (0 : ℝ) t_hi, γ t ∈ K_X := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with rfl | hlt
      · exact hγ_thi_KX
      · exact hUX_sub_KX (hbefore_UX t ⟨ht.1, hlt⟩)
    -- Coordinate curve η = φ ∘ γ on [0, t_hi]
    let η : ℝ → Euc n := φ ∘ γ
    have hη_in_Kr : ∀ t ∈ Icc (0 : ℝ) t_hi, η t ∈ K_r := fun t ht =>
      ((hsymm_mem hK_sub).mp (hγ_sub_KX t ht)).2
    have hη_in_W : ∀ t ∈ Icc (0 : ℝ) t_hi, η t ∈ W := fun t ht => hK_sub_W (hη_in_Kr t ht)
    have hη_cont : ContinuousOn η (Icc 0 t_hi) :=
      φ.continuousOn_toFun.comp (hγ.continuousOn.mono (Icc_subset_Icc_right ht_hi_E.1.2))
        fun t ht => ((hsymm_mem hK_sub).mp (hγ_sub_KX t ht)).1
    have hρ_cont : ContinuousOn (fun t => M.gnorm p (M.log p (η t))) (Icc 0 t_hi) :=
      hρW_cont.comp hη_cont hη_in_W
    have hρ_0 : M.gnorm p (M.log p (η 0)) = 0 := by
      have hη0 : η 0 = M.exp p 0 := by
        change φ (γ 0) = M.exp p 0
        rw [hγ0, φ.right_inv hp_tgt, hexp0]
      rw [hη0, (hcore 0 (by rw [M.gnorm_zero]; exact hr.1.trans hr.2)).2.2.2.2.1, M.gnorm_zero]
    have hρ_thi : M.gnorm p (M.log p (η t_hi)) = r := by
      obtain ⟨v, hv_le, hv_eq⟩ := hη_in_Kr t_hi (right_mem_Icc.mpr ht_hi_pos.le)
      have hlog_v : M.log p (η t_hi) = v := by
        rw [← hv_eq]; exact (hcore v (hv_le.trans_lt hr.2)).2.2.2.2.1
      rw [hlog_v]
      refine le_antisymm hv_le (not_lt.mp fun hlt => ht_hi_E.2 ?_)
      rw [hsymm_mem hU_sub]
      exact ⟨((hsymm_mem hK_sub).mp hγ_thi_KX).1, ⟨v, hlt, hv_eq⟩⟩
    -- For every ε ∈ (0, r), find last time t_lo with ρ(t_lo) ≤ ε and apply annulus_length_ge
    have hge_sub : ∀ ε : ℝ, 0 < ε → ε < r → ENNReal.ofReal (r - ε) ≤ pathELength (𝓡 n) γ 0 1 := by
      intro ε hε hεr
      let F : Set ℝ := {t ∈ Icc (0 : ℝ) t_hi | M.gnorm p (M.log p (η t)) ≤ ε}
      have hF_closed : IsClosed F :=
        hρ_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have h0_F : (0 : ℝ) ∈ F := ⟨left_mem_Icc.mpr ht_hi_pos.le, by rw [hρ_0]; exact hε.le⟩
      have hF_bdd : BddAbove F := ⟨t_hi, fun t ht => ht.1.2⟩
      set t_lo : ℝ := sSup F
      have ht_lo_F : t_lo ∈ F := hF_closed.csSup_mem ⟨0, h0_F⟩ hF_bdd
      have ht_lo_lt : t_lo < t_hi := by
        refine lt_of_le_of_ne ht_lo_F.1.2 fun heq => ?_
        have := ht_lo_F.2
        rw [heq, hρ_thi] at this
        linarith
      have hρ_after : ∀ t ∈ Ioc t_lo t_hi, ε < M.gnorm p (M.log p (η t)) := by
        intro t ht
        by_contra hle
        push Not at hle
        have ht_F : t ∈ F := ⟨⟨ht_lo_F.1.1.trans ht.1.le, ht.2⟩, hle⟩
        exact (le_csSup hF_bdd ht_F).not_gt ht.1
      have hρ_tlo : M.gnorm p (M.log p (η t_lo)) = ε := by
        refine le_antisymm ht_lo_F.2 ?_
        have ht_cl : t_lo ∈ closure (Ioc t_lo t_hi) := by
          rw [closure_Ioc ht_lo_lt.ne]
          exact left_mem_Icc.mpr ht_lo_lt.le
        have hcont_at : ContinuousWithinAt (fun t => M.gnorm p (M.log p (η t))) (Ioc t_lo t_hi) t_lo :=
          (hρ_cont t_lo ht_lo_F.1).mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc_left ht_lo_F.1.1))
        have hmem := hcont_at.mem_closure_image ht_cl
        have hsub : (fun t => M.gnorm p (M.log p (η t))) '' Ioc t_lo t_hi ⊆ Ici ε := by
          rintro _ ⟨t, ht, rfl⟩; exact (hρ_after t ht).le
        exact isClosed_Ici.closure_subset_iff.mpr hsub hmem
      have hγ_sub_Icc : Icc t_lo t_hi ⊆ Icc (0 : ℝ) 1 :=
        Icc_subset_Icc ht_lo_F.1.1 (ht_hi_E.1.2)
      have hγ_seg : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc t_lo t_hi) := hγ.mono hγ_sub_Icc
      have hγ_seg_r1 : ∀ t ∈ Icc t_lo t_hi, γ t ∈ φ.symm '' ball a₀ r₁ := fun t ht =>
        let h1 := hγ_sub_KX t ⟨ht_lo_F.1.1.trans ht.1, ht.2⟩
        (image_mono hK_sub) h1
      have hlen_seg := pathELength_eq_ofReal_integral x₀ hr₁_tgt hg_smooth hinner ht_lo_lt hγ_seg hγ_seg_r1
      have hη_cd : ContDiffOn ℝ 1 η (Icc t_lo t_hi) := hlen_seg.1
      have hη_ann : ∀ t ∈ Icc t_lo t_hi, η t ∈ W ∧ ε ≤ M.gnorm p (M.log p (η t)) := by
        intro t ht
        refine ⟨hη_in_W t ⟨ht_lo_F.1.1.trans ht.1, ht.2⟩, ?_⟩
        rcases eq_or_lt_of_le ht.1 with rfl | hlt
        · rw [hρ_tlo]
        · exact (hρ_after t ⟨hlt, ht.2⟩).le
      have hann := annulus_length_ge M hp_r1 hr_v hm_g hc₀ (hmet_rp p hp) hcore hW_open hW_log
        ht_lo_lt.le hε hη_cd hη_ann
      have hr_sub_le : r - ε ≤ ∫ t in t_lo..t_hi, M.gnorm (η t) (derivWithin η (Icc t_lo t_hi) t) := by
        dsimp only at hann
        rw [hρ_thi, hρ_tlo] at hann
        have h1 : r - ε ≤ Real.sqrt ((r - ε) ^ 2 + (c₀ * ε * m_g *
            ‖r⁻¹ • M.log p (η t_hi) - ε⁻¹ • M.log p (η t_lo)‖) ^ 2) := by
          conv_lhs => rw [← Real.sqrt_sq (sub_nonneg.mpr hεr.le)]
          exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
        exact h1.trans hann
      have hseg_le : pathELength (𝓡 n) γ t_lo t_hi ≤ pathELength (𝓡 n) γ 0 1 := by
        have hadd1 := pathELength_add (I := 𝓡 n) (γ := γ) ht_lo_F.1.1 ht_lo_lt.le
        have hadd2 := pathELength_add (I := 𝓡 n) (γ := γ) ht_hi_pos.le ht_hi_E.1.2
        calc pathELength (𝓡 n) γ t_lo t_hi
            ≤ pathELength (𝓡 n) γ 0 t_lo + pathELength (𝓡 n) γ t_lo t_hi := le_add_self
          _ = pathELength (𝓡 n) γ 0 t_hi := hadd1
          _ ≤ pathELength (𝓡 n) γ 0 t_hi + pathELength (𝓡 n) γ t_hi 1 := le_self_add
          _ = pathELength (𝓡 n) γ 0 1 := hadd2
      calc ENNReal.ofReal (r - ε)
          ≤ ENNReal.ofReal (∫ t in t_lo..t_hi, M.gnorm (η t) (derivWithin η (Icc t_lo t_hi) t)) :=
            ENNReal.ofReal_le_ofReal hr_sub_le
        _ = pathELength (𝓡 n) γ t_lo t_hi := hlen_seg.2.2.symm
        _ ≤ pathELength (𝓡 n) γ 0 1 := hseg_le
    -- Take ε → 0⁺
    by_contra hlt_len
    push Not at hlt_len
    have hlt_top : pathELength (𝓡 n) γ 0 1 < ⊤ := hlt_len.trans ENNReal.ofReal_lt_top
    set L := (pathELength (𝓡 n) γ 0 1).toReal
    have hL_eq : ENNReal.ofReal L = pathELength (𝓡 n) γ 0 1 := ENNReal.ofReal_toReal hlt_top.ne
    have hL_lt : L < r := by
      have h1 : ENNReal.ofReal L < ENNReal.ofReal r := hL_eq.symm ▸ hlt_len
      exact (ENNReal.ofReal_lt_ofReal_iff hr.1).mp h1
    set ε := (r - L) / 2 with hε_def
    have hε_pos : 0 < ε := by rw [hε_def]; linarith
    have hε_lt : ε < r := by
      have hL_nn : 0 ≤ L := ENNReal.toReal_nonneg
      rw [hε_def]; linarith
    have hbound := hge_sub ε hε_pos hε_lt
    rw [← hL_eq] at hbound
    have hle_real := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hbound
    rw [hε_def] at hle_real
    linarith
  -- Corollary 1: points outside W_X have distance ≥ r_v from φ.symm p
  have hdist_outside : ∀ x : X, x ∉ W_X → r_v ≤ dist (φ.symm p) x := by
    intro x hx
    by_contra hlt
    push Not at hlt
    set r := (dist (φ.symm p) x + r_v) / 2 with hr_def
    have hr_pos : 0 < r := by rw [hr_def]; linarith [dist_nonneg (x := φ.symm p) (y := x)]
    have hr_lt : r < r_v := by rw [hr_def]; linarith
    have hdist_lt : riemannianEDist (𝓡 n) (φ.symm p) x < ENNReal.ofReal r := by
      rw [← hRM.out, edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff hr_pos).mpr (by rw [hr_def]; linarith)
    obtain ⟨γ, hγ0, hγ1, hγ_cmd, hlen_lt⟩ := exists_lt_of_riemannianEDist_lt hdist_lt
    have hnot_Ur : γ 1 ∉ φ.symm '' (M.exp p '' {v | M.gnorm p v < r}) := by
      rw [hγ1]
      intro hmem
      exact hx ((image_mono (image_mono fun (v : Euc n) (hv : M.gnorm p v < r) => hv.trans hr_lt)) hmem)
    exact (hpath_cross r ⟨hr_pos, hr_lt⟩ γ hγ_cmd hγ0 hnot_Ur).not_gt hlen_lt
  -- Corollary 2: exact radial distance formula inside W_X
  have hdist_exp : ∀ v : Euc n, M.gnorm p v < r_v →
      dist (φ.symm p) (φ.symm (M.exp p v)) = M.gnorm p v := by
    intro v hv
    refine le_antisymm ?_ ?_
    · have h := hray_le v hv 0 1 le_rfl zero_le_one le_rfl
      simpa [zero_smul, one_smul, hexp0] using h
    · by_cases hgn0 : M.gnorm p v = 0
      · rw [hgn0]; exact dist_nonneg
      · have hgn_pos : 0 < M.gnorm p v := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hgn0)
        by_contra hlt
        push Not at hlt
        set r := (dist (φ.symm p) (φ.symm (M.exp p v)) + M.gnorm p v) / 2 with hr_def
        have hr_pos : 0 < r := by rw [hr_def]; linarith [dist_nonneg (x := φ.symm p) (y := φ.symm (M.exp p v))]
        have hr_lt_v : r < M.gnorm p v := by rw [hr_def]; linarith
        have hr_lt_rv : r < r_v := hr_lt_v.trans hv
        have hdist_lt : riemannianEDist (𝓡 n) (φ.symm p) (φ.symm (M.exp p v)) < ENNReal.ofReal r := by
          rw [← hRM.out, edist_dist]
          exact (ENNReal.ofReal_lt_ofReal_iff hr_pos).mpr (by rw [hr_def]; linarith)
        obtain ⟨γ, hγ0, hγ1, hγ_cmd, hlen_lt⟩ := exists_lt_of_riemannianEDist_lt hdist_lt
        have hnot_Ur : γ 1 ∉ φ.symm '' (M.exp p '' {w | M.gnorm p w < r}) := by
          rw [hγ1]
          rintro ⟨q, ⟨w, hw, hw_eq⟩, hsymm_eq⟩
          have hw_lt : M.gnorm p w < r := hw
          have hq_r1 : q ∈ ball a₀ r₁ := hw_eq ▸ (hcore w (hw_lt.trans hr_lt_rv)).1
          have hv_r1 : M.exp p v ∈ ball a₀ r₁ := (hcore v hv).1
          have hq_eq : q = M.exp p v := by
            have := congrArg φ hsymm_eq
            rwa [φ.right_inv (hr₁_tgt hq_r1), φ.right_inv (hr₁_tgt hv_r1)] at this
          have hwv : w = v := by
            have h1 := (hcore w (hw_lt.trans hr_lt_rv)).2.2.2.2.1
            have h2 := (hcore v hv).2.2.2.2.1
            rw [hw_eq, hq_eq, h2] at h1
            exact h1.symm
          rw [hwv] at hw_lt
          linarith
        exact (hpath_cross r ⟨hr_pos, hr_lt_rv⟩ γ hγ_cmd hγ0 hnot_Ur).not_gt hlen_lt
  -- Strict ray uniqueness: if dist(p', z') + dist(z', q') = dist(p', q') with 0 < r_z < r_q < r_v, then θ_z = θ_q
  have hray_unique : ∀ v_z v_q : Euc n,
      0 < M.gnorm p v_z → M.gnorm p v_z < M.gnorm p v_q → M.gnorm p v_q < r_v →
      dist (φ.symm (M.exp p v_z)) (φ.symm (M.exp p v_q)) = M.gnorm p v_q - M.gnorm p v_z →
      (M.gnorm p v_z)⁻¹ • v_z = (M.gnorm p v_q)⁻¹ • v_q := by
    intro v_z v_q hrz_pos hrz_lt hrq_lt hdist_zq
    set r_z := M.gnorm p v_z
    set r_q := M.gnorm p v_q
    set z' := φ.symm (M.exp p v_z)
    set q' := φ.symm (M.exp p v_q)
    set r_lo := r_z / 2 with hrlo_def
    set r_hi := (r_q + r_v) / 2 with hrhi_def
    have hrlo_pos : 0 < r_lo := half_pos hrz_pos
    have hrlo_lt_rz : r_lo < r_z := half_lt_self hrz_pos
    have hrq_lt_rhi : r_q < r_hi := by rw [hrhi_def]; linarith
    have hrhi_lt_rv : r_hi < r_v := by rw [hrhi_def]; linarith
    set δ₀ := min (r_z - r_lo) (r_hi - r_q)
    have hδ₀_pos : 0 < δ₀ := lt_min (by linarith) (by linarith)
    let A : Set (Euc n) := M.exp p '' {v | r_lo < M.gnorm p v ∧ M.gnorm p v < r_hi}
    let K_hi : Set (Euc n) := M.exp p '' {v | M.gnorm p v ≤ r_hi}
    have hA_open : IsOpen A := by
      have heq : A = (M.exp p '' {v | M.gnorm p v < r_hi}) ∩
          (M.exp p '' {v | M.gnorm p v ≤ r_lo})ᶜ := by
        ext q
        constructor
        · rintro ⟨v, ⟨h1, h2⟩, rfl⟩
          refine ⟨⟨v, h2, rfl⟩, ?_⟩
          rintro ⟨w, hw, hw_eq⟩
          have hw_le : M.gnorm p w ≤ r_lo := hw
          have hv_eq := (hcore v (h2.trans hrhi_lt_rv)).2.2.2.2.1
          have hw_eq' := (hcore w (hw_le.trans_lt (hrlo_lt_rz.trans (hrz_lt.trans hrq_lt)))).2.2.2.2.1
          have hvw : v = w := by rw [← hv_eq, ← hw_eq, hw_eq']
          rw [← hvw] at hw_le
          linarith
        · rintro ⟨⟨v, hv, rfl⟩, hnot⟩
          refine ⟨v, ⟨?_, hv⟩, rfl⟩
          by_contra hle
          push Not at hle
          exact hnot ⟨v, hle, rfl⟩
      rw [heq]
      exact (hshells r_hi ⟨hrlo_pos.trans (hrlo_lt_rz.trans (hrz_lt.trans hrq_lt_rhi)), hrhi_lt_rv⟩).1.inter
        (hshells r_lo ⟨hrlo_pos, hrlo_lt_rz.trans (hrz_lt.trans hrq_lt)⟩).2.isClosed.isOpen_compl
    have hA_sub : A ⊆ ball a₀ r₁ := fun _ ⟨v, hv, hv_eq⟩ => hv_eq ▸ (hcore v (hv.2.trans hrhi_lt_rv)).1
    have hKhi_sub : K_hi ⊆ ball a₀ r₁ := fun _ ⟨v, hv, hv_eq⟩ => hv_eq ▸ (hcore v (hv.trans_lt hrhi_lt_rv)).1
    have hKhi_sub_W : K_hi ⊆ W := fun _ ⟨v, hv, hv_eq⟩ => ⟨v, hv.trans_lt hrhi_lt_rv, hv_eq⟩
    let A_X : Set X := φ.symm '' A
    let Khi_X : Set X := φ.symm '' K_hi
    have hAX_open : IsOpen A_X := hsymm_open A hA_open hA_sub
    have hKhiX_closed : IsClosed Khi_X :=
      ((hshells r_hi ⟨hrlo_pos.trans (hrlo_lt_rz.trans (hrz_lt.trans hrq_lt_rhi)), hrhi_lt_rv⟩).2.image_of_continuousOn
        (φ.continuousOn_symm.mono (hKhi_sub.trans hr₁_tgt))).isClosed
    have hAX_sub_KhiX : A_X ⊆ Khi_X :=
      image_mono (image_mono fun (v : Euc n) (hv : r_lo < M.gnorm p v ∧ M.gnorm p v < r_hi) => hv.2.le)
    -- Show √((r_q - r_z)^2 + (c₀ * r_lo * m_g * ‖θ_q - θ_z‖)^2) ≤ r_q - r_z + ε for all ε ∈ (0, δ₀)
    have hbound_eps : ∀ ε : ℝ, 0 < ε → ε < δ₀ →
        Real.sqrt ((r_q - r_z) ^ 2 + (c₀ * r_lo * m_g * ‖r_q⁻¹ • v_q - r_z⁻¹ • v_z‖) ^ 2) ≤
          r_q - r_z + ε := by
      intro ε hε hεδ
      have hdist_lt : riemannianEDist (𝓡 n) z' q' < ENNReal.ofReal (r_q - r_z + ε) := by
        rw [← hRM.out, edist_dist, hdist_zq]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
      obtain ⟨γ, hγ0, hγ1, hγ_cmd, hlen_lt⟩ := exists_lt_of_riemannianEDist_lt hdist_lt
      -- Every point γ t stays inside A_X
      have hγ_in_AX : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ A_X := by
        by_contra hnot_all
        push Not at hnot_all
        let E : Set ℝ := {t ∈ Icc (0 : ℝ) 1 | γ t ∉ A_X}
        have hE_closed : IsClosed E :=
          hγ_cmd.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hAX_open.isClosed_compl
        have hE_ne : E.Nonempty := by
          obtain ⟨t, ht, hnt⟩ := hnot_all; exact ⟨t, ht, hnt⟩
        have hE_bdd : BddBelow E := ⟨0, fun t ht => ht.1.1⟩
        set t₁ := sInf E
        have ht₁_E : t₁ ∈ E := hE_closed.csInf_mem hE_ne hE_bdd
        have h0_AX : γ 0 ∈ A_X := by
          rw [hγ0]; exact ⟨M.exp p v_z, ⟨v_z, ⟨hrlo_lt_rz, hrz_lt.trans hrq_lt_rhi⟩, rfl⟩, rfl⟩
        have ht₁_pos : 0 < t₁ := by
          by_contra hle
          have h0 : t₁ = 0 := le_antisymm (not_lt.mp hle) ht₁_E.1.1
          exact ht₁_E.2 (h0 ▸ h0_AX)
        have hγ_t₁_Khi : γ t₁ ∈ Khi_X := by
          have ht_cl : t₁ ∈ closure (Ico (0 : ℝ) t₁) := by
            rw [closure_Ico ht₁_pos.ne]; exact right_mem_Icc.mpr ht₁_pos.le
          have hcont_at : ContinuousWithinAt γ (Ico 0 t₁) t₁ :=
            (hγ_cmd.continuousOn t₁ ht₁_E.1).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc_right ht₁_E.1.2))
          have hmem := hcont_at.mem_closure_image ht_cl
          have hsub : γ '' Ico (0 : ℝ) t₁ ⊆ Khi_X := by
            rintro _ ⟨t, ht, rfl⟩
            apply hAX_sub_KhiX
            by_contra hnt
            exact (csInf_le hE_bdd ⟨⟨ht.1, ht.2.le.trans ht₁_E.1.2⟩, hnt⟩).not_gt ht.2
          exact hKhiX_closed.closure_subset_iff.mpr hsub hmem
        -- Extract v₁ with γ t₁ = φ.symm (M.exp p v₁), gnorm p v₁ ≤ r_hi, and (gnorm p v₁ ≤ r_lo ∨ r_hi ≤ gnorm p v₁)
        obtain ⟨q₁, ⟨v₁, hv₁_le, rfl⟩, hγt₁_eq⟩ := hγ_t₁_Khi
        have hdist_p1 : dist (φ.symm p) (γ t₁) = M.gnorm p v₁ := by
          rw [← hγt₁_eq]; exact hdist_exp v₁ (hv₁_le.trans_lt hrhi_lt_rv)
        have hdist_pz : dist (φ.symm p) z' = r_z := hdist_exp v_z (hrz_lt.trans hrq_lt)
        have hdist_pq : dist (φ.symm p) q' = r_q := hdist_exp v_q hrq_lt
        -- Sum of distances dist z' (γ t₁) + dist (γ t₁) q' ≤ (pathELength γ 0 1).toReal < r_q - r_z + ε
        have hsum_lt : dist z' (γ t₁) + dist (γ t₁) q' < r_q - r_z + ε := by
          have h1 : edist z' (γ t₁) ≤ pathELength (𝓡 n) γ 0 t₁ := by
            rw [hRM.out]
            exact riemannianEDist_le_pathELength (hγ_cmd.mono (Icc_subset_Icc_right ht₁_E.1.2)) hγ0 rfl ht₁_E.1.1
          have h2 : edist (γ t₁) q' ≤ pathELength (𝓡 n) γ t₁ 1 := by
            rw [hRM.out]
            exact riemannianEDist_le_pathELength (hγ_cmd.mono (Icc_subset_Icc_left ht₁_E.1.1)) rfl hγ1 ht₁_E.1.2
          have hsum_e : edist z' (γ t₁) + edist (γ t₁) q' < ENNReal.ofReal (r_q - r_z + ε) :=
            (add_le_add h1 h2).trans_lt (by rw [pathELength_add ht₁_E.1.1 ht₁_E.1.2]; exact hlen_lt)
          rw [edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at hsum_e
          exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp hsum_e
        have hboundary : M.gnorm p v₁ ≤ r_lo ∨ r_hi ≤ M.gnorm p v₁ := by
          by_contra hmid
          push Not at hmid
          exact ht₁_E.2 ⟨M.exp p v₁, ⟨v₁, hmid, rfl⟩, hγt₁_eq⟩
        have hδ1 : δ₀ ≤ r_z - r_lo := min_le_left _ _
        have hδ2 : δ₀ ≤ r_hi - r_q := min_le_right _ _
        rcases hboundary with hlo | hhi
        · have hdz : r_z - r_lo ≤ dist z' (γ t₁) := by
            have := dist_triangle (φ.symm p) (γ t₁) z'
            rw [dist_comm (γ t₁) z', hdist_pz, hdist_p1] at this; linarith
          have hdq : r_q - r_lo ≤ dist (γ t₁) q' := by
            have := dist_triangle (φ.symm p) (γ t₁) q'
            rw [hdist_pq, hdist_p1] at this; linarith
          linarith
        · have hdz : r_hi - r_z ≤ dist z' (γ t₁) := by
            have := dist_triangle (φ.symm p) z' (γ t₁)
            rw [hdist_pz, hdist_p1] at this; linarith
          have hdq : r_hi - r_q ≤ dist (γ t₁) q' := by
            have := dist_triangle (φ.symm p) q' (γ t₁)
            rw [dist_comm q' (γ t₁), hdist_pq, hdist_p1] at this; linarith
          linarith
      -- Apply annulus_length_ge on [0, 1]
      let η := φ ∘ γ
      have hη_in_A : ∀ t ∈ Icc (0 : ℝ) 1, η t ∈ A := fun t ht =>
        ((hsymm_mem hA_sub).mp (hγ_in_AX t ht)).2
      have hη_ann : ∀ t ∈ Icc (0 : ℝ) 1, η t ∈ W ∧ r_lo ≤ M.gnorm p (M.log p (η t)) := by
        intro t ht
        obtain ⟨v, ⟨hv1, hv2⟩, hv_eq⟩ := hη_in_A t ht
        have hlog_v : M.log p (η t) = v := by
          rw [← hv_eq]; exact (hcore v (hv2.trans hrhi_lt_rv)).2.2.2.2.1
        exact ⟨⟨v, hv2.trans hrhi_lt_rv, hv_eq⟩, by rw [hlog_v]; exact hv1.le⟩
      have hlen_eq := pathELength_eq_ofReal_integral x₀ hr₁_tgt hg_smooth hinner zero_lt_one hγ_cmd
        (fun t ht => (image_mono hA_sub) (hγ_in_AX t ht))
      have hη_cd : ContDiffOn ℝ 1 η (Icc 0 1) := hlen_eq.1
      have hann := annulus_length_ge M hp_r1 hr_v hm_g hc₀ (hmet_rp p hp) hcore hW_open hW_log
        zero_le_one hrlo_pos hη_cd hη_ann
      have hv0 : M.log p (η 0) = v_z := by
        have hη0 : η 0 = M.exp p v_z := by
          change φ (γ 0) = M.exp p v_z
          rw [hγ0]; exact φ.right_inv (hr₁_tgt (hcore v_z (hrz_lt.trans hrq_lt)).1)
        rw [hη0]; exact (hcore v_z (hrz_lt.trans hrq_lt)).2.2.2.2.1
      have hv1 : M.log p (η 1) = v_q := by
        have hη1 : η 1 = M.exp p v_q := by
          change φ (γ 1) = M.exp p v_q
          rw [hγ1]; exact φ.right_inv (hr₁_tgt (hcore v_q hrq_lt).1)
        rw [hη1]; exact (hcore v_q hrq_lt).2.2.2.2.1
      dsimp only at hann
      rw [hv0, hv1] at hann
      rw [hlen_eq.2.2] at hlen_lt
      have hint_lt : ∫ t in (0 : ℝ)..1, M.gnorm (η t) (derivWithin η (Icc 0 1) t) < r_q - r_z + ε :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp hlen_lt
      exact hann.trans hint_lt.le
    -- Let ε → 0⁺ to deduce ‖r_q⁻¹ • v_q - r_z⁻¹ • v_z‖ = 0
    have hle0 : Real.sqrt ((r_q - r_z) ^ 2 + (c₀ * r_lo * m_g * ‖r_q⁻¹ • v_q - r_z⁻¹ • v_z‖) ^ 2) ≤
        r_q - r_z := by
      by_contra hgt
      push Not at hgt
      set diff := Real.sqrt ((r_q - r_z) ^ 2 + (c₀ * r_lo * m_g * ‖r_q⁻¹ • v_q - r_z⁻¹ • v_z‖) ^ 2) - (r_q - r_z)
      have hdiff_pos : 0 < diff := by linarith
      let ε := min (diff / 2) (δ₀ / 2)
      have hε_pos : 0 < ε := lt_min (half_pos hdiff_pos) (half_pos hδ₀_pos)
      have hε_lt : ε < δ₀ := (min_le_right _ _).trans_lt (half_lt_self hδ₀_pos)
      have hb := hbound_eps ε hε_pos hε_lt
      have hε_le : ε ≤ diff / 2 := min_le_left _ _
      linarith
    have hsq : (r_q - r_z) ^ 2 + (c₀ * r_lo * m_g * ‖r_q⁻¹ • v_q - r_z⁻¹ • v_z‖) ^ 2 ≤ (r_q - r_z) ^ 2 := by
      have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle0 2
      rwa [Real.sq_sqrt (by positivity)] at h1
    have hnorm_zero : ‖r_q⁻¹ • v_q - r_z⁻¹ • v_z‖ = 0 := by
      have hprod0 : c₀ * r_lo * m_g * ‖r_q⁻¹ • v_q - r_z⁻¹ • v_z‖ = 0 := by
        nlinarith [sq_nonneg (c₀ * r_lo * m_g * ‖r_q⁻¹ • v_q - r_z⁻¹ • v_z‖)]
      have hc_pos : 0 < c₀ * r_lo * m_g := by positivity
      exact (mul_eq_zero.mp hprod0).resolve_left hc_pos.ne'
    exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)).symm
  -- Finally prove e y = y for every y ∈ W_X, giving x₀ ∈ W_X ⊆ interior {x | e x = x}
  have he_p' : e (φ.symm p) = φ.symm p := interior_subset (s := {x : X | e x = x}) hp'_S
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp isOpen_interior (φ.symm p) hp'_S
  have he_WX : ∀ y ∈ W_X, e y = y := by
    rintro _ ⟨q, ⟨v, hv, rfl⟩, rfl⟩
    have hv_lt : M.gnorm p v < r_v := hv
    by_cases hv0 : v = 0
    · subst hv0; rwa [hexp0]
    · have hgn_pos : 0 < M.gnorm p v := M.gnorm_pos hp_r1 hv0
      set r := M.gnorm p v
      let s : ℝ := min (1 / 2) (δ / (2 * r))
      have hs_pos : 0 < s := lt_min (by norm_num) (by positivity)
      have hs_lt1 : s < 1 := (min_le_left _ _).trans_lt (by norm_num)
      have hsr_lt_δ : s * r < δ := by
        have h1 : s ≤ δ / (2 * r) := min_le_right _ _
        calc s * r ≤ (δ / (2 * r)) * r := mul_le_mul_of_nonneg_right h1 hgn_pos.le
          _ = δ / 2 := by field_simp [hgn_pos.ne']
          _ < δ := half_lt_self hδ_pos
      let z' := φ.symm (M.exp p (s • v))
      let y := φ.symm (M.exp p v)
      have hgn_sv : M.gnorm p (s • v) = s * r := by
        rw [M.gnorm_smul hp_r1, abs_of_pos hs_pos]
      have hgn_sv_lt : M.gnorm p (s • v) < r_v := by
        rw [hgn_sv]; nlinarith [hv_lt]
      have hdist_pz : dist (φ.symm p) z' = s * r := by
        rw [hdist_exp (s • v) hgn_sv_lt, hgn_sv]
      have hdist_py : dist (φ.symm p) y = r := hdist_exp v hv_lt
      have hdist_zy : dist z' y = r - s * r := by
        refine le_antisymm ?_ ?_
        · have h := hray_le v hv_lt s 1 hs_pos.le hs_lt1.le le_rfl
          simpa [one_smul, sub_mul, one_mul] using h
        · have htri := dist_triangle (φ.symm p) z' y
          rw [hdist_py, hdist_pz] at htri; linarith
      have hz'_S : z' ∈ S := hδ_sub (by rw [Metric.mem_ball, dist_comm, hdist_pz]; exact hsr_lt_δ)
      have he_z' : e z' = z' := interior_subset (s := {x : X | e x = x}) hz'_S
      have hdist_pey : dist (φ.symm p) (e y) = r := by
        rw [← he_p', he.dist_eq, hdist_py]
      have hey_WX : e y ∈ W_X := by
        by_contra hnot
        have := hdist_outside (e y) hnot
        linarith [hv_lt]
      obtain ⟨q_e, ⟨v_e, hv_e, rfl⟩, hey_eq⟩ := hey_WX
      have hgn_ve : M.gnorm p v_e = r := by
        have := hdist_exp v_e hv_e
        rw [hey_eq, hdist_pey] at this
        exact this.symm
      have hdist_zey : dist z' (φ.symm (M.exp p v_e)) = M.gnorm p v_e - M.gnorm p (s • v) := by
        rw [hey_eq, ← he_z', he.dist_eq, hdist_zy, hgn_ve, hgn_sv]
      have hdir := hray_unique (s • v) v_e (by rw [hgn_sv]; positivity)
        (by rw [hgn_sv, hgn_ve]; nlinarith) (hgn_ve.symm ▸ hv_lt) hdist_zey
      have hve_eq : v_e = v := by
        rw [hgn_sv, hgn_ve, smul_smul] at hdir
        have hcoef : (s * r)⁻¹ * s = r⁻¹ := by field_simp [hs_pos.ne', hgn_pos.ne']
        rw [hcoef] at hdir
        have := congrArg (fun w : Euc n => r • w) hdir
        simp only [smul_smul, mul_inv_cancel₀ hgn_pos.ne', one_smul] at this
        exact this.symm
      rw [← hey_eq, hve_eq]
  exact mem_interior.mpr ⟨W_X, he_WX, hWX_open, hx₀_WX⟩

end UniqueContinuation

end OMA.Hilbert5H2

theorem OMA.solution : OMA.R_Hilbert5_hilbert_smith_conjecture_variants_riemannian_R1.H2 := by
  intro n X _ _ _ _ _ _ _ e he ⟨U, hU_open, hU_ne, hU_fix⟩
  let S : Set X := interior {x : X | e x = x}
  have hS_ne : S.Nonempty := hU_ne.mono (interior_maximal hU_fix hU_open)
  have hS_clopen : IsClopen S :=
    ⟨closure_subset_iff_isClosed.mp fun x₀ hx₀ =>
      OMA.Hilbert5H2.local_unique_continuation (n := n) e he x₀ hx₀, isOpen_interior⟩
  have hS_univ : S = Set.univ := hS_clopen.eq_univ hS_ne
  ext x
  have hx : x ∈ S := hS_univ ▸ Set.mem_univ x
  show e x = x
  exact interior_subset (s := {x : X | e x = x}) hx

