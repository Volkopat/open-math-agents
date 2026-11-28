import OMAReductions.R_Borsuk_borsuk_conjecture_four_eight_parts_R1
import Mathlib

/-!
# Eight-part Borsuk cover in four dimensions for intermediate circumradius

This file proves `OMA.R_Borsuk_borsuk_conjecture_four_eight_parts_R1.H1`:
every compact nontrivial subset `K ⊂ ℝ⁴` whose circumradius lies in `(4/7, 627/1000] · diam K`
can be covered by eight closed sets, none of which contains a diametral pair of `K`.

## Proof outline

1. **Single-body reduction (`exists_norm_map_to_LStar2`)**:
   Rescaling `K` to unit diameter and shifting the enclosing center away from a farthest point
   `a ∈ K` places `K` inside the fixed Lassak lens `‖y‖ ≤ 627/1000`, `‖y - aStd‖ ≤ 1` with
   `aStd = (0, 0, 0, 627/1000)`. Applying the one-dimensional intermediate value theorem twice
   in `aStd⊥` (following the orthogonal-slabs idea of Tolmachev and Voronov, arXiv:2605.19068)
   gives `|y₀| ≤ 1/2` and `|y₁| ≤ 1/2`. Dihedral symmetries of the `(y₀, y₁)` square and a sign
   flip on `y₂` then simultaneously enforce `y₂ ≤ 1/2`, `y₀ + y₁ ≤ 99/140`, and
   `y₀ - y₁ ≤ 99/140` with zero case branching. Thus every `K` maps isometrically (up to scale)
   into one single fixed four-dimensional body `L**(0.627)`.

2. **Eight affine cells and rational outer polytopes**:
   We partition `ℝ⁴` into eight closed cells `Cⱼ = {y | ∀ k, ⟨cₖ, y⟩ + bₖ ≤ ⟨cⱼ, y⟩ + bⱼ}`
   using exact integer affine functionals, and enclose each `L**(0.627) ∩ Cⱼ` in an explicit
   simple rational four-dimensional polytope `Pⱼ` cut out by base inequalities, valid integer
   tangent hyperplanes to the two balls `B(0, 627/1000)` and `B(aStd, 1)`, and the seven cell
   inequalities.

3. **Polar-duality vertex containment (`polar_polytope_subset_convexHull`)**:
   For each simple vertex `vₖ = pₖ / dₖ` of `Pⱼ`, we exhibit its four active facets and four
   edge-adjacent neighbor vertices `wₛ` lying on the three complementary active facets and
   strictly inside the fourth. By Hahn--Banach separation, every `x ∈ Pⱼ` lies in the convex
   hull of the listed vertices. A centroid-pruned exact integer check (`verifyCell`) certifies
   that every pair of vertices of `Pⱼ` has Euclidean distance strictly less than `1`, whence
   `diam (L**(0.627) ∩ Cⱼ) < 1` for all eight cells.
-/

noncomputable section

namespace BorsukEightH1

open Metric Bornology
open scoped EuclideanGeometry InnerProductSpace BigOperators

abbrev E4 := EuclideanSpace ℝ (Fin 4)

/- Part 1: Normalization and 1D-IVT reduction to the single fixed body L**(0.627) -/

private def R0 : ℝ := 627 / 1000
private def aStd : E4 := EuclideanSpace.single (3 : Fin 4) R0

private def InLStar2 (y : E4) : Prop :=
  ‖y‖ ≤ R0 ∧
  ‖y - aStd‖ ≤ 1 ∧
  -(1 / 2 : ℝ) ≤ y 0 ∧ y 0 ≤ 1 / 2 ∧
  -(1 / 2 : ℝ) ≤ y 1 ∧ y 1 ≤ 1 / 2 ∧
  y 2 ≤ 1 / 2 ∧
  y 0 + y 1 ≤ 99 / 140 ∧
  y 0 - y 1 ≤ 99 / 140

private lemma norm_rot_unit {v₁ v₂ : E4} (hv₁ : ‖v₁‖ = 1) (hv₂ : ‖v₂‖ = 1)
    (horth : ⟪v₁, v₂⟫_ℝ = 0) (θ : ℝ) :
    ‖Real.cos θ • v₁ + Real.sin θ • v₂‖ = 1 := by
  have horth' : ⟪v₂, v₁⟫_ℝ = 0 := by rw [real_inner_comm, horth]
  have hsq : ‖Real.cos θ • v₁ + Real.sin θ • v₂‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      conj_trivial, real_inner_self_eq_norm_sq, hv₁, hv₂, horth, horth']
    nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg (Real.cos θ • v₁ + Real.sin θ • v₂)]

private lemma norm_rot_perp {v₁ v₂ : E4} (hv₁ : ‖v₁‖ = 1) (hv₂ : ‖v₂‖ = 1)
    (horth : ⟪v₁, v₂⟫_ℝ = 0) (θ : ℝ) :
    ‖(-Real.sin θ) • v₁ + Real.cos θ • v₂‖ = 1 := by
  have horth' : ⟪v₂, v₁⟫_ℝ = 0 := by rw [real_inner_comm, horth]
  have hsq : ‖(-Real.sin θ) • v₁ + Real.cos θ • v₂‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      conj_trivial, real_inner_self_eq_norm_sq, hv₁, hv₂, horth, horth']
    nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg ((-Real.sin θ) • v₁ + Real.cos θ • v₂)]

private lemma inner_rot_perp {v₁ v₂ : E4} (hv₁ : ‖v₁‖ = 1) (hv₂ : ‖v₂‖ = 1)
    (horth : ⟪v₁, v₂⟫_ℝ = 0) (θ : ℝ) :
    ⟪Real.cos θ • v₁ + Real.sin θ • v₂, (-Real.sin θ) • v₁ + Real.cos θ • v₂⟫_ℝ = 0 := by
  have horth' : ⟪v₂, v₁⟫_ℝ = 0 := by rw [real_inner_comm, horth]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    conj_trivial, real_inner_self_eq_norm_sq, hv₁, hv₂, horth, horth']
  ring

private lemma exists_balanced_unit_in_plane {S : Set E4} (hS : IsCompact S) (hne : S.Nonempty)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1)
    {v₁ v₂ : E4} (hv₁ : ‖v₁‖ = 1) (hv₂ : ‖v₂‖ = 1) (horth : ⟪v₁, v₂⟫_ℝ = 0) :
    ∃ θ : ℝ, ∀ x ∈ S, |⟪x, Real.cos θ • v₁ + Real.sin θ • v₂⟫_ℝ| ≤ 1 / 2 := by
  let w (θ : ℝ) : E4 := Real.cos θ • v₁ + Real.sin θ • v₂
  have hw_norm (θ : ℝ) : ‖w θ‖ = 1 := norm_rot_unit hv₁ hv₂ horth θ
  have hw_neg (θ : ℝ) : w (θ + Real.pi) = -w θ := by
    simp only [w, Real.cos_add_pi, Real.sin_add_pi, neg_smul]
    abel
  have hw_cont : Continuous w := by fun_prop
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall (0 : E4)
  let M (θ : ℝ) : ℝ := sSup ((fun x => ⟪x, w θ⟫_ℝ) '' S)
  have hM_att (θ : ℝ) : ∃ x ∈ S, ⟪x, w θ⟫_ℝ = M θ ∧ ∀ y ∈ S, ⟪y, w θ⟫_ℝ ≤ M θ := by
    obtain ⟨x, hx, hmax⟩ := hS.exists_isMaxOn hne
      (show Continuous (fun z : E4 => ⟪z, w θ⟫_ℝ) by fun_prop).continuousOn
    have hg : IsGreatest ((fun y => ⟪y, w θ⟫_ℝ) '' S) ⟪x, w θ⟫_ℝ := by
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact hmax hy
    have hEq : M θ = ⟪x, w θ⟫_ℝ := hg.csSup_eq
    exact ⟨x, hx, hEq.symm, fun y hy => hEq.symm ▸ hmax hy⟩
  have hM_sum (θ : ℝ) : M θ + M (θ + Real.pi) ≤ 1 := by
    obtain ⟨x, hx, hxM, _⟩ := hM_att θ
    obtain ⟨y, hy, hyM, _⟩ := hM_att (θ + Real.pi)
    rw [← hxM, ← hyM, hw_neg, inner_neg_right, ← sub_eq_add_neg, ← inner_sub_left]
    calc ⟪x - y, w θ⟫_ℝ ≤ ‖x - y‖ * ‖w θ‖ := real_inner_le_norm _ _
      _ = dist x y := by rw [hw_norm, mul_one, dist_eq_norm]
      _ ≤ 1 := hdiam x hx y hy
  have hM_cont : Continuous M := by
    have hLip : ∀ θ₁ θ₂, |M θ₁ - M θ₂| ≤ max R 0 * ‖w θ₁ - w θ₂‖ := by
      have hone (θ₁ θ₂ : ℝ) : M θ₁ - M θ₂ ≤ max R 0 * ‖w θ₁ - w θ₂‖ := by
        obtain ⟨x, hx, hxM, _⟩ := hM_att θ₁
        obtain ⟨_, _, _, hyM⟩ := hM_att θ₂
        have hxR : ‖x‖ ≤ max R 0 := (mem_closedBall_zero_iff.mp (hR hx)).trans (le_max_left _ _)
        calc M θ₁ - M θ₂ ≤ ⟪x, w θ₁⟫_ℝ - ⟪x, w θ₂⟫_ℝ := by linarith [hyM x hx]
          _ = ⟪x, w θ₁ - w θ₂⟫_ℝ := by rw [inner_sub_right]
          _ ≤ ‖x‖ * ‖w θ₁ - w θ₂‖ := real_inner_le_norm _ _
          _ ≤ max R 0 * ‖w θ₁ - w θ₂‖ := mul_le_mul_of_nonneg_right hxR (norm_nonneg _)
      intro θ₁ θ₂
      rw [abs_le]
      exact ⟨by have := hone θ₂ θ₁; rw [norm_sub_rev] at this; linarith, hone θ₁ θ₂⟩
    rw [Metric.continuous_iff]
    intro θ ε hε
    have hpos : 0 < max R 0 + 1 := by positivity
    obtain ⟨δ, hδ, hcont⟩ :=
      Metric.continuous_iff.mp hw_cont θ (ε / (max R 0 + 1)) (div_pos hε hpos)
    refine ⟨δ, hδ, fun θ' hθ' => ?_⟩
    have hw' : ‖w θ' - w θ‖ < ε / (max R 0 + 1) := by
      simpa [dist_eq_norm] using hcont θ' hθ'
    rw [Real.dist_eq]
    calc |M θ' - M θ| ≤ max R 0 * ‖w θ' - w θ‖ := hLip θ' θ
      _ ≤ (max R 0 + 1) * ‖w θ' - w θ‖ := by nlinarith [norm_nonneg (w θ' - w θ)]
      _ < (max R 0 + 1) * (ε / (max R 0 + 1)) := mul_lt_mul_of_pos_left hw' hpos
      _ = ε := mul_div_cancel₀ ε hpos.ne'
  let g (θ : ℝ) : ℝ := M θ - M (θ + Real.pi)
  have hg_cont : Continuous g := hM_cont.sub (hM_cont.comp (continuous_id.add continuous_const))
  have hg_pi : g Real.pi = -g 0 := by
    have h2pi : w (Real.pi + Real.pi) = w 0 := by
      rw [hw_neg, ← zero_add Real.pi, hw_neg, neg_neg]
    have hM2pi : M (Real.pi + Real.pi) = M 0 := by simp only [M, h2pi]
    dsimp [g]
    rw [zero_add, hM2pi]
    ring
  have hex : ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi, g θ = 0 := by
    by_cases h0 : 0 ≤ g 0
    · exact intermediate_value_Icc' Real.pi_pos.le hg_cont.continuousOn ⟨by linarith, h0⟩
    · exact intermediate_value_Icc Real.pi_pos.le hg_cont.continuousOn ⟨le_of_not_ge h0, by linarith⟩
  obtain ⟨θ, _, hθ⟩ := hex
  refine ⟨θ, fun x hx => ?_⟩
  have h1 : M θ ≤ 1 / 2 := by have := hM_sum θ; dsimp [g] at hθ; linarith
  have h2 : M (θ + Real.pi) ≤ 1 / 2 := by have := hM_sum θ; dsimp [g] at hθ; linarith
  obtain ⟨_, _, _, hle1⟩ := hM_att θ
  obtain ⟨_, _, _, hle2⟩ := hM_att (θ + Real.pi)
  rw [abs_le]
  exact ⟨by have := hle2 x hx; rw [hw_neg, inner_neg_right] at this; linarith,
    (hle1 x hx).trans h1⟩

private lemma unit_halfspace_dichotomy {S : Set E4} (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1)
    {v : E4} (hv : ‖v‖ = 1) :
    (∀ x ∈ S, ⟪x, v⟫_ℝ ≤ 1 / 2) ∨ (∀ x ∈ S, ⟪x, -v⟫_ℝ ≤ 1 / 2) := by
  by_contra h
  push Not at h
  obtain ⟨⟨x, hx, hxv⟩, ⟨y, hy, hyv⟩⟩ := h
  rw [inner_neg_right] at hyv
  have h1 : 1 < ⟪x - y, v⟫_ℝ := by rw [inner_sub_left]; linarith
  have h2 : ⟪x - y, v⟫_ℝ ≤ 1 := by
    calc ⟪x - y, v⟫_ℝ ≤ ‖x - y‖ * ‖v‖ := real_inner_le_norm _ _
      _ = dist x y := by rw [hv, mul_one, dist_eq_norm]
      _ ≤ 1 := hdiam x hx y hy
  linarith

private lemma dihedral_select {K₂ : Set E4} (hdiam : ∀ x ∈ K₂, ∀ y ∈ K₂, dist x y ≤ 1)
    {e₀ e₁ e₂₀ e₃ : E4} (he₀ : ‖e₀‖ = 1) (he₁ : ‖e₁‖ = 1) (he₀₁ : ⟪e₀, e₁⟫_ℝ = 0)
    (he₀2 : ⟪e₀, e₂₀⟫_ℝ = 0) (he₁2 : ⟪e₁, e₂₀⟫_ℝ = 0)
    (he₀3 : ⟪e₀, e₃⟫_ℝ = 0) (he₁3 : ⟪e₁, e₃⟫_ℝ = 0)
    (hθ : ∀ x ∈ K₂, |⟪x, e₀⟫_ℝ| ≤ 1 / 2) (hφ : ∀ x ∈ K₂, |⟪x, e₁⟫_ℝ| ≤ 1 / 2) :
    ∃ f₀ f₁ : E4, ‖f₀‖ = 1 ∧ ‖f₁‖ = 1 ∧ ⟪f₀, f₁⟫_ℝ = 0 ∧
      ⟪f₀, e₂₀⟫_ℝ = 0 ∧ ⟪f₁, e₂₀⟫_ℝ = 0 ∧ ⟪f₀, e₃⟫_ℝ = 0 ∧ ⟪f₁, e₃⟫_ℝ = 0 ∧
      (∀ x ∈ K₂, |⟪x, f₀⟫_ℝ| ≤ 1 / 2 ∧ |⟪x, f₁⟫_ℝ| ≤ 1 / 2 ∧
        ⟪x, f₀⟫_ℝ + ⟪x, f₁⟫_ℝ ≤ 99 / 140 ∧ ⟪x, f₀⟫_ℝ - ⟪x, f₁⟫_ℝ ≤ 99 / 140) := by
  have he₁₀ : ⟪e₁, e₀⟫_ℝ = 0 := by rw [real_inner_comm, he₀₁]
  have hs2sq : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = 1 / 2 := by
    rw [one_div_mul_one_div, Real.mul_self_sqrt (by norm_num)]
  have hdiag_pos_norm : ‖(1 / Real.sqrt 2 : ℝ) • (e₀ + e₁)‖ = 1 := by
    have hsq : ‖(1 / Real.sqrt 2 : ℝ) • (e₀ + e₁)‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_smul_left, inner_smul_right, conj_trivial, inner_add_left, inner_add_right,
        real_inner_self_eq_norm_sq, he₀, he₁, he₀₁, he₁₀]
      nlinarith
    nlinarith [norm_nonneg ((1 / Real.sqrt 2 : ℝ) • (e₀ + e₁))]
  have hdiag_neg_norm : ‖(1 / Real.sqrt 2 : ℝ) • (e₀ - e₁)‖ = 1 := by
    have hsq : ‖(1 / Real.sqrt 2 : ℝ) • (e₀ - e₁)‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_smul_left, inner_smul_right, conj_trivial, inner_sub_left, inner_sub_right,
        real_inner_self_eq_norm_sq, he₀, he₁, he₀₁, he₁₀]
      nlinarith
    nlinarith [norm_nonneg ((1 / Real.sqrt 2 : ℝ) • (e₀ - e₁))]
  have hdp := unit_halfspace_dichotomy hdiam hdiag_pos_norm
  have hdm := unit_halfspace_dichotomy hdiam hdiag_neg_norm
  have hs2_lt : Real.sqrt 2 / 2 ≤ 99 / 140 := by
    have : Real.sqrt 2 ≤ 99 / 70 := by rw [Real.sqrt_le_iff]; constructor <;> norm_num
    linarith
  have hsc (x : E4) (v : E4) (h : ⟪x, (1 / Real.sqrt 2 : ℝ) • v⟫_ℝ ≤ 1 / 2) :
      ⟪x, v⟫_ℝ ≤ 99 / 140 := by
    rw [inner_smul_right] at h
    have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h1 : ⟪x, v⟫_ℝ ≤ Real.sqrt 2 / 2 := by
      have := mul_le_mul_of_nonneg_left h hs2.le
      have hcancel : Real.sqrt 2 * (1 / Real.sqrt 2 * ⟪x, v⟫_ℝ) = ⟪x, v⟫_ℝ := by
        field_simp [hs2.ne']
      linarith
    exact h1.trans hs2_lt
  rcases hdp with hp | hp <;> rcases hdm with hm | hm
  · refine ⟨e₀, e₁, he₀, he₁, he₀₁, he₀2, he₁2, he₀3, he₁3, fun x hx => ?_⟩
    refine ⟨hθ x hx, hφ x hx, ?_, ?_⟩
    · simpa [inner_add_right] using hsc x (e₀ + e₁) (hp x hx)
    · simpa [inner_sub_right] using hsc x (e₀ - e₁) (hm x hx)
  · refine ⟨e₁, e₀, he₁, he₀, he₁₀, he₁2, he₀2, he₁3, he₀3, fun x hx => ?_⟩
    refine ⟨hφ x hx, hθ x hx, ?_, ?_⟩
    · have := hsc x (e₀ + e₁) (hp x hx); rw [inner_add_right] at this; linarith
    · have h1 := hm x hx; rw [← smul_neg] at h1
      have := hsc x (-(e₀ - e₁)) h1
      rw [inner_neg_right, inner_sub_right] at this; linarith
  · refine ⟨-e₁, -e₀, by simp [he₁], by simp [he₀], by simp [he₁₀],
      by simp [he₁2], by simp [he₀2], by simp [he₁3], by simp [he₀3], fun x hx => ?_⟩
    refine ⟨by simpa [inner_neg_right] using hφ x hx,
      by simpa [inner_neg_right] using hθ x hx, ?_, ?_⟩
    · have h1 := hp x hx; rw [← smul_neg] at h1
      have := hsc x (-(e₀ + e₁)) h1
      simp only [inner_neg_right, inner_add_right] at this ⊢; linarith
    · have := hsc x (e₀ - e₁) (hm x hx)
      simp only [inner_neg_right, inner_sub_right] at this ⊢; linarith
  · refine ⟨-e₀, -e₁, by simp [he₀], by simp [he₁], by simp [he₀₁],
      by simp [he₀2], by simp [he₁2], by simp [he₀3], by simp [he₁3], fun x hx => ?_⟩
    refine ⟨by simpa [inner_neg_right] using hθ x hx,
      by simpa [inner_neg_right] using hφ x hx, ?_, ?_⟩
    · have h1 := hp x hx; rw [← smul_neg] at h1
      have := hsc x (-(e₀ + e₁)) h1
      simp only [inner_neg_right, inner_add_right] at this ⊢; linarith
    · have h1 := hm x hx; rw [← smul_neg] at h1
      have := hsc x (-(e₀ - e₁)) h1
      simp only [inner_neg_right, inner_sub_right] at this ⊢; linarith

private lemma exists_norm_map_to_LStar2 {K : Set E4} (hK : IsCompact K) (hnt : K.Nontrivial)
    (hlo : ∀ c, ∃ x ∈ K, (4 / 7 : ℝ) * diam K < dist x c)
    (hhi : ∃ c, ∀ x ∈ K, dist x c ≤ R0 * diam K) :
    ∃ Φ : E4 → E4, Continuous Φ ∧
      (∀ x y, dist (Φ x) (Φ y) = (diam K)⁻¹ * dist x y) ∧
      (∀ x ∈ K, InLStar2 (Φ x)) := by
  classical
  let D := diam K
  have hD : 0 < D := diam_pos hnt hK.isBounded
  obtain ⟨c₀, hc₀⟩ := hhi
  let f₁ (x : E4) : E4 := D⁻¹ • (x - c₀)
  have hf₁_dist (x y : E4) : dist (f₁ x) (f₁ y) = D⁻¹ * dist x y := by
    simp only [f₁, dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hD)]
  have hf₁_cont : Continuous f₁ := by fun_prop
  let K₁ := f₁ '' K
  have hK₁ : IsCompact K₁ := hK.image hf₁_cont
  have hne₁ : K₁.Nonempty := hnt.nonempty.image f₁
  have hK₁_hi (x) (hx : x ∈ K₁) : ‖x‖ ≤ R0 := by
    rcases hx with ⟨x₀, hx₀, rfl⟩
    have := hc₀ x₀ hx₀
    rw [dist_eq_norm] at this
    simp only [f₁, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hD)]
    calc D⁻¹ * ‖x₀ - c₀‖ ≤ D⁻¹ * (R0 * D) := mul_le_mul_of_nonneg_left this (inv_pos.mpr hD).le
      _ = R0 := by field_simp [hD.ne']
  obtain ⟨a, ha, hmax⟩ := hK₁.exists_isMaxOn hne₁ continuous_norm.continuousOn
  let r₀ := ‖a‖
  have hr₀_pos : 0 < r₀ := by
    obtain ⟨x₀, hx₀, hfar⟩ := hlo c₀
    have hle : ‖f₁ x₀‖ ≤ r₀ := hmax ⟨x₀, hx₀, rfl⟩
    have hgt : (4 / 7 : ℝ) < ‖f₁ x₀‖ := by
      rw [dist_eq_norm] at hfar
      simp only [f₁, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hD)]
      have hmul := mul_lt_mul_of_pos_left hfar (inv_pos.mpr hD)
      have hsimp : D⁻¹ * ((4 / 7 : ℝ) * D) = 4 / 7 := by field_simp [hD.ne']
      linarith
    linarith
  have hr₀_le : r₀ ≤ R0 := hK₁_hi a ha
  let s : E4 := (1 - R0 / r₀) • a
  let g₂ (x : E4) : E4 := f₁ x - s
  have hg₂_dist (x y : E4) : dist (g₂ x) (g₂ y) = D⁻¹ * dist x y := by
    simp only [g₂, dist_sub_right, hf₁_dist]
  have hg₂_cont : Continuous g₂ := hf₁_cont.sub continuous_const
  let K₂ := g₂ '' K
  have hK₂ : IsCompact K₂ := hK.image hg₂_cont
  have hne₂ : K₂.Nonempty := hnt.nonempty.image g₂
  have hK₂_diam (x) (hx : x ∈ K₂) (y) (hy : y ∈ K₂) : dist x y ≤ 1 := by
    rcases hx with ⟨x₀, hx₀, rfl⟩; rcases hy with ⟨y₀, hy₀, rfl⟩
    rw [hg₂_dist]
    have hd := dist_le_diam_of_mem hK.isBounded hx₀ hy₀
    exact (mul_le_mul_of_nonneg_left hd (inv_pos.mpr hD).le).trans_eq (inv_mul_cancel₀ hD.ne')
  have hK₂_ball (x) (hx : x ∈ K₂) : ‖x‖ ≤ R0 := by
    rcases hx with ⟨x₀, hx₀, rfl⟩
    have h1 : ‖f₁ x₀‖ ≤ r₀ := hmax ⟨x₀, hx₀, rfl⟩
    have hs : ‖s‖ = R0 - r₀ := by
      have hnonpos : 1 - R0 / r₀ ≤ 0 := by rw [sub_nonpos, one_le_div hr₀_pos]; exact hr₀_le
      simp only [s, norm_smul, Real.norm_eq_abs, abs_of_nonpos hnonpos]
      change -(1 - R0 / r₀) * r₀ = R0 - r₀
      field_simp [hr₀_pos.ne']; ring
    calc ‖g₂ x₀‖ = ‖f₁ x₀ - s‖ := rfl
      _ ≤ ‖f₁ x₀‖ + ‖s‖ := norm_sub_le _ _
      _ ≤ r₀ + (R0 - r₀) := by linarith
      _ = R0 := by ring
  let a₂ : E4 := a - s
  have ha₂_mem : a₂ ∈ K₂ := by rcases ha with ⟨a₀, ha₀, rfl⟩; exact ⟨a₀, ha₀, rfl⟩
  have hR0pos : 0 < R0 := by norm_num [R0]
  have ha₂_norm : ‖a₂‖ = R0 := by
    have hEq : a₂ = (R0 / r₀) • a := by dsimp [a₂, s]; rw [sub_smul, one_smul]; abel
    rw [hEq, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR0pos hr₀_pos)]
    exact div_mul_cancel₀ R0 hr₀_pos.ne'
  let u₃ : E4 := R0⁻¹ • a₂
  have hu₃ : ‖u₃‖ = 1 := by
    simp only [u₃, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR0pos), ha₂_norm]
    exact inv_mul_cancel₀ hR0pos.ne'
  have horth3 : Orthonormal ℝ (({(3 : Fin 4)} : Set (Fin 4)).domRestrict (fun _ : Fin 4 => u₃)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have he : i = j := Subtype.ext (i.property.trans j.property.symm)
    simp [he, Set.domRestrict, hu₃]
  obtain ⟨b₀, hb₀⟩ := horth3.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ E4 = Fintype.card (Fin 4) by simp [E4])
  have hb₀3 : b₀ 3 = u₃ := hb₀ 3 (Set.mem_singleton _)
  have hb₀_norm (i : Fin 4) : ‖b₀ i‖ = 1 := b₀.orthonormal.1 i
  have hb₀_orth {i j : Fin 4} (h : i ≠ j) : ⟪b₀ i, b₀ j⟫_ℝ = 0 := b₀.orthonormal.2 h
  obtain ⟨θ, hθ⟩ := exists_balanced_unit_in_plane hK₂ hne₂ hK₂_diam
    (hb₀_norm 0) (hb₀_norm 1) (hb₀_orth (by decide))
  let e₀ : E4 := Real.cos θ • b₀ 0 + Real.sin θ • b₀ 1
  let e₀' : E4 := (-Real.sin θ) • b₀ 0 + Real.cos θ • b₀ 1
  have he₀_norm : ‖e₀‖ = 1 := norm_rot_unit (hb₀_norm 0) (hb₀_norm 1) (hb₀_orth (by decide)) θ
  have he₀'_norm : ‖e₀'‖ = 1 := norm_rot_perp (hb₀_norm 0) (hb₀_norm 1) (hb₀_orth (by decide)) θ
  have he₀_e₀' : ⟪e₀, e₀'⟫_ℝ = 0 := inner_rot_perp (hb₀_norm 0) (hb₀_norm 1) (hb₀_orth (by decide)) θ
  have he₀_b2 : ⟪e₀, b₀ 2⟫_ℝ = 0 := by
    simp [e₀, inner_add_left, inner_smul_left, hb₀_orth (by decide : (0:Fin 4) ≠ 2),
      hb₀_orth (by decide : (1:Fin 4) ≠ 2)]
  have he₀'_b2 : ⟪e₀', b₀ 2⟫_ℝ = 0 := by
    simp [e₀', inner_add_left, inner_smul_left, hb₀_orth (by decide : (0:Fin 4) ≠ 2),
      hb₀_orth (by decide : (1:Fin 4) ≠ 2)]
  have he₀_b3 : ⟪e₀, b₀ 3⟫_ℝ = 0 := by
    simp [e₀, inner_add_left, inner_smul_left, hb₀_orth (by decide : (0:Fin 4) ≠ 3),
      hb₀_orth (by decide : (1:Fin 4) ≠ 3)]
  have he₀'_b3 : ⟪e₀', b₀ 3⟫_ℝ = 0 := by
    simp [e₀', inner_add_left, inner_smul_left, hb₀_orth (by decide : (0:Fin 4) ≠ 3),
      hb₀_orth (by decide : (1:Fin 4) ≠ 3)]
  obtain ⟨φ, hφ⟩ := exists_balanced_unit_in_plane hK₂ hne₂ hK₂_diam
    he₀'_norm (hb₀_norm 2) he₀'_b2
  let e₁ : E4 := Real.cos φ • e₀' + Real.sin φ • b₀ 2
  let e₂₀ : E4 := (-Real.sin φ) • e₀' + Real.cos φ • b₀ 2
  have he₁_norm : ‖e₁‖ = 1 := norm_rot_unit he₀'_norm (hb₀_norm 2) he₀'_b2 φ
  have he₂₀_norm : ‖e₂₀‖ = 1 := norm_rot_perp he₀'_norm (hb₀_norm 2) he₀'_b2 φ
  have he₀_e₁ : ⟪e₀, e₁⟫_ℝ = 0 := by
    simp [e₁, inner_add_right, inner_smul_right, he₀_e₀', he₀_b2]
  have he₀_e₂₀ : ⟪e₀, e₂₀⟫_ℝ = 0 := by
    simp [e₂₀, inner_add_right, inner_smul_right, he₀_e₀', he₀_b2]
  have he₁_e₂₀ : ⟪e₁, e₂₀⟫_ℝ = 0 := inner_rot_perp he₀'_norm (hb₀_norm 2) he₀'_b2 φ
  have he₁_b3 : ⟪e₁, b₀ 3⟫_ℝ = 0 := by
    simp [e₁, inner_add_left, inner_smul_left, he₀'_b3, hb₀_orth (by decide : (2:Fin 4) ≠ 3)]
  have he₂₀_b3 : ⟪e₂₀, b₀ 3⟫_ℝ = 0 := by
    simp [e₂₀, inner_add_left, inner_smul_left, he₀'_b3, hb₀_orth (by decide : (2:Fin 4) ≠ 3)]
  obtain ⟨f₀, f₁, hf₀, hf₁, hf₀₁, hf₀2, hf₁2, hf₀3, hf₁3, hf01_bd⟩ :=
    dihedral_select hK₂_diam he₀_norm he₁_norm he₀_e₁ he₀_e₂₀ he₁_e₂₀ he₀_b3 he₁_b3 hθ hφ
  have hf₂_ex : ∃ f₂ : E4, ‖f₂‖ = 1 ∧ ⟪f₀, f₂⟫_ℝ = 0 ∧ ⟪f₁, f₂⟫_ℝ = 0 ∧ ⟪f₂, b₀ 3⟫_ℝ = 0 ∧
      ∀ x ∈ K₂, ⟪x, f₂⟫_ℝ ≤ 1 / 2 := by
    rcases unit_halfspace_dichotomy hK₂_diam he₂₀_norm with h2p | h2m
    · exact ⟨e₂₀, he₂₀_norm, hf₀2, hf₁2, he₂₀_b3, h2p⟩
    · exact ⟨-e₂₀, by simp [he₂₀_norm], by simp [hf₀2], by simp [hf₁2], by simp [he₂₀_b3], h2m⟩
  obtain ⟨f₂, hf₂, hf₀f₂, hf₁f₂, hf₂3, hf2_bd⟩ := hf₂_ex
  let vecs : Fin 4 → E4 := ![f₀, f₁, f₂, b₀ 3]
  have horth_vecs : Orthonormal ℝ vecs := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [vecs, hf₀, hf₁, hf₂, hb₀_norm,
        hf₀₁, hf₀f₂, hf₁f₂, hf₀3, hf₁3, hf₂3, real_inner_comm]
  have horth_univ : Orthonormal ℝ ((Set.univ : Set (Fin 4)).domRestrict vecs) :=
    horth_vecs.comp Subtype.val Subtype.val_injective
  obtain ⟨B, hB⟩ := horth_univ.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ E4 = Fintype.card (Fin 4) by simp [E4])
  have hB_eq (i : Fin 4) : B i = vecs i := hB i (Set.mem_univ i)
  let Φ (x : E4) : E4 := B.repr (g₂ x)
  refine ⟨Φ, B.repr.continuous.comp hg₂_cont, ?_, ?_⟩
  · intro x y
    dsimp [Φ]
    rw [B.repr.isometry.dist_eq, hg₂_dist]
  · intro x hx
    have hx₂ : g₂ x ∈ K₂ := ⟨x, hx, rfl⟩
    have hcoord (i : Fin 4) : Φ x i = ⟪g₂ x, vecs i⟫_ℝ := by
      dsimp [Φ]
      rw [B.repr_apply_apply, hB_eq, real_inner_comm]
    have h01 := hf01_bd (g₂ x) hx₂
    have h2 := hf2_bd (g₂ x) hx₂
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [Φ]; rw [B.repr.norm_map]; exact hK₂_ball _ hx₂
    · have ha_eq : B.repr a₂ = aStd := by
        ext i
        rw [B.repr_apply_apply, hB_eq]
        have ha₂_smul : a₂ = R0 • b₀ 3 := by
          rw [hb₀3]; dsimp [u₃]; rw [smul_smul, mul_inv_cancel₀ hR0pos.ne', one_smul]
        rw [ha₂_smul, inner_smul_right]
        fin_cases i <;> simp [vecs, aStd, hf₀3, hf₁3, hf₂3, hb₀_norm]
      dsimp [Φ]
      rw [← ha_eq, ← map_sub, B.repr.norm_map, ← dist_eq_norm]
      exact hK₂_diam _ hx₂ _ ha₂_mem
    · rw [hcoord 0]; exact (abs_le.mp h01.1).1
    · rw [hcoord 0]; exact (abs_le.mp h01.1).2
    · rw [hcoord 1]; exact (abs_le.mp h01.2.1).1
    · rw [hcoord 1]; exact (abs_le.mp h01.2.1).2
    · rw [hcoord 2]; exact h2
    · rw [hcoord 0, hcoord 1]; exact h01.2.2.1
    · rw [hcoord 0, hcoord 1]; exact h01.2.2.2

/- Part 2: Polar-duality polytope containment and fast kernel-decidable verifier -/

private def S_SCALE : ℕ := 65536
private def S_OFF : ℕ := 65536

private abbrev IVec4 := ℤ × ℤ × ℤ × ℤ
private abbrev NVec4 := ℕ × ℕ × ℕ × ℕ

private def dotIV (a b : IVec4) : ℤ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2.1 * b.2.2.1 + a.2.2.2 * b.2.2.2

private def ivAt (a : IVec4) : Fin 4 → ℤ
  | ⟨0, _⟩ => a.1
  | ⟨1, _⟩ => a.2.1
  | ⟨2, _⟩ => a.2.2.1
  | ⟨3, _⟩ => a.2.2.2

private def nvAt (a : NVec4) : Fin 4 → ℕ
  | ⟨0, _⟩ => a.1
  | ⟨1, _⟩ => a.2.1
  | ⟨2, _⟩ => a.2.2.1
  | ⟨3, _⟩ => a.2.2.2

private def toE4 (a : IVec4) : E4 :=
  WithLp.toLp 2 (fun i : Fin 4 => (ivAt a i : ℝ))

private def vertE4 (p : IVec4) (d : ℕ) : E4 :=
  WithLp.toLp 2 (fun i : Fin 4 => (ivAt p i : ℝ) / (d : ℝ))

private def shiftedE4 (M : NVec4) : E4 :=
  WithLp.toLp 2 (fun i : Fin 4 => (((nvAt M i : ℤ) - (S_OFF : ℤ)) : ℝ) / (S_SCALE : ℝ))

private lemma inner_toE4 (a : IVec4) (x : E4) :
    ⟪toE4 a, x⟫_ℝ = (a.1 : ℝ) * x 0 + (a.2.1 : ℝ) * x 1 +
      (a.2.2.1 : ℝ) * x 2 + (a.2.2.2 : ℝ) * x 3 := by
  simp [toE4, PiLp.inner_apply, Fin.sum_univ_four, ivAt, mul_comm]

private lemma inner_toE4_vertE4 (a p : IVec4) (d : ℕ) (hd : 0 < d) :
    ⟪toE4 a, vertE4 p d⟫_ℝ = ((dotIV a p : ℤ) : ℝ) / (d : ℝ) := by
  rw [inner_toE4]
  simp only [vertE4, dotIV, ivAt, Int.cast_add, Int.cast_mul]
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  field_simp [hd0]

private lemma norm_toE4_sq (a : IVec4) :
    ‖toE4 a‖ ^ 2 = ((dotIV a a : ℤ) : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [toE4, Fin.sum_univ_four, ivAt, dotIV, Int.cast_add, Int.cast_mul]
  ring

private lemma ball0_tangent_valid (n : IVec4) (b : ℤ)
    (hb : 0 ≤ b) (hsq : (627 : ℤ) ^ 2 * dotIV n n ≤ (1000 : ℤ) ^ 2 * b ^ 2)
    {y : E4} (hy : ‖y‖ ≤ R0) :
    ⟪toE4 n, y⟫_ℝ ≤ (b : ℝ) := by
  have h1 : ⟪toE4 n, y⟫_ℝ ≤ ‖toE4 n‖ * R0 := by
    calc ⟪toE4 n, y⟫_ℝ ≤ ‖toE4 n‖ * ‖y‖ := real_inner_le_norm _ _
      _ ≤ ‖toE4 n‖ * R0 := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
  have h2 : (‖toE4 n‖ * R0) ^ 2 ≤ (b : ℝ) ^ 2 := by
    rw [mul_pow, norm_toE4_sq]
    have hsqR : (627 : ℝ) ^ 2 * ((dotIV n n : ℤ) : ℝ) ≤ (1000 : ℝ) ^ 2 * (b : ℝ) ^ 2 := by
      exact_mod_cast hsq
    dsimp [R0]
    nlinarith
  have hbR : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hnn : 0 ≤ ‖toE4 n‖ * R0 := mul_nonneg (norm_nonneg _) (by norm_num [R0])
  nlinarith

private lemma ballA_tangent_valid (n : IVec4) (b : ℤ)
    (hrhs : 0 ≤ 1000 * b - 627 * n.2.2.2)
    (hsq : (1000 : ℤ) ^ 2 * dotIV n n ≤ (1000 * b - 627 * n.2.2.2) ^ 2)
    {y : E4} (hy : ‖y - aStd‖ ≤ 1) :
    ⟪toE4 n, y⟫_ℝ ≤ (b : ℝ) := by
  have ha : ⟪toE4 n, aStd⟫_ℝ = (n.2.2.2 : ℝ) * R0 := by
    rw [inner_toE4]
    simp [aStd]
  have h1 : ⟪toE4 n, y - aStd⟫_ℝ ≤ ‖toE4 n‖ := by
    calc ⟪toE4 n, y - aStd⟫_ℝ ≤ ‖toE4 n‖ * ‖y - aStd‖ := real_inner_le_norm _ _
      _ ≤ ‖toE4 n‖ * 1 := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
      _ = ‖toE4 n‖ := mul_one _
  have h2 : ‖toE4 n‖ ≤ (b : ℝ) - (n.2.2.2 : ℝ) * R0 := by
    have hrhsR : 0 ≤ (1000 : ℝ) * (b : ℝ) - 627 * (n.2.2.2 : ℝ) := by exact_mod_cast hrhs
    have hsqR : (1000 : ℝ) ^ 2 * ((dotIV n n : ℤ) : ℝ) ≤
        ((1000 : ℝ) * (b : ℝ) - 627 * (n.2.2.2 : ℝ)) ^ 2 := by exact_mod_cast hsq
    have hnorm2 := norm_toE4_sq n
    dsimp [R0]
    nlinarith [norm_nonneg (toE4 n)]
  have hsub : ⟪toE4 n, y - aStd⟫_ℝ = ⟪toE4 n, y⟫_ℝ - ⟪toE4 n, aStd⟫_ℝ := inner_sub_right _ _ _
  linarith

private def natDiff (a b : ℕ) : ℕ :=
  if b ≤ a then a - b else b - a

private lemma natDiff_cast (a b : ℕ) :
    ((natDiff a b : ℕ) : ℝ) = |(a : ℝ) - (b : ℝ)| := by
  unfold natDiff
  split_ifs with h
  · rw [Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))]
  · have hlt : a ≤ b := le_of_not_ge h
    rw [Nat.cast_sub hlt, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hlt))]

private def distSqN (a b : NVec4) : ℕ :=
  let d0 := natDiff a.1 b.1 + 1
  let d1 := natDiff a.2.1 b.2.1 + 1
  let d2 := natDiff a.2.2.1 b.2.2.1 + 1
  let d3 := natDiff a.2.2.2 b.2.2.2 + 1
  d0 * d0 + d1 * d1 + d2 * d2 + d3 * d3

private lemma distSqN_eq_sum (a b : NVec4) :
    distSqN a b = ∑ i : Fin 4, (natDiff (nvAt a i) (nvAt b i) + 1) ^ 2 := by
  simp [distSqN, Fin.sum_univ_four, nvAt, pow_two]

private lemma norm_sub_ctr_le_of_bracket {p : IVec4} {M ctr : NVec4} {d rad : ℕ}
    (hd : 0 < d)
    (hM : ∀ i : Fin 4,
      (d : ℤ) * ((nvAt M i : ℤ) - S_OFF) ≤ (S_SCALE : ℤ) * ivAt p i ∧
      (S_SCALE : ℤ) * ivAt p i < (d : ℤ) * ((nvAt M i : ℤ) - S_OFF + 1))
    (hrad : distSqN M ctr ≤ rad * rad) :
    ‖vertE4 p d - shiftedE4 ctr‖ ≤ (rad : ℝ) / (S_SCALE : ℝ) := by
  have hS : (0 : ℝ) < S_SCALE := by norm_num [S_SCALE]
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hcoord (i : Fin 4) :
      |(S_SCALE : ℝ) * ((ivAt p i : ℝ) / d -
        (((nvAt ctr i : ℤ) - (S_OFF : ℤ)) : ℝ) / S_SCALE)| ≤
        ((natDiff (nvAt M i) (nvAt ctr i) + 1 : ℕ) : ℝ) := by
    have h1a : ((nvAt M i : ℤ) - (S_OFF : ℤ) : ℝ) ≤ (S_SCALE : ℝ) * (ivAt p i : ℝ) / d := by
      rw [le_div_iff₀ hd']
      have := (hM i).1
      exact_mod_cast (show ((nvAt M i : ℤ) - S_OFF) * d ≤ S_SCALE * ivAt p i by linarith)
    have h1b : (S_SCALE : ℝ) * (ivAt p i : ℝ) / d < ((nvAt M i : ℤ) - (S_OFF : ℤ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hd']
      have := (hM i).2
      exact_mod_cast (show (S_SCALE : ℤ) * ivAt p i < ((nvAt M i : ℤ) - S_OFF + 1) * d by linarith)
    have hsub : (S_SCALE : ℝ) * ((ivAt p i : ℝ) / d -
        (((nvAt ctr i : ℤ) - (S_OFF : ℤ)) : ℝ) / S_SCALE) =
        (S_SCALE : ℝ) * (ivAt p i : ℝ) / d - (((nvAt ctr i : ℤ) - (S_OFF : ℤ)) : ℝ) := by
      field_simp [hS.ne', hd'.ne']
    rw [hsub]
    push_cast at h1a h1b ⊢
    rw [natDiff_cast, abs_le]
    have hl := neg_abs_le ((nvAt M i : ℝ) - (nvAt ctr i : ℝ))
    have hu := le_abs_self ((nvAt M i : ℝ) - (nvAt ctr i : ℝ))
    constructor <;> linarith
  have hsq : ((S_SCALE : ℝ) * ‖vertE4 p d - shiftedE4 ctr‖) ^ 2 ≤ (rad : ℝ) ^ 2 := by
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    have hle : ∑ i : Fin 4, (S_SCALE : ℝ) ^ 2 * (vertE4 p d i - shiftedE4 ctr i) ^ 2 ≤
        ∑ i : Fin 4, ((natDiff (nvAt M i) (nvAt ctr i) + 1 : ℕ) : ℝ) ^ 2 := by
      apply Finset.sum_le_sum; intro i _
      have hi : (S_SCALE : ℝ) ^ 2 * (vertE4 p d i - shiftedE4 ctr i) ^ 2 =
          ((S_SCALE : ℝ) * ((ivAt p i : ℝ) / d -
            (((nvAt ctr i : ℤ) - (S_OFF : ℤ)) : ℝ) / S_SCALE)) ^ 2 := by
        simp [vertE4, shiftedE4]; ring
      rw [hi, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2
    have hle2 : ∑ i : Fin 4, ((natDiff (nvAt M i) (nvAt ctr i) + 1 : ℕ) : ℝ) ^ 2 ≤ (rad : ℝ) ^ 2 := by
      rw [distSqN_eq_sum] at hrad
      have : ∑ i : Fin 4, (natDiff (nvAt M i) (nvAt ctr i) + 1) ^ 2 ≤ rad ^ 2 := by
        simpa [pow_two] using hrad
      exact_mod_cast this
    exact hle.trans hle2
  rw [le_div_iff₀ hS, mul_comm]
  nlinarith [norm_nonneg (vertE4 p d - shiftedE4 ctr), Nat.cast_nonneg (α := ℝ) rad]

private lemma norm_sub_lt_one_of_bracket {p q : IVec4} {M₁ M₂ : NVec4} {d₁ d₂ : ℕ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hM₁ : ∀ i : Fin 4,
      (d₁ : ℤ) * ((nvAt M₁ i : ℤ) - S_OFF) ≤ (S_SCALE : ℤ) * ivAt p i ∧
      (S_SCALE : ℤ) * ivAt p i < (d₁ : ℤ) * ((nvAt M₁ i : ℤ) - S_OFF + 1))
    (hM₂ : ∀ i : Fin 4,
      (d₂ : ℤ) * ((nvAt M₂ i : ℤ) - S_OFF) ≤ (S_SCALE : ℤ) * ivAt q i ∧
      (S_SCALE : ℤ) * ivAt q i < (d₂ : ℤ) * ((nvAt M₂ i : ℤ) - S_OFF + 1))
    (hpair : distSqN M₁ M₂ < S_SCALE * S_SCALE) :
    ‖vertE4 p d₁ - vertE4 q d₂‖ < 1 := by
  have hS : (0 : ℝ) < S_SCALE := by norm_num [S_SCALE]
  have hd₁' : (0 : ℝ) < d₁ := Nat.cast_pos.mpr hd₁
  have hd₂' : (0 : ℝ) < d₂ := Nat.cast_pos.mpr hd₂
  have hcoord (i : Fin 4) :
      |(S_SCALE : ℝ) * ((ivAt p i : ℝ) / d₁ - (ivAt q i : ℝ) / d₂)| ≤
        ((natDiff (nvAt M₁ i) (nvAt M₂ i) + 1 : ℕ) : ℝ) := by
    have h1a : ((nvAt M₁ i : ℤ) - (S_OFF : ℤ) : ℝ) ≤ (S_SCALE : ℝ) * (ivAt p i : ℝ) / d₁ := by
      rw [le_div_iff₀ hd₁']
      have := (hM₁ i).1
      exact_mod_cast (show ((nvAt M₁ i : ℤ) - S_OFF) * d₁ ≤ S_SCALE * ivAt p i by linarith)
    have h1b : (S_SCALE : ℝ) * (ivAt p i : ℝ) / d₁ < ((nvAt M₁ i : ℤ) - (S_OFF : ℤ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hd₁']
      have := (hM₁ i).2
      exact_mod_cast (show (S_SCALE : ℤ) * ivAt p i < ((nvAt M₁ i : ℤ) - S_OFF + 1) * d₁ by linarith)
    have h2a : ((nvAt M₂ i : ℤ) - (S_OFF : ℤ) : ℝ) ≤ (S_SCALE : ℝ) * (ivAt q i : ℝ) / d₂ := by
      rw [le_div_iff₀ hd₂']
      have := (hM₂ i).1
      exact_mod_cast (show ((nvAt M₂ i : ℤ) - S_OFF) * d₂ ≤ S_SCALE * ivAt q i by linarith)
    have h2b : (S_SCALE : ℝ) * (ivAt q i : ℝ) / d₂ < ((nvAt M₂ i : ℤ) - (S_OFF : ℤ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hd₂']
      have := (hM₂ i).2
      exact_mod_cast (show (S_SCALE : ℤ) * ivAt q i < ((nvAt M₂ i : ℤ) - S_OFF + 1) * d₂ by linarith)
    have hsub : (S_SCALE : ℝ) * ((ivAt p i : ℝ) / d₁ - (ivAt q i : ℝ) / d₂) =
        (S_SCALE : ℝ) * (ivAt p i : ℝ) / d₁ - (S_SCALE : ℝ) * (ivAt q i : ℝ) / d₂ := by ring
    rw [hsub]
    push_cast at h1a h1b h2a h2b ⊢
    rw [natDiff_cast, abs_le]
    have hl := neg_abs_le ((nvAt M₁ i : ℝ) - (nvAt M₂ i : ℝ))
    have hu := le_abs_self ((nvAt M₁ i : ℝ) - (nvAt M₂ i : ℝ))
    constructor <;> linarith
  have hsq : ((S_SCALE : ℝ) * ‖vertE4 p d₁ - vertE4 q d₂‖) ^ 2 < (S_SCALE : ℝ) ^ 2 := by
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    have hle : ∑ i : Fin 4, (S_SCALE : ℝ) ^ 2 * (vertE4 p d₁ i - vertE4 q d₂ i) ^ 2 ≤
        ∑ i : Fin 4, ((natDiff (nvAt M₁ i) (nvAt M₂ i) + 1 : ℕ) : ℝ) ^ 2 := by
      apply Finset.sum_le_sum; intro i _
      have hi : (S_SCALE : ℝ) ^ 2 * (vertE4 p d₁ i - vertE4 q d₂ i) ^ 2 =
          ((S_SCALE : ℝ) * ((ivAt p i : ℝ) / d₁ - (ivAt q i : ℝ) / d₂)) ^ 2 := by
        simp [vertE4]; ring
      rw [hi, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2
    have hlt : ∑ i : Fin 4, ((natDiff (nvAt M₁ i) (nvAt M₂ i) + 1 : ℕ) : ℝ) ^ 2 < (S_SCALE : ℝ) ^ 2 := by
      rw [distSqN_eq_sum] at hpair
      have : ∑ i : Fin 4, (natDiff (nvAt M₁ i) (nvAt M₂ i) + 1) ^ 2 < S_SCALE ^ 2 := by
        simpa [pow_two] using hpair
      exact_mod_cast this
    exact hle.trans_lt hlt
  have hmul_lt : (S_SCALE : ℝ) * ‖vertE4 p d₁ - vertE4 q d₂‖ < (S_SCALE : ℝ) := by
    nlinarith [mul_nonneg hS.le (norm_nonneg (vertE4 p d₁ - vertE4 q d₂))]
  exact lt_of_mul_lt_mul_left (by simpa [mul_one] using hmul_lt) hS.le

private theorem polar_polytope_subset_convexHull {m N : ℕ} (hN : 0 < N)
    (A : Fin m → E4) (b : Fin m → ℝ)
    (v : Fin N → E4)
    (act : Fin N → Fin 4 → Fin m)
    (nbr : Fin N → Fin 4 → Fin N)
    (hv_act : ∀ k r, ⟪A (act k r), v k⟫_ℝ = b (act k r))
    (hnbr_eq : ∀ k s r, r ≠ s → ⟪A (act k r), v (nbr k s)⟫_ℝ = b (act k r))
    (hnbr_lt : ∀ k s, ⟪A (act k s), v (nbr k s)⟫_ℝ < b (act k s))
    {x₀ : E4} (hx₀ : ∀ i : Fin m, ⟪A i, x₀⟫_ℝ ≤ b i) :
    x₀ ∈ convexHull ℝ (Set.range v) := by
  by_contra hout
  have hcomp : IsCompact (convexHull ℝ (Set.range v)) :=
    (Set.finite_range v).isCompact_convexHull (𝕜 := ℝ)
  obtain ⟨f, α, hα_lt, hα_sep⟩ :=
    geometric_hahn_banach_point_closed (convex_convexHull ℝ (Set.range v)) hcomp.isClosed hout
  let c : E4 := -((InnerProductSpace.toDual ℝ E4).symm f)
  have hc_lt : ∀ k : Fin N, ⟪c, v k⟫_ℝ < ⟪c, x₀⟫_ℝ := by
    intro k
    have h1 : α < f (v k) := hα_sep (v k) (subset_convexHull ℝ _ ⟨k, rfl⟩)
    have h2 : f x₀ < α := hα_lt
    have hf1 : ⟪c, v k⟫_ℝ = -f (v k) := by simp [c, inner_neg_left]
    have hf2 : ⟪c, x₀⟫_ℝ = -f x₀ := by simp [c, inner_neg_left]
    linarith
  have hneN : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  obtain ⟨k, _, hk_max⟩ := Finset.exists_max_image Finset.univ (fun j : Fin N => ⟪c, v j⟫_ℝ) hneN
  let a (r : Fin 4) : E4 := A (act k r)
  let w (s : Fin 4) : E4 := v (nbr k s)
  let t (s : Fin 4) : ℝ := b (act k s) - ⟪a s, w s⟫_ℝ
  have ht_pos (s : Fin 4) : 0 < t s := sub_pos.mpr (hnbr_lt k s)
  have hadiff (r s : Fin 4) : ⟪a r, v k - w s⟫_ℝ = if r = s then t s else 0 := by
    rw [inner_sub_right, hv_act k r]
    split_ifs with hrs
    · subst hrs; rfl
    · rw [hnbr_eq k s r hrs, sub_self]
  let lam (s : Fin 4) : ℝ := ⟪c, v k - w s⟫_ℝ / t s
  have hlam_nonneg (s : Fin 4) : 0 ≤ lam s := by
    apply div_nonneg _ (ht_pos s).le
    rw [inner_sub_right, sub_nonneg]
    exact hk_max (nbr k s) (Finset.mem_univ _)
  have hli : LinearIndependent ℝ (fun s : Fin 4 => v k - w s) := by
    rw [Fintype.linearIndependent_iff]
    intro μ hμ s
    have h0 := congrArg (fun z => ⟪a s, z⟫_ℝ) hμ
    simp only [inner_sum, inner_smul_right, inner_zero_right, hadiff, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at h0
    exact (mul_eq_zero.mp h0).resolve_right (ht_pos s).ne'
  let bas := basisOfLinearIndependentOfCardEqFinrank hli (by simp [E4])
  have hbas_apply (s : Fin 4) : bas s = v k - w s := by
    simp [bas]
  let u : E4 := c - ∑ r : Fin 4, lam r • a r
  have hu_orth (s : Fin 4) : ⟪u, bas s⟫_ℝ = 0 := by
    rw [hbas_apply]
    dsimp only [u]
    rw [inner_sub_left, sum_inner]
    have hsum : ∑ r : Fin 4, ⟪lam r • a r, v k - w s⟫_ℝ = ⟪c, v k - w s⟫_ℝ := by
      simp only [inner_smul_left, conj_trivial, hadiff, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      exact div_mul_cancel₀ _ (ht_pos s).ne'
    linarith
  have hu_zero : u = 0 := by
    have hself : ⟪u, u⟫_ℝ = 0 := by
      have hrepr : ⟪u, u⟫_ℝ = ⟪u, ∑ s : Fin 4, (bas.repr u s) • bas s⟫_ℝ := by
        rw [bas.sum_repr u]
      rw [hrepr, inner_sum]
      exact Finset.sum_eq_zero fun s _ => by rw [inner_smul_right, hu_orth s, mul_zero]
    exact inner_self_eq_zero.mp hself
  have hc_eq : c = ∑ r : Fin 4, lam r • a r := sub_eq_zero.mp hu_zero
  have hle : ⟪c, x₀⟫_ℝ ≤ ⟪c, v k⟫_ℝ := by
    rw [hc_eq, sum_inner, sum_inner]
    apply Finset.sum_le_sum
    intro r _
    simp only [inner_smul_left, conj_trivial]
    rw [hv_act k r]
    exact mul_le_mul_of_nonneg_left (hx₀ (act k r)) (hlam_nonneg r)
  linarith [hc_lt k]

private theorem norm_sub_lt_one_of_convexHull {N : ℕ} (v : Fin N → E4)
    (hpairs : ∀ k l : Fin N, ‖v k - v l‖ < 1)
    {x y : E4} (hx : x ∈ convexHull ℝ (Set.range v)) (hy : y ∈ convexHull ℝ (Set.range v)) :
    ‖x - y‖ < 1 := by
  have hfin : convexHull ℝ (Set.range v) =
      convexHull ℝ ((Finset.univ.image v : Finset E4) : Set E4) := by
    congr 1; ext z; simp
  rw [hfin, Finset.convexHull_eq] at hx hy
  obtain ⟨α, hα0, hα1, hx_eq⟩ := hx
  obtain ⟨β, hβ0, hβ1, hy_eq⟩ := hy
  set S : Finset E4 := Finset.univ.image v
  have hsum1 : ∑ p ∈ S, ∑ q ∈ S, (α p * β q) • p = ∑ p ∈ S, α p • p := by
    apply Finset.sum_congr rfl; intro p _
    rw [← Finset.sum_smul, ← Finset.mul_sum, hβ1, mul_one]
  have hsum2 : ∑ p ∈ S, ∑ q ∈ S, (α p * β q) • q = ∑ q ∈ S, β q • q := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro q _
    rw [← Finset.sum_smul, ← Finset.sum_mul, hα1, one_mul]
  have hxy : x - y = ∑ p ∈ S, ∑ q ∈ S, (α p * β q) • (p - q) := by
    rw [← hx_eq, ← hy_eq]
    simp only [Finset.centerMass, hα1, hβ1, inv_one, one_smul, id_eq, smul_sub,
      Finset.sum_sub_distrib, hsum1, hsum2]
  have hlt_pq : ∀ p ∈ S, ∀ q ∈ S, ‖p - q‖ < 1 := by
    intro p hp q hq
    rcases Finset.mem_image.mp hp with ⟨k, _, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨l, _, rfl⟩
    exact hpairs k l
  have hsum_one : ∑ p ∈ S, ∑ q ∈ S, α p * β q = 1 := by
    simp only [← Finset.mul_sum, hβ1, mul_one, hα1]
  have hne_pair : ∃ p ∈ S, ∃ q ∈ S, 0 < α p * β q := by
    by_contra h
    push Not at h
    have hz : ∑ p ∈ S, ∑ q ∈ S, α p * β q ≤ 0 :=
      Finset.sum_nonpos fun p hp => Finset.sum_nonpos fun q hq => h p hp q hq
    linarith
  obtain ⟨p₀, hp₀, q₀, hq₀, hpos₀⟩ := hne_pair
  calc ‖x - y‖ = ‖∑ p ∈ S, ∑ q ∈ S, (α p * β q) • (p - q)‖ := by rw [hxy]
    _ ≤ ∑ p ∈ S, ‖∑ q ∈ S, (α p * β q) • (p - q)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ S, ∑ q ∈ S, ‖(α p * β q) • (p - q)‖ :=
        Finset.sum_le_sum fun p _ => norm_sum_le _ _
    _ = ∑ p ∈ S, ∑ q ∈ S, (α p * β q) * ‖p - q‖ := by
        apply Finset.sum_congr rfl; intro p hp
        apply Finset.sum_congr rfl; intro q hq
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hα0 p hp) (hβ0 q hq))]
    _ < ∑ p ∈ S, ∑ q ∈ S, α p * β q := by
        apply Finset.sum_lt_sum
        · intro p hp
          apply Finset.sum_le_sum; intro q hq
          have hle := (hlt_pq p hp q hq).le
          nlinarith [mul_nonneg (hα0 p hp) (hβ0 q hq)]
        · refine ⟨p₀, hp₀, ?_⟩
          apply Finset.sum_lt_sum
          · intro q hq
            have hle := (hlt_pq p₀ hp₀ q hq).le
            nlinarith [mul_nonneg (hα0 p₀ hp₀) (hβ0 q hq)]
          · refine ⟨q₀, hq₀, ?_⟩
            nlinarith [hlt_pq p₀ hp₀ q₀ hq₀]
    _ = 1 := hsum_one

/- Part 3: Fast balanced binary tree and computable integer certificate verifier -/

private inductive BTree (α : Type) where
  | leaf (a : α)
  | node (l r : BTree α)

private def BTree.get {α : Type} : BTree α → ℕ → α
  | .leaf a, _ => a
  | .node l r, n => if n % 2 == 0 then l.get (n / 2) else r.get (n / 2)

private def splitEO {α : Type} : List α → List α × List α
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: rest =>
    let p := splitEO rest
    (a :: p.1, b :: p.2)

private lemma splitEO_len_le {α : Type} : ∀ l : List α,
    (splitEO l).1.length ≤ l.length ∧ (splitEO l).2.length ≤ l.length
  | [] => ⟨le_rfl, le_rfl⟩
  | [_] => ⟨le_rfl, Nat.zero_le _⟩
  | _ :: _ :: rest => by
    have ih := splitEO_len_le rest
    simp only [splitEO, List.length_cons]
    omega

private lemma splitEO_getElem_even {α : Type} : ∀ (l : List α) (k : ℕ) (hk : 2 * k < l.length),
    ∃ hk1 : k < (splitEO l).1.length, (splitEO l).1[k]'hk1 = l[2 * k]'hk
  | [], k, hk => by simp at hk
  | [a], k, hk => by
    have hk0 : k = 0 := by simp at hk; omega
    subst hk0
    exact ⟨by simp [splitEO], rfl⟩
  | a :: b :: rest, 0, hk => ⟨by simp [splitEO], rfl⟩
  | a :: b :: rest, k + 1, hk => by
    have hk' : 2 * k < rest.length := by simp at hk; omega
    obtain ⟨hk1, heq⟩ := splitEO_getElem_even rest k hk'
    refine ⟨by simp only [splitEO, List.length_cons]; omega, ?_⟩
    simpa [splitEO, Nat.mul_add] using heq

private lemma splitEO_getElem_odd {α : Type} : ∀ (l : List α) (k : ℕ) (hk : 2 * k + 1 < l.length),
    ∃ hk2 : k < (splitEO l).2.length, (splitEO l).2[k]'hk2 = l[2 * k + 1]'hk
  | [], k, hk => by simp at hk
  | [_], k, hk => by simp at hk
  | a :: b :: rest, 0, hk => ⟨by simp [splitEO], rfl⟩
  | a :: b :: rest, k + 1, hk => by
    have hk' : 2 * k + 1 < rest.length := by simp at hk; omega
    obtain ⟨hk2, heq⟩ := splitEO_getElem_odd rest k hk'
    refine ⟨by simp only [splitEO, List.length_cons]; omega, ?_⟩
    simpa [splitEO, Nat.mul_add] using heq

private lemma splitEO_len_pow {α : Type} : ∀ (l : List α) (m : ℕ),
    l.length ≤ 2 * m → (splitEO l).1.length ≤ m ∧ (splitEO l).2.length ≤ m
  | [], _, _ => ⟨Nat.zero_le _, Nat.zero_le _⟩
  | [_], m, hm => by simp [splitEO] at hm ⊢; omega
  | _ :: _ :: rest, m, hm => by
    cases m with
    | zero => simp at hm
    | succ m' =>
      have ih := splitEO_len_pow rest m' (by simp at hm; omega)
      simp only [splitEO, List.length_cons]
      omega

private def BTree.ofListAux {α : Type} (d : α) : ℕ → List α → BTree α
  | 0, l => .leaf (l.headD d)
  | _ + 1, [] => .leaf d
  | _ + 1, [a] => .leaf a
  | fuel + 1, l =>
    let p := splitEO l
    .node (ofListAux d fuel p.1) (ofListAux d fuel p.2)

private lemma BTree.get_ofListAux {α : Type} (d : α) :
    ∀ (fuel : ℕ) (l : List α), l.length ≤ 2 ^ fuel → ∀ (i : ℕ) (hi : i < l.length),
      (BTree.ofListAux d fuel l).get i = l[i]'hi
  | 0, [], _, _, hi => by simp at hi
  | 0, [a], _, i, hi => by
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0; rfl
  | 0, _ :: _ :: _, hlen, _, _ => by simp at hlen
  | _ + 1, [], _, _, hi => by simp at hi
  | _ + 1, [a], _, i, hi => by
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0; rfl
  | fuel + 1, a :: b :: rest, hlen, i, hi => by
    have hpow : (a :: b :: rest).length ≤ 2 * 2 ^ fuel := by
      simpa [Nat.pow_succ, Nat.mul_comm] using hlen
    have ⟨h1, h2⟩ := splitEO_len_pow (a :: b :: rest) (2 ^ fuel) hpow
    change (BTree.node (ofListAux d fuel (splitEO (a :: b :: rest)).1)
      (ofListAux d fuel (splitEO (a :: b :: rest)).2)).get i = (a :: b :: rest)[i]'hi
    simp only [BTree.get]
    by_cases hev : i % 2 = 0
    · simp only [hev, beq_self_eq_true, ↓reduceIte]
      have hi_eq : 2 * (i / 2) = i := by omega
      have hk : 2 * (i / 2) < (a :: b :: rest).length := by omega
      obtain ⟨hk1, heq⟩ := splitEO_getElem_even (a :: b :: rest) (i / 2) hk
      rw [BTree.get_ofListAux d fuel _ h1 (i / 2) hk1, heq]
      congr 1
    · simp only [beq_iff_eq, hev, ↓reduceIte]
      have hi_eq : 2 * (i / 2) + 1 = i := by omega
      have hk : 2 * (i / 2) + 1 < (a :: b :: rest).length := by omega
      obtain ⟨hk2, heq⟩ := splitEO_getElem_odd (a :: b :: rest) (i / 2) hk
      rw [BTree.get_ofListAux d fuel _ h2 (i / 2) hk2, heq]
      congr 1

private inductive HSTag where
  | base (idx : ℕ)
  | ball0
  | ballA
  | aff (other : ℕ)
  deriving DecidableEq

private structure HSData where
  tag : HSTag
  n : IVec4
  b : ℤ

private structure VertData where
  p : IVec4
  d : ℕ
  M : NVec4
  rad : ℕ
  act : ℕ × ℕ × ℕ × ℕ
  nbr : ℕ × ℕ × ℕ × ℕ

private def dummyHS : HSData := ⟨.ball0, (0, 0, 0, 0), 0⟩
private def dummyVert : VertData := ⟨(0, 0, 0, 0), 1, (0, 0, 0, 0), 0, (0, 0, 0, 0), (0, 0, 0, 0)⟩

private def affC : Fin 8 → IVec4
  | ⟨0, _⟩ => (243, 488, 184, 1673)
  | ⟨1, _⟩ => (-652, -1118, 1218, -400)
  | ⟨2, _⟩ => (487, 799, -1460, -618)
  | ⟨3, _⟩ => (-1102, -953, -1368, -529)
  | ⟨4, _⟩ => (1277, -1453, -607, -364)
  | ⟨5, _⟩ => (1966, -208, 864, -629)
  | ⟨6, _⟩ => (-345, 1589, 1398, -888)
  | ⟨7, _⟩ => (-1875, 847, -237, -443)

private def affB : Fin 8 → ℤ
  | ⟨0, _⟩ => -147
  | ⟨1, _⟩ => 131
  | ⟨2, _⟩ => 173
  | ⟨3, _⟩ => 60
  | ⟨4, _⟩ => 37
  | ⟨5, _⟩ => 21
  | ⟨6, _⟩ => 16
  | ⟨7, _⟩ => 18

private def cellSet (j : Fin 8) : Set E4 :=
  {y : E4 | ∀ k : Fin 8, ⟪toE4 (affC k), y⟫_ℝ + (affB k : ℝ) ≤
    ⟪toE4 (affC j), y⟫_ℝ + (affB j : ℝ)}

private lemma cellSet_isClosed (j : Fin 8) : IsClosed (cellSet j) := by
  have hEq : cellSet j = ⋂ k : Fin 8, {y : E4 | ⟪toE4 (affC k), y⟫_ℝ + (affB k : ℝ) ≤
      ⟪toE4 (affC j), y⟫_ℝ + (affB j : ℝ)} := by
    ext y; simp [cellSet]
  rw [hEq]
  refine isClosed_iInter fun k => isClosed_le ?_ ?_ <;> fun_prop

private lemma cellSet_cover (y : E4) : ∃ j : Fin 8, y ∈ cellSet j := by
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
    (fun k : Fin 8 => ⟪toE4 (affC k), y⟫_ℝ + (affB k : ℝ)) Finset.univ_nonempty
  exact ⟨j, fun k => hj k (Finset.mem_univ k)⟩

private def checkHS (j : Fin 8) (h : HSData) : Bool :=
  match h.tag with
  | .base 0 => h.n == (2, 0, 0, 0) && h.b == 1
  | .base 1 => h.n == (-2, 0, 0, 0) && h.b == 1
  | .base 2 => h.n == (0, 2, 0, 0) && h.b == 1
  | .base 3 => h.n == (0, -2, 0, 0) && h.b == 1
  | .base 4 => h.n == (0, 0, 2, 0) && h.b == 1
  | .base 5 => h.n == (140, 140, 0, 0) && h.b == 99
  | .base 6 => h.n == (140, -140, 0, 0) && h.b == 99
  | .base _ => false
  | .ball0 => decide (0 ≤ h.b) && decide ((627 : ℤ) ^ 2 * dotIV h.n h.n ≤ (1000 : ℤ) ^ 2 * h.b ^ 2)
  | .ballA =>
    let rhs := 1000 * h.b - 627 * h.n.2.2.2
    decide (0 ≤ rhs) && decide ((1000 : ℤ) ^ 2 * dotIV h.n h.n ≤ rhs ^ 2)
  | .aff k =>
    if hk : k < 8 then
      let ck := affC ⟨k, hk⟩
      let cj := affC j
      let dc : IVec4 := (ck.1 - cj.1, ck.2.1 - cj.2.1, ck.2.2.1 - cj.2.2.1, ck.2.2.2 - cj.2.2.2)
      h.n == dc && h.b == affB j - affB ⟨k, hk⟩
    else false

private lemma checkHS_sound (j : Fin 8) (h : HSData) (hok : checkHS j h = true)
    {y : E4} (hL : InLStar2 y) (hC : y ∈ cellSet j) :
    ⟪toE4 h.n, y⟫_ℝ ≤ (h.b : ℝ) := by
  rcases h with ⟨tag, n, b⟩
  cases tag with
  | base idx =>
    rcases hL with ⟨_, _, hx0l, hx0u, hx1l, hx1u, hx2u, hdp, hdm⟩
    match idx with
    | 0 =>
      simp only [checkHS, Bool.and_eq_true, beq_iff_eq] at hok
      rw [hok.1, hok.2, inner_toE4]; norm_num; linarith
    | 1 =>
      simp only [checkHS, Bool.and_eq_true, beq_iff_eq] at hok
      rw [hok.1, hok.2, inner_toE4]; norm_num; linarith
    | 2 =>
      simp only [checkHS, Bool.and_eq_true, beq_iff_eq] at hok
      rw [hok.1, hok.2, inner_toE4]; norm_num; linarith
    | 3 =>
      simp only [checkHS, Bool.and_eq_true, beq_iff_eq] at hok
      rw [hok.1, hok.2, inner_toE4]; norm_num; linarith
    | 4 =>
      simp only [checkHS, Bool.and_eq_true, beq_iff_eq] at hok
      rw [hok.1, hok.2, inner_toE4]; norm_num; linarith
    | 5 =>
      simp only [checkHS, Bool.and_eq_true, beq_iff_eq] at hok
      rw [hok.1, hok.2, inner_toE4]; norm_num; linarith
    | 6 =>
      simp only [checkHS, Bool.and_eq_true, beq_iff_eq] at hok
      rw [hok.1, hok.2, inner_toE4]; norm_num; linarith
    | _ + 7 => simp [checkHS] at hok
  | ball0 =>
    simp only [checkHS, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact ball0_tangent_valid n b hok.1 hok.2 hL.1
  | ballA =>
    simp only [checkHS, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact ballA_tangent_valid n b hok.1 hok.2 hL.2.1
  | aff k =>
    simp only [checkHS] at hok
    split_ifs at hok with hk
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    rw [hok.1, hok.2]
    have hcell := hC ⟨k, hk⟩
    simp only [inner_toE4, Int.cast_sub] at hcell ⊢
    linarith

private def checkBracket1 (d : ℕ) (p : ℤ) (m : ℕ) : Bool :=
  let s : ℤ := (m : ℤ) - (S_OFF : ℤ)
  decide ((d : ℤ) * s ≤ (S_SCALE : ℤ) * p) &&
  decide ((S_SCALE : ℤ) * p < (d : ℤ) * (s + 1))

private lemma checkBracket1_sound {d : ℕ} {p : ℤ} {m : ℕ} (h : checkBracket1 d p m = true) :
    (d : ℤ) * ((m : ℤ) - S_OFF) ≤ (S_SCALE : ℤ) * p ∧
    (S_SCALE : ℤ) * p < (d : ℤ) * ((m : ℤ) - S_OFF + 1) := by
  simpa [checkBracket1, Bool.and_eq_true, decide_eq_true_eq] using h

private def checkVert (m N : ℕ) (hTree : BTree HSData) (vTree : BTree VertData)
    (ctr : NVec4) (v : VertData) : Bool :=
  let (a0, a1, a2, a3) := v.act
  let (n0, n1, n2, n3) := v.nbr
  let h0 := hTree.get a0; let h1 := hTree.get a1
  let h2 := hTree.get a2; let h3 := hTree.get a3
  let w0 := vTree.get n0; let w1 := vTree.get n1
  let w2 := vTree.get n2; let w3 := vTree.get n3
  decide (0 < v.d) &&
  decide (a0 < m) && decide (a1 < m) && decide (a2 < m) && decide (a3 < m) &&
  decide (n0 < N) && decide (n1 < N) && decide (n2 < N) && decide (n3 < N) &&
  checkBracket1 v.d v.p.1 v.M.1 && checkBracket1 v.d v.p.2.1 v.M.2.1 &&
  checkBracket1 v.d v.p.2.2.1 v.M.2.2.1 && checkBracket1 v.d v.p.2.2.2 v.M.2.2.2 &&
  decide (distSqN v.M ctr ≤ v.rad * v.rad) &&
  -- Active equations for v
  (dotIV h0.n v.p == (v.d : ℤ) * h0.b) &&
  (dotIV h1.n v.p == (v.d : ℤ) * h1.b) &&
  (dotIV h2.n v.p == (v.d : ℤ) * h2.b) &&
  (dotIV h3.n v.p == (v.d : ℤ) * h3.b) &&
  -- Neighbor 0: strictly inside h0, on h1, h2, h3
  decide (dotIV h0.n w0.p < (w0.d : ℤ) * h0.b) &&
  (dotIV h1.n w0.p == (w0.d : ℤ) * h1.b) &&
  (dotIV h2.n w0.p == (w0.d : ℤ) * h2.b) &&
  (dotIV h3.n w0.p == (w0.d : ℤ) * h3.b) &&
  -- Neighbor 1: strictly inside h1, on h0, h2, h3
  (dotIV h0.n w1.p == (w1.d : ℤ) * h0.b) &&
  decide (dotIV h1.n w1.p < (w1.d : ℤ) * h1.b) &&
  (dotIV h2.n w1.p == (w1.d : ℤ) * h2.b) &&
  (dotIV h3.n w1.p == (w1.d : ℤ) * h3.b) &&
  -- Neighbor 2: strictly inside h2, on h0, h1, h3
  (dotIV h0.n w2.p == (w2.d : ℤ) * h0.b) &&
  (dotIV h1.n w2.p == (w2.d : ℤ) * h1.b) &&
  decide (dotIV h2.n w2.p < (w2.d : ℤ) * h2.b) &&
  (dotIV h3.n w2.p == (w2.d : ℤ) * h3.b) &&
  -- Neighbor 3: strictly inside h3, on h0, h1, h2
  (dotIV h0.n w3.p == (w3.d : ℤ) * h0.b) &&
  (dotIV h1.n w3.p == (w3.d : ℤ) * h1.b) &&
  (dotIV h2.n w3.p == (w3.d : ℤ) * h2.b) &&
  decide (dotIV h3.n w3.p < (w3.d : ℤ) * h3.b)

private def isDescRad : List VertData → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (b.rad ≤ a.rad) && isDescRad (b :: rest)

private lemma isDescRad_le : ∀ (l : List VertData), isDescRad l = true →
    ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i ≤ j → l[j].rad ≤ l[i].rad
  | [], _, _, _, hi, _, _ => by simp at hi
  | [_], _, i, j, hi, hj, _ => by
    have : i = 0 := by simp at hi; omega
    have : j = 0 := by simp at hj; omega
    subst_vars; exact le_rfl
  | a :: b :: rest, h, i, j, hi, hj, hij => by
    simp only [isDescRad, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := isDescRad_le (b :: rest) h.2
    cases i with
    | zero =>
      cases j with
      | zero => exact le_rfl
      | succ j' =>
        have hj' : j' < (b :: rest).length := by simp only [List.length_cons] at hj ⊢; omega
        have h1 := ih 0 j' (by simp) hj' (Nat.zero_le _)
        exact h1.trans h.1
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        have hi' : i' < (b :: rest).length := by simp only [List.length_cons] at hi ⊢; omega
        have hj' : j' < (b :: rest).length := by simp only [List.length_cons] at hj ⊢; omega
        exact ih i' j' hi' hj' (Nat.succ_le_succ_iff.mp hij)

private def checkPairsOne (v : VertData) : List VertData → Bool
  | [] => true
  | w :: rest =>
    if v.rad + w.rad < S_SCALE then true
    else decide (distSqN v.M w.M < S_SCALE * S_SCALE) && checkPairsOne v rest

private lemma checkPairsOne_sound (v : VertData) :
    ∀ (l : List VertData), isDescRad l = true → checkPairsOne v l = true →
      ∀ (j : ℕ) (hj : j < l.length),
        v.rad + l[j].rad < S_SCALE ∨ distSqN v.M l[j].M < S_SCALE * S_SCALE
  | [], _, _, _, hj => by simp at hj
  | w :: rest, hdesc, hok, j, hj => by
    simp only [checkPairsOne] at hok
    split_ifs at hok with hlt
    · left
      have hle := isDescRad_le (w :: rest) hdesc 0 j (by simp) hj (Nat.zero_le _)
      exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hle v.rad) hlt
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      cases j with
      | zero => exact Or.inr hok.1
      | succ j' =>
        have hdesc' : isDescRad rest = true := by
          cases rest with
          | nil => rfl
          | cons c cs => exact (Bool.and_eq_true _ _ |>.mp hdesc).2
        exact checkPairsOne_sound v rest hdesc' hok.2 j' (by simp at hj; omega)

private def checkPairsAll : List VertData → Bool
  | [] => true
  | v :: rest => checkPairsOne v rest && checkPairsAll rest

private lemma checkPairsAll_sound :
    ∀ (l : List VertData), isDescRad l = true → checkPairsAll l = true →
      ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i < j →
        l[i].rad + l[j].rad < S_SCALE ∨ distSqN l[i].M l[j].M < S_SCALE * S_SCALE
  | [], _, _, _, _, hi, _, _ => by simp at hi
  | v :: rest, hdesc, hok, i, j, hi, hj, hij => by
    simp only [checkPairsAll, Bool.and_eq_true] at hok
    have hdesc' : isDescRad rest = true := by
      cases rest with
      | nil => rfl
      | cons c cs => exact (Bool.and_eq_true _ _ |>.mp hdesc).2
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' =>
        exact checkPairsOne_sound v rest hdesc' hok.1 j' (by simp at hj; omega)
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        exact checkPairsAll_sound rest hdesc' hok.2 i' j'
          (by simp at hi; omega) (by simp at hj; omega) (Nat.succ_lt_succ_iff.mp hij)

private def verifyCell (j : Fin 8) (hs : List HSData) (vs : List VertData) (ctr : NVec4) : Bool :=
  let m := hs.length
  let N := vs.length
  let hTree := BTree.ofListAux dummyHS 8 hs
  let vTree := BTree.ofListAux dummyVert 9 vs
  decide (0 < N) && decide (m ≤ 256) && decide (N ≤ 512) &&
  hs.all (checkHS j) &&
  isDescRad vs &&
  vs.all (checkVert m N hTree vTree ctr) &&
  checkPairsAll vs

private lemma verifyCell_sound (j : Fin 8) (hs : List HSData) (vs : List VertData) (ctr : NVec4)
    (hok : verifyCell j hs vs ctr = true)
    {x y : E4} (hxL : InLStar2 x) (hyL : InLStar2 y) (hxC : x ∈ cellSet j) (hyC : y ∈ cellSet j) :
    ‖x - y‖ < 1 := by
  unfold verifyCell at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨hNpos, hm256⟩, hN512⟩, hHS⟩, hDesc⟩, hVerts⟩, hPairs⟩ := hok
  set m := hs.length
  set N := vs.length
  set hTree := BTree.ofListAux dummyHS 8 hs
  set vTree := BTree.ofListAux dummyVert 9 vs
  have hTree_get (i : ℕ) (hi : i < m) : hTree.get i = hs[i]'hi :=
    BTree.get_ofListAux dummyHS 8 hs (by omega) i hi
  have vTree_get (k : ℕ) (hk : k < N) : vTree.get k = vs[k]'hk :=
    BTree.get_ofListAux dummyVert 9 vs (by omega) k hk
  let A (i : Fin m) : E4 := toE4 (hs[i.val]'i.isLt).n
  let b (i : Fin m) : ℝ := ((hs[i.val]'i.isLt).b : ℝ)
  let v (k : Fin N) : E4 := vertE4 (vs[k.val]'k.isLt).p (vs[k.val]'k.isLt).d
  have hv_ok (k : Fin N) : checkVert m N hTree vTree ctr (vs[k.val]'k.isLt) = true :=
    hVerts _ (List.getElem_mem k.isLt)
  -- Extract structured facts from checkVert for every vertex k
  have hv_props (k : Fin N) :
      let vk := vs[k.val]'k.isLt
      0 < vk.d ∧
      vk.act.1 < m ∧ vk.act.2.1 < m ∧ vk.act.2.2.1 < m ∧ vk.act.2.2.2 < m ∧
      vk.nbr.1 < N ∧ vk.nbr.2.1 < N ∧ vk.nbr.2.2.1 < N ∧ vk.nbr.2.2.2 < N ∧
      (∀ c : Fin 4, (vk.d : ℤ) * ((nvAt vk.M c : ℤ) - S_OFF) ≤ (S_SCALE : ℤ) * ivAt vk.p c ∧
        (S_SCALE : ℤ) * ivAt vk.p c < (vk.d : ℤ) * ((nvAt vk.M c : ℤ) - S_OFF + 1)) ∧
      distSqN vk.M ctr ≤ vk.rad * vk.rad := by
    have h := hv_ok k
    dsimp only [checkVert] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    refine ⟨h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1,
      h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
      h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
      h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
      h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
      h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
      h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
      h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
      h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, ?_,
      h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2⟩
    intro c; fin_cases c
    · exact checkBracket1_sound h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · exact checkBracket1_sound h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · exact checkBracket1_sound h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · exact checkBracket1_sound h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  let act (k : Fin N) : Fin 4 → Fin m
    | ⟨0, _⟩ => ⟨(vs[k.val]'k.isLt).act.1, (hv_props k).2.1⟩
    | ⟨1, _⟩ => ⟨(vs[k.val]'k.isLt).act.2.1, (hv_props k).2.2.1⟩
    | ⟨2, _⟩ => ⟨(vs[k.val]'k.isLt).act.2.2.1, (hv_props k).2.2.2.1⟩
    | ⟨3, _⟩ => ⟨(vs[k.val]'k.isLt).act.2.2.2, (hv_props k).2.2.2.2.1⟩
  let nbr (k : Fin N) : Fin 4 → Fin N
    | ⟨0, _⟩ => ⟨(vs[k.val]'k.isLt).nbr.1, (hv_props k).2.2.2.2.2.1⟩
    | ⟨1, _⟩ => ⟨(vs[k.val]'k.isLt).nbr.2.1, (hv_props k).2.2.2.2.2.2.1⟩
    | ⟨2, _⟩ => ⟨(vs[k.val]'k.isLt).nbr.2.2.1, (hv_props k).2.2.2.2.2.2.2.1⟩
    | ⟨3, _⟩ => ⟨(vs[k.val]'k.isLt).nbr.2.2.2, (hv_props k).2.2.2.2.2.2.2.2.1⟩
  have hinner_eq {i : Fin m} {k : Fin N}
      (heq : dotIV (hs[i.val]'i.isLt).n (vs[k.val]'k.isLt).p =
        ((vs[k.val]'k.isLt).d : ℤ) * (hs[i.val]'i.isLt).b) :
      ⟪A i, v k⟫_ℝ = b i := by
    have hd : 0 < (vs[k.val]'k.isLt).d := (hv_props k).1
    dsimp only [A, b, v]
    rw [inner_toE4_vertE4 _ _ _ hd, heq]
    have hd0 : ((vs[k.val]'k.isLt).d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    push_cast
    exact mul_div_cancel_left₀ _ hd0
  have hinner_lt {i : Fin m} {k : Fin N}
      (hlt : dotIV (hs[i.val]'i.isLt).n (vs[k.val]'k.isLt).p <
        ((vs[k.val]'k.isLt).d : ℤ) * (hs[i.val]'i.isLt).b) :
      ⟪A i, v k⟫_ℝ < b i := by
    have hd : 0 < (vs[k.val]'k.isLt).d := (hv_props k).1
    dsimp only [A, b, v]
    rw [inner_toE4_vertE4 _ _ _ hd, div_lt_iff₀ (Nat.cast_pos.mpr hd)]
    have hltR : ((dotIV (hs[i.val]'i.isLt).n (vs[k.val]'k.isLt).p : ℤ) : ℝ) <
        ((vs[k.val]'k.isLt).d : ℝ) * ((hs[i.val]'i.isLt).b : ℝ) := by exact_mod_cast hlt
    linarith
  have hv_act : ∀ k r, ⟪A (act k r), v k⟫_ℝ = b (act k r) := by
    intro k r
    have h := hv_ok k
    dsimp only [checkVert] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    fin_cases r
    · apply hinner_eq
      simpa [act, hTree_get _ (hv_props k).2.1] using h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · apply hinner_eq
      simpa [act, hTree_get _ (hv_props k).2.2.1] using h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · apply hinner_eq
      simpa [act, hTree_get _ (hv_props k).2.2.2.1] using h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · apply hinner_eq
      simpa [act, hTree_get _ (hv_props k).2.2.2.2.1] using h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  have hnbr_eq : ∀ k s r, r ≠ s → ⟪A (act k r), v (nbr k s)⟫_ℝ = b (act k r) := by
    intro k s r hrs
    have h := hv_ok k
    dsimp only [checkVert] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    have hp := hv_props k
    fin_cases s <;> fin_cases r <;> try exact (hrs rfl).elim
    · apply hinner_eq; simpa [act, nbr, hTree_get _ hp.2.2.1, vTree_get _ hp.2.2.2.2.2.1] using h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · apply hinner_eq; simpa [act, nbr, hTree_get _ hp.2.2.2.1, vTree_get _ hp.2.2.2.2.2.1] using h.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · apply hinner_eq; simpa [act, nbr, hTree_get _ hp.2.2.2.2.1, vTree_get _ hp.2.2.2.2.2.1] using h.1.1.1.1.1.1.1.1.1.1.1.1.2
    · apply hinner_eq; simpa [act, nbr, hTree_get _ hp.2.1, vTree_get _ hp.2.2.2.2.2.2.1] using h.1.1.1.1.1.1.1.1.1.1.1.2
    · apply hinner_eq; simpa [act, nbr, hTree_get _ hp.2.2.2.1, vTree_get _ hp.2.2.2.2.2.2.1] using h.1.1.1.1.1.1.1.1.1.2
    · apply hinner_eq; simpa [act, nbr, hTree_get _ hp.2.2.2.2.1, vTree_get _ hp.2.2.2.2.2.2.1] using h.1.1.1.1.1.1.1.1.2
    · apply hinner_eq; simpa [act, nbr, hTree_get _ hp.2.1, vTree_get _ hp.2.2.2.2.2.2.2.1] using h.1.1.1.1.1.1.1.2
    · apply hinner_eq; simpa [act, nbr, hTree_get _ hp.2.2.1, vTree_get _ hp.2.2.2.2.2.2.2.1] using h.1.1.1.1.1.1.2
    · apply hinner_eq; simpa [act, nbr, hTree_get _ hp.2.2.2.2.1, vTree_get _ hp.2.2.2.2.2.2.2.1] using h.1.1.1.1.2
    · apply hinner_eq; simpa [act, nbr, hTree_get _ hp.2.1, vTree_get _ hp.2.2.2.2.2.2.2.2.1] using h.1.1.1.2
    · apply hinner_eq; simpa [act, nbr, hTree_get _ hp.2.2.1, vTree_get _ hp.2.2.2.2.2.2.2.2.1] using h.1.1.2
    · apply hinner_eq; simpa [act, nbr, hTree_get _ hp.2.2.2.1, vTree_get _ hp.2.2.2.2.2.2.2.2.1] using h.1.2
  have hnbr_lt : ∀ k s, ⟪A (act k s), v (nbr k s)⟫_ℝ < b (act k s) := by
    intro k s
    have h := hv_ok k
    dsimp only [checkVert] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    have hp := hv_props k
    fin_cases s
    · apply hinner_lt; simpa [act, nbr, hTree_get _ hp.2.1, vTree_get _ hp.2.2.2.2.2.1] using h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · apply hinner_lt; simpa [act, nbr, hTree_get _ hp.2.2.1, vTree_get _ hp.2.2.2.2.2.2.1] using h.1.1.1.1.1.1.1.1.1.1.2
    · apply hinner_lt; simpa [act, nbr, hTree_get _ hp.2.2.2.1, vTree_get _ hp.2.2.2.2.2.2.2.1] using h.1.1.1.1.1.2
    · apply hinner_lt; simpa [act, nbr, hTree_get _ hp.2.2.2.2.1, vTree_get _ hp.2.2.2.2.2.2.2.2.1] using h.2
  have hxP : ∀ i : Fin m, ⟪A i, x⟫_ℝ ≤ b i := fun i =>
    checkHS_sound j (hs[i.val]'i.isLt) (hHS _ (List.getElem_mem i.isLt)) hxL hxC
  have hyP : ∀ i : Fin m, ⟪A i, y⟫_ℝ ≤ b i := fun i =>
    checkHS_sound j (hs[i.val]'i.isLt) (hHS _ (List.getElem_mem i.isLt)) hyL hyC
  have hx_hull := polar_polytope_subset_convexHull hNpos A b v act nbr hv_act hnbr_eq hnbr_lt hxP
  have hy_hull := polar_polytope_subset_convexHull hNpos A b v act nbr hv_act hnbr_eq hnbr_lt hyP
  have hpair_lt (k l : Fin N) (hkl : k.val < l.val) : ‖v k - v l‖ < 1 := by
    have hpk := hv_props k
    have hpl := hv_props l
    rcases checkPairsAll_sound vs hDesc hPairs k.val l.val k.isLt l.isLt hkl with hrad | hdist
    · have hk_c := norm_sub_ctr_le_of_bracket hpk.1 hpk.2.2.2.2.2.2.2.2.2.1 hpk.2.2.2.2.2.2.2.2.2.2
      have hl_c := norm_sub_ctr_le_of_bracket hpl.1 hpl.2.2.2.2.2.2.2.2.2.1 hpl.2.2.2.2.2.2.2.2.2.2
      have htri : ‖v k - v l‖ ≤ ‖v k - shiftedE4 ctr‖ + ‖v l - shiftedE4 ctr‖ := by
        simpa [dist_eq_norm] using dist_triangle_right (v k) (v l) (shiftedE4 ctr)
      have hS : (0 : ℝ) < S_SCALE := by norm_num [S_SCALE]
      have hradR : ((vs[k.val]'k.isLt).rad : ℝ) + ((vs[l.val]'l.isLt).rad : ℝ) < (S_SCALE : ℝ) := by
        exact_mod_cast hrad
      have hdiv : ((vs[k.val]'k.isLt).rad : ℝ) / (S_SCALE : ℝ) +
          ((vs[l.val]'l.isLt).rad : ℝ) / (S_SCALE : ℝ) < 1 := by
        rw [← add_div, div_lt_one hS]; exact hradR
      change ‖v k - shiftedE4 ctr‖ ≤ _ at hk_c
      change ‖v l - shiftedE4 ctr‖ ≤ _ at hl_c
      linarith
    · exact norm_sub_lt_one_of_bracket hpk.1 hpl.1
        hpk.2.2.2.2.2.2.2.2.2.1 hpl.2.2.2.2.2.2.2.2.2.1 hdist
  have hall_pairs (k l : Fin N) : ‖v k - v l‖ < 1 := by
    rcases lt_trichotomy k.val l.val with hlt | heq | hgt
    · exact hpair_lt k l hlt
    · have : k = l := Fin.ext heq; subst this; simp
    · rw [norm_sub_rev]; exact hpair_lt l k hgt
  exact norm_sub_lt_one_of_convexHull v hall_pairs hx_hull hy_hull

/- Part 4: Explicit exact integer certificates for all eight cells of L**(0.627) -/

private def ctr0 : NVec4 := (67612, 70172, 67560, 94002)

private def hs0 : List HSData := [
  ⟨.base 0, (2, 0, 0, 0), 1⟩,
  ⟨.base 2, (0, 2, 0, 0), 1⟩,
  ⟨.base 4, (0, 0, 2, 0), 1⟩,
  ⟨.base 5, (140, 140, 0, 0), 99⟩,
  ⟨.ball0, (0, -1414, 0, 1414), 1254⟩,
  ⟨.ball0, (1000, 1000, -1000, 1000), 1254⟩,
  ⟨.ball0, (742, 1319, -329, 1265), 1254⟩,
  ⟨.ball0, (-11, -991, -991, 1427), 1255⟩,
  ⟨.ball0, (-699, -1272, 166, 1366), 1255⟩,
  ⟨.ball0, (-30, 974, 974, 1449), 1254⟩,
  ⟨.ball0, (-398, 1542, -479, 1110), 1254⟩,
  ⟨.ball0, (560, 318, 1478, 1183), 1254⟩,
  ⟨.ball0, (-405, 91, -1467, 1294), 1254⟩,
  ⟨.ball0, (-1328, -226, 531, 1380), 1255⟩,
  ⟨.ball0, (663, -222, -1304, 1345), 1254⟩,
  ⟨.ball0, (1084, 1144, 734, 989), 1255⟩,
  ⟨.ball0, (-989, -620, -487, 1549), 1254⟩,
  ⟨.ball0, (1533, 241, -579, 1121), 1255⟩,
  ⟨.ball0, (-612, 223, 1430, 1237), 1254⟩,
  ⟨.ball0, (-716, 724, -1121, 1307), 1255⟩,
  ⟨.ball0, (-1027, 946, 71, 1430), 1254⟩,
  ⟨.ball0, (-1314, -434, 242, 1424), 1255⟩,
  ⟨.ball0, (660, -827, 1163, 1236), 1254⟩,
  ⟨.ball0, (496, -219, 1574, 1108), 1254⟩,
  ⟨.ball0, (1496, 747, -395, 1023), 1254⟩,
  ⟨.ball0, (265, -328, -1409, 1356), 1255⟩,
  ⟨.ball0, (1246, -713, 356, 1347), 1255⟩,
  ⟨.ball0, (-1138, 279, 1032, 1250), 1255⟩,
  ⟨.ball0, (1395, 162, -818, 1165), 1254⟩,
  ⟨.ball0, (-387, -1316, -79, 1453), 1254⟩,
  ⟨.ball0, (635, 1533, 377, 1050), 1254⟩,
  ⟨.ball0, (643, -1142, 743, 1316), 1255⟩,
  ⟨.ball0, (-1095, 348, 1104, 1209), 1255⟩,
  ⟨.ball0, (717, -1058, 826, 1298), 1255⟩,
  ⟨.ball0, (780, 784, 1343, 985), 1254⟩,
  ⟨.aff 1, (-895, -1606, 1034, -2073), -278⟩,
  ⟨.aff 2, (244, 311, -1644, -2291), -320⟩,
  ⟨.aff 3, (-1345, -1441, -1552, -2202), -207⟩,
  ⟨.aff 4, (1034, -1941, -791, -2037), -184⟩,
  ⟨.aff 5, (1723, -696, 680, -2302), -168⟩,
  ⟨.aff 6, (-588, 1101, 1214, -2561), -163⟩,
  ⟨.aff 7, (-2118, 359, -421, -2116), -165⟩
]

private def vs0 : List VertData := [
  ⟨(-1796481311949, -3452125897259, 4988182717351, 7763177790105), 13609070733649, (56884, 48911, 89557, 102920), 33626, (8, 18, 22, 35), (64, 40, 19, 133)⟩,
  ⟨(3825501721834, 1270886065049, -1353653404778, 2656807754277), 7914601191362, (97212, 76059, 54327, 87535), 33584, (17, 24, 36, 39), (8, 4, 114, 67)⟩,
  ⟨(-1823605831, 7551263092, -2591058266, 4799646952), 15102526184, (57622, 98304, 54292, 86363), 33552, (1, 10, 36, 41), (5, 71, 16, 35)⟩,
  ⟨(-6078326373541, 458686447200, -4899165663161, 8455570743854), 16914395491513, (41985, 67313, 46553, 98297), 33538, (16, 19, 37, 41), (23, 54, 60, 22)⟩,
  ⟨(12186743188082, 1729434831773, -5288938299830, 8905561559401), 25613148115918, (96718, 69961, 52003, 88322), 33491, (17, 36, 38, 39), (184, 72, 1, 10)⟩,
  ⟨(-1312398230890, 2845222195149, -2132836869374, 2781522142505), 7192014002731, (53576, 91462, 46100, 90882), 33477, (10, 19, 36, 41), (23, 2, 105, 20)⟩,
  ⟨(-3730512433, 8073137425, 1497583079, 6064808385), 16146274850, (50394, 98304, 71614, 90152), 33455, (1, 20, 40, 41), (30, 71, 16, 28)⟩,
  ⟨(516945814964, 609484365604, 415259749983, 441566313734), 1592931568480, (86804, 90611, 82620, 83702), 33454, (3, 15, 39, 40), (13, 59, 44, 88)⟩,
  ⟨(676368954914, 340669268221, -186617876614, 453084869193), 1438235871100, (96356, 81059, 57032, 86181), 33420, (3, 24, 36, 39), (1, 59, 88, 70)⟩,
  ⟨(2155064364, 1565296606, 6011179227, 3792826914), 12022358454, (77283, 74068, 98304, 86211), 33388, (2, 11, 39, 40), (18, 45, 68, 33)⟩,
  ⟨(246690156095, 31788533403, -116160723848, 187803195875), 528782061775, (96110, 69475, 51139, 88811), 33307, (17, 28, 36, 38), (37, 4, 89, 67)⟩,
  ⟨(-2848773065617, -13133738410555, -1949111166940, 14699606291709), 31817370533274, (59668, 38483, 61521, 95813), 33274, (29, 35, 37, 38), (186, 15, 39, 42)⟩,
  ⟨(101377591, 244704530, -587226, 112795958), 489409060, (79111, 98304, 65457, 80640), 33268, (1, 3, 36, 40), (59, 71, 55, 31)⟩,
  ⟨(166884337494, 183191369404, 191779481453, 166649795959), 554626562575, (85255, 87182, 88197, 85227), 33221, (15, 34, 39, 40), (18, 7, 90, 61)⟩,
  ⟨(-2420674906567, -1774072229319, -47376194714, 3322368456071), 6908607025560, (42573, 48706, 65086, 97052), 33216, (16, 21, 35, 37), (26, 17, 54, 29)⟩,
  ⟨(-738547712668, -5644349961110, -2541025397385, 7327159256081), 14801344433096, (62265, 40544, 54285, 97978), 33145, (7, 29, 37, 38), (11, 34, 52, 75)⟩,
  ⟨(-1350447764, 2958729626, 355990694, 2244301037), 5917459252, (50579, 98304, 69478, 90391), 33142, (1, 10, 20, 41), (105, 6, 2, 113)⟩,
  ⟨(-732778104809, -689716695408, -38234733568, 1146841201801), 2350414061919, (45104, 46304, 64469, 97513), 33141, (8, 16, 35, 37), (14, 42, 56, 29)⟩,
  ⟨(1684143124504, 1411325120561, 3857675722470, 2562640257772), 8074297991081, (79205, 76991, 96847, 86335), 33129, (11, 34, 39, 40), (13, 9, 101, 62)⟩,
  ⟨(-1365897584805, -1815135828179, 2680412292471, 4366572048641), 7707809596985, (53922, 50102, 88326, 102662), 33115, (8, 13, 18, 35), (109, 0, 100, 134)⟩,
  ⟨(194290318583, 1587023259930, -1535292613766, 1921261002446), 4176927587500, (68584, 90436, 41447, 95680), 33112, (5, 10, 19, 36), (5, 32, 36, 85)⟩,
  ⟨(2412841307157, -4018034303818, -11987113590002, 12261471104818), 28265909214737, (71130, 56219, 37743, 93964), 33110, (25, 36, 37, 38), (186, 34, 47, 48)⟩,
  ⟨(-3556866649, 83232716, -3529522711, 5650590568), 11114656445, (44563, 66026, 44724, 98853), 33070, (12, 16, 19, 37), (3, 27, 77, 157)⟩,
  ⟨(-3011105312290, 1908503128737, -5023632022382, 5340670070285), 12868091591839, (50200, 75255, 39951, 92735), 33061, (19, 36, 37, 41), (185, 3, 5, 27)⟩,
  ⟨(-10368693455489, 3759079797463, 11082507306313, 11199508337251), 30627229282218, (43349, 73579, 89250, 89500), 33033, (32, 35, 40, 41), (183, 30, 50, 38)⟩,
  ⟨(1863993116, -446592374, 6107692559, 4225848858), 12215385118, (75536, 63140, 98304, 88207), 33033, (2, 23, 35, 39), (53, 45, 33, 81)⟩,
  ⟨(-11693109784205, -5137165322451, 264772163939, 13029946143127), 28854975440538, (38978, 53868, 66137, 95129), 33002, (21, 35, 37, 41), (185, 54, 87, 14)⟩,
  ⟨(-1847512658475, 1087436755336, -3771476850361, 3935024213720), 9148227466867, (52300, 73326, 38517, 93725), 32986, (12, 19, 36, 37), (23, 48, 22, 32)⟩,
  ⟨(-1861237759, 5069294278, 1811309633, 4110589860), 10138588556, (53504, 98304, 77244, 92106), 32984, (1, 9, 20, 40), (43, 6, 108, 113)⟩,
  ⟨(-116232618838, -97778325151, 3695300350, 175419535596), 355264649914, (44094, 47498, 66217, 97895), 32929, (8, 16, 21, 35), (14, 100, 17, 164)⟩,
  ⟨(-4378853853923, 4560679518641, 3542718037037, 5504970842531), 13504885979316, (44286, 87667, 82727, 92250), 32916, (20, 32, 40, 41), (24, 6, 110, 43)⟩,
  ⟨(82168571, 198337930, -48220002, 125684062), 396675860, (79111, 98304, 57569, 86300), 32908, (1, 3, 6, 36), (82, 35, 12, 104)⟩,
  ⟨(35317947088, 123266444633, -201068950469, 230516033881), 470629486500, (70454, 82701, 37536, 97635), 32861, (5, 12, 19, 36), (27, 20, 41, 122)⟩,
  ⟨(607057356, 68834986, 1722349071, 1193726034), 3444698142, (77085, 66845, 98304, 88246), 32852, (2, 11, 23, 39), (103, 25, 9, 111)⟩,
  ⟨(647883826227, -2534556136042, -4541003138474, 5585134221478), 11932062990443, (69094, 51615, 40594, 96211), 32844, (7, 25, 37, 38), (21, 15, 93, 78)⟩,
  ⟨(127129588, 838682125, -360087616, 620074361), 1677364250, (70503, 98304, 51467, 89762), 32816, (1, 6, 10, 36), (36, 2, 31, 126)⟩,
  ⟨(25005023994, 159641570125, -136542329208, 177907691393), 398003680000, (69653, 91822, 43052, 94830), 32777, (5, 6, 10, 36), (35, 20, 82, 85)⟩,
  ⟨(183111777582, -12038977392, -183505199036, 223507373000), 529492789271, (88199, 64045, 42823, 93199), 32773, (14, 28, 36, 38), (10, 47, 63, 92)⟩,
  ⟨(-1193883358145, 490197136761, 1804805070374, 1615441621469), 4321485736104, (47430, 72969, 92906, 90034), 32763, (18, 32, 35, 40), (24, 51, 98, 107)⟩,
  ⟨(-123613082939, -959133398885, -51678314380, 1078826234803), 2297986381208, (62010, 38182, 64062, 96302), 32747, (4, 29, 35, 38), (11, 49, 52, 112)⟩,
  ⟨(-331976578781, -1058129392650, 1187589908076, 2043399743825), 3638578638107, (59556, 46477, 86926, 102340), 32727, (8, 22, 31, 35), (116, 84, 0, 133)⟩,
  ⟨(404617623127, 825990053605, -1649345386586, 1867579672397), 3785911272500, (72540, 79834, 36985, 97864), 32673, (5, 12, 14, 36), (86, 92, 32, 122)⟩,
  ⟨(-1034237633757, -1689256778444, -174199307074, 2309166330313), 4778542510287, (51351, 42368, 63146, 97205), 32670, (8, 29, 35, 37), (11, 17, 56, 112)⟩,
  ⟨(-2042404454565, 2710965595067, 2105685165655, 3101921050156), 7374301097493, (47384, 89628, 84249, 93103), 32668, (9, 20, 32, 40), (30, 98, 28, 169)⟩,
  ⟨(119038222101, 208034901276, 102181533081, 139981389962), 462527649220, (82402, 95012, 80014, 85370), 32643, (3, 15, 30, 40), (91, 55, 7, 130)⟩,
  ⟨(3837772956, 1585180086, 16208318459, 9546850138), 32416636918, (73294, 68740, 98304, 84836), 32614, (2, 35, 39, 40), (182, 9, 51, 25)⟩,
  ⟨(2970467101595, -2757573073788, -1859708972553, 5778048077037), 10189901175887, (84640, 47800, 53575, 102697), 32585, (7, 14, 26, 38), (63, 65, 93, 123)⟩,
  ⟨(842483058499, -650208247869, -2332746877152, 2461266495675), 5626170544897, (75349, 57962, 38363, 94205), 32582, (14, 25, 36, 38), (21, 37, 93, 86)⟩,
  ⟨(-269411332272, -405354877237, -4489985007173, 4533374882467), 9988213236983, (63768, 62876, 36075, 95280), 32574, (12, 25, 36, 37), (21, 27, 78, 86)⟩,
  ⟨(223206566172, -970570732203, 314377622867, 1130005755642), 2368592626645, (71711, 38681, 74234, 96801), 32573, (4, 31, 35, 38), (66, 39, 102, 84)⟩,
  ⟨(-591265047279, 159059236618, 563350788638, 636876757941), 1669092519618, (42320, 71781, 87655, 90542), 32530, (27, 32, 35, 41), (24, 74, 110, 107)⟩,
  ⟨(-736576811, 573357059, 3270165976, 2382049547), 6540331952, (58155, 71281, 98304, 89404), 32513, (2, 18, 35, 40), (38, 45, 68, 81)⟩,
  ⟨(-14542957607, -416556927525, -171466220445, 555092894574), 1095624281059, (64666, 40619, 55279, 98739), 32488, (4, 7, 29, 38), (15, 39, 65, 148)⟩,
  ⟨(2107230334468, -1769497228658, 4808962698736, 4336277963310), 11010055350981, (78079, 55003, 94160, 91347), 32472, (22, 23, 35, 39), (25, 69, 103, 64)⟩,
  ⟨(-2874149497943, -944091834579, -455066060425, 3357573098158), 7057710280206, (38847, 56769, 61310, 96713), 32459, (16, 21, 37, 41), (26, 3, 83, 14)⟩,
  ⟨(64965713, 156813790, 40647535, 91729616), 313627580, (79111, 98304, 74029, 84703), 32436, (1, 3, 30, 40), (44, 108, 12, 104)⟩,
  ⟨(-309842350044, -408401111218, -89214044333, 638778631181), 1269982545804, (49546, 44460, 60932, 98499), 32431, (8, 16, 29, 37), (75, 42, 17, 164)⟩,
  ⟨(4112703356, 799765666, 1511313629, 3883193994), 8225406712, (98304, 71908, 77577, 96475), 32428, (0, 15, 26, 39), (61, 106, 79, 76)⟩,
  ⟨(6145105518408, -8842120952067, 6938971076405, 11309794632796), 27229249535032, (80326, 44254, 82236, 92756), 32411, (33, 35, 38, 39), (184, 99, 69, 66)⟩,
  ⟨(550568439918, 736748323947, 89568885202, 348651036431), 1820447948900, (85356, 92058, 68760, 78087), 32384, (3, 36, 39, 40), (182, 7, 12, 8)⟩,
  ⟨(-3970391633831, 929235072182, -1758841965913, 5248934354144), 9838713662739, (39089, 71725, 53820, 100499), 32359, (16, 19, 20, 41), (105, 83, 3, 137)⟩,
  ⟨(3468326734934, 571168912868, 2080112908301, 3589593350487), 7561748299055, (95595, 70486, 83563, 96646), 32347, (15, 26, 34, 39), (62, 13, 57, 97)⟩,
  ⟨(2122508705224, 324583840961, 1320100213110, 2222194223572), 4682445309261, (95242, 70078, 84012, 96638), 32267, (11, 26, 34, 39), (61, 18, 96, 97)⟩,
  ⟨(36810199575, -20475808239, -18989099504, 54742518701), 101548058336, (89292, 52321, 53281, 100865), 32246, (14, 26, 28, 38), (89, 37, 46, 151)⟩,
  ⟨(-311015458066, -849053963686, 1848665052584, 2301430170420), 4379156756331, (60881, 52829, 93202, 99977), 32240, (18, 22, 23, 35), (53, 81, 0, 165)⟩,
  ⟨(179181793223, -229646480685, -95334975723, 412169751900), 723706660985, (81761, 44740, 56902, 102860), 32236, (4, 7, 26, 38), (46, 102, 52, 142)⟩,
  ⟨(412654380833, -653088255391, 471889918372, 824659664093), 1949824607035, (79405, 43584, 81396, 93253), 32220, (31, 33, 35, 38), (58, 49, 115, 116)⟩,
  ⟨(295503752581, 130173340729, -162359272820, 262812048833), 695615421137, (93376, 77800, 50239, 90296), 32185, (17, 24, 28, 36), (80, 10, 1, 174)⟩,
  ⟨(-45724369, 488974684, 1227106544, 958606456), 2454213088, (64315, 78593, 98304, 91134), 32176, (2, 11, 18, 40), (73, 51, 9, 111)⟩,
  ⟨(1333068242968, -1742842017261, 1865428255971, 2518243258420), 6063155596280, (79944, 46697, 85699, 92755), 32154, (22, 33, 35, 39), (58, 53, 118, 116)⟩,
  ⟨(3857788427, 3332678098, -1907945752, 3652681694), 10168336500, (90399, 87015, 53239, 89077), 32131, (3, 5, 24, 36), (80, 8, 82, 95)⟩,
  ⟨(-559717926, 3554910895, -581794789, 1833531087), 7109821790, (60376, 98304, 60173, 82436), 32129, (1, 36, 40, 41), (183, 6, 2, 12)⟩,
  ⟨(7451616135146, -1449690990831, -855905043190, 6884424074853), 15368095947654, (97312, 59353, 61886, 94894), 32129, (17, 26, 38, 39), (99, 4, 106, 89)⟩,
  ⟨(-55934453858, 606704940068, 1465098523897, 1155676269110), 2945924658260, (64291, 79032, 98129, 91245), 32120, (9, 11, 18, 40), (68, 98, 101, 166)⟩,
  ⟨(-4218642606103, 77043599494, 2695887573950, 4523112285645), 10564427715838, (39365, 66013, 82259, 93594), 32118, (13, 27, 35, 41), (50, 87, 119, 109)⟩,
  ⟨(-232697099724, -485408962894, -293743190741, 811601690813), 1540123557880, (55634, 44880, 53036, 100071), 32111, (7, 16, 29, 37), (56, 15, 77, 148)⟩,
  ⟨(2314779971, 479407378, 747351164, 2228390742), 4629559942, (98304, 72322, 76115, 97081), 32084, (0, 15, 24, 26), (158, 94, 57, 79)⟩,
  ⟨(-1402164301954, -1245230975839, -2914778817181, 4518666920293), 8435164308735, (54642, 55861, 42889, 100643), 32030, (7, 12, 16, 37), (22, 75, 78, 152)⟩,
  ⟨(-401026239144, -556753213813, -1492859612057, 2031052043353), 3931385549747, (58850, 56254, 40650, 99393), 31997, (7, 12, 25, 37), (48, 34, 77, 152)⟩,
  ⟨(1214460284, 344774473, 356850119, 1087432134), 2428920568, (98304, 74838, 75164, 94876), 31976, (0, 15, 24, 39), (88, 114, 57, 76)⟩,
  ⟨(581181834473, 306382625543, -370133108758, 573006311407), 1459891451500, (91625, 79289, 48920, 91258), 31857, (5, 24, 28, 36), (67, 92, 70, 154)⟩,
  ⟨(-22901034, -29238174, 369504959, 315950708), 739009918, (63505, 62943, 98304, 93554), 31853, (2, 18, 23, 35), (64, 25, 51, 111)⟩,
  ⟨(2767099161, 3007588164, -1526639918, 2939118280), 8166224500, (87742, 89672, 53284, 89123), 31831, (3, 5, 6, 36), (36, 31, 70, 95)⟩,
  ⟨(-2590436829589, 434004845671, -693954399227, 3284551538458), 6155171567498, (37954, 70156, 58147, 100507), 31791, (16, 20, 21, 41), (117, 54, 60, 170)⟩,
  ⟨(-90929019959, -614072375246, 433995394404, 971183780083), 1787521693489, (62202, 43022, 81447, 101142), 31786, (4, 8, 31, 35), (40, 49, 112, 128)⟩,
  ⟨(34943314107, 249238475150, -234979157574, 328978551694), 676347287500, (68921, 89686, 42767, 97413), 31764, (5, 6, 10, 19), (178, 20, 135, 36)⟩,
  ⟨(113726502481, 192775052613, -572050185114, 629860137093), 1296427380577, (71285, 75281, 36618, 97376), 31757, (12, 14, 25, 36), (47, 48, 41, 168)⟩,
  ⟨(-2127819607815, -516348430474, 621895124346, 2320833906973), 5159694252682, (38509, 58977, 73435, 95014), 31749, (13, 21, 35, 41), (26, 74, 117, 100)⟩,
  ⟨(305163511924, 142102431761, 69546706387, 252148020978), 632497294100, (97155, 80259, 72742, 91662), 31733, (3, 15, 24, 39), (79, 8, 7, 124)⟩,
  ⟨(967379299133, -290455370280, -257103806705, 1066086260501), 2196763763695, (94395, 56870, 57865, 97340), 31616, (17, 26, 28, 38), (63, 10, 72, 162)⟩,
  ⟨(94795049787, 253078538360, 197374026274, 218814835634), 600446286518, (75882, 93158, 87078, 89418), 31605, (9, 15, 34, 40), (13, 101, 91, 176)⟩,
  ⟨(695658883779, 1867141509540, 1447069145967, 1610137798004), 4418071037686, (75855, 93232, 87001, 89420), 31604, (9, 15, 30, 40), (44, 108, 90, 181)⟩,
  ⟨(112190389897, 56471189827, -146852521712, 180210981923), 395315058500, (84135, 74897, 41190, 95411), 31509, (5, 14, 28, 36), (37, 80, 41, 159)⟩,
  ⟨(288439542277, -402651730551, -606733872924, 933323594301), 1855761806491, (75722, 51316, 44109, 98496), 31490, (7, 14, 25, 38), (47, 34, 46, 153)⟩,
  ⟨(771316996, 128501879, 188524600, 741983493), 1542633992, (98304, 70995, 73545, 97057), 31432, (0, 17, 24, 26), (161, 76, 106, 114)⟩,
  ⟨(679622394, 636359856, -317676117, 700016823), 1860985000, (89469, 87945, 54348, 90187), 31351, (3, 5, 6, 24), (154, 124, 70, 82)⟩,
  ⟨(2444964266756, -238094376219, 2146875234747, 3002853047150), 6394675222871, (90593, 63095, 87538, 96310), 31350, (11, 22, 26, 39), (118, 62, 103, 173)⟩,
  ⟨(210891901159, 37685870390, 128313655496, 235532779620), 477166214152, (94500, 70711, 83159, 97885), 31333, (11, 15, 26, 34), (61, 62, 176, 163)⟩,
  ⟨(-769823548250, 1016235620244, 1389998668281, 1503225221766), 3624354266196, (51615, 83911, 90670, 92717), 31313, (9, 18, 32, 40), (38, 43, 73, 175)⟩,
  ⟨(404563656654, -371065615905, 243683221714, 582338312711), 1306627119110, (85827, 46924, 77758, 94744), 31256, (26, 33, 38, 39), (58, 72, 118, 115)⟩,
  ⟨(-389577793134, -381575169443, 388662600300, 872953303328), 1605299360102, (49631, 49958, 81403, 101174), 31227, (8, 13, 21, 35), (87, 29, 19, 150)⟩,
  ⟨(7705547396, 29446851769, 51772805318, 42566286028), 112085588545, (70041, 82753, 95807, 90424), 31225, (9, 11, 34, 40), (18, 90, 73, 176)⟩,
  ⟨(29601587072, -46054452480, 718316193, 70502950845), 131429161325, (80296, 42571, 65894, 100691), 31150, (4, 26, 31, 38), (115, 49, 65, 144)⟩,
  ⟨(609068396916, -74703688146, 595747632432, 777697011270), 1688878065797, (89170, 62637, 88653, 95714), 31137, (11, 22, 23, 39), (53, 33, 96, 165)⟩,
  ⟨(23848295, 57564850, -1756325, 39661139), 115129700, (79111, 98304, 64536, 88112), 31106, (1, 3, 6, 30), (130, 126, 55, 31)⟩,
  ⟨(-1748877676672, 2294126675263, -1185296945870, 2872402375183), 6371387976153, (47547, 89133, 53344, 95081), 31073, (10, 19, 20, 41), (60, 16, 5, 178)⟩,
  ⟨(27901714, 371435, 2742550, 25654233), 55803428, (98304, 65972, 68756, 95664), 31047, (0, 17, 26, 39), (72, 57, 114, 94)⟩,
  ⟨(-4180907722, 392496258, 5751416191, 6375735988), 14958176046, (47218, 67255, 90734, 93469), 31014, (18, 27, 32, 35), (50, 38, 109, 175)⟩,
  ⟨(2803543, 226185394, 99565385, 172585104), 452370788, (65942, 98304, 79960, 90538), 30985, (1, 9, 30, 40), (91, 55, 28, 120)⟩,
  ⟨(-25422096683, -10941441501, 33419657065, 49135552783), 97040805511, (48367, 58146, 88105, 98719), 30976, (13, 18, 27, 35), (107, 74, 19, 177)⟩,
  ⟨(-281129200792, 199892665759, 171165584194, 342145374763), 780892179753, (41942, 82311, 79900, 94250), 30964, (20, 27, 32, 41), (50, 30, 119, 169)⟩,
  ⟨(-2289495, 21763116, 364261322, 312384284), 728522644, (65330, 67493, 98304, 93637), 30949, (2, 11, 18, 23), (165, 81, 33, 68)⟩,
  ⟨(-20560691919, -103249760398, 47059452142, 150748345271), 286406157429, (60831, 41910, 76304, 100030), 30946, (4, 8, 29, 35), (42, 39, 84, 128)⟩,
  ⟨(-355158056, 1286831779, 328361726, 1134244918), 2573663558, (56492, 98304, 73897, 94418), 30911, (1, 9, 10, 20), (180, 16, 28, 120)⟩,
  ⟨(135332402, 30411544, 1998533, 112442217), 270664804, (98304, 72899, 66019, 92761), 30878, (0, 17, 24, 39), (1, 79, 106, 94)⟩,
  ⟨(178101157802, -187138802955, 93166115062, 288478543293), 619196608690, (84386, 45729, 75396, 96068), 30735, (26, 31, 33, 38), (66, 99, 102, 155)⟩,
  ⟨(21606479723, -58982906018, 60647255380, 93224310585), 198402827579, (72673, 46052, 85568, 96329), 30614, (22, 31, 33, 35), (66, 69, 40, 156)⟩,
  ⟨(-1079457276390, 216027701748, -7212384712, 1317313287529), 2548812400764, (37780, 71090, 65350, 99407), 30414, (13, 20, 21, 41), (83, 87, 119, 171)⟩,
  ⟨(580741426362, -349353246601, 481949678699, 812877643273), 1784233428828, (86866, 52704, 83238, 95393), 30393, (22, 26, 33, 39), (99, 69, 96, 167)⟩,
  ⟨(-2053245910424, 696545516672, 705482450350, 2423734388955), 5010881211290, (38682, 74645, 74762, 97235), 30321, (13, 20, 27, 41), (110, 74, 117, 179)⟩,
  ⟨(-15872893, 149391059, 30357940, 137419644), 298782118, (62054, 98304, 72194, 95678), 29098, (1, 9, 10, 30), (172, 126, 108, 113)⟩,
  ⟨(825960789504, 217693947377, -229795784834, 8033689076108), 9253787446501, (71385, 67077, 63908, 122431), 29077, (9, 14, 16, 26), (123, 131, 127, 125)⟩,
  ⟨(40617728033, 99944402648, -154732345093, 257337975289), 440695734500, (71576, 80398, 42525, 103804), 29039, (5, 12, 14, 19), (168, 135, 32, 41)⟩,
  ⟨(260277717168, -6610399261, -94605223334, 2473727045684), 2890398503023, (71437, 65386, 63390, 121624), 28601, (7, 14, 16, 26), (121, 142, 46, 153)⟩,
  ⟨(43122013033, 35486201003, 4836883777, 49159737702), 111163130960, (90958, 86456, 68387, 94518), 28483, (3, 6, 15, 24), (158, 88, 95, 130)⟩,
  ⟨(65309082432, 106774473432, -85475002536, 1079509419978), 1262356907279, (68926, 71079, 61098, 121579), 28371, (6, 9, 14, 16), (121, 132, 129, 127)⟩,
  ⟨(22149025, 286039285, -5894650, 254329481), 572078570, (68073, 98304, 64860, 94671), 28275, (1, 6, 10, 30), (172, 120, 104, 35)⟩,
  ⟨(704968751442, 306536098447, -159232234039, 4660165386034), 5482380020537, (73963, 69200, 63632, 121243), 28265, (6, 9, 14, 26), (121, 151, 160, 125)⟩,
  ⟨(-2685400481, -15177342628, 12930744196, 37683548279), 59605502187, (62583, 48848, 79753, 106968), 28230, (4, 8, 29, 31), (136, 144, 84, 112)⟩,
  ⟨(108770582481, 221625922617, -170754039357, 2081110577502), 2441639014052, (68455, 71484, 60952, 121395), 28224, (6, 9, 16, 20), (170, 132, 180, 125)⟩,
  ⟨(39412067270, 44450347531, 7761308971, 50115196778), 118593313860, (87315, 90099, 69824, 93230), 28127, (3, 6, 15, 30), (181, 44, 104, 124)⟩,
  ⟨(88956694164, -60354557599, 106598464930, 1448446621532), 1707473699773, (68950, 63219, 69627, 121130), 28115, (9, 16, 26, 29), (143, 138, 149, 121)⟩,
  ⟨(75470955450, 181382629230, -160777243572, 1608937808016), 1900673984987, (68138, 71790, 59992, 121012), 28104, (6, 14, 16, 20), (137, 129, 139, 125)⟩,
  ⟨(-34300245311, -75056754572, 130306047286, 387965639646), 534693172027, (61331, 56336, 81507, 113087), 28103, (8, 18, 22, 31), (147, 40, 134, 0)⟩,
  ⟨(-52772032932, -113948886487, 208854233352, 697509384121), 931711757830, (61824, 57520, 80226, 114598), 27899, (8, 13, 18, 31), (141, 133, 136, 19)⟩,
  ⟨(117348200589, 277411776644, -385827583049, 757252027277), 1226347358500, (71807, 80360, 44917, 106003), 27897, (5, 6, 14, 19), (139, 122, 85, 159)⟩,
  ⟨(-46332284988, -100673244263, 184661827218, 625688521934), 833296428836, (61892, 57618, 80059, 114744), 27873, (8, 13, 29, 31), (140, 128, 134, 150)⟩,
  ⟨(114051402176, 361596411545, -355764342250, 3053861548078), 3641708262152, (67588, 72043, 59133, 120493), 27864, (14, 16, 19, 20), (60, 139, 132, 146)⟩,
  ⟨(163679630255, -160223367990, 303681056661, 2824566991992), 3371303804828, (68717, 62421, 71439, 120443), 27849, (9, 26, 29, 31), (144, 140, 155, 131)⟩,
  ⟨(129032461925, 390064622540, -367914540729, 3157080882693), 3767933432524, (67780, 72320, 59136, 120447), 27840, (6, 14, 19, 20), (137, 178, 132, 135)⟩,
  ⟨(-110965043348, -275914291509, 647833455102, 2677595047890), 3385497161908, (63387, 60194, 78076, 117368), 27822, (9, 13, 29, 31), (136, 138, 141, 145)⟩,
  ⟨(-127790775628, -317533902480, 746001769461, 3080278297416), 3895123348217, (63385, 60193, 78087, 117362), 27822, (9, 13, 18, 31), (134, 147, 140, 177)⟩,
  ⟨(15302656959, -10108965181, -2551193075, 162358630064), 194473030045, (70692, 62129, 64676, 120249), 27776, (4, 7, 16, 26), (123, 143, 65, 148)⟩,
  ⟨(9047172, -6276148, 1488625, 108562037), 129490585, (70114, 62359, 66289, 120479), 27750, (4, 16, 26, 29), (131, 144, 148, 142)⟩,
  ⟨(4397559836, -4686390060, 7276510671, 70152980139), 84388253159, (68951, 61896, 71186, 120016), 27573, (4, 26, 29, 31), (138, 128, 102, 143)⟩,
  ⟨(-26538784414, -54385083443, 129558836900, 602317033858), 755002218070, (63232, 60815, 76782, 117818), 27552, (9, 13, 21, 29), (150, 149, 140, 171)⟩,
  ⟨(12226446109, 45032590888, -54154143008, 403749975407), 487854559807, (67178, 71585, 58261, 119773), 27439, (14, 16, 19, 25), (157, 168, 153, 137)⟩,
  ⟨(-27299914099, -101826692466, 266604579588, 1009113605376), 1294671669593, (64154, 60381, 79031, 116617), 27404, (9, 18, 22, 31), (133, 156, 141, 166)⟩,
  ⟨(4347039684, -3866258881, -1096367300, 50630377214), 61449954895, (70172, 61412, 64366, 119532), 27302, (4, 7, 16, 29), (75, 143, 52, 142)⟩,
  ⟨(-41776413852, -73434460379, 177761391554, 1025912823322), 1267476399022, (63375, 61739, 74727, 118581), 27289, (9, 16, 21, 29), (164, 145, 131, 170)⟩,
  ⟨(-11123227002, -18824490539, 30397328460, 114205887974), 153602459870, (60790, 57504, 78505, 114263), 27156, (8, 13, 21, 29), (145, 164, 136, 100)⟩,
  ⟨(99717176303, 32155493603, -25691805408, 404747028717), 507863505730, (78403, 69685, 62220, 117765), 26646, (6, 14, 26, 28), (63, 162, 159, 127)⟩,
  ⟨(-18801908011, -15619825031, -64737565618, 162183546785), 248029415445, (60568, 61408, 48430, 108389), 26448, (7, 12, 16, 25), (157, 153, 78, 77)⟩,
  ⟨(22238696677, 114274289, -49296422874, 377740125321), 468151428221, (68649, 65551, 58635, 118415), 26423, (7, 14, 16, 25), (146, 152, 93, 123)⟩,
  ⟨(52585562667, 35394075387, -31687097772, 88824180093), 166260698500, (86263, 79487, 53045, 100548), 26235, (5, 6, 24, 28), (174, 80, 159, 95)⟩,
  ⟨(26121231947, -13351463605, 46795980982, 260861924598), 326778510135, (70774, 62858, 74921, 117852), 26203, (9, 26, 31, 33), (115, 156, 167, 138)⟩,
  ⟨(4543599483, -5739023256, 19159876062, 80245451188), 103039283429, (68425, 61885, 77722, 116574), 26119, (9, 22, 31, 33), (116, 155, 167, 147)⟩,
  ⟨(-4442482971, 20713196059, -50002719888, 239746422875), 308827725455, (64593, 69931, 54924, 116412), 25907, (12, 16, 19, 25), (146, 168, 152, 22)⟩,
  ⟨(86510403892, 36616936304, 24237029083, 176381458881), 261273541937, (87235, 74720, 71615, 109778), 25907, (6, 15, 24, 26), (76, 161, 160, 124)⟩,
  ⟨(4622588223, 3625319643, -5045057688, 12910884921), 20896212500, (80033, 76905, 49713, 106027), 25746, (5, 6, 14, 28), (151, 92, 154, 135)⟩,
  ⟨(1295060501801, 609688186810, 491592302354, 3095567184090), 4401333517654, (84819, 74614, 72855, 111629), 25587, (6, 9, 15, 26), (163, 158, 127, 181)⟩,
  ⟨(29007341297, 11635112497, 5970922295, 61248636852), 89621413723, (86747, 74044, 69902, 110324), 25557, (6, 17, 24, 26), (94, 158, 162, 174)⟩,
  ⟨(192801680153, 65138478562, -19211965025, 599289283409), 792183556541, (81486, 70924, 63946, 115114), 25533, (6, 17, 26, 28), (89, 151, 174, 161)⟩,
  ⟨(443867344190, 182284211042, 249984525235, 1008629666718), 1490604558120, (85051, 73550, 76526, 109881), 25459, (9, 11, 15, 26), (97, 160, 173, 176)⟩,
  ⟨(-8269395600, -9371230129, 5688243027, 40260449725), 58677717064, (56300, 55069, 71889, 110502), 25440, (8, 16, 21, 29), (149, 150, 56, 29)⟩,
  ⟨(646547409, -1282088916, 8051191404, 18933561180), 27314534326, (67087, 62459, 84853, 110963), 25428, (11, 18, 22, 23), (64, 103, 111, 166)⟩,
  ⟨(19722326382, -35686128852, 232155832722, 571627115730), 812645544235, (67126, 62658, 84258, 111635), 25427, (9, 11, 18, 22), (165, 147, 173, 73)⟩,
  ⟨(79761201379, -23179145253, 132375656385, 571830369056), 743657711773, (72565, 63493, 77201, 115929), 25357, (9, 22, 26, 33), (118, 155, 156, 173)⟩,
  ⟨(873810470, 2808619687, -4834527065, 14390123366), 20426444969, (68339, 74547, 50024, 111705), 25312, (12, 14, 19, 25), (146, 157, 86, 122)⟩,
  ⟨(-48805493531, 48060870009, 49926143313, 117371856764), 212898992211, (50512, 80330, 80904, 101666), 25150, (9, 20, 27, 32), (110, 175, 43, 179)⟩,
  ⟨(-56007373727, 15589315038, 51573005361, 464864575988), 590657968012, (59321, 67265, 71258, 117114), 25003, (9, 16, 20, 21), (83, 171, 149, 129)⟩,
  ⟨(-81022665038, 22882739409, 75495347940, 629820060506), 806108616190, (58948, 67396, 71673, 116739), 24835, (9, 13, 20, 21), (117, 170, 145, 179)⟩,
  ⟨(199394246, 21210679070, 1890338842, 27220136554), 49391058601, (65800, 93680, 68044, 101653), 24795, (6, 9, 10, 30), (120, 126, 181, 180)⟩,
  ⟨(121941821486, -7933931091, 170802367251, 613664385590), 832675675355, (75133, 64911, 78979, 113834), 24659, (9, 11, 22, 26), (96, 167, 163, 166)⟩,
  ⟨(22223445959, 12833312781, -9154903810, 41405152867), 70818515303, (86101, 77412, 57063, 103852), 24527, (6, 17, 24, 28), (67, 154, 162, 161)⟩,
  ⟨(-1927669586, 1621926980, 2941612441, 5873640614), 10377689580, (53362, 75778, 84112, 102628), 24145, (9, 18, 27, 32), (107, 169, 98, 177)⟩,
  ⟨(66226674770, 48497571601, 62267338922, 145270939702), 252309261750, (82738, 78132, 81709, 103269), 24049, (9, 11, 15, 34), (97, 90, 101, 163)⟩,
  ⟨(-96599745597, 21404793706, 145283117720, 501863931814), 711684892580, (56640, 67507, 78914, 111750), 23906, (9, 13, 18, 27), (109, 175, 179, 141)⟩,
  ⟨(-47002801280, 564197066055, -264959401054, 1413826124823), 2061372840849, (64041, 83473, 57112, 110484), 23887, (6, 10, 19, 20), (105, 139, 180, 85)⟩,
  ⟨(-222614854331, 103579181813, 222883171585, 935962565052), 1340400745295, (54651, 70600, 76433, 111297), 23369, (9, 13, 20, 27), (119, 169, 177, 171)⟩,
  ⟨(-25902385740, 552869771190, -9482438262, 995103512634), 1572520991747, (64456, 88577, 65140, 107007), 22886, (6, 9, 10, 20), (113, 178, 129, 172)⟩,
  ⟨(225597256240, 282212850823, 126099359753, 582701356484), 985057767910, (80545, 84311, 73925, 104303), 22670, (6, 9, 15, 30), (91, 130, 172, 160)⟩,
  ⟨(579126143596, 738747226134, 873278486207, 1488700944530), 13985082902742, (68249, 68997, 69628, 72512), 21632, (35, 36, 39, 40), (59, 45, 183, 184)⟩,
  ⟨(-1270229377173, 2294717854587, 1316439905821, 4137879816671), 35126214313802, (63166, 69817, 67992, 73256), 21226, (35, 36, 40, 41), (71, 24, 185, 182)⟩,
  ⟨(610192400276, -164543623234, 192061633236, 1283590154246), 9871064029925, (69587, 64443, 66811, 74058), 20860, (35, 36, 38, 39), (4, 58, 182, 186)⟩,
  ⟨(-1764723158941, 58468154683, -615581465697, 3967742289527), 26532782844924, (61177, 65680, 64015, 75336), 20559, (35, 36, 37, 41), (23, 26, 183, 186)⟩,
  ⟨(-27726915617, -1528484761427, -1034549351732, 4245957828093), 26590044931650, (65467, 61768, 62986, 76000), 20501, (35, 36, 37, 38), (21, 11, 184, 185)⟩
]

set_option maxRecDepth 20000 in
private lemma cell0_ok : verifyCell ⟨0, by decide⟩ hs0 vs0 ctr0 = true := by
  decide

private def ctr1 : NVec4 := (54267, 48464, 84938, 69627)

private def hs1 : List HSData := [
  ⟨.base 1, (-2, 0, 0, 0), 1⟩,
  ⟨.base 3, (0, -2, 0, 0), 1⟩,
  ⟨.base 4, (0, 0, 2, 0), 1⟩,
  ⟨.base 6, (140, -140, 0, 0), 99⟩,
  ⟨.ball0, (-869, -1160, 177, 1367), 1255⟩,
  ⟨.ballA, (-91, -23, 44, -1997), 748⟩,
  ⟨.ball0, (-581, 233, 1331, 1355), 1254⟩,
  ⟨.ball0, (-141, -881, 952, 1516), 1255⟩,
  ⟨.ball0, (478, -175, 1574, 1125), 1255⟩,
  ⟨.ball0, (709, -1110, 838, 1250), 1254⟩,
  ⟨.ballA, (-970, -208, 426, -1684), 945⟩,
  ⟨.ball0, (-1529, 53, 1183, -510), 1255⟩,
  ⟨.ballA, (-985, 34, 762, -1564), 1019⟩,
  ⟨.ballA, (-993, -470, 83, -1669), 954⟩,
  ⟨.ball0, (-199, -1381, -62, 1431), 1254⟩,
  ⟨.ball0, (-1296, -540, 100, 1421), 1255⟩,
  ⟨.ballA, (298, -322, 979, -1688), 942⟩,
  ⟨.ball0, (666, -788, 1173, 1249), 1255⟩,
  ⟨.ball0, (-705, -1128, -21, 1493), 1254⟩,
  ⟨.ballA, (-117, -998, -52, -1728), 917⟩,
  ⟨.ballA, (-640, 119, 988, -1612), 989⟩,
  ⟨.ball0, (634, -886, 1587, -544), 1255⟩,
  ⟨.ballA, (398, -557, 997, -1593), 1002⟩,
  ⟨.ball0, (-1593, -1072, 131, -544), 1254⟩,
  ⟨.ball0, (-1271, -46, 714, 1368), 1254⟩,
  ⟨.ballA, (465, -947, 554, -1606), 993⟩,
  ⟨.ball0, (-442, 298, 1530, 1172), 1254⟩,
  ⟨.ballA, (193, -51, 997, -1722), 921⟩,
  ⟨.ballA, (194, -987, 273, -1707), 930⟩,
  ⟨.ball0, (-1095, -753, 0, 1495), 1255⟩,
  ⟨.ball0, (-629, 314, 1447, 1188), 1254⟩,
  ⟨.ball0, (-1373, -1347, 90, -539), 1254⟩,
  ⟨.ballA, (-866, -850, 57, -1589), 1004⟩,
  ⟨.ball0, (-1073, 376, 1145, 1181), 1254⟩,
  ⟨.ball0, (479, -1175, 598, 1425), 1254⟩,
  ⟨.aff 0, (895, 1606, -1034, 2073), 278⟩,
  ⟨.aff 2, (1139, 1917, -2678, -218), -42⟩,
  ⟨.aff 3, (-450, 165, -2586, -129), 71⟩,
  ⟨.aff 4, (1929, -335, -1825, 36), 94⟩,
  ⟨.aff 5, (2618, 910, -354, -229), 110⟩,
  ⟨.aff 6, (307, 2707, 180, -488), 115⟩,
  ⟨.aff 7, (-1223, 1965, -1455, -43), 113⟩
]

private def vs1 : List VertData := [
  ⟨(73671146752, -163530665222, -585766884, -691164546122), 1841292721669, (68158, 59715, 65515, 40935), 38990, (5, 36, 38, 39), (122, 8, 2, 1)⟩,
  ⟨(68855299115, -352237029339, -64503229206, -1284728857648), 3428610970713, (66852, 58803, 64303, 40979), 38884, (5, 36, 37, 38), (126, 6, 0, 3)⟩,
  ⟨(442289395058, -544951868280, 632811282149, -6771755327058), 18079311019478, (67139, 63560, 67829, 40988), 38816, (5, 36, 39, 40), (120, 15, 3, 0)⟩,
  ⟨(-1473209547692, -323203215250, 57192793339, -7399008794538), 19946300519238, (60695, 64474, 65723, 41225), 38389, (5, 36, 37, 40), (14, 4, 2, 1)⟩,
  ⟨(-1826329816823, -202350680948, 155028086299, -6121617481739), 16580937735057, (58317, 64736, 66148, 41340), 37876, (5, 37, 40, 41), (14, 26, 18, 3)⟩,
  ⟨(-2850646347159, -13140229335156, -1948837212861, 14702987673005), 31798037162841, (59660, 38453, 61519, 95838), 36945, (14, 35, 37, 38), (126, 17, 10, 7)⟩,
  ⟨(-27350028028, -521004882293, -45531259001, -708482529457), 1908166043814, (64596, 47642, 63972, 41203), 36811, (5, 19, 37, 38), (31, 1, 9, 39)⟩,
  ⟨(-1184483776051, -3265867864844, -426918890364, 3942249252075), 8304388711089, (56188, 39762, 62166, 96647), 36445, (14, 18, 35, 37), (16, 5, 37, 58)⟩,
  ⟨(1096872992034, -2488973190460, 1019321707636, -3795391859838), 10135934011147, (72628, 49443, 72126, 40996), 36361, (5, 28, 38, 39), (49, 0, 21, 9)⟩,
  ⟨(18594959019, -129884670524, 16254952789, -172369400937), 462877162761, (68168, 47146, 67837, 41131), 36050, (5, 19, 28, 38), (68, 8, 6, 140)⟩,
  ⟨(162198566217, -1414324582008, 289562272401, 1621810631023), 3368231965854, (68691, 38017, 71170, 97091), 35513, (14, 34, 35, 38), (19, 5, 38, 41)⟩,
  ⟨(-11693704191623, -5129012433494, 258170189911, 13050804392797), 29080252914411, (39182, 53977, 66117, 94947), 35404, (15, 35, 37, 41), (128, 51, 30, 12)⟩,
  ⟨(-1761847711658, -935838219070, 14830809585, 2111904464052), 4614507248592, (40513, 52245, 65746, 95529), 35254, (15, 29, 35, 37), (16, 11, 75, 83)⟩,
  ⟨(3086014740152, -4441210178233, 3485229530751, 5679498094628), 13666445545184, (80334, 44238, 82249, 92771), 35219, (9, 35, 38, 39), (122, 50, 20, 19)⟩,
  ⟨(-487613700077, -5927184485, 12527931447, -1665747491723), 5646934863450, (59876, 65467, 65681, 46204), 35216, (36, 37, 40, 41), (4, 124, 128, 3)⟩,
  ⟨(865045264047, -677841399975, 3683526347436, -5092015028692), 13726872198872, (69665, 62299, 83122, 41225), 35194, (5, 27, 39, 40), (59, 2, 90, 24)⟩,
  ⟨(-747480840546, -774131032535, -52781743330, 1244723955570), 2599421913525, (46690, 46018, 64205, 96917), 35187, (18, 29, 35, 37), (12, 7, 28, 45)⟩,
  ⟨(-19286184, -94307865, -11386449, 71097871), 188615730, (58834, 32768, 61579, 90239), 35184, (1, 14, 37, 38), (5, 31, 38, 37)⟩,
  ⟨(-3381177965709, -1251038803705, 401478374603, -4017385518714), 11198990664063, (45749, 58214, 67885, 42026), 34934, (5, 13, 37, 41), (77, 4, 22, 39)⟩,
  ⟨(202566282886, -365672200112, 236170003800, 454299159820), 1048883612161, (78192, 42688, 80292, 93921), 34896, (9, 34, 35, 38), (10, 13, 74, 62)⟩,
  ⟨(749228282080, -978785172442, 1051358432841, 1415685565384), 3403747780587, (79961, 46690, 85778, 92793), 34653, (9, 17, 35, 39), (27, 13, 40, 62)⟩,
  ⟨(558384429228, -1063656532930, 1052448002938, -1830979252202), 4915005876971, (72981, 51353, 79569, 41121), 34643, (5, 16, 28, 39), (48, 8, 24, 144)⟩,
  ⟨(-708720653905, -231748478426, 127671842080, -828109452483), 2311732529638, (45444, 58966, 69155, 42059), 34603, (5, 10, 13, 41), (104, 18, 26, 129)⟩,
  ⟨(1791199044, -423797598, 5876936837, 4062626806), 11753873674, (75523, 63173, 98304, 88187), 34518, (2, 8, 35, 39), (27, 25, 73, 72)⟩,
  ⟨(133216088225, -175884769769, 419597419660, -597433499180), 1608903302144, (70962, 58371, 82627, 41200), 34503, (5, 16, 27, 39), (78, 15, 21, 139)⟩,
  ⟨(3837772956, 1585180086, 16208318459, 9546850138), 32416636918, (73294, 68740, 98304, 84836), 34399, (2, 35, 39, 40), (120, 59, 54, 23)⟩,
  ⟨(-2963754323507, -15181431875, 1758926191198, -3800418010418), 10610799913890, (47230, 65442, 76399, 42063), 34214, (5, 10, 40, 41), (91, 4, 22, 76)⟩,
  ⟨(2086027010604, -1682085218817, 4884400396157, 4317364852666), 11025153392161, (77935, 55537, 94569, 91199), 34183, (8, 17, 35, 39), (20, 23, 73, 88)⟩,
  ⟨(-58603260248, -60722839555, -3124690469, 85287411483), 189162986712, (45232, 44498, 64453, 95084), 34135, (4, 18, 29, 37), (16, 75, 52, 45)⟩,
  ⟨(-383986705018, 139304147723, 410419478566, 414894894390), 1135819192393, (43380, 73573, 89216, 89475), 34079, (33, 35, 40, 41), (124, 35, 44, 42)⟩,
  ⟨(-1562706246080, -357256222019, 491428178679, 1696455766760), 3727483758760, (38060, 59254, 74176, 95362), 34020, (15, 24, 35, 41), (44, 11, 85, 83)⟩,
  ⟨(-449995216, -3329510181, -238485765, -1573159613), 6659020362, (61107, 32768, 63188, 50053), 33905, (1, 19, 37, 38), (6, 17, 68, 86)⟩,
  ⟨(172997681328, -279074384865, 309288467042, 83579915934), 639293830980, (83270, 36927, 97242, 74104), 33851, (3, 17, 21, 39), (43, 36, 40, 56)⟩,
  ⟨(100499402089, -208682876789, 120501012844, -76621672116), 437227465080, (80599, 34256, 83597, 54051), 33761, (3, 25, 38, 39), (49, 50, 36, 47)⟩,
  ⟨(-5504433095, 1003849901, 5123641904, 1401222649), 11008866190, (32768, 71511, 96037, 73877), 33686, (0, 11, 33, 40), (55, 35, 46, 152)⟩,
  ⟨(-6303876220, 1157305760, 5834207721, 1634841295), 12607752440, (32768, 71551, 95862, 74034), 33677, (0, 33, 40, 41), (29, 46, 105, 34)⟩,
  ⟨(273088707347, -521028895327, 433780183136, -158417679492), 1122994589640, (81472, 35129, 90850, 56291), 33629, (3, 21, 25, 39), (64, 33, 32, 66)⟩,
  ⟨(-782725336, -1873811577, -154099621, 1360216023), 3747623154, (51848, 32768, 62841, 89322), 33594, (1, 14, 18, 37), (7, 52, 17, 65)⟩,
  ⟨(96076713, -898207374, 188279055, 728911445), 1796414748, (69041, 32768, 72404, 92127), 33588, (1, 14, 34, 38), (10, 74, 17, 132)⟩,
  ⟨(-65758750887, -77953708307, 3720760921, -104920796694), 290731986765, (50712, 47963, 66374, 41885), 33575, (5, 13, 19, 37), (53, 6, 18, 129)⟩,
  ⟨(57347106114, -93065438949, 97547824858, 32819813770), 212704609180, (83205, 36861, 95591, 75648), 33495, (3, 9, 17, 39), (20, 32, 50, 56)⟩,
  ⟨(-23747882402, -393690437472, 152091409597, 529839324372), 1034435987662, (64031, 40594, 75171, 99103), 33491, (7, 14, 34, 35), (10, 69, 58, 132)⟩,
  ⟨(-719675663870, 297057984127, 1096337276094, 979961770538), 2628825216505, (47594, 72941, 92867, 89966), 33472, (30, 33, 35, 40), (29, 61, 106, 67)⟩,
  ⟨(1348453648, -2103204475, 2545197142, 678569514), 5090394284, (82896, 38458, 98304, 74272), 33468, (2, 17, 21, 39), (32, 100, 73, 115)⟩,
  ⟨(-1193927239852, 163840872137, 943343565610, 1279809258444), 3137377362943, (40596, 68958, 85241, 92269), 33463, (24, 33, 35, 41), (29, 30, 105, 98)⟩,
  ⟨(-95752423039, -100581389930, 17928312216, 175546010601), 353010339198, (47759, 46863, 68864, 98125), 33400, (4, 18, 29, 35), (16, 84, 81, 28)⟩,
  ⟨(-1154374033, 205702811, 1061061470, 262151062), 2308748066, (32768, 71375, 95655, 72977), 33367, (0, 11, 40, 41), (79, 35, 99, 34)⟩,
  ⟨(84419174, -203770420, 104234166, -71430151), 407540840, (79111, 32768, 82297, 54049), 33367, (1, 3, 25, 38), (33, 63, 71, 66)⟩,
  ⟨(2661001647, -5061966400, 4883987860, -6588536516), 19454145887, (74500, 48483, 81988, 43340), 33305, (16, 25, 28, 39), (49, 21, 80, 135)⟩,
  ⟨(465242679204, -996088105455, 527069366483, -701096713250), 2595761361739, (77282, 40387, 78843, 47835), 33273, (25, 28, 38, 39), (8, 33, 48, 63)⟩,
  ⟨(277126731040, -473543860037, 330408562275, 265752215500), 1061554371220, (82644, 36301, 85934, 81942), 33256, (3, 9, 38, 39), (13, 33, 40, 71)⟩,
  ⟨(-1379264019, -621641080, 77887563, 936630246), 2758528038, (32768, 50767, 67386, 87788), 33250, (0, 15, 37, 41), (11, 77, 85, 70)⟩,
  ⟨(-229467303, -506594319, -38136752, 359360241), 1013188638, (50693, 32768, 63069, 88780), 33232, (1, 4, 18, 37), (28, 37, 60, 65)⟩,
  ⟨(-339744901406, -410905033691, 18526495633, -505335552657), 1441755544500, (50092, 46858, 66378, 42565), 33121, (13, 19, 32, 37), (86, 97, 39, 134)⟩,
  ⟨(-521100461, 459344909, 2704090076, 1943164597), 5408180152, (59221, 71102, 98304, 89083), 33081, (2, 26, 35, 40), (61, 25, 95, 72)⟩,
  ⟨(-6319610413, 1134336397, 6700401604, 1630139651), 13400803208, (34630, 71083, 98304, 73508), 33032, (2, 11, 33, 40), (34, 106, 114, 152)⟩,
  ⟨(29330464918, -55693959215, 57703718466, 15844268026), 120236559380, (81522, 35179, 96987, 74172), 32944, (3, 9, 17, 21), (115, 32, 87, 40)⟩,
  ⟨(-575024478, -565951725, 22041679, 207176145), 1150048956, (32768, 33285, 66792, 77342), 32887, (0, 4, 31, 37), (60, 117, 70, 154)⟩,
  ⟨(-364512238967, -1263867232860, 491868931636, 1857235335471), 3544773903853, (58796, 42169, 74629, 99872), 32883, (7, 14, 18, 35), (7, 81, 41, 109)⟩,
  ⟨(2462454923, -1046338275, 11750248924, -5458968228), 23500497848, (72403, 62618, 98304, 50312), 32881, (2, 27, 39, 40), (15, 25, 119, 78)⟩,
  ⟨(-6042133200, -6141933483, 212671387, 2197039953), 12283866966, (33300, 32768, 66670, 77257), 32834, (1, 4, 31, 37), (57, 103, 52, 138)⟩,
  ⟨(-255565404878, 145819834887, 710776456718, 554412364826), 1510106451441, (54444, 71864, 96382, 89596), 32825, (26, 30, 35, 40), (42, 54, 95, 89)⟩,
  ⟨(19085539884, -47609233936, 48911011993, 74478381976), 159859093275, (73360, 46018, 85587, 96069), 32715, (9, 17, 34, 35), (69, 19, 20, 101)⟩,
  ⟨(610686915, -1857763651, 780215448, -755920087), 3715527302, (76307, 32768, 79297, 52202), 32676, (1, 25, 28, 38), (49, 68, 47, 172)⟩,
  ⟨(860865932528, -1556167232885, 1597356993307, -654688051026), 3837218340793, (80238, 38958, 92817, 54354), 32563, (21, 22, 25, 39), (80, 36, 100, 159)⟩,
  ⟨(-25963197, -62846369, -1879433, 45803394), 125692738, (51998, 32768, 64556, 89417), 32538, (1, 4, 14, 18), (109, 37, 52, 151)⟩,
  ⟨(65173034, -157314220, 120812884, -41228939), 314628440, (79111, 32768, 90700, 56948), 32522, (1, 3, 21, 25), (36, 159, 47, 87)⟩,
  ⟨(-153936755410, 42102907656, 229763121952, 224262406744), 565340916135, (47691, 70416, 92170, 91533), 32519, (6, 30, 33, 35), (42, 98, 89, 175)⟩,
  ⟨(76178688, -2056718799, 226320165, -1007001430), 4113437598, (66749, 32768, 69141, 49492), 32516, (1, 19, 28, 38), (9, 63, 31, 176)⟩,
  ⟨(323659617899, -907494064120, 955685333790, 1453194091569), 3081052545779, (72420, 46233, 85864, 96446), 32477, (7, 17, 34, 35), (62, 41, 88, 101)⟩,
  ⟨(-2332146495, -1709814004, 102051245, 1335482870), 4664292990, (32768, 41512, 66969, 84300), 32386, (0, 4, 15, 37), (75, 51, 57, 162)⟩,
  ⟨(67031122, -161799260, 85571514, 85569097), 323598520, (79111, 32768, 82866, 82865), 32300, (1, 3, 9, 38), (50, 74, 47, 87)⟩,
  ⟨(-39543771, -71216229, 1023481892, 857260563), 2046963784, (64269, 63255, 98304, 92982), 32297, (2, 8, 26, 35), (92, 54, 23, 121)⟩,
  ⟨(1855929, -1832352, 4495892, 2666986), 8991784, (79062, 52181, 98304, 84974), 32295, (2, 8, 17, 39), (27, 43, 23, 148)⟩,
  ⟨(103798430, -322705021, 139815801, 208306313), 645410042, (76075, 32768, 79733, 86687), 32253, (1, 9, 34, 38), (19, 38, 71, 166)⟩,
  ⟨(-207166227976, -153223629950, 7860322974, 132294742449), 430282910715, (33982, 42198, 66733, 85685), 32252, (4, 15, 29, 37), (12, 28, 70, 113)⟩,
  ⟨(-739134970188, -43180675730, 854478808287, -1139785926682), 3184497327510, (50324, 64647, 83120, 42079), 32245, (5, 10, 20, 40), (108, 90, 26, 137)⟩,
  ⟨(-1612963683, -698944222, 181355351, -678433488), 3225927366, (32768, 51336, 69220, 51753), 32205, (0, 13, 37, 41), (18, 51, 104, 94)⟩,
  ⟨(112428563, -85273859, 462006052, -211583876), 924012104, (73510, 59487, 98304, 50529), 32177, (2, 16, 27, 39), (24, 59, 102, 178)⟩,
  ⟨(-6517045971411, 554677518540, 5221552382312, -2359460069824), 13844129324825, (34685, 68161, 90254, 54366), 32136, (11, 12, 40, 41), (91, 46, 99, 112)⟩,
  ⟨(115149222399, -210524723780, 224149316660, -219944719012), 735469528699, (75796, 46776, 85509, 45937), 32063, (16, 22, 25, 39), (64, 48, 102, 135)⟩,
  ⟨(-164586551311, -334670058219, 168313399082, 555362894691), 1051964565182, (55282, 44686, 76021, 100134), 32025, (4, 7, 18, 35), (58, 45, 84, 109)⟩,
  ⟨(-492010134698, -378443388335, 421062546653, 956446208636), 1795702032527, (47579, 51724, 80903, 100442), 31958, (7, 24, 29, 35), (83, 84, 107, 96)⟩,
  ⟨(-300654667446, -201758008050, 218797969933, 531580127504), 1016615881700, (46154, 52529, 79640, 99804), 31956, (15, 24, 29, 35), (82, 12, 30, 113)⟩,
  ⟨(-550441475738, -445091146185, 467706731253, 1090128237596), 2045919334037, (47903, 51278, 80517, 100455), 31913, (4, 7, 29, 35), (82, 45, 81, 96)⟩,
  ⟨(-537642800, -140407223, 167133243, 394204880), 1075285600, (32768, 56978, 75722, 89561), 31893, (0, 15, 24, 41), (30, 105, 51, 162)⟩,
  ⟨(-161916856, -314898171, -2158185, -141318503), 629796342, (48687, 32768, 65311, 50830), 31878, (1, 19, 32, 37), (53, 103, 31, 176)⟩,
  ⟨(70749038, -170773540, 161168156, 42817141), 341547080, (79111, 32768, 96460, 73751), 31835, (1, 3, 9, 21), (56, 116, 66, 71)⟩,
  ⟨(101857994139, -326969815135, 816570432147, 869862449315), 1888274864164, (69071, 54187, 93876, 95726), 31829, (7, 8, 17, 35), (27, 69, 93, 148)⟩,
  ⟨(-5976018331, 1944429221, 16570608387, 14170887543), 36030423479, (54666, 69072, 95676, 91311), 31788, (6, 26, 30, 35), (61, 67, 92, 156)⟩,
  ⟨(-205313431794, -42232275731, 483020705490, -534326721045), 1481227590379, (56452, 63667, 86906, 41895), 31764, (5, 20, 27, 40), (119, 15, 76, 137)⟩,
  ⟨(-1424003046048, 71601545274, 1038664882153, -976829097801), 3654858490734, (40001, 66819, 84160, 48020), 31750, (10, 12, 40, 41), (79, 26, 111, 108)⟩,
  ⟨(-6265375803, -12649279342, 70967893856, 67920876959), 149269502597, (62785, 59982, 96694, 95356), 31710, (6, 8, 26, 35), (72, 89, 93, 118)⟩,
  ⟨(-155187112149, -371499891583, 1583638893343, 1602771472587), 3415616387412, (62558, 58407, 95921, 96288), 31610, (6, 7, 8, 35), (88, 92, 107, 118)⟩,
  ⟨(-3940509987, -2602864074, 373524499, -1408758532), 7881019974, (32768, 43891, 68642, 53821), 31602, (0, 13, 23, 37), (97, 117, 77, 150)⟩,
  ⟨(-112350882, 53504998, 301084642, 195270649), 602169284, (53308, 71359, 98304, 86787), 31597, (2, 26, 30, 40), (61, 106, 54, 156)⟩,
  ⟨(-191263939126, -148857074395, 163667389231, 361939897892), 687349432439, (47299, 51343, 81141, 100045), 31569, (4, 7, 24, 29), (82, 113, 84, 164)⟩,
  ⟨(-1271927338666, -868962278073, 118359621848, -462622783742), 2571674415795, (33122, 43391, 68552, 53746), 31523, (13, 23, 32, 37), (110, 53, 94, 169)⟩,
  ⟨(-603258102198, -37802922576, 710997956000, 914664072052), 2015464891135, (45920, 64306, 88655, 95277), 31504, (6, 24, 33, 35), (44, 67, 107, 175)⟩,
  ⟨(-2967413492, -27624265, 2025925019, -1011426322), 5934826984, (32768, 65230, 87907, 54367), 31387, (0, 11, 12, 41), (79, 111, 46, 136)⟩,
  ⟨(1389136231, -2021824094, 3623921310, -1236821418), 7247842620, (78096, 47254, 98304, 54352), 31327, (2, 21, 22, 39), (64, 102, 43, 171)⟩,
  ⟨(1962744442, -6343400285, 6436029126, 9050041105), 20046813329, (71952, 44798, 86576, 95121), 31288, (7, 9, 17, 34), (62, 69, 166, 174)⟩,
  ⟨(146329697, -192153998, 429766630, -167925926), 859533260, (76693, 50885, 98304, 52732), 31193, (2, 16, 22, 39), (80, 100, 78, 158)⟩,
  ⟨(-1062069808, -1495120479, 32740107, -509585195), 2990240958, (42259, 32768, 66253, 54367), 31188, (1, 31, 32, 37), (110, 86, 60, 145)⟩,
  ⟨(-888407789, -295406862, 221416378, -392854609), 1776815578, (32768, 54640, 73702, 51045), 31177, (0, 10, 13, 41), (22, 77, 111, 150)⟩,
  ⟨(-10111238, 120208, 6927327, 5531447), 20222476, (32768, 65925, 87985, 83462), 31112, (0, 24, 33, 41), (44, 35, 85, 153)⟩,
  ⟨(-1001693269, 276207559, 1512076787, 747070060), 3024153574, (43828, 71521, 98304, 81725), 31077, (2, 30, 33, 40), (42, 55, 95, 181)⟩,
  ⟨(-1525314972674, -873237555359, 2169619428849, 3273429116124), 6384372855559, (49878, 56572, 87807, 99137), 31051, (6, 7, 24, 35), (82, 98, 93, 183)⟩,
  ⟨(-59922971536, 1175138922, 55570504197, -53475015971), 181593455214, (43910, 65960, 85591, 46237), 31000, (10, 12, 20, 40), (112, 76, 91, 180)⟩,
  ⟨(-32878525979, -105832430787, 43012159477, 135089875890), 273799260046, (57666, 40204, 75831, 97870), 30992, (4, 7, 14, 18), (58, 65, 81, 151)⟩,
  ⟨(-1043233225471, -854136263514, 84790783565, -379948147313), 2229110037837, (34864, 40424, 68028, 54365), 30986, (23, 31, 32, 37), (103, 97, 117, 179)⟩,
  ⟨(-888184770, -69718887, 524612174, -343909545), 1776369540, (32768, 62963, 84890, 52848), 30889, (0, 10, 12, 41), (91, 99, 104, 136)⟩,
  ⟨(-78070949636, 5404752168, 85253224074, -32175014547), 188781478372, (38433, 67412, 95131, 54366), 30768, (11, 12, 20, 40), (108, 114, 79, 182)⟩,
  ⟨(-39303741386, -28920545660, 30213685424, 64342491019), 128292264361, (45458, 50762, 80970, 98404), 30444, (4, 15, 24, 29), (83, 96, 75, 162)⟩,
  ⟨(-4371150884, 284382328, 5723865930, -1758839459), 11447731860, (40512, 67164, 98304, 55466), 30302, (2, 11, 20, 40), (112, 119, 55, 182)⟩,
  ⟨(94616930, -303259005, 305715926, 85475758), 611431852, (75677, 33031, 98304, 74697), 30018, (2, 9, 17, 21), (56, 43, 116, 123)⟩,
  ⟨(350890, -1178196, 1178196, 328807), 2356392, (75294, 32768, 98304, 74680), 29880, (1, 2, 9, 21), (115, 87, 171, 123)⟩,
  ⟨(-414615678, -336548537, 29261870, -27132369), 829231356, (32768, 38937, 67848, 63391), 29733, (0, 23, 31, 37), (110, 57, 94, 154)⟩,
  ⟨(-10463312129, -20307090058, 75634083478, 67086455587), 153842699197, (61078, 56885, 97755, 94114), 29687, (6, 7, 8, 26), (121, 92, 133, 93)⟩,
  ⟨(-986879940, -181302280, 3918390906, -2028026555), 7836781812, (57283, 64019, 98304, 48576), 29546, (2, 20, 27, 40), (90, 59, 114, 178)⟩,
  ⟨(579126143596, 738747226134, 873278486207, 1488700944530), 13985082902742, (68249, 68997, 69628, 72512), 29325, (35, 36, 39, 40), (2, 25, 124, 122)⟩,
  ⟨(-81208675, -155589757, 553249700, 470605563), 1106499400, (60726, 56320, 98304, 93409), 29117, (2, 7, 8, 26), (118, 72, 133, 148)⟩,
  ⟨(610192400276, -164543623234, 192061633236, 1283590154246), 9871064029925, (69587, 64443, 66811, 74058), 28955, (35, 36, 38, 39), (0, 13, 120, 126)⟩,
  ⟨(13190, -53041, 53041, 16281), 106082, (73684, 32768, 98304, 75594), 28944, (1, 2, 9, 17), (115, 174, 173, 116)⟩,
  ⟨(-1270229377173, 2294717854587, 1316439905821, 4137879816671), 35126214313802, (63166, 69817, 67992, 73256), 28907, (35, 36, 40, 41), (14, 29, 128, 120)⟩,
  ⟨(-131029, -116759, 131029, 41248), 262058, (32768, 36336, 98304, 75851), 28754, (0, 2, 4, 23), (130, 154, 127, 131)⟩,
  ⟨(-27726915617, -1528484761427, -1034549351732, 4245957828093), 26590044931650, (65467, 61768, 62986, 76000), 28724, (35, 36, 37, 38), (1, 5, 122, 128)⟩,
  ⟨(-35972, -31858, 35972, 10937), 71944, (32768, 36515, 98304, 75498), 28605, (0, 2, 11, 23), (167, 170, 125, 152)⟩,
  ⟨(-1764723158941, 58468154683, -615581465697, 3967742289527), 26532782844924, (61177, 65680, 64015, 75336), 28542, (35, 36, 37, 41), (14, 11, 124, 126)⟩,
  ⟨(-117366702528, -160184713741, 106699763575, -200893481213), 561823114874, (51845, 46850, 77982, 42102), 28541, (5, 10, 13, 19), (134, 39, 140, 22)⟩,
  ⟨(-385117927, -364827729, 395163815, 120006976), 790327630, (33601, 35283, 98304, 75487), 28530, (2, 4, 23, 31), (154, 167, 138, 125)⟩,
  ⟨(-217714, -183973, 217714, 77048), 435428, (32768, 37846, 98304, 77132), 28462, (0, 2, 4, 24), (164, 162, 153, 125)⟩,
  ⟨(-25963046, -230060598, 100131691, 181914614), 460121196, (61838, 32768, 79797, 91446), 28396, (1, 7, 14, 34), (41, 38, 166, 151)⟩,
  ⟨(-15209657, -23698359, 80090570, 67122884), 160181140, (59313, 55840, 98304, 92998), 28370, (2, 6, 7, 26), (118, 121, 156, 183)⟩,
  ⟨(-19482314102, -26773980764, 17903930901, -32739497003), 92303936714, (51703, 46526, 78247, 42290), 28329, (10, 13, 19, 32), (53, 157, 169, 129)⟩,
  ⟨(49387110, -299533531, 297721180, -271793219), 914461937, (69075, 44069, 86872, 46057), 28249, (16, 22, 25, 28), (172, 48, 165, 80)⟩,
  ⟨(-165830056, -40452184, 114961226, -56517883), 331660112, (32768, 57542, 88252, 54368), 28081, (0, 10, 11, 12), (177, 99, 111, 170)⟩,
  ⟨(-102740270619, -110515481092, 199782916641, -216490480907), 605632566036, (54418, 53577, 87154, 42109), 28079, (5, 10, 20, 27), (146, 90, 139, 76)⟩,
  ⟨(-1048152, -1172641, 1172641, 339915), 2345282, (36246, 32768, 98304, 75034), 27913, (1, 2, 4, 31), (130, 60, 145, 168)⟩,
  ⟨(-92335964419, -116345074147, 183258608356, -199834301962), 559105600606, (54712, 51898, 87016, 42112), 27811, (5, 10, 16, 27), (146, 24, 137, 144)⟩,
  ⟨(-147277772502, -235252185911, 199823934884, -288505618657), 807153811720, (53577, 46434, 81760, 42111), 27783, (5, 10, 19, 28), (157, 9, 144, 129)⟩,
  ⟨(-926007, -1786528, 1786528, -733194), 3573056, (48551, 32768, 98304, 52087), 27667, (1, 2, 28, 32), (142, 176, 145, 143)⟩,
  ⟨(-175024821, -335702840, 337958012, -139985634), 675916024, (48565, 32986, 98304, 51963), 27620, (2, 22, 28, 32), (160, 141, 149, 143)⟩,
  ⟨(-31275, -61724, 61724, -25250), 123448, (48932, 32768, 98304, 52131), 27563, (1, 2, 22, 28), (142, 172, 141, 171)⟩,
  ⟨(-286983781932, -482690188771, 544282920718, -635752640651), 1779096083408, (54964, 47755, 85585, 42116), 27538, (5, 10, 16, 28), (165, 21, 140, 139)⟩,
  ⟨(-369460, -571641, 571641, -194729), 1143282, (44357, 32768, 98304, 54373), 27496, (1, 2, 31, 32), (147, 103, 141, 138)⟩,
  ⟨(-39423265462, -47857174636, 78736348948, -78354178051), 226121672288, (54110, 51665, 88355, 42826), 27209, (10, 16, 20, 27), (178, 137, 139, 161)⟩,
  ⟨(-458959930, -590470539, 637992429, -217346741), 1275984858, (41963, 35208, 98304, 54372), 27177, (2, 10, 31, 32), (179, 145, 149, 155)⟩,
  ⟨(18008579, -308231185, 622623117, 462423715), 1245246234, (66483, 49314, 98304, 89872), 27177, (2, 7, 8, 17), (88, 73, 173, 121)⟩,
  ⟨(-380775278, -646625500, 709207409, -317357199), 1418414818, (47942, 35659, 98304, 50872), 27102, (2, 10, 22, 32), (160, 142, 147, 158)⟩,
  ⟨(-285514444, -176433495, 134550620, -100152350), 571028888, (32768, 45287, 80978, 54041), 27037, (0, 10, 13, 23), (169, 94, 170, 104)⟩,
  ⟨(-251092007, -1012287047, 449977385, 781816066), 2024574094, (57408, 32768, 80101, 90843), 27016, (1, 4, 7, 14), (109, 132, 65, 168)⟩,
  ⟨(-23123, -8242, 23123, 8302), 46246, (32768, 53856, 98304, 77300), 26999, (0, 2, 11, 33), (55, 34, 153, 127)⟩,
  ⟨(-568694, -220943, 568694, 209988), 1137388, (32768, 52805, 98304, 77635), 26906, (0, 2, 24, 33), (181, 105, 152, 131)⟩,
  ⟨(-161869319, -148199089, 131731655, 51499712), 323738638, (32768, 35535, 92203, 75961), 26877, (0, 4, 23, 31), (130, 117, 57, 125)⟩,
  ⟨(-228609178, -247397403, 287100479, -87354833), 574200958, (39443, 37299, 98304, 55565), 26850, (2, 10, 11, 31), (163, 167, 147, 177)⟩,
  ⟨(-1625229, -684236, 4105573, 2987032), 8211146, (52564, 60074, 98304, 89376), 26580, (2, 6, 26, 30), (89, 95, 184, 133)⟩,
  ⟨(-65089345386, -104757723778, 85476656301, -106768984655), 318664864882, (52149, 43991, 83114, 43578), 26579, (10, 19, 28, 32), (176, 160, 134, 140)⟩,
  ⟨(-134496234, -218880187, 259578250, -121160411), 519156500, (48557, 37905, 98304, 50241), 26433, (2, 10, 16, 22), (165, 102, 149, 161)⟩,
  ⟨(-21639625, -484547927, 447842086, -165257289), 969095854, (64072, 32768, 95821, 54360), 26347, (1, 21, 22, 25), (64, 172, 66, 171)⟩,
  ⟨(-75970833363, -133481398484, 142795673384, -74799635626), 305025801590, (49213, 36856, 96216, 49465), 26346, (10, 22, 28, 32), (142, 157, 149, 165)⟩,
  ⟨(-63325414, -101130044, 122606996, -57622293), 245213992, (48611, 38507, 98304, 50135), 26265, (2, 10, 16, 20), (146, 178, 180, 158)⟩,
  ⟨(-616652378, -407474297, 380733002, 345184072), 1233304756, (32768, 43883, 85767, 83878), 26212, (0, 4, 15, 24), (113, 85, 131, 70)⟩,
  ⟨(-389586515227, -378903366966, 434213589695, -137327077643), 923750908000, (37896, 38654, 96341, 55793), 26187, (10, 11, 23, 31), (167, 179, 155, 170)⟩,
  ⟨(-14585762, -13480988, 16968639, 8247887), 33937278, (37369, 39502, 98304, 81463), 26167, (2, 4, 7, 24), (96, 183, 131, 168)⟩,
  ⟨(-7666769874, -13471589957, 14572580750, -8009153221), 31676392500, (49674, 37664, 95685, 48965), 26082, (10, 16, 22, 28), (135, 160, 144, 158)⟩,
  ⟨(1747150, -84113154, 59763559, 53015678), 168226308, (66216, 32768, 88818, 86189), 26050, (1, 7, 9, 34), (101, 74, 132, 174)⟩,
  ⟨(-34504931, -33162748, 37561235, 2267951), 75122470, (35434, 36605, 98304, 67514), 26049, (2, 11, 23, 31), (163, 130, 155, 127)⟩,
  ⟨(-852809, -1124657, 1124657, 422920), 2249314, (40688, 32768, 98304, 77858), 26025, (1, 2, 4, 7), (164, 151, 173, 138)⟩,
  ⟨(-154768087292, -113242234101, 85675627276, -59304641914), 328091284200, (34621, 42915, 82649, 53689), 26002, (10, 13, 23, 32), (97, 179, 134, 150)⟩,
  ⟨(-891076454, -552185090, 654583558, -253018553), 1782152908, (32768, 45230, 89607, 56231), 25962, (0, 10, 11, 23), (163, 127, 150, 136)⟩,
  ⟨(-185859, -793450, 793450, -270574), 1586900, (57860, 32768, 98304, 54361), 25906, (1, 2, 21, 22), (100, 159, 143, 116)⟩,
  ⟨(-4496385, -24784879, 22428370, -9599621), 49569758, (59591, 32768, 95188, 52844), 25721, (1, 22, 25, 28), (135, 63, 143, 159)⟩,
  ⟨(-13289, -1185765, 1185765, 528291), 2371530, (65168, 32768, 98304, 80135), 25581, (1, 2, 7, 17), (148, 174, 123, 168)⟩,
  ⟨(1758132, -423367160, 410280609, 197444499), 846734320, (65672, 32768, 97291, 80817), 25581, (1, 7, 9, 17), (101, 123, 173, 166)⟩,
  ⟨(-24985587594, -11692627056, 33754838436, 24956686656), 72197962253, (42855, 54922, 96176, 88189), 25355, (6, 24, 30, 33), (181, 67, 98, 184)⟩,
  ⟨(-209634684, -481167718, 270032905, -226719135), 962335436, (51259, 32768, 83925, 50096), 25259, (1, 19, 28, 32), (157, 141, 86, 68)⟩,
  ⟨(-88598058, -74808517, 114032473, -38861789), 228064946, (40076, 44039, 98304, 54368), 25151, (2, 10, 11, 12), (136, 182, 180, 155)⟩,
  ⟨(-115218770, -145652540, 353156348, -181896665), 706312696, (54845, 52021, 98304, 48658), 25128, (2, 16, 20, 27), (146, 119, 78, 161)⟩,
  ⟨(-395876789, -371105946, 345697105, -157532053), 924594144, (37475, 39231, 90039, 54369), 25023, (10, 23, 31, 32), (110, 147, 169, 163)⟩,
  ⟨(-1876096, -1648946, 2590739, -967962), 5181478, (41806, 44679, 98304, 53293), 24803, (2, 10, 12, 20), (108, 182, 161, 177)⟩,
  ⟨(-192662342, -104159369, 258248508, 156164222), 516497016, (41089, 52319, 98304, 85350), 24789, (2, 24, 30, 33), (175, 106, 153, 184)⟩,
  ⟨(-4545972, -2569448, 5909402, -2014051), 11818804, (40328, 51288, 98304, 54367), 24777, (2, 11, 12, 20), (112, 180, 114, 177)⟩,
  ⟨(-845123666, -641423084, 1252774727, 836125891), 2505549454, (43430, 48758, 98304, 87405), 24746, (2, 6, 7, 24), (107, 164, 184, 133)⟩,
  ⟨(-47722, -33607, 69528, 45711), 139056, (43044, 49697, 98304, 87079), 24715, (2, 6, 24, 30), (175, 181, 156, 183)⟩
]

set_option maxRecDepth 20000 in
private lemma cell1_ok : verifyCell ⟨1, by decide⟩ hs1 vs1 ctr1 = true := by
  decide

private def ctr2 : NVec4 := (73493, 77731, 39707, 65385)

private def hs2 : List HSData := [
  ⟨.base 0, (2, 0, 0, 0), 1⟩,
  ⟨.base 2, (0, 2, 0, 0), 1⟩,
  ⟨.base 5, (140, 140, 0, 0), 99⟩,
  ⟨.ball0, (1000, 1000, -1000, 1000), 1254⟩,
  ⟨.ball0, (1204, 0, -1072, 1184), 1255⟩,
  ⟨.ballA, (-602, 249, -941, -1640), 972⟩,
  ⟨.ball0, (291, -623, -1735, 719), 1254⟩,
  ⟨.ballA, (529, 731, -123, -1781), 884⟩,
  ⟨.ball0, (658, 1454, -153, 1195), 1254⟩,
  ⟨.ballA, (125, -319, -1228, -1541), 1034⟩,
  ⟨.ball0, (-955, 951, -1389, -502), 1254⟩,
  ⟨.ballA, (-620, 617, -901, -1557), 1025⟩,
  ⟨.ballA, (959, 397, -286, -1686), 944⟩,
  ⟨.ball0, (-1020, 488, -1565, -523), 1255⟩,
  ⟨.ball0, (-315, 34, -1824, 756), 1254⟩,
  ⟨.ballA, (603, 803, 72, -1728), 917⟩,
  ⟨.ball0, (89, 938, -1106, 1374), 1254⟩,
  ⟨.ballA, (-38, -52, -68, -1998), 748⟩,
  ⟨.ball0, (-438, 1518, -519, 1111), 1254⟩,
  ⟨.ball0, (957, -408, -1644, -465), 1255⟩,
  ⟨.ballA, (635, -271, -1090, -1528), 1042⟩,
  ⟨.ball0, (407, -660, -1762, -541), 1254⟩,
  ⟨.ballA, (257, -417, -1112, -1589), 1005⟩,
  ⟨.ball0, (-394, 161, -1381, 1383), 1255⟩,
  ⟨.ballA, (502, -90, -297, -1911), 802⟩,
  ⟨.ball0, (282, -424, -1397, 1337), 1254⟩,
  ⟨.ball0, (1533, 463, -566, 1056), 1254⟩,
  ⟨.ballA, (411, 992, -95, -1685), 944⟩,
  ⟨.ballA, (-304, 987, -325, -1682), 946⟩,
  ⟨.ball0, (-1022, 581, -1524, -543), 1254⟩,
  ⟨.ball0, (769, -230, -1247, 1342), 1255⟩,
  ⟨.ball0, (1522, 216, -665, 1093), 1255⟩,
  ⟨.ball0, (-25, -179, -1400, 1417), 1255⟩,
  ⟨.ballA, (986, -23, -512, -1663), 958⟩,
  ⟨.ball0, (-674, 776, -1137, 1284), 1254⟩,
  ⟨.aff 0, (-244, -311, 1644, 2291), 320⟩,
  ⟨.aff 1, (-1139, -1917, 2678, 218), 42⟩,
  ⟨.aff 3, (-1589, -1752, 92, 89), 113⟩,
  ⟨.aff 4, (790, -2252, 853, 254), 136⟩,
  ⟨.aff 5, (1479, -1007, 2324, -11), 152⟩,
  ⟨.aff 6, (-832, 790, 2858, -270), 157⟩,
  ⟨.aff 7, (-2362, 48, 1223, 175), 155⟩
]

private def vs2 : List VertData := [
  ⟨(444177355748, -549959179374, 635430009925, -6819778899674), 18174369169362, (67137, 63552, 67827, 40944), 40370, (17, 36, 39, 40), (69, 5, 2, 1)⟩,
  ⟨(518979560836, -1144158295118, -2828981620, -4822760320798), 12935618315159, (68165, 59739, 65521, 41102), 40104, (17, 36, 38, 39), (80, 6, 0, 3)⟩,
  ⟨(-61599538345, -13848633815, 2412603242, -311968512885), 837179068368, (60713, 64451, 65724, 41114), 40073, (17, 36, 37, 40), (7, 4, 0, 3)⟩,
  ⟨(239605071153, -1230336074069, -227387174000, -4460354907151), 12008187052764, (66843, 58821, 64295, 41193), 39898, (17, 36, 37, 38), (90, 23, 1, 2)⟩,
  ⟨(-220156491217, 11975803484, -23216703117, -832323816901), 2235701773884, (59082, 65887, 64855, 41137), 39605, (17, 37, 40, 41), (7, 15, 37, 2)⟩,
  ⟨(1267662932641, 1184972290626, 181915586312, -2858662249909), 7472522947722, (76653, 75928, 67131, 40464), 37236, (7, 17, 39, 40), (0, 20, 32, 8)⟩,
  ⟨(387420884600, -224212452178, -156984748156, -1094648958326), 2934118496669, (74189, 60528, 62029, 41086), 37220, (17, 24, 38, 39), (74, 1, 8, 23)⟩,
  ⟨(-487613700077, -5927184485, 12527931447, -1665747491723), 5646934863450, (59876, 65467, 65681, 46204), 37129, (36, 37, 40, 41), (4, 72, 86, 2)⟩,
  ⟨(248832070360, 210570052594, 21412610668, -532096740442), 1392069476563, (77250, 75449, 66544, 40485), 36874, (7, 17, 24, 39), (6, 58, 5, 156)⟩,
  ⟨(550568439918, 736748323947, 89568885202, 348651036431), 1820447948900, (85356, 92058, 68760, 78087), 36764, (2, 35, 39, 40), (69, 12, 10, 18)⟩,
  ⟨(101377591, 244704530, -587226, 112795958), 489409060, (79111, 98304, 65457, 80640), 36753, (1, 2, 35, 40), (9, 13, 38, 27)⟩,
  ⟨(-73098723, 302698508, -103860410, 192394896), 605397016, (57622, 98304, 54292, 86363), 36443, (1, 18, 35, 41), (22, 13, 41, 39)⟩,
  ⟨(424996357759, 496809610049, 28586055191, -311399922878), 1303563994880, (86902, 90512, 66973, 49880), 36430, (2, 15, 39, 40), (20, 9, 25, 33)⟩,
  ⟨(-559717926, 3554910895, -581794789, 1833531087), 7109821790, (60376, 98304, 60173, 82436), 36126, (1, 35, 40, 41), (72, 36, 11, 10)⟩,
  ⟨(-6043576188490, 3835160187083, -10093040850958, 10715590626575), 25744864807241, (50151, 75298, 39843, 92813), 36100, (34, 35, 37, 41), (86, 50, 22, 16)⟩,
  ⟨(-298166522523, 552757501937, -196271589379, -834608021953), 2223904055742, (56749, 81825, 59752, 40941), 36008, (17, 28, 40, 41), (36, 4, 44, 32)⟩,
  ⟨(-1849967103479, 1124224585105, -3501551067854, 3673093729425), 8625830955756, (51480, 74077, 38932, 93442), 35859, (23, 34, 35, 37), (14, 35, 70, 67)⟩,
  ⟨(2405256751967, -4010202693718, -11953005697126, 12236297086014), 28259080150779, (71114, 56235, 37815, 93913), 35851, (25, 35, 37, 38), (90, 59, 26, 24)⟩,
  ⟨(874875615572, 421211542354, -251605716781, 586913315886), 1832850526360, (96818, 80596, 56539, 86521), 35812, (2, 26, 35, 39), (21, 9, 31, 45)⟩,
  ⟨(12254444726842, 1738345633813, -5317052512030, 8957359247681), 25779267816233, (96689, 69955, 52019, 88307), 35717, (31, 35, 38, 39), (80, 29, 21, 28)⟩,
  ⟨(493744551329, 556440479649, 39201072676, -497887838648), 1753241365350, (83992, 86335, 67001, 46924), 35640, (7, 15, 39, 40), (12, 5, 34, 33)⟩,
  ⟨(210009098128, 45331612460, -84623441969, 150477614688), 438384141359, (96931, 72312, 52885, 88031), 35572, (26, 31, 35, 39), (19, 18, 30, 64)⟩,
  ⟨(-2397645197183, 5183979364588, -3885416074930, 5083706865216), 13224863271096, (53654, 91225, 46281, 90728), 35515, (18, 34, 35, 41), (14, 11, 43, 42)⟩,
  ⟨(123947448816, -289389844429, -370137590392, -692467201142), 1897135150914, (69817, 55539, 52749, 41614), 35232, (17, 24, 37, 38), (60, 3, 6, 87)⟩,
  ⟨(192822698951, -508265419674, -2240145111458, 2276742665242), 5138252155647, (67995, 59053, 36963, 94574), 35196, (25, 32, 35, 37), (35, 17, 95, 63)⟩,
  ⟨(21424395943, 36807861041, -1224756718, -19170293933), 82348646240, (82586, 94829, 64561, 50279), 34944, (2, 15, 27, 40), (34, 38, 12, 40)⟩,
  ⟨(404770208887, -261468983662, -995184372646, 1059443047590), 2417668238591, (76508, 58448, 38559, 94254), 34868, (25, 30, 35, 38), (46, 17, 82, 63)⟩,
  ⟨(67137987, 162057210, -37306148, 101191350), 324114420, (79111, 98304, 57992, 85996), 34844, (1, 2, 8, 35), (57, 39, 10, 105)⟩,
  ⟨(3184023734179, 237683292888, -1981367095026, 2829041000628), 7416075415588, (93673, 67636, 48026, 90536), 34801, (4, 31, 35, 38), (19, 46, 78, 64)⟩,
  ⟨(4724486875, 610526233, -2110562650, 2865869354), 9448973750, (98304, 69770, 50897, 85413), 34720, (0, 31, 38, 39), (19, 73, 30, 78)⟩,
  ⟨(242710399, 49728647, -100462604, 148443600), 485420798, (98304, 72249, 51972, 85577), 34698, (0, 26, 31, 39), (21, 29, 31, 135)⟩,
  ⟨(171354260, 70989622, -55414579, 97384050), 342708520, (98304, 79111, 54939, 84158), 34671, (0, 2, 26, 39), (18, 30, 77, 134)⟩,
  ⟨(-20157074805, 360164885176, -81360087230, -477904366559), 1259923536270, (64487, 84270, 61303, 40677), 34654, (7, 17, 28, 40), (15, 56, 5, 156)⟩,
  ⟨(45168644777, 40387390447, -3473371212, -29819801174), 120988332640, (90002, 87412, 63654, 49383), 34583, (2, 7, 15, 39), (20, 12, 52, 40)⟩,
  ⟨(60680203416, 107309650252, -4110839121, -60840364101), 248196271060, (81558, 93871, 64450, 49471), 34513, (7, 15, 27, 40), (25, 56, 20, 40)⟩,
  ⟨(-438354331679, -24118648170, -2866057165129, 2914627113950), 6500225297181, (61116, 65292, 36640, 94921), 34494, (23, 32, 35, 37), (24, 16, 89, 76)⟩,
  ⟨(-67864582, 230682315, -67510973, -98808321), 461364630, (55895, 98304, 55946, 51500), 34491, (1, 28, 40, 41), (15, 13, 54, 55)⟩,
  ⟨(-1158921492719, 530934513115, -1283286145331, -1989581020217), 5453043794542, (51607, 71916, 50113, 41624), 34436, (5, 17, 37, 41), (4, 83, 44, 102)⟩,
  ⟨(70200010, 169448300, -14602395, -72158009), 338896600, (79111, 98304, 62712, 51582), 34274, (1, 2, 27, 40), (25, 55, 10, 124)⟩,
  ⟨(229118805, 1554038418, -680004784, 1157452374), 3108076836, (70367, 98304, 51197, 89941), 34179, (1, 8, 18, 35), (49, 11, 27, 62)⟩,
  ⟨(4961562908, 8176914796, -574790323, -4352461283), 18579665440, (83036, 94378, 63508, 50183), 34146, (2, 7, 15, 27), (34, 25, 121, 33)⟩,
  ⟨(-119104965, 223352617, -191162962, 62770062), 446705234, (48062, 98304, 37490, 74744), 34097, (1, 10, 18, 41), (43, 11, 54, 100)⟩,
  ⟨(-458727581834, 1520095342804, -1210488220606, 1569764824932), 3892088929995, (57811, 91131, 45153, 91968), 34087, (16, 18, 34, 35), (22, 67, 49, 123)⟩,
  ⟨(-2277095011401, 4084671625005, -3677109534154, 1277330814774), 8393487659642, (47756, 97428, 36825, 75509), 34078, (10, 18, 34, 41), (22, 51, 41, 100)⟩,
  ⟨(-256164512666, 258405847611, -272751667585, -476742412776), 1293282889743, (52555, 78630, 51714, 41377), 34057, (5, 17, 28, 41), (15, 65, 37, 157)⟩,
  ⟨(6030813095, 4308796405, -2751783127, 5244181553), 14621670000, (92566, 84848, 53202, 89041), 34005, (2, 3, 26, 35), (68, 18, 57, 134)⟩,
  ⟨(752841379078, -86964125003, -845350679054, 1009796723505), 2397001011144, (86119, 63158, 42423, 93144), 33910, (4, 30, 35, 38), (26, 28, 108, 79)⟩,
  ⟨(-348664154958, 248529510669, -575887189136, 162983277254), 1030233495026, (43356, 81345, 28902, 75903), 33894, (13, 14, 34, 41), (50, 51, 48, 53)⟩,
  ⟨(-2069455636554, 1352779757577, -3412038221498, 925201778682), 6077259408268, (43219, 80124, 28741, 75513), 33841, (13, 14, 37, 41), (50, 98, 47, 122)⟩,
  ⟨(215225177410, 1336385568466, -653485716388, 1057353025458), 2749795026567, (70665, 97386, 49961, 90735), 33797, (8, 16, 18, 35), (42, 39, 71, 62)⟩,
  ⟨(-157519246110, 103030096626, -260661891346, 87267004365), 474117010307, (43762, 79777, 29505, 77598), 33786, (14, 34, 37, 41), (14, 48, 47, 70)⟩,
  ⟨(-718926089553, 532335708363, -1186708662440, 332714201043), 2132489216413, (43441, 81895, 29065, 75761), 33786, (10, 13, 34, 41), (47, 43, 66, 53)⟩,
  ⟨(219472057243, 163635182855, -33969937980, -134209100788), 541767814280, (92084, 85330, 61426, 49301), 33674, (2, 7, 12, 39), (58, 77, 33, 132)⟩,
  ⟨(-333208194186, 253955853180, -569593125122, 157677068535), 1014144181987, (44003, 81947, 28727, 75725), 33392, (10, 13, 14, 34), (47, 144, 51, 159)⟩,
  ⟨(-3348055048, 6930432297, -4663414519, -2222724599), 13860864594, (49705, 98304, 43486, 55026), 33330, (1, 10, 28, 41), (61, 36, 41, 149)⟩,
  ⟨(94498168, 1903132303, -380855609, -967469741), 3806264606, (67163, 98304, 58978, 48878), 33277, (1, 27, 28, 40), (56, 36, 38, 129)⟩,
  ⟨(19790613521, 431161381238, -86176417984, -391745254273), 1169622399898, (66644, 89694, 60707, 43585), 33263, (7, 27, 28, 40), (55, 32, 34, 152)⟩,
  ⟨(1645086671, 2317479904, -1043254582, 2021130236), 5603629500, (84775, 92639, 53334, 89173), 33185, (2, 3, 8, 35), (71, 27, 45, 105)⟩,
  ⟨(334745073265, 169007434981, -70975450268, -361604270908), 1078474847962, (85877, 75806, 61223, 43562), 33112, (7, 12, 24, 39), (85, 8, 52, 183)⟩,
  ⟨(839204458037, -1321169311765, -3809449498894, 2521131818430), 7567293171093, (72803, 54094, 32544, 87370), 33075, (6, 25, 37, 38), (17, 99, 82, 95)⟩,
  ⟨(882865757085, -1675415238298, -2956277302858, -2939450831042), 8839514811189, (72081, 53114, 43618, 43742), 33043, (22, 24, 37, 38), (23, 92, 106, 87)⟩,
  ⟨(-1004970446024, 1936496248422, -1401728700998, -697997093239), 4065989166423, (49337, 96748, 42942, 54285), 32848, (10, 11, 28, 41), (65, 54, 94, 149)⟩,
  ⟨(75010330, 433094131, -220597708, 312445998), 866188262, (71211, 98304, 48845, 89175), 32834, (1, 8, 16, 18), (49, 123, 39, 97)⟩,
  ⟨(130640944809, 7120882966, -442369463810, 475776229122), 1027052991497, (73872, 65990, 37308, 95895), 32783, (25, 30, 32, 35), (75, 24, 26, 148)⟩,
  ⟨(25681714471, 10522631857, -19491113989, 27547146037), 67275760420, (90553, 75786, 46548, 92370), 32710, (4, 26, 31, 35), (21, 28, 68, 128)⟩,
  ⟨(-135546403196, 150507051242, -156263885386, -214965848565), 636485080533, (51579, 81033, 49446, 43401), 32702, (5, 11, 28, 41), (61, 44, 88, 175)⟩,
  ⟨(-10466083557, 7724937849, -17059270222, 3561026199), 31299216011, (43621, 81710, 29816, 72992), 32619, (10, 13, 29, 41), (98, 94, 51, 168)⟩,
  ⟨(-238754107640, 600395767993, -1243186705396, 1371600639797), 3031472001632, (60374, 78515, 38660, 95188), 32591, (16, 23, 34, 35), (16, 42, 76, 141)⟩,
  ⟨(156000324579, 72468368563, -124433075926, 174487426243), 420565546500, (89845, 76828, 46145, 92726), 32516, (3, 4, 26, 35), (64, 45, 79, 128)⟩,
  ⟨(579126143596, 738747226134, 873278486207, 1488700944530), 13985082902742, (68249, 68997, 69628, 72512), 32403, (35, 36, 39, 40), (0, 9, 72, 80)⟩,
  ⟨(-552141990282, 326748621288, -1181464612826, 702651018001), 2289656940563, (49732, 74888, 31719, 85647), 32360, (14, 23, 34, 37), (16, 50, 89, 141)⟩,
  ⟨(330777047594, 866366642753, -515729301107, 803169294897), 2006413306500, (76340, 93834, 48690, 91770), 32317, (3, 8, 16, 35), (49, 81, 57, 97)⟩,
  ⟨(-1270229377173, 2294717854587, 1316439905821, 4137879816671), 35126214313802, (63166, 69817, 67992, 73256), 32116, (35, 36, 40, 41), (7, 13, 86, 69)⟩,
  ⟨(7432522068, -66788403, -3800907166, -2985354733), 14865044136, (98304, 65241, 48778, 52374), 31989, (0, 33, 38, 39), (74, 29, 84, 91)⟩,
  ⟨(2300310708594, -185144324412, -1162966891352, -1703912385506), 5951367456789, (90866, 63497, 52729, 46772), 31947, (24, 33, 38, 39), (73, 6, 85, 114)⟩,
  ⟨(223632788952, 192776106483, -709273407810, 789520288031), 1650705399434, (74414, 73189, 37376, 96881), 31922, (16, 30, 32, 35), (63, 76, 81, 150)⟩,
  ⟨(127110262872, 318238853995, -1092552817778, 1192324112375), 2517095379034, (68845, 73821, 37089, 96579), 31889, (16, 23, 32, 35), (35, 75, 67, 145)⟩,
  ⟨(274498700, 113720890, -90025929, -109202066), 548997400, (98304, 79111, 54789, 52500), 31798, (0, 2, 12, 39), (52, 84, 31, 140)⟩,
  ⟨(51931296, 1260047, -35654164, 25000852), 103862592, (98304, 66331, 43038, 81311), 31787, (0, 4, 31, 38), (28, 29, 93, 136)⟩,
  ⟨(83346313098, 56142421397, -134841796354, 161842333905), 347825251000, (81239, 76114, 40129, 96029), 31654, (3, 4, 30, 35), (46, 81, 68, 169)⟩,
  ⟨(610192400276, -164543623234, 192061633236, 1283590154246), 9871064029925, (69587, 64443, 66811, 74058), 31651, (35, 36, 38, 39), (1, 19, 69, 90)⟩,
  ⟨(689847351792, 504341239063, -1195867993352, 1425021623019), 3042327119000, (80396, 76400, 39775, 96232), 31640, (3, 16, 30, 35), (75, 79, 71, 160)⟩,
  ⟨(133366015761, -89546558425, -319798662430, 205682859498), 635832274147, (79282, 56306, 32573, 86735), 31613, (6, 25, 30, 38), (26, 108, 59, 151)⟩,
  ⟨(-4050605580353, 2429104764565, -5995418190557, -2214724181519), 12671962778554, (44587, 78098, 34529, 54082), 31470, (5, 29, 37, 41), (98, 37, 88, 107)⟩,
  ⟨(2017085996, 404177626, -848822793, -872272274), 4034171992, (98304, 72101, 51746, 51365), 31447, (0, 12, 33, 39), (85, 73, 77, 140)⟩,
  ⟨(21706931042, 3407839726, -8807843702, -16232278556), 55144623077, (91333, 69586, 55068, 46244), 31418, (12, 24, 33, 39), (74, 84, 58, 184)⟩,
  ⟨(-1764723158941, 58468154683, -615581465697, 3967742289527), 26532782844924, (61177, 65680, 64015, 75336), 31416, (35, 36, 37, 41), (7, 14, 72, 90)⟩,
  ⟨(1716879423, -85288174172, -290057604383, -297749887201), 827537346744, (65671, 58781, 42565, 41955), 31266, (17, 22, 24, 37), (60, 23, 101, 130)⟩,
  ⟨(-739278845801, 514062919810, -1091135356124, -415282091348), 2346572563918, (44889, 79892, 35062, 53937), 31235, (5, 11, 29, 41), (94, 83, 65, 172)⟩,
  ⟨(-41804634494, -6016317054, -313455663892, 218373668117), 597924664371, (60953, 64876, 31179, 89471), 31233, (14, 23, 32, 37), (35, 96, 70, 145)⟩,
  ⟨(-27726915617, -1528484761427, -1034549351732, 4245957828093), 26590044931650, (65467, 61768, 62986, 76000), 31209, (35, 36, 37, 38), (3, 17, 80, 86)⟩,
  ⟨(2048978175, -242540099, -1700281852, -619018023), 4097956350, (98304, 61657, 38344, 55636), 31161, (0, 19, 33, 38), (104, 73, 93, 137)⟩,
  ⟨(1845126710067, -2965962533228, -6859296217400, -2179599471115), 12738233725566, (75028, 50276, 30246, 54322), 31115, (21, 22, 37, 38), (60, 99, 109, 118)⟩,
  ⟨(3014619936, -348742633, -2947030636, 656990536), 6029239872, (98304, 61745, 33502, 72677), 31031, (0, 4, 19, 38), (103, 91, 78, 138)⟩,
  ⟨(-777070621821, 606738822660, -1147230820379, -428133462708), 2494049180203, (45116, 81479, 35390, 54285), 31004, (10, 11, 29, 41), (88, 66, 61, 171)⟩,
  ⟨(19418797546, -112154083890, -679333357257, 407941920105), 1234032280499, (66567, 59579, 29458, 87200), 30960, (6, 25, 32, 37), (24, 96, 59, 117)⟩,
  ⟨(9601401714, -90622256106, -590188222565, 346770807893), 1062644697351, (66128, 59947, 29137, 86922), 30761, (6, 14, 32, 37), (89, 95, 131, 117)⟩,
  ⟨(80648896, 298763500, -172921849, 196964613), 597527000, (74381, 98304, 46570, 87138), 30732, (1, 3, 8, 16), (71, 62, 147, 105)⟩,
  ⟨(-35217488943, 22092290025, -55157471707, -1491076755), 106616854676, (43888, 79115, 31631, 64619), 30729, (13, 29, 37, 41), (83, 48, 66, 107)⟩,
  ⟨(1923500836147, -2947226996200, -7656963176424, 427707540965), 12749771925838, (75423, 50386, 26177, 67734), 30662, (6, 21, 37, 38), (92, 59, 115, 131)⟩,
  ⟨(-135904383, 385410747, -379304518, 112665594), 770821494, (53981, 98304, 33287, 75114), 30659, (1, 10, 18, 34), (43, 123, 125, 41)⟩,
  ⟨(-1320500553, -1328975036, -9410558879, -8817426649), 24567409320, (62013, 61990, 40432, 42014), 30437, (9, 17, 22, 37), (87, 118, 102, 130)⟩,
  ⟨(-135447788415, -120295223074, -907934435932, -847935000125), 2362721977878, (61779, 62199, 40352, 42016), 30416, (5, 9, 17, 37), (101, 37, 127, 133)⟩,
  ⟨(3349458369449, -947047852486, -4654652487676, 1347204687393), 8460259516716, (91482, 58199, 29479, 75971), 30363, (4, 6, 19, 38), (115, 93, 108, 167)⟩,
  ⟨(1676699896155, -298868414537, -1569850765096, -630067790325), 3665622545076, (95512, 60192, 37469, 54271), 30350, (19, 20, 33, 38), (114, 91, 112, 161)⟩,
  ⟨(377725, 911750, -459890, 537304), 1823500, (79111, 98304, 49007, 84846), 30334, (1, 2, 3, 8), (57, 97, 27, 126)⟩,
  ⟨(416552343373, -284241775287, -682314718102, -541487587414), 1835562701962, (80408, 55387, 41174, 46203), 30287, (20, 22, 24, 38), (60, 114, 112, 182)⟩,
  ⟨(-137854906853, 78297808045, -235186477933, -80790210615), 469435421062, (46290, 76466, 32702, 54257), 30243, (5, 13, 29, 37), (98, 83, 127, 173)⟩,
  ⟨(256207473230, -82130337071, -385756808390, 158562226965), 724894639912, (88699, 58110, 30660, 79871), 30134, (4, 6, 30, 38), (82, 46, 103, 169)⟩,
  ⟨(857645502555, -742049863388, -1972008844664, -635492961619), 3713952078078, (80669, 52441, 30738, 54322), 29901, (19, 21, 22, 38), (92, 112, 115, 165)⟩,
  ⟨(105051659405, 201501398164, -298713718613, -74509771607), 433509374340, (81417, 95998, 20377, 54271), 29896, (2, 10, 11, 19), (143, 111, 113, 120)⟩,
  ⟨(135228188909, 259046692729, -384046665296, -96007111063), 557560438680, (81430, 95984, 20394, 54251), 29888, (2, 11, 19, 20), (142, 154, 116, 110)⟩,
  ⟨(534738378992, -455507131618, -1214788854598, -394278842151), 2293262212713, (80817, 52518, 30820, 54268), 29867, (19, 20, 22, 38), (106, 109, 104, 166)⟩,
  ⟨(5579976983, 10757421292, -16082823455, -3448568789), 23103391500, (81364, 96050, 19914, 55753), 29702, (2, 3, 10, 19), (139, 110, 146, 126)⟩,
  ⟨(679894248270, -240584966788, -753606573704, -582263986350), 2119061334099, (86563, 58095, 42229, 47528), 29695, (20, 24, 33, 38), (74, 104, 106, 184)⟩,
  ⟨(817677820171, -768376230760, -2232371837672, 145678243885), 3743660632494, (79850, 52084, 26456, 68086), 29685, (6, 19, 21, 38), (109, 99, 103, 176)⟩,
  ⟨(16575348490, 31291148936, -44995774009, -12723912047), 67689996360, (81583, 95831, 21972, 53216), 29254, (2, 7, 11, 20), (177, 111, 132, 121)⟩,
  ⟨(3907578554, -4769432898, -49823941353, 28842682089), 88748715091, (68421, 62014, 28743, 86834), 29209, (6, 14, 25, 32), (148, 95, 96, 151)⟩,
  ⟨(47691601791, -100578964228, -317442308485, -95058446753), 555464565840, (71162, 53669, 28082, 54320), 29019, (9, 21, 22, 37), (92, 101, 119, 165)⟩,
  ⟨(-180705782287, -17919875212, -1176696735443, -210603172287), 1695020596736, (58549, 64843, 20040, 57393), 28987, (9, 13, 21, 37), (122, 118, 127, 163)⟩,
  ⟨(49600759, 119725970, -153436965, -41151625), 239451940, (79111, 98304, 23541, 54273), 28979, (1, 2, 10, 11), (110, 149, 124, 126)⟩,
  ⟨(19302806710, 39239600840, -53735854679, -15541313713), 82787243000, (80816, 96598, 22997, 53233), 28924, (2, 7, 11, 27), (152, 124, 40, 116)⟩,
  ⟨(-1049108348458, -91088299911, -6939443171610, -866990303846), 9832114675340, (58543, 64928, 19281, 59757), 28921, (13, 14, 21, 37), (131, 119, 48, 164)⟩,
  ⟨(-96842510, 462925711, -476330872, 151812522), 925851422, (58681, 98304, 31819, 76281), 28701, (1, 16, 18, 34), (42, 100, 125, 62)⟩,
  ⟨(39737830, 95918900, -120221493, -34534151), 191837800, (79111, 98304, 24465, 53738), 28687, (1, 2, 11, 27), (121, 129, 38, 120)⟩,
  ⟨(-349649798, 1734322732, -1880903680, 490339193), 3468645464, (58929, 98304, 29998, 74800), 28608, (1, 10, 16, 34), (144, 123, 100, 147)⟩,
  ⟨(1370975, 3309250, -4377953, -758579), 6618500, (79111, 98304, 22185, 58024), 28568, (1, 2, 3, 10), (113, 147, 120, 105)⟩,
  ⟨(-757842321773, 92749885483, -3618970029571, -919494188772), 5548083401857, (56584, 66631, 22787, 54674), 28465, (5, 9, 13, 37), (119, 107, 102, 173)⟩,
  ⟨(242622426, 91542764, -204258047, 151583993), 550245000, (94433, 76439, 41208, 83590), 27820, (3, 4, 26, 31), (64, 135, 136, 68)⟩,
  ⟨(220146677, 590991207, -710371003, -220511924), 1181982414, (77742, 98304, 26148, 53309), 27769, (1, 11, 27, 28), (152, 55, 149, 124)⟩,
  ⟨(-551667981, 102890852, -30008313619, -27770432237), 76927141704, (65066, 65623, 39971, 41877), 27757, (9, 17, 22, 24), (87, 182, 133, 101)⟩,
  ⟨(-16134923634, -464805158061, -3287000561141, 82599329252), 4822339108458, (65316, 59219, 20865, 66658), 27682, (6, 14, 21, 37), (122, 99, 96, 176)⟩,
  ⟨(2762098987, 4272043271, -6254552488, -1931535312), 9947271880, (83733, 93681, 24328, 52810), 27460, (2, 7, 12, 20), (183, 154, 116, 52)⟩,
  ⟨(-2374326792, 5332935440, -122561987116, -112409934842), 311152642665, (65035, 66659, 39721, 41859), 27344, (5, 9, 17, 24), (130, 157, 178, 102)⟩,
  ⟨(857500, 355250, -650609, 287251), 1715000, (98304, 79111, 40674, 76512), 27246, (0, 2, 3, 26), (45, 135, 31, 146)⟩,
  ⟨(43981500, 14812954, -37494301, 14016847), 87963000, (98304, 76572, 37601, 75979), 27087, (0, 3, 26, 31), (128, 30, 136, 134)⟩,
  ⟨(25533000, 8204168, -22576997, 7722599), 51066000, (98304, 76064, 36561, 75446), 27011, (0, 3, 4, 31), (128, 78, 135, 138)⟩,
  ⟨(174712440, 72380868, -169879691, -46403444), 349424880, (98304, 79111, 33674, 56832), 26966, (0, 2, 19, 33), (155, 91, 140, 146)⟩,
  ⟨(155667000, 47420863, -165104161, 22220812), 311334000, (98304, 75518, 30781, 70213), 26899, (0, 3, 4, 19), (167, 93, 146, 136)⟩,
  ⟨(737320915114, 1583184503403, -2960232443049, -244679100778), 4015995822000, (77568, 91371, 17228, 61543), 26886, (3, 10, 14, 19), (159, 174, 113, 153)⟩,
  ⟨(27132980, 11240806, -21884391, -8591342), 54265960, (98304, 79111, 39106, 55160), 26879, (0, 2, 12, 33), (155, 84, 137, 77)⟩,
  ⟨(-25830659760, 91217002689, -209624860938, 127000107226), 390435297711, (61200, 80847, 30349, 86853), 26634, (14, 16, 23, 34), (67, 70, 144, 145)⟩,
  ⟨(180494876781, 383815272011, -724335036764, -176872608942), 1027242653145, (77051, 90022, 19324, 54251), 26519, (9, 11, 19, 20), (111, 166, 181, 143)⟩,
  ⟨(11649046010, 24837949473, -46946953291, -11435991299), 66544048455, (77008, 89997, 19300, 54273), 26511, (9, 10, 11, 19), (110, 142, 158, 171)⟩,
  ⟨(-20179223790, 104536573746, -150032676882, 34587064314), 246984148529, (60181, 93274, 25725, 74713), 26485, (10, 14, 16, 34), (141, 125, 53, 153)⟩,
  ⟨(24890711104, 49134818007, -179791641092, 120738957184), 329384860285, (70488, 75312, 29763, 89558), 26424, (14, 16, 23, 32), (76, 89, 150, 141)⟩,
  ⟨(3690750, 1529025, -3903560, 133066), 7381500, (98304, 79111, 30878, 66717), 26407, (0, 2, 3, 19), (113, 138, 137, 134)⟩,
  ⟨(82277646, 637834750, -800228234, 79348923), 1275669500, (69762, 98304, 24425, 69612), 26243, (1, 3, 10, 16), (153, 125, 97, 126)⟩,
  ⟨(41830173258, 20870176044, -164032615661, 94023845233), 285335406197, (75143, 70329, 27860, 87131), 25901, (14, 25, 30, 32), (63, 150, 117, 151)⟩,
  ⟨(-1829740, 45544153, -44140269, -15645440), 91088306, (64219, 98304, 33778, 54279), 25843, (1, 10, 11, 28), (61, 129, 54, 120)⟩,
  ⟨(101933701962, 98490838350, -381930998151, 233025118465), 673085089771, (75460, 75125, 28348, 88224), 25718, (14, 16, 30, 32), (75, 148, 145, 160)⟩,
  ⟨(18162864434, 5736541758, -66794199987, 34948759815), 113817881435, (75994, 68839, 27076, 85659), 25613, (6, 14, 25, 30), (148, 82, 170, 117)⟩,
  ⟨(2303533607, 5875449318, -7438902670, -2845146077), 13004200137, (77144, 95145, 28046, 51197), 25573, (7, 11, 27, 28), (129, 56, 175, 121)⟩,
  ⟨(64932409674, 405480643557, -595723937721, 56541411003), 895277832500, (70289, 95217, 21927, 69674), 25508, (3, 10, 14, 16), (144, 160, 147, 139)⟩,
  ⟨(16569345686, 15514777264, -26632369135, -7808100278), 45371487000, (89469, 87946, 27067, 54257), 25363, (2, 12, 19, 20), (161, 111, 132, 155)⟩,
  ⟨(22201128643, 13971428591, -27304481303, -8091290533), 51153111240, (93979, 83435, 30554, 55169), 25308, (2, 12, 19, 33), (161, 137, 140, 154)⟩,
  ⟨(4449058692, 30559074070, -44904728912, -49432974158), 133773352743, (67715, 80506, 43537, 41318), 25201, (7, 17, 24, 28), (157, 162, 32, 8)⟩,
  ⟨(7711526729, 62949477213, -98112608661, -103856121275), 281563872815, (67330, 80187, 42699, 41362), 25103, (5, 17, 24, 28), (156, 162, 44, 133)⟩,
  ⟨(181276691953, 505486481074, -1377888049959, -246918774061), 1870365333858, (71887, 83247, 17255, 56884), 24687, (9, 10, 13, 19), (159, 163, 143, 168)⟩,
  ⟨(4665441326, 13120756890, -35890837892, -5219922785), 48241721217, (71873, 83360, 16778, 58444), 24664, (10, 13, 14, 19), (164, 139, 158, 53)⟩,
  ⟨(105326095022, 96228948561, -333596166580, 177960090156), 568669298500, (77674, 76625, 27090, 86044), 24592, (3, 14, 16, 30), (150, 81, 170, 153)⟩,
  ⟨(96540513206, 66880956424, -131814964585, -41264242160), 239835470358, (91916, 83811, 29517, 54260), 24578, (12, 19, 20, 33), (104, 184, 155, 154)⟩,
  ⟨(11469761945, 61429968635, -96722057199, -95127684881), 262773790667, (68396, 80856, 41413, 41811), 24382, (5, 7, 24, 28), (156, 157, 175, 178)⟩,
  ⟨(139285054189, 413940049060, -1373414753223, -223724718595), 1853652673536, (70460, 80170, 16978, 57626), 24332, (9, 13, 19, 21), (164, 165, 119, 158)⟩,
  ⟨(159305935430, 475576785201, -1584532445242, -241536172054), 2132036742492, (70432, 80154, 16829, 58111), 24324, (13, 14, 19, 21), (176, 163, 122, 159)⟩,
  ⟨(23228817279, -8877668740, -74353819333, -21564951329), 125989998672, (77618, 60918, 26859, 54318), 24235, (9, 19, 21, 22), (109, 118, 166, 163)⟩,
  ⟨(28930027358, -10480959292, -91732265557, -26754132954), 155546441412, (77725, 61120, 26886, 54263), 24125, (9, 19, 20, 22), (112, 182, 165, 142)⟩,
  ⟨(118281176014, 52192291441, -250910295105, 56404356226), 381011259000, (85881, 74513, 22378, 75237), 23691, (3, 4, 6, 19), (103, 174, 138, 169)⟩,
  ⟨(639752966, 3152388623, -8363957043, -1953976547), 11950071816, (69044, 82824, 19666, 54820), 23645, (9, 10, 13, 29), (66, 173, 171, 158)⟩,
  ⟨(8550187882, 4499439429, -20855687266, 6990237505), 32612083000, (82718, 74577, 23625, 79583), 23566, (3, 4, 6, 30), (108, 170, 79, 167)⟩,
  ⟨(193725261122, 104538162369, -479825183066, 162472818125), 750048983000, (82462, 74670, 23610, 79732), 23556, (3, 6, 14, 30), (151, 160, 169, 174)⟩,
  ⟨(10329054966, 62772310779, -164718817633, -40994177817), 238601064605, (68373, 82777, 20293, 54276), 23497, (9, 10, 11, 29), (94, 172, 168, 143)⟩,
  ⟨(25176118274, 164609530241, -436607279379, -109312874747), 633695796615, (68139, 82559, 20382, 54231), 23451, (5, 9, 11, 29), (171, 88, 173, 181)⟩,
  ⟨(2031578222, 13953985787, -37449054813, -9368763203), 54378461526, (67984, 82353, 20403, 54244), 23422, (5, 9, 13, 29), (168, 107, 172, 127)⟩,
  ⟨(480213200338, 273542817567, -1155024199375, 229578770782), 1705230453000, (83991, 76048, 21145, 74359), 23200, (3, 6, 14, 19), (176, 139, 167, 170)⟩,
  ⟨(9769796049, 37246776999, -58363249235, -46494825241), 138440700799, (70160, 83168, 37907, 43525), 22844, (5, 7, 11, 28), (152, 65, 162, 177)⟩,
  ⟨(157559502846, 33144594315, -815258270717, 31002004484), 1165840728858, (74392, 67399, 19707, 67278), 22610, (6, 14, 19, 21), (164, 115, 131, 174)⟩,
  ⟨(16100529003, 32098820387, -59843926579, -35673238811), 116375858413, (74602, 83612, 31835, 45446), 22258, (5, 7, 11, 20), (116, 181, 179, 175)⟩,
  ⟨(162991994020, 312275321610, -612418066514, -399917457116), 1246692803437, (74104, 81951, 33342, 44513), 22236, (5, 7, 9, 24), (180, 133, 162, 179)⟩,
  ⟨(3027330100, 5911800634, -11286016226, -7008470252), 22390553621, (74396, 82839, 32502, 45022), 22216, (5, 7, 9, 20), (180, 181, 177, 178)⟩,
  ⟨(829214015, 1556690099, -3058212166, -1989000158), 6216248930, (74278, 81947, 33294, 44566), 22204, (7, 9, 20, 24), (182, 183, 178, 179)⟩,
  ⟨(22605519479, 45276344461, -85061871309, -49964824112), 164249814290, (74555, 83601, 31596, 45599), 22202, (5, 9, 11, 20), (142, 177, 179, 172)⟩,
  ⟨(15928445803, 11339818143, -52647809422, -36705546454), 115656103282, (74561, 71961, 35703, 44736), 21839, (9, 20, 22, 24), (106, 130, 180, 166)⟩,
  ⟨(161037069, 179208617, -349342066, -225785146), 748057158, (79644, 81236, 34930, 45755), 21409, (7, 12, 20, 24), (184, 180, 58, 132)⟩,
  ⟨(34318025881, 29495582445, -63667773351, -41570542997), 140802597163, (81509, 79264, 35902, 46187), 21207, (12, 20, 24, 33), (114, 85, 161, 183)⟩
]

set_option maxRecDepth 20000 in
private lemma cell2_ok : verifyCell ⟨2, by decide⟩ hs2 vs2 ctr2 = true := by
  decide

private def ctr3 : NVec4 := (47900, 49450, 45079, 65282)

private def hs3 : List HSData := [
  ⟨.base 1, (-2, 0, 0, 0), 1⟩,
  ⟨.base 3, (0, -2, 0, 0), 1⟩,
  ⟨.ball0, (278, -590, -1747, 724), 1255⟩,
  ⟨.ball0, (-1442, -1115, 287, -772), 1255⟩,
  ⟨.ballA, (-909, -703, 181, -1627), 980⟩,
  ⟨.ballA, (-721, -657, 155, -1739), 910⟩,
  ⟨.ballA, (-448, 174, -743, -1794), 876⟩,
  ⟨.ballA, (230, -387, -1214, -1524), 1045⟩,
  ⟨.ball0, (-143, -1039, -889, 1452), 1254⟩,
  ⟨.ball0, (-1549, -798, 73, 980), 1255⟩,
  ⟨.ball0, (-1272, -647, 31, 1401), 1255⟩,
  ⟨.ballA, (-91, -23, 44, -1997), 748⟩,
  ⟨.ballA, (-33, -500, -52, -1936), 787⟩,
  ⟨.ball0, (-1014, -288, -762, 1519), 1254⟩,
  ⟨.ball0, (-959, 485, -1599, -537), 1255⟩,
  ⟨.ballA, (-98, -995, -67, -1731), 915⟩,
  ⟨.ball0, (-759, 463, -1214, 1318), 1255⟩,
  ⟨.ball0, (295, -352, -1401, 1352), 1255⟩,
  ⟨.ballA, (259, -404, -1107, -1596), 1001⟩,
  ⟨.ballA, (-991, -491, 53, -1665), 956⟩,
  ⟨.ballA, (-643, 336, -963, -1596), 1000⟩,
  ⟨.ball0, (430, -734, -1727, -543), 1255⟩,
  ⟨.ball0, (-295, -1407, -177, 1379), 1254⟩,
  ⟨.ball0, (-970, 618, -1588, 392), 1254⟩,
  ⟨.aff 0, (1345, 1441, 1552, 2202), 207⟩,
  ⟨.aff 1, (450, -165, 2586, 129), -71⟩,
  ⟨.aff 2, (1589, 1752, -92, -89), -113⟩,
  ⟨.aff 4, (2379, -500, 761, 165), 23⟩,
  ⟨.aff 6, (757, 2542, 2766, -359), 44⟩,
  ⟨.aff 7, (-773, 1800, 1131, 86), 42⟩
]

private def vs3 : List VertData := [
  ⟨(-358392871913, 56775160253, -1918349132301, 1920192790065), 4109957795138, (59821, 66441, 34946, 96154), 38558, (16, 17, 24, 26), (2, 5, 24, 9)⟩,
  ⟨(-927027704373, -1210519474000, -100591776080, 1760849487669), 3526866236499, (48310, 43042, 63666, 98255), 38394, (10, 22, 24, 25), (3, 7, 26, 10)⟩,
  ⟨(2411819619761, -4017797978044, -11983128502438, 12260360669832), 28278981939147, (71125, 56224, 37765, 93949), 38220, (17, 24, 26, 27), (78, 20, 4, 0)⟩,
  ⟨(-571496047306, -2635182125899, -391308007819, 2950095965560), 6390539425029, (59675, 38511, 61523, 95789), 38204, (22, 24, 25, 27), (78, 22, 6, 1)⟩,
  ⟨(627380295060, -3205635162391, -5079460733693, 6593846574710), 13820450853479, (68511, 50335, 41449, 96803), 37848, (8, 17, 24, 27), (2, 6, 28, 13)⟩,
  ⟨(-3003112458949, 1897052337793, -4996271551569, 5331539165093), 12948318623058, (50336, 75137, 40248, 92520), 37831, (16, 24, 26, 29), (77, 23, 18, 0)⟩,
  ⟨(-635957795730, -4522550420951, -1879903208551, 5787302128392), 11853483648313, (62019, 40531, 55142, 97533), 37689, (8, 22, 24, 27), (3, 4, 39, 12)⟩,
  ⟨(-11732219361222, -5146254638725, 259294870780, 13092951838266), 29166751749111, (39174, 53972, 66118, 94955), 37681, (10, 24, 25, 29), (77, 21, 16, 1)⟩,
  ⟨(68855299115, -352237029339, -64503229206, -1284728857648), 3428610970713, (66852, 58803, 64303, 40979), 37510, (11, 25, 26, 27), (78, 19, 14, 11)⟩,
  ⟨(-262535174771, -119889917479, -781435711851, 966862157268), 1885850552450, (56412, 61369, 38379, 99135), 37491, (13, 16, 17, 24), (0, 13, 18, 80)⟩,
  ⟨(-1757156429907, -2098889697152, -950450221507, 3780347988774), 7059671863191, (49224, 46051, 56712, 100629), 37392, (10, 13, 22, 24), (12, 1, 16, 95)⟩,
  ⟨(-1473209547692, -323203215250, 57192793339, -7399008794538), 19946300519238, (60695, 64474, 65723, 41225), 37343, (11, 25, 26, 28), (27, 15, 17, 8)⟩,
  ⟨(-229974824844, -288909353719, -144783228269, 523139137224), 973982085843, (50061, 46096, 55794, 100736), 37254, (8, 13, 22, 24), (10, 6, 13, 96)⟩,
  ⟨(-856536686832, -870519347047, -2612151903257, 3574027867392), 6809127474679, (57292, 57157, 40394, 99935), 37021, (8, 13, 17, 24), (9, 4, 12, 87)⟩,
  ⟨(43020725337, -336464889568, -52831533481, -1017326352327), 2718048054249, (66573, 57423, 64262, 41006), 37010, (11, 12, 25, 27), (46, 8, 19, 43)⟩,
  ⟨(-1748412191871, 92569395688, -179377059907, -6596145778275), 17809608211148, (59102, 65876, 64875, 41263), 36936, (11, 26, 28, 29), (27, 17, 32, 11)⟩,
  ⟨(-1161833356044, -306499895375, -305264798254, 1396814639466), 2887355826567, (39165, 58579, 58607, 97240), 36934, (10, 13, 24, 29), (18, 7, 38, 10)⟩,
  ⟨(-1826329816823, -202350680948, 155028086299, -6121617481739), 16580937735057, (58317, 64736, 66148, 41340), 36871, (11, 25, 28, 29), (27, 15, 29, 11)⟩,
  ⟨(-370615770981, 61660428161, -349741087811, 540943426068), 1153302999660, (44475, 69039, 45662, 96274), 36830, (13, 16, 24, 29), (5, 16, 54, 9)⟩,
  ⟨(74808288997, -280567301383, -143990483654, -922600867474), 2454203000933, (67533, 58043, 61690, 40899), 36468, (11, 12, 26, 27), (35, 8, 14, 53)⟩,
  ⟨(853161587038, -1343922819321, -3885614320008, 2627026176340), 7745202034518, (72755, 54164, 32657, 87764), 36054, (2, 17, 26, 27), (2, 33, 28, 24)⟩,
  ⟨(-2656847570876, -1186557548579, 119794384778, 2185625489617), 5747400622284, (35240, 52006, 66901, 90458), 35735, (9, 10, 25, 29), (7, 31, 37, 26)⟩,
  ⟨(-1659936911, -8149590228, -979231083, 6025883648), 16299180456, (58861, 32768, 61598, 89764), 35649, (1, 22, 25, 27), (3, 49, 39, 30)⟩,
  ⟨(-713618439314, 460392323423, -1182312700334, 719892441973), 2501150516263, (46837, 77599, 34556, 84398), 35634, (16, 23, 26, 29), (41, 5, 58, 25)⟩,
  ⟨(-431034680980, 65789302915, -2471072273749, 1348185895223), 4091160573983, (58631, 66589, 25952, 87132), 35388, (2, 16, 17, 26), (0, 20, 25, 80)⟩,
  ⟨(-223890876046, 55755879805, -1118676159253, 514088574053), 1777999796975, (57283, 67591, 24302, 84484), 34896, (2, 16, 23, 26), (23, 36, 24, 100)⟩,
  ⟨(-76321943675, -99344311632, -3471027312, 85502105243), 223934764605, (43199, 36462, 64520, 90558), 34753, (9, 10, 22, 25), (1, 30, 21, 95)⟩,
  ⟨(-487613700077, -5927184485, 12527931447, -1665747491723), 5646934863450, (59876, 65467, 65681, 46204), 34475, (25, 26, 28, 29), (15, 17, 77, 11)⟩,
  ⟨(209562350924, -1096475485983, -1545000223069, 1261096628790), 3440102166719, (69528, 44647, 36102, 89560), 34073, (2, 8, 17, 27), (4, 20, 55, 87)⟩,
  ⟨(-557326580326, -203197253163, 65782852380, -687353899837), 1913008608438, (46443, 58574, 67789, 41988), 33821, (5, 11, 25, 29), (17, 47, 45, 43)⟩,
  ⟨(-246323275, -352697892, -10359447, 227571712), 705395784, (42650, 32768, 64573, 86678), 33820, (1, 9, 22, 25), (26, 22, 48, 107)⟩,
  ⟨(-38610039, -17359610, 2316003, 23553276), 77220078, (32768, 50803, 67501, 85525), 33815, (0, 9, 25, 29), (21, 51, 37, 48)⟩,
  ⟨(-1554524319404, 596554577945, -1433228628536, -3284858022179), 8856337390921, (54032, 69950, 54930, 41228), 33670, (6, 11, 26, 29), (15, 57, 68, 53)⟩,
  ⟨(1951058781338, -2987448562501, -7769665045928, 450955190880), 12912418634678, (75438, 50373, 26101, 67824), 33555, (2, 21, 26, 27), (40, 20, 61, 34)⟩,
  ⟨(-166051904215, -44597614689, -1375486047459, -36564762332), 1877809880699, (59740, 63979, 17531, 64259), 33337, (2, 14, 21, 26), (44, 33, 36, 64)⟩,
  ⟨(261705335853, -512305041529, -857156918718, -983470614074), 2790454273573, (71682, 53504, 45404, 42438), 33228, (12, 18, 26, 27), (40, 19, 75, 52)⟩,
  ⟨(-2737496122, -241966317, -19391578323, 203184235), 26618270057, (58796, 64940, 17792, 66036), 33226, (2, 14, 23, 26), (41, 25, 34, 89)⟩,
  ⟨(-339337838, -102652133, -62652492, 253837645), 678675676, (32768, 55623, 59485, 90047), 32986, (0, 9, 10, 29), (21, 38, 31, 69)⟩,
  ⟨(-2704732767, -612687227, -834237109, 2125561656), 5409465534, (32768, 58113, 55429, 91287), 32978, (0, 10, 13, 29), (16, 54, 37, 69)⟩,
  ⟨(-233468559, -2520072916, -1166532923, 1812364560), 5040145832, (62500, 32768, 50367, 89101), 32968, (1, 8, 22, 27), (6, 22, 55, 107)⟩,
  ⟨(1836871579930, -2954052022205, -6826600898608, -2181315655188), 12694918817794, (75018, 50286, 30294, 54275), 32802, (18, 21, 26, 27), (33, 35, 62, 59)⟩,
  ⟨(-1493545908067, 933891342339, -2329266448927, -128675562547), 4524975024536, (43904, 79061, 31800, 63672), 32739, (14, 23, 26, 29), (23, 42, 93, 36)⟩,
  ⟨(-1956246036332, 1176634704920, -2905339159888, -1027482278435), 6090918789569, (44487, 78196, 34275, 54480), 32734, (14, 20, 26, 29), (57, 41, 90, 56)⟩,
  ⟨(-225436946326, -152346384339, 20607455996, -341057485109), 943873335270, (49883, 54958, 66966, 41855), 32593, (5, 11, 12, 25), (14, 76, 29, 101)⟩,
  ⟨(-105954800449, -32954344351, -828093977245, -167307162072), 1194895627305, (59724, 63728, 20117, 56359), 32350, (7, 14, 21, 26), (34, 59, 56, 83)⟩,
  ⟨(-33365058322, -9227757825, -1355822824, -37695965647), 104903269960, (44691, 59771, 64688, 41986), 32314, (5, 11, 19, 29), (68, 47, 29, 101)⟩,
  ⟨(-249180018615, -2401483783727, -186666232700, -1941850355340), 6325405037505, (62954, 40654, 63601, 45416), 32278, (12, 15, 25, 27), (49, 14, 75, 76)⟩,
  ⟨(-164784236671, -65250099910, 19170754107, -144416546566), 456912738072, (41900, 56177, 68285, 44822), 32226, (5, 19, 25, 29), (51, 29, 45, 82)⟩,
  ⟨(-2524863, -2524863, 119113, 411079), 5049726, (32768, 32768, 67081, 70871), 31980, (0, 1, 9, 25), (30, 31, 50, 91)⟩,
  ⟨(-1353016755, -10008711759, -717117786, -4723646323), 20017423518, (61106, 32768, 63188, 50071), 31814, (1, 15, 25, 27), (46, 22, 67, 74)⟩,
  ⟨(-2033415, -2033415, 104333, 162583), 4066830, (32768, 32768, 67217, 68155), 31714, (0, 1, 3, 25), (71, 66, 48, 104)⟩,
  ⟨(-4018227309, -1741140325, 452034743, -1694852619), 8036454618, (32768, 51337, 69222, 51714), 31617, (0, 19, 25, 29), (47, 31, 97, 65)⟩,
  ⟨(35730360789, -245647983035, -695350669566, -781982192674), 2124168550757, (66638, 57957, 44082, 41409), 31536, (6, 12, 18, 26), (35, 86, 53, 118)⟩,
  ⟨(-33354363185, -121651589173, -419137002530, -587371874422), 1551300586511, (64126, 60396, 47829, 40721), 31528, (6, 11, 12, 26), (19, 52, 32, 102)⟩,
  ⟨(-2796698079, 161334893, -2092180469, 1731724728), 5593396158, (32768, 67426, 41022, 85826), 31477, (0, 13, 16, 29), (18, 58, 38, 81)⟩,
  ⟨(310943097, -4971434995, -4445020418, 2338760137), 9942869990, (67585, 32768, 36237, 80951), 31459, (1, 2, 8, 27), (28, 39, 61, 79)⟩,
  ⟨(-744707347517, 3206001239, -4045618984179, -1154842380978), 6218983562675, (57688, 65569, 22903, 53366), 31457, (7, 14, 20, 26), (42, 60, 44, 111)⟩,
  ⟨(-270587127528, 153560202133, -377500254060, -221368950693), 942421340883, (46719, 76214, 39284, 50141), 31316, (6, 20, 26, 29), (42, 32, 98, 60)⟩,
  ⟨(-907004539, 80896573, -720305989, 513094358), 1814009078, (32768, 68458, 39512, 84072), 31217, (0, 16, 23, 29), (23, 93, 54, 81)⟩,
  ⟨(38170411841, -81082051096, -259118868695, -75674341587), 449814307820, (71097, 53722, 27783, 54510), 31172, (7, 18, 21, 26), (40, 44, 86, 112)⟩,
  ⟨(-210156942756, -3190890485, -1144507317936, -351004520229), 1796422536447, (57869, 65419, 23782, 52730), 31075, (6, 7, 20, 26), (56, 57, 86, 111)⟩,
  ⟨(738395578, -5627869925, -5803856812, 636600048), 11255739850, (69835, 32768, 31743, 69242), 30872, (1, 2, 21, 27), (33, 62, 55, 64)⟩,
  ⟨(216409066, -1845898469, -1629738520, -682691268), 3691796938, (69377, 32768, 36605, 53417), 30859, (1, 18, 21, 27), (40, 61, 67, 112)⟩,
  ⟨(-419163, -419163, -530878, -8458), 838326, (32768, 32768, 24034, 64874), 30830, (0, 1, 2, 14), (64, 89, 70, 79)⟩,
  ⟨(-595459471, -598714049, -759129230, -15373008), 1197428098, (32946, 32768, 23988, 64694), 30777, (1, 2, 14, 21), (34, 72, 61, 63)⟩,
  ⟨(-459450405, -284832257, 44964511, -168719559), 918900810, (32768, 45221, 68742, 53502), 30752, (0, 4, 19, 25), (82, 51, 66, 108)⟩,
  ⟨(-3233828115, -2280561427, 293071121, -1070972829), 6467656230, (32768, 42427, 68505, 54683), 30652, (0, 3, 4, 25), (71, 65, 50, 108)⟩,
  ⟨(134770801, -1581243479, -1207757125, -723643048), 3162486958, (68328, 32768, 40507, 50539), 30561, (1, 15, 18, 27), (75, 62, 49, 105)⟩,
  ⟨(-170591400488, -19327223715, -53903568392, -178416131123), 494510161007, (42928, 62974, 58392, 41891), 30531, (6, 11, 19, 29), (45, 97, 32, 102)⟩,
  ⟨(-355299073, -116820767, -128472041, 262854996), 710598146, (32768, 54762, 53687, 89778), 30520, (0, 9, 10, 13), (95, 38, 92, 37)⟩,
  ⟨(-1345398, -1345398, -1579515, -397739), 2690796, (32768, 32768, 27065, 55848), 30347, (0, 1, 14, 19), (72, 103, 104, 63)⟩,
  ⟨(-3446378509, -4399645197, 150086479, -1456933187), 8799290394, (39867, 32768, 66653, 54684), 30343, (1, 3, 4, 25), (66, 73, 50, 115)⟩,
  ⟨(-1917643176, -1941796482, -2289250533, -588731947), 3883592964, (33175, 32768, 26904, 55601), 30320, (1, 14, 19, 21), (83, 85, 64, 70)⟩,
  ⟨(-388377069, -541884975, 13239071, -200195689), 1083769950, (42050, 32768, 66336, 53430), 30083, (1, 4, 5, 25), (82, 74, 71, 117)⟩,
  ⟨(-1542365060, -2951725581, -15382634, -1335937867), 5903451162, (48413, 32768, 65365, 50705), 30045, (1, 5, 15, 25), (76, 49, 73, 116)⟩,
  ⟨(158267441723, -1138986419941, -957420296642, -900213914470), 2994752704235, (68999, 40610, 44584, 45836), 30031, (12, 15, 18, 27), (67, 35, 46, 118)⟩,
  ⟨(-179402748451, -350260225839, -2735788804, -299323481984), 966560261445, (53371, 41787, 65350, 45240), 30023, (5, 12, 15, 25), (46, 74, 43, 120)⟩,
  ⟨(-1764723158941, 58468154683, -615581465697, 3967742289527), 26532782844924, (61177, 65680, 64015, 75336), 29992, (24, 25, 26, 29), (27, 5, 7, 78)⟩,
  ⟨(-27726915617, -1528484761427, -1034549351732, 4245957828093), 26590044931650, (65467, 61768, 62986, 76000), 29934, (24, 25, 26, 27), (8, 2, 3, 77)⟩,
  ⟨(-473252, -473252, -557868, 90625), 946504, (32768, 32768, 26909, 71810), 29668, (0, 1, 2, 8), (55, 84, 91, 63)⟩,
  ⟨(-355786404020, -239620048065, -856906403147, 572559802224), 1556984853505, (50560, 55450, 29467, 89635), 29665, (2, 13, 16, 17), (9, 24, 87, 100)⟩,
  ⟨(-115661729, -849307, -96224584, 65326458), 231323458, (32768, 65295, 38274, 84043), 29639, (0, 13, 16, 23), (100, 58, 94, 54)⟩,
  ⟨(-27069044705, -18648796903, 2513057329, -14397362911), 62852284380, (37311, 46090, 68156, 50523), 29562, (4, 5, 19, 25), (47, 65, 73, 117)⟩,
  ⟨(-1850783252196, -1866208532754, -2280892064955, -645925259813), 3875536475580, (34238, 33978, 26965, 54613), 29464, (7, 14, 19, 21), (72, 85, 44, 88)⟩,
  ⟨(-1494856361, -1462907877, -1763894786, 308038254), 2989712722, (32768, 33468, 26870, 72288), 29414, (0, 2, 8, 13), (87, 92, 94, 79)⟩,
  ⟨(-21789852, -23548902, -27129525, -7992259), 47097804, (35215, 32768, 27785, 54414), 29267, (1, 7, 19, 21), (83, 72, 112, 99)⟩,
  ⟨(-44919964729, -22935286115, -335647431574, -144904821786), 599861525523, (60628, 63030, 28865, 49704), 29191, (6, 7, 18, 26), (59, 52, 60, 110)⟩,
  ⟨(-103944675812, -93950777721, -250348305323, 176350092720), 471370753393, (51084, 52473, 30729, 90054), 28965, (2, 8, 13, 17), (13, 80, 28, 84)⟩,
  ⟨(-1326947419053, -1307328157554, -1636995362766, -485819102477), 2802333754224, (34503, 34962, 27252, 54174), 28822, (6, 7, 14, 19), (83, 103, 110, 111)⟩,
  ⟨(-7770743, -6490809, -9820842, 936800), 15541486, (32768, 38165, 24123, 69486), 28518, (0, 2, 14, 23), (36, 93, 94, 63)⟩,
  ⟨(-2170101321, 315815640, -1770631759, -710272590), 4340202642, (32768, 70304, 38799, 54811), 28515, (0, 14, 20, 29), (42, 98, 93, 114)⟩,
  ⟨(-977216, -977216, -1062804, 241705), 1954432, (32768, 32768, 29898, 73640), 28420, (0, 1, 8, 9), (107, 92, 48, 79)⟩,
  ⟨(-804342691, -802826738, -874571921, 200164632), 1608685382, (32768, 32829, 29906, 73690), 28395, (0, 8, 9, 13), (96, 69, 84, 91)⟩,
  ⟨(-1617416597, 301319739, -1461191093, -48470225), 3234833194, (32768, 71640, 35933, 64554), 28384, (0, 14, 23, 29), (41, 58, 90, 89)⟩,
  ⟨(-1206048733, -982461211, -1487825270, 253564926), 2412097466, (32768, 38842, 25112, 72425), 28131, (0, 2, 13, 23), (100, 81, 89, 84)⟩,
  ⟨(-49401968319, -55518682659, -33740546956, 49051219320), 132617285015, (41122, 38100, 48862, 89775), 28091, (9, 10, 13, 22), (10, 96, 26, 69)⟩,
  ⟨(-5818847811, -6569620411, -4055343704, 5680554264), 15559247359, (41026, 37864, 48454, 89462), 27887, (8, 9, 13, 22), (95, 12, 107, 92)⟩,
  ⟨(-3691245658, -266216197, -1671668848, -2016530659), 7382491316, (32768, 63172, 50696, 47634), 27575, (0, 6, 19, 29), (68, 51, 98, 103)⟩,
  ⟨(-95416806, 3395851, -60178506, -44102568), 190833612, (32768, 66702, 44869, 50390), 27360, (0, 6, 20, 29), (57, 90, 97, 114)⟩,
  ⟨(-95468018, -115237966, -122706999, -45434123), 230475932, (38389, 32768, 30644, 52616), 27160, (1, 7, 15, 19), (106, 116, 85, 105)⟩,
  ⟨(-184259174949, -100046924255, -344918773746, 165175678830), 581644560862, (44774, 54263, 26672, 84146), 26976, (2, 13, 16, 23), (81, 25, 94, 80)⟩,
  ⟨(-22201959536, -10064537295, -11083507656, -27162422851), 74876399428, (46103, 56726, 55835, 41761), 26930, (5, 11, 12, 19), (102, 109, 45, 43)⟩,
  ⟨(-118249258658, -52973581601, -61549484072, -144350029783), 397777950658, (46053, 56808, 55395, 41753), 26790, (6, 11, 12, 19), (101, 109, 68, 53)⟩,
  ⟨(-517336812, -415961979, -567003444, -181550183), 1034673624, (32768, 39189, 29622, 54036), 26453, (0, 6, 14, 19), (88, 70, 97, 114)⟩,
  ⟨(-436939, -436939, -410215, -125901), 873878, (32768, 32768, 34772, 56094), 26421, (0, 1, 3, 19), (115, 108, 70, 50)⟩,
  ⟨(-1674331, -2214676, -2314295, -883947), 4429352, (40762, 32768, 31294, 52457), 26151, (1, 7, 15, 18), (106, 67, 112, 99)⟩,
  ⟨(-75355099593, -89853793233, -97567057800, -39479433586), 187612258401, (39213, 34148, 31454, 51745), 26051, (7, 15, 18, 19), (113, 110, 99, 105)⟩,
  ⟨(-140797253, -178827052, -112414201, 98227760), 357654104, (39736, 32768, 44937, 83535), 26043, (1, 8, 9, 22), (96, 30, 39, 91)⟩,
  ⟨(-2334246, -1797677, -377177, -773076), 4668492, (32768, 40300, 60241, 54683), 25594, (0, 3, 4, 19), (115, 65, 104, 66)⟩,
  ⟨(-9342568968, -4922030713, -5523770148, -11168086169), 31357015252, (46010, 55248, 53991, 42194), 25491, (5, 6, 12, 19), (102, 101, 119, 120)⟩,
  ⟨(-10465236177, -11837218347, -13506882150, -5622036074), 25970657499, (39127, 35665, 31451, 51348), 25436, (6, 7, 18, 19), (106, 113, 88, 86)⟩,
  ⟨(-20335647894, -11901516777, -57782168298, -16984070086), 91827715887, (51022, 57042, 24297, 53414), 25303, (6, 7, 14, 20), (56, 114, 60, 88)⟩,
  ⟨(-24332263, -40983988, -43561475, -14769371), 81967976, (46081, 32768, 30707, 53727), 24936, (1, 7, 18, 21), (59, 62, 85, 105)⟩,
  ⟨(-17368437303, -20347585728, -22615495590, -10375974001), 45272135361, (40393, 36080, 32797, 50515), 24579, (6, 15, 18, 19), (106, 110, 119, 118)⟩,
  ⟨(-212952648, -142529331, -224373228, -75686203), 425905296, (32768, 43604, 31010, 53889), 24311, (0, 6, 14, 20), (111, 90, 98, 103)⟩,
  ⟨(-53963741, -59329431, -35611855, -19649539), 118658862, (35731, 32768, 45867, 54683), 23226, (1, 3, 4, 19), (108, 117, 104, 71)⟩,
  ⟨(-2527318, -3213497, -2391927, -1314462), 6426994, (39764, 32768, 41145, 52132), 23087, (1, 5, 15, 19), (119, 99, 117, 74)⟩,
  ⟨(-5907896, -7213699, -4630239, -2787594), 14427398, (38699, 32768, 44503, 52873), 22746, (1, 4, 5, 19), (82, 116, 115, 73)⟩,
  ⟨(-43077997735, -66835655835, -76536412198, -59087237934), 194678764825, (51034, 43036, 39771, 45645), 21560, (6, 12, 15, 18), (75, 113, 52, 120)⟩,
  ⟨(-40358099642, -45648892311, -47759162600, -34450121189), 122632530368, (43968, 41140, 40013, 47125), 20975, (5, 6, 15, 19), (113, 116, 109, 120)⟩,
  ⟨(-90466451533, -103844714607, -106126879762, -94344356012), 308865338235, (46340, 43501, 43017, 45517), 20804, (5, 6, 12, 15), (118, 76, 119, 109)⟩
]

set_option maxRecDepth 20000 in
private lemma cell3_ok : verifyCell ⟨3, by decide⟩ hs3 vs3 ctr3 = true := by
  decide

private def ctr4 : NVec4 := (79353, 48867, 57472, 70226)

private def hs4 : List HSData := [
  ⟨.base 0, (2, 0, 0, 0), 1⟩,
  ⟨.base 3, (0, -2, 0, 0), 1⟩,
  ⟨.base 6, (140, -140, 0, 0), 99⟩,
  ⟨.ballA, (0, 0, 0, -2000), 746⟩,
  ⟨.ball0, (1000, -1000, -1000, 1000), 1254⟩,
  ⟨.ball0, (811, -249, -1350, 1208), 1255⟩,
  ⟨.ball0, (500, -1453, 575, 1143), 1254⟩,
  ⟨.ball0, (1498, 209, -656, 1132), 1254⟩,
  ⟨.ball0, (1279, -733, 339, 1309), 1255⟩,
  ⟨.ball0, (-54, -1579, 115, 1221), 1255⟩,
  ⟨.ball0, (893, -386, -1670, -517), 1255⟩,
  ⟨.ball0, (311, -482, -1624, 1016), 1254⟩,
  ⟨.ballA, (992, 10, -496, -1664), 957⟩,
  ⟨.ballA, (461, -950, 509, -1620), 984⟩,
  ⟨.ball0, (15, -1030, -835, 1498), 1255⟩,
  ⟨.ball0, (303, -440, -1383, 1342), 1254⟩,
  ⟨.ball0, (717, -1058, 826, 1298), 1255⟩,
  ⟨.ball0, (430, -734, -1727, -543), 1255⟩,
  ⟨.ballA, (-132, -995, -71, -1728), 917⟩,
  ⟨.ball0, (-277, -1322, -165, 1465), 1254⟩,
  ⟨.ballA, (276, -472, -1073, -1597), 999⟩,
  ⟨.aff 0, (-1034, 1941, 791, 2037), 184⟩,
  ⟨.aff 1, (-1929, 335, 1825, -36), -94⟩,
  ⟨.aff 2, (-790, 2252, -853, -254), -136⟩,
  ⟨.aff 3, (-2379, 500, -761, -165), -23⟩,
  ⟨.aff 5, (689, 1245, 1471, -265), 16⟩
]

private def vs4 : List VertData := [
  ⟨(6649169613, -842713207, -6749560040, 1635097293), 13298339226, (98304, 61382, 32273, 73593), 34092, (0, 5, 10, 23), (44, 15, 23, 54)⟩,
  ⟨(-2832299166505, -13063903711243, -1942273773748, 14632514217381), 31748114893554, (59689, 38568, 61526, 95741), 34064, (19, 21, 22, 24), (102, 20, 18, 10)⟩,
  ⟨(60985582891, -126650240066, 73123364361, -46571738504), 265343588020, (80598, 34255, 83596, 54033), 34057, (2, 13, 22, 25), (7, 9, 68, 8)⟩,
  ⟨(516373232561, -1138939062499, -2901944554, -4801642736844), 12873036828000, (68164, 59737, 65521, 41091), 34017, (3, 22, 23, 25), (101, 43, 7, 4)⟩,
  ⟨(240543421621, -1232940255449, -226871893784, -4482765206559), 12018137283000, (66847, 58812, 64298, 41091), 33925, (3, 22, 23, 24), (102, 39, 19, 3)⟩,
  ⟨(122088734375, -723731454694, 189003761885, 834918802949), 1734940610616, (70147, 38197, 72675, 97074), 33922, (6, 9, 21, 22), (10, 12, 61, 26)⟩,
  ⟨(6145105518408, -8842120952067, 6938971076405, 11309794632796), 27229249535032, (80326, 44254, 82236, 92756), 33812, (16, 21, 22, 25), (101, 11, 33, 12)⟩,
  ⟨(147226131403, -334179183658, 145727394553, -451360759072), 1210082464000, (73509, 47437, 73428, 41091), 33761, (3, 13, 22, 25), (2, 3, 65, 13)⟩,
  ⟨(3550296, -8569680, 4383756, -2997479), 17139360, (79111, 32768, 82298, 54074), 33714, (1, 2, 13, 22), (2, 40, 50, 95)⟩,
  ⟨(241351256482, -410746331693, 287724098077, 239243206572), 922158205500, (82688, 36345, 85983, 82538), 33653, (2, 6, 22, 25), (11, 2, 14, 50)⟩,
  ⟨(-5682316139, -2064931898765, 167265731524, 2341651363179), 4891813694652, (65459, 37871, 67776, 96907), 33648, (9, 19, 21, 22), (1, 5, 24, 26)⟩,
  ⟨(648163988750, -1098471714449, 771724371321, 658238632104), 2485063529086, (82629, 36567, 85887, 82895), 33617, (6, 16, 22, 25), (6, 9, 14, 12)⟩,
  ⟨(435727915799, -1087001632039, 537972580094, 1307439951427), 2871623147757, (75480, 40728, 77813, 95374), 33579, (6, 16, 21, 22), (6, 5, 11, 35)⟩,
  ⟨(223353298100, -643927788072, 225687312400, -814848047195), 2184579215000, (72236, 46218, 72306, 41091), 33566, (3, 13, 18, 22), (40, 19, 7, 73)⟩,
  ⟨(18902823720, -31608747588, 22065348765, 18816583967), 71430504880, (82878, 36535, 85780, 82799), 33527, (2, 6, 16, 25), (11, 67, 9, 83)⟩,
  ⟨(3089988297, -384651855, -2613423656, -935431247), 6179976594, (98304, 61456, 37821, 55616), 33428, (0, 10, 12, 23), (52, 49, 0, 72)⟩,
  ⟨(206766553011, -363498452209, -39395702672, 556282884943), 992603936219, (79187, 41536, 62934, 102264), 33319, (6, 8, 19, 21), (17, 26, 35, 22)⟩,
  ⟨(1545849369065, -2704891550979, -311695047308, 4151697493745), 7401381871057, (79223, 41585, 62776, 102297), 33314, (8, 14, 19, 21), (18, 16, 36, 22)⟩,
  ⟨(-586279731163, -4340927254485, -1888164380381, 5611649944910), 11510143228084, (62197, 40819, 54785, 97487), 33311, (14, 19, 21, 24), (1, 31, 64, 17)⟩,
  ⟨(-81404782850, -1607464256223, -141019071525, -2218078885005), 5946592185000, (64638, 47820, 63981, 41091), 33301, (3, 18, 22, 24), (42, 4, 55, 13)⟩,
  ⟨(-884321063, -4320257271, -522194262, 3271471765), 8640514542, (58828, 32768, 61575, 90349), 33202, (1, 19, 22, 24), (1, 42, 64, 24)⟩,
  ⟨(12197941393548, 1729814720466, -5291598276148, 8917778329930), 25678039093099, (96667, 69950, 52030, 88296), 33175, (7, 21, 23, 25), (101, 28, 32, 27)⟩,
  ⟨(173744330857, -304885017531, -35665725364, 461324986345), 826680034457, (79309, 41365, 62708, 102108), 33170, (6, 8, 14, 19), (17, 47, 16, 70)⟩,
  ⟨(2225861000, -155465004, -2014439070, 847296613), 4451722000, (98304, 63247, 35880, 78009), 33059, (0, 5, 7, 23), (27, 28, 0, 77)⟩,
  ⟨(-218469935, -1187952075, -117337362, 907190665), 2375904150, (59509, 32768, 62299, 90559), 33013, (1, 9, 19, 22), (10, 20, 61, 91)⟩,
  ⟨(227993462, -1689931921, -1809376877, 407941001), 3379863842, (69956, 32768, 30451, 73446), 32987, (1, 11, 17, 24), (29, 34, 53, 51)⟩,
  ⟨(26015504161, -59133121849, -1224209067, 84020406788), 154911948064, (76541, 40519, 65018, 101081), 32965, (6, 9, 19, 21), (10, 16, 5, 47)⟩,
  ⟨(5201618830143, -66000530068, -4502377749674, 5688511391080), 13693130458739, (90431, 65220, 43987, 92761), 32863, (5, 7, 21, 23), (21, 41, 23, 46)⟩,
  ⟨(4893426475, 634317226, -2185116000, 2982643413), 9786852950, (98304, 69783, 50903, 85508), 32764, (0, 7, 23, 25), (21, 49, 45, 23)⟩,
  ⟨(62371064222, -94307506219, -252503665572, 36425458530), 408235915252, (75548, 50396, 25000, 71383), 32752, (11, 17, 23, 24), (56, 58, 25, 38)⟩,
  ⟨(2402368575786, -4005911369689, -11939042938466, 12223063938619), 28234104362561, (71112, 56237, 37823, 93907), 32699, (15, 21, 23, 24), (102, 58, 31, 41)⟩,
  ⟨(550985749549, -2960996572943, -4591931645771, 6030542207330), 12690124627230, (68381, 50244, 41821, 96679), 32667, (14, 15, 21, 24), (30, 18, 71, 59)⟩,
  ⟨(7511664462030, -1419057646044, -904151817941, 6911764641983), 15449068168574, (97400, 59516, 61700, 94856), 32615, (7, 8, 21, 25), (33, 21, 45, 37)⟩,
  ⟨(1463739479310, -1317926318328, 856804390943, 2088018588511), 4670785502998, (86073, 47044, 77557, 94833), 32520, (8, 16, 21, 25), (6, 32, 67, 35)⟩,
  ⟨(330305792, -2793142006, -2496272237, -934671379), 5586284012, (69411, 32768, 36250, 54570), 32460, (1, 17, 20, 24), (56, 48, 25, 79)⟩,
  ⟨(98109985725, -152682621968, 16472856488, 227847388346), 431263397083, (80445, 42333, 68039, 100160), 32430, (6, 8, 16, 21), (33, 12, 16, 83)⟩,
  ⟨(273507741594, -301581238195, -126918230274, 566889710525), 1011879522000, (83250, 46003, 57315, 102251), 32390, (4, 8, 14, 21), (17, 59, 37, 70)⟩,
  ⟨(1519602069924, -661148695412, -643103886699, 1998444537541), 3845533644000, (91433, 54268, 54576, 99593), 32342, (4, 7, 8, 21), (32, 36, 46, 85)⟩,
  ⟨(463117156212, -422234501449, -1268847509062, 186102738255), 2071160448217, (80190, 52175, 25386, 71424), 32291, (10, 11, 17, 23), (29, 63, 44, 76)⟩,
  ⟨(550840861844, -1121879749159, -1753194762916, -2370086737620), 6354119940000, (71217, 53965, 47453, 41091), 32273, (3, 20, 23, 24), (56, 4, 55, 57)⟩,
  ⟨(601635060, -3761356536, 901227672, -1909248337), 7522713072, (70777, 32768, 73387, 48903), 32262, (1, 13, 18, 22), (13, 42, 8, 95)⟩,
  ⟨(437184580446, -243747737711, -979344968158, 1050893082365), 2395891977643, (77494, 58868, 38747, 94281), 32139, (5, 15, 21, 23), (30, 27, 66, 60)⟩,
  ⟨(-449616592, -3326394183, -238292679, -1570935503), 6652788366, (61106, 32768, 63188, 50060), 32119, (1, 18, 22, 24), (19, 20, 48, 40)⟩,
  ⟨(762688923163, -162473258684, -377497219532, -1044935553773), 2801435801000, (83378, 61735, 56704, 41091), 32115, (3, 12, 23, 25), (49, 3, 65, 57)⟩,
  ⟨(1620263026584, -707506501081, -2793991995122, 651517331749), 4820019572507, (87566, 55916, 27547, 74394), 32096, (5, 10, 11, 23), (38, 66, 0, 69)⟩,
  ⟨(1530606131, -308296458, -185815267, 1314886340), 3061212262, (98304, 58935, 61557, 93685), 32057, (0, 7, 8, 25), (32, 93, 28, 85)⟩,
  ⟨(742187774422, -291020079776, -435838959957, 1001230053123), 1969917757000, (90227, 55854, 51036, 98845), 32057, (4, 5, 7, 21), (27, 37, 60, 77)⟩,
  ⟨(69678446795, -130974516735, -18388849331, 179161696730), 334412621380, (79191, 39868, 61932, 100646), 32037, (6, 9, 14, 19), (91, 22, 26, 74)⟩,
  ⟨(327411232, -4638021675, -3326456043, -2140243107), 9276043350, (67849, 32768, 42034, 50415), 31976, (1, 18, 20, 24), (55, 34, 42, 89)⟩,
  ⟨(411812141, -3703099, -210597242, -165427640), 823624282, (98304, 65241, 48778, 52372), 31965, (0, 12, 23, 25), (43, 28, 87, 15)⟩,
  ⟨(61093575, -147467250, 77838633, 70230925), 294934500, (79111, 32768, 82832, 81141), 31963, (1, 2, 6, 22), (9, 61, 8, 100)⟩,
  ⟨(114143928, -547983500, -577475619, 134739571), 1095967000, (72361, 32768, 31004, 73593), 31939, (1, 4, 11, 17), (76, 25, 88, 62)⟩,
  ⟨(824454665490, -279624071737, -1006202083780, -481146263814), 2209787255998, (89986, 57243, 35694, 51266), 31893, (10, 12, 20, 23), (57, 63, 15, 80)⟩,
  ⟨(46933190, -593004673, -559772582, 273386390), 1186009346, (68129, 32768, 34604, 80642), 31886, (1, 11, 14, 24), (71, 64, 25, 62)⟩,
  ⟨(556389750, -152147120, -546902083, 139986540), 1112779500, (98304, 56575, 33326, 73780), 31849, (0, 4, 5, 10), (69, 0, 78, 77)⟩,
  ⟨(163102224188, -738736359225, -684493590987, -1043353280313), 2797193781000, (69357, 48228, 49498, 41091), 31826, (3, 18, 20, 24), (48, 39, 19, 75)⟩,
  ⟨(927191575106, -1490485459867, -3447986686198, -1089603998667), 6405606918867, (75022, 50286, 30259, 54388), 31817, (17, 20, 23, 24), (39, 29, 34, 63)⟩,
  ⟨(278772107661, -174528505400, -355941633226, -500556595178), 1341974786000, (79149, 57012, 48153, 41091), 31658, (3, 12, 20, 23), (52, 39, 43, 75)⟩,
  ⟨(213292320282, -342331417706, -998509687114, 787500284357), 2115644079523, (72143, 54931, 34605, 89930), 31624, (11, 15, 23, 24), (30, 29, 71, 66)⟩,
  ⟨(198144932519, -197979937618, -238600089311, 460795172005), 873620519500, (80400, 50684, 47637, 100103), 31526, (4, 14, 15, 21), (31, 60, 36, 92)⟩,
  ⟨(244894541653, -219400112555, -286553429311, 537443260634), 1027345569500, (81158, 51540, 47256, 99820), 31475, (4, 5, 15, 21), (41, 59, 46, 96)⟩,
  ⟨(77513385, -582684555, 137440998, 434774225), 1165369110, (69895, 32768, 73265, 89986), 31443, (1, 6, 9, 22), (5, 24, 50, 100)⟩,
  ⟨(36546284, -342269750, -320398974, 159197525), 684539500, (69034, 32768, 34861, 80777), 31439, (1, 4, 11, 14), (92, 53, 97, 51)⟩,
  ⟨(387022525140, -344398455727, -908526555190, -290567419269), 1709969419753, (80368, 52336, 30715, 54399), 31299, (10, 17, 20, 23), (56, 52, 38, 94)⟩,
  ⟨(-134136764, -1346611363, -600245336, 997190930), 2693222726, (62271, 32768, 50929, 89801), 31259, (1, 14, 19, 24), (18, 20, 53, 91)⟩,
  ⟨(88460243609, -63455251568, -2525462881, -98006256534), 262751358000, (87599, 49708, 64906, 41091), 31192, (3, 12, 13, 25), (68, 7, 43, 73)⟩,
  ⟨(100113335856, -74346692336, -261142858450, 205088640035), 557764285132, (77299, 56800, 34852, 89633), 30912, (5, 11, 15, 23), (58, 41, 44, 96)⟩,
  ⟨(78477296316, -74446516209, 42641271536, 77925134215), 216255896500, (89318, 42975, 78458, 89151), 30541, (2, 8, 16, 25), (33, 14, 93, 83)⟩,
  ⟨(39782364383, -26606159566, -547845507, -30274054788), 93882761140, (93306, 46963, 65153, 44402), 30403, (2, 12, 13, 25), (65, 2, 87, 81)⟩,
  ⟨(281999683772, -166527583358, -446805777255, 109516580702), 801315490500, (88599, 51916, 28993, 74492), 30400, (4, 5, 10, 11), (44, 76, 96, 54)⟩,
  ⟨(307581260122, -506894058225, -103961383642, 614732873575), 1222623266000, (82023, 38365, 59963, 98487), 30372, (4, 6, 8, 14), (22, 36, 74, 82)⟩,
  ⟨(79501036618, -501633270347, -651650724302, 548320338050), 1500706777050, (69007, 43629, 37078, 89481), 30353, (11, 14, 15, 24), (31, 58, 53, 92)⟩,
  ⟨(88285680, -36575496, -68102117, -28838042), 176571360, (98304, 51960, 40259, 54832), 30035, (0, 2, 10, 12), (80, 15, 87, 78)⟩,
  ⟨(25370475488, -26306640116, -8014874692, -32028775563), 85868031000, (84899, 45458, 59418, 41091), 29919, (3, 12, 13, 18), (81, 13, 75, 65)⟩,
  ⟨(31167279415, -56000939235, -11884332703, 62468798890), 128804904500, (81393, 37042, 59489, 97320), 29703, (4, 6, 9, 14), (47, 97, 70, 90)⟩,
  ⟨(107590421463, -126061279920, -77960106452, -159853512608), 428561696000, (81988, 46258, 53614, 41091), 29624, (3, 12, 18, 20), (84, 55, 57, 73)⟩,
  ⟨(238044128810, -247037853977, -465648487170, 88334819756), 828600709500, (84363, 45997, 28706, 72522), 29431, (4, 10, 11, 17), (38, 51, 98, 69)⟩,
  ⟨(80863250, -19671252, -62998035, 39272494), 161726500, (98304, 57564, 40007, 81450), 29427, (0, 4, 5, 7), (46, 23, 85, 54)⟩,
  ⟨(3827250, -1585575, -3539438, 646480), 7654500, (98304, 51960, 35232, 71071), 29397, (0, 2, 4, 10), (98, 54, 72, 86)⟩,
  ⟨(31543010, -76138300, -62483681, -25320091), 152276600, (79111, 32768, 38644, 54638), 29272, (1, 2, 17, 20), (94, 34, 89, 88)⟩,
  ⟨(93371356677, -60796731210, -86105217323, -44420796857), 218015477820, (93603, 47260, 39652, 52182), 29136, (2, 10, 12, 20), (52, 84, 94, 72)⟩,
  ⟨(11722805708, -12980926840, -4752249192, -11764456203), 34934571280, (87527, 41184, 56620, 43466), 29031, (2, 12, 13, 18), (73, 95, 84, 68)⟩,
  ⟨(2423997778, -3784717922, -692130095, 4109276713), 8780002000, (83629, 37285, 60369, 96208), 28914, (2, 4, 6, 8), (70, 83, 86, 90)⟩,
  ⟨(12987685336, -16441245041, 4396684033, 16864600324), 41616669220, (85988, 39645, 72459, 92093), 28844, (2, 6, 8, 16), (35, 67, 14, 82)⟩,
  ⟨(68227004841, -80698113930, -40574404334, -68837869706), 210601178060, (86767, 40423, 52909, 44114), 28793, (2, 12, 18, 20), (75, 89, 80, 81)⟩,
  ⟨(483948000, -198773404, -148705299, 382314881), 967896000, (98304, 52077, 55467, 91422), 28685, (0, 4, 7, 8), (37, 45, 86, 77)⟩,
  ⟨(2884000, -1194800, -882601, 2271671), 5768000, (98304, 51960, 55507, 91346), 28614, (0, 2, 4, 8), (82, 85, 93, 78)⟩,
  ⟨(10030160, -4155352, -1868255, -5025665), 20060320, (98304, 51960, 59432, 49117), 28605, (0, 2, 12, 25), (68, 49, 93, 72)⟩,
  ⟨(822875, -1986250, -1917776, 254614), 3972500, (79111, 32768, 33897, 69736), 28555, (1, 2, 4, 17), (98, 51, 79, 99)⟩,
  ⟨(50481953, -121852990, -70848922, -60108798), 243705980, (79111, 32768, 46483, 49371), 28549, (1, 2, 18, 20), (84, 48, 79, 95)⟩,
  ⟨(659535985, -1236667940, -256191767, 1210205935), 2681500500, (81655, 35311, 59274, 95113), 28492, (2, 4, 6, 9), (74, 100, 99, 82)⟩,
  ⟨(42784225, -282969415, -94364411, 226541180), 565938830, (70490, 32768, 54608, 91769), 28463, (1, 9, 14, 19), (47, 64, 24, 97)⟩,
  ⟨(16699233968, -49066913072, -57900437802, 49534999175), 138119285500, (73459, 42254, 38062, 89039), 28448, (4, 11, 14, 15), (71, 59, 96, 62)⟩,
  ⟨(70538090, -29222923, 2131240, 49419019), 141076180, (98304, 51960, 66526, 88493), 28009, (0, 2, 8, 25), (67, 45, 87, 86)⟩,
  ⟨(41375057873, -44869136647, -52851923813, -20370484027), 121961487200, (87768, 41425, 37136, 54589), 28007, (2, 10, 17, 20), (63, 79, 80, 98)⟩,
  ⟨(28842588, -69620040, -1308312, -35952283), 139240080, (79111, 32768, 64920, 48614), 27963, (1, 2, 13, 18), (81, 40, 89, 8)⟩,
  ⟨(41257218224, -46705230416, -82580571330, 68078512619), 190288303500, (79745, 49450, 37094, 88982), 27707, (4, 5, 11, 15), (66, 92, 60, 69)⟩,
  ⟨(109303735, -283990750, -89180711, 229773605), 567981500, (78147, 32768, 55245, 92048), 27238, (1, 4, 9, 14), (74, 91, 62, 99)⟩,
  ⟨(1071122168, -1175853607, -1589297608, 148363658), 3177541500, (87627, 41284, 32757, 68595), 27195, (2, 4, 10, 17), (76, 94, 88, 78)⟩,
  ⟨(484300, -1169000, -334297, 944255), 2338000, (79111, 32768, 56165, 92004), 27117, (1, 2, 4, 9), (90, 97, 100, 88)⟩,
  ⟨(8274135, -19972050, -1906449, 15773975), 39944100, (79111, 32768, 62408, 91416), 27069, (1, 2, 6, 9), (90, 61, 99, 50)⟩,
  ⟨(610192400276, -164543623234, 192061633236, 1283590154246), 9871064029925, (69587, 64443, 66811, 74058), 20976, (21, 22, 23, 25), (3, 21, 6, 102)⟩,
  ⟨(-27726915617, -1528484761427, -1034549351732, 4245957828093), 26590044931650, (65467, 61768, 62986, 76000), 20569, (21, 22, 23, 24), (4, 30, 1, 101)⟩
]

set_option maxRecDepth 20000 in
private lemma cell4_ok : verifyCell ⟨4, by decide⟩ hs4 vs4 ctr4 = true := by
  decide

private def ctr5 : NVec4 := (87708, 64541, 76647, 66617)

private def hs5 : List HSData := [
  ⟨.base 0, (2, 0, 0, 0), 1⟩,
  ⟨.base 4, (0, 0, 2, 0), 1⟩,
  ⟨.base 5, (140, 140, 0, 0), 99⟩,
  ⟨.base 6, (140, -140, 0, 0), 99⟩,
  ⟨.ballA, (0, 0, 0, -2000), 746⟩,
  ⟨.ball0, (1414, 0, 0, 1414), 1254⟩,
  ⟨.ball0, (1000, 1000, 1000, 1000), 1254⟩,
  ⟨.ball0, (725, -340, 1450, 1121), 1255⟩,
  ⟨.ballA, (969, 97, -412, -1698), 936⟩,
  ⟨.ballA, (428, -977, 508, -1614), 989⟩,
  ⟨.ball0, (768, -1279, 907, 975), 1254⟩,
  ⟨.ballA, (428, -623, 987, -1566), 1018⟩,
  ⟨.ball0, (1500, 732, -404, 1025), 1254⟩,
  ⟨.ball0, (1535, 250, -653, 1074), 1254⟩,
  ⟨.ballA, (997, 2, -509, -1657), 961⟩,
  ⟨.ball0, (717, -1058, 825, 1298), 1254⟩,
  ⟨.ball0, (485, -116, 1591, 1104), 1254⟩,
  ⟨.ballA, (193, -51, 999, -1721), 921⟩,
  ⟨.ball0, (690, -1189, 1349, -539), 1255⟩,
  ⟨.ballA, (652, 761, 42, -1730), 916⟩,
  ⟨.aff 0, (-1723, 696, -680, 2302), 168⟩,
  ⟨.aff 1, (-2618, -910, 354, 229), -110⟩,
  ⟨.aff 2, (-1479, 1007, -2324, 11), -152⟩,
  ⟨.aff 4, (-689, -1245, -1471, 265), -16⟩,
  ⟨.aff 6, (-2311, 1797, 534, -259), 5⟩
]

private def vs5 : List VertData := [
  ⟨(6133446911690, 869930532593, -2660999126046, 4483647269357), 12907012152464, (96678, 69953, 52024, 88301), 34444, (13, 20, 22, 23), (97, 10, 20, 8)⟩,
  ⟨(48236078, 40035589, 62414310, -26349515), 124828620, (90860, 86554, 98304, 51702), 34441, (1, 2, 17, 24), (13, 60, 47, 53)⟩,
  ⟨(219818705893, -438199652324, 307099378676, -149990842430), 930531011620, (81017, 34674, 87164, 54972), 34397, (3, 9, 18, 21), (22, 12, 5, 67)⟩,
  ⟨(516373232561, -1138939062499, -2901944554, -4801642736844), 12873036828000, (68164, 59737, 65521, 41091), 34359, (4, 21, 22, 23), (97, 31, 7, 11)⟩,
  ⟨(6140372978228, -8833856730232, 6932613931686, 11301411955190), 27222892390313, (80318, 44269, 82225, 92742), 34342, (15, 20, 21, 23), (97, 18, 6, 9)⟩,
  ⟨(304579234767, -632717416788, 365202242987, -233483441168), 1325470012300, (80595, 34252, 83592, 53991), 34290, (3, 9, 21, 23), (7, 29, 55, 2)⟩,
  ⟨(3260157358462, -1898593112203, 861447681044, 3854104920035), 8021983143377, (92170, 50025, 72573, 97022), 34232, (5, 15, 20, 23), (4, 20, 21, 35)⟩,
  ⟨(749088055651, -1700527123864, 744874957411, -2275160590504), 6099626248000, (73584, 47265, 73539, 41091), 34049, (4, 9, 21, 23), (5, 3, 45, 32)⟩,
  ⟨(3814025848660, 1247915069630, -1357520428114, 2652685148126), 7896294365029, (97190, 75893, 54269, 87552), 34029, (12, 13, 20, 22), (0, 19, 17, 42)⟩,
  ⟨(2860702352388, -3155756815507, 5201934701086, 5619908544710), 13537601050158, (79384, 50258, 90718, 92742), 33970, (7, 15, 20, 21), (4, 28, 25, 35)⟩,
  ⟨(4665123698, 601351241, -2084746926, 2818889949), 9330247396, (98304, 69759, 50892, 85335), 33961, (0, 13, 22, 23), (0, 24, 30, 17)⟩,
  ⟨(221456831939, -269821941591, 316945726491, -3368990258818), 9032145466000, (67142, 63578, 67835, 41091), 33960, (4, 21, 22, 24), (96, 46, 41, 3)⟩,
  ⟨(111373063128, -187660772775, 185858797113, 37087281188), 422876131580, (82796, 36452, 94339, 71283), 33883, (3, 10, 18, 21), (14, 2, 29, 69)⟩,
  ⟨(380841125229, 321813979362, 463067258710, -229785605235), 993653683260, (90654, 86761, 96077, 50380), 33819, (2, 17, 19, 24), (71, 34, 1, 66)⟩,
  ⟨(1486187857, -2275065643, 2917848623, 636178886), 5835697246, (82226, 39986, 98304, 72680), 33748, (1, 10, 18, 21), (12, 37, 27, 69)⟩,
  ⟨(1315655166, 1125366483, 2892728000, 1921212175), 5785456000, (80439, 78283, 98304, 87298), 33743, (1, 6, 20, 24), (44, 40, 47, 16)⟩,
  ⟨(224323666, 186265162, 489548250, 327649933), 979096500, (80551, 78003, 98304, 87467), 33710, (1, 6, 16, 20), (57, 26, 15, 75)⟩,
  ⟨(1464459479, 471873131, -531727185, 893606088), 2928918958, (98304, 76094, 53638, 85530), 33660, (0, 12, 13, 22), (8, 10, 23, 48)⟩,
  ⟨(997929325098, -1539179441380, 1151550155888, 1503034566278), 4182563732625, (81172, 41418, 83579, 89086), 33622, (10, 15, 21, 23), (4, 29, 56, 25)⟩,
  ⟨(686850618544, 346090272680, -189435428725, 460100090876), 1460724492640, (96351, 81063, 57036, 86178), 33393, (2, 12, 20, 22), (8, 62, 23, 52)⟩,
  ⟨(2013198119606, -77429170919, -529979148908, 1677400188175), 4161488044021, (97240, 64316, 57189, 91952), 33340, (5, 13, 20, 23), (0, 6, 30, 42)⟩,
  ⟨(2420025147, -1420630749, 559685237, 2396639013), 5431230560, (94737, 48393, 72289, 94455), 33230, (3, 5, 15, 23), (6, 56, 63, 70)⟩,
  ⟨(858393609241, -1600153399620, 1491623653796, -725926850294), 3903066823748, (79949, 38667, 90581, 53347), 33167, (9, 11, 18, 21), (37, 2, 36, 67)⟩,
  ⟨(166435920, 68952024, -53830523, 93216580), 332871840, (98304, 79111, 54937, 83888), 33081, (0, 2, 12, 22), (19, 17, 39, 64)⟩,
  ⟨(7390440381, -65911794, -3779153872, -2964815845), 14780880762, (98304, 65243, 48779, 52390), 33045, (0, 14, 22, 23), (49, 10, 68, 33)⟩,
  ⟨(465082344569, -582370890655, 861949835483, 690721526060), 2039296330517, (80482, 46820, 93236, 87733), 32977, (7, 10, 15, 21), (18, 9, 27, 84)⟩,
  ⟨(1667708636, -382536893, 5489232976, 3786606586), 10978465952, (75491, 63252, 98304, 88140), 32914, (1, 16, 20, 21), (28, 40, 38, 16)⟩,
  ⟨(1511218376, -1983831861, 3178451787, 1426425280), 6356903574, (81115, 45083, 98304, 80241), 32816, (1, 7, 10, 21), (25, 14, 38, 72)⟩,
  ⟨(765707276268, -414572825783, 2129674070036, 1655528376610), 4493997807006, (76702, 59490, 96593, 89678), 32809, (7, 16, 20, 21), (26, 9, 38, 57)⟩,
  ⟨(214976865656, -374436353365, 256439763371, 172952732556), 833513643060, (82438, 36095, 85698, 79134), 32798, (3, 10, 21, 23), (18, 5, 56, 12)⟩,
  ⟨(834779645, -60925289, -204925085, 645862045), 1669559290, (98304, 63144, 57491, 90888), 32717, (0, 5, 13, 23), (20, 10, 63, 48)⟩,
  ⟨(468416093147, -105336166807, -230482045258, -663849178230), 1779756510000, (82784, 61657, 57048, 41091), 32686, (4, 8, 22, 23), (49, 3, 45, 59)⟩,
  ⟨(335678467979, -617008138136, 698752408739, -1061668046936), 2846295032000, (73265, 51329, 81624, 41091), 32552, (4, 9, 17, 21), (36, 41, 7, 79)⟩,
  ⟨(549045117, 41384651, -260733037, -226355370), 1098090234, (98304, 68005, 49974, 52026), 32385, (0, 8, 14, 22), (49, 24, 39, 77)⟩,
  ⟨(32859188007, 38417017620, 2213265883, -24032015485), 100794634220, (86900, 90514, 66975, 49910), 32374, (2, 19, 22, 24), (46, 62, 13, 43)⟩,
  ⟨(157712061448, -44197562677, 103362785774, 190603558160), 392757803928, (91852, 58161, 82783, 97340), 32242, (5, 7, 15, 20), (9, 6, 50, 73)⟩,
  ⟨(209867319389, -379895146283, 445971989471, -618688185608), 1704850629767, (73603, 50932, 82679, 41753), 32232, (9, 11, 17, 21), (58, 32, 22, 79)⟩,
  ⟨(948004933, -1421877838, 2375398514, -766422118), 4750797028, (78613, 45921, 98304, 54963), 32162, (1, 11, 18, 21), (22, 14, 58, 83)⟩,
  ⟨(313533286, -190626459, 894372082, 585111310), 1788744164, (77023, 58551, 98304, 86973), 32150, (1, 7, 16, 21), (28, 26, 27, 75)⟩,
  ⟨(276547880, 114569836, -90738173, -118507264), 553095760, (98304, 79111, 54784, 51494), 32116, (0, 2, 8, 22), (43, 33, 23, 78)⟩,
  ⟨(3837772956, 1585180086, 16208318459, 9546850138), 32416636918, (73294, 68740, 98304, 84836), 32039, (1, 20, 21, 24), (96, 60, 15, 26)⟩,
  ⟨(439561044849, -348393974001, 1865815585736, -2628488222868), 7046885316000, (69623, 62295, 82888, 41091), 31981, (4, 17, 21, 24), (60, 11, 71, 32)⟩,
  ⟨(204972585344, 45949883599, -28398849842, 161275301980), 412978080284, (98063, 72827, 61029, 91128), 31949, (5, 12, 13, 20), (8, 20, 52, 48)⟩,
  ⟨(374040675010, 208606803722, -94734714121, -205831810228), 823945929520, (95286, 82128, 58000, 49164), 31925, (2, 8, 19, 22), (59, 34, 39, 78)⟩,
  ⟨(16125946722, 18940652703, 13243709593, 13874460629), 49589130500, (86847, 90567, 83038, 83872), 31887, (2, 6, 20, 24), (15, 62, 47, 51)⟩,
  ⟨(850812727688, -632225339890, -5875548487, -943490367043), 2529464791000, (87579, 49155, 65383, 41091), 31864, (4, 8, 9, 23), (54, 7, 31, 88)⟩,
  ⟨(745472060983, 734378714640, 90320292057, -1444964657105), 3873899885000, (78147, 77959, 67063, 41091), 31860, (4, 19, 22, 24), (34, 11, 71, 59)⟩,
  ⟨(5322099, 4845201, 7189000, 673712), 14378000, (89794, 87620, 98304, 68606), 31782, (1, 2, 6, 24), (44, 15, 1, 76)⟩,
  ⟨(266536172, 58668661, -35521706, 206216812), 533072344, (98304, 72748, 61168, 90888), 31756, (0, 5, 12, 13), (42, 17, 30, 64)⟩,
  ⟨(282244307883, -13385064639, -143480597634, -164939369222), 653181023753, (93854, 64193, 51140, 48987), 31614, (8, 14, 22, 23), (24, 31, 54, 33)⟩,
  ⟨(579796784000, 79511482085, 423397920262, 634960226500), 1369749930500, (93276, 69340, 85793, 95915), 31562, (5, 6, 7, 20), (57, 35, 51, 74)⟩,
  ⟨(917998080, 432116895, 268873494, 775215420), 1909253500, (97046, 80368, 74765, 92145), 31513, (2, 5, 6, 20), (50, 44, 52, 65)⟩,
  ⟨(987843968, 455781655, 244005910, 822643612), 2041490780, (97247, 80167, 73369, 91944), 31425, (2, 5, 12, 20), (42, 19, 51, 64)⟩,
  ⟨(120470, 49909, 120470, -46979), 240940, (98304, 79111, 98304, 52757), 31398, (0, 1, 2, 17), (1, 66, 80, 76)⟩,
  ⟨(88314766523, -60928654505, -314485817, -71338056073), 214667218635, (92497, 46935, 65439, 43757), 31325, (8, 9, 14, 23), (55, 49, 45, 61)⟩,
  ⟨(201563937759, -138319500300, -486377801, -157494258244), 480643245740, (93019, 46676, 65469, 44061), 31325, (3, 9, 14, 23), (54, 68, 5, 61)⟩,
  ⟨(327526804, -327661235, 192495964, 324772969), 926528540, (88702, 42359, 79151, 88508), 31283, (3, 10, 15, 23), (18, 21, 29, 84)⟩,
  ⟨(406984064312, 138176587781, 525792632076, 510177110840), 1260869533500, (86689, 72717, 92865, 92053), 31274, (6, 7, 16, 20), (28, 16, 50, 75)⟩,
  ⟨(903096758, -1057174601, 2970608287, -1322492276), 5941216574, (75497, 53874, 98304, 50947), 31267, (1, 11, 17, 21), (36, 60, 37, 80)⟩,
  ⟨(215436512870, 96350609342, -45547408651, -291932924508), 782661996000, (83575, 73603, 61722, 41091), 31204, (4, 8, 19, 22), (43, 46, 31, 92)⟩,
  ⟨(2461298251, -1043878395, 11743441368, -5445353116), 23486882736, (72403, 62623, 98304, 50341), 31177, (1, 17, 21, 24), (41, 40, 1, 58)⟩,
  ⟨(20530313224, -13796101910, 213855229, -15882301549), 48542405240, (93253, 46910, 65824, 44093), 31084, (3, 8, 9, 14), (54, 55, 77, 86)⟩,
  ⟨(550568439918, 736748323947, 89568885202, 348651036431), 1820447948900, (85356, 92058, 68760, 78087), 30929, (2, 20, 22, 24), (96, 34, 44, 19)⟩,
  ⟨(10399970, -4308559, 451165, 8046370), 20799940, (98304, 51960, 66957, 90888), 30882, (0, 3, 5, 23), (21, 30, 68, 70)⟩,
  ⟨(1428140, 591658, 312109, 1104940), 2856280, (98304, 79111, 72697, 90888), 30486, (0, 2, 5, 12), (52, 48, 23, 65)⟩,
  ⟨(176750, 73225, 56564, 136750), 353500, (98304, 79111, 76022, 90888), 30235, (0, 2, 5, 6), (51, 74, 76, 64)⟩,
  ⟨(115919160, 48023652, 98078719, -55560291), 231838320, (98304, 79111, 93260, 49830), 29707, (0, 2, 17, 19), (13, 95, 78, 53)⟩,
  ⟨(41669861255, -46884360556, 44563780908, -23278538266), 125228192460, (87343, 40999, 88857, 53353), 29656, (3, 9, 11, 18), (22, 91, 2, 94)⟩,
  ⟨(180063240, -74597628, -33553565, -90301103), 360126480, (98304, 51960, 59429, 49102), 29562, (0, 3, 14, 23), (55, 24, 63, 77)⟩,
  ⟨(21686482, -16030241, 26668390, 5680201), 53336780, (92182, 45839, 98304, 72515), 29559, (1, 3, 10, 18), (12, 14, 85, 72)⟩,
  ⟨(530250, -219675, 223948, 410250), 1060500, (98304, 51960, 79375, 90888), 29448, (0, 3, 5, 15), (21, 73, 82, 63)⟩,
  ⟨(655534626837, 469710642906, 739271743630, -1124205257895), 3013955115000, (79790, 75749, 81610, 41091), 29405, (4, 17, 19, 24), (13, 46, 41, 92)⟩,
  ⟨(55838171, -38034223, 66374420, 15113805), 132748840, (93102, 46759, 98304, 72997), 29243, (1, 3, 7, 10), (84, 27, 69, 81)⟩,
  ⟨(443147600, -135634175, 248660162, 342859600), 886295200, (98304, 55506, 83922, 90888), 28914, (0, 5, 7, 15), (35, 82, 70, 74)⟩,
  ⟨(31638250, 2599205, 20633026, 24478250), 63276500, (98304, 68228, 86905, 90888), 28641, (0, 5, 6, 7), (50, 87, 73, 65)⟩,
  ⟨(3850138, 1120455, 5014750, 2591650), 10029500, (90694, 72857, 98304, 82470), 28258, (1, 6, 7, 16), (57, 38, 16, 87)⟩,
  ⟨(1750, 725, 1750, 164), 3500, (98304, 79111, 98304, 68606), 28243, (0, 1, 2, 6), (47, 65, 87, 53)⟩,
  ⟨(12711860, -5266342, -643873, -6904811), 25423720, (98304, 51960, 63876, 47737), 28111, (0, 3, 8, 14), (61, 33, 68, 86)⟩,
  ⟨(27442660, 11369102, -852586, -13737723), 54885320, (98304, 79111, 64517, 49132), 27885, (0, 2, 8, 19), (43, 95, 66, 39)⟩,
  ⟨(10087112705, -5980947326, 8022443756, -13721851265), 36787805000, (83505, 54881, 79827, 41091), 27799, (4, 9, 11, 17), (36, 89, 32, 88)⟩,
  ⟨(992317, -50841, 992317, -373279), 1984634, (98304, 63857, 98304, 53209), 27598, (0, 1, 11, 17), (58, 93, 53, 83)⟩,
  ⟨(78470, -32509, 78470, 13590), 156940, (98304, 51960, 98304, 71210), 27583, (0, 1, 3, 7), (72, 82, 87, 85)⟩,
  ⟨(6091750, -2523725, 3931052, 3849850), 12183500, (98304, 51960, 86681, 86244), 27506, (0, 3, 7, 15), (84, 73, 70, 81)⟩,
  ⟨(1526177, -402867, 1526177, -444936), 3052354, (98304, 56886, 98304, 55982), 27443, (0, 1, 11, 18), (37, 91, 85, 80)⟩,
  ⟨(3112286879, -1363955254, 2090996651, 1955487515), 6330039380, (97758, 51414, 87184, 85781), 27418, (3, 7, 10, 15), (25, 56, 82, 72)⟩,
  ⟨(37730, -15631, 37730, 1511), 75460, (98304, 51960, 98304, 66848), 27198, (0, 1, 3, 18), (69, 91, 83, 81)⟩,
  ⟨(8910720, -3691584, 2463537, -5547374), 17821440, (98304, 51960, 74595, 45136), 27135, (0, 3, 8, 9), (61, 90, 94, 77)⟩,
  ⟨(121750, 19539, 121750, 42310), 243500, (98304, 70794, 98304, 76923), 26958, (0, 1, 6, 7), (75, 74, 81, 76)⟩,
  ⟨(287047488840, -86210712374, 133240907692, -264845607439), 710041843000, (92030, 57578, 77833, 41091), 26837, (4, 8, 9, 11), (90, 79, 89, 45)⟩,
  ⟨(250965562481, -66650096615, 120706450615, -230457657977), 617848949000, (92156, 58466, 78339, 41091), 26669, (4, 8, 11, 17), (93, 79, 92, 88)⟩,
  ⟨(1393423920, -421295814, 570621252, -903547379), 2786847840, (98304, 55628, 78954, 44288), 26377, (0, 8, 9, 11), (88, 94, 93, 86)⟩,
  ⟨(110637870, -45835689, 94579427, -35760004), 221275740, (98304, 51960, 93547, 54944), 26316, (0, 3, 11, 18), (67, 83, 85, 94)⟩,
  ⟨(298820461118, 2585267464, 152069272705, -279960452195), 750564215000, (91627, 65761, 78814, 41091), 25946, (4, 8, 17, 19), (95, 71, 59, 89)⟩,
  ⟨(1367141803, -161461929, 691141113, -903969961), 2734283606, (98304, 61666, 82101, 43869), 25843, (0, 8, 11, 17), (89, 80, 95, 90)⟩,
  ⟨(11164860, -4625442, 5394036, -6224477), 22329720, (98304, 51960, 81367, 47267), 25834, (0, 3, 9, 11), (67, 90, 91, 86)⟩,
  ⟨(1709831434, 50019232, 890940499, -1122610957), 3419662868, (98304, 66494, 82610, 44021), 25736, (0, 8, 17, 19), (92, 66, 78, 93)⟩,
  ⟨(579126143596, 738747226134, 873278486207, 1488700944530), 13985082902742, (68249, 68997, 69628, 72512), 21969, (20, 21, 22, 24), (11, 62, 40, 97)⟩,
  ⟨(610192400276, -164543623234, 192061633236, 1283590154246), 9871064029925, (69587, 64443, 66811, 74058), 21922, (20, 21, 22, 23), (3, 0, 4, 96)⟩
]

set_option maxRecDepth 20000 in
private lemma cell5_ok : verifyCell ⟨5, by decide⟩ hs5 vs5 ctr5 = true := by
  decide

private def ctr6 : NVec4 := (56269, 84447, 84584, 63299)

private def hs6 : List HSData := [
  ⟨.base 1, (-2, 0, 0, 0), 1⟩,
  ⟨.base 2, (0, 2, 0, 0), 1⟩,
  ⟨.base 4, (0, 0, 2, 0), 1⟩,
  ⟨.base 5, (140, 140, 0, 0), 99⟩,
  ⟨.ball0, (1000, 1000, 1000, 1000), 1254⟩,
  ⟨.ball0, (314, 237, 1515, 1245), 1255⟩,
  ⟨.ballA, (-195, 936, -263, -1737), 912⟩,
  ⟨.ballA, (-865, 214, 876, -1562), 1021⟩,
  ⟨.ballA, (-284, 998, -270, -1688), 942⟩,
  ⟨.ballA, (603, 804, 72, -1728), 917⟩,
  ⟨.ball0, (-1366, 292, 1282, 636), 1254⟩,
  ⟨.ballA, (-884, 137, 812, -1594), 1001⟩,
  ⟨.ball0, (-1473, 170, 1227, -543), 1254⟩,
  ⟨.ballA, (-171, 7, 6, -1993), 751⟩,
  ⟨.ball0, (41, 1115, 1101, 1242), 1254⟩,
  ⟨.ball0, (-1231, 344, 1228, 926), 1254⟩,
  ⟨.ballA, (101, -77, 509, -1930), 790⟩,
  ⟨.ball0, (-752, 1411, 329, 1155), 1254⟩,
  ⟨.ball0, (-1078, 390, 1152, 1166), 1255⟩,
  ⟨.aff 0, (588, -1101, -1214, 2561), 163⟩,
  ⟨.aff 1, (-307, -2707, -180, 488), -115⟩,
  ⟨.aff 2, (832, -790, -2858, 270), -157⟩,
  ⟨.aff 3, (-757, -2542, -2766, 359), -44⟩,
  ⟨.aff 5, (2311, -1797, -534, 259), -5⟩,
  ⟨.aff 7, (-1530, -742, -1635, 445), -2⟩
]

private def vs6 : List VertData := [
  ⟨(76425824, 63096163, 98651910, -44566307), 197303820, (90921, 86493, 98304, 50732), 39386, (2, 3, 9, 23), (1, 2, 8, 35)⟩,
  ⟨(424966853680, 496809610049, 28603523140, -311099844013), 1303522271940, (86901, 90513, 66974, 49895), 38276, (3, 9, 21, 23), (7, 5, 0, 6)⟩,
  ⟨(785256526, 588487719, 1140855723, -615471049), 2281711446, (88090, 82438, 98304, 47858), 37993, (2, 9, 16, 23), (14, 23, 0, 72)⟩,
  ⟨(16125946722, 18940652703, 13243709593, 13874460629), 49589130500, (86847, 90567, 83038, 83872), 37393, (3, 4, 19, 23), (9, 5, 8, 12)⟩,
  ⟨(101377591, 244704530, -587226, 112795958), 489409060, (79111, 98304, 65457, 80640), 37155, (1, 3, 19, 21), (5, 24, 6, 12)⟩,
  ⟨(550568439918, 736748323947, 89568885202, 348651036431), 1820447948900, (85356, 92058, 68760, 78087), 37057, (3, 19, 21, 23), (73, 1, 3, 4)⟩,
  ⟨(71328168, 172171440, -15314643, -78372889), 344342880, (79111, 98304, 62621, 50619), 36839, (1, 3, 9, 21), (1, 15, 4, 35)⟩,
  ⟨(367600077118, 346173576821, 48884437999, -817744322215), 2090041734558, (77062, 76390, 67068, 39894), 36770, (9, 13, 21, 23), (10, 1, 14, 25)⟩,
  ⟨(5322099, 4845201, 7189000, 673712), 14378000, (89794, 87620, 98304, 68606), 36750, (2, 3, 4, 23), (3, 11, 0, 44)⟩,
  ⟨(2017796547098, 1812165650069, 4064475975030, 2784496293365), 8515896703000, (81064, 79481, 96815, 86964), 36732, (4, 5, 19, 23), (13, 3, 11, 21)⟩,
  ⟨(438598814906, -557349338532, 627009559671, -6836073103894), 18041483236618, (67129, 63511, 67813, 40703), 36719, (13, 20, 21, 23), (73, 7, 18, 17)⟩,
  ⟨(487208296, 421646613, 995638000, 592567195), 1991276000, (81570, 79413, 98304, 85038), 36421, (2, 4, 5, 23), (9, 13, 8, 31)⟩,
  ⟨(2736875, 6606250, 2830804, 4394546), 13212500, (79111, 98304, 79577, 87333), 36286, (1, 3, 4, 19), (3, 16, 4, 44)⟩,
  ⟨(1791771138, 1393932589, 4574389110, 2938585545), 9148778220, (78371, 75521, 98304, 86586), 36040, (2, 5, 19, 23), (9, 22, 11, 32)⟩,
  ⟨(307932924994, 274931886977, 97049521565, -673183444495), 1719713575290, (77270, 76013, 69234, 39881), 36005, (9, 13, 16, 23), (18, 2, 7, 78)⟩,
  ⟨(273509154, 1119431961, -161474976, -578538830), 2238863922, (73542, 98304, 60809, 48601), 35663, (1, 6, 9, 21), (25, 6, 27, 79)⟩,
  ⟨(367106273, 1063895500, 494376715, 742871426), 2127791000, (76842, 98304, 80762, 88416), 35509, (1, 4, 14, 19), (21, 38, 12, 53)⟩,
  ⟨(-1457182359212, -317724710630, 56446259133, -7303304123678), 19710756200394, (60691, 64479, 65723, 41253), 35499, (13, 20, 21, 22), (36, 19, 20, 10)⟩,
  ⟨(7765781806, -8105957409, 22161673859, -84118233182), 221565803441, (67833, 63138, 72091, 40655), 35451, (13, 16, 20, 23), (23, 10, 14, 48)⟩,
  ⟨(-1758000018479, 90482954314, -175248851475, -6618110634719), 17962842058224, (59122, 65866, 64896, 41390), 34945, (13, 21, 22, 24), (36, 20, 29, 17)⟩,
  ⟨(-609666170374, -66421763263, 51075231280, -2044254985228), 5563641277947, (58354, 64753, 66137, 41456), 34782, (13, 20, 22, 24), (36, 19, 41, 17)⟩,
  ⟨(464151631169, 731847285067, 1245544048064, 971731519231), 2721909476500, (76711, 83156, 95525, 88932), 34590, (4, 5, 14, 19), (34, 16, 9, 31)⟩,
  ⟨(3837772956, 1585180086, 16208318459, 9546850138), 32416636918, (73294, 68740, 98304, 84836), 34479, (2, 19, 20, 23), (73, 23, 13, 28)⟩,
  ⟨(2743434281, -1353326829, 13213785594, -7135062872), 26427571188, (72339, 62179, 98304, 47842), 34372, (2, 16, 20, 23), (18, 22, 2, 49)⟩,
  ⟨(-559717926, 3554910895, -581794789, 1833531087), 7109821790, (60376, 98304, 60173, 82436), 34222, (1, 19, 21, 24), (77, 26, 33, 4)⟩,
  ⟨(346688673526, 1335547606069, -175065403269, -1888628349215), 4944142446918, (70131, 83239, 63215, 40501), 34207, (6, 9, 13, 21), (7, 29, 15, 78)⟩,
  ⟨(-372367654, 1265591165, -370425241, -542385393), 2531182330, (55894, 98304, 55945, 51492), 33940, (1, 8, 21, 24), (30, 24, 47, 27)⟩,
  ⟨(-25171592, 123981149, -33222501, -55526357), 247962298, (58883, 98304, 56755, 50860), 33588, (1, 6, 8, 21), (30, 26, 15, 92)⟩,
  ⟨(-1708426141, 944280799, 4781384575, 3673385387), 9562769150, (53827, 72007, 98304, 90710), 33173, (2, 18, 19, 20), (39, 22, 45, 32)⟩,
  ⟨(-1560509542204, 2900195731397, -1014280009953, -4309218540949), 11810033786802, (56876, 81629, 59907, 41623), 32973, (6, 13, 21, 24), (19, 30, 67, 25)⟩,
  ⟨(-72872998492, 228459805551, -68298940839, -122819378507), 503671594966, (56054, 95262, 56649, 49555), 32961, (6, 8, 21, 24), (26, 29, 67, 27)⟩,
  ⟨(89397767, 156512011, 273092750, 165914089), 546185500, (76262, 84315, 98304, 85443), 32840, (2, 4, 5, 14), (21, 37, 53, 11)⟩,
  ⟨(-33488928, 40743521, 123894138, 99706005), 247788276, (56678, 76312, 98304, 91906), 32758, (2, 5, 18, 19), (34, 28, 13, 37)⟩,
  ⟨(-2753679457, 7373478470, 618758404, 5034084342), 14746956940, (53298, 98304, 68285, 87907), 32745, (1, 17, 19, 24), (40, 24, 57, 38)⟩,
  ⟨(-85208328545, 125180999525, 321314094848, 267413542179), 655484617874, (57016, 78051, 97661, 92272), 32435, (5, 14, 18, 19), (42, 32, 21, 37)⟩,
  ⟨(50112, 120960, 120960, -49573), 241920, (79111, 98304, 98304, 52106), 32054, (1, 2, 3, 9), (0, 6, 70, 44)⟩,
  ⟨(-487613700077, -5927184485, 12527931447, -1665747491723), 5646934863450, (59876, 65467, 65681, 46204), 31984, (20, 21, 22, 24), (19, 20, 77, 17)⟩,
  ⟨(-17246446, 25611457, 65629523, 51925176), 131259046, (56925, 78323, 98304, 91461), 31928, (2, 5, 14, 18), (34, 84, 32, 31)⟩,
  ⟨(-55533761, 550534529, 220351764, 423964727), 1101069058, (62230, 98304, 78651, 90770), 31899, (1, 14, 17, 19), (42, 33, 16, 83)⟩,
  ⟨(-10381530761659, 3765389863097, 11096191143523, 11215871424177), 30693474490522, (43369, 73575, 89228, 89483), 31495, (18, 19, 20, 24), (77, 43, 40, 28)⟩,
  ⟨(-5564011650563, 5541995119966, 4599529152518, 6932861181540), 17164746117506, (44292, 86695, 83097, 92006), 31224, (17, 18, 19, 24), (39, 33, 63, 42)⟩,
  ⟨(-4081603156928, 27017702659, 2600481953180, -4491591040736), 12870155924979, (44752, 65673, 78777, 42664), 30737, (11, 13, 20, 24), (20, 50, 66, 48)⟩,
  ⟨(-1887520719423, 2734261631919, 2609282943612, 3353780931977), 7982081187022, (50038, 87985, 86959, 93071), 30716, (14, 17, 18, 19), (40, 34, 38, 80)⟩,
  ⟨(-1273514113826, 416237822368, 1324546735577, 1166203595343), 3522591392018, (41842, 73279, 90178, 87232), 30612, (15, 18, 20, 24), (39, 51, 63, 45)⟩,
  ⟨(725, 1750, 1750, 164), 3500, (79111, 98304, 98304, 68606), 30501, (1, 2, 3, 4), (8, 12, 53, 35)⟩,
  ⟨(-324855214, 118209504, 624432639, 387378985), 1248865278, (48488, 71739, 98304, 85864), 30325, (2, 15, 18, 20), (43, 28, 55, 84)⟩,
  ⟨(-80150, 80150, 29947, -32619), 160300, (32768, 98304, 77779, 52200), 30232, (0, 1, 7, 24), (47, 76, 57, 56)⟩,
  ⟨(-2374931202, 2392145295, 871721597, -995453259), 4784290590, (33003, 98304, 77476, 51900), 30231, (1, 7, 8, 24), (68, 26, 46, 92)⟩,
  ⟨(-282112135756, -10322330819, 284496746827, -388258983130), 1096772373845, (48678, 64919, 82535, 42336), 29711, (11, 13, 16, 20), (18, 49, 41, 93)⟩,
  ⟨(-1692807698, -246333370, 5199596762, -2964131627), 10399193524, (54867, 63983, 98304, 46855), 29657, (2, 11, 16, 20), (48, 23, 64, 54)⟩,
  ⟨(-1626314247648, 137380086375, 1301396799900, -596544502672), 3460648357175, (34737, 68137, 90181, 54238), 29038, (11, 12, 20, 24), (52, 41, 75, 59)⟩,
  ⟨(-788815252484, 205927266679, 776315206017, 474837456355), 1941694667559, (38911, 72486, 91738, 81562), 28796, (10, 15, 20, 24), (43, 52, 69, 55)⟩,
  ⟨(-3294530367282, 486862365387, 2901064693521, 113281579795), 6725442036877, (33432, 70280, 93805, 66639), 28610, (10, 12, 20, 24), (50, 51, 71, 61)⟩,
  ⟨(84734, 300250, 300250, 67793), 600500, (74783, 98304, 98304, 72934), 28566, (1, 2, 4, 14), (31, 16, 86, 44)⟩,
  ⟨(-47057630, 532786, 149388198, -85382697), 298776396, (55214, 65652, 98304, 46807), 28543, (2, 7, 11, 16), (93, 49, 72, 64)⟩,
  ⟨(-445156682, 119736442, 687259116, 313730515), 1374518232, (44311, 71244, 98304, 80494), 28308, (2, 10, 15, 20), (51, 45, 61, 88)⟩,
  ⟨(-1440906, 1440906, 828221, -423861), 2881812, (32768, 98304, 84370, 55896), 28272, (0, 1, 7, 12), (89, 76, 65, 46)⟩,
  ⟨(-2034830, 2034830, 1068285, 303507), 4069660, (32768, 98304, 82739, 70423), 28259, (0, 1, 17, 24), (33, 62, 46, 60)⟩,
  ⟨(-3658078356, 214053174, 4920650447, -1618075073), 9841300894, (41175, 66961, 98304, 54760), 28194, (2, 7, 12, 20), (59, 61, 64, 89)⟩,
  ⟨(-136884576978, 8599942446, 170542995519, -59015756803), 354381805064, (40221, 67126, 97074, 54622), 28089, (7, 11, 12, 20), (50, 58, 64, 75)⟩,
  ⟨(-635733, 635733, 381165, 81320), 1271466, (32768, 98304, 85182, 69727), 28038, (0, 1, 10, 17), (87, 62, 57, 65)⟩,
  ⟨(-2037514727, 282887457, 2361160471, 45494470), 4722320942, (37259, 69461, 98304, 66167), 27974, (2, 10, 12, 20), (52, 58, 55, 81)⟩,
  ⟨(-1310730631, 1227213792, 749079011, 280170851), 2621461262, (32768, 96216, 84262, 72540), 27864, (0, 10, 17, 24), (69, 57, 71, 60)⟩,
  ⟨(-661982601466, 598695981230, 476272981957, 464849191743), 1623736501870, (38817, 89700, 84758, 84297), 27807, (15, 17, 18, 24), (40, 43, 69, 80)⟩,
  ⟨(-19743726, 263170, 34052658, -14449909), 68105316, (46537, 65789, 98304, 51631), 27701, (2, 7, 11, 20), (59, 49, 58, 54)⟩,
  ⟨(-738249, 738249, 505845, -32990), 1476498, (32768, 98304, 87988, 64071), 27506, (0, 1, 10, 12), (81, 71, 56, 60)⟩,
  ⟨(-982788499776, 786961794719, 310908499148, -936728814304), 2719482748239, (41852, 84500, 73028, 42962), 27479, (8, 11, 13, 24), (41, 67, 68, 74)⟩,
  ⟨(-2864922120, 2446031446, 775548495, -2960515913), 8537929971, (43545, 84311, 71489, 42811), 27446, (6, 8, 13, 24), (66, 29, 30, 74)⟩,
  ⟨(-104115030325, 92139557143, 35744895498, -74132004064), 251600475283, (38416, 89536, 74846, 46226), 27038, (7, 8, 11, 24), (66, 75, 47, 82)⟩,
  ⟨(-24532206892, 22109211534, 15819271457, 10401412377), 53319368949, (35382, 92710, 84979, 78320), 27027, (10, 15, 17, 24), (63, 62, 51, 87)⟩,
  ⟨(-74330, 1218303, 1218303, -701363), 2436606, (63536, 98304, 98304, 46671), 26640, (1, 2, 7, 9), (72, 79, 35, 89)⟩,
  ⟨(-360999668, 103955751, 293781094, 8300596), 721999336, (32768, 74972, 92202, 66289), 26630, (0, 10, 12, 24), (52, 76, 62, 65)⟩,
  ⟨(-37909406, 881711005, 934199589, -555569097), 1868399178, (64206, 96462, 98304, 46048), 26331, (2, 7, 9, 16), (91, 2, 54, 70)⟩,
  ⟨(579126143596, 738747226134, 873278486207, 1488700944530), 13985082902742, (68249, 68997, 69628, 72512), 26285, (19, 20, 21, 23), (10, 5, 22, 77)⟩,
  ⟨(-10367548094, 9496405671, 4474133172, -10929014266), 31488276691, (43958, 85300, 74847, 42789), 25843, (6, 8, 11, 13), (66, 90, 67, 82)⟩,
  ⟨(-141995907450, 50470618422, 96822295809, -49617537065), 289859056132, (33431, 76947, 87427, 54317), 25820, (7, 11, 12, 24), (50, 76, 68, 59)⟩,
  ⟨(-387203406, 186422442, 243370643, -129738363), 774406812, (32768, 81312, 86131, 54556), 25319, (0, 7, 12, 24), (75, 71, 46, 56)⟩,
  ⟨(-1270229377173, 2294717854587, 1316439905821, 4137879816671), 35126214313802, (63166, 69817, 67992, 73256), 25222, (19, 20, 21, 24), (36, 24, 39, 73)⟩,
  ⟨(-3703788933, 92009114588, 52038300051, -104244598390), 278760487485, (64665, 87167, 77770, 41028), 24908, (6, 9, 13, 16), (14, 94, 91, 25)⟩,
  ⟨(-156654538, 969893127, 800388255, -599435563), 1939786254, (60243, 98304, 92577, 45283), 24421, (1, 6, 7, 9), (91, 70, 15, 92)⟩,
  ⟨(-168187495856, 262099259969, 257371600941, 140956198140), 593124974690, (46952, 94496, 93973, 81110), 24358, (14, 15, 17, 18), (63, 42, 84, 83)⟩,
  ⟨(-606879, 839283, 839283, -70922), 1678566, (41841, 98304, 98304, 62767), 24265, (1, 2, 10, 12), (61, 65, 89, 86)⟩,
  ⟨(-90646769, 97291699, 51902340, -99948441), 294628593, (45372, 87177, 77080, 43303), 24134, (6, 7, 8, 11), (68, 74, 90, 92)⟩,
  ⟨(-870945520, 1488308473, 1415319429, 443362140), 2976616946, (46360, 98304, 96697, 75297), 24104, (1, 14, 15, 17), (80, 87, 38, 85)⟩,
  ⟨(-82980408, 131085621, 176663329, 85190848), 353326658, (50144, 89850, 98304, 81337), 24092, (2, 14, 15, 18), (80, 45, 37, 88)⟩,
  ⟨(-122027090, 211997516, 207897608, 57504335), 423995032, (46674, 98304, 97670, 74424), 24067, (1, 10, 14, 15), (88, 83, 87, 86)⟩,
  ⟨(-162386, 287108, 287108, 72861), 574216, (47002, 98304, 98304, 73851), 24033, (1, 2, 10, 14), (88, 85, 53, 81)⟩,
  ⟨(-80996890, 130762839, 121434632, 36870285), 261525678, (45238, 98304, 95966, 74775), 23981, (1, 10, 15, 17), (69, 83, 60, 85)⟩,
  ⟨(-112962478, 197082364, 201182272, 54708601), 402364544, (47136, 97636, 98304, 74446), 23874, (2, 10, 14, 15), (85, 84, 55, 86)⟩,
  ⟨(-1218446, 1831131, 1831131, -441281), 3662262, (43731, 98304, 98304, 57639), 23866, (1, 2, 7, 12), (58, 56, 81, 70)⟩,
  ⟨(-13822893357, 15871105399, 9411652038, -17565196611), 49984979041, (47412, 86344, 77875, 42506), 23654, (6, 7, 11, 13), (93, 74, 94, 82)⟩,
  ⟨(-27090214666, 158589563939, 135251957811, -113903286711), 346492508574, (60412, 95531, 91117, 43992), 23570, (6, 7, 9, 16), (72, 78, 94, 79)⟩,
  ⟨(-35163186, 99944021, 70686255, -57849139), 199888042, (54007, 98304, 88711, 46569), 22230, (1, 6, 7, 8), (82, 47, 27, 79)⟩,
  ⟨(-19969531155, 23035075529, 26723155812, -35322080193), 98712756479, (52278, 80829, 83277, 42085), 21928, (7, 11, 13, 16), (48, 94, 54, 90)⟩,
  ⟨(-92140613523, 189574232206, 148510351155, -196884128844), 546423695647, (54485, 88272, 83347, 41922), 21827, (6, 7, 13, 16), (93, 78, 91, 90)⟩
]

set_option maxRecDepth 20000 in
private lemma cell6_ok : verifyCell ⟨6, by decide⟩ hs6 vs6 ctr6 = true := by
  decide

private def ctr7 : NVec4 := (42946, 75260, 62478, 69788)

private def hs7 : List HSData := [
  ⟨.base 1, (-2, 0, 0, 0), 1⟩,
  ⟨.base 2, (0, 2, 0, 0), 1⟩,
  ⟨.ball0, (-1342, 438, 1264, 641), 1255⟩,
  ⟨.ballA, (-91, -23, 44, -1997), 748⟩,
  ⟨.ballA, (-803, 194, 808, -1632), 977⟩,
  ⟨.ballA, (-989, -509, 97, -1659), 960⟩,
  ⟨.ball0, (-1000, 938, 79, 1454), 1255⟩,
  ⟨.ball0, (-899, 519, -1515, 793), 1255⟩,
  ⟨.ball0, (-703, 1482, -1026, -506), 1254⟩,
  ⟨.ballA, (-460, 970, -671, -1548), 1030⟩,
  ⟨.ball0, (-759, 463, -1214, 1317), 1254⟩,
  ⟨.ball0, (-696, 819, -1075, 1300), 1255⟩,
  ⟨.ball0, (-1473, 170, 1227, -543), 1254⟩,
  ⟨.ball0, (-1027, 538, -1540, -531), 1254⟩,
  ⟨.ball0, (-371, 1593, -511, 1032), 1255⟩,
  ⟨.ball0, (-1095, 348, 1104, 1209), 1255⟩,
  ⟨.ballA, (-937, 84, 752, -1596), 999⟩,
  ⟨.ballA, (-303, 998, -325, -1675), 950⟩,
  ⟨.ball0, (-1291, -543, 58, 1427), 1255⟩,
  ⟨.ballA, (-639, 370, -952, -1596), 999⟩,
  ⟨.aff 0, (2118, -359, 421, 2116), 165⟩,
  ⟨.aff 1, (1223, -1965, 1455, 43), -113⟩,
  ⟨.aff 2, (2362, -48, -1223, -175), -155⟩,
  ⟨.aff 3, (773, -1800, -1131, -86), -42⟩,
  ⟨.aff 6, (1530, 742, 1635, -445), 2⟩
]

private def vs7 : List VertData := [
  ⟨(-67728019419, -4559881075, -39419498093, 88118841150), 170017644562, (39429, 63778, 50341, 99502), 34272, (10, 18, 20, 23), (12, 31, 46, 32)⟩,
  ⟨(-2308760, 2308760, 866679, -924759), 4617520, (32768, 98304, 77836, 52410), 34244, (0, 1, 4, 24), (6, 62, 45, 7)⟩,
  ⟨(-1826329816823, -202350680948, 155028086299, -6121617481739), 16580937735057, (58317, 64736, 66148, 41340), 34204, (3, 21, 23, 24), (58, 3, 16, 15)⟩,
  ⟨(-1748412191871, 92569395688, -179377059907, -6596145778275), 17809608211148, (59102, 65876, 64875, 41263), 34185, (3, 22, 23, 24), (58, 2, 27, 33)⟩,
  ⟨(-73359896692, 136245917914, -118047348677, 45713170232), 280282434871, (48382, 97393, 37934, 76224), 34109, (7, 8, 14, 22), (8, 9, 24, 75)⟩,
  ⟨(-8215638207647, -822702870666, 4064403667346, 8752627933861), 18947292477426, (37119, 62690, 79594, 95810), 34091, (15, 18, 20, 21), (12, 13, 14, 47)⟩,
  ⟨(-2191131440, 2248954735, 772742554, -964648164), 4497909470, (33610, 98304, 76795, 51480), 34037, (1, 4, 17, 24), (65, 25, 1, 7)⟩,
  ⟨(-1883800, 1883800, 625407, -795017), 3767600, (32768, 98304, 76414, 51706), 33999, (0, 1, 4, 17), (6, 83, 71, 1)⟩,
  ⟨(-2134686958, 4224817307, -3403870619, 1301173181), 8449634614, (48979, 98304, 39135, 75627), 33861, (1, 8, 14, 22), (4, 22, 29, 82)⟩,
  ⟨(-276109737920, 508678280150, -445677277765, 196340818480), 1070219941559, (48628, 96685, 38244, 77559), 33751, (7, 11, 14, 22), (23, 4, 54, 75)⟩,
  ⟨(-6629556080754, 564748793088, 5311055027829, -2401805586349), 14100628671698, (34723, 68160, 90220, 54373), 33547, (12, 16, 21, 24), (49, 11, 56, 18)⟩,
  ⟨(-6723363977562, 1010891502261, 5942377544413, 340941867311), 13701381584831, (33377, 70371, 93959, 67166), 33370, (2, 12, 21, 24), (10, 26, 53, 17)⟩,
  ⟨(-11676722553236, -5120767076877, 257168652818, 13033764946132), 29059222070889, (39201, 53987, 66115, 94930), 33347, (18, 20, 21, 23), (94, 37, 0, 5)⟩,
  ⟨(-10368693455489, 3759079797463, 11082507306313, 11199508337251), 30627229282218, (43349, 73579, 89250, 89500), 33293, (15, 20, 21, 24), (93, 26, 28, 5)⟩,
  ⟨(-4608977547, -652824314, 2170121610, 3600555693), 9217955094, (32768, 60894, 80964, 91134), 33279, (0, 15, 18, 21), (5, 37, 48, 69)⟩,
  ⟨(-3493312541102, -1301081465339, 415910204068, -4079225341205), 11380119479022, (45418, 58043, 67931, 42044), 33198, (3, 5, 21, 23), (39, 2, 55, 20)⟩,
  ⟨(-3772969272427, 985346312, 2336936521715, -4440275763795), 12451034021497, (45676, 65541, 77836, 42164), 33181, (3, 4, 21, 24), (49, 2, 65, 19)⟩,
  ⟨(-3412637233, 425023950, 2906618633, 196308652), 6825274466, (32768, 69617, 93445, 67420), 33168, (0, 2, 12, 21), (11, 18, 48, 53)⟩,
  ⟨(-3375133876, -2620458, 2342871571, -1139973521), 6750267752, (32768, 65510, 88282, 54468), 33157, (0, 12, 16, 21), (10, 38, 17, 64)⟩,
  ⟨(-170179691261, -9465078988, 94474109957, -189692162025), 532989514871, (44610, 64372, 77152, 42211), 33125, (3, 4, 16, 21), (49, 20, 16, 80)⟩,
  ⟨(-1598918212578, -201527272599, 753486251796, -1683369532565), 4739276786398, (43425, 62749, 75955, 42257), 33113, (3, 5, 16, 21), (38, 19, 15, 72)⟩,
  ⟨(-3742529395, 8075759410, 1510453964, 6075129666), 16151518820, (50350, 98304, 71664, 90186), 32961, (1, 6, 20, 24), (28, 52, 41, 35)⟩,
  ⟨(-1771415428, 7375568577, -2509929919, 4674057241), 14751137154, (57665, 98304, 54384, 86301), 32955, (1, 14, 20, 22), (23, 52, 8, 35)⟩,
  ⟨(-1209675153650, 2833234823565, -1947583393570, 2616948860185), 6898835771927, (54044, 92450, 47034, 90395), 32894, (11, 14, 20, 22), (22, 42, 9, 61)⟩,
  ⟨(-444406760908, 535679346798, -706849304405, 65081184842), 1434283135297, (45229, 90012, 33238, 68509), 32857, (7, 8, 13, 22), (34, 43, 4, 85)⟩,
  ⟨(-26555660, 90259465, -26417180, -38675874), 180518930, (55895, 98304, 55945, 51495), 32805, (1, 17, 22, 24), (27, 52, 6, 30)⟩,
  ⟨(-2815397558662, 828004691939, 2855588779819, 2159890535273), 7278791736729, (40187, 72991, 91246, 84982), 32731, (2, 15, 21, 24), (13, 11, 51, 48)⟩,
  ⟨(-1805561231414, 3418112103571, -1206941261027, -5003192120715), 13401014362646, (56706, 82251, 59633, 41068), 32730, (3, 17, 22, 24), (25, 3, 65, 40)⟩,
  ⟨(-871608932908, 909277533886, 704611612267, 1096146964111), 2688424910661, (44288, 87701, 82712, 92256), 32725, (6, 15, 20, 24), (13, 21, 51, 47)⟩,
  ⟨(-1670290498, 3995781521, -2173063238, -1375286044), 7991563042, (51838, 98304, 47715, 54257), 32702, (1, 8, 9, 22), (36, 30, 8, 73)⟩,
  ⟨(-731801992, 1844486613, -920575126, -682271048), 3688973226, (52535, 98304, 49181, 53415), 32681, (1, 9, 17, 22), (57, 25, 29, 73)⟩,
  ⟨(-6002038971306, 3790840475377, -9984217086646, 10656136794717), 25889695710647, (50342, 75131, 40262, 92510), 32630, (10, 20, 22, 23), (94, 50, 0, 42)⟩,
  ⟨(-4523892864781, 806856896292, -1752390406392, 5862887362113), 10889979295546, (38311, 70391, 54990, 100818), 32623, (6, 10, 18, 20), (0, 47, 60, 68)⟩,
  ⟨(-2625221154677, 1216827404667, -2939015379765, -4496911023518), 12114869962599, (51334, 72118, 49637, 41209), 32589, (3, 19, 22, 23), (44, 3, 55, 40)⟩,
  ⟨(-412285634514, 477933055945, -606737193596, -229013668848), 1384790165104, (46024, 88154, 36821, 54697), 32587, (8, 13, 19, 22), (44, 36, 24, 84)⟩,
  ⟨(-1406622708, 3097001726, 245154914, 2367604379), 6194003452, (50653, 98304, 68129, 90586), 32482, (1, 6, 14, 20), (61, 22, 21, 87)⟩,
  ⟨(-1166461068746, 1407174474205, -1704288036194, -686691144002), 3988452907576, (46369, 88657, 37532, 54252), 32481, (8, 9, 19, 22), (57, 34, 29, 86)⟩,
  ⟨(-6935946456, -3126213995, 391196262, 4719478029), 13871892912, (32768, 50766, 67384, 87832), 32455, (0, 18, 21, 23), (12, 39, 46, 14)⟩,
  ⟨(-1774413764, -358008576, 757247207, -841651519), 3548827528, (32768, 58924, 79520, 49993), 32448, (0, 5, 16, 21), (20, 18, 39, 76)⟩,
  ⟨(-4008435171, -1736905652, 450906227, -1690193046), 8016870342, (32768, 51337, 69222, 51719), 32373, (0, 5, 21, 23), (15, 37, 63, 38)⟩,
  ⟨(-528725813125, 518275641500, -566060996740, -983491077789), 2640800411401, (52414, 78397, 51488, 41128), 32277, (3, 17, 19, 22), (57, 33, 27, 74)⟩,
  ⟨(-1892911303, 2180714100, 1058734988, 998302062), 4361428200, (37092, 98304, 81444, 80536), 32259, (1, 2, 6, 24), (51, 21, 45, 59)⟩,
  ⟨(-587866492174, 544553713579, -977065129150, 1080911328063), 2637987498241, (50931, 79064, 41262, 92389), 32238, (10, 11, 20, 22), (23, 31, 54, 60)⟩,
  ⟨(-4201707007873, 2676530702409, -6708386213861, 580788586019), 12581852189116, (43650, 79477, 30593, 68561), 32195, (7, 13, 22, 23), (44, 50, 70, 24)⟩,
  ⟨(-3895355028492, 2340041153335, -5777748968588, -2065667540094), 12164333835862, (44549, 78143, 34408, 54407), 32179, (13, 19, 22, 23), (33, 43, 66, 34)⟩,
  ⟨(-1610515, 1610515, 832522, 192462), 3221030, (32768, 98304, 82474, 69451), 32167, (0, 1, 2, 24), (41, 53, 1, 59)⟩,
  ⟨(-110595980, -8527011, -60929118, 93707233), 221191960, (32768, 63009, 47483, 93300), 32117, (0, 10, 18, 23), (0, 37, 67, 68)⟩,
  ⟨(-389561627915, 66811736070, 109584925895, 448628487400), 887007224043, (36753, 70472, 73632, 98682), 31948, (6, 15, 18, 20), (5, 32, 28, 69)⟩,
  ⟨(-411269502, -12334709, 257779605, 249503838), 822539004, (32768, 64553, 86074, 85415), 31927, (0, 2, 15, 21), (26, 14, 17, 89)⟩,
  ⟨(-46823323535, 1719964624, 32702374853, -38551970869), 130269331909, (41980, 66401, 81987, 46141), 31927, (4, 16, 21, 24), (10, 16, 56, 19)⟩,
  ⟨(-1615037500037, 1034054378419, -2679376213117, 2069423513752), 6126614138813, (48260, 76597, 36874, 87672), 31711, (7, 10, 22, 23), (31, 43, 67, 54)⟩,
  ⟨(-113267584444, 116387323674, 77923626911, 89647416891), 286009724889, (39581, 92204, 83391, 86077), 31643, (2, 6, 15, 24), (28, 26, 41, 89)⟩,
  ⟨(-559717926, 3554910895, -581794789, 1833531087), 7109821790, (60376, 98304, 60173, 82436), 31627, (1, 20, 22, 24), (93, 25, 21, 22)⟩,
  ⟨(-669369808, 193271961, 544238292, 14436218), 1338739616, (32768, 74997, 92178, 66242), 31598, (0, 2, 12, 24), (11, 62, 45, 17)⟩,
  ⟨(-318934522786, 286272752576, -528641397935, 417088949594), 1248558525475, (48795, 80562, 37787, 87428), 31357, (7, 10, 11, 22), (42, 9, 50, 92)⟩,
  ⟨(-2098353428450, -22248944567, -1042972103492, -1989612124349), 5506452576852, (40562, 65271, 53122, 41856), 31198, (3, 5, 19, 23), (63, 33, 15, 74)⟩,
  ⟨(-96250481602, 33194715606, 66038019205, -33829766361), 196824779706, (33487, 76588, 87524, 54271), 30975, (4, 12, 16, 24), (10, 49, 62, 64)⟩,
  ⟨(-68376339353, 82657217817, -82417669944, -96959289127), 307792090763, (50977, 83135, 47987, 44891), 30927, (9, 17, 19, 22), (40, 36, 30, 90)⟩,
  ⟨(-487613700077, -5927184485, 12527931447, -1665747491723), 5646934863450, (59876, 65467, 65681, 46204), 30808, (21, 22, 23, 24), (3, 2, 93, 94)⟩,
  ⟨(-1787217, 1787217, 694768, 665338), 3574434, (32768, 98304, 78274, 77734), 30780, (0, 1, 2, 6), (41, 89, 87, 45)⟩,
  ⟨(-447725083095, 198609467260, -221188993933, 620189267103), 1209802412137, (41282, 76294, 53554, 99132), 30735, (6, 10, 11, 20), (42, 61, 32, 91)⟩,
  ⟨(-838947892560, 1227337764790, -534669169780, 1402044601155), 3176513706454, (48227, 90857, 54505, 94462), 30719, (6, 11, 14, 20), (23, 35, 60, 88)⟩,
  ⟨(-417049150, 201290085, 261652751, -140660461), 834098300, (32768, 81351, 86094, 54484), 30541, (0, 4, 12, 24), (56, 53, 1, 64)⟩,
  ⟨(-4695963106, -237885055, -2277203380, -2695447189), 9391926212, (32768, 63876, 49645, 46727), 30493, (0, 5, 19, 23), (55, 66, 39, 77)⟩,
  ⟨(-79373652, 30203898, 50690415, -27292685), 158747304, (32768, 78005, 86462, 54268), 30453, (0, 4, 12, 16), (56, 18, 83, 62)⟩,
  ⟨(-1837353314422, 1530429090383, 484327719773, -2010884371767), 5573590631848, (43931, 83531, 71230, 41891), 30403, (3, 4, 17, 24), (6, 27, 16, 80)⟩,
  ⟨(-4268069382, 570734693, -3396172450, -1476176868), 8536138764, (32768, 69917, 39461, 54202), 30083, (0, 13, 19, 23), (44, 63, 70, 84)⟩,
  ⟨(-2210264490, 59868247, -1554406864, 1481384709), 4420528980, (32768, 66423, 42491, 87498), 29916, (0, 7, 10, 23), (50, 46, 70, 92)⟩,
  ⟨(-340593169, 62794176, -119899512, 319715825), 681186338, (32768, 71577, 54000, 96295), 29863, (0, 6, 10, 18), (32, 46, 69, 91)⟩,
  ⟨(-444368907, 78492810, 100887928, 405364957), 888737814, (32768, 71324, 72975, 95427), 29779, (0, 6, 15, 18), (47, 14, 68, 89)⟩,
  ⟨(-4441806873, 879689179, -4146039641, 527039259), 8883613746, (32768, 72025, 34949, 69424), 29532, (0, 7, 13, 23), (43, 66, 67, 85)⟩,
  ⟨(-1554100, 1554100, -237931, -509599), 3108200, (32768, 98304, 60519, 54791), 29385, (0, 1, 8, 17), (73, 81, 7, 82)⟩,
  ⟨(-841161494475, 342622443000, -78411053604, -626341371047), 1759383705121, (34203, 78298, 62615, 42205), 29097, (3, 5, 16, 17), (76, 80, 74, 20)⟩,
  ⟨(-69344694, 99916741, -35445206, -34384338), 199833482, (42794, 98304, 53911, 54259), 29081, (1, 8, 9, 17), (81, 30, 71, 29)⟩,
  ⟨(-262555098107, 104801208148, -32055651884, -196299157363), 550910500951, (34302, 78003, 61722, 42184), 29067, (3, 5, 17, 19), (77, 40, 55, 72)⟩,
  ⟨(-13393713508, 13608174088, -8662654439, 4828480412), 28730276683, (34983, 96577, 45775, 76550), 29029, (7, 8, 11, 14), (78, 9, 4, 79)⟩,
  ⟨(-2054663788, 833984682, -210548711, -1421225687), 4109327576, (32768, 78836, 62178, 42870), 29003, (0, 5, 16, 17), (72, 83, 77, 38)⟩,
  ⟨(-2018734240, 814280210, -225172447, -1395872171), 4037468480, (32768, 78753, 61881, 42878), 28990, (0, 5, 17, 19), (74, 90, 63, 76)⟩,
  ⟨(-428657498, 405025463, -240251577, 144306463), 857314996, (32768, 96497, 47170, 76567), 28897, (0, 8, 11, 14), (75, 88, 82, 79)⟩,
  ⟨(-1975069152, 1857672187, -1117586229, 661489788), 3950138304, (32768, 96356, 46994, 76510), 28874, (0, 7, 8, 11), (75, 78, 92, 85)⟩,
  ⟨(-89331221475, 44503136600, -239581668, -72621064959), 203368040297, (36748, 79877, 65458, 42133), 28871, (3, 4, 16, 17), (83, 72, 65, 19)⟩,
  ⟨(-658810206, 628238159, -139761518, -226695954), 1317620412, (32768, 96783, 58584, 54260), 28692, (0, 8, 9, 17), (73, 90, 71, 86)⟩,
  ⟨(-1317398, 1317398, -609612, 395143), 2634796, (32768, 98304, 50372, 75364), 28503, (0, 1, 8, 14), (8, 78, 87, 71)⟩,
  ⟨(-124465196, 73805494, 6259685, -75908915), 248930392, (32768, 84966, 67183, 45551), 28416, (0, 4, 16, 17), (80, 76, 7, 64)⟩,
  ⟨(-1092398862, 746820065, -665483698, -360091572), 2184797724, (32768, 87937, 45573, 54734), 27872, (0, 8, 13, 19), (34, 66, 86, 85)⟩,
  ⟨(-2273584512, 1693746551, -1691132779, 279475446), 4547169024, (32768, 89947, 41162, 69563), 27818, (0, 7, 8, 13), (24, 84, 70, 79)⟩,
  ⟨(-628001650, 439629551, -363174022, -216196516), 1256003300, (32768, 88475, 46586, 54255), 27788, (0, 8, 9, 19), (36, 90, 84, 81)⟩,
  ⟨(-412261, 412261, -101790, 167713), 824522, (32768, 98304, 57445, 78866), 27248, (0, 1, 6, 14), (35, 88, 82, 59)⟩,
  ⟨(-1560752432, 1395255342, -655970550, 756401881), 3121504864, (32768, 94829, 51763, 81416), 27142, (0, 6, 11, 14), (61, 78, 87, 91)⟩,
  ⟨(-161787906, 94679301, 64230434, 103450034), 323575812, (32768, 84712, 78545, 86488), 27020, (0, 2, 6, 15), (51, 69, 48, 59)⟩,
  ⟨(-411943310, 234499165, -107753594, -232133362), 823886620, (32768, 84189, 56964, 47070), 27018, (0, 9, 17, 19), (57, 77, 86, 81)⟩,
  ⟨(-607277081, 232068486, -249901560, 494532583), 1214554162, (32768, 78058, 52051, 92220), 26897, (0, 6, 10, 11), (60, 92, 88, 68)⟩,
  ⟨(-412776907, 181041092, -238248974, 264913083), 825553814, (32768, 79907, 46622, 86565), 25655, (0, 7, 10, 11), (54, 91, 79, 67)⟩,
  ⟨(-1270229377173, 2294717854587, 1316439905821, 4137879816671), 35126214313802, (63166, 69817, 67992, 73256), 21932, (20, 21, 22, 24), (58, 52, 13, 94)⟩,
  ⟨(-1764723158941, 58468154683, -615581465697, 3967742289527), 26532782844924, (61177, 65680, 64015, 75336), 21386, (20, 21, 22, 23), (58, 31, 12, 93)⟩
]

set_option maxRecDepth 20000 in
private lemma cell7_ok : verifyCell ⟨7, by decide⟩ hs7 vs7 ctr7 = true := by
  decide

private lemma cell_diam_lt_one (j : Fin 8) {x y : E4}
    (hxL : InLStar2 x) (hyL : InLStar2 y) (hxC : x ∈ cellSet j) (hyC : y ∈ cellSet j) :
    ‖x - y‖ < 1 := by
  fin_cases j
  · exact verifyCell_sound ⟨0, by decide⟩ hs0 vs0 ctr0 cell0_ok hxL hyL hxC hyC
  · exact verifyCell_sound ⟨1, by decide⟩ hs1 vs1 ctr1 cell1_ok hxL hyL hxC hyC
  · exact verifyCell_sound ⟨2, by decide⟩ hs2 vs2 ctr2 cell2_ok hxL hyL hxC hyC
  · exact verifyCell_sound ⟨3, by decide⟩ hs3 vs3 ctr3 cell3_ok hxL hyL hxC hyC
  · exact verifyCell_sound ⟨4, by decide⟩ hs4 vs4 ctr4 cell4_ok hxL hyL hxC hyC
  · exact verifyCell_sound ⟨5, by decide⟩ hs5 vs5 ctr5 cell5_ok hxL hyL hxC hyC
  · exact verifyCell_sound ⟨6, by decide⟩ hs6 vs6 ctr6 cell6_ok hxL hyL hxC hyC
  · exact verifyCell_sound ⟨7, by decide⟩ hs7 vs7 ctr7 cell7_ok hxL hyL hxC hyC

end BorsukEightH1

theorem OMA.solution : OMA.R_Borsuk_borsuk_conjecture_four_eight_parts_R1.H1 := by
  intro K hK hnt hlo hhi
  obtain ⟨Φ, hΦ_cont, hΦ_dist, hΦ_in⟩ :=
    BorsukEightH1.exists_norm_map_to_LStar2 hK hnt hlo hhi
  have hD : 0 < Metric.diam K := Metric.diam_pos hnt hK.isBounded
  refine ⟨fun j => Φ ⁻¹' BorsukEightH1.cellSet j, ?_, ?_, ?_⟩
  · intro j
    exact (BorsukEightH1.cellSet_isClosed j).preimage hΦ_cont
  · intro x _
    obtain ⟨j, hj⟩ := BorsukEightH1.cellSet_cover (Φ x)
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  · intro j x hx y hy hdist
    have hlt : ‖Φ x - Φ y‖ < 1 :=
      BorsukEightH1.cell_diam_lt_one j (hΦ_in x hx.1) (hΦ_in y hy.1) hx.2 hy.2
    rw [← dist_eq_norm, hΦ_dist, hdist, inv_mul_cancel₀ hD.ne'] at hlt
    exact lt_irrefl 1 hlt
