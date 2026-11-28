import OMAStatements.S_mo_243037

/-!
This shortening adapts @connoranderson's complete earlier proof at
https://github.com/connoranderson/open-math-agents/blob/c50d84ab90034aaa230635b859328d1eeaf0e695/proofs/mo-243037.lean,
linked from statement PR #24171. The current proof by @FrancoisCharroin
(PR #28761) was also reviewed. The reflection, Hilbert-basis sequence, explicit
spherical caps, counting measure and antipodal law are retained from the earlier proof.
The new simplifications use measure support, counting measure of an injective image,
the square-root comparison API, and continuity automation.

Original question: ijon, https://mathoverflow.net/questions/243037, CC BY-SA 3.0.
Nate Eldredge's comment: https://mathoverflow.net/questions/243037#comment599225_243037.
-/

/-! Nate Eldredge's MathOverflow comment 599225 suggests counting measure
and disjoint small balls in each open set. Here the ball centers are explicit
combinations of orthonormal vectors; a Householder reflection identifies
the masses of the corresponding balls. -/

namespace OMA.S_mo_243037

open Metric Set

private lemma ortho_seq (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : ¬FiniteDimensional ℝ H) : ∃ e : ℕ → H, Orthonormal ℝ e := by
  obtain ⟨I,b,_⟩ := exists_hilbertBasis ℝ H
  have : Infinite I := by
    by_contra! hf
    let _ := Fintype.ofFinite I
    exact h (Module.Finite.of_basis b.toOrthonormalBasis.toBasis)
  let f := Infinite.natEmbedding I
  exact ⟨b ∘ f,b.orthonormal.comp f f.injective⟩

private lemma caps {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e : ℕ → H) (he : Orthonormal ℝ e) (r : ℝ) (hr : 0<r) :
    ∃ o : S H, ∃ δ : ℝ, 0<δ ∧ ∃ u : ℕ → S H, (∀ i, ball (u i) δ ⊆ ball o r) ∧
        Pairwise (fun i j => Disjoint (ball (u i) δ) (ball (u j) δ)) := by
  let b := min (r/8) (1/4)
  have hb : 0<b := lt_min (by positivity) (by norm_num)
  have hb' : b ≤ 1/4 := min_le_right _ _
  have hb'' : b ≤ r/8 := min_le_left _ _
  let a := Real.sqrt (1-b^2)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a^2 = 1-b^2 := Real.sq_sqrt (by nlinarith)
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg b]
  have hab : 1-a ≤ b := by
    have : 1-b ≤ a := Real.le_sqrt_of_sq_le (by nlinarith)
    linarith
  let o : S H := ⟨e 0,mem_sphere_zero_iff_norm.mpr (he.norm_eq_one 0)⟩
  let w (i : ℕ) := a • e 0+b • e (i+1)
  have hw (i : ℕ) : ‖w i‖=1 := by
    have hsq := norm_add_sq_real (a • e 0) (b • e (i+1))
    rw [real_inner_smul_left,real_inner_smul_right,he.inner_eq_zero (by omega : 0≠i+1)] at hsq
    simp [w,norm_smul,he.norm_eq_one,Real.norm_of_nonneg ha,Real.norm_of_nonneg hb.le] at hsq ⊢
    nlinarith [norm_nonneg (w i)]
  let u (i : ℕ) : S H := ⟨w i,mem_sphere_zero_iff_norm.mpr (hw i)⟩
  have hd (i : ℕ) : dist (u i) o ≤ 2*b := by
    change dist (w i) (e 0) ≤ _
    rw [dist_eq_norm]
    have ee : w i-e 0=(a-1) • e 0+b • e (i+1) := by
      simp [w,sub_smul]; abel
    rw [ee]
    have h := norm_add_le ((a-1) • e 0) (b • e (i+1))
    simp [norm_smul,he.norm_eq_one,Real.norm_of_nonneg hb.le,
      Real.norm_of_nonpos (sub_nonpos.mpr ha1)] at h
    linarith
  refine ⟨o,b/3,by positivity,u,fun i => ball_subset_ball' (by linarith [hd i]),?_⟩
  intro i j hij
  apply ball_disjoint_ball
  change _ ≤ dist (w i) (w j)
  rw [dist_eq_norm]
  have ee : w i-w j=b • (e (i+1)-e (j+1)) := by simp [w,smul_sub]
  rw [ee,norm_smul,Real.norm_of_nonneg hb.le]
  have hsq := norm_sub_sq_real (e (i+1)) (e (j+1))
  rw [he.norm_eq_one,he.norm_eq_one,he.inner_eq_zero (by omega)] at hsq
  have hlo : 1 ≤ ‖e (i+1)-e (j+1)‖ := by nlinarith [norm_nonneg (e (i+1)-e (j+1))]
  linarith [mul_le_mul_of_nonneg_left hlo hb.le]

end OMA.S_mo_243037
namespace OMA.S_mo_243037
open MeasureTheory Metric Set
open scoped ENNReal

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private lemma act_cont (e : H ≃ₗᵢ[ℝ] H) : Continuous (act e) :=
  by unfold act; fun_prop

private lemma act_bij (e : H ≃ₗᵢ[ℝ] H) : Function.Bijective (act e) := by
  constructor
  · intro x y h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  · intro x
    exact ⟨act e.symm x,Subtype.ext (e.apply_symm_apply _)⟩

variable [MeasurableSpace H] [BorelSpace H]

private lemma count_invariant (e : H ≃ₗᵢ[ℝ] H) : (Measure.count : Measure (S H)).map (act e)=Measure.count := by
  ext s hs
  rw [Measure.map_apply (act_cont e).measurable hs,
    ← Measure.count_injective_image (act_bij e).1, (act_bij e).2.image_preimage]

private lemma line_invariant (x : S H) : IsProbabilityMeasure (lineLaw x) ∧
    ∀ e : H ≃ₗᵢ[ℝ] H, act e x=x ∨ act e x=antipode x → (lineLaw x).map (act e)=lineLaw x := by
  constructor
  · constructor
    simp [lineLaw,Measure.smul_apply,Measure.add_apply,ENNReal.inv_two_add_inv_two]
  · intro e h
    have ha : act e (antipode x)=antipode (act e x) := Subtype.ext (map_neg e _)
    have hneg : antipode (antipode x)=x := Subtype.ext (neg_neg _)
    rw [lineLaw,Measure.map_smul,Measure.map_add _ _ (act_cont e).measurable,
      Measure.map_dirac' (act_cont e).measurable,Measure.map_dirac' (act_cont e).measurable,ha]
    rcases h with h | h <;> simp [h,hneg,add_comm]

private lemma ball_const (μ : Measure (S H)) (hm : ∀ e : H ≃ₗᵢ[ℝ] H, μ.map (act e)=μ)
    (x y : S H) (r : ℝ) : μ (ball x r)=μ (ball y r) := by
  let e := (ℝ ∙ (x.val-y.val))ᗮ.reflection
  have hx : act e x = y := Subtype.ext (Submodule.reflection_sub
    ((mem_sphere_zero_iff_norm.mp x.property).trans (mem_sphere_zero_iff_norm.mp y.property).symm))
  have he : act e ⁻¹' ball y r = ball x r := by
    ext z
    rw [← hx]
    change dist (e z.val) (e x.val) < r ↔ dist z.val x.val < r
    rw [e.dist_map]
  rw [← he,← Measure.map_apply (act_cont e).measurable measurableSet_ball,hm]

private lemma infinite_open [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (hH : ¬FiniteDimensional ℝ H) (μ : Measure (S H)) (hμ : μ≠0)
    (hm : ∀ e : H ≃ₗᵢ[ℝ] H, μ.map (act e)=μ) (U : Set (S H)) (hu : IsOpen U) (hne : U.Nonempty) :
    μ U=⊤ := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hu x hx
  obtain ⟨e,he⟩ := ortho_seq H hH
  obtain ⟨o,δ,hδ,u,hsub,hdis⟩ := caps e he r hr
  have hpos : μ (ball o δ)≠0 := by
    obtain ⟨y,hy⟩ := Measure.nonempty_support hμ
    rw [← ball_const μ hm y o δ]
    exact ne_of_gt ((Measure.mem_support_iff_forall y).mp hy _ (ball_mem_nhds _ hδ))
  apply top_unique
  calc
    ⊤ = ∑' _ : ℕ, μ (ball o δ) := (ENNReal.tsum_const_eq_top_of_ne_zero hpos).symm
    _ = ∑' i : ℕ, μ (ball (u i) δ) := tsum_congr (fun i => ball_const μ hm o (u i) δ)
    _ = μ (⋃ i, ball (u i) δ) := (measure_iUnion hdis (fun _ => measurableSet_ball)).symm
    _ ≤ μ (ball o r) := measure_mono (Set.iUnion_subset hsub)
    _ = μ (ball x r) := ball_const μ hm o x r
    _ ≤ μ U := measure_mono hball

end OMA.S_mo_243037

theorem OMA.solution : type_of% @OMA.S_mo_243037.main := by
  intro H _ _ _ _ _ _ h
  exact ⟨OMA.S_mo_243037.count_invariant,
    fun μ hμ hm U ho hn => OMA.S_mo_243037.infinite_open h μ hμ hm U ho hn,
    OMA.S_mo_243037.line_invariant⟩
