import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Contractibility of secant-free Grassmannians by simplex dimension

For a 3-simplex (`s.card = 4`) in a simplicial complex of dimension at most 3,
the closed star `S s` reduces to `convexHull ℝ s`. Secant-free planes of
codimension 3 are precisely the complements of the 3-dimensional direction `W`
of `affineSpan ℝ s`, which are homeomorphic under `starProjection` to the
real normed vector space `Wᗮ →L[ℝ] W` of linear graphs, hence contractible.

This proves the `s.card = 4` case completely and splits the remaining faces
into interior triangles (`s.card = 3`, `H1`) and edges (`s.card = 2`, `H2`).
-/

open Geometry Set ContinuousLinearMap InnerProductSpace
open scoped BigOperators ContDiff Topology unitInterval

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1_H1_R1

/-- Every Real normed vector space is contractible via radial scaling to zero. -/
private theorem normedSpace_contractible (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ContractibleSpace V := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨0, ⟨{
    toFun := fun p => (1 - (p.1 : ℝ)) • p.2
    continuous_toFun := ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      continuous_snd)
    map_zero_left := fun x => by simp
    map_one_left := fun x => by simp }⟩⟩

/-- Any bijective continuous linear endomorphism of a finite-dimensional normed space is invertible,
with continuous inverse map. -/
private theorem isInvertible_of_injective {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V →L[ℝ] V) (hinj : Function.Injective A) :
    A.IsInvertible := by
  have hbij : Function.Bijective A.toLinearMap :=
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let e : V ≃L[ℝ] V := (LinearEquiv.ofBijective A.toLinearMap hbij).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

/-- Secant-free codimension-3 planes on a single 3-simplex (`s.card = 4`) form a contractible space
homeomorphic to `Wᗮ →L[ℝ] W`. -/
private theorem contractible_of_card_four (m : ℕ)
    (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m)))
    (hsmall : ∀ u ∈ K.faces, u.card ≤ 4)
    {s : Finset (EuclideanSpace ℝ (Fin m))} (hs : s ∈ K.faces) (hs4 : s.card = 4) :
    let E := EuclideanSpace ℝ (Fin m)
    letI : DecidableEq E := Classical.decEq E
    let S := ⋃ t ∈ {t | t ∈ K.faces ∧ s ∪ t ∈ K.faces}, convexHull ℝ (t : Set E)
    let G := {P : Submodule ℝ E //
      Module.finrank ℝ P + 3 = m ∧ ∀ x ∈ S, ∀ y ∈ S, x - y ∈ P → x = y}
    let topo : TopologicalSpace G :=
      TopologicalSpace.induced (fun P : G => P.val.starProjection) inferInstance
    @ContractibleSpace G topo := by
  intro E S G topo
  let : DecidableEq E := Classical.decEq E
  let : TopologicalSpace G := topo
  -- 1. The closed star of a maximal 4-vertex face equals its own convex hull.
  have hS_eq : S = convexHull ℝ (s : Set E) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨t, ⟨_, hst⟩, hxt⟩ := Set.mem_iUnion₂.mp hx
      have heq : s = s ∪ t := Finset.eq_of_subset_of_card_le Finset.subset_union_left
        ((hsmall (s ∪ t) hst).trans_eq hs4.symm)
      have hts : t ⊆ s := Finset.subset_union_right.trans_eq heq.symm
      exact convexHull_mono (Finset.coe_subset.mpr hts) hxt
    · intro x hx
      have hss : s ∪ s = s := Finset.union_idempotent s
      exact Set.mem_iUnion₂.mpr ⟨s, ⟨hs, hss.symm ▸ hs⟩, hx⟩
  -- 2. Direction subspace W of the 3-simplex s has dimension 3, so Wᗮ has dimension m - 3.
  let W : Submodule ℝ E := vectorSpan ℝ (s : Set E)
  have hcard_coe : Fintype.card (s : Set E) = 3 + 1 := by
    simpa using hs4
  have hdimW : Module.finrank ℝ W = 3 := by
    have hW_eq_r : W = vectorSpan ℝ (range (Subtype.val : ↥(s : Set E) → E)) := by simp [W]
    rw [hW_eq_r]
    exact (K.indep hs).finrank_vectorSpan hcard_coe
  have hdimE : Module.finrank ℝ E = m := finrank_euclideanSpace_fin
  have hsumW : Module.finrank ℝ W + Module.finrank ℝ Wᗮ = m :=
    W.finrank_add_finrank_orthogonal.trans hdimE
  have hm3 : 3 ≤ m := by omega
  have hdimU : Module.finrank ℝ Wᗮ = m - 3 := by omega
  -- 3. Equivalence between secant-freeness on conv(s) and transversality P ⊓ W = ⊥.
  have hsec_iff (P : Submodule ℝ E) :
      (∀ x ∈ S, ∀ y ∈ S, x - y ∈ P → x = y) ↔ P ⊓ W = ⊥ := by
    rw [hS_eq]
    constructor
    · intro hsec
      rw [eq_bot_iff]
      intro w hw
      rcases hw with ⟨hwP, hwW⟩
      have hs_ne : s.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨p₀, hp₀⟩ := hs_ne
      have hw_span : w ∈ Submodule.span ℝ ((s.image (fun x : E => x - p₀) : Finset E) : Set E) := by
        have hv : W = Submodule.span ℝ ((fun x : E => x -ᵥ p₀) '' (s : Set E)) :=
          vectorSpan_eq_span_vsub_set_right ℝ (Finset.mem_coe.mpr hp₀)
        have himg : ((fun x : E => x -ᵥ p₀) '' (s : Set E)) =
            ((s.image (fun x : E => x - p₀) : Finset E) : Set E) := by
          simp [Finset.coe_image, vsub_eq_sub]
        rwa [hv, himg] at hwW
      have hfin_span : ∀ {u : Finset E} {y : E}, y ∈ Submodule.span ℝ (u : Set E) →
          ∃ f : E → ℝ, ∑ z ∈ u, f z • z = y := by
        intro u y hy
        induction hy using Submodule.span_induction with
        | mem z hz =>
          exact ⟨fun q => if q = z then 1 else 0, by
            simp [Finset.sum_ite_eq', Finset.mem_coe.mp hz]⟩
        | zero => exact ⟨0, by simp⟩
        | add _ _ _ _ ih1 ih2 =>
          obtain ⟨f1, hf1⟩ := ih1
          obtain ⟨f2, hf2⟩ := ih2
          exact ⟨fun q => f1 q + f2 q, by simp [add_smul, Finset.sum_add_distrib, hf1, hf2]⟩
        | smul a _ _ ih =>
          obtain ⟨f1, hf1⟩ := ih
          exact ⟨fun q => a * f1 q, by simp [mul_smul, ← Finset.smul_sum, hf1]⟩
      obtain ⟨f_lin, hf_lin⟩ := hfin_span hw_span
      let c : E → ℝ := fun x => f_lin (x - p₀)
      have hc_fin : ∑ x ∈ s, c x • (x - p₀) = w := by
        have hsum_img : ∑ z ∈ s.image (fun x : E => x - p₀), f_lin z • z =
            ∑ x ∈ s, f_lin (x - p₀) • (x - p₀) :=
          Finset.sum_image fun x _ y _ hxy => sub_left_inj.mp hxy
        exact hsum_img.symm.trans hf_lin
      let d : E → ℝ := fun x => if x = p₀ then c p₀ - ∑ y ∈ s, c y else c x
      have hd_sum : ∑ x ∈ s, d x = 0 := by
        have hsplit : ∑ x ∈ s, d x = d p₀ + ∑ x ∈ s.erase p₀, d x :=
          (Finset.add_sum_erase s d hp₀).symm
        have herase : ∑ x ∈ s.erase p₀, d x = ∑ x ∈ s.erase p₀, c x :=
          Finset.sum_congr rfl fun x hx => if_neg (Finset.ne_of_mem_erase hx)
        rw [hsplit, herase]
        dsimp only [d]
        rw [if_pos rfl, ← Finset.add_sum_erase s c hp₀]
        ring
      have hd_vec : ∑ x ∈ s, d x • x = w := by
        calc
          ∑ x ∈ s, d x • x = d p₀ • p₀ + ∑ x ∈ s.erase p₀, c x • x := by
            rw [← Finset.add_sum_erase s (fun x => d x • x) hp₀]
            congr 1
            exact Finset.sum_congr rfl fun x hx => by
              dsimp only [d]; rw [if_neg (Finset.ne_of_mem_erase hx)]
          _ = (c p₀ - (c p₀ + ∑ x ∈ s.erase p₀, c x)) • p₀ + ∑ x ∈ s.erase p₀, c x • x := by
            dsimp only [d]; rw [if_pos rfl, ← Finset.add_sum_erase s c hp₀]
          _ = ∑ x ∈ s, c x • (x - p₀) := by
            rw [← Finset.add_sum_erase s (fun x => c x • (x - p₀)) hp₀, sub_self, smul_zero,
              zero_add]
            simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
            module
          _ = w := hc_fin
      let M : ℝ := 1 + ∑ x ∈ s, |d x|
      have hM_pos : 0 < M := by
        have hnn : 0 ≤ ∑ x ∈ s, |d x| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        linarith
      let ε : ℝ := 1 / (4 * M)
      have hε_pos : 0 < ε := div_pos one_pos (by linarith)
      let u : E → ℝ := fun _ => (1 : ℝ) / 4
      let v : E → ℝ := fun x => (1 : ℝ) / 4 + ε * d x
      have hu_sum : ∑ x ∈ s, u x = 1 := by
        simp [u, hs4]
      have hv_sum : ∑ x ∈ s, v x = 1 := by
        dsimp only [u] at hu_sum
        simp only [v, Finset.sum_add_distrib, ← Finset.mul_sum, hu_sum, hd_sum, mul_zero, add_zero]
      have hv_nonneg : ∀ x ∈ s, 0 ≤ v x := by
        intro x hx
        have hle_sum : |d x| ≤ ∑ y ∈ s, |d y| :=
          Finset.single_le_sum (fun y _ => abs_nonneg (d y)) hx
        have hlt_M : |d x| ≤ M := by dsimp [M]; linarith
        have hneg : -M ≤ d x := by linarith [neg_abs_le (d x)]
        have hmul : -(1 / 4 : ℝ) ≤ ε * d x := by
          dsimp [ε]
          rw [one_div_mul_eq_div]
          have h1 : -M / (4 * M) ≤ d x / (4 * M) :=
            div_le_div_of_nonneg_right hneg (by linarith)
          have h2 : -M / (4 * M) = -(1 / 4 : ℝ) := by
            field_simp [hM_pos.ne']
          linarith
        dsimp [v]
        linarith
      have hy_mem : (∑ x ∈ s, u x • x) ∈ convexHull ℝ (s : Set E) :=
        Finset.mem_convexHull'.mpr ⟨u, fun _ _ => by norm_num [u], hu_sum, rfl⟩
      have hx_mem : (∑ x ∈ s, v x • x) ∈ convexHull ℝ (s : Set E) :=
        Finset.mem_convexHull'.mpr ⟨v, hv_nonneg, hv_sum, rfl⟩
      have hdiff_eq : (∑ x ∈ s, v x • x) - (∑ x ∈ s, u x • x) = ε • w := by
        rw [← Finset.sum_sub_distrib]
        have hterm : ∀ x ∈ s, v x • x - u x • x = (ε * d x) • x := fun x _ => by
          rw [← sub_smul]; dsimp [u, v]; ring_nf
        rw [Finset.sum_congr rfl hterm]
        simp_rw [mul_smul, ← Finset.smul_sum, hd_vec]
      have heq_xy := hsec _ hx_mem _ hy_mem (hdiff_eq ▸ P.smul_mem ε hwP)
      have h0 : ε • w = 0 := hdiff_eq.symm.trans (sub_eq_zero.mpr heq_xy)
      exact (smul_eq_zero.mp h0).resolve_left hε_pos.ne'
    · intro hbot x hx y hy hxy
      have hx_aff : x ∈ affineSpan ℝ (s : Set E) := convexHull_subset_affineSpan (s : Set E) hx
      have hy_aff : y ∈ affineSpan ℝ (s : Set E) := convexHull_subset_affineSpan (s : Set E) hy
      have hxy_W : x - y ∈ W := by
        dsimp only [W]
        rw [← vsub_eq_sub, ← direction_affineSpan]
        exact AffineSubspace.vsub_mem_direction hx_aff hy_aff
      have h0 : x - y ∈ (⊥ : Submodule ℝ E) := hbot ▸ ⟨hxy, hxy_W⟩
      exact sub_eq_zero.mp ((Submodule.mem_bot ℝ).mp h0)
  -- 4. Homeomorphism between G and the space of continuous linear maps Wᗮ →L[ℝ] W.
  let F : (Wᗮ →L[ℝ] W) → (Wᗮ →L[ℝ] E) := fun T => Wᗮ.subtypeL + W.subtypeL.comp T
  have hF_apply (T : Wᗮ →L[ℝ] W) (u : Wᗮ) : F T u = (u : E) + (T u : E) := rfl
  have hF_inj (T : Wᗮ →L[ℝ] W) : Function.Injective (F T) := by
    intro u₁ u₂ h
    have h0 : ((u₁ - u₂ : Wᗮ) : E) = -((T (u₁ - u₂) : W) : E) := by
      have hsub : F T (u₁ - u₂) = 0 := by rw [map_sub, h, sub_self]
      rw [hF_apply] at hsub
      exact eq_neg_of_add_eq_zero_left hsub
    have hmemW : ((u₁ - u₂ : Wᗮ) : E) ∈ W := by
      rw [h0]
      exact W.neg_mem (T (u₁ - u₂)).2
    have hbot : ((u₁ - u₂ : Wᗮ) : E) ∈ W ⊓ Wᗮ := ⟨hmemW, (u₁ - u₂).2⟩
    rw [W.inf_orthogonal_eq_bot, Submodule.mem_bot] at hbot
    exact sub_eq_zero.mp (Subtype.ext hbot)
  let gram : (Wᗮ →L[ℝ] W) → (Wᗮ →L[ℝ] Wᗮ) := fun T => (adjoint (F T)).comp (F T)
  have hgram_inv (T : Wᗮ →L[ℝ] W) : (gram T).IsInvertible := by
    apply isInvertible_of_injective
    intro u₁ u₂ h
    have hsub : gram T (u₁ - u₂) = 0 := by rw [map_sub, h, sub_self]
    have hinn : ⟪F T (u₁ - u₂), F T (u₁ - u₂)⟫_ℝ = 0 := by
      rw [← adjoint_inner_left (F T)]
      change ⟪gram T (u₁ - u₂), u₁ - u₂⟫_ℝ = 0
      rw [hsub, inner_zero_left]
    exact sub_eq_zero.mp (hF_inj T (by rw [inner_self_eq_zero.mp hinn, map_zero]))
  let graphSub : (Wᗮ →L[ℝ] W) → G := fun T =>
    ⟨LinearMap.range (F T).toLinearMap, by
      have hfr : Module.finrank ℝ (LinearMap.range (F T).toLinearMap) = Module.finrank ℝ Wᗮ :=
        LinearMap.finrank_range_of_inj (hF_inj T)
      refine ⟨by omega, (hsec_iff _).mpr ?_⟩
      rw [eq_bot_iff]
      rintro z ⟨⟨u, rfl⟩, hzW⟩
      change (u : E) + (T u : E) ∈ W at hzW
      have huW : (u : E) ∈ W := by
        have := W.sub_mem hzW (T u).2
        simpa only [add_sub_cancel_right] using this
      have hbot : (u : E) ∈ W ⊓ Wᗮ := ⟨huW, u.2⟩
      rw [W.inf_orthogonal_eq_bot, Submodule.mem_bot] at hbot
      have hu0 : u = 0 := Subtype.ext hbot
      simp [hu0]⟩
  have hproj_formula (T : Wᗮ →L[ℝ] W) :
      (graphSub T).val.starProjection =
        (F T).comp ((gram T).inverse.comp (adjoint (F T))) := by
    apply ContinuousLinearMap.ext
    intro v
    let u : Wᗮ := (gram T).inverse ((adjoint (F T)) v)
    change (LinearMap.range (F T).toLinearMap).starProjection v = F T u
    have humem : F T u ∈ LinearMap.range (F T).toLinearMap := ⟨u, rfl⟩
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero humem
    rintro _ ⟨w, rfl⟩
    change ⟪v - F T u, F T w⟫_ℝ = 0
    rw [← adjoint_inner_left (F T), map_sub]
    have hgu : (adjoint (F T)) (F T u) = (adjoint (F T)) v :=
      (hgram_inv T).self_apply_inverse ((adjoint (F T)) v)
    rw [hgu, sub_self, inner_zero_left]
  -- Inverse map G → (Wᗮ →L[ℝ] W)
  let S_op : (E →L[ℝ] E) → (Wᗮ →L[ℝ] Wᗮ) :=
    fun L => Wᗮ.orthogonalProjectionOnto.comp (L.comp Wᗮ.subtypeL)
  have hS_inv (P : G) : (S_op P.val.starProjection).IsInvertible := by
    apply isInvertible_of_injective
    intro u₁ u₂ h
    have hsub : S_op P.val.starProjection (u₁ - u₂) = 0 := by rw [map_sub, h, sub_self]
    let d : Wᗮ := u₁ - u₂
    have hd_proj : Wᗮ.starProjection (P.val.starProjection (d : E)) = 0 :=
      congrArg Subtype.val hsub
    have hd_orth : P.val.starProjection (d : E) ∈ Wᗮᗮ :=
      (Submodule.starProjection_apply_eq_zero_iff Wᗮ).mp hd_proj
    have hinn0 : ⟪P.val.starProjection (d : E), (d : E)⟫_ℝ = 0 :=
      (Submodule.mem_orthogonal' _ _).mp hd_orth (d : E) d.2
    have hnorm0 : ⟪P.val.starProjection (d : E), P.val.starProjection (d : E)⟫_ℝ = 0 := by
      have hsym := Submodule.inner_starProjection_left_eq_right P.val (d : E)
        (P.val.starProjection (d : E))
      have hidem : P.val.starProjection (P.val.starProjection (d : E)) =
          P.val.starProjection (d : E) :=
        Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem P.val (d : E))
      rw [hsym, hidem, real_inner_comm, hinn0]
    have hp0 : P.val.starProjection (d : E) = 0 := inner_self_eq_zero.mp hnorm0
    have hd_Porth : (d : E) ∈ P.valᗮ := (Submodule.starProjection_apply_eq_zero_iff P.val).mp hp0
    -- Since finrank P + finrank W = m and P ⊓ W = ⊥, P ⊔ W = ⊤ so Pᗮ ⊓ Wᗮ = ⊥.
    have hPW_bot : P.val ⊓ W = ⊥ := (hsec_iff P.val).mp P.2.2
    have hPW_top : P.val ⊔ W = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have hmod := P.val.finrank_sup_add_finrank_inf_eq W
      rw [hPW_bot, finrank_bot, add_zero, hdimW, P.2.1] at hmod
      exact hmod.trans hdimE.symm
    have hd_zero : (d : E) = 0 := by
      apply ext_inner_right ℝ
      intro z
      have hz_top : z ∈ P.val ⊔ W := hPW_top.symm ▸ Submodule.mem_top
      rw [Submodule.mem_sup] at hz_top
      obtain ⟨p, hp, w, hw, rfl⟩ := hz_top
      rw [inner_add_right, inner_zero_left]
      have hp0' : ⟪(d : E), p⟫_ℝ = 0 := by
        rw [real_inner_comm]
        exact hd_Porth p hp
      have hw0' : ⟪(d : E), w⟫_ℝ = 0 := by
        rw [real_inner_comm]
        exact d.2 w hw
      rw [hp0', hw0', add_zero]
    exact sub_eq_zero.mp (Subtype.ext hd_zero)
  let toHom : G → (Wᗮ →L[ℝ] W) := fun P =>
    W.orthogonalProjectionOnto.comp
      (P.val.starProjection.comp (Wᗮ.subtypeL.comp (S_op P.val.starProjection).inverse))
  -- Verify left_inv and right_inv
  have hleft_inv : Function.LeftInverse graphSub toHom := by
    intro P
    apply Subtype.ext
    -- Both graphSub (toHom P) and P.val have finrank = m - 3; show ≤!
    have hle : (graphSub (toHom P)).val ≤ P.val := by
      rintro _ ⟨u, rfl⟩
      let v : Wᗮ := (S_op P.val.starProjection).inverse u
      let z : E := P.val.starProjection (v : E)
      have hzP : z ∈ P.val := Submodule.starProjection_apply_mem P.val (v : E)
      have hzU : Wᗮ.starProjection z = (u : E) := by
        have h1 : Wᗮ.orthogonalProjectionOnto z = u :=
          (hS_inv P).self_apply_inverse u
        exact congrArg Subtype.val h1
      have hzW : W.starProjection z = ((toHom P u : W) : E) := rfl
      have hsum_z : Wᗮ.starProjection z + W.starProjection z = z := by
        have hw_mem : z - W.starProjection z ∈ Wᗮ := Submodule.sub_starProjection_mem_orthogonal z
        have hw_eq : Wᗮ.starProjection z = z - W.starProjection z := by
          apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hw_mem
          intro y hy
          rw [sub_sub_cancel]
          exact hy (W.starProjection z) (Submodule.starProjection_apply_mem W z)
        rw [hw_eq, sub_add_cancel]
      change (u : E) + ((toHom P u : W) : E) ∈ P.val
      rw [← hzU, ← hzW, hsum_z]
      exact hzP
    have hfr1 : Module.finrank ℝ (graphSub (toHom P)).val = m - 3 := by
      have := (graphSub (toHom P)).2.1; omega
    have hfr2 : Module.finrank ℝ P.val = m - 3 := by
      have := P.2.1; omega
    exact Submodule.eq_of_le_of_finrank_eq hle (hfr1.trans hfr2.symm)
  have hright_inv : Function.RightInverse graphSub toHom := by
    intro T
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    let P := graphSub T
    let v : Wᗮ := (S_op P.val.starProjection).inverse u
    let z : E := P.val.starProjection (v : E)
    have hz_mem : z ∈ P.val := Submodule.starProjection_apply_mem P.val (v : E)
    obtain ⟨u', hu'⟩ := hz_mem
    have hu'' : F T u' = z := hu'
    have hzU : Wᗮ.starProjection z = (u : E) :=
      congrArg Subtype.val ((hS_inv P).self_apply_inverse u)
    have hfu'U : Wᗮ.starProjection (F T u') = (u' : E) := by
      rw [hF_apply, map_add,
        Submodule.starProjection_eq_self_iff.mpr u'.2,
        (Submodule.starProjection_apply_eq_zero_iff Wᗮ).mpr (W.le_orthogonal_orthogonal (T u').2),
        add_zero]
    have hu_eq : u' = u := Subtype.ext (by rw [← hfu'U, hu'', hzU])
    have hz_eq : z = F T u := by rw [← hu'', hu_eq]
    have hzW : W.starProjection (F T u) = (T u : E) := by
      rw [hF_apply, map_add,
        (Submodule.starProjection_apply_eq_zero_iff W).mpr u.2,
        Submodule.starProjection_eq_self_iff.mpr (T u).2,
        zero_add]
    have hto : ((toHom P u : W) : E) = W.starProjection z := rfl
    rw [hto, hz_eq, hzW]
  -- Verify continuity of graphSub and toHom
  have hF_cont : Continuous F := by
    refine continuous_const.add ?_
    exact (ContinuousLinearMap.compL ℝ Wᗮ W E W.subtypeL).continuous
  have hadj_cont : Continuous (fun T : Wᗮ →L[ℝ] W => adjoint (F T)) :=
    ContinuousLinearMap.adjoint.continuous.comp hF_cont
  have hgram_cont : Continuous gram := hadj_cont.clm_comp hF_cont
  have hgram_inv_cont : Continuous (fun T : Wᗮ →L[ℝ] W => (gram T).inverse) :=
    continuous_iff_continuousAt.mpr fun T =>
      ((hgram_inv T).contDiffAt_map_inverse (n := ⊤)).continuousAt.comp hgram_cont.continuousAt
  have hgraph_cont : Continuous graphSub := by
    rw [continuous_induced_rng]
    have hfun : (fun P : G => P.val.starProjection) ∘ graphSub =
        fun T : Wᗮ →L[ℝ] W => (F T).comp ((gram T).inverse.comp (adjoint (F T))) := by
      funext T
      exact hproj_formula T
    rw [hfun]
    exact hF_cont.clm_comp (hgram_inv_cont.clm_comp hadj_cont)
  have hprojG_cont : Continuous (fun P : G => P.val.starProjection) := continuous_induced_dom
  have hS_cont : Continuous (fun P : G => S_op P.val.starProjection) :=
    continuous_const.clm_comp (hprojG_cont.clm_comp continuous_const)
  have hS_inv_cont : Continuous (fun P : G => (S_op P.val.starProjection).inverse) :=
    continuous_iff_continuousAt.mpr fun P =>
      ContinuousAt.comp (g := ContinuousLinearMap.inverse)
        (f := fun Q : G => S_op Q.val.starProjection)
        ((hS_inv P).contDiffAt_map_inverse (n := ⊤)).continuousAt hS_cont.continuousAt
  have htoHom_cont : Continuous toHom :=
    continuous_const.clm_comp (hprojG_cont.clm_comp (continuous_const.clm_comp hS_inv_cont))
  let homeo : G ≃ₜ (Wᗮ →L[ℝ] W) :=
    { toFun := toHom
      invFun := graphSub
      left_inv := hleft_inv
      right_inv := hright_inv
      continuous_toFun := htoHom_cont
      continuous_invFun := hgraph_cont }
  let : ContractibleSpace (Wᗮ →L[ℝ] W) := normedSpace_contractible (Wᗮ →L[ℝ] W)
  exact homeo.contractibleSpace

/-- Contractibility of secant-free Grassmannians on interior 2-simplices (`s.card = 3`),
whose link consists of two vertices. -/
def H1 : Prop :=
  ∀ (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
    let E := EuclideanSpace ℝ (Fin m)
    letI : DecidableEq E := Classical.decEq E
    let S (s : Finset E) := ⋃ t ∈ {t | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
      convexHull ℝ (t : Set E)
    let G (s : Finset E) := {P : Submodule ℝ E //
      Module.finrank ℝ P + 3 = m ∧ ∀ x ∈ S s, ∀ y ∈ S s, x - y ∈ P → x = y}
    let topo (s : Finset E) : TopologicalSpace (G s) :=
      TopologicalSpace.induced (fun P : G s => P.val.starProjection) inferInstance
    let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
    AffineIndependent ℝ ((↑) : K.vertices → E) → K.faces.Finite →
    (∀ s ∈ K.faces, s.card ≤ 4) →
    (∀ s ∈ K.faces, s.card = 3 → ({p : E | {p} ∈ link s} : Set E).ncard = 2) →
    ∀ s ∈ K.faces, s.card = 3 → @ContractibleSpace (G s) (topo s)

/-- Contractibility of secant-free Grassmannians on edges (`s.card = 2`),
whose link is connected and locally 2-valent. -/
def H2 : Prop :=
  ∀ (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
    let E := EuclideanSpace ℝ (Fin m)
    letI : DecidableEq E := Classical.decEq E
    let S (s : Finset E) := ⋃ t ∈ {t | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
      convexHull ℝ (t : Set E)
    let G (s : Finset E) := {P : Submodule ℝ E //
      Module.finrank ℝ P + 3 = m ∧ ∀ x ∈ S s, ∀ y ∈ S s, x - y ∈ P → x = y}
    let topo (s : Finset E) : TopologicalSpace (G s) :=
      TopologicalSpace.induced (fun P : G s => P.val.starProjection) inferInstance
    let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
    AffineIndependent ℝ ((↑) : K.vertices → E) → K.faces.Finite →
    (∀ s ∈ K.faces, s.card ≤ 4) →
    (∀ s ∈ K.faces, s.card = 2 →
      IsConnected (⋃ t ∈ link s, convexHull ℝ (t : Set E))) →
    (∀ s ∈ K.faces, s.card = 3 → ({p : E | {p} ∈ link s} : Set E).ncard = 2) →
    ∀ s ∈ K.faces, s.card = 2 → @ContractibleSpace (G s) (topo s)

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1.H1 := by
  intro h3 h2 m K
  dsimp only
  intro hind hfin hsmall hedges htriangles s hs hcard_ge
  have hcard_le : s.card ≤ 4 := hsmall s hs
  rcases (show s.card = 2 ∨ s.card = 3 ∨ s.card = 4 by omega) with hc2 | hc3 | hc4
  · exact h2 m K hind hfin hsmall hedges htriangles s hs hc2
  · exact h3 m K hind hfin hsmall htriangles s hs hc3
  · exact contractible_of_card_four m K hsmall hs hc4

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1_H1_R1
