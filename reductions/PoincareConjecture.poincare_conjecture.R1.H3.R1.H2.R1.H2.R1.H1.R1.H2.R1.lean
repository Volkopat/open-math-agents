import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1
import Mathlib

/-!
# Cairns' transverse plane field construction via skeleton extension and foliated smoothing

To construct smooth local submersions `R : E → E →L[ℝ] ℝ³` whose kernels define a locally
leaf-constant transverse `(m - 3)`-plane field `P` over the geometric carrier `K.space` of a
finite pure 3-dimensional simplicial complex `K`:

1. **`H1` (Continuous skeleton-by-skeleton section)**: Using nonemptiness of the secant-free
   Grassmannian `G s` on vertices (`s.card = 1`) and contractibility of `G s` on higher faces
   (`2 ≤ s.card`), construct a continuous `(m - 3)`-plane field `P₀ : K.space → Submodule ℝ E`
   such that `P₀ x` avoids all secants of the closed star `S s` whenever `x ∈ convexHull ℝ s`.
2. **`H2` (Ambient foliated smoothing)**: Smooth and locally foliate `P₀` on an open neighborhood
   `W` of `K.space` in `E`, yielding `P : E → Submodule ℝ E` with smooth orthogonal projection
   `y ↦ (P y).starProjection` on `W`, codimension 3, local secant-freeness along `K.space`, and
   local leaf constancy `z - y ∈ P y → P z = P y`.
3. **Submersion assembly (proved in `main`)**: Around each `a : K.space`, identify `(P a)ᗮ ≃L[ℝ] ℝ³`
   and set `R y := e ∘ (P a)ᗮ.orthogonalProjectionOnto ∘ (id - (P y).starProjection)`. On the open
   neighborhood `U = W ∩ {y | ‖(P y).starProjection - (P a).starProjection‖ < 1}` of `a`, a direct
   operator-norm contraction bound shows `(R y).ker = P y`, while `R a` is surjective and locally
   injective on `K.space`.
-/

open Geometry Set Filter Metric ContinuousLinearMap
open scoped ContDiff Topology

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1_H2_R1

/-- If two closed subspaces `P_y, P_a` of a Hilbert space satisfy
`‖P_y.starProjection - P_a.starProjection‖ < 1`, then `(P_a)ᗮ.starProjection` is injective on
`(P_y)ᗮ`, so `(P_a)ᗮ.orthogonalProjectionOnto ∘ (id - P_y.starProjection)` has kernel `P_y`. -/
private theorem ker_proj_comp_compl_eq {E V : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Pa Py : Submodule ℝ E} (e : Paᗮ ≃L[ℝ] V)
    (hdist : ‖Py.starProjection - Pa.starProjection‖ < 1) :
    (((e : Paᗮ →L[ℝ] V).comp
      (Paᗮ.orthogonalProjectionOnto.comp
        (ContinuousLinearMap.id ℝ E - Py.starProjection))).ker) = Py := by
  ext x
  change e (Paᗮ.orthogonalProjectionOnto (x - Py.starProjection x)) = 0 ↔ x ∈ Py
  constructor
  · intro hx
    let u : E := x - Py.starProjection x
    have horth0 : Paᗮ.orthogonalProjectionOnto u = 0 :=
      e.injective (hx.trans (map_zero e).symm)
    have hproj0 : Paᗮ.starProjection u = 0 := congrArg Subtype.val horth0
    have hu_Pa_orth_orth : u ∈ Paᗮᗮ :=
      (Submodule.starProjection_apply_eq_zero_iff Paᗮ).mp hproj0
    have hu_Pa : u ∈ Pa := by rwa [Submodule.orthogonal_orthogonal] at hu_Pa_orth_orth
    have hu_Pa_eq : Pa.starProjection u = u := Submodule.starProjection_eq_self_iff.mpr hu_Pa
    have hu_Py_orth : u ∈ Pyᗮ := Submodule.sub_starProjection_mem_orthogonal x
    have hu_Py_eq : Py.starProjection u = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff Py).mpr hu_Py_orth
    have hu_diff : (Py.starProjection - Pa.starProjection) u = -u := by
      simp [hu_Py_eq, hu_Pa_eq]
    have hnorm_le : ‖u‖ ≤ ‖Py.starProjection - Pa.starProjection‖ * ‖u‖ := by
      calc
        ‖u‖ = ‖-u‖ := (norm_neg u).symm
        _ = ‖(Py.starProjection - Pa.starProjection) u‖ := by rw [hu_diff]
        _ ≤ ‖Py.starProjection - Pa.starProjection‖ * ‖u‖ :=
          (Py.starProjection - Pa.starProjection).le_opNorm u
    have hu0 : u = 0 := by
      by_contra hne
      have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hne
      have hlt : ‖Py.starProjection - Pa.starProjection‖ * ‖u‖ < 1 * ‖u‖ :=
        mul_lt_mul_of_pos_right hdist hpos
      linarith
    have hx_eq : x = Py.starProjection x := sub_eq_zero.mp hu0
    rw [hx_eq]
    exact Submodule.starProjection_apply_mem Py x
  · intro hx
    have hx_eq : Py.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
    simp [hx_eq]

/-- Continuous assignment of star-secant-free `(m - 3)`-planes over `K.space` obtained from
nonemptiness on 0-simplices and contractibility on higher simplices. -/
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
    K.faces.Finite → (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) →
    (∀ s ∈ K.faces, s.card = 1 → Nonempty (G s)) →
    (∀ s ∈ K.faces, 2 ≤ s.card → @ContractibleSpace (G s) (topo s)) →
    ∃ P₀ : K.space → Submodule ℝ E,
      Continuous (fun x : K.space => (P₀ x).starProjection) ∧
      (∀ x : K.space, Module.finrank ℝ (P₀ x) + 3 = m) ∧
      (∀ x : K.space, ∀ s ∈ K.faces, (x : E) ∈ convexHull ℝ (s : Set E) →
        ∀ u ∈ S s, ∀ v ∈ S s, u - v ∈ P₀ x → u = v)

/-- Ambient smoothing and local leaf-foliation of a continuous star-transverse `(m - 3)`-plane
field in a neighborhood of `K.space`. -/
def H2 : Prop :=
  ∀ (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
    let E := EuclideanSpace ℝ (Fin m)
    letI : DecidableEq E := Classical.decEq E
    let S (s : Finset E) := ⋃ t ∈ {t | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
      convexHull ℝ (t : Set E)
    K.faces.Finite → (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) →
    ∀ P₀ : K.space → Submodule ℝ E,
      Continuous (fun x : K.space => (P₀ x).starProjection) →
      (∀ x : K.space, Module.finrank ℝ (P₀ x) + 3 = m) →
      (∀ x : K.space, ∀ s ∈ K.faces, (x : E) ∈ convexHull ℝ (s : Set E) →
        ∀ u ∈ S s, ∀ v ∈ S s, u - v ∈ P₀ x → u = v) →
      ∃ (W : Set E) (P : E → Submodule ℝ E),
        IsOpen W ∧ K.space ⊆ W ∧
        ContDiffOn ℝ ∞ (fun y : E => (P y).starProjection) W ∧
        (∀ y ∈ W, Module.finrank ℝ (P y) + 3 = m) ∧
        (∀ a : K.space, ∃ r : ℝ, 0 < r ∧
          ∀ u ∈ K.space ∩ ball (a : E) r, ∀ v ∈ K.space ∩ ball (a : E) r,
            u - v ∈ P (a : E) → u = v) ∧
        (∀ y ∈ W, ∀ᶠ z in 𝓝 y, z - y ∈ P y → P z = P y)

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1.H2 := by
  intro hsec hfol m K
  dsimp only
  let E := EuclideanSpace ℝ (Fin m)
  let V := EuclideanSpace ℝ (Fin 3)
  let : DecidableEq E := Classical.decEq E
  intro hfin hpure h1 h2
  obtain ⟨P₀, hP₀_cont, hP₀_dim, hP₀_star⟩ := hsec m K hfin hpure h1 h2
  obtain ⟨W, P, hW_open, hKW, hP_smooth, hP_dim, hP_loc, hP_leaf⟩ :=
    hfol m K hfin hpure P₀ hP₀_cont hP₀_dim hP₀_star
  refine ⟨P, fun a => ?_⟩
  have haW : (a : E) ∈ W := hKW a.2
  let Pa : Submodule ℝ E := P (a : E)
  have hdimE : Module.finrank ℝ E = m := finrank_euclideanSpace_fin
  have hdimV : Module.finrank ℝ V = 3 := finrank_euclideanSpace_fin
  have hsumPa : Module.finrank ℝ Pa + Module.finrank ℝ Paᗮ = m :=
    Pa.finrank_add_finrank_orthogonal.trans hdimE
  have hdimPa : Module.finrank ℝ Pa + 3 = m := hP_dim (a : E) haW
  have hdimOrth : Module.finrank ℝ Paᗮ = Module.finrank ℝ V := by omega
  let e : Paᗮ ≃L[ℝ] V := (LinearEquiv.ofFinrankEq Paᗮ V hdimOrth).toContinuousLinearEquiv
  let R : E → E →L[ℝ] V := fun y =>
    (e : Paᗮ →L[ℝ] V).comp
      (Paᗮ.orthogonalProjectionOnto.comp
        (ContinuousLinearMap.id ℝ E - (P y).starProjection))
  let diffMap : E → E →L[ℝ] E := fun y => (P y).starProjection - Pa.starProjection
  have hdiff_cont : ContinuousOn diffMap W :=
    hP_smooth.continuousOn.sub continuousOn_const
  let U : Set E := W ∩ diffMap ⁻¹' ball 0 1
  have hU_open : IsOpen U := hdiff_cont.isOpen_inter_preimage hW_open isOpen_ball
  have haU : (a : E) ∈ U := ⟨haW, by simp [diffMap, Pa]⟩
  have hR_smooth : ContDiffOn ℝ ∞ R U := by
    have h1_smooth : ContDiffOn ℝ ∞ (fun y : E => ContinuousLinearMap.id ℝ E - (P y).starProjection) U :=
      contDiffOn_const.sub (hP_smooth.mono Set.inter_subset_left)
    exact contDiffOn_const.clm_comp (contDiffOn_const.clm_comp h1_smooth)
  have hR_surj : Function.Surjective (R (a : E)) := by
    intro v
    let w : Paᗮ := e.symm v
    refine ⟨(w : E), ?_⟩
    have hw_proj0 : Pa.starProjection (w : E) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff Pa).mpr w.2
    have hw_orth : Paᗮ.orthogonalProjectionOnto (w : E) = w :=
      Subtype.ext (Submodule.starProjection_eq_self_iff.mpr w.2)
    change e (Paᗮ.orthogonalProjectionOnto ((w : E) - Pa.starProjection (w : E))) = v
    rw [hw_proj0, sub_zero, hw_orth, e.apply_symm_apply]
  have hR_ker : ∀ y ∈ U, (R y).ker = P y := by
    intro y hy
    have hnorm : ‖(P y).starProjection - Pa.starProjection‖ < 1 := by
      simpa [diffMap, mem_ball_zero_iff] using hy.2
    exact ker_proj_comp_compl_eq e hnorm
  obtain ⟨r, hr_pos, hsec_a⟩ := hP_loc a
  have hR_inj : InjOn (R (a : E)) (K.space ∩ ball (a : E) r) := by
    intro x hx y hy hxy
    have hmem_ker : x - y ∈ (R (a : E)).ker := by
      change R (a : E) (x - y) = 0
      rw [map_sub, hxy, sub_self]
    rw [hR_ker (a : E) haU] at hmem_ker
    exact hsec_a x hx y hy hmem_ker
  refine ⟨U, R, r, hU_open, haU, hR_smooth, hR_surj, hr_pos, hR_inj, hR_ker, ?_⟩
  intro y hy
  exact hP_leaf y hy.1

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1_H2_R1
