import FormalConjectures.Millennium.Poincare

/-!
Credit: @willspag

Topological recognition and uniqueness of smoothing give two independent
ways to share work on the smooth three-sphere. For the topological step,
the spherical-covering formulation of elliptization is one route. For the
second step, a homeomorphism supplies the compactness of its source, and
compact locally Euclidean spaces are second countable. The smoothing step
asserts the existence of a diffeomorphism, which can differ from the
homeomorphism supplied by the first step.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_for_three_R1

open scoped Manifold ContDiff EuclideanGeometry ContinuousMap unitInterval Topology
open Set Filter OpenPartialHomeomorph

universe u

def H1 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M],
    (M ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) →
      Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

def H2 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [SecondCountableTopology M],
    (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) →
      Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

/-- Encode the inverse homotopy path of each point by its starting coordinate in K
and the coordinates of each point on the path in every chart centered on the path.
Paths with identical codes agree on a closed and open subset of the unit interval. -/
lemma small_of_small_homotopy_model (E K : Type) [TopologicalSpace E] [TopologicalSpace K]
    (M : Type u) [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    (h : M ≃ₕ K) : Small.{0} M := by
  classical
  obtain ⟨H⟩ := h.left_inv
  let path (x : M) (t : I) := H (t, x)
  have cont (x : M) : Continuous (path x) :=
    H.continuous.comp (continuous_id.prodMk continuous_const)
  let code (x : M) : K × (I → I → E) :=
    (h x, fun s t => chartAt E (path x s) (path x t))
  refine small_of_injective (f := code) ?_
  intro x y hxy
  have hstart : h x = h y := congrArg Prod.fst hxy
  have coords (s t : I) :
      chartAt E (path x s) (path x t) = chartAt E (path y s) (path y t) :=
    congrFun (congrFun (congrArg Prod.snd hxy) s) t
  let S : Set I := {t | path x t = path y t}
  have hclosed : IsClosed S := isClosed_eq (cont x) (cont y)
  have hopen : IsOpen S := by
    refine isOpen_iff_mem_nhds.mpr ?_
    intro s hs
    change path x s = path y s at hs
    let e := chartAt E (path x s)
    have hx : e.source ∈ 𝓝 (path x s) := e.open_source.mem_nhds (mem_chart_source _ _)
    have hy : e.source ∈ 𝓝 (path y s) := hs ▸ hx
    filter_upwards [(cont x).continuousAt hx, (cont y).continuousAt hy] with t ht hu
    apply e.injOn ht hu
    simpa only [← hs] using coords s t
  have hzero : (0 : I) ∈ S := by
    change H (0, x) = H (0, y)
    simpa using congrArg h.invFun hstart
  have hall := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, hzero⟩
  have hone : (1 : I) ∈ S := hall.symm ▸ Set.mem_univ _
  change H (1, x) = H (1, y) at hone
  simpa using hone

/-- Transfer the smooth atlas to a small representative so both hypotheses apply
in the same universe. The chart transport adapts the argument in the project's
smooth_other_cases.R1 reduction (PR 4745) to an arbitrary equivalence. -/
lemma smooth_sphere_of_topological_recognition : H1 → H2 →
    type_of% @PoincareConjecture.poincare_conjecture.variants.smooth_for_three.{u} := by
  intro recognize smooth M _ _ _ _ h
  classical
  let E := EuclideanSpace ℝ (Fin 3)
  let _ : Small.{0} M := small_of_small_homotopy_model E _ M h
  let N := Shrink.{0} M
  let q : N ≃ M := (equivShrink M).symm
  let _ : TopologicalSpace N := TopologicalSpace.induced q inferInstance
  let e : N ≃ₜ M :=
    { toEquiv := q
      continuous_toFun := continuous_induced_dom
      continuous_invFun := continuous_induced_rng.mpr (by simpa using (continuous_id : Continuous (id : M → M))) }
  let _ : T2Space N := e.isEmbedding.t2Space
  let _ : ChartedSpace E N :=
    { atlas := e.transOpenPartialHomeomorph '' atlas E M
      chartAt x := e.transOpenPartialHomeomorph (chartAt E (e x))
      mem_chart_source x := mem_chart_source E (e x)
      chart_mem_atlas x := ⟨_, chart_mem_atlas E (e x), rfl⟩ }
  have : IsManifold (𝓡 3) ∞ N := by
    refine { compatible := ?_ }
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    simp only [Homeomorph.transOpenPartialHomeomorph_eq_trans, trans_symm_eq_symm_trans_symm,
      trans_assoc, ← Homeomorph.symm_toOpenPartialHomeomorph]
    rw [← trans_assoc e.symm.toOpenPartialHomeomorph e.toOpenPartialHomeomorph b,
      ← Homeomorph.trans_toOpenPartialHomeomorph, Homeomorph.symm_trans_self,
      Homeomorph.refl_toOpenPartialHomeomorph, refl_trans]
    exact (contDiffGroupoid ∞ (𝓡 3)).compatible ha hb
  have hdown : ContMDiff (𝓡 3) (𝓡 3) ∞ e := by
    intro x
    let a := chartAt E (e x)
    let b := chartAt E x
    have hb : b = e.transOpenPartialHomeomorph a := rfl
    have hcomp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (a.symm ∘ b) b.source := by
      apply contMDiffOn_chart_symm.comp contMDiffOn_chart
      change Set.MapsTo b b.source a.target
      rw [hb]
      exact (e.transOpenPartialHomeomorph a).mapsTo
    apply (hcomp.congr ?_).contMDiffAt (b.open_source.mem_nhds (mem_chart_source E x))
    intro y hy
    rw [hb] at hy ⊢
    exact (a.left_inv hy).symm
  have hup : ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm := by
    intro x
    let a := chartAt E x
    let b := chartAt E (e.symm x)
    have hb : b = e.transOpenPartialHomeomorph a := by
      change e.transOpenPartialHomeomorph (chartAt E (e (e.symm x))) = _
      rw [e.apply_symm_apply]
    have hcomp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (b.symm ∘ a) a.source := by
      apply contMDiffOn_chart_symm.comp contMDiffOn_chart
      change Set.MapsTo a a.source b.target
      rw [hb]
      exact a.mapsTo
    apply (hcomp.congr ?_).contMDiffAt (a.open_source.mem_nhds (mem_chart_source E x))
    intro y hy
    rw [hb]
    change e.symm y = e.symm (a.symm (a y))
    rw [a.left_inv hy]
  let lift : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N := ⟨e.symm.toEquiv, hup, hdown⟩
  obtain ⟨f⟩ := recognize N (e.toHomotopyEquiv.trans h)
  let _ : CompactSpace N := f.symm.compactSpace
  let _ : SecondCountableTopology N := ChartedSpace.secondCountable_of_sigmaCompact E N
  obtain ⟨d⟩ := smooth N f
  exact ⟨lift.trans d⟩

theorem main : H1 → H2 → type_of% @PoincareConjecture.poincare_conjecture.variants.smooth_for_three := by
  exact smooth_sphere_of_topological_recognition

end OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_for_three_R1
