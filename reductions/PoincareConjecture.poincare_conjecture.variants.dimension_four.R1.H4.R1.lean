import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_four_R1
import Mathlib

open CategoryTheory Limits AlgebraicTopology Set Topology

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_four_R1_H4_R1

theorem chart_inside {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (p : M) {V : Set M} (hV : IsOpen V) (hp : p ∈ V) :
    ∃ f : (EuclideanSpace ℝ (Fin 4)) → M, IsOpenEmbedding f ∧ f 0 = p ∧ range f ⊆ V := by
  let e := chartAt (EuclideanSpace ℝ (Fin 4)) p
  have hs : p ∈ e.source := mem_chart_source (EuclideanSpace ℝ (Fin 4)) p
  have ho := e.isOpen_image_source_inter hV
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ho (e p) ⟨p, ⟨hs, hp⟩, rfl⟩
  let b := OpenPartialHomeomorph.univBall (e p) r
  have hb (x : (EuclideanSpace ℝ (Fin 4))) : b x ∈ e '' (e.source ∩ V) := by
    apply hball
    rw [← OpenPartialHomeomorph.univBall_target (e p) hr]
    exact b.map_source (by simp [b, OpenPartialHomeomorph.univBall_source])
  let t := b.trans e.symm
  have ht : t.source = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨y, hy, hxy⟩ := hb x
    refine ⟨by simp [b, OpenPartialHomeomorph.univBall_source], ?_⟩
    change b x ∈ e.target
    rw [← hxy]
    exact e.map_source hy.1
  refine ⟨t, t.isOpenEmbedding ht, ?_, ?_⟩
  · change e.symm (b 0) = p
    rw [OpenPartialHomeomorph.univBall_apply_zero]
    exact e.left_inv hs
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hb x
    change e.symm (b x) ∈ V
    rw [← hxy, e.left_inv hy.1]
    exact hy.2

/-- Outside any compact set in a punctured compact four-manifold there is
an open copy of punctured four-space whose complement is compact. -/
theorem standard_neighborhoods_at_infinity {M : Type*} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (p : M)
    (K : Set (↥({p}ᶜ : Set M))) (hK : IsCompact K) :
    ∃ g : ↥(({0} : Set (EuclideanSpace ℝ (Fin 4)))ᶜ) → ↥(({p} : Set M)ᶜ),
      IsOpenEmbedding g ∧ Disjoint K (range g) ∧ IsCompact (range g)ᶜ := by
  let P := ↥(({p} : Set M)ᶜ)
  let D := ↥(({0} : Set (EuclideanSpace ℝ (Fin 4)))ᶜ)
  let i : P → M := Subtype.val
  have hp : p ∉ i '' K := by
    rintro ⟨x, _, hx⟩
    exact x.property (show x.val = p from hx)
  obtain ⟨f, hf, hzero, hav⟩ := chart_inside p (hK.image continuous_subtype_val).isClosed.isOpen_compl hp
  let g : D → P := fun x => ⟨f x, by
    intro h
    exact x.property (hf.injective ((show f x = p from h).trans hzero.symm))⟩
  have hi : IsOpenEmbedding i := isClosed_singleton.isOpen_compl.isOpenEmbedding_subtypeVal
  have hg : IsOpenEmbedding g := IsOpenEmbedding.of_comp g hi
    (hf.comp (isClosed_singleton.isOpen_compl.isOpenEmbedding_subtypeVal))
  refine ⟨g, hg, Set.disjoint_left.mpr ?_, ?_⟩
  · rintro y hy ⟨x, rfl⟩
    exact hav ⟨x.val, rfl⟩ ⟨g x, hy, rfl⟩
  · have heq : i '' (range g)ᶜ = (range f)ᶜ := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩ ⟨x, hx⟩
        have hx0 : x ≠ 0 := by
          rintro rfl
          exact z.property (hx.symm.trans hzero)
        exact hz ⟨⟨x, hx0⟩, Subtype.ext hx⟩
      · intro hy
        have hne : y ≠ p := fun he => hy ⟨0, hzero.trans he.symm⟩
        refine ⟨⟨y, hne⟩, ?_, rfl⟩
        rintro ⟨x, hx⟩
        exact hy ⟨x.val, congrArg Subtype.val hx⟩
    exact hi.isInducing.isCompact_iff.mpr (heq ▸ hf.isOpen_range.isClosed_compl.isCompact)

/-- Removing a point from a simply connected four-manifold preserves simple connectivity. -/
def H1 : Prop := ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [SimplyConnectedSpace M] (p : M),
    SimplyConnectedSpace (↥(({p} : Set M)ᶜ))

/-- In degree two a puncture preserves vanishing of integral homology.
Excision reduces the relative groups in degrees two and three to a punctured ball. -/
def H2 : Prop := ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (p : M),
    IsZero (((singularHomologyFunctor AddCommGrpCat 2).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of M)) →
    IsZero (((singularHomologyFunctor AddCommGrpCat 2).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of (↥(({p} : Set M)ᶜ))))

/-- Open four-manifold recognition with a standard end. The displayed end
condition gives cofinal connected, simply connected neighborhoods of infinity.
Together with the fundamental group and homology hypotheses, this is the
standard-end case of Freedman (1982), Corollary 1.2, p. 366. -/
def H3 : Prop := ∀ (X : Type) [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) X] [SecondCountableTopology X]
    [SimplyConnectedSpace X],
    IsZero (((singularHomologyFunctor AddCommGrpCat 2).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of X)) →
    (∀ K : Set X, IsCompact K →
      ∃ g : ↥(({0} : Set (EuclideanSpace ℝ (Fin 4)))ᶜ) → X,
        IsOpenEmbedding g ∧ Disjoint K (range g) ∧ IsCompact (range g)ᶜ) →
    Nonempty (X ≃ₜ EuclideanSpace ℝ (Fin 4))

theorem main : H1 → H2 → H3 → OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_four_R1.H4 := by
  intro simple homology recognize M _ _ _ _ _ _ hM
  obtain ⟨p⟩ := (inferInstance : Nonempty M)
  let U : TopologicalSpace.Opens M := ⟨({p} : Set M)ᶜ, isClosed_singleton.isOpen_compl⟩
  let : SimplyConnectedSpace U := simple M p
  exact ⟨p, recognize U (homology M p hM) (standard_neighborhoods_at_infinity p)⟩

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_four_R1_H4_R1
