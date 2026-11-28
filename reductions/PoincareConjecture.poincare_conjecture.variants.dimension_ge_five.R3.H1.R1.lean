import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R3

/-! Removing the open unit ball in a chart around a contractible puncture
gives a compact contractible exterior. The radial projection on the
punctured closed ball glues to the identity on its exterior. -/

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R3_H1_R1

open Set Metric Topology
open scoped ContinuousMap

private theorem contractible_of_left_inverse {P D : Type*}
    [TopologicalSpace P] [ContractibleSpace P] [TopologicalSpace D]
    (i : C(D, P)) (r : C(P, D)) (h : Function.LeftInverse r i) : ContractibleSpace D := by
  have hn := ((id_nullhomotopic P).comp_left i).comp_right r
  have heq : r.comp ((ContinuousMap.id P).comp i) = ContinuousMap.id D := by
    ext x
    exact h x
  exact (contractible_iff_id_nullhomotopic D).2 (heq ▸ hn)

private theorem centered_chart {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (p : M) :
    ∃ e : OpenPartialHomeomorph E M, e.source = univ ∧ e 0 = p := by
  let c := chartAt E p
  have ps : p ∈ c.source := mem_chart_source E p
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp c.open_target (c p) (c.map_source ps)
  let b : OpenPartialHomeomorph E E := OpenPartialHomeomorph.univBall (c p) r
  have bv : b.source = univ := OpenPartialHomeomorph.univBall_source _ _
  have bt : b.target = ball (c p) r := OpenPartialHomeomorph.univBall_target _ hr
  refine ⟨b.trans c.symm, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source, bv, univ_inter]
    apply eq_univ_of_forall
    intro x
    apply hsub
    rw [← bt]
    exact b.map_source (by rw [bv]; exact mem_univ _)
  · rw [OpenPartialHomeomorph.trans_apply]
    change c.symm (OpenPartialHomeomorph.univBall (c p) r 0) = p
    rw [OpenPartialHomeomorph.univBall_apply_zero, c.left_inv ps]

private theorem chart_exterior {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M]
    (p : M) [ContractibleSpace ↥(({p} : Set M)ᶜ)] :
    ∃ χ : E → M, IsOpenEmbedding χ ∧
      IsCompact (χ '' ball 0 1)ᶜ ∧ ContractibleSpace ↥((χ '' ball 0 1)ᶜ) := by
  classical
  obtain ⟨e, he, h0⟩ := centered_chart (E := E) p
  have hemb := e.isOpenEmbedding he
  let V : Set M := e '' ball 0 1
  let P := ↥(({p} : Set M)ᶜ)
  let D := ↥(Vᶜ)
  let inside : Set P := (Subtype.val : P → M) ⁻¹' (e '' closedBall 0 1)
  let outside : Set P := (Subtype.val : P → M) ⁻¹' Vᶜ
  have openV : IsOpen V := hemb.isOpenMap _ isOpen_ball
  have hpV : p ∈ V := ⟨0, mem_ball_self zero_lt_one, h0⟩
  have ic : IsClosed inside :=
    ((isCompact_closedBall (0 : E) 1).image hemb.continuous).isClosed.preimage continuous_subtype_val
  have oc : IsClosed outside := openV.isClosed_compl.preimage continuous_subtype_val
  have cover : inside ∪ outside = univ := by
    apply eq_univ_of_forall
    intro y
    by_cases hy : (y : M) ∈ V
    · left
      exact image_mono ball_subset_closedBall hy
    · exact Or.inr hy
  have inv_in (y : P) (hy : y ∈ inside) : (y : M) ∈ e.target := by
    obtain ⟨x, _, hx⟩ := hy
    rw [← hx]
    exact e.map_source (by rw [he]; exact mem_univ _)
  have inv_ne (y : P) (hy : y ∈ inside) : e.symm (y : M) ≠ 0 := by
    intro hn
    have hy0 : (y : M) = p := by
      rw [← e.right_inv (inv_in y hy), hn, h0]
    exact y.property (Set.mem_singleton_iff.mpr hy0)
  let radial (y : P) : E := ‖e.symm (y : M)‖⁻¹ • e.symm (y : M)
  let cap (y : P) : M := e (radial y)
  have radial_norm (y : P) (hy : y ∈ inside) : ‖radial y‖ = 1 := by
    have hn := norm_ne_zero_iff.mpr (inv_ne y hy)
    change ‖‖e.symm (y : M)‖⁻¹ • e.symm (y : M)‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]
  have cap_in (y : P) (hy : y ∈ inside) : cap y ∈ Vᶜ := by
    change cap y ∉ V
    rintro ⟨z, hz, eq⟩
    have hz' : z = radial y := hemb.injective eq
    exact (not_lt_of_ge (radial_norm y hy).ge) (by simpa [hz'] using mem_ball_zero_iff.mp hz)
  have agree (y : P) (hy : y ∈ inside) (ho : y ∈ outside) : cap y = (y : M) := by
    obtain ⟨x, hx, hxy⟩ := hy
    have hsrc : x ∈ e.source := by rw [he]; exact mem_univ _
    have hinv : e.symm (y : M) = x := by rw [← hxy, e.left_inv hsrc]
    have hxlo : 1 ≤ ‖x‖ := by
      apply le_of_not_gt
      exact fun h ↦ ho ⟨x, mem_ball_zero_iff.mpr h, hxy⟩
    have hnorm : ‖x‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp hx) hxlo
    simp [cap, radial, hinv, hnorm, hxy]
  have invCont : ContinuousOn (fun y : P ↦ e.symm (y : M)) inside :=
    e.continuousOn_symm.comp continuous_subtype_val.continuousOn inv_in
  have capCont : ContinuousOn cap inside :=
    hemb.continuous.comp_continuousOn
      ((invCont.norm.inv₀ fun y hy ↦ norm_ne_zero_iff.mpr (inv_ne y hy)).smul invCont)
  let project (y : P) : M := if y ∈ inside then cap y else (y : M)
  have projectInside : ContinuousOn project inside :=
    capCont.congr fun y hy ↦ if_pos hy
  have outside_eq (y : P) (ho : y ∈ outside) : project y = (y : M) := by
    by_cases hy : y ∈ inside
    · simpa [project, hy] using agree y hy ho
    · exact if_neg hy
  have projectOutside : ContinuousOn project outside :=
    continuous_subtype_val.continuousOn.congr outside_eq
  have projectCont : Continuous project := by
    rw [← continuousOn_univ, ← cover]
    exact projectInside.union_of_isClosed projectOutside ic oc
  have projectV (y : P) : project y ∈ Vᶜ := by
    by_cases hy : y ∈ inside
    · simpa [project, hy] using cap_in y hy
    · have ho : y ∈ outside := by
        have hu : y ∈ inside ∪ outside := by rw [cover]; exact mem_univ _
        exact hu.resolve_left hy
      rw [outside_eq y ho]
      change (y : M) ∈ Vᶜ at ho
      exact ho
  let i : C(D, P) :=
    ⟨fun y ↦ ⟨y.val, fun h ↦ y.property ((Set.mem_singleton_iff.mp h).symm ▸ hpV)⟩,
      continuous_subtype_val.subtype_mk _⟩
  let r : C(P, D) := ⟨fun y ↦ ⟨project y, projectV y⟩, projectCont.subtype_mk _⟩
  have hri : Function.LeftInverse r i := fun y ↦ Subtype.ext (outside_eq (i y) y.property)
  exact ⟨e, hemb, openV.isClosed_compl.isCompact, contractible_of_left_inverse i r hri⟩

/-- A homotopy sphere is compact. This has a separate proof in the second
reduction of the original problem. -/
def H1 : Prop :=
  ∀ (n : ℕ), 5 ≤ n → ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M],
    M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → CompactSpace M

/-- Puncture contractibility for a compact homotopy sphere. -/
def H2 : Prop :=
  ∀ (n : ℕ), 5 ≤ n → ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M],
    M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
    ∃ p : M, ContractibleSpace ↥(({p} : Set M)ᶜ)

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R3.H1 := by
  intro compact puncture n hn M _ _ _ e
  let _ := compact n hn M e
  obtain ⟨p, contract⟩ := puncture n hn M e
  let _ := contract
  exact chart_exterior p

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R3_H1_R1
