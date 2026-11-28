import OMAReductions.R_Erdos910_erdos_910_variants_rudin_CH_R1

-- Step Erdos910.erdos_910.variants.rudin_CH.R1.H2: hypothesis H2 of reduction Erdos910.erdos_910.variants.rudin_CH.R1
-- Credit: @PanPapag
-- H2 := let E := EuclideanSpace ℝ (Fin 2)   let J := Closeds E ⊕ {B : Set E // B.Countable}   ((ℵ₁ : Cardinal.{0}) = 𝔠) → ∃ r : J → J → Prop, IsWellOrder J r ∧ ∀ i, {j | r j i}.Countable

open Cardinal Set TopologicalSpace
open scoped Cardinal

theorem OMA.solution : OMA.R_Erdos910_erdos_910_variants_rudin_CH_R1.H2 := by
  classical
  let E := EuclideanSpace ℝ (Fin 2)
  let C := {s : Set E // s.Countable}
  let J := Closeds E ⊕ C
  intro ch
  have plane : #E = 𝔠 := by
    rw [mk_congr (WithLp.equiv 2 (Fin 2 → ℝ)), mk_arrow]
    simp [mk_real]
    rw [show (2 : Cardinal) = 1+1 by norm_num, power_add, power_one, continuum_mul_self]
  let enumerate : Option (ℕ → E) → C
    | none => ⟨∅, countable_empty⟩
    | some f => ⟨range f, countable_range f⟩
  have onto : Function.Surjective enumerate := by
    rintro ⟨s, hs⟩
    rcases s.eq_empty_or_nonempty with rfl | hn
    · exact ⟨none, rfl⟩
    · obtain ⟨f, rfl⟩ := hs.exists_eq_range hn
      exact ⟨some f, rfl⟩
  have small : #C ≤ 𝔠 := by
    refine (mk_le_of_surjective onto).trans_eq ?_
    simp [mk_option, plane, continuum_power_aleph0]
    exact continuum_add_nat 1
  let close : C → Closeds E := fun s => ⟨closure s.val, isClosed_closure⟩
  have covers : Function.Surjective close := by
    intro F
    obtain ⟨d, hd, dense⟩ := exists_countable_dense F
    refine ⟨⟨Subtype.val '' d, hd.image _⟩, SetLike.coe_injective ?_⟩
    change closure (Subtype.val '' d) = (F : Set E)
    apply le_antisymm (closure_minimal (by rintro _ ⟨x, _, rfl⟩; exact x.property) F.isClosed)
    simpa using continuous_subtype_val.range_subset_closure_image_dense dense
  have bound : #J ≤ ℵ₁ := by
    rw [ch]
    change #(Closeds E ⊕ C) ≤ _
    simpa [mk_sum, continuum_add_self] using
      add_le_add ((mk_le_of_surjective covers).trans small) small
  obtain ⟨r, hr, htype⟩ := exists_ord_eq J
  refine ⟨r, hr, fun i => ?_⟩
  apply le_aleph0_iff_set_countable.mp
  exact lt_aleph_one_iff.mp ((card_typein_lt i htype).trans_le bound)
