import OMAReductions.R_LatinTableau_SimpleGraph_LatinTableauConjecture_R1
import Mathlib

open SimpleGraph BigOperators

private theorem rectangleColoring {V : Type} [Fintype V] {s t : ℕ}
    (hst : s ≤ t) (e : V ≃ Fin s × Fin t) (G : SimpleGraph V)
    (hAdj : ∀ x y, G.Adj x y ↔ x ≠ y ∧ ((e x).1 = (e y).1 ∨ (e x).2 = (e y).2)) :
    G.CDSColorable := by
  classical
  by_cases ht : t = 0
  · subst t
    have : IsEmpty V := ⟨fun v => Fin.elim0 (e v).2⟩
    refine ⟨Coloring.ofIsEmpty, fun k => ?_⟩
    have hzero (A : Set V) : A.ncard = 0 := by
      have : IsEmpty A := ⟨fun a => isEmptyElim a.val⟩
      simp [Set.eq_empty_of_isEmpty A]
    have hsets : ∃ f : Fin k → Set V, ∀ i, G.IsIndepSet (f i) := ⟨fun _ => ∅, by simp⟩
    simp [indepNumK, hzero, hsets, eq_comm]
  have : NeZero t := ⟨ht⟩
  let z := ZMod.finEquiv t
  let row (a : Fin s) : ZMod t := z (Fin.castLE hst a)
  have hrow : Function.Injective row := fun _ _ h => Fin.ext (congrArg (fun i : Fin t => i.val) (z.injective h))
  let colorFin (x : V) : Fin t := z.symm (row (e x).1 + z (e x).2)
  let C : G.Coloring ℕ := Coloring.mk (fun x => (colorFin x).val) (by
    intro x y hxy hcol
    obtain ⟨hne, h⟩ := (hAdj x y).mp hxy
    have heq := z.symm.injective (Fin.ext hcol : colorFin x = colorFin y)
    apply hne
    apply e.injective
    rcases h with h₁ | h₂
    · rw [h₁] at heq
      exact Prod.ext h₁ (z.injective (add_left_cancel heq))
    · rw [h₂] at heq
      exact Prod.ext (hrow (add_right_cancel heq)) h₂)
  have hcard (i : Fin t) : (C.colorClass i.val).ncard = s := by
    let col : {x : V // x ∈ C.colorClass i.val} ≃ Fin s :=
      { toFun := fun x => (e x.1).1
        invFun := fun a => ⟨e.symm (a, z.symm (z i - row a)), by
          change (colorFin (e.symm (a, z.symm (z i - row a)))).val = i.val
          simp [colorFin, add_sub_cancel]⟩
        left_inv := by
          intro x
          apply Subtype.ext
          apply e.injective
          simp only [Equiv.apply_symm_apply]
          refine Prod.ext rfl ?_
          have hi : colorFin x.val = i := Fin.ext x.property
          have hi' : row (e x.val).1 + z (e x.val).2 = z i := by
            simpa [colorFin] using congrArg z hi
          rw [← hi', add_comm, add_sub_cancel_right, RingEquiv.symm_apply_apply]
        right_inv := by intro a; simp }
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, Fintype.card_congr col, Fintype.card_fin]
  have hsmall (k : ℕ) (hk : k ≤ t) : (∑ i < k, (C.colorClass i).ncard) = k * s := by
    calc
      (∑ i < k, (C.colorClass i).ncard) = ∑ _i ∈ Finset.range k, s := Finset.sum_congr (Nat.Iio_eq_range k) fun i hi =>
        hcard ⟨i, (Finset.mem_range.mp hi).trans_le hk⟩
      _ = _ := by simp
  have hindep (A : Set V) (hA : G.IsIndepSet A) : A.ncard ≤ s := by
    simpa using Set.ncard_le_ncard_of_injOn (fun x => (e x).1)
      (t := (Set.univ : Set (Fin s))) (fun _ _ => Set.mem_univ _) (by
        intro x hx y hy h
        by_contra hne
        exact hA hx hy hne ((hAdj x y).mpr ⟨hne, Or.inl h⟩))
  refine ⟨C, fun k => ?_⟩
  simp only [Nat.Iio_eq_range]
  let sizes : Set ℕ := {n | ∃ f : Fin k → Set V, (∀ i, G.IsIndepSet (f i)) ∧ (⋃ i, f i).ncard = n}
  have htotal (A : Set V) : A.ncard ≤ s * t := by
    have hc : A.ncard ≤ (Set.univ : Set V).ncard := Set.ncard_le_ncard (Set.subset_univ A)
    simpa [Fintype.card_congr e] using hc
  have hbound : BddAbove sizes := ⟨s * t, by
    rintro n ⟨f, _, rfl⟩
    exact htotal _⟩
  change _ = sSup sizes
  apply le_antisymm
  · apply le_csSup hbound
    refine ⟨fun i => C.colorClass i.val, fun i => C.isIndepSet_colorClass _, ?_⟩
    rw [Set.ncard_iUnion_of_finite (fun _ => Set.toFinite _) (by
      intro i j hij
      refine Set.disjoint_left.mpr fun x hx hy => hij (Fin.ext (hx.symm.trans hy)))]
    rw [finsum_eq_sum_of_fintype]
    exact Fin.sum_univ_eq_sum_range (fun i => (C.colorClass i).ncard) k
  · apply csSup_le
    · exact ⟨0, fun _ => ∅, by simp⟩
    rintro n ⟨f, hf, rfl⟩
    by_cases hk : k ≤ t
    · rw [← Nat.Iio_eq_range, hsmall k hk]
      exact (Set.ncard_iUnion_le_of_fintype f).trans (by
        calc
          _ ≤ ∑ _i : Fin k, s := Finset.sum_le_sum fun i _ => hindep _ (hf i)
          _ = _ := by simp)
    · calc
        _ ≤ s * t := htotal _
        _ = (∑ i ∈ Finset.range t, (C.colorClass i).ncard) := by
          rw [← Nat.Iio_eq_range, hsmall t le_rfl, mul_comm]
        _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

theorem OMA.solution : OMA.R_LatinTableau_SimpleGraph_LatinTableauConjecture_R1.H1 := by
  intro μ a b hab
  let e : μ.Cell ≃ Fin a × Fin b :=
    { toFun := fun x => ⟨⟨x.val.1, ((hab x.val).mp x.property).1⟩,
        ⟨x.val.2, ((hab x.val).mp x.property).2⟩⟩
      invFun := fun x => ⟨(x.1.val, x.2.val), (hab _).mpr ⟨x.1.isLt, x.2.isLt⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun x => by cases x; rfl }
  have hAdj (x y : μ.Cell) : μ.toSimpleGraph.Adj x y ↔
      x ≠ y ∧ ((e x).1 = (e y).1 ∨ (e x).2 = (e y).2) := by
    change (x ≠ y ∧ ((x.val.1 = y.val.1 ∨ x.val.2 = y.val.2) ∨
      (y.val.1 = x.val.1 ∨ y.val.2 = x.val.2))) ↔ _
    have h₁ : (e x).1 = (e y).1 ↔ x.val.1 = y.val.1 := Fin.ext_iff
    have h₂ : (e x).2 = (e y).2 ↔ x.val.2 = y.val.2 := Fin.ext_iff
    rw [h₁, h₂]
    grind
  by_cases h : a ≤ b
  · exact rectangleColoring h e _ hAdj
  · apply rectangleColoring (Nat.le_of_not_ge h) (e.trans (Equiv.prodComm _ _))
    intro x y
    change μ.toSimpleGraph.Adj x y ↔
      x ≠ y ∧ ((e x).2 = (e y).2 ∨ (e x).1 = (e y).1)
    rw [hAdj x y, or_comm]