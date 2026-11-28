import OMAReductions.R_Erdos1029_erdos_1029_R1_H2_R1

namespace LLLHelper

open Finset

variable {M K : ℕ} (w : Fin M → ℝ) (E : Fin K → Finset (Fin M))

/-- weight of the avoiding set -/
noncomputable def W (S : Finset (Fin K)) : ℝ :=
  ∑ ω ∈ (Finset.univ : Finset (Fin M)).filter (fun ω => ∀ j ∈ S, ω ∉ E j), w ω

noncomputable def B (i : Fin K) (S : Finset (Fin K)) : ℝ :=
  ∑ ω ∈ (E i).filter (fun ω => ∀ j ∈ S, ω ∉ E j), w ω

theorem W_insert (j : Fin K) (S : Finset (Fin K)) :
    W w E (insert j S) = W w E S - B w E j S := by
  classical
  unfold W B
  rw [eq_sub_iff_add_eq, ← Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset (Fin M)).filter (fun ω => ∀ j ∈ S, ω ∉ E j)) (fun ω => ω ∈ E j),
    add_comm]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext ω
    simp only [mem_filter, mem_univ, true_and]
    tauto
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext ω
    simp only [mem_filter, mem_univ, true_and, Finset.forall_mem_insert]
    tauto

theorem B_anti (hw : ∀ ω, 0 ≤ w ω) (i : Fin K) {S T : Finset (Fin K)} (h : S ⊆ T) :
    B w E i T ≤ B w E i S := by
  unfold B
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω
    simp only [mem_filter]
    exact fun hω => ⟨hω.1, fun j hj => hω.2 j (h hj)⟩
  · intro ω _ _
    exact hw ω

/-- product lower bound, given the claim on strictly smaller sets -/
theorem prod_bound (x : Fin K → ℝ) (I : Finset (Fin K))
    (hx : ∀ i ∈ I, 0 ≤ x i ∧ x i < 1) (T : Finset (Fin K)) :
    ∀ U : Finset (Fin K), U ⊆ I → Disjoint T U →
    (∀ V, V ⊆ T ∪ U → V ≠ T ∪ U → ∀ i ∈ I, i ∉ V → B w E i V ≤ x i * W w E V) →
    (∏ j ∈ U, (1 - x j)) * W w E T ≤ W w E (T ∪ U) := by
  classical
  intro U
  induction U using Finset.induction_on with
  | empty => intro _ _ _; simp
  | insert j U hjU ih =>
    intro hUI hdisj hC
    have hjI : j ∈ I := hUI (mem_insert_self j U)
    have hdisj' : Disjoint T U := hdisj.mono_right (subset_insert j U)
    have hjT : j ∉ T := fun h => (Finset.disjoint_left.mp hdisj) h (mem_insert_self j U)
    have hsub : T ∪ U ⊆ T ∪ insert j U := union_subset_union_right (subset_insert j U)
    have hjn : j ∉ T ∪ U := by
      intro h
      rcases mem_union.mp h with h1 | h1
      · exact hjT h1
      · exact hjU h1
    have hne : T ∪ U ≠ T ∪ insert j U := by
      intro h
      exact hjn (h ▸ mem_union_right T (mem_insert_self j U))
    have ih' := ih (fun a ha => hUI (mem_insert_of_mem ha)) hdisj'
      (fun V hV hVne => hC V (hV.trans hsub) (fun h => hVne (by
        apply le_antisymm hV; rw [h]; exact hsub)))
    have hBj := hC (T ∪ U) hsub hne j hjI hjn
    have heq : T ∪ insert j U = insert j (T ∪ U) := by
      ext a; simp only [mem_union, mem_insert]; tauto
    rw [heq, W_insert, prod_insert hjU]
    have h1 : 0 ≤ 1 - x j := by linarith [(hx j hjI).2]
    calc (1 - x j) * (∏ j ∈ U, (1 - x j)) * W w E T
        = (1 - x j) * ((∏ j ∈ U, (1 - x j)) * W w E T) := by ring
      _ ≤ (1 - x j) * W w E (T ∪ U) := mul_le_mul_of_nonneg_left ih' h1
      _ ≤ W w E (T ∪ U) - B w E j (T ∪ U) := by nlinarith

end LLLHelper

open LLLHelper Finset in
theorem OMA.solution : OMA.R_Erdos1029_erdos_1029_R1_H2_R1.H1 := by
  classical
  intro M K w I E Γ p x hw hpos hΓ hx hp hcond
  have claim : ∀ S : Finset (Fin K), S ⊆ I → ∀ i ∈ I, i ∉ S → B w E i S ≤ x i * W w E S := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
      intro hSI i hi hiS
      let S1 := S.filter (fun j => j ∈ Γ i)
      let S2 := S.filter (fun j => j ∉ Γ i)
      have hS2S : S2 ⊆ S := filter_subset _ _
      have hS1S : S1 ⊆ S := filter_subset _ _
      have hdisj : Disjoint S2 S1 := by
        rw [Finset.disjoint_left]
        intro a ha hb
        exact (mem_filter.mp ha).2 (mem_filter.mp hb).2
      have hunion : S2 ∪ S1 = S := by
        ext a; simp only [S1, S2, mem_union, mem_filter]; tauto
      have hB1 : B w E i S ≤ B w E i S2 := B_anti w E hw i hS2S
      have hB2 : B w E i S2 ≤ p i * W w E S2 := by
        apply hcond i hi S2 (hS2S.trans hSI) (fun h => hiS (hS2S h))
        rw [Finset.disjoint_left]
        intro a ha hb
        exact (mem_filter.mp ha).2 hb
      have hprod := prod_bound w E x I hx S2 S1 (hS1S.trans hSI) hdisj (by
        intro V hV hVne j hj hjV
        rw [hunion] at hV hVne
        exact ih V (lt_of_le_of_ne hV hVne) (hV.trans hSI) j hj hjV)
      rw [hunion] at hprod
      have hW2 : 0 ≤ W w E S2 := sum_nonneg (fun ω _ => hw ω)
      have hprodΓ : ∏ j ∈ Γ i, (1 - x j) ≤ ∏ j ∈ S1, (1 - x j) := by
        have hsub : S1 ⊆ Γ i := fun a ha => (mem_filter.mp ha).2
        rw [← prod_sdiff hsub]
        have h0 : 0 ≤ ∏ j ∈ S1, (1 - x j) :=
          prod_nonneg (fun j hj => by linarith [(hx j (hSI (hS1S hj))).2])
        have h1 : ∏ j ∈ Γ i \ S1, (1 - x j) ≤ 1 := by
          apply prod_le_one
          · intro j hj
            linarith [(hx j (hΓ i hi (mem_sdiff.mp hj).1)).2]
          · intro j hj
            linarith [(hx j (hΓ i hi (mem_sdiff.mp hj).1)).1]
        nlinarith
      have hxi := (hx i hi).1
      calc B w E i S ≤ p i * W w E S2 := hB1.trans hB2
        _ ≤ (x i * ∏ j ∈ Γ i, (1 - x j)) * W w E S2 :=
          mul_le_mul_of_nonneg_right (hp i hi) hW2
        _ ≤ (x i * ∏ j ∈ S1, (1 - x j)) * W w E S2 := by
          apply mul_le_mul_of_nonneg_right _ hW2
          exact mul_le_mul_of_nonneg_left hprodΓ hxi
        _ = x i * ((∏ j ∈ S1, (1 - x j)) * W w E S2) := by ring
        _ ≤ x i * W w E S := mul_le_mul_of_nonneg_left hprod hxi
  have hfin := prod_bound w E x I hx ∅ I subset_rfl (disjoint_empty_left I) (by
    intro V hV _ j hj hjV
    rw [empty_union] at hV
    exact claim V hV j hj hjV)
  rw [empty_union] at hfin
  have hW0 : W w E ∅ = ∑ ω, w ω := by
    unfold W; simp
  have hprodpos : 0 < ∏ j ∈ I, (1 - x j) :=
    prod_pos (fun j hj => by linarith [(hx j hj).2])
  have hWI : 0 < W w E I := lt_of_lt_of_le (by rw [hW0]; exact mul_pos hprodpos hpos) hfin
  obtain ⟨ω, hω⟩ : ((Finset.univ : Finset (Fin M)).filter (fun ω => ∀ j ∈ I, ω ∉ E j)).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    unfold W at hWI
    rw [h, sum_empty] at hWI
    exact lt_irrefl _ hWI
  exact ⟨ω, (mem_filter.mp hω).2⟩
