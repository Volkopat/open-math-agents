import OMAReductions.R_Erdos17_erdos_17_R2_H3_R1

-- Step Erdos17.erdos_17.R2.H3.R1.H2: hypothesis H2 of reduction Erdos17.erdos_17.R2.H3.R1
-- Credit: @Raimo33

namespace RaimoE17

lemma greedy (s : ℕ) (hs : 0 < s) : ∀ n, ∀ A : Finset ℕ, A.card = n → ∃ S ⊆ A,
    A.card ≤ s * S.card ∧ ∀ p ∈ S, ∀ q ∈ S, p < q → p + s ≤ q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hA
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, by simp, by simp, by simp⟩
  set a := A.min' hne with hadef
  set A' := A.filter (fun x => a + s ≤ x) with hA'def
  have hlt : A'.card < n := by
    rw [← hA]
    apply Finset.card_lt_card
    refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
    have := h (A.min'_mem hne)
    rw [Finset.mem_filter] at this
    omega
  obtain ⟨S', hS'A', hcard, hgap⟩ := ih _ hlt A' rfl
  have hdiff : A.card ≤ A'.card + s := by
    have hsub : A.filter (fun x => ¬ (a + s ≤ x)) ⊆ Finset.Ico a (a + s) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have := A.min'_le x hx.1
      rw [Finset.mem_Ico]
      omega
    have h1 := Finset.card_le_card hsub
    have h2 : A'.card + (A.filter (fun x => ¬ (a + s ≤ x))).card = A.card :=
      Finset.card_filter_add_card_filter_not _
    rw [Nat.card_Ico, Nat.add_sub_cancel_left] at h1
    omega
  have haS' : a ∉ S' := fun h => by
    have := hS'A' h
    rw [Finset.mem_filter] at this
    omega
  refine ⟨insert a S', ?_, ?_, ?_⟩
  · exact Finset.insert_subset (A.min'_mem hne) (hS'A'.trans (Finset.filter_subset _ _))
  · rw [Finset.card_insert_of_notMem haS']
    nlinarith
  · intro p hp q hq hpq
    rw [Finset.mem_insert] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · omega
    · have := (Finset.mem_filter.mp (hS'A' hq)).2
      omega
    · have := A.min'_le _ (Finset.mem_filter.mp (hS'A' hp)).1
      omega
    · exact hgap p hp q hq hpq

end RaimoE17

theorem OMA.solution : OMA.R_Erdos17_erdos_17_R2_H3_R1.H2 := by
  intro k A _ hcard
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hne
    refine ⟨{x}, by simpa using hx, by simp, ?_⟩
    intro p hp q hq hpq
    rw [Finset.mem_singleton] at hp hq
    omega
  obtain ⟨S, hSA, hS, hgap⟩ := RaimoE17.greedy (2 * k ^ 2) (by positivity) _ A rfl
  refine ⟨S, hSA, ?_, hgap⟩
  by_contra h
  rw [not_lt] at h
  have h1 : 2 * k ^ 2 * S.card ≤ 2 * k ^ 2 * k := Nat.mul_le_mul_left _ h
  have h2 : 2 * k ^ 2 * k ≤ 4 * k ^ 3 := by nlinarith
  omega
