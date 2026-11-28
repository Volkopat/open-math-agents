import OMAReductions.R_Erdos165_erdos_165_variants_lower_R1

/-!
Proof of `OMA.R_Erdos165_erdos_165_variants_lower_R1.H1`: the Ramsey number `R(3, k)` is
finite, with the classical bound `R(3, k) ≤ k ^ 2`.

Induction on `k`: let `s` have at least `(k + 1) ^ 2` vertices and pick `v ∈ s`. If `v` has at
least `k + 1` neighbours in `s`, either two of them are adjacent (a triangle with `v`) or `k + 1`
of them are pairwise non-adjacent. Otherwise `v` has at least `k ^ 2` non-neighbours in `s`;
by induction they contain a triangle or `k` pairwise non-adjacent vertices, to which `v` can
be added.
-/

namespace OMAProof.RamseyThree

open SimpleGraph Finset

theorem ramsey_three {V : Type} [DecidableEq V] (C : SimpleGraph V) [DecidableRel C.Adj] :
    ∀ (k : ℕ) (s : Finset V), k * k ≤ s.card →
      (∃ t ⊆ s, C.IsNClique 3 t) ∨ (∃ t ⊆ s, Cᶜ.IsNClique k t) := by
  intro k
  induction k with
  | zero =>
    intro s _
    exact Or.inr ⟨∅, Finset.empty_subset _, isNClique_zero.mpr rfl⟩
  | succ k ih =>
    intro s hs
    obtain ⟨v, hv⟩ : s.Nonempty := by
      rw [← Finset.card_pos]
      nlinarith
    set N := (s.erase v).filter (C.Adj v) with hN
    set M := (s.erase v).filter (fun w => ¬ C.Adj v w) with hM
    have hNM : N.card + M.card = s.card - 1 := by
      rw [hN, hM, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]
    have hNs : N ⊆ s := fun w hw => Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1
    have hMs : M ⊆ s := fun w hw => Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1
    by_cases hbig : k + 1 ≤ N.card
    · by_cases hedge : ∃ a ∈ N, ∃ b ∈ N, C.Adj a b
      · obtain ⟨a, ha, b, hb, hab⟩ := hedge
        refine Or.inl ⟨{v, a, b}, ?_, ?_⟩
        · intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl
          · exact hv
          · exact hNs ha
          · exact hNs hb
        · exact is3Clique_triple_iff.mpr
            ⟨(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, hab⟩
      · push Not at hedge
        obtain ⟨t, htN, htc⟩ := Finset.exists_subset_card_eq hbig
        refine Or.inr ⟨t, htN.trans hNs, ⟨?_, htc⟩⟩
        intro x hx y hy hxy
        exact (compl_adj C x y).mpr ⟨hxy, hedge x (htN hx) y (htN hy)⟩
    · have hMk : k * k ≤ M.card := by
        push Not at hbig
        have : (k + 1) * (k + 1) ≤ N.card + M.card + 1 := by omega
        nlinarith
      rcases ih M hMk with ⟨t, htM, ht⟩ | ⟨t, htM, ht⟩
      · exact Or.inl ⟨t, htM.trans hMs, ht⟩
      · refine Or.inr ⟨insert v t, ?_, ht.insert ?_⟩
        · exact Finset.insert_subset hv (htM.trans hMs)
        · intro w hw
          have hw' := Finset.mem_filter.mp (htM hw)
          exact (compl_adj C v w).mpr ⟨(Finset.ne_of_mem_erase hw'.1).symm, hw'.2⟩

end OMAProof.RamseyThree

open OMAProof.RamseyThree in
theorem OMA.solution : OMA.R_Erdos165_erdos_165_variants_lower_R1.H1 := by
  intro k
  refine ⟨k * k, fun C => ?_⟩
  classical
  rcases ramsey_three C k Finset.univ (by simp) with ⟨t, -, ht⟩ | ⟨t, -, ht⟩
  · exact Or.inl ((SimpleGraph.not_cliqueFree_iff_top_isContained 3).mp fun h => h t ht)
  · exact Or.inr ((SimpleGraph.not_cliqueFree_iff_top_isContained k).mp fun h => h t ht)
