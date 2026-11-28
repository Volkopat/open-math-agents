import FormalConjectures.ErdosProblems.«1008»

/-!
In a four-cycle-free bipartite graph, choose one incident edge per nonisolated
right vertex. Assign that edge to the vertex and every other edge at that
vertex to the unordered pair of its left endpoint and the chosen left endpoint.
Two distinct right vertices sharing a pair would give a four-cycle.
-/

open SimpleGraph
open scoped SimpleGraph

namespace FolkmanBound

private lemma four_cycle {A B : Type*} {G : SimpleGraph (A ⊕ B)}
    {a a' : A} {b b' : B} (ha : a ≠ a') (hb : b ≠ b')
    (h₁ : G.Adj (.inl a) (.inr b)) (h₂ : G.Adj (.inl a') (.inr b))
    (h₃ : G.Adj (.inl a) (.inr b')) (h₄ : G.Adj (.inl a') (.inr b')) :
    cycleGraph 4 ⊑ G := by
  let f : Fin 4 → A ⊕ B := ![.inl a, .inr b, .inl a', .inr b']
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
    | exact False.elim ((show ¬ (cycleGraph 4).Adj _ _ from by decide) hij)
    | simpa [f, adj_comm] using h₁
    | simpa [f, adj_comm] using h₂
    | simpa [f, adj_comm] using h₃
    | simpa [f, adj_comm] using h₄
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]

private def pairEdge {A B : Type*} (p : A × B) : Sym2 (A ⊕ B) := s(.inl p.1, .inr p.2)

private lemma pair_edge_injective {A B : Type*} : Function.Injective (@pairEdge A B) := by
  intro p q h
  rcases Sym2.eq_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, _⟩
  · exact Prod.ext (Sum.inl.inj h₁) (Sum.inr.inj h₂)
  · cases h₁

private lemma complete_count {A B : Type*} [Finite A] [Finite B] :
    (completeBipartiteGraph A B).edgeSet.ncard = Nat.card A * Nat.card B := by
  rw [edgeSet_completeBipartiteGraph]
  change (Set.range (@pairEdge A B)).ncard = _
  rw [Set.ncard_range_of_injective pair_edge_injective, Nat.card_prod]

private lemma edge_bound {A B : Type*} [Finite A] [Finite B]
    (G : SimpleGraph (A ⊕ B)) (hG : G ≤ completeBipartiteGraph A B)
    (hfree : ¬ cycleGraph 4 ⊑ G) :
    G.edgeSet.ncard ≤ Nat.card B + (Nat.card A).choose 2 := by
  classical
  let E : Set (A × B) := pairEdge ⁻¹' G.edgeSet
  have has_neighbor (p : E) : ∃ a, G.Adj (.inl a) (.inr p.val.2) := ⟨p.val.1, p.prop⟩
  let pivot (p : E) : A := Classical.choose (has_neighbor p)
  have hpivot (p : E) : G.Adj (.inl (pivot p)) (.inr p.val.2) :=
    Classical.choose_spec (has_neighbor p)
  have same_pivot (p q : E) (h : p.val.2 = q.val.2) : pivot p = pivot q := by
    simp only [pivot, h]
  let encode (p : E) : B ⊕ {e : Sym2 A // ¬ e.IsDiag} :=
    if hp : p.val.1 = pivot p then .inl p.val.2
    else .inr ⟨s(p.val.1, pivot p), fun h => hp (Sym2.mk_isDiag_iff.mp h)⟩
  have hinj : Function.Injective encode := by
    intro p q h
    by_cases hp : p.val.1 = pivot p <;> by_cases hq : q.val.1 = pivot q <;>
      simp [encode, hp, hq] at h
    · exact Subtype.ext (Prod.ext (hp.trans ((same_pivot p q h).trans hq.symm)) h)
    · have hb : p.val.2 = q.val.2 := by
        by_contra hne
        apply hfree
        rcases h with ⟨ha, hr⟩ | ⟨ha, hr⟩
        · exact four_cycle hp hne p.prop (hpivot p)
            (by rw [ha]; exact q.prop) (by rw [hr]; exact hpivot q)
        · exact four_cycle hp hne p.prop (hpivot p)
            (by rw [ha]; exact hpivot q) (by rw [hr]; exact q.prop)
      rcases h with ⟨ha, _⟩ | ⟨ha, _⟩
      · exact Subtype.ext (Prod.ext ha hb)
      · exact (hp (ha.trans (same_pivot p q hb).symm)).elim
  have hcard : Nat.card E = G.edgeSet.ncard :=
    Set.ncard_preimage_of_injective_subset_range pair_edge_injective (by
      rw [show Set.range (@pairEdge A B) = (completeBipartiteGraph A B).edgeSet from
        edgeSet_completeBipartiteGraph.symm]
      exact edgeSet_mono hG)
  simpa only [hcard, Nat.card_sum, Sym2.natCard_subtype_not_diag] using
    Nat.card_le_card_of_injective encode hinj

end FolkmanBound

theorem OMA.solution : type_of% @Erdos1008.erdos_1008.variants.three_quarters := by
  rintro ⟨c, hc, h⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / c)
  have hcm : 2 < c * (m : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hc).mp hm
  have hmpos : 0 < (m : ℝ) := lt_trans (by positivity) hm
  let G := completeBipartiteGraph (Fin (m ^ 4)) (Fin (m ^ 8))
  obtain ⟨H, hHG, hfree, hlarge⟩ := h _ G
  have hbound : H.edgeSet.ncard ≤ 2 * m ^ 8 := by
    have hpairs := Nat.choose_le_pow (m ^ 4) 2
    rw [← pow_mul] at hpairs
    change (m ^ 4).choose 2 ≤ m ^ 8 at hpairs
    have hbound := FolkmanBound.edge_bound H hHG hfree
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hbound
    omega
  have hcount : G.edgeSet.ncard = m ^ 12 := by
    simp only [G, FolkmanBound.complete_count, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_add]
  have hpow : (G.edgeSet.ncard : ℝ) ^ (3 / 4 : ℝ) = (m : ℝ) ^ 9 := by
    rw [hcount, Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg m)]
    rw [show ((12 : ℕ) : ℝ) * (3 / 4) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hpow] at hlarge
  have hsmall : (H.edgeSet.ncard : ℝ) ≤ 2 * (m : ℝ) ^ 8 := by exact_mod_cast hbound
  have hstrict := mul_lt_mul_of_pos_right hcm (pow_pos hmpos 8)
  rw [mul_assoc, ← pow_succ'] at hstrict
  exact hstrict.not_ge (hlarge.trans hsmall)
