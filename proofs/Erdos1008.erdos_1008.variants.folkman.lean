import FormalConjectures.ErdosProblems.«1008»

/-! A shared pair of left-side neighbors gives a four-cycle. -/

open SimpleGraph
open scoped SimpleGraph

private lemma c4 {A B : Type*} (G : SimpleGraph (A ⊕ B)) {a a' : A} {b b' : B}
    (ha : a ≠ a') (hb : b ≠ b') (h1 : G.Adj (.inl a) (.inr b)) (h2 : G.Adj (.inl a) (.inr b'))
    (h3 : G.Adj (.inl a') (.inr b)) (h4 : G.Adj (.inl a') (.inr b')) : cycleGraph 4 ⊑ G := by
  let f : Fin 4 → A ⊕ B := ![.inl a, .inr b, .inl a', .inr b']
  refine ⟨⟨⟨f, fun {i j} hij => ?_⟩, fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all [f]⟩⟩
  fin_cases i <;> fin_cases j <;>
    first
    | exact False.elim ((by decide : ¬ (cycleGraph 4).Adj _ _) hij)
    | simpa [f] using h1 | simpa [f] using h1.symm
    | simpa [f] using h2 | simpa [f] using h2.symm
    | simpa [f] using h3 | simpa [f] using h3.symm
    | simpa [f] using h4 | simpa [f] using h4.symm

theorem OMA.solution : type_of% @Erdos1008.erdos_1008.variants.folkman := by
  classical
  intro n
  refine ⟨?_, fun H hH hbig => by_contra fun hfree => ?_⟩
  · rw [edgeSet_completeBipartiteGraph, Set.ncard_range_of_injective]
    · simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin]; ring
    · intro x y heq
      rcases Sym2.eq_iff.mp heq with h | h
      · exact Prod.ext (Sum.inl.inj h.1) (Sum.inr.inj h.2)
      · cases h.1
  · let L : Finset (Fin n ⊕ Fin (n ^ 2)) := Finset.univ.map Function.Embedding.inl
    let R : Finset (Fin n ⊕ Fin (n ^ 2)) := Finset.univ.map Function.Embedding.inr
    let N (b : Fin (n ^ 2)) : Finset (Fin n) := Finset.univ.filter fun a => H.Adj (.inl a) (.inr b)
    let P (b : Fin (n ^ 2)) : Finset (Finset (Fin n)) := (N b).powersetCard 2
    have hbip : H.IsBipartiteWith (L : Set _) (R : Set _) :=
      ⟨Set.disjoint_left.2 fun x => by cases x <;> simp [L, R],
       fun x y h => by have := hH h; cases x <;> cases y <;> simp_all [L, R]⟩
    have hdeg (b : Fin (n ^ 2)) : (N b).card = H.degree (.inr b) := by
      have hm : (N b).map Function.Embedding.inl = H.neighborFinset (.inr b) := by
        ext x; cases x with
        | inl a => simp [N, adj_comm]
        | inr a => have hn : ¬ H.Adj (.inr b) (.inr a) := fun h => by simpa using hH h
                   simp [N, hn]
      rw [← H.card_neighborFinset_eq_degree, ← hm, Finset.card_map]
    have hsum : H.edgeSet.ncard = ∑ b, (N b).card := by
      rw [← H.coe_edgeFinset, Set.ncard_coe_finset, ← isBipartiteWith_sum_degrees_eq_card_edges' hbip]
      simp only [R, Finset.sum_map]
      exact Finset.sum_congr rfl fun b _ => (hdeg b).symm
    have hdisj : ((Finset.univ : Finset (Fin (n ^ 2))) : Set _).PairwiseDisjoint P := fun b _ b' _ hbb' =>
      Finset.disjoint_left.2 fun T hT hT' => hfree <| by
        obtain ⟨hTb, hTc⟩ := Finset.mem_powersetCard.mp hT
        have hTb' := (Finset.mem_powersetCard.mp hT').1
        obtain ⟨a, a', haa', rfl⟩ := Finset.card_eq_two.mp hTc
        exact c4 H haa' hbb' (Finset.mem_filter.mp (hTb (by simp))).2
          (Finset.mem_filter.mp (hTb' (by simp))).2 (Finset.mem_filter.mp (hTb (by simp))).2
          (Finset.mem_filter.mp (hTb' (by simp))).2
    have hpairs : (∑ b, (N b).card.choose 2) ≤ n.choose 2 := by
      have hsub : (Finset.univ : Finset (Fin (n ^ 2))).biUnion P ⊆ (Finset.univ : Finset (Fin n)).powersetCard 2 :=
        fun T hT => by obtain ⟨b, _, hTb⟩ := Finset.mem_biUnion.mp hT
                       exact Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp hTb).2⟩
      calc ∑ b, (N b).card.choose 2 = ∑ b, (P b).card := Finset.sum_congr rfl fun _ _ => (Finset.card_powersetCard _ _).symm
        _ = ((Finset.univ : Finset (Fin (n ^ 2))).biUnion P).card := (Finset.card_biUnion hdisj).symm
        _ ≤ n.choose 2 := (Finset.card_le_card hsub).trans_eq (by simp [Finset.card_powersetCard])
    have hle : H.edgeSet.ncard ≤ n ^ 2 + n.choose 2 := by
      calc H.edgeSet.ncard = ∑ b, (N b).card := hsum
        _ ≤ ∑ b, (1 + (N b).card.choose 2) := Finset.sum_le_sum fun b _ => by
            cases (N b).card with
            | zero => simp
            | succ d => rw [show (2 : ℕ) = Nat.succ 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]; omega
        _ = n ^ 2 + ∑ b, (N b).card.choose 2 := by simp [Finset.sum_add_distrib]
        _ ≤ _ := Nat.add_le_add_left hpairs _
    omega
