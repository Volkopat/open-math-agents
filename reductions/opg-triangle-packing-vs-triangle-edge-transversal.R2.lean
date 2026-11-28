import OMAStatements.S_opg_triangle_packing_vs_triangle_edge_transversal

/-!
Tuza's triangle packing and covering conjecture. A packing P can be removed
if at most 2|P| edges meet every triangle that shares an edge with P. Delete
all edges of P for the recursive packing. For the cover, use the local cover
instead of all the deleted edges. The two lifts spend the same packing budget.

The proof works for local packings of any size. The hypotheses retain only
graphs resisting every one- and two-triangle exchange; the two residual
classes are K4-free graphs and graphs containing K4. For example, a triangle
with a private edge is removed using its other two edges. In a K4, if ab and
ac lie in exactly two triangles each, triangle abc is removed using ad and bc.
The two-triangle rule can also remove configurations with no removable singleton.

This specializes the edge reduction (Definition 4.2 and Lemma 4.3) of
Gregory J. Puleo, Tuza's Conjecture for Graphs with Maximum Average Degree
Less Than 7 (arXiv:1308.2211). See also Yasuhito Tsujimura, Triangle-overlap
cores and density bounds for Tuza's conjecture (arXiv:2611.11128, Lemma 2.2).
-/

namespace OMA.R_opg_triangle_packing_vs_triangle_edge_transversal_R2

/-- The remaining K4-free graphs. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ),
    G.CliqueFree 4 →
    (∀ P : Finset (Finset V), P.Nonempty → P.card ≤ 2 →
      (∀ t ∈ P, G.IsNClique 3 t) →
      (∀ t ∈ P, ∀ u ∈ P, t ≠ u → (t ∩ u).card ≤ 1) →
      ∀ X : Finset (Sym2 V), X.card ≤ 2 * P.card →
        ∃ u, (G.deleteEdges (X : Set (Sym2 V))).IsNClique 3 u ∧
          ∃ t ∈ P, 1 < (t ∩ u).card) →
    (∀ T : Finset (Finset V), (∀ t ∈ T, G.IsNClique 3 t) →
      (∀ t ∈ T, ∀ u ∈ T, t ≠ u → (t ∩ u).card ≤ 1) → T.card ≤ k) →
    ∃ S : Finset (Sym2 V), S.card ≤ 2 * k ∧
      (G.deleteEdges (S : Set (Sym2 V))).CliqueFree 3

/-- The remaining graphs containing a K4. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ),
    ¬ G.CliqueFree 4 →
    (∀ P : Finset (Finset V), P.Nonempty → P.card ≤ 2 →
      (∀ t ∈ P, G.IsNClique 3 t) →
      (∀ t ∈ P, ∀ u ∈ P, t ≠ u → (t ∩ u).card ≤ 1) →
      ∀ X : Finset (Sym2 V), X.card ≤ 2 * P.card →
        ∃ u, (G.deleteEdges (X : Set (Sym2 V))).IsNClique 3 u ∧
          ∃ t ∈ P, 1 < (t ∩ u).card) →
    (∀ T : Finset (Finset V), (∀ t ∈ T, G.IsNClique 3 t) →
      (∀ t ∈ T, ∀ u ∈ T, t ≠ u → (t ∩ u).card ≤ 1) → T.card ≤ k) →
    ∃ S : Finset (Sym2 V), S.card ≤ 2 * k ∧
      (G.deleteEdges (S : Set (Sym2 V))).CliqueFree 3

/-- Remove a local packing and transfer both the packing bound and the cover. -/
theorem removePacking {V : Type} [DecidableEq V] (G : SimpleGraph V) (k : ℕ)
    (P : Finset (Finset V)) (X : Finset (Sym2 V))
    (hp : P.Nonempty) (ht : ∀ t ∈ P, G.IsNClique 3 t)
    (hd : ∀ t ∈ P, ∀ u ∈ P, t ≠ u → (t ∩ u).card ≤ 1)
    (hx : X.card ≤ 2 * P.card)
    (hloc : ∀ u, (G.deleteEdges (X : Set (Sym2 V))).IsNClique 3 u →
      ∀ t ∈ P, (t ∩ u).card ≤ 1)
    (hk : ∀ T : Finset (Finset V), (∀ t ∈ T, G.IsNClique 3 t) →
      (∀ t ∈ T, ∀ u ∈ T, t ≠ u → (t ∩ u).card ≤ 1) → T.card ≤ k) :
    ∃ H : SimpleGraph V, k - P.card < k ∧
      (∀ T : Finset (Finset V), (∀ t ∈ T, H.IsNClique 3 t) →
        (∀ t ∈ T, ∀ u ∈ T, t ≠ u → (t ∩ u).card ≤ 1) → T.card ≤ k - P.card) ∧
      (∀ S : Finset (Sym2 V), S.card ≤ 2 * (k - P.card) →
        (H.deleteEdges (S : Set (Sym2 V))).CliqueFree 3 →
        ∃ Y : Finset (Sym2 V), Y.card ≤ 2 * k ∧
          (G.deleteEdges (Y : Set (Sym2 V))).CliqueFree 3) := by
  classical
  let D : Set (Sym2 V) := {e | ∃ t ∈ P, ∀ x ∈ e, x ∈ t}
  let H := G.deleteEdges D
  have hpk := hk P ht hd
  have hpos := hp.card_pos
  have hcross {u : Finset V} (hu : H.IsNClique 3 u) {t : Finset V} (h : t ∈ P) :
      (t ∩ u).card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro a b ha hb
    obtain ⟨hat, hau⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbt, hbu⟩ := Finset.mem_inter.mp hb
    by_contra hn
    exact (SimpleGraph.deleteEdges_adj.mp (hu.1 hau hbu hn)).2
      ⟨t, h, Sym2.ball.mpr ⟨hat, hbt⟩⟩
  refine ⟨H, by omega, ?_, ?_⟩
  · intro T hT dT
    have dis : Disjoint P T := by
      apply Finset.disjoint_left.mpr
      intro t hp' ht'
      have h := hcross (hT t ht') hp'
      simp [(ht t hp').card_eq] at h
    have bound := hk (P ∪ T) (by
      intro t hm
      rcases Finset.mem_union.mp hm with h | h
      · exact ht t h
      · exact (hT t h).mono (G.deleteEdges_le D)) (by
      intro t tm u um ne
      rcases Finset.mem_union.mp tm with tP | tT <;>
        rcases Finset.mem_union.mp um with uP | uT
      · exact hd t tP u uP ne
      · exact hcross (hT u uT) tP
      · simpa only [Finset.inter_comm] using hcross (hT t tT) uP
      · exact dT t tT u uT ne)
    rw [Finset.card_union_of_disjoint dis] at bound
    omega
  · intro S hs hfree
    refine ⟨X ∪ S, (Finset.card_union_le _ _).trans (by omega), ?_⟩
    intro u hu
    have hX : (G.deleteEdges (X : Set (Sym2 V))).IsNClique 3 u := by
      refine ⟨?_, hu.2⟩
      intro a ha b hb hn
      obtain ⟨hG, hY⟩ := SimpleGraph.deleteEdges_adj.mp (hu.1 ha hb hn)
      exact SimpleGraph.deleteEdges_adj.mpr ⟨hG, fun hx' => hY (Finset.mem_union_left S hx')⟩
    apply hfree u
    refine ⟨?_, hu.2⟩
    intro a ha b hb hn
    obtain ⟨hG, hY⟩ := SimpleGraph.deleteEdges_adj.mp (hu.1 ha hb hn)
    refine SimpleGraph.deleteEdges_adj.mpr ⟨SimpleGraph.deleteEdges_adj.mpr ⟨hG, ?_⟩,
      fun hs' => hY (Finset.mem_union_right X hs')⟩
    rintro ⟨t, htp, he⟩
    obtain ⟨hat, hbt⟩ := Sym2.ball.mp he
    exact hn (Finset.card_le_one_iff.mp (hloc u hX t htp)
      (Finset.mem_inter.mpr ⟨hat, ha⟩) (Finset.mem_inter.mpr ⟨hbt, hb⟩))

theorem main : H1 → H2 → type_of% @OMA.S_opg_triangle_packing_vs_triangle_edge_transversal.main := by
  intro hfourFree hfour V _ _ G k
  induction k using Nat.strong_induction_on generalizing G with
  | h k ih =>
    intro hk
    by_cases core : ∀ P : Finset (Finset V), P.Nonempty → P.card ≤ 2 →
        (∀ t ∈ P, G.IsNClique 3 t) →
        (∀ t ∈ P, ∀ u ∈ P, t ≠ u → (t ∩ u).card ≤ 1) →
        ∀ X : Finset (Sym2 V), X.card ≤ 2 * P.card →
          ∃ u, (G.deleteEdges (X : Set (Sym2 V))).IsNClique 3 u ∧
            ∃ t ∈ P, 1 < (t ∩ u).card
    · by_cases hf : G.CliqueFree 4
      · exact hfourFree V G k hf core hk
      · exact hfour V G k hf core hk
    · push Not at core
      obtain ⟨P, hp, _, ht, hd, X, hx, hloc⟩ := core
      obtain ⟨H, hlt, hpack, liftCover⟩ := removePacking G k P X hp ht hd hx hloc hk
      obtain ⟨S, hs, hf⟩ := ih _ hlt H hpack
      exact liftCover S hs hf

end OMA.R_opg_triangle_packing_vs_triangle_edge_transversal_R2
