import OMAReductions.R_mo_153208_R1
import Mathlib

/-! A map `φ` with `Sub G H ↔ Sub (φ G) (φ H)` preserves edge counts. An injective graph map raises
the edge count weakly, and between graphs with equal edge counts it is an isomorphism, so strict
`Sub`-steps raise the count strictly. Deleting edges of `G` one at a time gives
`|E(φ G)| ≥ |E(G)|`; adding the missing edges one at a time gives `|E(φ G)| ≤ |E(G)|`. -/

-- Original proof by @ppleskov (PR #20732), following reduction #20528.

open OMA.S_mo_153208 SimpleGraph

namespace MO153208

variable {n : ℕ}

lemma sub_le {G H : SimpleGraph (Fin n)} (h : Sub G H) : G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨f, hf⟩ := h
  calc G.edgeSet.ncard = ((Sym2.map f) '' G.edgeSet).ncard :=
        (Set.ncard_image_of_injective _ (Sym2.map.injective hf)).symm
    _ ≤ H.edgeSet.ncard := Set.ncard_le_ncard f.image_edgeSet_subset (Set.toFinite _)

lemma sub_of_eq {G H : SimpleGraph (Fin n)} (h : Sub G H)
    (he : G.edgeSet.ncard = H.edgeSet.ncard) : Sub H G := by
  obtain ⟨f, hf⟩ := h
  have hb : Function.Bijective f := Finite.injective_iff_bijective.mp hf
  let g := (Equiv.ofBijective f hb).symm
  have hfg : ∀ x, f (g x) = x := fun x => (Equiv.ofBijective f hb).apply_symm_apply x
  have himg : (Sym2.map f) '' G.edgeSet = H.edgeSet :=
    Set.eq_of_subset_of_ncard_le f.image_edgeSet_subset
      (by rw [Set.ncard_image_of_injective _ (Sym2.map.injective hf)]; omega) (Set.toFinite _)
  refine ⟨⟨g, fun {u v} huv => ?_⟩, (Equiv.ofBijective f hb).symm.injective⟩
  have : s(u, v) ∈ (Sym2.map f) '' G.edgeSet := by rw [himg]; exact huv
  obtain ⟨e, he, hfe⟩ := this
  induction e using Sym2.ind with
  | h a b =>
    simp only [Sym2.map_pair_eq, Sym2.eq_iff] at hfe
    have ga : ∀ x, g (f x) = x := fun x => (Equiv.ofBijective f hb).symm_apply_apply x
    rcases hfe with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2, ga, ga]; exact he
    · rw [← h1, ← h2, ga, ga]; exact he.symm

/-- Strict `Sub`-steps raise the edge count. -/
lemma lt_of_strict {G H : SimpleGraph (Fin n)} (h : Sub G H) (hn : ¬ Sub H G) :
    G.edgeSet.ncard < H.edgeSet.ncard :=
  lt_of_le_of_ne (sub_le h) fun he => hn (sub_of_eq h he)

lemma sub_of_le {G H : SimpleGraph (Fin n)} (h : G ≤ H) : Sub G H :=
  ⟨⟨id, fun huv => h huv⟩, Function.injective_id⟩

end MO153208

open MO153208 in
theorem OMA.solution : OMA.R_mo_153208_R1.H1 := by
  intro n φ hφ
  classical
  -- lower bound by induction on the number of edges
  have lower : ∀ m, ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
      m ≤ (φ G).edgeSet.ncard := by
    intro m
    induction m with
    | zero => intros; exact Nat.zero_le _
    | succ m ih =>
      intro G hG
      obtain ⟨e, he⟩ : G.edgeSet.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
      let G' := G.deleteEdges {e}
      have hG' : G'.edgeSet.ncard = m := by
        rw [edgeSet_deleteEdges, Set.ncard_diff_singleton_of_mem he]; omega
      have hle : G' ≤ G := deleteEdges_le _
      have hstrict : ¬ Sub G G' := fun h => by have := sub_le h; omega
      have := lt_of_strict ((hφ _ _).mp (sub_of_le hle)) (fun h => hstrict ((hφ _ _).mpr h))
      have := ih G' hG'
      omega
  -- upper bound by induction on the number of missing edges
  have upper : ∀ m, ∀ G : SimpleGraph (Fin n), (⊤ : SimpleGraph (Fin n)).edgeSet.ncard -
      G.edgeSet.ncard = m → (φ G).edgeSet.ncard ≤ G.edgeSet.ncard := by
    intro m
    induction m with
    | zero =>
      intro G hG
      have h1 : (φ G).edgeSet.ncard ≤ (⊤ : SimpleGraph (Fin n)).edgeSet.ncard :=
        Set.ncard_le_ncard (edgeSet_mono le_top) (Set.toFinite _)
      have h2 : G.edgeSet.ncard ≤ (⊤ : SimpleGraph (Fin n)).edgeSet.ncard :=
        Set.ncard_le_ncard (edgeSet_mono le_top) (Set.toFinite _)
      omega
    | succ m ih =>
      intro G hG
      have hlt : G.edgeSet.ncard < (⊤ : SimpleGraph (Fin n)).edgeSet.ncard := by omega
      obtain ⟨e, heT, heG⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
      induction e using Sym2.ind with
      | h u v =>
        have huv : u ≠ v := by simpa using heT
        let G' := G ⊔ SimpleGraph.edge u v
        have hG'e : G'.edgeSet = insert s(u, v) G.edgeSet := by
          simp [G', edgeSet_sup, edgeSet_edge_of_ne huv, Set.union_comm]
        have hG' : G'.edgeSet.ncard = G.edgeSet.ncard + 1 := by
          rw [hG'e, Set.ncard_insert_of_notMem heG]
        have hle : G ≤ G' := le_sup_left
        have hstrict : ¬ Sub G' G := fun h => by have := sub_le h; omega
        have := lt_of_strict ((hφ _ _).mp (sub_of_le hle)) (fun h => hstrict ((hφ _ _).mpr h))
        have := ih G' (by omega)
        omega
  intro G
  exact le_antisymm (upper _ G rfl) (lower _ G rfl)
