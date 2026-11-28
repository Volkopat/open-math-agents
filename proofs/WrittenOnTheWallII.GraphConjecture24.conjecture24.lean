import FormalConjectures.WrittenOnTheWallII.GraphConjecture24

/-! The 8x8 rook graph has b ≤ 16 while every vertex has 49 vertices at distance 2. -/

open SimpleGraph Finset

universe u

private abbrev A := ULift.{u} (Fin 8)

private def G : SimpleGraph (A.{u} × A.{u}) where
  Adj v w := v ≠ w ∧ (v.1 = w.1 ∨ v.2 = w.2)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp Eq.symm Eq.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture24.conjecture24 := by
  classical
  intro all
  have hcross {v w : A × A} (h1 : v.1 ≠ w.1) (h2 : v.2 ≠ w.2) :
      G.Adj v (v.1, w.2) ∧ G.Adj w (v.1, w.2) :=
    ⟨⟨fun h => by have := congrArg Prod.snd h; exact h2 this, Or.inl rfl⟩,
     ⟨fun h => by have := congrArg Prod.fst h; exact h1 this.symm, Or.inr rfl⟩⟩
  have hconn : G.Connected := ⟨fun v w => by
    by_cases he : v = w; · exact he ▸ .refl _
    by_cases h1 : v.1 = w.1; · exact (show G.Adj v w from ⟨he, Or.inl h1⟩).reachable
    by_cases h2 : v.2 = w.2; · exact (show G.Adj v w from ⟨he, Or.inr h2⟩).reachable
    exact (hcross h1 h2).1.reachable.trans (hcross h1 h2).2.reachable.symm⟩
  have h := all G hconn
  dsimp only at h
  have hm : 49 ≤ (univ.image (distEven G)).min' (by simp) := by
    apply le_min'; intro _ hk
    obtain ⟨v, _, rfl⟩ := mem_image.mp hk
    have hsub : (univ.erase v.1) ×ˢ (univ.erase v.2) ⊆
        univ.filter fun w : A × A => Even (G.dist v w) := fun w hw => by
      obtain ⟨h1, h2⟩ := mem_product.mp hw
      have hr := Ne.symm (mem_erase.mp h1).1
      have hc := Ne.symm (mem_erase.mp h2).1
      have hd : G.edist v w = 2 :=
        edist_eq_two_iff.2 ⟨fun h => hr (congrArg Prod.fst h), fun h => h.2.elim hr hc, (v.1, w.2), hcross hr hc⟩
      exact mem_filter.2 ⟨mem_univ _, by simp [SimpleGraph.dist, hd]⟩
    exact (by simp [A] : ((univ.erase v.1) ×ˢ (univ.erase v.2)).card = 49) ▸ card_le_card hsub
  have hmR : (49 : ℝ) ≤ ((univ.image (distEven G)).min' (by simp) : ℕ) := by exact_mod_cast hm
  have hbipN : G.largestInducedBipartiteSubgraphSize ≤ 16 := by
    unfold largestInducedBipartiteSubgraphSize
    refine csSup_le ⟨0, ∅, (induce_isBipartite_iff_exists_coloring G _).2 ⟨fun _ => 0, by simp⟩, rfl⟩ ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨c, hc⟩ := (induce_isBipartite_iff_exists_coloring _ _).1 hs
    let f : s → A × Fin 2 := fun v => (v.1.1, c v.1)
    have hinj : Function.Injective f := fun v w h => Subtype.ext (by_contra fun hne => by
      have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
      exact hc _ v.2 _ w.2 ⟨hne, Or.inl h1⟩ h2)
    simpa [A] using Fintype.card_le_of_injective f hinj
  have hbip : b G ≤ 16 := by unfold b; exact_mod_cast hbipN
  have hc := Int.le_ceil ((((univ.image (distEven G)).min' (by simp) : ℕ) : ℝ) / 3)
  have hn : (0 : ℝ) ≤ ((univ.image (fun v => indepNeighborsCard G v)).max' (by simp) : ℕ) := by positivity
  linarith
