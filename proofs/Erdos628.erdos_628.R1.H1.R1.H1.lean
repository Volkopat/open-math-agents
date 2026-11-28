import OMAReductions.R_Erdos628_erdos_628_R1_H1_R1

/-!
The four-chromatic case of the double-critical graph conjecture is
classical. See Kawarabayashi, Pedersen, and Toft, "Double-Critical
Graphs and Complete Minors," Electronic J. Combin. 17 (2010), R87.

If every adjacent pair has a bipartite complement, then an edge with no
common neighbor permits a three-coloring by recoloring one independent
class of neighbors. If a triangle exists, its complement is independent,
and each exterior vertex can use the color of a triangle vertex it misses.
-/

namespace OMA.Erdos628CaseFour

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

private theorem three_coloring_of_edge_without_common_neighbor {x y : V}
    (hxy : G.Adj x y) (hno : ∀ v, G.Adj x v → ¬ G.Adj y v)
    (hdel : (G.induce ({x, y} : Set V)ᶜ).Colorable 2) : G.Colorable 3 := by
  classical
  obtain ⟨old⟩ := hdel
  let col (v : V) : Fin 2 :=
    if hv : v ∈ ({x, y} : Set V)ᶜ then old ⟨v, hv⟩ else 0
  let paint (v : V) : Fin 3 :=
    if v = x then 0 else if v = y then 2 else
      if col v = 1 then 1 else if G.Adj x v then 2 else 0
  have hpx : paint x = 0 := by simp [paint]
  have hpy : paint y = 2 := by simp [paint, hxy.ne.symm]
  have hx {v : V} (hv : G.Adj x v) : paint v ≠ 0 := by
    by_cases hvy : v = y
    · rw [hvy, hpy]
      decide
    · simp only [paint, if_neg hv.ne.symm, if_neg hvy, if_pos hv]
      split <;> decide
  have hy {v : V} (hv : G.Adj y v) : paint v ≠ 2 := by
    by_cases hvx : v = x
    · rw [hvx, hpx]
      decide
    · have hnv : ¬ G.Adj x v := fun h => hno v h hv
      simp only [paint, if_neg hvx, if_neg hv.ne.symm, if_neg hnv]
      split <;> decide
  have hTwo : ∀ a b : Fin 2, a ≠ b → (a = 1 ∧ b ≠ 1) ∨ (b = 1 ∧ a ≠ 1) := by
    decide
  refine ⟨Coloring.mk paint ?_⟩
  intro u v huv
  by_cases hux : u = x
  · subst u
    rw [hpx]
    exact (hx huv).symm
  by_cases hvx : v = x
  · subst v
    rw [hpx]
    exact hx huv.symm
  by_cases huy : u = y
  · subst u
    rw [hpy]
    exact (hy huv).symm
  by_cases hvy : v = y
  · subst v
    rw [hpy]
    exact hy huv.symm
  have hu : u ∈ ({x, y} : Set V)ᶜ := by simp [hux, huy]
  have hv : v ∈ ({x, y} : Set V)ᶜ := by simp [hvx, hvy]
  have hcol : col u ≠ col v := by
    simpa only [col, dif_pos hu, dif_pos hv] using
      old.valid (v := ⟨u, hu⟩) (w := ⟨v, hv⟩) huv
  rcases hTwo (col u) (col v) hcol with ⟨hU, hV⟩ | ⟨hV, hU⟩
  · simp only [paint, if_neg hux, if_neg huy, if_neg hvx, if_neg hvy, if_pos hU, if_neg hV]
    split <;> decide
  · simp only [paint, if_neg hux, if_neg huy, if_neg hvx, if_neg hvy, if_neg hU, if_pos hV]
    split <;> decide

private theorem three_coloring_of_triangle (hfree : G.CliqueFree 4)
    (hdel : ∀ x y, G.Adj x y → (G.induce ({x, y} : Set V)ᶜ).Colorable 2)
    {t : Finset V} (ht : G.IsNClique 3 t) : G.Colorable 3 := by
  classical
  have hind {x y : V} (hx : x ∉ t) (hy : y ∉ t) : ¬ G.Adj x y := by
    intro hxy
    obtain ⟨old⟩ := hdel x y hxy
    have hmem (v : t) : v.val ∈ ({x, y} : Set V)ᶜ := by
      have hnx : v.val ≠ x := fun heq => hx (heq ▸ v.property)
      have hny : v.val ≠ y := fun heq => hy (heq ▸ v.property)
      simp [hnx, hny]
    let f (v : t) : Fin 2 := old ⟨v.val, hmem v⟩
    have hf : Function.Injective f := by
      intro a b hab
      by_contra hn
      have hadj : G.Adj a.val b.val :=
        ht.isClique a.property b.property (fun heq => hn (Subtype.ext heq))
      exact old.valid (v := ⟨a.val, hmem a⟩) (w := ⟨b.val, hmem b⟩) hadj hab
    have hc := Fintype.card_le_of_injective f hf
    rw [Fintype.card_coe, ht.card_eq, Fintype.card_fin] at hc
    omega
  have hmiss (v : V) : ∃ w : t, ¬ G.Adj v w.val := by
    by_contra hn
    have hn' : ∀ w ∈ t, G.Adj v w := by
      intro w hw
      by_contra h
      exact hn ⟨⟨w, hw⟩, h⟩
    exact hfree _ (ht.insert hn')
  let paint (v : V) : t := if hv : v ∈ t then ⟨v, hv⟩ else (hmiss v).choose
  have hfixed {v : V} (hv : v ∈ t) : (paint v).val = v := by simp [paint, hv]
  have havoid {v : V} (hv : v ∉ t) : ¬ G.Adj v (paint v).val := by
    simpa only [paint, dif_neg hv] using (hmiss v).choose_spec
  let c : G.Coloring t := Coloring.mk paint (by
    intro u v huv heq
    have hval : (paint u).val = (paint v).val := congrArg Subtype.val heq
    by_cases hu : u ∈ t <;> by_cases hv : v ∈ t
    · exact huv.ne ((hfixed hu).symm.trans (hval.trans (hfixed hv)))
    · apply havoid hv
      rw [← hval, hfixed hu]
      exact huv.symm
    · apply havoid hu
      rw [hval, hfixed hv]
      exact huv
    · exact hind hu hv huv)
  simpa only [Fintype.card_coe, ht.card_eq] using c.colorable

private theorem split_four (hchi : G.chromaticNumber = 4) (hfree : G.CliqueFree 4) :
    ∃ s : Set V, (G.induce s).chromaticNumber ≥ (2 : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (3 : ℕ∞) := by
  classical
  by_contra hsplit
  have hno3 : ¬ G.Colorable 3 := by
    intro hc
    have hle := hc.chromaticNumber_le
    rw [hchi] at hle
    norm_num at hle
  have hdel (x y : V) (hxy : G.Adj x y) :
      (G.induce ({x, y} : Set V)ᶜ).Colorable 2 := by
    rw [← chromaticNumber_le_iff_colorable]
    apply (ENat.lt_add_one_iff (by decide : (2 : ℕ∞) ≠ ⊤)).mp
    have h2 : (2 : ℕ∞) ≤ (G.induce ({x, y} : Set V)).chromaticNumber :=
      two_le_chromaticNumber_of_adj
        (u := ⟨x, by simp⟩) (v := ⟨y, by simp⟩) hxy
    have hlt : (G.induce ({x, y} : Set V)ᶜ).chromaticNumber < (3 : ℕ∞) :=
      lt_of_not_ge (fun h3 => hsplit ⟨{x, y}, h2, h3⟩)
    exact hlt
  by_cases ht : ∃ t : Finset V, G.IsNClique 3 t
  · obtain ⟨t, ht⟩ := ht
    exact hno3 (three_coloring_of_triangle G hfree hdel ht)
  · have hedge : ∃ x y, G.Adj x y := by
      by_contra hn
      exact hno3 ⟨Coloring.mk (fun _ => (0 : Fin 3)) (fun {x y} h => (hn ⟨x, y, h⟩).elim)⟩
    obtain ⟨x, y, hxy⟩ := hedge
    have hno (v : V) (hxv : G.Adj x v) (hyv : G.Adj y v) : False :=
      ht ⟨{x, y, v}, is3Clique_triple_iff.mpr ⟨hxy, hxv, hyv⟩⟩
    exact hno3 (three_coloring_of_edge_without_common_neighbor G hxy hno (hdel x y hxy))

end OMA.Erdos628CaseFour

theorem OMA.solution : OMA.R_Erdos628_erdos_628_R1_H1_R1.H1 := by
  intro n k G hchi hfree _ hk
  subst k
  exact OMA.Erdos628CaseFour.split_four G hchi hfree
