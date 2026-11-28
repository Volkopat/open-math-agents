import FormalConjectures.ErdosProblems.«23»

/-!
Every triangle-free graph on five vertices becomes bipartite after deleting at most one edge.

Colour the vertices by a predicate `c` and keep exactly the edges whose ends get different
colours; that subgraph is bipartite, so it is enough to find a `c` for which any two edges
with equally coloured ends coincide.

* If some vertex `v` has two distinct neighbours `a`, `b`, take `c = G.Adj v`. An edge with
  equally coloured ends cannot join two neighbours of `v` (triangle), so it joins two
  non-neighbours, and it avoids `v`, `a`, `b`: only two vertices are left, hence one edge.
* Otherwise the graph is a matching; colour a vertex by "is the smaller end of its edge".
  Then no edge has equally coloured ends.
-/

open SimpleGraph

theorem OMA.solution : type_of% @Erdos23.erdos_23.variants.n1 := by
  intro G hG
  -- Five vertices: two pairs avoiding three given distinct vertices are the same pair.
  have D : ∀ v a b x y x' y' : Fin 5, v ≠ a → v ≠ b → a ≠ b → x ≠ v → x ≠ a → x ≠ b →
      y ≠ v → y ≠ a → y ≠ b → x ≠ y → x' ≠ v → x' ≠ a → x' ≠ b → y' ≠ v → y' ≠ a → y' ≠ b →
      x' ≠ y' → x = x' ∧ y = y' ∨ x = y' ∧ y = x' := by decide +kernel
  classical
  have tri : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → False :=
    fun a b c h1 h2 h3 => hG _ (is3Clique_triple_iff.2 ⟨h1, h2, h3⟩)
  have key : ∃ c : Fin 5 → Prop, ∀ x y x' y', G.Adj x y → (c x ↔ c y) → G.Adj x' y' →
      (c x' ↔ c y') → s(x, y) = s(x', y') := by
    by_cases h : ∃ v a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b
    · obtain ⟨v, a, b, hab, ha, hb⟩ := h
      refine ⟨G.Adj v, fun x y x' y' h1 h2 h3 h4 => ?_⟩
      have nx : ¬ G.Adj v x := fun h => tri v x y h (h2.1 h) h1
      have ny : ¬ G.Adj v y := fun h => nx (h2.2 h)
      have nx' : ¬ G.Adj v x' := fun h => tri v x' y' h (h4.1 h) h3
      have ny' : ¬ G.Adj v y' := fun h => nx' (h4.2 h)
      have := h1.symm; have := h3.symm; have := h1.ne; have := h3.ne
      rw [Sym2.eq_iff]
      apply D v a b <;> grind
    · refine ⟨fun x => ∃ y, G.Adj x y ∧ x < y, fun x y x' y' h1 h2 h3 h4 => ?_⟩
      exfalso
      have := h1.symm; have := h1.ne
      grind
  obtain ⟨c, hc⟩ := key
  refine ⟨G ⊓ (⊤ : SimpleGraph Prop).comap c, inf_le_left, ?_, ?_⟩
  · simpa using (Coloring.mk c fun h => h.2 : (G ⊓ (⊤ : SimpleGraph Prop).comap c).Coloring Prop).colorable
  · refine Finset.card_le_one.2 fun e he e' he' => ?_
    induction e with | _ x y
    induction e' with | _ x' y'
    simp at he he'
    exact hc _ _ _ _ he.1 (by grind) he'.1 (by grind)
