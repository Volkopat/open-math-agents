import FormalConjectures.Wikipedia.SidorenkoConjecture

-- Reduction SidorenkoConjecture.tournament_anti_sidorenko_trees_conjecture.R1.
-- Credit: @marcusbuffett

/-!
# Tournament anti-Sidorenko for trees (finite tournaments): stars versus the rest

Split by the shape of the tree.

* `H1` (proved in the step): every star `K_{1,k}` (a tree all of whose edges contain one centre)
  has an orientation with `t(T, G) ≤ 2^{-k}` for every finite tournament `G`. Orient `⌈k/2⌉`
  leaves out of the centre and `⌊k/2⌋` into it; homomorphisms are counted by the image `x` of the
  centre, giving `Σ_x d⁺(x)^{⌈k/2⌉} d⁻(x)^{⌊k/2⌋}`. As `d⁺(x) + d⁻(x) = |G| - 1` and
  `Σ_x d⁺(x) = |G|(|G|-1)/2`, AM-GM gives at most `|G|^{k+1} / 2^k`. For odd `k` every vertex of
  the star has odd degree, so this is not covered by the solved single-even-degree case.
* `H2` (open core): the same statement for trees that are not stars (diameter at least 3).

`main` relabels the tree to `Fin (card V)` and the tournament to `Fin (card W)` (hom counts and
densities are invariant under relabelling) and splits on the shape of the tree.
This is the star case of the conjecture, not progress on the general tree case.
-/

namespace OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R1

open scoped Classical in
/-- Stars satisfy the TAS inequality for finite tournaments. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree → (∃ c : V, ∀ u v : V, T.Adj u v → u = c ∨ v = c) →
      ∃ D : Digraph V, D.IsOrientation T ∧
        ∀ {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : Digraph W) [DecidableRel G.Adj],
          G.IsTournament → Digraph.homDensity D G ≤ (1 / 2 : ℝ) ^ T.edgeFinset.card

open scoped Classical in
/-- Trees that are not stars satisfy the TAS inequality for finite tournaments (open). -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree → (¬ ∃ c : V, ∀ u v : V, T.Adj u v → u = c ∨ v = c) →
      ∃ D : Digraph V, D.IsOrientation T ∧
        ∀ {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : Digraph W) [DecidableRel G.Adj],
          G.IsTournament → Digraph.homDensity D G ≤ (1 / 2 : ℝ) ^ T.edgeFinset.card


lemma hom_ext {V W : Type*} {D : Digraph V} {G : Digraph W} {f g : D →g G}
    (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

/-- Relabelling the source digraph does not change the hom count. -/
lemma homCount_comap {V V' W : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    [Fintype W] [DecidableEq W] (e : V ≃ V') (D' : Digraph V') (D : Digraph V)
    (hD : ∀ u v, D.Adj u v ↔ D'.Adj (e u) (e v)) (G : Digraph W) [DecidableRel D.Adj]
    [DecidableRel D'.Adj] [DecidableRel G.Adj] :
    Digraph.homCount D G = Digraph.homCount D' G := by
  unfold Digraph.homCount
  refine Fintype.card_congr
    { toFun := fun f => ⟨fun v' => f.toFun (e.symm v'), fun {u v} h => f.map_adj' ((hD _ _).2
        (by simpa using h))⟩
      invFun := fun g => ⟨fun v => g.toFun (e v), fun {u v} h => g.map_adj' ((hD _ _).1 h)⟩
      left_inv := fun f => hom_ext (by funext v; simp)
      right_inv := fun g => hom_ext (by funext v; simp) }

/-- Relabelling the host digraph does not change the hom count. -/
lemma homCount_map {V W W' : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype W'] [DecidableEq W'] (σ : W ≃ W') (G : Digraph W) (G' : Digraph W')
    (hG : ∀ x y, G.Adj x y ↔ G'.Adj (σ x) (σ y)) (D : Digraph V) [DecidableRel D.Adj]
    [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    Digraph.homCount D G = Digraph.homCount D G' := by
  unfold Digraph.homCount
  refine Fintype.card_congr
    { toFun := fun f => ⟨fun v => σ (f.toFun v), fun {u v} h => (hG _ _).1 (f.map_adj' h)⟩
      invFun := fun g => ⟨fun v => σ.symm (g.toFun v), fun {u v} h => (hG _ _).2
        (by simpa using g.map_adj' h)⟩
      left_inv := fun f => hom_ext (by funext v; simp)
      right_inv := fun g => hom_ext (by funext v; simp) }

lemma homDensity_comap {V V' W : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    [Fintype W] [DecidableEq W] (e : V ≃ V') (D' : Digraph V') (D : Digraph V)
    (hD : ∀ u v, D.Adj u v ↔ D'.Adj (e u) (e v)) (G : Digraph W) [DecidableRel D.Adj]
    [DecidableRel D'.Adj] [DecidableRel G.Adj] :
    Digraph.homDensity D G = Digraph.homDensity D' G := by
  unfold Digraph.homDensity
  rw [homCount_comap e D' D hD G, Fintype.card_congr e]

lemma homDensity_map {V W W' : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype W'] [DecidableEq W'] (σ : W ≃ W') (G : Digraph W) (G' : Digraph W')
    (hG : ∀ x y, G.Adj x y ↔ G'.Adj (σ x) (σ y)) (D : Digraph V) [DecidableRel D.Adj]
    [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    Digraph.homDensity D G = Digraph.homDensity D G' := by
  unfold Digraph.homDensity
  rw [homCount_map σ G G' hG D, Fintype.card_congr σ]

theorem main : H1 → H2 →
    type_of% @SidorenkoConjecture.tournament_anti_sidorenko_trees_conjecture := by
  intro h1 h2 V _ _ T _ hT
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let T' : SimpleGraph (Fin (Fintype.card V)) := T.comap e.symm
  let iso : T ≃g T' := { toEquiv := e, map_rel_iff' := by intro a b; simp [T'] }
  have hT' : T'.IsTree := iso.isTree_iff.1 hT
  have key : ∃ D' : Digraph (Fin (Fintype.card V)), D'.IsOrientation T' ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : Digraph W) [DecidableRel G.Adj],
        G.IsTournament → Digraph.homDensity D' G ≤ (1 / 2 : ℝ) ^ T'.edgeFinset.card := by
    by_cases hs : ∃ c, ∀ u v, T'.Adj u v → u = c ∨ v = c
    · exact h1 T' hT' hs
    · exact h2 T' hT' hs
  obtain ⟨D', hor, hW⟩ := key
  refine ⟨⟨fun u v => D'.Adj (e u) (e v)⟩, ⟨?_, ?_⟩, ?_⟩
  · intro u v h
    have := hor.1 _ _ h
    simpa [T'] using this
  · intro u v h
    exact hor.2 (e u) (e v) (by simpa [T'] using h)
  · intro W _ _ _ G _ hG
    let σ : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
    let G' : Digraph (Fin (Fintype.card W)) := ⟨fun x y => G.Adj (σ.symm x) (σ.symm y)⟩
    have hG' : G'.IsTournament := by
      refine ⟨fun x => hG.1 _, fun x y hxy => hG.2 _ _ ?_⟩
      exact fun h => hxy (σ.symm.injective h)
    have : Nonempty (Fin (Fintype.card W)) := ⟨σ (Classical.arbitrary W)⟩
    rw [homDensity_comap e D' _ (fun _ _ => Iff.rfl) G,
      homDensity_map σ G G' (fun x y => by simp [G']) D', iso.card_edgeFinset_eq]
    exact hW G' hG'

end OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R1
