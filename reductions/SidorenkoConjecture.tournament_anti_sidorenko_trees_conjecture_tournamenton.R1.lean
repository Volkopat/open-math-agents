import FormalConjectures.Wikipedia.SidorenkoConjecture

-- Reduction SidorenkoConjecture.tournament_anti_sidorenko_trees_conjecture_tournamenton.R1.
-- Credit: @marcusbuffett

/-!
# Tournament anti-Sidorenko for trees (tournamenton form): stars versus the rest

Split by the shape of the tree.

* `H1` (proved in the step): every star `K_{1,k}` (a tree all of whose edges contain one centre)
  has an orientation with `t(T, W) ≤ 2^{-k}` for every tournamenton `W`. Orient
  `⌈k/2⌉` leaves out of the centre and `⌊k/2⌋` into it; by Fubini the density is
  `∫ d(x)^{⌈k/2⌉} (1 - d(x))^{⌊k/2⌋} dx` with `d(x) = ∫ W(x, y) dy`, and
  `d (1 - d) ≤ 1/4` together with `∫ d = 1/2` (from `W(x, y) + W(y, x) = 1`) gives `2^{-k}`.
* `H2` (open core): the same statement for trees that are not stars (diameter at least 3).

`main` transports an arbitrary finite vertex type to `Fin (card V)` and splits on the shape.
This is the star case of the conjecture, not progress on the general tree case.
-/

namespace OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_tournamenton_R1

open LimitObjects MeasureTheory

open scoped Classical in
/-- Stars satisfy the tournamenton TAS inequality. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree → (∃ c : V, ∀ u v : V, T.Adj u v → u = c ∨ v = c) →
      ∃ D : Digraph V, D.IsOrientation T ∧
        ∀ W : Tournamenton, tournamentonHomDensity D W ≤ (1 / 2 : ℝ) ^ T.edgeFinset.card

open scoped Classical in
/-- Trees that are not stars satisfy the tournamenton TAS inequality (open). -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree → (¬ ∃ c : V, ∀ u v : V, T.Adj u v → u = c ∨ v = c) →
      ∃ D : Digraph V, D.IsOrientation T ∧
        ∀ W : Tournamenton, tournamentonHomDensity D W ≤ (1 / 2 : ℝ) ^ T.edgeFinset.card

/-- The tournamenton density is invariant under relabelling the vertices. -/
lemma density_comap {V : Type*} {V' : Type*} [Fintype V] [DecidableEq V] [Fintype V']
    [DecidableEq V'] (e : V ≃ V') (D' : Digraph V') (D : Digraph V)
    (hD : ∀ u v, D.Adj u v ↔ D'.Adj (e u) (e v)) [DecidableRel D.Adj] [DecidableRel D'.Adj]
    (W : Tournamenton) : tournamentonHomDensity D W = tournamentonHomDensity D' W := by
  unfold tournamentonHomDensity
  have hmp := measurePreserving_piCongrLeft (fun _ : V' => (volume : Measure unitInterval)) e
  rw [← hmp.integral_comp' (tournamentonHomIntegrand D' W)]
  congr 1
  funext x
  unfold tournamentonHomIntegrand
  refine Finset.prod_nbij (fun p => (e p.1, e p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [digraphEdgeFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact (hD _ _).1 hp
  · intro a _ b _ h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    exact Prod.ext h.1 h.2
  · intro q hq
    refine ⟨(e.symm q.1, e.symm q.2), ?_, by simp⟩
    simp only [digraphEdgeFinset, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hq ⊢
    rw [hD]
    simpa using hq
  · intro p _
    simp only [MeasurableEquiv.coe_piCongrLeft]
    rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]

theorem main : H1 → H2 →
    type_of% @SidorenkoConjecture.tournament_anti_sidorenko_trees_conjecture_tournamenton := by
  intro h1 h2 V _ _ T _ hT
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let T' : SimpleGraph (Fin (Fintype.card V)) := T.comap e.symm
  let iso : T ≃g T' := { toEquiv := e, map_rel_iff' := by intro a b; simp [T'] }
  have hT' : T'.IsTree := iso.isTree_iff.1 hT
  have key : ∃ D' : Digraph (Fin (Fintype.card V)), D'.IsOrientation T' ∧
      ∀ W : Tournamenton, tournamentonHomDensity D' W ≤ (1 / 2 : ℝ) ^ T'.edgeFinset.card := by
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
  · intro W
    rw [density_comap e D' _ (fun _ _ => Iff.rfl), iso.card_edgeFinset_eq]
    exact hW W

end OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_tournamenton_R1
