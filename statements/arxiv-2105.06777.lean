import Mathlib

namespace OMA.S_arxiv_2105_06777

/-- The generalized blow-up of a finite simple graph `G` on `Fin n`, replacing each vertex `i`
by a block of `sizes i` vertices that induces either a clique (`isClique i = true`) or an
independent set (`isClique i = false`), with complete bipartite joins between adjacent blocks. -/
def blowup {n : ℕ} (G : SimpleGraph (Fin n)) (sizes : Fin n → ℕ)
    (isClique : Fin n → Bool) : SimpleGraph ((i : Fin n) × Fin (sizes i)) where
  Adj u v := u ≠ v ∧ (G.Adj u.1 v.1 ∨ (u.1 = v.1 ∧ isClique u.1 = true))
  symm := ⟨by
    intro u v ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with hadj | ⟨heq, hcl⟩
    · exact Or.inl hadj.symm
    · exact Or.inr ⟨heq.symm, heq ▸ hcl⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The finite set of shortest paths from `u` to `v` in `G`, represented as sequences of
`G.dist u v + 1` vertices starting at `u`, ending at `v`, with consecutive vertices adjacent. -/
noncomputable def shortestPaths {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) : Finset (Fin (G.dist u v + 1) → V) := by
  classical
  exact Finset.univ.filter fun w =>
    w 0 = u ∧ w ⟨G.dist u v, Nat.lt_succ_self _⟩ = v ∧
    ∀ k : Fin (G.dist u v), G.Adj (w k.castSucc) (w k.succ)

/-- Whether a path `w : Fin (L + 1) → V` passes strictly through `x` as an internal vertex. -/
def passesThrough {V : Type*} {L : ℕ} (x : V) (w : Fin (L + 1) → V) : Prop :=
  ∃ k : Fin (L + 1), 0 < k.val ∧ k.val < L ∧ w k = x

/-- Number of shortest paths between `u` and `v` in `G`. -/
noncomputable def sigma {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) : ℕ :=
  (shortestPaths G u v).card

/-- Number of shortest paths between `u` and `v` in `G` passing strictly through `x`. -/
noncomputable def sigmaThrough {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v x : V) : ℕ := by
  classical
  exact ((shortestPaths G u v).filter (passesThrough x)).card

/-- Betweenness centrality of a vertex `x` in a finite simple graph `G` (summed over ordered
distinct pairs `(u, v)` not equal to `x`). -/
noncomputable def betweenness {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) : ℚ :=
  ∑ u : V, ∑ v : V,
    if u ≠ x ∧ v ≠ x ∧ u ≠ v ∧ 0 < sigma G u v then
      (sigmaThrough G u v x : ℚ) / (sigma G u v : ℚ)
    else 0

/-- A finite simple graph is betweenness-uniform if all vertices have the same betweenness
centrality. -/
def IsBetweennessUniform {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∀ x y : V, betweenness G x = betweenness G y

/-- Universality conjecture for the blow-up construction (disproved in arXiv:2105.06777,
"Constructions of betweenness-uniform graphs from trees"): every finite tree can be transformed
into a betweenness-uniform graph by some generalized blow-up with positive block sizes. -/
theorem main :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.IsTree →
      ∃ (sizes : Fin n → ℕ) (isClique : Fin n → Bool),
        (∀ i, 0 < sizes i) ∧ IsBetweennessUniform (blowup G sizes isClique) := by
  sorry

end OMA.S_arxiv_2105_06777
