import FormalConjectures.ErdosProblems.«719»

-- Reduction Erdos719.erdos_719.R1 of Erdős Problem 719
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch: split the statement by the uniformity r.
-- * H1 (r = 2, graphs): every graph on n vertices is an edge-disjoint union of at most
--   ex(n; K_3) = floor(n^2/4) edges and triangles. This is the theorem of Erdős, Goodman
--   and Pósa (Canad. J. Math. 1966, The representation of a graph by set intersections),
--   which is not yet in Mathlib.
-- * H2 (r ≥ 3): the open hypergraph case.
-- The statements for different r are independent (no case implies another), and main is a
-- case split r = 2 or r ≥ 3. No computer search was used.

namespace OMA.R_Erdos719_erdos_719_R1

/-- The graph case `r = 2` (Erdős–Goodman–Pósa). -/
def H1 : Prop :=
  ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
    H.IsUniform 2 → ∃ D : Finset (Finset (Fin n)),
      H.IsCompleteHypergraphDecomposition 2 D ∧
        D.card ≤ Hypergraph.cliqueExtremalNumber n 2 (2 + 1)

/-- The hypergraph case `r ≥ 3`. -/
def H2 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
    H.IsUniform r → ∃ D : Finset (Finset (Fin n)),
      H.IsCompleteHypergraphDecomposition r D ∧
        D.card ≤ Hypergraph.cliqueExtremalNumber n r (r + 1)

theorem main : H1 → H2 → type_of% @Erdos719.erdos_719 := by
  intro h1 h2 r hr
  unfold H1 at h1
  unfold H2 at h2
  rcases (show r = 2 ∨ 3 ≤ r by omega) with h | h
  · subst h
    exact h1
  · exact h2 r h

end OMA.R_Erdos719_erdos_719_R1
