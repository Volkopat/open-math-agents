import Mathlib

/-!
# Connectivity of the reconfiguration graph of Hamiltonian paths under backbites

Source: arXiv:2610.05068, "Connectivity of the reconfiguration graph of Hamiltonian paths",
Conjecture 7.8.
Credit: @jagraj28

A *backbite* on a Hamiltonian path `w₁ ⋯ wₙ` of a graph `G` chooses an endpoint, say `w₁`, and an
index `k ≥ 3` with `{w₁, w_k} ∈ E(G)`, adds the edge `{w₁, w_k}` and deletes `{w_{k-1}, w_k}`.
The result is the Hamiltonian path `w_{k-1}, …, w₁, w_k, …, w_n` (Observation 2.1); a backbite at
`wₙ` is symmetric. The reconfiguration graph `R(G)` has the Hamiltonian paths of `G` as vertices
(a path and its reversal are the same vertex), joined when one backbite carries one to the other.
The paper shows that `R(G)` can be disconnected when the minimum degree is `⌊n/2⌋ - 3`, and states:

  Conjecture 7.8. Let `G` be a graph on `n` vertices with minimum degree at least `n/2`. Then
  `R(G)` is connected, that is, any two Hamiltonian paths of `G` can be reconfigured into one
  another by a sequence of backbite moves.

Conventions.
* Graphs are `SimpleGraph (Fin n)`. "Minimum degree at least `n/2`" is `n ≤ 2 * G.degree v` for
  every vertex `v`.
* A Hamiltonian path is a list `w` of vertices with no repetition, containing every vertex
  (`w.length = n`), and with consecutive entries adjacent (`List.IsChain`).
* With 0-based indices, the backbite at the first endpoint with partner `w[j]`, `j ≥ 2`, sends `w`
  to `(w.take j).reverse ++ w.drop j`. A backbite at the last endpoint is the same operation
  applied to `w.reverse`. A path and its reversal are identified by allowing either orientation
  on both sides of a move.
* "`R(G)` is connected" is stated as: any two Hamiltonian paths are related by the
  reflexive-transitive closure of the move relation (backbites are invertible, so this relation
  is symmetric).
-/

namespace OMA.S_arxiv_2610_05068

variable {n : ℕ}

/-- `w` is a Hamiltonian path of `G`, given as its list of vertices. -/
def IsHamPath (G : SimpleGraph (Fin n)) (w : List (Fin n)) : Prop :=
  w.Nodup ∧ w.length = n ∧ w.IsChain G.Adj

/-- A backbite at the first vertex of `w`, using the edge from `w[0]` to `w[j]`, `j ≥ 2`. -/
def Backbite (G : SimpleGraph (Fin n)) (w w' : List (Fin n)) : Prop :=
  ∃ (j : ℕ) (hj : j < w.length) (h0 : 0 < w.length), 2 ≤ j ∧
    G.Adj (w.get ⟨0, h0⟩) (w.get ⟨j, hj⟩) ∧ w' = (w.take j).reverse ++ w.drop j

/-- One backbite move between Hamiltonian paths, at either endpoint, with paths identified with
their reversals. -/
def Move (G : SimpleGraph (Fin n)) (w w' : List (Fin n)) : Prop :=
  ∃ u ∈ [w, w.reverse], ∃ u' ∈ [w', w'.reverse], Backbite G u u'

/-- Conjecture 7.8: if `G` has minimum degree at least `n/2`, any two Hamiltonian paths of `G`
are connected by a sequence of backbite moves. -/
theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ v, n ≤ 2 * G.degree v) →
    ∀ w w' : List (Fin n), IsHamPath G w → IsHamPath G w' → Relation.ReflTransGen (Move G) w w' := by
  sorry

end OMA.S_arxiv_2610_05068
