import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# A lower bound for graph Metropolis-Hastings eigenvalues

Source: https://mathoverflow.net/questions/239951/lower-bound-for-smallest-eigenvalue-of-symmetric-doubly-stochastic-metropolis-ha
Credit: @etaubman.

The transition weights are defined from the actual graph degrees and neighbor sets.
For a real symmetric matrix the asserted least-eigenvalue bound is equivalent to
this bound for every real eigenpair with nonzero eigenvector.
-/

open scoped BigOperators

namespace OMA.S_mo_239951

noncomputable def transition {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  fun i j => if i = j then
    1 - ∑ k ∈ G.neighborFinset i,
      (1 : ℝ) / ((max (G.degree i) (G.degree k) : ℕ) + 1)
  else if G.Adj i j then
    (1 : ℝ) / ((max (G.degree i) (G.degree j) : ℕ) + 1)
  else 0

def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → ∀ (eigenvalue : ℝ) (v : V → ℝ),
      v ≠ 0 → (transition G).mulVec v = eigenvalue • v → -(1 / 2 : ℝ) ≤ eigenvalue

theorem main : claim := by
  sorry

end OMA.S_mo_239951
