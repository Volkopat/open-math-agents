import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fintype.Fin

/-!
# The special-node conjecture for symmetric travelling-salesman instances

Source: Ehsan Javanbakht, https://math.stackexchange.com/questions/4804070,
and the author's document linked from that question:
https://docs.google.com/document/d/1EpoB2uS_QnEaweDEIOl2ucLaHrd4QD5EJfxh8ww9fwM/edit

The concrete conjecture asserts that every symmetric distance matrix has an
optimal Hamiltonian cycle containing the two smallest incident edges at some
vertex. A Hamiltonian cycle is represented by a permutation of all vertices,
with cyclically adjacent positions joined, including the last-to-first edge.
The special-node predicate says both selected edges are no heavier than every
other incident edge. Diagonal entries do not represent edges. The main theorem
also includes the author's 12 November 2023 clarification on the linked Reddit
crosspost, requiring distinct weights on distinct undirected edges:
https://www.reddit.com/r/math/comments/17rxc28
No triangle inequality or Euclidean realization is assumed in the source.

This is the explicit existence conjecture in the linked document. It is not
the separate question whether removing a fixed proportion of edges by itself
establishes polynomial running time.
-/

noncomputable section

namespace OMA.S_mse_4804070

def tourLength {n : ℕ} (d : Fin n → Fin n → ℝ) (p : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i : Fin n, d (p i) (p (finRotate n i))

def IsSpecial {n : ℕ} (d : Fin n → Fin n → ℝ)
    (p : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∀ w : Fin n, w ≠ p i →
    w ≠ p ((finRotate n).symm i) → w ≠ p (finRotate n i) →
    d (p i) (p ((finRotate n).symm i)) ≤ d (p i) w ∧
    d (p i) (p (finRotate n i)) ≤ d (p i) w

theorem main :
    ∀ n : ℕ, 3 ≤ n → ∀ d : Fin n → Fin n → ℝ,
      (∀ i, d i i = 0) →
      (∀ i j, d i j = d j i) →
      (∀ i j, 0 ≤ d i j) →
      (∀ i j k l, i ≠ j → k ≠ l → d i j = d k l →
        (i = k ∧ j = l) ∨ (i = l ∧ j = k)) →
      ∃ p : Equiv.Perm (Fin n),
        (∀ q : Equiv.Perm (Fin n), tourLength d p ≤ tourLength d q) ∧
        ∃ i : Fin n, IsSpecial d p i := by
  sorry

end OMA.S_mse_4804070
