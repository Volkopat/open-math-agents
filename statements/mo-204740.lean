import Mathlib

/-!
# Orthogonal complements of intersections of closed subspaces

Source: https://mathoverflow.net/questions/204740
Credit: @artnoage

The source: let `H` be a Hilbert space and `H_1, ..., H_n` closed subspaces of `H`. Is it always
true that the orthogonal complement `(H_1 ∩ ... ∩ H_n)^⊥` of the intersection equals the sum
`H_1^⊥ + ... + H_n^⊥` of the orthogonal complements?

Choices made here:

* The statement is the negative answer: the equality is not true for all Hilbert spaces and all
  finite families of closed subspaces. It is stated for real Hilbert spaces.
* The sum of subspaces is the algebraic sum, which is the supremum `⨆` in the lattice of
  submodules (no closure is taken), as in the first question of the source.
* The follow-up about infinitely many subspaces (with the closure of the sum) is conditional on
  a positive answer and is not stated.
-/

namespace OMA.S_mo_204740

theorem main :
    ¬ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (n : ℕ) (K : Fin n → Submodule ℝ H), (∀ i, IsClosed (K i : Set H)) →
        (⨅ i, K i)ᗮ = ⨆ i, (K i)ᗮ := by
  sorry

end OMA.S_mo_204740
