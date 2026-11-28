import Mathlib

-- Rota's basis conjecture (matroid form)
-- Source: https://en.wikipedia.org/wiki/Rota%27s_basis_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
Source: if `X` is a vector space of dimension `n`, or more generally a matroid of rank `n`, with
`n` disjoint bases `B_i`, then the elements of these bases can be arranged into an `n × n` matrix
whose rows are exactly the given bases and whose columns are also bases.

Conventions:
* The general (matroid) form is stated, with Mathlib's `Matroid`, `Matroid.IsBase` and
  `Matroid.eRank`; the vector-space form is the special case of the matroid of a family of vectors.
* An `n × n` arrangement is `A : Fin n → Fin n → α`; row `i` is exactly `B i` means
  `Set.range (A i) = B i`, and column `j` is a basis means `M.IsBase (Set.range fun i => A i j)`.
  Each basis has exactly `n` elements, so these conditions force the entries of each row and
  each column to be distinct, and every element of every `B i` appears exactly once.
* `n` ranges over all natural numbers (for `n = 0` the statement is trivial).
-/

universe u

namespace OMA.S_wp_rota_s_basis_conjecture

/-- Rota's basis conjecture for matroids. -/
theorem main : ∀ (α : Type u) (M : Matroid α) (n : ℕ), M.eRank = n →
    ∀ B : Fin n → Set α, (∀ i, M.IsBase (B i)) → Pairwise (Function.onFun Disjoint B) →
      ∃ A : Fin n → Fin n → α, (∀ i, Set.range (A i) = B i) ∧
        ∀ j, M.IsBase (Set.range fun i => A i j) := by
  sorry

end OMA.S_wp_rota_s_basis_conjecture
