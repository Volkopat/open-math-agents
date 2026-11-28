import Mathlib

/-!
# Cardinality of the union of a chain

Source: https://mathoverflow.net/questions/363564
Asked by MathOverflow user Michelle.

Given an index set `I` and two chains `(U_i)_{i ∈ I}` and `(V_i)_{i ∈ I}` of sets with
`|U_i| ≤ |V_i|` for each `i`, is it necessarily true that
`|⋃_{i ∈ I} U_i| ≤ |⋃_{i ∈ I} V_i|`?

Translation choices.
* The two chains are indexed by a common linearly ordered index type `I` and both are
  increasing along this order (`Monotone U`, `Monotone V`), so each family is a chain under
  inclusion. This is the reading of the question in which the asker attempts a proof (by
  well-ordering `I`); it is also the strongest form of the hypotheses.
* The sets live in arbitrary types `α`, `β` (in `Type`), and `|·|` is `Cardinal.mk`.
* `main` is the affirmative answer.
-/

namespace OMA.S_mo_363564

theorem main :
    ∀ (I α β : Type) [LinearOrder I] (U : I → Set α) (V : I → Set β),
      Monotone U → Monotone V → (∀ i, Cardinal.mk (U i) ≤ Cardinal.mk (V i)) →
        Cardinal.mk (⋃ i, U i) ≤ Cardinal.mk (⋃ i, V i) := by
  sorry

end OMA.S_mo_363564
