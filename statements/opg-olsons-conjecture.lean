import Mathlib

/-!
# Olson's Conjecture

Source: https://www.openproblemgarden.org/op/olsons_conjecture
Credit: @ishaanzee

**Conjecture** (J. E. Olson). If `a₁, a₂, …, a₂ₙ₋₁` is a sequence of elements from a
multiplicative group of order `n`, then there exist `1 ≤ j₁ < j₂ < … < jₙ ≤ 2n - 1` so that
`∏_{i=1}^{n} a_{jᵢ} = 1`.

The Erdős–Ginzburg–Ziv theorem is the abelian case. Olson proved that in an arbitrary group of
order `n` some `n` terms of such a sequence have product `1` *in some order*; the conjecture is
that no reordering is needed: the product is taken in the order of the indices.

Formalization: the group is a finite group `G` with `n = Fintype.card G`, the sequence is
`a : Fin (2 * n - 1) → G` (indices shifted to start at `0`), the chosen indices are a strictly
increasing `j : Fin n → Fin (2 * n - 1)`, and the product `a (j 0) * a (j 1) * ⋯ * a (j (n-1))`
is `(List.ofFn fun i => a (j i)).prod`, which multiplies in the order of the indices.
-/

namespace OMA.S_opg_olsons_conjecture

universe u

/-- **Olson's conjecture**: every sequence of `2n - 1` elements of a group of order `n` has `n`
terms, taken in their original order, whose product is `1`. -/
theorem main : ∀ (G : Type u) [Group G] [Fintype G] (a : Fin (2 * Fintype.card G - 1) → G),
    ∃ j : Fin (Fintype.card G) → Fin (2 * Fintype.card G - 1),
      StrictMono j ∧ (List.ofFn fun i => a (j i)).prod = 1 := by
  sorry

end OMA.S_opg_olsons_conjecture
