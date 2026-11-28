import Mathlib

/-!
# Semimagic squares and partitions

Source: https://mathoverflow.net/questions/121754
Credit: @zarnab222-dev

Given a square matrix of natural numbers with common row and column sum
`s`, can each cell be assigned a subset of an arbitrary set of `s` labels
whose size equals the cell entry? Every label must occur in exactly one
cell of each row and exactly one cell of each column. This expresses the
two partitions without choosing an ordering of the labels.
-/

namespace OMA.S_mo_121754

theorem main : ∀ (n s : ℕ) (X : Fin n → Fin n → ℕ)
    (M : Type*) [Fintype M], Fintype.card M = s →
    (∀ i, ∑ j, X i j = s) → (∀ j, ∑ i, X i j = s) →
    ∃ T : Fin n → Fin n → Finset M,
      (∀ i j, (T i j).card = X i j) ∧
      (∀ i m, ∃! j, m ∈ T i j) ∧ (∀ j m, ∃! i, m ∈ T i j) := by
  sorry

end OMA.S_mo_121754
