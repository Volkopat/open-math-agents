import Mathlib

/-!
# Equal sums in two bounded multisets

Zeyu asked whether two nonempty submultisets of equal sum always exist
when each multiset's cardinality bounds all the entries of the other.
Gjergji Zaimi identified the 19-by-93 case as the 1993 Putnam problem A4.

Source: https://mathoverflow.net/questions/16041/is-it-always-possible-to-choose-two-subsets-with-the-same-sum
Credit: @dwilfand-sys (formalization by Codex)
-/

namespace OMA.S_mo_16041

theorem main : ∀ (n m : ℕ), 0 < n → 0 < m → ∀ A B : Multiset ℕ,
    A.card = n → B.card = m →
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ m) → (∀ b ∈ B, 1 ≤ b ∧ b ≤ n) →
    ∃ X ≤ A, ∃ Y ≤ B, X ≠ 0 ∧ Y ≠ 0 ∧ X.sum = Y.sum := by
  sorry

end OMA.S_mo_16041
