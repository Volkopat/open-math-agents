import Mathlib

/-!
# A294225: A triple of practical numbers

Source: https://oeis.org/A294225
Formalization: @pyaf

Every natural number up to a practical number is a sum of distinct divisors of it.
-/

namespace OMA.S_oeis_a294225

def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m ≤ n → ∃ s ⊆ n.divisors, ∑ i ∈ s, i = m

theorem main : {q : ℕ | IsPractical q ∧ IsPractical (q + 2) ∧ IsPractical (q ^ 2 + 2)}.Infinite := by
  sorry

end OMA.S_oeis_a294225
