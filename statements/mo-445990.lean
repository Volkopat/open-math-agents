import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Combinatorics.Enumerative.Stirling

/-! Source: https://mathoverflow.net/questions/445990 -/

open scoped BigOperators

namespace OMA.S_mo_445990

def closedForm (n : ℕ) (m k : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1),
    (Nat.stirlingSecond n i : ℤ) * (m - k) ^ (n - i) *
      ∏ j ∈ Finset.range i, (k * (j : ℤ) + 1)

/-- A finite set records the positions of the nonzero bits of an integer. -/
theorem main :
    ∀ m k : ℤ, ∀ b : Finset ℕ → ℤ, b ∅ = 1 →
      (∀ (d : ℕ) (S : Finset ℕ), S ⊆ Finset.range d →
        b (insert d S) = m * ((d + 1 - S.card : ℕ) : ℤ) * b S +
          ∑ j ∈ Finset.range d \ S, k * b (insert j S)) →
      ∀ n : ℕ, (∑ S ∈ (Finset.range n).powerset, b S) = closedForm (n + 1) m k := by
  sorry

end OMA.S_mo_445990
