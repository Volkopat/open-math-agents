import Mathlib

/-!
Uniqueness conjecture for Markov numbers.

Source: https://en.wikipedia.org/wiki/Markov_number#Other_properties
Credit: @Tchikrazi
-/

namespace OMA.S_wp_uniqueness_conjecture_for_markov_numbers

/-- A normalized Markov triple consists of positive integers in nondecreasing order. -/
def IsNormalizedMarkovTriple (a b c : ℕ) : Prop :=
  0 < a ∧ a ≤ b ∧ b ≤ c ∧ a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c

/-- Each Markov number occurs as the largest entry of a unique normalized triple. -/
theorem main :
    ∀ a b c a' b' : ℕ,
      IsNormalizedMarkovTriple a b c →
      IsNormalizedMarkovTriple a' b' c →
      a = a' ∧ b = b' := by
  sorry

end OMA.S_wp_uniqueness_conjecture_for_markov_numbers
