import Mathlib

/-!
# A391037: Representations using a scaled fourth power and three squares

Source: https://oeis.org/A391037, conjecture of Zhi-Wei Sun.
The sequence counts representations for coefficient `1`. The conjecture asks
for a representation for every positive integer at each of `1`, `5`, and `7`.
-/

namespace OMA.S_oeis_a391037

def OneOrOddPrime (p : ℕ) : Prop := p = 1 ∨ (p.Prime ∧ Odd p)

theorem main : ∀ c : ℕ, c ∈ ({1, 5, 7} : Set ℕ) → ∀ n : ℕ, 0 < n →
    ∃ p q r s : ℕ, OneOrOddPrime p ∧ OneOrOddPrime q ∧ OneOrOddPrime r ∧
      OneOrOddPrime s ∧
      n = c * ((p - 1) / 2) ^ 4 + (q - 1) ^ 2 / 2 + (r - 1) ^ 2 / 4 + (s + 1) ^ 2 / 4 := by
  sorry

end OMA.S_oeis_a391037
