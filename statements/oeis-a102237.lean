import Mathlib

/-!
# A102237: Smallest number equal to the product of n primes which is also equal to the sum of n distinct primes.

Source: https://oeis.org/A102237
Credit: @eltociear

`a(n)` (offset 1) is the least `m` that is a product of `n` primes (counted with multiplicity, so
`Ω(m) = n`) and also a sum of `n` distinct primes (`a(2) = 9 = 3·3 = 2 + 7`,
`a(3) = 12 = 2·2·3 = 2 + 3 + 7`). The entry records (Ray Chandler, Feb 25 2005):

  Conjecture: a(n) = 2^n for n>5.

`main` states that for every `n > 5`, `2^n` is the least element of this set. `Ω` is
`ArithmeticFunction.cardFactors`; a sum of `n` distinct primes is the sum of a set of `n` primes.
-/

namespace OMA.S_oeis_a102237

/-- `m` is a product of `n` primes and a sum of `n` distinct primes. -/
def Admissible (n m : ℕ) : Prop :=
  ArithmeticFunction.cardFactors m = n ∧
    ∃ S : Finset ℕ, S.card = n ∧ (∀ p ∈ S, p.Prime) ∧ ∑ p ∈ S, p = m

/-- The conjecture in OEIS A102237: `a(n) = 2^n` for `n > 5`. -/
theorem main : ∀ n : ℕ, 5 < n → IsLeast {m : ℕ | Admissible n m} (2 ^ n) := by
  sorry

end OMA.S_oeis_a102237
