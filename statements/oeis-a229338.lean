import Mathlib

/-!
# A229338: Product of products of elements of subsets of divisors of n

Source: https://oeis.org/A229338
Credit: @jagong-cmu

Formalizes the OEIS A229338 conjecture (offset 1):
`a(n) = n^s(n)`, where `s(n) = A057711(tau(n)) = tau(n)*2^(tau(n)-2)`.

Conventions:
* The sequence is defined literally from the OEIS name: the product, over all subsets `S` of the
  set of divisors of `n` (the empty subset included), of the product of the elements of `S`.
  The empty product is `1`.
* `tau(n)` is `n.divisors.card`. The exponent `tau(n) * 2^(tau(n) - 2)` uses truncated
  subtraction on `ℕ`. For `n >= 2` we have `tau(n) >= 2`, so the subtraction is exact. For
  `n = 1` we have `tau(1) = 1`, and the truncated value `1 * 2^0 = 1` is `A057711(1) = 1`.
* The offset is 1, so the statement is for every `n >= 1`.
-/

namespace OMA.S_oeis_a229338

/-- The product, over all subsets of the divisors of `n`, of the product of the elements. -/
def a (n : ℕ) : ℕ := ∏ s ∈ n.divisors.powerset, ∏ d ∈ s, d

/-- For every `n >= 1`: `a(n) = n^(tau(n) * 2^(tau(n)-2))`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = n ^ (n.divisors.card * 2 ^ (n.divisors.card - 2)) := by
  sorry

end OMA.S_oeis_a229338
