import Mathlib

/-!
# A078615: a(n) = rad(n)^2, where rad is the squarefree kernel of n (A007947).

Source: https://oeis.org/A078615
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a078615

/-- The squarefree kernel (radical) of `n`: the product of its distinct prime factors (`rad 1 = 1`). -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- A078615: a(n) = rad(n)^2 (offset 1: 1, 4, 9, 4, 25, 36, 49, 4, 9, 100, ...). -/
def a (n : ℕ) : ℕ := rad n ^ 2

/-- Conjecture (A078615, cf. Broughan): only `k = 1` and `k = 1782` satisfy `a(k) = sigma(k)`, where
`sigma` is the sum of divisors (`ArithmeticFunction.sigma 1`). -/
theorem main : ∀ k : ℕ, 0 < k → (a k = ArithmeticFunction.sigma 1 k ↔ (k = 1 ∨ k = 1782)) := by
  sorry

end OMA.S_oeis_a078615
