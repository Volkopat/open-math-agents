import Mathlib

/-!
# A262826: the 2-adic valuation of Hanna's divisor sum

Source: https://oeis.org/A262826
Credit: @ivillar

Paul D. Hanna's sequence a(n) = Sum_{d|n} -(-1)^d * 2^(n^2/d) * d (offset 1) is the logarithmic
derivative of A158096. The entry conjectures that a(n) = 2^A007814(n) * 2^n * d for some odd d,
where A007814(n) is the exponent of the highest power of 2 dividing n.

Formalization notes:
* a(n) is computed in ℤ; `n ^ 2 / d` is an exact division for every divisor `d` of `n`.
* A007814(n) is `padicValNat 2 n`.
-/

namespace OMA.S_oeis_a262826

/-- A262826: `a(n) = Sum_{d|n} -(-1)^d * 2^(n^2/d) * d`. -/
def a (n : ℕ) : ℤ := ∑ d ∈ n.divisors, -(-1 : ℤ) ^ d * 2 ^ (n ^ 2 / d) * d

/-- The conjecture in A262826: `a(n) = 2^A007814(n) * 2^n * d` with `d` odd, for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ d : ℤ, Odd d ∧ a n = 2 ^ padicValNat 2 n * 2 ^ n * d := by
  sorry

end OMA.S_oeis_a262826
