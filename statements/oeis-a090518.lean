import Mathlib

/-!
# A090518: Primes arising in A090517, or 0 if A090517(n) = 0.

Source: https://oeis.org/A090518
Credit: @bnb9001

A090517(n) is the least `k` such that `⌊10 ^ n / k⌋` is prime (offset 1). We take it to be
`sInf` of that set, which is `0` exactly when no such `k` exists. A090518(n) is the prime
`⌊10 ^ n / A090517(n)⌋`, or `0` if A090517(n) = 0.

Conjecture: no term is zero. The entry notes that the conjecture is true.
-/

namespace OMA.S_oeis_a090518

/-- A090517: the least `k` such that `⌊10 ^ n / k⌋` is prime, or `0` if there is none. -/
noncomputable def b (n : ℕ) : ℕ := sInf {k : ℕ | (10 ^ n / k).Prime}

/-- A090518: the prime `⌊10 ^ n / b n⌋`, or `0` if `b n = 0`. -/
noncomputable def a (n : ℕ) : ℕ := if b n = 0 then 0 else 10 ^ n / b n

/-- For every `n ≥ 1`, `a n ≠ 0`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≠ 0 := by
  sorry

end OMA.S_oeis_a090518
