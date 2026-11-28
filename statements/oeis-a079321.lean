import Mathlib

/-!
# A079321: Composite numbers of the form 1^1 * 2^2 * 3^3 * 4^4 * ... * n^n + 1.

Source: https://oeis.org/A079321
Credit: @divmxnd0x

Conjecture (stated in A079321): there are no primes in the sequence `2^2 3^3 4^4 ... n^n + 1` for
`n > 3`. (The values for `n = 2, 3` are the primes `5` and `109`.)

Formalization notes:
* The product `1^1 2^2 ... n^n` is `∏_{k=1}^{n} k^k` (the factor `1^1` changes nothing).
-/

namespace OMA.S_oeis_a079321

/-- For `n > 3`, `1^1 2^2 ... n^n + 1` is not prime. -/
theorem main : ∀ n : ℕ, 3 < n → ¬ (∏ k ∈ Finset.Icc 1 n, k ^ k + 1).Prime := by
  sorry

end OMA.S_oeis_a079321
