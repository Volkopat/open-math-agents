import Mathlib

/-!
# A114888: Multiperfect numbers, sigma(n) = k*n, which are divisible by their sums of prime factors with and without repetition.

Source: https://oeis.org/A114888
Credit: @luciusacarr

The entry records one conjecture: the sequence is finite. Its terms begin 1379454720 =
2^8 * 3 * 5 * 7 * 19 * 37 * 73, with sum of prime factors with repetition 160 = 2^5 * 5 and without
repetition 146 = 2 * 73, both dividing it.

Reading of the source:
* `n ≥ 1` is multiperfect if `sigma(n) = k * n` for an integer `k`, i.e. `n ∣ sigma(n)`.
* The sum of prime factors with repetition is `sopfr(n) = (Nat.primeFactorsList n).sum`
  (A001414); without repetition it is `sopf(n) = ∑ p ∈ n.primeFactors, p` (A008472). Both must
  divide `n`.
* `1` is excluded automatically (`sopfr(1) = 0` does not divide `1`).
-/

namespace OMA.S_oeis_a114888

/-- The sum of the prime factors of `n` with repetition (A001414). -/
def sopfr (n : ℕ) : ℕ := (Nat.primeFactorsList n).sum

/-- The sum of the distinct prime factors of `n` (A008472). -/
def sopf (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, p

theorem main :
    {n : ℕ | 1 ≤ n ∧ n ∣ ArithmeticFunction.sigma 1 n ∧ sopfr n ∣ n ∧ sopf n ∣ n}.Finite := by
  sorry

end OMA.S_oeis_a114888
