import Mathlib

/-!
# A091443: Multiperfect numbers n which are divisible by sopfr(n) (multiperfect number: sigma(n) = k*n with k integer, sopfr: Sum of prime factors with repetition).

Source: https://oeis.org/A091443
Credit: @luciusacarr

The entry records one conjecture: the sequence is finite. Its terms begin 1379454720 =
2^8 * 3 * 5 * 7 * 19 * 37 * 73 (sopfr = 160 = 2^5 * 5), 14182439040, ...

Reading of the source:
* `n ≥ 1` is multiperfect if `sigma(n) = k * n` for an integer `k`, i.e. `n ∣ sigma(n)`.
* `sopfr(n)` is the sum of the prime factors of `n` with repetition,
  `(Nat.primeFactorsList n).sum`; the condition is `sopfr(n) ∣ n`.
* The source mentions "the trivial case 1" separately; `1` is not a listed term. Here it is
  excluded automatically (`sopfr(1) = 0` does not divide `1`); a single number does not affect
  finiteness anyway.
-/

namespace OMA.S_oeis_a091443

/-- The sum of the prime factors of `n` with repetition (A001414). -/
def sopfr (n : ℕ) : ℕ := (Nat.primeFactorsList n).sum

theorem main :
    {n : ℕ | 1 ≤ n ∧ n ∣ ArithmeticFunction.sigma 1 n ∧ sopfr n ∣ n}.Finite := by
  sorry

end OMA.S_oeis_a091443
