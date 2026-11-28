import Mathlib

/-!
# A234309: a(n) = |{2 < k <= n/2: 2^{phi(k)} + 2^{phi(n-k)} - 1 is prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A234309
Credit: @luciusacarr

Data: 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 4, 4, 6, 5, 6, 5, 7, ... (offset 1).

The entry's comment (Zhi-Wei Sun) states a two-part conjecture. `main` states both parts, as a
conjunction, in the order the source gives them.

Conjecture: (i) a(n) > 0 for all n > 5.
(ii) For any integer n > 1, 2^k + 2^{phi(n-k)} - 1 is prime for some 0 < k < n, and
2^{sigma(j)} + 2^{phi(n-j)} - 1 is prime for some 0 < j < n, where sigma(j) is the sum of all
positive divisors of j.

Reading of the source:
* `phi` is `Nat.totient` and `sigma` is `ArithmeticFunction.sigma 1`.
* a(n) > 0 means some `k` with `2 < k ≤ n/2` (i.e. `2k ≤ n`) makes `2^phi(k) + 2^phi(n-k) - 1`
  prime. The first 25 data values were recomputed from this definition.
-/

namespace OMA.S_oeis_a234309

theorem main :
    -- (i) a(n) > 0 for all n > 5.
    (∀ n : ℕ, 5 < n → ∃ k : ℕ, 2 < k ∧ 2 * k ≤ n ∧
      (2 ^ Nat.totient k + 2 ^ Nat.totient (n - k) - 1).Prime) ∧
    -- (ii) for every n > 1, both representations exist.
    (∀ n : ℕ, 1 < n →
      (∃ k : ℕ, 0 < k ∧ k < n ∧ (2 ^ k + 2 ^ Nat.totient (n - k) - 1).Prime) ∧
      (∃ j : ℕ, 0 < j ∧ j < n ∧
        (2 ^ ArithmeticFunction.sigma 1 j + 2 ^ Nat.totient (n - j) - 1).Prime)) := by
  sorry

end OMA.S_oeis_a234309
