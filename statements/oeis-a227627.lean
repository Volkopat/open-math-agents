import Mathlib

/-!
# A227627: Numbers k such that F(5*k)/(5*F(k)) is prime, where F(m) is the m-th Fibonacci number.

Source: https://oeis.org/A227627
Credit: @luciusacarr

The entry records one conjecture (Thomas Ordowski, Jul 18 2013): the sequence is infinite. Its
known terms are 2, 3, 5, 7, 13, 25, 29, 37, 47, 67, 457, 2309, ... (a(17) > 50000).

Reading of the source:
* `F(m) = Nat.fib m`. For `k ≥ 1`, `F(5k) / F(k) = 25 F(k)^4 ± 25 F(k)^2 + 5`, so `5 * F(k)`
  divides `F(5k)` and the natural-number division `F(5k) / (5 * F(k))` is exact.
* `k` ranges over the positive integers (offset 1).
-/

namespace OMA.S_oeis_a227627

theorem main :
    {k : ℕ | 1 ≤ k ∧ (Nat.fib (5 * k) / (5 * Nat.fib k)).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a227627
