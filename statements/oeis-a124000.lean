import Mathlib

/-!
# A124000: Semiprimes in A006987(n), or semiprime binomial coefficients: C(n,k), 2 <= k <= n-2.

Source: https://oeis.org/A124000
Credit: @azmiozgen

Conjectures (from the entry):
1. all a(n) except a(1) = 6 and a(2) = 10 are odd;
2. all a(n) except a(5) = 35 are triangular numbers of the form p*(2p ± 1) that belong to
   A068443 (triangular numbers with two distinct prime factors).

Formalization notes:
* The terms are the values C(n,k) with 2 ≤ k ≤ n - 2 that are semiprimes (products of exactly two
  primes, counted with multiplicity: `primeFactorsList.length = 2`).
* Conjecture 2 is stated as: every such value other than 35 equals p(2p + 1) or p(2p - 1) for a
  prime p (these are triangular numbers, T(2p) and T(2p-1), with two distinct prime factors).
* Controls (computed): the semiprime values C(n,k) ≤ 10^8 with 2 ≤ k ≤ n - 2 begin 6, 10, 15, 21, 35, 55, 91,
  253, 703, 1081, 1711, 1891, 2701, 3403, 5671, 12403, as in the entry; among them only 6 and 10
  are even, and every one other than 35 has the form p(2p ± 1).
-/

namespace OMA.S_oeis_a124000



/-- The conjecture of the entry. -/
theorem main :
    ∀ n k : ℕ, 2 ≤ k → k + 2 ≤ n → (n.choose k).primeFactorsList.length = 2 →
      (n.choose k ≠ 6 → n.choose k ≠ 10 → Odd (n.choose k)) ∧
      (n.choose k ≠ 35 → ∃ p : ℕ, p.Prime ∧
        (n.choose k = p * (2 * p + 1) ∨ n.choose k = p * (2 * p - 1))) := by
  sorry

end OMA.S_oeis_a124000
