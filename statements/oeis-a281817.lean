import Mathlib

/-!
# A281817: a(n) = 2*Sum_{k odd} k!*Stirling2(n,k)/(k + 1).

Source: https://oeis.org/A281817

Definition: a(n) = 2 * Sum_{k odd} k! * Stirling2(n,k) / (k + 1), offset 0
(0, 1, 1, 4, 19, 116, 871, ...).

Claims (Peter Bala, Jan 2017):
1. (comment) a(2*n) - 1 = integer * the denominator of Bernoulli(2*n - 2)
   = integer * (Product_{p prime, p - 1 | 2*n - 2} p), checked up to n = 200.
2. (formula) Conjecture: for prime p, a(2*p) = 1 (mod p).
The formula line also says a(p) = 1 (mod p) for prime p; it is presented as a fact,
not as a conjecture, and is not part of the target. The comment about the companion
sequence b(n) is not part of the quoted target either.

Formalized:
- `a n` is a rational number; the sum runs over odd k with 1 <= k <= n
  (Stirling2(n,k) = 0 for k > n), using `Nat.stirlingSecond`.
- Claim 1 is stated for n >= 1 (Bernoulli(2n-2) needs 2n-2 >= 0). Since the product of the
  distinct primes p with p - 1 | 2n - 2 is squarefree, divisibility by it is equivalent to
  divisibility by each such prime. We state: for every prime p with (p - 1) | (2n - 2),
  a(2n) - 1 = p * m for some integer m. This also asserts that a(2n) is an integer.
  For n = 1 every prime qualifies and a(2) - 1 = 0, matching the denominator 1 of Bernoulli(0)
  after the identification with the product (the claim then just says a(2) = 1).
- Claim 2: for every prime p, a(2p) - 1 = p * m for some integer m.
-/

namespace OMA.S_oeis_a281817

/-- a(n) = 2 * Sum_{k odd, k <= n} k! * Stirling2(n,k) / (k + 1), as a rational. -/
def a (n : ℕ) : ℚ :=
  2 * ∑ k ∈ (Finset.range (n + 1)).filter Odd,
    ((k.factorial * Nat.stirlingSecond n k : ℕ) : ℚ) / ((k : ℚ) + 1)

theorem main :
    (∀ n : ℕ, 1 ≤ n → ∀ p : ℕ, p.Prime → (p - 1) ∣ (2 * n - 2) →
        ∃ m : ℤ, a (2 * n) - 1 = (p : ℚ) * m) ∧
    (∀ p : ℕ, p.Prime → ∃ m : ℤ, a (2 * p) - 1 = (p : ℚ) * m) := by
  sorry

end OMA.S_oeis_a281817
