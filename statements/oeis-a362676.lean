import Mathlib

/-!
# A362676: a(n) = Sum_{k = 0..n} 4^(n-k)*binomial(n,k)*binomial(n-1,k)*binomial(2*k,k).

Source: https://oeis.org/A362676
Credit: @azmiozgen

Conjecture (Peter Bala, from the entry): the sequence satisfies the supercongruences
a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) for all primes p >= 5 and positive integers n and r
(as the Franel numbers do).

Formalization notes:
* a(n) is the sum in the name (offset 0), computed in ℤ. In `n + k - 1` and `n - 1` the
  subtraction is in ℕ; it only matters at n = 0, where it gives the entry's a(0) = 1.
* The congruence is stated in ℤ as divisibility of the difference by p^(3r).
* Controls (computed): a(0..5) = 1, 4, 32, 328, 3840, 48504, as in the entry; the congruence holds for
  p = 5, 7, 11 and n = 1, 2, 3 with r = 1 (n*p ≤ 80).
-/

namespace OMA.S_oeis_a362676

/-- a(n) = Sum_{k = 0..n} 4^(n-k)*binomial(n,k)*binomial(n-1,k)*binomial(2*k,k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (4 ^ (n - k) * n.choose k * (n - 1).choose k * (2 * k).choose k : ℕ)

/-- The supercongruences `a(n p^r) ≡ a(n p^(r-1)) (mod p^(3r))` for primes `p ≥ 5`. -/
theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n r : ℕ, 1 ≤ n → 1 ≤ r →
      ((p : ℤ) ^ (3 * r) ∣ a (n * p ^ r) - a (n * p ^ (r - 1))) := by
  sorry

end OMA.S_oeis_a362676
