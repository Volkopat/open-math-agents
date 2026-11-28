import Mathlib

/-!
# A363983: a(n) = Sum_{k = floor((n+1)/2)..n} (-1)^(n+k)*binomial(n,k)*binomial(n+k-1,k)*binomial(2*k,n).

Source: https://oeis.org/A363983
Credit: @azmiozgen

Conjecture (Peter Bala, from the entry): the sequence satisfies the supercongruences
a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) for all primes p >= 5 and positive integers n and r
(as the Franel numbers do).

Formalization notes:
* a(n) is the sum in the name (offset 0), computed in ℤ. In `n + k - 1` and `n - 1` the
  subtraction is in ℕ; it only matters at n = 0, where it gives the entry's a(0) = 1.
* The congruence is stated in ℤ as divisibility of the difference by p^(3r).
* Controls (computed): a(0..5) = 1, 2, 14, 128, 1310, 14252, as in the entry; the congruence holds for
  p = 5, 7, 11 and n = 1, 2, 3 with r = 1 (n*p ≤ 80).
-/

namespace OMA.S_oeis_a363983

/-- a(n) = Sum_{k = floor((n+1)/2)..n} (-1)^(n+k)*binomial(n,k)*binomial(n+k-1,k)*binomial(2*k,n). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc ((n + 1) / 2) n,
    (-1 : ℤ) ^ (n + k) * (n.choose k * (n + k - 1).choose k * (2 * k).choose n : ℕ)

/-- The supercongruences `a(n p^r) ≡ a(n p^(r-1)) (mod p^(3r))` for primes `p ≥ 5`. -/
theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n r : ℕ, 1 ≤ n → 1 ≤ r →
      ((p : ℤ) ^ (3 * r) ∣ a (n * p ^ r) - a (n * p ^ (r - 1))) := by
  sorry

end OMA.S_oeis_a363983
