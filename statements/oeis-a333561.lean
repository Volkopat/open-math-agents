import Mathlib

/-!
# A333561: a(n) = Sum_{j = 0..2*n} binomial(n+j-1,j)*2^j.

Source: https://oeis.org/A333561
Credit: @azmiozgen

Conjecture (Peter Bala, from the entry): the sequence satisfies the supercongruences
a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) for all primes p >= 5 and positive integers n and r
(as the central binomial-type sums of the entry do).

Formalization notes:
* a(n) is the sum in the name (offset 0), computed in ℤ. In `n + k - 1` and `n - 1` the
  subtraction is in ℕ; it only matters at n = 0, where it gives the entry's a(0) = 1.
* The congruence is stated in ℤ as divisibility of the difference by p^(3r).
* Controls (computed): a(0..5) = 1, 7, 129, 2815, 65537, 1579007, as in the entry; the congruence holds for
  p = 5, 7, 11 and n = 1, 2, 3 with r = 1 (n*p ≤ 80).
-/

namespace OMA.S_oeis_a333561

/-- a(n) = Sum_{j = 0..2*n} binomial(n+j-1,j)*2^j. -/
def a (n : ℕ) : ℤ := ∑ j ∈ Finset.range (2 * n + 1), ((n + j - 1).choose j * 2 ^ j : ℕ)

/-- The supercongruences `a(n p^r) ≡ a(n p^(r-1)) (mod p^(3r))` for primes `p ≥ 5`. -/
theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n r : ℕ, 1 ≤ n → 1 ≤ r →
      ((p : ℤ) ^ (3 * r) ∣ a (n * p ^ r) - a (n * p ^ (r - 1))) := by
  sorry

end OMA.S_oeis_a333561
