import Mathlib

/-!
# A365028: a(n) = Sum_{k = 0..n} (-1)^(n+k) * binomial(n,k)*binomial(n+k-1,n)* binomial(3*n+k-1,n).

Source: https://oeis.org/A365028
Credit: @azmiozgen

Conjecture (Peter Bala, from the entry): the sequence satisfies the same supercongruences as the
central binomial coefficients, a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) for all primes p >= 5 and
all positive integers n and r. (The entry's more general conjectures and the identity it states
for general x are not stated here.)

Formalization notes:
* a(n) is the sum in the name (offset 0), computed in ℤ; the subtractions inside the binomials are
  in ℕ and only matter at n = 0, where they give a(0) = 1 as in the entry.
* The congruence is stated in ℤ as divisibility of the difference by p^(3r).
* Controls (computed): a(0..7) = 1, 3, 33, 462, 7185, 118503, 2029650, 35690868, as in the entry;
  the congruence holds for p = 5, 7 and n = 1, 2, 3 with r = 1.
-/

namespace OMA.S_oeis_a365028

/-- A365028(n). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ (n + k) * (n.choose k * (n + k - 1).choose n * (3 * n + k - 1).choose n : ℕ)

/-- The supercongruences `a(n p^r) ≡ a(n p^(r-1)) (mod p^(3r))` for primes `p ≥ 5`. -/
theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n r : ℕ, 1 ≤ n → 1 ≤ r →
      ((p : ℤ) ^ (3 * r) ∣ a (n * p ^ r) - a (n * p ^ (r - 1))) := by
  sorry

end OMA.S_oeis_a365028
