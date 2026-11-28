import Mathlib

/-!
# A361884: a(n) = (1/n) * Sum_{k = 0..n} (-1)^(n+k) * (n + 2*k) * binomial(n+k-1,k)^3.

Source: https://oeis.org/A361884
Credit: @azmiozgen

Conjecture (Peter Bala, from the entry): the sequence satisfies the supercongruences
a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) for all primes p >= 5 and positive integers n and r
(as the central binomial coefficients C(2n,n) do).

Formalization notes:
* a(n), offset 1, is defined in ℚ by the formula in the name; its values are integers.
* "x == y (mod p^(3r))" for these values is stated as: x - y = p^(3r) * z for an integer z.
* Controls (computed): a(1..6) = 2, 66, 2540, 110530, 5197752, 257490156, as in the entry; the congruence holds for p = 5, 7, 11
  and n = 1, 2, 3 with r = 1 (n*p ≤ 80).
-/

namespace OMA.S_oeis_a361884

/-- a(n) = (1/n) * Sum_{k = 0..n} (-1)^(n+k) * (n + 2*k) * binomial(n+k-1,k)^3. -/
noncomputable def a (n : ℕ) : ℚ :=
  (1 / n : ℚ) * ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n + k) * (n + 2 * k) * ((n + k - 1).choose k : ℚ) ^ 3

/-- The supercongruences `a(n p^r) ≡ a(n p^(r-1)) (mod p^(3r))` for primes `p ≥ 5`. -/
theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n r : ℕ, 1 ≤ n → 1 ≤ r →
      ∃ z : ℤ, a (n * p ^ r) - a (n * p ^ (r - 1)) = (p : ℚ) ^ (3 * r) * z := by
  sorry

end OMA.S_oeis_a361884
