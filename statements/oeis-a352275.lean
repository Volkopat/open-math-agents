import Mathlib

/-!
# A352275: a(0) = 1 and a(n) = Sum_{k = 0..2*n} n/(n + 2*k)*binomial(n + 2*k,k) for n >= 1.

Source: https://oeis.org/A352275
Credit: @azmiozgen

Conjecture (Peter Bala): the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for
primes p >= 5 and positive integers n and r.

Formalization notes:
* a(n) is defined in ℚ by the sum in the name (each summand n/(n+2k) * C(n+2k,k) is rational);
  the terms are integers.
* "x == y (mod p^(3r))" for these rational values is stated as: x - y = p^(3r) * z for some
  integer z.
* Controls (computed): a(0..4) = 1, 4, 64, 1429, 35072, as in the entry; the congruence holds
  for p = 5, 7, 11, n = 1, 2, 3 (r = 1, n*p ≤ 130).
-/

namespace OMA.S_oeis_a352275

/-- A352275(n), in ℚ. -/
noncomputable def a (n : ℕ) : ℚ :=
  if n = 0 then 1 else ∑ k ∈ Finset.range (2 * n + 1), (n : ℚ) / (n + 2 * k) * ((n + 2 * k).choose k : ℚ)

/-- The supercongruences `a(n p^r) ≡ a(n p^(r-1)) (mod p^(3r))` for primes `p ≥ 5`. -/
theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n r : ℕ, 1 ≤ n → 1 ≤ r →
      ∃ z : ℤ, a (n * p ^ r) - a (n * p ^ (r - 1)) = (p : ℚ) ^ (3 * r) * z := by
  sorry

end OMA.S_oeis_a352275
