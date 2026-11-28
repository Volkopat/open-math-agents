import Mathlib

/-!
# A357558: a supercongruence for Sum_k (-1)^(n+k) * k * C(n,k) * C(n+k,k)^2

Source: https://oeis.org/A357558

A357558 (offset 0): `a(n) = Sum_{k=0..n} (-1)^(n+k) * k * binomial(n,k) * binomial(n+k,k)^2`:
0, 4, 54, 648, 7500, 85440, 965202, …

Conjecture (Peter Bala, Oct 03 2022): `a(p-1) ≡ 0 (mod (p-1)*p^4)` for all primes `p ≥ 5`
(checked up to `p = 499`). For example
`a(16) = 28872014164369968 = 2^4 * 3 * 17^4 * 107 * 251 * 268153`.

Conventions:
- `a` is indexed as in the OEIS (offset 0) and is defined as an integer, since the summands
  alternate in sign.
- The congruence is stated as divisibility in `ℤ` by `(p-1)*p^4`; `p - 1` is an exact
  subtraction for a prime `p`.
-/

namespace OMA.S_oeis_a357558

/-- A357558: `a(n) = Sum_{k=0..n} (-1)^(n+k) * k * C(n,k) * C(n+k,k)^2`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ (n + k) * (k : ℤ) * (n.choose k : ℤ) * ((n + k).choose k : ℤ) ^ 2

theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → (((p - 1) * p ^ 4 : ℕ) : ℤ) ∣ a (p - 1) := by
  sorry

end OMA.S_oeis_a357558
