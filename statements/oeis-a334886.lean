import Mathlib

/-!
# A334886: Numerator of 2*Sum_{k=0..n} binomial(n,k)^2*binomial(n+k,k)^2*(H(n+k)-H(n-k)) where H(n)=Sum_{k=1..n} 1/k

Source: https://oeis.org/A334886

`a(n)` is the numerator, in lowest terms, of the rational number
`2 * Sum_{k=0..n} binomial(n,k)^2 * binomial(n+k,k)^2 * (H(n+k) - H(n-k))`,
where `H(n) = Sum_{k=1..n} 1/k` is the harmonic number. Offset 0; keyword `nonn,frac`.
First terms: 0, 12, 210, 4438, 104825, 13276637, 70543291, 67890874657, ...
(the denominators are A334887).

Conjecture (Peter Bala, Oct 23 2022, comment in the entry):
`a(p-1) == 0 (mod p^2)` for all primes `p >= 5` (checked by him up to `p = 499`).
This is the only conjectural claim of the entry, and the entry does not say that it has been proved.

Formalized:
* the sum is taken in `ℚ` over `k ∈ Finset.range (n + 1)`, i.e. `k = 0..n`; the binomial coefficients
  are `Nat.choose` cast to `ℚ`, and `H` is Mathlib's `harmonic : ℕ → ℚ`
  (`harmonic n = ∑ i ∈ Finset.range n, 1/(i+1)`, so `harmonic 0 = 0`);
* `n - k` is a natural-number subtraction, exact because `k ≤ n` on the range of summation;
* the numerator is `Rat.num` (numerator of the reduced fraction with positive denominator, as in
  Maple's `numer`, PARI's `numerator`), so `a n : ℤ`;
* the congruence `a(p-1) == 0 (mod p^2)` is written as divisibility `(p : ℤ)^2 ∣ a (p - 1)`;
  `p - 1` is a natural-number subtraction, exact because `p ≥ 5`;
* the range is exactly the stated one, all primes `p ≥ 5` (the claim is false for `p = 3`:
  `a(2) = 210` is not divisible by 9).
-/

namespace OMA.S_oeis_a334886

/-- A334886: numerator of `2 * Sum_{k=0..n} C(n,k)^2 * C(n+k,k)^2 * (H(n+k) - H(n-k))`. -/
def a (n : ℕ) : ℤ :=
  (2 * ∑ k ∈ Finset.range (n + 1),
    ((n.choose k : ℚ) ^ 2 * ((n + k).choose k : ℚ) ^ 2 * (harmonic (n + k) - harmonic (n - k)))).num

/-- Bala's conjecture: `a(p-1) == 0 (mod p^2)` for all primes `p >= 5`. -/
theorem main : ∀ p : ℕ, p.Prime → 5 ≤ p → ((p : ℤ) ^ 2) ∣ a (p - 1) := by
  sorry

end OMA.S_oeis_a334886
