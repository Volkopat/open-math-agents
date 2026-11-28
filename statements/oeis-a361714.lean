import Mathlib

/-!
# A361714: a(n) = Sum_{k = 0..n-1} (-1)^(n+k+1)*binomial(n,k)*binomial(n+k-1,k)^2.

Source: https://oeis.org/A361714
Credit: @azmiozgen

Conjectures (Peter Bala):
1. the supercongruence a(p) == a(1) (mod p^5) holds for all primes p >= 7;
2. for r >= 2, the supercongruence a(p^r) == a(p^(r-1)) (mod p^(3*r+3)) holds for all primes
   p >= 7.
The entry notes (Roberto Blanco Gómez, Oct 18 2026) that both conjectures are true.

Formalization notes:
* a(n) is the sum in the name (offset 0), computed in ℤ; a(1) = 1.
* Both congruences are stated in ℤ as divisibility of the differences.
* Controls (computed): a(0..4) = 0, 1, 7, 82, 1063, as in the entry; a(p) ≡ 1 (mod p^5) for p = 7, 11, 13,
  17, 19, and a(p^2) ≡ a(p) (mod p^9) for p = 5, 7.
-/

namespace OMA.S_oeis_a361714

/-- a(n) = Sum_{k = 0..n-1} (-1)^(n+k+1)*binomial(n,k)*binomial(n+k-1,k)^2. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range n, (-1 : ℤ) ^ (n + k + 1) * ((n.choose k) * ((n + k - 1).choose k) ^ 2 : ℕ)

/-- Both conjectures of the entry. -/
theorem main :
    (∀ p : ℕ, p.Prime → 7 ≤ p → (p : ℤ) ^ 5 ∣ a p - a 1) ∧
      ∀ p r : ℕ, p.Prime → 7 ≤ p → 2 ≤ r → (p : ℤ) ^ (3 * r + 3) ∣ a (p ^ r) - a (p ^ (r - 1)) := by
  sorry

end OMA.S_oeis_a361714
