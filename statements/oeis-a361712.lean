import Mathlib

/-!
# A361712: a(n) = Sum_{k = 0..n-1} binomial(n,k)^2*binomial(n+k,k)*binomial(n+k-1,k).

Source: https://oeis.org/A361712
Credit: @azmiozgen

Conjectures (Peter Bala):
1. the supercongruence a(p) == a(1) (mod p^5) holds for all primes p >= 7;
2. for r >= 2, the supercongruence a(p^r) == a(p^(r-1)) (mod p^(3*r+3)) holds for all primes
   p >= 5.

Formalization notes:
* a(n) is the sum in the name (offset 0), computed in ℤ; a(1) = 1.
* Both congruences are stated in ℤ as divisibility of the differences.
* Controls (computed): a(0..4) = 0, 1, 25, 649, 16921, as in the entry; a(p) ≡ 1 (mod p^5) for p = 7, 11, 13,
  17, 19, and a(p^2) ≡ a(p) (mod p^9) for p = 5, 7.
-/

namespace OMA.S_oeis_a361712

/-- a(n) = Sum_{k = 0..n-1} binomial(n,k)^2*binomial(n+k,k)*binomial(n+k-1,k). -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range n, ((n.choose k) ^ 2 * (n + k).choose k * (n + k - 1).choose k : ℕ)

/-- Both conjectures of the entry. -/
theorem main :
    (∀ p : ℕ, p.Prime → 7 ≤ p → (p : ℤ) ^ 5 ∣ a p - a 1) ∧
      ∀ p r : ℕ, p.Prime → 5 ≤ p → 2 ≤ r → (p : ℤ) ^ (3 * r + 3) ∣ a (p ^ r) - a (p ^ (r - 1)) := by
  sorry

end OMA.S_oeis_a361712
