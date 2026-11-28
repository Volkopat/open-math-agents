import Mathlib

/-!
# A375178: a(n) = Sum_{k = 0..n-1} binomial(n+k-1, k)^3 (same as A112028 with an extra 0 at the start).

Source: https://oeis.org/A375178
Credit: @azmiozgen

Conjectures (Peter Bala): a(p) == 1 (mod p^5) for all primes p >= 7; and for r >= 2 and prime
p >= 5, a(p^r) == a(p^(r-1)) (mod p^(3*r+3)). (The entry also states a more general conjecture
for exponents 2m+1; only the case of this sequence is stated here.)

Formalization notes:
* a(n) is the sum in the name (offset 0), computed in ℤ.
* Both congruences are stated in ℤ as divisibility of the differences.
* Controls (computed): a(0..4) = 0, 1, 9, 244, 9065, as in the entry; a(p) ≡ 1 (mod p^5) for
  p = 7, 11, 13, 17, 19, and a(p^2) ≡ a(p) (mod p^9) for p = 5, 7.
-/

namespace OMA.S_oeis_a375178

/-- A375178(n) = ∑_{k=0}^{n-1} C(n+k-1,k)^3. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range n, (((n + k - 1).choose k) ^ 3 : ℕ)

/-- Both conjectures for this sequence. -/
theorem main :
    (∀ p : ℕ, p.Prime → 7 ≤ p → (p : ℤ) ^ 5 ∣ a p - 1) ∧
      ∀ p r : ℕ, p.Prime → 5 ≤ p → 2 ≤ r → (p : ℤ) ^ (3 * r + 3) ∣ a (p ^ r) - a (p ^ (r - 1)) := by
  sorry

end OMA.S_oeis_a375178
