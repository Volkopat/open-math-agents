import Mathlib

/-!
# A361713: a(n) = Sum_{k = 0..n-1} binomial(n,k)^2 * binomial(n+k-1,k)^2.

Source: https://oeis.org/A361713
Credit: @azmiozgen

Conjecture 1 (Peter Bala): the supercongruence a(p) == a(1) (mod p^5) holds for all primes
p >= 7. The entry notes (Aug 12 2026) that Conjecture 1 is correct; Conjecture 2 of the entry
was disproved (Adamczewski) and is not stated here.

Formalization notes:
* a(n) is the sum in the name (offset 0), computed in ℤ; a(1) = 1.
* The congruence is stated in ℤ as divisibility of a(p) - a(1) by p^5.
* Controls (computed): a(0..4) = 0, 1, 17, 406, 10257, as in the entry; a(p) ≡ 1 (mod p^5) for
  p = 7, 11, 13, 17, 19.
-/

namespace OMA.S_oeis_a361713

/-- A361713(n) = ∑_{k=0}^{n-1} C(n,k)^2 C(n+k-1,k)^2. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range n, ((n.choose k) ^ 2 * ((n + k - 1).choose k) ^ 2 : ℕ)

/-- Conjecture 1: `a(p) ≡ a(1) (mod p^5)` for primes `p ≥ 7`. -/
theorem main :
    ∀ p : ℕ, p.Prime → 7 ≤ p → (p : ℤ) ^ 5 ∣ a p - a 1 := by
  sorry

end OMA.S_oeis_a361713
