import Mathlib

/-!
# A277273: Numbers k such that sigma(k) = sigma(k - d(k))

Source: https://oeis.org/A277273
Credit: @xor2k

The entry text is a remark, not a conjecture: If p, p+2, 3p+2 and 3p+8 are primes, then
(p+2)*(3p+2) is in the sequence. Dickson's conjecture implies that there are infinitely many such p.
Terms of this form include 55, 119, 1007, 118007, 6120407, 8350007, 13083407, 51875207.

Formalized claims (the two precise claims the remark makes on its own):
1. if `p, p+2, 3p+2, 3p+8` are all prime, then `(p+2)*(3p+2)` is in A277273;
2. each of the eight listed numbers is a term of A277273 of this form.
The sentence about Dickson's conjecture (infinitely many such `p`) is NOT formalized.
The other comment of the entry (if a(n) is odd then 2*a(n) is a term) is not part of this remark.

Conventions:
* `sigma` is `ArithmeticFunction.sigma 1` (A000203), `d(k)` is `k.divisors.card` (A000005).
* Terms are positive integers (offset 1, first term 55), so membership requires `0 < k`; this
  excludes the spurious solution `k = 0` of the bare equation. Natural subtraction `k - d(k)` is
  exact since `d(k) ≤ k`.
-/

namespace OMA.S_oeis_a277273

/-- Membership in A277273: `k > 0` and `sigma(k) = sigma(k - d(k))`. -/
def InSeq (k : ℕ) : Prop :=
  0 < k ∧ ArithmeticFunction.sigma 1 k = ArithmeticFunction.sigma 1 (k - k.divisors.card)

/-- `p, p+2, 3p+2, 3p+8` are all prime. -/
def Good (p : ℕ) : Prop :=
  p.Prime ∧ (p + 2).Prime ∧ (3 * p + 2).Prime ∧ (3 * p + 8).Prime

/-- If `p, p+2, 3p+2, 3p+8` are prime then `(p+2)(3p+2)` is a term, and the eight listed numbers
are terms of this form. -/
theorem main :
    (∀ p : ℕ, Good p → InSeq ((p + 2) * (3 * p + 2))) ∧
    (∀ k ∈ [55, 119, 1007, 118007, 6120407, 8350007, 13083407, 51875207],
      InSeq k ∧ ∃ p : ℕ, Good p ∧ k = (p + 2) * (3 * p + 2)) := by
  sorry

end OMA.S_oeis_a277273
