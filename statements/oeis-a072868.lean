import Mathlib

/-!
# A072868: Numbers k such that sigma(sigma(k) - k) = k.

Source: https://oeis.org/A072868
Credit: @azmiozgen

Conjecture (from the entry): a(n) = 1 + A000668(n), where A000668 lists the Mersenne primes
(which implies equivalent conjectures stated in A000668).

Formalization notes:
* Both sequences are increasing, so a(n) = 1 + A000668(n) for all n says that the terms are
  exactly the numbers 2^q with 2^q - 1 prime. Stated for every k ≥ 1:
  sigma(sigma(k) - k) = k iff k = 2^q for some q with 2^q - 1 prime.
* sigma(k) - k ≥ 0 for k ≥ 1; for k = 1 it is 0 and Mathlib's sigma(0) = 0 ≠ 1.
* Controls (computed): the k < 60000 with sigma(sigma(k) - k) = k are 4, 8, 32, 128, 8192, as in the entry
  (= 1 + 3, 1 + 7, 1 + 31, 1 + 127, 1 + 8191).
-/

namespace OMA.S_oeis_a072868

open ArithmeticFunction

/-- The conjecture of the entry. -/
theorem main :
    ∀ k : ℕ, 1 ≤ k → (sigma 1 (sigma 1 k - k) = k ↔ ∃ q : ℕ, (2 ^ q - 1).Prime ∧ k = 2 ^ q) := by
  sorry

end OMA.S_oeis_a072868
