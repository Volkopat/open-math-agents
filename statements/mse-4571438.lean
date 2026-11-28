import Mathlib

/-!
# Coman's last conjecture

Source: https://math.stackexchange.com/questions/4571438
(M. Coman, *Conjectures on Primes and Fermat Pseudoprimes, many based on Smarandache function*,
Part Two, Section 14, p. 81).
Credit: @prasledi

The conjecture as stated in the post: let `p₁, p₂` range over the odd primes (`ℙ - {2}`).
If `q` is a prime other than `2, 3, 5, 7`, then `q = 3 * (p₁ - 1) + p₂` for some such `p₁, p₂`.

Formalization notes:
* `p₁` and `p₂` are primes different from `2`, as in the source (`p₁, p₂ ∈ ℙ - {2}`).
* Since `p₁ ≥ 3`, the natural-number subtraction `p₁ - 1` is the usual one.
* `p₁` and `p₂` need not be distinct.
-/

namespace OMA.S_mse_4571438

/-- Every prime `q` other than `2, 3, 5, 7` is `3 * (p₁ - 1) + p₂` for odd primes `p₁, p₂`. -/
theorem main :
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 → q ≠ 5 → q ≠ 7 →
      ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₁ ≠ 2 ∧ p₂.Prime ∧ p₂ ≠ 2 ∧ q = 3 * (p₁ - 1) + p₂ := by
  sorry

end OMA.S_mse_4571438
