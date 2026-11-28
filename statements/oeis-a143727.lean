import Mathlib

/-!
# A143727: Near-prime numbers.

Source: https://oeis.org/A143727
Credit: @bnb9001

The sequence lists the numbers `n` such that `n - 2`, `n + 2`, `n - 4`, `n + 4`, `n - 8` and
`n + 8` are all prime (15, 105, 16065, ...).

Conjecture (Harvey P. Dale): all terms are multiples of 15. David A. Corneth notes that the
conjecture is true. Natural-number subtraction is harmless here: `n - 8` prime forces `n ≥ 10`.
-/

namespace OMA.S_oeis_a143727

/-- `n - 2`, `n + 2`, `n - 4`, `n + 4`, `n - 8` and `n + 8` are all prime. -/
def IsNearPrime (n : ℕ) : Prop :=
  (n - 2).Prime ∧ (n + 2).Prime ∧ (n - 4).Prime ∧ (n + 4).Prime ∧ (n - 8).Prime ∧ (n + 8).Prime

/-- Every near-prime number is a multiple of 15. -/
theorem main : ∀ n : ℕ, IsNearPrime n → 15 ∣ n := by
  sorry

end OMA.S_oeis_a143727
