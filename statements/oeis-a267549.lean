import Mathlib

/-!
# A267549: Primes prime(k) such that floor( (prime(k)/k)^2 ) <= prime(k+1) - prime(k).

Source: https://oeis.org/A267549
Credit: @azmiozgen

Conjecture (from the entry): the list 3, 5, 7, 13, 23, 113 is complete.

Formalization notes:
* prime(k) = `Nat.nth Nat.Prime (k - 1)` (prime(1) = 2); floor((prime(k)/k)^2) is the natural
  division prime(k)^2 / k^2.
* Stated as equality of the set of terms (over k ≥ 1) with {3, 5, 7, 13, 23, 113}.
* Controls (computed): for k < 15000 the terms are exactly 3, 5, 7, 13, 23, 113.
-/

namespace OMA.S_oeis_a267549

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The list is complete. -/
theorem main :
    {q : ℕ | ∃ k : ℕ, 1 ≤ k ∧ q = prime k ∧ prime k ^ 2 / k ^ 2 ≤ prime (k + 1) - prime k} =
      ({3, 5, 7, 13, 23, 113} : Set ℕ) := by
  sorry

end OMA.S_oeis_a267549
