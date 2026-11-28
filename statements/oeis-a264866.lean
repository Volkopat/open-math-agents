import Mathlib

/-!
# A264866: Primes of the form 2^x + y (x >= 0 and 0 <= y < 2^x) such that all the numbers 2^(x+a) + (y-a) (0 < a <= y) are composite.

Source: https://oeis.org/A264866
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A264866 (Zhi-Wei Sun, Nov 26 2015): The sequence has
infinitely many terms.

Conventions:
* The sequence has offset 1 (data 2, 3, 5, 11, 13, 17, 19, 23, 41, 71, 131, 149, ...).
* Every positive integer has a unique representation 2^x + y with x >= 0 and 0 <= y < 2^x. For 0 <
  a <= y the number 2^(x+a) + (y-a) is at least 4, so `composite` is `not prime`; the subtraction
  y - a is exact.
* `The sequence is infinite` / `has infinitely many terms` is rendered as `Set.Infinite` of the
  set of all numbers with the defining property of the OEIS name.
-/

namespace OMA.S_oeis_a264866

/-- The conjecture recorded in A264866. -/
theorem main : Set.Infinite {p : ℕ | p.Prime ∧ ∃ x y : ℕ, p = 2 ^ x + y ∧ y < 2 ^ x ∧
    ∀ a : ℕ, 0 < a → a ≤ y → ¬ (2 ^ (x + a) + (y - a)).Prime} := by
  sorry

end OMA.S_oeis_a264866
