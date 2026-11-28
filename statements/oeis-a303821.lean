import Mathlib

/-!
# A303821: Number of ways to write 2*n as p + 2^x + 5^y, where p is a prime, and x and y are nonnegative integers.

Source: https://oeis.org/A303821
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A303821 (Zhi-Wei Sun, May 01 2018): a(n) > 0 for all n > 1.

Conventions:
* The sequence has offset 1 (data 0, 1, 1, 3, 3, 4, 4, 5, 3, 6, 5, 5, ...). `a n` is the number
  of triples (p, x, y) of natural numbers with p prime and p + 2^x + 5^y = 2*n; x and y range
  over all nonnegative integers (a(2) = 1 comes from 4 = 2 + 2^0 + 5^0).
* The set of such triples is finite for every n, so `Set.ncard` is its number of elements.
* Only the first sentence of the conjecture is formalized; the refinement for n > 4 with p odd
  and x, y positive is a separate claim.
-/

namespace OMA.S_oeis_a303821

/-- A303821: number of triples (p, x, y) with p prime and p + 2^x + 5^y = 2n. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℕ | x.1.Prime ∧ x.1 + 2 ^ x.2.1 + 5 ^ x.2.2 = 2 * n}

/-- The conjecture of Sun: a(n) > 0 for all n > 1. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a303821
