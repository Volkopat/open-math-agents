import Mathlib

/-!
# A262311: Number of ordered ways to write n = x^2 + y^2 + phi(z^2) (0 <= x <= y and z > 0) with y or z prime, where phi(.) is Euler's totient function given by A000010.

Source: https://oeis.org/A262311
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A262311 (Zhi-Wei Sun, Oct 01 2015): a(n) > 0 for all n > 1.

Conventions:
* The sequence has offset 1 (data 0, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, ...). `a n` is the number
  of triples (x, y, z) of natural numbers with 0 <= x <= y, z > 0,
  n = x^2 + y^2 + phi(z^2) and (y prime or z prime), exactly as in the OEIS name.
* phi is `Nat.totient`.
* The set of such triples is finite for every n (phi(z^2) = z*phi(z) >= z), so `Set.ncard` is
  its number of elements.
-/

namespace OMA.S_oeis_a262311

/-- A262311: number of triples (x, y, z) with x <= y, z > 0, x^2 + y^2 + phi(z^2) = n
and y or z prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℕ | x.1 ≤ x.2.1 ∧ 0 < x.2.2 ∧
    x.1 ^ 2 + x.2.1 ^ 2 + Nat.totient (x.2.2 ^ 2) = n ∧ (x.2.1.Prime ∨ x.2.2.Prime)}

/-- The conjecture of Sun: a(n) > 0 for all n > 1. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a262311
