import Mathlib

/-!
# Infinitely many consecutive primes with no common digit?

Source: https://math.stackexchange.com/questions/4649148
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question: are there infinitely many pairs of consecutive primes whose decimal representations have
no digit in common (e.g. `59, 61` and `99999989, 100000007`)? `main` states the answer yes.

Conventions:
* Consecutive primes are `nth Prime i` and `nth Prime (i + 1)`; digits are `Nat.digits 10`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mse_4649148

/-- Infinitely many indices `i` such that the `i`-th and `(i+1)`-st primes share no digit. -/
theorem main : {i : ℕ | Disjoint (Nat.digits 10 (Nat.nth Nat.Prime i)).toFinset
    (Nat.digits 10 (Nat.nth Nat.Prime (i + 1))).toFinset}.Infinite := by
  sorry

end OMA.S_mse_4649148
