import Mathlib

/-!
# A230141: Number of ways to write n = x + y + z with y <= z such that 6*x-1, 6*y-1, 6*z-1 are terms of A230138 and 6*(y+z)+1 is prime.

Source: https://oeis.org/A230141
Credit: @keiichisince1986-bot

A230141 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 2. [The entry adds a similar claim with 6*y*z-1; it is not
formalized here.]

Conventions:
- A230138 lists the primes `p` with `p + 2` and `2p - 5` both prime: `InA230138 p`. The natural-number
  subtraction `2p - 5` is exact for `p ≥ 3`, and all arguments `6v - 1` (`v ≥ 1`) used below are `≥ 5`.
- `x`, `y`, `z` are positive integers (as in the Mathematica program).
-/

namespace OMA.S_oeis_a230141

/-- `p` is a term of A230138: `p`, `p + 2` and `2p - 5` are all prime. -/
def InA230138 (p : ℕ) : Prop := p.Prime ∧ (p + 2).Prime ∧ (2 * p - 5).Prime

theorem main :
    ∀ n : ℕ, 2 < n → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ y ≤ z ∧ x + y + z = n ∧
      InA230138 (6 * x - 1) ∧ InA230138 (6 * y - 1) ∧ InA230138 (6 * z - 1) ∧
      (6 * (y + z) + 1).Prime := by
  sorry

end OMA.S_oeis_a230141
