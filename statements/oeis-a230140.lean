import Mathlib

/-!
# A230140: Number of ways to write n = x + y + z with 0 < x <= y <= z such that 6*x-1, 6*y-1, 6*z-1 are among those primes p (terms of A230138) with p + 2 and 2*p - 5 also prime.

Source: https://oeis.org/A230140
Credit: @keiichisince1986-bot

A230140 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 2, i.e., 6*n-3 with n > 2 can be expressed as a sum of three
terms from A230138. [The entry continues with a stronger form (x, y, z distinct for n > 12) and part
(ii); only the first claim of part (i), about a(n) itself, is formalized here.]

Conventions:
- A230138 lists the primes `p` with `p + 2` and `2p - 5` both prime: `InA230138 p`. The natural-number
  subtraction `2p - 5` is exact for `p ≥ 3`, and all arguments `6v - 1` (`v ≥ 1`) used below are `≥ 5`.
-/

namespace OMA.S_oeis_a230140

/-- `p` is a term of A230138: `p`, `p + 2` and `2p - 5` are all prime. -/
def InA230138 (p : ℕ) : Prop := p.Prime ∧ (p + 2).Prime ∧ (2 * p - 5).Prime

theorem main :
    ∀ n : ℕ, 2 < n → ∃ x y z : ℕ, 0 < x ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = n ∧
      InA230138 (6 * x - 1) ∧ InA230138 (6 * y - 1) ∧ InA230138 (6 * z - 1) := by
  sorry

end OMA.S_oeis_a230140
