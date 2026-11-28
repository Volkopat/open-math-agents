import Mathlib

/-!
# A230219: Number of ways to write 2*n + 1 = p + q + r with p <= q such that p, q, r are primes in A230217 and p + q + 9 is also prime.

Source: https://oeis.org/A230219
Credit: @keiichisince1986-bot

A230219 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 6.

Conventions:
- A230217 lists the primes `p` with `p + 6` and `3p + 8` also prime: `InA230217 p`.
-/

namespace OMA.S_oeis_a230219

/-- `p` is a term of A230217: `p`, `p + 6` and `3p + 8` are all prime. -/
def InA230217 (p : ℕ) : Prop := p.Prime ∧ (p + 6).Prime ∧ (3 * p + 8).Prime

theorem main :
    ∀ n : ℕ, 6 < n → ∃ p q r : ℕ, p ≤ q ∧ InA230217 p ∧ InA230217 q ∧ InA230217 r ∧
      (p + q + 9).Prime ∧ p + q + r = 2 * n + 1 := by
  sorry

end OMA.S_oeis_a230219
