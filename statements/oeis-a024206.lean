import Mathlib

/-!
# A024206: values of the form `p# - 1`

Source: https://oeis.org/A024206
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A024206): if `a(n) = p# - 1` for some prime `p`, then `q = n + 1` is also
prime, where `p# = ⌊q²/4⌋`.

Conventions:
* `a(n) = ⌊(n+1)²/4⌋ - 1` (A002620(n+1) - 1, offset 1, matching the listed terms
  `0, 1, 3, 5, 8, …`), so `a(n) = p# - 1` is the same as `⌊q²/4⌋ = p#` with `q = n + 1`.
* `p#` is the primorial, the product of the primes `≤ p` (Mathlib's `primorial`).
-/

namespace OMA.S_oeis_a024206

/-- A024206. -/
def a (n : ℕ) : ℕ := (n + 1) ^ 2 / 4 - 1

theorem main : ∀ n p : ℕ, 1 ≤ n → p.Prime → a n + 1 = primorial p → (n + 1).Prime := by
  sorry

end OMA.S_oeis_a024206
