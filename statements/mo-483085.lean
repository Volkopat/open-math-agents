import Mathlib

/-!
# Euler quotients of `W(n) = (2^n + 1)/3`

Source: https://mathoverflow.net/questions/483085
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjectures (MathOverflow): for odd `n` let `a(n) = ((2^{φ(n)} - 1) mod n²)/n` (the Euler
quotient) and `W(n) = (2^n + 1)/3`. Conjecture 1: `a(W(n))` is odd for all odd `n > 1`.
Conjecture 2: `a(W(n)) ≠ 0` for all odd `n > 1`.

Conventions:
* `main` states both conjectures (the first implies the second).
-/

namespace OMA.S_mo_483085

/-- The Euler quotient `((2^{φ(n)} - 1) mod n²)/n`. -/
def a (n : ℕ) : ℕ := ((2 ^ n.totient - 1) % n ^ 2) / n

/-- `W(n) = (2^n + 1)/3`. -/
def W (n : ℕ) : ℕ := (2 ^ n + 1) / 3

theorem main :
    (∀ n : ℕ, Odd n → 1 < n → a (W n) % 2 = 1) ∧ (∀ n : ℕ, Odd n → 1 < n → a (W n) ≠ 0) := by
  sorry

end OMA.S_mo_483085
