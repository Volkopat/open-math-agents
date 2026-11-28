import Mathlib

/-!
# OEIS A009191

Source: https://oeis.org/A009191 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Ciphore

`a(n) = gcd(n, d(n))`, where `d(n)` is the number of divisors of `n`.  The
sequence entry conjectures that every positive integer occurs as a value.
-/

namespace OMA.S_oeis_a009191

/-- The greatest common divisor of `n` and its number of divisors. -/
def a (n : ℕ) : ℕ := Nat.gcd n n.divisors.card

theorem main : ∀ k : ℕ, 0 < k → ∃ n : ℕ, a n = k := by
  sorry

end OMA.S_oeis_a009191
