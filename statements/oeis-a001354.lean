import Mathlib

/-!
# A001354: Fibonacci numbers interlaced from the 3⁷ tessellation

Source: https://oeis.org/A001354 (Avi Friedlich's conjecture).
Credit: @eulogica

The ordinary generating function at the source gives the three initial values
and the recurrence below. Its reference to A001906 identifies the Fibonacci
indices as 2k and 2k+1. The quotients in the conjecture are exact.
-/

namespace OMA.S_oeis_a001354

/-- The coordination sequence A001354, indexed from zero. -/
def coordination : ℕ → ℕ
  | 0 => 1
  | 1 => 7
  | 2 => 21
  | n + 3 => 3 * coordination (n + 2) - coordination (n + 1)

theorem main :
    ∀ k : ℕ, 1 < k →
      coordination k = 7 * Nat.fib (2 * k) ∧
        coordination (k + 1) = coordination k + 7 * Nat.fib (2 * k + 1) := by
  sorry

end OMA.S_oeis_a001354
