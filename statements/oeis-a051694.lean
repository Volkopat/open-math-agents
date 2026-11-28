import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Defs

/-!
# Prime divisibility of the least positive Fibonacci multiple

OEIS A051694 lists the least positive Fibonacci number divisible by each prime,
starting with 2, 3, 5, 21 for the primes 2, 3, 5, 7. Michel Marcus records the
conjecture that the square of that prime never divides the listed value.

Source: https://oeis.org/A051694
Credit: @hiattco
-/

namespace OMA.S_oeis_a051694

def positiveFibonacciMultiples (p : ℕ) : Set ℕ :=
  {a | 0 < a ∧ p ∣ a ∧ ∃ k : ℕ, a = Nat.fib k}

theorem main : ∀ p : ℕ, p.Prime → ∃ a : ℕ,
    IsLeast (positiveFibonacciMultiples p) a ∧ ¬ p ^ 2 ∣ a := by
  sorry

end OMA.S_oeis_a051694
