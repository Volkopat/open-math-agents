import Mathlib

/-!
# Infinitely many Fibonacci gaps between consecutive primes

Source: https://oeis.org/A396340 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

The conjecture asks for infinitely many consecutive prime pairs whose
difference is a Fibonacci number. The larger primes are strictly ordered.
-/

namespace OMA.S_oeis_a396340

theorem main : ∀ bound : ℕ, ∃ p q : ℕ,
    bound < q ∧ p.Prime ∧ q.Prime ∧ p < q ∧
    (¬ ∃ r : ℕ, r.Prime ∧ p < r ∧ r < q) ∧ (∃ k : ℕ, q - p = Nat.fib k) := by
  sorry

end OMA.S_oeis_a396340
