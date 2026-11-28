import Mathlib

/-!
# A221018: Numbers k such that Fibonacci(k) is divisible by k, k + 1 and k - 1.

Source: https://oeis.org/A221018
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a221018

def IsTerm (k : ℕ) : Prop :=
  0 < k ∧ k ∣ Nat.fib k ∧ k + 1 ∣ Nat.fib k ∧ k - 1 ∣ Nat.fib k

theorem main : ∀ k : ℕ, IsTerm k → k % 10 = 0 ∨ k % 10 = 2 ∨ k % 10 = 8 := by
  sorry

end OMA.S_oeis_a221018
