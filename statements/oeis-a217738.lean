import Mathlib

/-!
# A217738: Numbers k such that Fibonacci(k) is divisible by k*(k+1).

Source: https://oeis.org/A217738
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a217738

def IsTerm (k : ℕ) : Prop :=
  0 < k ∧ k * (k + 1) ∣ Nat.fib k

theorem main : Set.Infinite {k : ℕ | IsTerm k} ∧ ∀ k : ℕ, IsTerm k → 12 ∣ k := by
  sorry

end OMA.S_oeis_a217738
