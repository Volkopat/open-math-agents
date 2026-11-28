import Mathlib

/-!
# A280681: Numbers k such that Fibonacci(k) is a totient.

Source: https://oeis.org/A280681
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a280681

def IsTotient (n : ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ Nat.totient m = n

def IsTerm (k : ℕ) : Prop :=
  IsTotient (Nat.fib k)

theorem main : Set.Infinite {k : ℕ | IsTerm k} := by
  sorry

end OMA.S_oeis_a280681
