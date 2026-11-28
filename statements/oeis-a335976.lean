import Mathlib

/-!
# A335976: Numbers k such that Fibonacci(6*k) is not a totient.

Source: https://oeis.org/A335976
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a335976

def IsTotient (n : ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ Nat.totient m = n

def IsTerm (k : ℕ) : Prop :=
  ¬ IsTotient (Nat.fib (6 * k))

theorem main : Set.Infinite {k : ℕ | IsTerm k ∧ k.Prime} := by
  sorry

end OMA.S_oeis_a335976
