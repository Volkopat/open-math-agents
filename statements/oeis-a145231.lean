import Mathlib

/-!
# A145231: a(n) = Fibonacci(4^n).

Source: https://oeis.org/A145231
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a145231

def a (n : ℕ) : ℕ :=
  Nat.fib (4 ^ n)

theorem main : ∀ n : ℕ, Squarefree (a n) := by
  sorry

end OMA.S_oeis_a145231
