import Mathlib

/-!
# A214853: Fibonacci numbers with only one 0 in their binary representation

Source: https://oeis.org/A214853

Conjecture (OEIS A214853):
There are only finitely many Fibonacci numbers whose base-2 expansion contains
exactly one `0` digit.

Conventions:
- Offset: `1`; known terms: `0, 2, 5, 13, 55` (in binary: `0, 10, 101, 1101, 110111`).
- Since `Nat.digits 2 0 = []`, we define `binZeroCount 0 = 1` so that `0` is included
  faithfully alongside `2, 5, 13, 55`.
-/

namespace OMA.S_oeis_a214853

/-- Number of `0` bits in the standard binary representation of `m : ℕ`. -/
def binZeroCount (m : ℕ) : ℕ :=
  if m = 0 then 1 else (Nat.digits 2 m).count 0

/-- The set of Fibonacci numbers having exactly one `0` in base 2 (OEIS A214853). -/
def S : Set ℕ :=
  {m : ℕ | (∃ n : ℕ, m = Nat.fib n) ∧ binZeroCount m = 1}

/-- Conjecture: there are only finitely many Fibonacci numbers with a single `0` bit. -/
theorem main : Set.Finite S := by
  sorry

end OMA.S_oeis_a214853
