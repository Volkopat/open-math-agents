import Mathlib

/-!
# A276464: Fibbinary Fibonacci numbers.

Source: https://oeis.org/A276464
Credit: @azmiozgen

Conjecture (Altug Alkan, Jul 07 2020): 75025 is the last term of this sequence.

Formalization notes:
* A fibbinary number has no two adjacent 1's in binary, i.e. n AND 2n = 0 (`n &&& (2 * n) = 0`).
* Stated as equality of the set of fibbinary Fibonacci numbers with the ten listed values.
* Controls (computed): among F(k), k < 1500, the fibbinary ones are 0, 1, 2, 5, 8, 21, 34, 144, 4181,
  75025, as in the entry.
-/

namespace OMA.S_oeis_a276464



/-- The conjecture of the entry. -/
theorem main :
    {m : ℕ | (∃ k : ℕ, Nat.fib k = m) ∧ m &&& (2 * m) = 0} =
      ({0, 1, 2, 5, 8, 21, 34, 144, 4181, 75025} : Set ℕ) := by
  sorry

end OMA.S_oeis_a276464
