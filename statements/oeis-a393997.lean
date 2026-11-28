import Mathlib

/-!
# A393997: the 3x+1 process on n/(2n+1) always reaches a finite cycle

Source: https://oeis.org/A393997
Credit: @gblacher2

A393997, offset 0: number of steps to reach the end of the cycle starting with n/(2n+1),
or -1 if the end of the cycle is never reached, in the following process: if the numerator is
even, divide the fraction by 2, otherwise multiply the fraction by 3 and add 1.
Conjecture (in the entry): a finite cycle is always reached (checked for n <= 10^5).

Conventions:
* "the numerator" is the numerator of the fraction in lowest terms, Mathlib's `Rat.num`
  (this matches the entry's Mathematica and Python programs, which use reduced rationals).
* "a finite cycle is always reached" means that the trajectory of n/(2n+1) under `T` repeats a
  value: some iterates `T^[i] x` and `T^[j] x` with `i < j` are equal. Since `T` is a function,
  this is the same as the trajectory being eventually periodic, i.e. a(n) ≠ -1.
* n ranges over all n ≥ 0 (offset 0; a(0) = 0 since 0 -> 0).
-/

namespace OMA.S_oeis_a393997

/-- One step of the process: halve when the (reduced) numerator is even, else `3x + 1`. -/
def T (x : ℚ) : ℚ := if Even x.num then x / 2 else 3 * x + 1

/-- For every `n ≥ 0`, the trajectory of `n / (2n + 1)` under `T` reaches a finite cycle. -/
theorem main : ∀ n : ℕ, ∃ i j : ℕ, i < j ∧
    T^[i] ((n : ℚ) / (2 * n + 1)) = T^[j] ((n : ℚ) / (2 * n + 1)) := by
  sorry

end OMA.S_oeis_a393997
