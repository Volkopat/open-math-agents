import Mathlib

/-!
# A341763: Numbers whose trajectory under iteration of sum of cubes of digits (map) produce a
narcissistic number greater than nine.

Source: https://oeis.org/A341763
Credit: @Squee451

Data (offset 1): 2, 3, 5, 6, 7, 8, 9, 11, 12, 14, 15, 17, 18, 19, 20, 21, 23, 24, 26, 27, 29, 30, ...

The entry's comment: Conjecture: all multiples of 3 are terms of this sequence.

Conventions.
* The terms are positive integers, so "multiples of 3" means positive multiples of 3 (0 is a fixed
  point of the map and never leaves 0).
* A narcissistic number is a number equal to the sum of its decimal digits, each raised to the power
  of the number of digits (for example 153 = 1^3 + 5^3 + 3^3).
* "The trajectory produces" is read as: some iterate of the map, counting the starting number itself
  as the 0-th iterate, is a narcissistic number greater than nine.
-/

namespace OMA.S_oeis_a341763

/-- The map: sum of the cubes of the decimal digits. -/
def step (n : ℕ) : ℕ := ((Nat.digits 10 n).map fun d => d ^ 3).sum

/-- `n` equals the sum of its decimal digits, each raised to the number of digits of `n`. -/
def Narcissistic (n : ℕ) : Prop :=
  ((Nat.digits 10 n).map fun d => d ^ (Nat.digits 10 n).length).sum = n

/-- Every positive multiple of 3 reaches a narcissistic number greater than nine. -/
theorem main : ∀ n : ℕ, 0 < n → 3 ∣ n →
    ∃ t : ℕ, 9 < step^[t] n ∧ Narcissistic (step^[t] n) := by
  sorry

end OMA.S_oeis_a341763
