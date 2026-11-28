import Mathlib

/-!
# Do any odd weird numbers exist?

Source: https://en.wikipedia.org/wiki/Weird_number
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: a **weird number** is a natural number that is abundant but not semiperfect, that is,
the sum of its proper divisors exceeds the number, yet the number is not the sum of any subset of
its proper divisors.  Every known weird number is even; the open question, from "List of unsolved
problems in mathematics", is whether any odd weird number exists.

So the proposition formalized below is: there is an odd natural number `n` whose proper divisors sum
to more than `n`, and which is not the sum of any set of its proper divisors.
-/

namespace OMA.S_wp_do_any_odd_weird_numbers_exist

-- definitions the statement needs (no sorry, no axiom)

/-- `n` is a **weird number**: `n` is abundant (its proper divisors sum to more than `n`) and not
semiperfect (no set of its proper divisors sums to `n`). -/
def IsWeird (n : ℕ) : Prop :=
  n < n.properDivisors.sum id ∧
    ¬ ∃ s : Finset ℕ, s ⊆ n.properDivisors ∧ s.sum id = n

/-- Do any odd weird numbers exist? -/
theorem main : ∃ n : ℕ, Odd n ∧ IsWeird n := by
  sorry

end OMA.S_wp_do_any_odd_weird_numbers_exist
