import Mathlib

/-!
# A079279: a(n)=n for n<=3; for n>3, a(n) is next integer sharing common factors with 1 or 2 of previous 3 terms.

Source: https://oeis.org/A079279

Conjecture in the entry (Colin Barker, Oct 15 2019):
a(n) = a(n-1) + a(n-14) - a(n-15) for n>16.

Formalization notes:
* Offset 1. `a n` is defined for every natural number n, with the junk value a(0) = 0 that is
  never used: the claim is made only for n > 16, so the indices n-1, n-14 and n-15 are at
  least 1 and the natural-number subtractions in them are exact.
* The sequence is defined by the name of the entry, not by the conjectured recurrence.
  A number m shares a common factor with a term t when gcd(m, t) > 1. `shared m x y z` counts
  how many of the three previous terms x = a(n-3), y = a(n-2), z = a(n-1) do so (counted by
  position, as a list), and the rule asks for this count to be 1 or 2. This is the reading
  fixed by the example in the entry: 5, 6, 7 and 8 have factors in common with 0, 3, 0 and 2
  of the terms 2, 3, 4, therefore a(5) = 8.
* Next integer is read as the least integer greater than the previous term a(n-1) that
  satisfies the rule. It is taken with `sInf` on the natural numbers, which is the least
  element of the set when the set is nonempty (and 0 by convention if it were empty).
* The values of a are natural numbers. The recurrence is stated in the integers, so that the
  subtraction of a(n-15) is the ordinary one.
* The same formula block of the entry also gives a conjectured generating function with
  denominator (1 - x)(1 - x^14). It encodes this recurrence together with the first 16 terms,
  and it is not restated here.
-/

namespace OMA.S_oeis_a079279

/-- The number of the three terms x, y, z that share a common factor with m. -/
def shared (m x y z : ℕ) : ℕ :=
  ([x, y, z].filter (fun t => 1 < Nat.gcd m t)).length

/-- The next integer after z sharing common factors with 1 or 2 of the terms x, y, z. -/
noncomputable def next (x y z : ℕ) : ℕ :=
  sInf {m : ℕ | z < m ∧ (shared m x y z = 1 ∨ shared m x y z = 2)}

/-- A079279: a(n) = n for n ≤ 3, and for n > 3, a(n) is the next integer sharing common
factors with 1 or 2 of the previous 3 terms. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | (n + 4) => next (a (n + 1)) (a (n + 2)) (a (n + 3))

/-- Barker's conjecture on A079279: a(n) = a(n-1) + a(n-14) - a(n-15) for n > 16. -/
theorem main :
    ∀ n : ℕ, 16 < n →
      (a n : ℤ) = (a (n - 1) : ℤ) + (a (n - 14) : ℤ) - (a (n - 15) : ℤ) := by
  sorry

end OMA.S_oeis_a079279
