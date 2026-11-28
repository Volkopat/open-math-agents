import Mathlib

/-!
# A097602: a(n+1) = a(n) + number of squares so far; a(1) = 1.

Source: https://oeis.org/A097602
Credit: @rorcores

The entry (offset 1, data 1, 2, 3, 4, 6, 8, 10, 12, 14, 16, 19, 22, 25, 29, 33, 37, 41, 45, 49, ...)
records in its COMMENTS section:

  Conjecture: a(n) = m^2 iff m mod 3 > 0.

Conventions:
* The sequence is indexed from `1`: `a(1) = 1` and, for `n ≥ 1`,
  `a(n+1) = a(n) + (number of squares among a(1), ..., a(n))`, as in the entry's examples
  (`a(5) = a(4) + #{1,4} = 4 + 2 = 6`) and in its formula
  `a(n+1) = a(n) + Sum_{k=1..n} A010052(a(k))`. These two conditions determine `a(n)` for all
  `n ≥ 1`; the statement quantifies over every function `a : ℕ → ℕ` satisfying them (the value
  `a 0` plays no role).
* The conjecture says that the squares occurring in the sequence are exactly the squares `m^2`
  with `m` not divisible by `3`: for every `m`, some term `a(n)` (with `n ≥ 1`) equals `m^2` if and
  only if `m mod 3 > 0`.
-/

namespace OMA.S_oeis_a097602

/-- `a` (indexed from `1`) is the sequence A097602: `a(1) = 1` and
`a(n+1) = a(n) + (number of squares among a(1), ..., a(n))` for `n ≥ 1`. -/
def IsA097602 (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ ∀ n : ℕ, 1 ≤ n →
    a (n + 1) = a n + ((Finset.Icc 1 n).filter fun i => IsSquare (a i)).card

/-- The conjecture of A097602: `m^2` occurs in the sequence if and only if `m mod 3 > 0`. -/
theorem main : ∀ a : ℕ → ℕ, IsA097602 a →
    ∀ m : ℕ, (∃ n : ℕ, 1 ≤ n ∧ a n = m ^ 2) ↔ 0 < m % 3 := by
  sorry

end OMA.S_oeis_a097602
