import Mathlib

/-!
# A325618: Numbers m such that there exists an integer partition of m whose reciprocal factorial sum is 1.

Source: https://oeis.org/A325618
Credit: @warshanks

The reciprocal factorial sum of an integer partition `(y_1, …, y_k)` is `1/y_1! + … + 1/y_k!`.
A325618 lists the positive integers `m` having an integer partition whose reciprocal factorial sum
is `1`. The entry records one conjecture (Charlie Neder, 2019):

  `137` is the greatest integer not in this sequence.

`main` states it as: `137` is not a term, and every `m > 137` is a term. An integer partition of
`m` is Mathlib's `Nat.Partition m` (a multiset of positive parts summing to `m`); the reciprocal
factorial sum is computed in `ℚ`.
-/

namespace OMA.S_oeis_a325618

/-- The reciprocal factorial sum `1/y_1! + … + 1/y_k!` of an integer partition `(y_1, …, y_k)`. -/
def recipFactorialSum {m : ℕ} (p : Nat.Partition m) : ℚ :=
  (p.parts.map fun y => (1 : ℚ) / (y.factorial : ℚ)).sum

/-- `m` is a term of A325618: some integer partition of `m` has reciprocal factorial sum `1`. -/
def IsTerm (m : ℕ) : Prop := ∃ p : Nat.Partition m, recipFactorialSum p = 1

/-- The conjecture of OEIS A325618: `137` is the greatest integer not in the sequence. -/
theorem main : ¬ IsTerm 137 ∧ ∀ m : ℕ, 137 < m → IsTerm m := by
  sorry

end OMA.S_oeis_a325618
