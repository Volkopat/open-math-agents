import Mathlib

/-!
# A325689: Number of length-3 compositions of n such that no part is the sum of the other two.

Source: https://oeis.org/A325689
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (offset 0, data 0, 0, 0, 1, 0, 6, 4, 15, 12, 28, 24, 45, 40, 66, ...) records in its
FORMULA section, under Conjectures from Colin Barker, May 16 2019:

  a(n) = -(5 + 3*(-1)^n - 2*n) * (n-2) / 4 for n>0.

Conventions:
* A composition of `n` of length 3 is an ordered triple `(x, y, z)` of positive integers with
  `x + y + z = n`. The sequence `a n` counts those triples with `x ≠ y + z`, `y ≠ x + z` and
  `z ≠ x + y`. Every part of such a triple is at most `n`, so the triples are counted inside
  `{1, ..., n}^3`; this gives `a 0 = 0`, matching the entry (offset 0).
* The closed form is read in `ℤ`, where the division by `4` is integer division (it is exact),
  and is claimed for every `n ≥ 1`, as in the entry.
-/

namespace OMA.S_oeis_a325689

/-- `a n` is the number of length-3 compositions `(x, y, z)` of `n` in which no part is the sum
of the other two. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun t : ℕ × ℕ × ℕ =>
    t.1 + t.2.1 + t.2.2 = n ∧ t.1 ≠ t.2.1 + t.2.2 ∧ t.2.1 ≠ t.1 + t.2.2 ∧
      t.2.2 ≠ t.1 + t.2.1).card

/-- Colin Barker's conjectured closed form for A325689. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℤ) = -(5 + 3 * (-1) ^ n - 2 * (n : ℤ)) * ((n : ℤ) - 2) / 4 := by
  sorry

end OMA.S_oeis_a325689
