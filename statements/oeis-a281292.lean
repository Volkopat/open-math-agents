import Mathlib

/-!
# A281292: Squarefree numbers that are the sum of two squares in exactly one way.

Source: https://oeis.org/A281292
Credit: @matchalabubu15

Conjecture, from the COMMENTS section of the entry:

  Conjecture: each positive integer is a sum |x| + |y| such that x^2 + y^2 is in the sequence.

## How "exactly one way" is counted

A "way" is an unordered pair of squares. The order of the two squares and the signs of their
square roots are ignored, and 0^2 is allowed. So a way of writing n is a pair of natural numbers
(a, b) with a ≤ b and a^2 + b^2 = n.

The data of the entry requires this reading:
* 1 is a term, with the example 1 = 0^2 + 1^2. Its only way uses 0^2, so 0^2 must be allowed.
* 5 is a term, although 5 = 1^2 + 2^2 = 2^2 + 1^2 = (-1)^2 + 2^2. If order or signs were counted,
  these would be several ways.

## The conjecture

x and y are integers, as the absolute values in the source indicate. Either of them may be 0
(this is needed for the positive integer 1 = |0| + |1|).
-/

namespace OMA.S_oeis_a281292

/-- Membership in A281292: `n` is squarefree, and there is exactly one pair of natural numbers
`(a, b)` with `a ≤ b` and `a ^ 2 + b ^ 2 = n`. -/
def InA281292 (n : ℕ) : Prop :=
  Squarefree n ∧ ∃! p : ℕ × ℕ, p.1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 = n

/-- Each positive integer `n` is a sum `|x| + |y|` such that `x ^ 2 + y ^ 2` is in the sequence.
The number `x ^ 2 + y ^ 2` is never negative, so `Int.toNat` does not change its value. -/
theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ x y : ℤ, (n : ℤ) = |x| + |y| ∧ InA281292 (x ^ 2 + y ^ 2).toNat := by
  sorry

end OMA.S_oeis_a281292
