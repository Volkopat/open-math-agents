import Mathlib

/-!
# A173526: a(n) = 1 + A053827(n-1), where A053827 is the sum-of-digits function in base 6.

Source: https://oeis.org/A173526
Credit: @agchua

Formula lines of A173526 (Joerg Arndt, Dec 08 2010), verbatim:
  Conjecture: Fixed point of the morphism 1->{1,2,3,...,b}, 2->{2,3,4,...,b+1},
  j->{j,j+1,...,j+b-1} for b=6.
Offset of A173526: 1 (data 1, 2, 3, 4, 5, 6, 2, 3, 4, ...). A053827(m) is the sum of the
base-6 digits of m, with A053827(0) = 0.

Formalisation. For b = 6 the morphism maps the letter j to the word j, j+1, ..., j+5 of length 6.
So the image of a sequence u(1), u(2), u(3), ... is the concatenation of the blocks
u(i), u(i)+1, ..., u(i)+5, and its term at position 6*i + j + 1 (i >= 0, 0 <= j <= 5) is
u(i+1) + j. A fixed point is a sequence equal to its own image; the one meant here starts with
the letter 1 (its first block is 1, 2, ..., 6, as in the data). So the conjecture says:
a(1) = 1, and a(6*i + j + 1) = a(i + 1) + j for all i >= 0 and 0 <= j <= 5.
-/

namespace OMA.S_oeis_a173526

/-- A053827: the sum of the base-6 digits of m. -/
def A053827 (m : ℕ) : ℕ := (Nat.digits 6 m).sum

/-- A173526, offset 1: a(n) = 1 + A053827(n-1). -/
def a (n : ℕ) : ℕ := 1 + A053827 (n - 1)

/-- A173526 is the fixed point, starting with 1, of the morphism j -> j, j+1, ..., j+5. -/
theorem main : a 1 = 1 ∧ ∀ i j : ℕ, j < 6 → a (6 * i + j + 1) = a (i + 1) + j := by
  sorry

end OMA.S_oeis_a173526
