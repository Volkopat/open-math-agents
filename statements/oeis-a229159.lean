import Mathlib

/-!
# A229159: Smallest integer areas of integer-sided triangles where at least one side is of length prime(n)

Source: https://oeis.org/A229159
Credit: @xor2k

Formalizes the OEIS A229159 conjecture:
Conjecture: for all prime p > 2 there exists an integer-sided triangle with integer area where at
least one side is of length p.

Conventions: a triangle with integer sides `a, b, c` is a triple of positive natural numbers
satisfying the strict triangle inequalities (non-degenerate, matching the entry, where a(1) = 0
for p = 2 records that no such triangle exists). Its area `A` is given by Heron's formula
`16 * A^2 = (a+b+c)(-a+b+c)(a-b+c)(a+b-c)`, evaluated in `ℤ` so that no truncated subtraction
occurs; integer area means this holds for some natural number `A`, and `0 < A` (the area of a
non-degenerate triangle is positive). At least one side is of length `p` means `a = p ∨ b = p ∨ c = p`.
The other comments of the entry are examples and an observation, not conjectures.
-/

namespace OMA.S_oeis_a229159

/-- `a, b, c` are the side lengths of a non-degenerate triangle whose area, by Heron's formula,
is the positive natural number `A`. -/
def IsIntTriangleWithArea (a b c A : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ a < b + c ∧ b < a + c ∧ c < a + b ∧ 0 < A ∧
    16 * (A : ℤ) ^ 2 =
      ((a : ℤ) + b + c) * (-(a : ℤ) + b + c) * ((a : ℤ) - b + c) * ((a : ℤ) + b - c)

/-- Every prime `p > 2` is a side length of some integer-sided triangle with integer area. -/
theorem main :
    ∀ p : ℕ, p.Prime → 2 < p →
      ∃ a b c A : ℕ, (a = p ∨ b = p ∨ c = p) ∧ IsIntTriangleWithArea a b c A := by
  sorry

end OMA.S_oeis_a229159
