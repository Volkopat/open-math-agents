import Mathlib

/-!
# A214900: Number of ordered ways to represent n as the sum of three squares and one fourth power.

Source: https://oeis.org/A214900
Credit: @luciusacarr

The entry records one conjecture: a(n) != 0, that is, all numbers are sums of three squares and
one fourth power. (Here a(n) counts the ordered quadruples `(x, y, z, w)` of nonnegative integers
with `n = x^2 + y^2 + z^2 + w^4`; e.g. a(0) = 1, a(1) = 4.)

Reading of the source:
* The squares and the fourth power are those of nonnegative integers (the g.f. in the entry is
  `(Sum_{j>=0} x^(j^2))^3 * (Sum_{j>=0} x^(j^4))`), and the sequence starts at n = 0.
* `a(n) != 0` means that at least one such quadruple exists, so the conjecture is: for every
  natural number `n` there are natural numbers `x, y, z, w` with `x^2 + y^2 + z^2 + w^4 = n`.
-/

namespace OMA.S_oeis_a214900

/-- `n` is a sum of three squares and one fourth power of natural numbers. -/
def IsRep (n : ℕ) : Prop :=
  ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 4 = n

theorem main : ∀ n : ℕ, IsRep n := by
  sorry

end OMA.S_oeis_a214900
