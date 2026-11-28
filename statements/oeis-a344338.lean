import Mathlib

/-!
# A344338: Smallest number that is the sum of two or more consecutive positive n-th powers in more than one way.

Source: https://oeis.org/A344338
Credit: @luciusacarr

The entry records one conjecture (Jon E. Schoenfield, May 16 2021): no terms exist for n >= 4,
i.e. for n >= 4 no number is the sum of two or more consecutive positive n-th powers in more than
one way. (Known terms: a(1) = 9 = 2 + 3 + 4 = 4 + 5, a(2) = 365 = 10^2 + 11^2 + 12^2 = 13^2 + 14^2,
a(3) = 33075; a(4) > 10^24.)

Reading of the source:
* A way of writing `N` as a sum of two or more consecutive positive `n`-th powers is a pair
  `(a, l)` with `a ≥ 1`, `l ≥ 2` and `N = a^n + (a+1)^n + ... + (a+l-1)^n`. Two ways are
  different if the pairs differ.
* The conjecture: for every `n ≥ 4` and every `N`, any two such ways of writing `N` coincide.
-/

namespace OMA.S_oeis_a344338

/-- `N = a^n + (a+1)^n + ... + (a+l-1)^n` with `a ≥ 1` and `l ≥ 2`. -/
def IsRep (n N a l : ℕ) : Prop :=
  1 ≤ a ∧ 2 ≤ l ∧ N = ∑ i ∈ Finset.range l, (a + i) ^ n

theorem main :
    ∀ n : ℕ, 4 ≤ n → ∀ N a l a' l' : ℕ, IsRep n N a l → IsRep n N a' l' → a = a' ∧ l = l' := by
  sorry

end OMA.S_oeis_a344338
