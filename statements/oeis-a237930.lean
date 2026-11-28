import Mathlib

/-!
# A237930: a(n) = 3^(n+1) + (3^n-1)/2

Source: https://oeis.org/A237930
Credit: @jrohcz

Conjecture (Klaus Purath, Apr 13 2020, in the comments of A237930): this sequence contains no
prime factors p == {11, 13, 23, 61, 71, 73} (mod 84).

Conventions:
* The sequence has offset 0: a(0) = 3, a(1) = 10, a(2) = 31, a(3) = 94, a(4) = 283. The division
  in `(3 ^ n - 1) / 2` is exact, because `3 ^ n` is odd.
* The sequence contains no prime factors p in these residue classes: no prime `p` whose residue
  modulo 84 is one of 11, 13, 23, 61, 71, 73 divides any term `a n`.
-/

namespace OMA.S_oeis_a237930

/-- A237930 (offset 0): `a n = 3 ^ (n + 1) + (3 ^ n - 1) / 2`. -/
def a (n : ℕ) : ℕ := 3 ^ (n + 1) + (3 ^ n - 1) / 2

/-- The conjecture on A237930: no term has a prime factor congruent to 11, 13, 23, 61, 71 or 73
modulo 84. -/
theorem main : ∀ n p : ℕ, p.Prime → p ∣ a n →
    p % 84 ∉ ({11, 13, 23, 61, 71, 73} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a237930
