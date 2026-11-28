import Mathlib

/-!
# A390730: Number of ways to write 6*n+2 as an unordered sum of four squares of elements in the set {m >= 0: m = 0 or 2*m is practical}

Source: https://oeis.org/A390730
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, in the comments of A390730): Let S be the set of those natural numbers m
such that 2*m is either zero or practical. Then any integer n >= 0 with n == 0,1 (mod 4) or
n == 2,4 (mod 6) can be written as w^2 + x^2 + y^2 + z^2 with w,x,y,z in the set S.
This has been verified for n <= 6*10^5.

Conventions:
* A practical number is a positive integer n such that every m with m <= n is a sum of distinct
  divisors of n (Srinivasan's definition, A005153: 1, 2, 4, 6, 8, 12, ...).
* The integers n >= 0 are taken as natural numbers.
-/

namespace OMA.S_oeis_a390730

/-- `n` is a practical number: `n > 0` and every `m <= n` is a sum of distinct divisors of `n`. -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m ≤ n → ∃ s ⊆ n.divisors, ∑ i ∈ s, i = m

/-- The set `S` of A390730: natural numbers `m` such that `2*m` is either zero or practical. -/
def S : Set ℕ := {m | 2 * m = 0 ∨ IsPractical (2 * m)}

/-- Sun's conjecture on A390730: every `n >= 0` with `n ≡ 0, 1 (mod 4)` or `n ≡ 2, 4 (mod 6)` is
`w^2 + x^2 + y^2 + z^2` with `w, x, y, z ∈ S`. -/
theorem main : ∀ n : ℕ, (n % 4 = 0 ∨ n % 4 = 1 ∨ n % 6 = 2 ∨ n % 6 = 4) →
    ∃ w ∈ S, ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, n = w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 := by
  sorry

end OMA.S_oeis_a390730
