import Mathlib

/-!
# A390795: Number of ways to write n as ((p-1)/2)^4 + x^2 + 2*y^2 + 3*z^2, where p is 1 or an odd prime, and x,y,z are in the set {m >= 0: 2*m is practical}

Source: https://oeis.org/A390795
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, Nov 19 2025, in the comments of A390795): a(n) > 0 for every natural
number n, i.e. every natural number n can be written as ((p-1)/2)^4 + x^2 + 2*y^2 + 3*z^2 with p
equal to 1 or an odd prime, and x, y, z in the set {m >= 0 : 2*m is practical}. This has been
verified for n <= 2*10^5.

Conventions:
* A practical number is a positive integer n such that every m with m <= n is a sum of distinct
  divisors of n (Srinivasan's definition, A005153: 1, 2, 4, 6, 8, 12, ...).
* The set {m >= 0 : 2*m is practical} contains m = 0, as the examples and the Mathematica program
  of A390795 require (the program tests `n == 0 || pr[2n]`, and the example
  251 = ((1-1)/2)^4 + 0^2 + 2*2^2 + 3*9^2 uses x = 0; also a(0) = 1).
* For p = 1 or p an odd prime, (p - 1) / 2 is an exact division.
* "Natural number" includes 0: the sequence starts at a(0) = 1.
-/

namespace OMA.S_oeis_a390795

/-- `n` is a practical number: `n > 0` and every `m <= n` is a sum of distinct divisors of `n`. -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m ≤ n → ∃ s ⊆ n.divisors, ∑ i ∈ s, i = m

/-- `m` belongs to the set `{m >= 0 : 2*m is practical}` of A390795 (with `m = 0` included). -/
def InPracticalHalves (m : ℕ) : Prop :=
  m = 0 ∨ IsPractical (2 * m)

/-- Sun's conjecture on A390795: every natural number `n` is `((p-1)/2)^4 + x^2 + 2*y^2 + 3*z^2`
with `p` equal to 1 or an odd prime and `x, y, z` in `{m >= 0 : 2*m is practical}`. -/
theorem main : ∀ n : ℕ, ∃ p x y z : ℕ, (p = 1 ∨ (p.Prime ∧ Odd p)) ∧
    InPracticalHalves x ∧ InPracticalHalves y ∧ InPracticalHalves z ∧
    n = ((p - 1) / 2) ^ 4 + x ^ 2 + 2 * y ^ 2 + 3 * z ^ 2 := by
  sorry

end OMA.S_oeis_a390795
