import Mathlib

/-!
# OEIS A007018: `a(n) = a(n-1)² + a(n-1)` and unitary half-Zumkeller numbers

Source: https://oeis.org/A007018
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(0) = 1`, `a(n) = a(n-1)² + a(n-1)`: `1, 2, 6, 42, 1806, …`. The entry notes that, except for
the first two, all terms are conjecturally (Das, Conjecture 3.1, see A290467) unitary
half-Zumkeller numbers: numbers `k` whose unitary proper divisors can be partitioned into two
disjoint sets with equal sums.

Conventions:
* A unitary divisor of `k` is a divisor `d` with `gcd(d, k/d) = 1`; proper means `d < k`.
* 'Except for the first two' means `n ≥ 2`.
-/

namespace OMA.S_oeis_a007018

/-- `a(0) = 1`, `a(n+1) = a(n)² + a(n)`. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => a n ^ 2 + a n

/-- The unitary proper divisors of `k`. -/
def unitaryProperDivisors (k : ℕ) : Finset ℕ :=
  k.properDivisors.filter fun d => Nat.Coprime d (k / d)

/-- `k` is a unitary half-Zumkeller number. -/
def IsUnitaryHalfZumkeller (k : ℕ) : Prop :=
  ∃ S ⊆ unitaryProperDivisors k, ∑ d ∈ S, d = ∑ d ∈ unitaryProperDivisors k \ S, d

/-- Every `a(n)` with `n ≥ 2` is a unitary half-Zumkeller number. -/
theorem main : ∀ n : ℕ, 2 ≤ n → IsUnitaryHalfZumkeller (a n) := by
  sorry

end OMA.S_oeis_a007018
