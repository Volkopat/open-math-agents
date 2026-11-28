import Mathlib

/-!
# A248923: a(n) is the smallest k >= n such that prime(n)*prime(k) - prime(n+k) is a perfect square.

Source: https://oeis.org/A248923
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A248923 (Michel Lagneau, Oct 16 2014): a(n) exists for
all n.

Conventions:
* The sequence has offset 1 (data 1, 3, 5, 57, 99, 10, 30, 17, 28, 91, 398, 2638, ...).
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* `a(n) exists` is the statement that for every n >= 1 (the offset) there is k >= n such that
  prime(n)*prime(k) - prime(n+k) is a perfect square; a(n) is then the smallest such k.
* The difference is computed in `ℤ` and `a perfect square` is `IsSquare` in `ℤ` (a negative
  integer is never a square).
-/

namespace OMA.S_oeis_a248923

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The conjecture recorded in A248923. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ k : ℕ, n ≤ k ∧ IsSquare ((pr n : ℤ) * (pr k : ℤ) - (pr (n + k) : ℤ)) := by
  sorry

end OMA.S_oeis_a248923
