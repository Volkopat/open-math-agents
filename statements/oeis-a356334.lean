import Mathlib

/-!
# A356334: number of solutions of x^(n+1) + y^(n+1) = (x+y)^n

Source: https://oeis.org/A356334 (conjecture of Chai Wah Wu, Sep 21 2022)

`a(n)` (offset 0) is the number of pairs `(x, y)` of nonnegative integers with `x <= y` and
`x^(n+1) + y^(n+1) = (x+y)^n`. The solution set is finite (any solution has `y <= 2^n`), and
we count it with `Set.ncard`.

Conjecture: `a(n) = 3` except for `n = 0` or `n = 2`.
-/

namespace OMA.S_oeis_a356334

/-- The solutions `(x, y)` with `x <= y` of `x^(n+1) + y^(n+1) = (x+y)^n`. -/
def sols (n : ℕ) : Set (ℕ × ℕ) :=
  {p | p.1 ≤ p.2 ∧ p.1 ^ (n + 1) + p.2 ^ (n + 1) = (p.1 + p.2) ^ n}

/-- The number of such solutions. -/
noncomputable def a (n : ℕ) : ℕ := (sols n).ncard

theorem main : ∀ n : ℕ, n ≠ 0 → n ≠ 2 → a n = 3 := by
  sorry

end OMA.S_oeis_a356334
