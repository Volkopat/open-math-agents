import Mathlib

/-!
# OEIS A218980: Integers not in A218852.

Source: https://oeis.org/A218980
Credit: @unserus

OEIS: "Conjecture: This sequence is infinite."
A218852 lists the `n` for which `σ(n) = σ(x) + σ(y) + σ(z)` for some positive `x, y, z` with
`n = x + y + z` (`σ` = sum of divisors). A218980 lists the positive integers not in A218852
(`1, 2, 3, 4, 6, 8, 9, ...`).
-/

namespace OMA.S_oeis_a218980

/-- The sum of divisors `σ(n)`. -/
abbrev sigma (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

/-- `n` is in A218852: `σ(n) = σ(x) + σ(y) + σ(z)` with `n = x + y + z`, `x, y, z ≥ 1`. -/
def InA218852 (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ n = x + y + z ∧ sigma n = sigma x + sigma y + sigma z

/-- The terms of A218980: positive integers not in A218852. -/
def a218980Set : Set ℕ := {n : ℕ | 0 < n ∧ ¬ InA218852 n}

/-- A218980 is infinite. -/
theorem main : a218980Set.Infinite := by
  sorry

end OMA.S_oeis_a218980
