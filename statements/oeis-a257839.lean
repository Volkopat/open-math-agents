import Mathlib.Order.Lattice.Nat

namespace OMA.S_oeis_a257839

/-- Predicate: `x` is the smallest positive integer in an Erdős–Straus decomposition
`4 / n = 1 / x + 1 / y + 1 / z` with `0 < x < y < z`, written in cleared-denominator form
`4 * x * y * z = n * (y * z + x * z + x * y)`. -/
def HasESWithX (n x : ℕ) : Prop :=
  0 < x ∧ ∃ y z : ℕ, x < y ∧ y < z ∧ 4 * x * y * z = n * (y * z + x * z + x * y)

/-- OEIS A257839(n): Smallest `x > 0` admitting integers `x < y < z` with
`4 / n = 1 / x + 1 / y + 1 / z`, or `0` if no such solution exists. -/
noncomputable def A257839 (n : ℕ) : ℕ :=
  sInf { x : ℕ | HasESWithX n x }

/-- Conjecture (OEIS A257839): For all `n > 2`, `A257839(n) = ⌊n / 4⌋ + 1` or
`A257839(n) = ⌊n / 4⌋ + 2`. -/
theorem main :
    ∀ n : ℕ, 2 < n → A257839 n = n / 4 + 1 ∨ A257839 n = n / 4 + 2 := by
  sorry

end OMA.S_oeis_a257839
