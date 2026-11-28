import Mathlib

/-!
# A324298: Positive integers k such that 10*k+6 is equal to the product of two integers ending with 6 (A324297).

Source: https://oeis.org/A324298
Credit: @bnb9001

The sequence has offset 1 (3, 9, 15, 21, 25, ...). The integers ending with 6 are the numbers
`10 a + 6` with `a ≥ 0`. `a n` is the `n`-th such `k` in increasing order.

Conjecture: lim_{n -> oo} a(n)/a(n-1) = 1. Stefano Spezia notes that the conjecture is true. We
state the limit as `a (n + 1) / a n → 1`.
-/

namespace OMA.S_oeis_a324298

open Filter Topology

/-- `10 k + 6` is a product of two integers ending with 6. -/
def IsTerm (k : ℕ) : Prop := ∃ x y : ℕ, 10 * k + 6 = (10 * x + 6) * (10 * y + 6)

/-- A324298: the `n`-th term (1-indexed) in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- The ratio of consecutive terms tends to 1. -/
theorem main : Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / a n) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a324298
