import Mathlib

/-!
# A353008: smallest positive k such that k^2 + 1 has 2n divisors

Source: https://oeis.org/A353008
Credit: @Bondyboy2001

For positive `n`, `a(n)` is the smallest positive integer `k` such that `k^2 + 1` has exactly
`2n` positive divisors, or `-1` if no such `k` exists. Jon E. Schoenfield conjectured in the
OEIS entry that `a(n)` is never `-1`.

The sequence offset is `1`, so the conjecture is stated for positive `n`.
-/

namespace OMA.S_oeis_a353008

/-- The positive-integer condition defining A353008. -/
def IsWitness (n k : ℕ) : Prop :=
  0 < k ∧ (k ^ 2 + 1).divisors.card = 2 * n

open scoped Classical in
/-- `a n`: the least positive witness, or `-1` if no witness exists. -/
noncomputable def a (n : ℕ) : ℤ :=
  if h : ∃ k : ℕ, IsWitness n k then (Nat.find h : ℤ) else -1

theorem main : ∀ n : ℕ, 1 ≤ n → a n ≠ -1 := by
  sorry

end OMA.S_oeis_a353008
