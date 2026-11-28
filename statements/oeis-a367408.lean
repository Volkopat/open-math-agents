import Mathlib.Data.Nat.Log
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# OEIS A367408

At positive indices that are powers of two, the sequence equals its index.
For `2^r < n < 2^(r+1)`, put `k = n - 2^r` and choose the least positive
multiplier `m` such that both `m` and `m * a k` are absent from the earlier
terms. Then `a n = m * a k`.

The source starts at index 1. Index 0 has no role in the rule or the conclusion.

Source: https://oeis.org/A367408
-/

namespace OMA.S_oeis_a367408

/-- The values at positive indices strictly below `n`. -/
def used (a : ℕ → ℕ) (n : ℕ) : Finset ℕ := (Finset.Ioo 0 n).image a

/-- Both the multiplier and the resulting term must be new. -/
def Eligible (a : ℕ → ℕ) (n k m : ℕ) : Prop :=
  0 < m ∧ m ∉ used a n ∧ m * a k ∉ used a n

/-- The prescribed terms and the greedy rule between consecutive powers of two. -/
def Rule (a : ℕ → ℕ) : Prop :=
  (∀ r : ℕ, a (2 ^ r) = 2 ^ r) ∧
    ∀ r n : ℕ, 2 ^ r < n → n < 2 ^ (r + 1) →
      ∃ m, IsLeast {x | Eligible a n (n - 2 ^ r) x} m ∧ a n = m * a (n - 2 ^ r)

theorem main :
    (∃ a, Rule a) ∧ ∀ a, Rule a → Set.BijOn a (Set.Ici 1) (Set.Ici 1) := by
  sorry

end OMA.S_oeis_a367408
