import Mathlib

/-!
# OEIS A033496: sizes of initial Collatz fans

Source: https://oeis.org/A033496
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For `n` the maximum of some Collatz trajectory, the initial fan `F(n)` is the set of starting
values `m ≤ n` whose Collatz trajectory has maximum `n`. Its size is never `2, 4, 5, 7` or `10`.
Conjecture (Hoft, 2016): every number `k > 10` occurs as the size of `F(n)` for some `n`.

Conventions:
* The Collatz map is `m ↦ m/2` (`m` even), `3m + 1` (`m` odd), on positive integers. The
  trajectory of `m` has maximum `n` iff every iterate is `≤ n` and some iterate equals `n` (this
  makes sense whether or not the trajectory reaches `1`). Starting values are `m ≥ 1`.
-/

namespace OMA.S_oeis_a033496

/-- The Collatz map. -/
def collatz (m : ℕ) : ℕ := if m % 2 = 0 then m / 2 else 3 * m + 1

/-- The trajectory of `m` has maximum `n`. -/
def HasMax (m n : ℕ) : Prop :=
  (∀ i : ℕ, collatz^[i] m ≤ n) ∧ ∃ i : ℕ, collatz^[i] m = n

/-- The initial fan `F(n)`. -/
def fan (n : ℕ) : Set ℕ := {m | 1 ≤ m ∧ m ≤ n ∧ HasMax m n}

/-- Every `k > 10` is the size of some fan. -/
theorem main : ∀ k : ℕ, 10 < k → ∃ n : ℕ, (fan n).ncard = k := by
  sorry

end OMA.S_oeis_a033496
