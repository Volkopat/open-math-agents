import Mathlib

/-!
# Is every twin prime middle `m > 348` the midpoint of two other twin prime middles?

Source: https://math.stackexchange.com/questions/5153000

Call an integer `m` a twin middle if both `m - 1` and `m + 1` are prime (`4, 6, 12, 18, 30, …`).
Question: for a twin middle `m`, does there exist `d > 0` such that `m - d` and `m + d` are both
twin middles? Conjecture: this holds for every twin middle `m > 348`. (The only exceptions found
up to about `4.9 · 10⁶` are `m = 4, 6, 198, 348`.)

Formalization notes:
* `m` ranges over `ℕ`; `d < m` keeps `m - d` positive (a twin middle is at least `4`), so the
  truncated subtraction is exact.
-/

namespace OMA.S_mse_5153000

/-- `m` is a twin middle: `m - 1` and `m + 1` are both prime. -/
def IsTwinMiddle (m : ℕ) : Prop := (m - 1).Prime ∧ (m + 1).Prime

/-- Every twin middle `m > 348` is the midpoint of two twin middles `m - d`, `m + d`, `d > 0`. -/
theorem main : ∀ m : ℕ, 348 < m → IsTwinMiddle m →
    ∃ d : ℕ, 0 < d ∧ d < m ∧ IsTwinMiddle (m - d) ∧ IsTwinMiddle (m + d) := by
  sorry

end OMA.S_mse_5153000
