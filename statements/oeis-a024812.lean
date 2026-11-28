import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Nth

namespace OMA.S_oeis_a024812

/-- `HasUniqueCotPreimage n` holds when `n ≥ 1` and there is a unique positive integer `m ≥ 1`
such that `⌊cot(π / (2m))⌋ = n` (where `cot θ = cos θ / sin θ`). -/
def HasUniqueCotPreimage (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃! m : ℕ, 1 ≤ m ∧ ⌊Real.cos (Real.pi / (2 * (m : ℝ))) / Real.sin (Real.pi / (2 * (m : ℝ)))⌋ = (n : ℤ)

/-- 1-indexed `k`-th term (`k ≥ 1`) of OEIS A024812 (positive integers `n` with a unique
positive integer `m` such that `n = ⌊cot(π / (2m))⌋`). -/
noncomputable def a024812 (k : ℕ) : ℕ :=
  Nat.nth HasUniqueCotPreimage (k - 1)

/-- Colin Barker's 2014 recurrence conjecture for OEIS A024812:
`a(n) = a(n - 1) + a(n - 3) - a(n - 4)` for all `n ≥ 5`. -/
theorem main :
    ∀ n : ℕ, 5 ≤ n → a024812 n + a024812 (n - 4) = a024812 (n - 1) + a024812 (n - 3) := by
  sorry

end OMA.S_oeis_a024812
