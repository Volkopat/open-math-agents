import Mathlib.Data.Nat.Choose.Basic

/-!
# Odd terms of OEIS A007228

Peter Bala's conjecture of March 13, 2023.
Source: https://oeis.org/A007228
OEIS A263133 lists exactly the nonnegative integers m for which
binomial(4m + 3, m) is odd: https://oeis.org/A263133
Credit: @jatin6
-/

namespace OMA.S_oeis_a007228

def a (n : ℕ) : ℕ := 3 * (4 * n).choose n / (n + 1)

theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n % 2 = 1 ↔ ∃ m : ℕ, n = 4 * m + 3 ∧ (4 * m + 3).choose m % 2 = 1) := by
  sorry

end OMA.S_oeis_a007228
