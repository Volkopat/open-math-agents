import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A266220: Number of black cells at each step of the Rule 7 cellular automaton

Source: https://oeis.org/A266220
Credit: @MMexicann
-/

namespace OMA.S_oeis_a266220

open PowerSeries

def black : ℕ → ℤ → Bool
  | 0, x => decide (x = 0)
  | n + 1, x => !black n (x - 1) && !(black n x && black n (x + 1))

-- The source counts only the centered row of width 2*n+1 at step n.
def blackCount (n : ℕ) : ℤ :=
  ((Finset.range (2 * n + 1)).filter
    (fun (j : ℕ) => black n ((j : ℤ) - (n : ℤ)) = true)).card

theorem main :
    (∀ n : ℕ, 1 < n → 2 * blackCount n = (1 - (-1 : ℤ) ^ n) * (2 * (n : ℤ) + 1)) ∧
    (∀ n : ℕ, 5 < n → blackCount n = 2 * blackCount (n - 2) - blackCount (n - 4)) ∧
    PowerSeries.mk blackCount * ((1 - X) ^ 2 * (1 + X) ^ 2) =
      1 + 2 * X - 2 * X ^ 2 + 3 * X ^ 3 + X ^ 4 - X ^ 5 := by
  sorry

end OMA.S_oeis_a266220
