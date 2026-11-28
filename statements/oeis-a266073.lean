import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

/-!
# A266073: Number of white cells at each step of the Rule 3 cellular automaton

Source: https://oeis.org/A266073
Credit: @MMexicann
-/

namespace OMA.S_oeis_a266073

def black : ℕ → ℤ → Bool
  | 0, x => decide (x = 0)
  | n + 1, x => !(black n (x - 1) || black n x)

-- The source counts only the centered row of width 2*n+1 at step n.
def whiteCount (n : ℕ) : ℤ :=
  ((Finset.range (2 * n + 1)).filter
    (fun (j : ℕ) => black n ((j : ℤ) - (n : ℤ)) = false)).card

theorem main :
    (∀ n : ℕ, whiteCount n = (-1 : ℤ) ^ n * (n : ℤ) + (n : ℤ) - (-1 : ℤ) ^ n + 1) ∧
    (∀ n : ℕ, 3 < n → whiteCount n = 2 * whiteCount (n - 2) - whiteCount (n - 4)) := by
  sorry

end OMA.S_oeis_a266073
