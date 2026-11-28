import Mathlib

/-!
# Kurkov's first-column conjecture for OEIS A370381

The array and conjecture are from https://oeis.org/A370381 (Mikhail Kurkov, 2024).
The comparison sequence https://oeis.org/A003319 counts connected permutations.
We use its independent factorial recurrence, recorded there by Bowen in 1976.
It classifies decomposable permutations by the length of their first connected block.
-/

namespace OMA.S_oeis_a370381

/-- The row and column indices of Kurkov's array both start at zero. -/
def entry : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, k => ∑ j ∈ Finset.range (k + 2), (k + 2).choose (j + 1) * entry n j

/-- A003319, with the empty permutation counted once. In the sum, `j + 1` is the
length of the suffix after the first connected block. -/
def connected : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1).factorial -
      ∑ j ∈ Finset.range n, (j + 1).factorial * connected (n - j)
termination_by n => n

/-- Kurkov's conjecture holds at every row, including row zero. -/
theorem main : ∀ n : ℕ, entry n 0 = connected (n + 2) := by
  sorry

end OMA.S_oeis_a370381
