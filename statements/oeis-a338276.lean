import Mathlib

/-!
# A338276: Number of odd entries in each column of A334016

Sources: https://oeis.org/A338276 and https://oeis.org/A334016
Conjecture by Peter Kagey. Formalization by @yuka30240.
-/

namespace OMA.S_oeis_a338276

/-- A334016 counts queen paths from (1, 1) to (r, k) in the positive quadrant.
The three sums classify paths by the direction and length of the last move. -/
def queenPaths (r k : ℕ) : ℕ :=
  if r = 0 ∨ k = 0 then 0
  else if r = 1 ∧ k = 1 then 1
  else
    (∑ i : Fin (k - 1), queenPaths (r + (i.val + 1)) (k - (i.val + 1))) +
    (∑ i : Fin (min r k - 1), queenPaths (r - (i.val + 1)) (k - (i.val + 1))) +
    (∑ i : Fin (r - 1), queenPaths (i.val + 1) k)
termination_by (k, r)
decreasing_by all_goals decreasing_tactic

/-- A338276 counts rows, starting at one, whose entry in column k is odd. -/
noncomputable def oddCount (k : ℕ) : ℕ :=
  {r : ℕ | 0 < r ∧ Odd (queenPaths r k)}.ncard

theorem main : ∀ n : ℕ, 0 < n → oddCount (2 ^ n - 1) = 2 ^ n := by
  sorry

end OMA.S_oeis_a338276
