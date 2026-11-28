import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Perm

/-!
# A227918: Recurrence for a weighted count of permutations

Source: https://oeis.org/A227918 (sequence by Richard Ehrenborg, recurrence by R. J. Mathar)
Credit: @Alienchisel

The first and last adjacent pairs are ascents. Two adjacent ascents are
forbidden, and a permutation with d adjacent pairs of descents has weight
2^d. The sequence starts at length 2, so the four-term recurrence starts
at length 5.
-/

namespace OMA.S_oeis_a227918

open scoped BigOperators

/-- The adjacent pair at this position is an ascent. -/
def ascends {n : ℕ} (perm : Equiv.Perm (Fin (n + 1))) (i : Fin n) : Bool :=
  decide (perm i.castSucc < perm i.succ)

/-- The weighted sum for permutations of the given length. -/
def weightedCount : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | n + 2 =>
    ∑ perm : Equiv.Perm (Fin (n + 2)),
      let doubleAscents := (Finset.univ : Finset (Fin n)).filter fun i =>
        ascends perm i.castSucc && ascends perm i.succ
      let doubleDescents := (Finset.univ : Finset (Fin n)).filter fun i =>
        !ascends perm i.castSucc && !ascends perm i.succ
      if ascends perm 0 && ascends perm (Fin.last n) && (doubleAscents.card == 0) then
        (2 : ℤ) ^ doubleDescents.card
      else
        0

theorem main : ∀ n : ℕ, 5 ≤ n →
    weightedCount n - (n : ℤ) * weightedCount (n - 1) - weightedCount (n - 2) +
      ((n : ℤ) - 2) * weightedCount (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a227918
