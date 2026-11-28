import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# A163824: Recurrence for double-chevron grid permutations

Source: https://oeis.org/A163824 (sequence by David Bevan, recurrence by R. J. Mathar)
Credit: @Alienchisel

The two upper cells are increasing and the two lower cells are decreasing.
The recurrence is stated from length 4. At length 3, the four displayed
initial values give a nonzero residual of -6.
-/

namespace OMA.S_oeis_a163824

/-- The permutation admits a two-by-two gridding with the double-chevron cell orientations. -/
def HasDoubleChevronGridding {n : ℕ} (perm : Equiv.Perm (Fin n)) : Prop :=
  ∃ columnDivider rowDivider : Fin (n + 1),
    ∀ i j : Fin n, i < j →
      (i.val < columnDivider.val ↔ j.val < columnDivider.val) →
      ((perm i).val < rowDivider.val ↔ (perm j).val < rowDivider.val) →
      (perm i < perm j ↔ rowDivider.val ≤ (perm i).val)

/-- Each permutation is counted once, independently of the number of valid griddings. -/
noncomputable def gridCount (n : ℕ) : ℤ :=
  Nat.card {perm : Equiv.Perm (Fin n) // HasDoubleChevronGridding perm}

theorem main : ∀ n : ℕ, 4 ≤ n →
    let x : ℤ := n
    x * (x ^ 2 - 6 * x + 11) * gridCount n +
      (-9 * x ^ 3 + 56 * x ^ 2 - 119 * x + 60) * gridCount (n - 1) +
      2 * (13 * x ^ 3 - 83 * x ^ 2 + 193 * x - 150) * gridCount (n - 2) -
      12 * (2 * x - 5) * (x ^ 2 - 4 * x + 6) * gridCount (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a163824
