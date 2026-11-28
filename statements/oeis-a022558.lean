import Mathlib.Data.Fin.VecNotation
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Order.Hom.Basic

/-!
# A022558: The patterns 1342 and the pair 2143, 415263 have equal avoidance counts

Source: https://oeis.org/A022558 (conjecture by Alexander Burstein)
Credit: @Alienchisel

A pattern occurs when the values at a strictly increasing selection of positions
have the same relative order as the displayed pattern. The selection can skip positions.
-/

namespace OMA.S_oeis_a022558

/-- There is no increasing selection of positions whose values have the given relative order. -/
def AvoidsPattern {n k : ℕ} (perm : Equiv.Perm (Fin n)) (pattern : Fin k → ℕ) : Prop :=
  ¬ ∃ positions : Fin k ↪o Fin n, ∀ i j : Fin k,
    perm (positions i) < perm (positions j) ↔ pattern i < pattern j

theorem main : ∀ n : ℕ,
    Nat.card {perm : Equiv.Perm (Fin n) // AvoidsPattern perm ![1, 3, 4, 2]} =
      Nat.card {perm : Equiv.Perm (Fin n) //
        AvoidsPattern perm ![2, 1, 4, 3] ∧ AvoidsPattern perm ![4, 1, 5, 2, 6, 3]} := by
  sorry

end OMA.S_oeis_a022558
