import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Order.Bounds.Basic

/-!
# OEIS A351495

Scott R. Shannon's sequence starts at 1. The next term is the least positive
unused multiple of the least prime that does not divide the current term.
The conjecture says that this rule gives a permutation of the positive integers.
The Lean indexing starts at zero.

Source: https://oeis.org/A351495
-/

namespace OMA.S_oeis_a351495

/-- The initial term and the two minimum conditions defining the recurrence. -/
def Greedy (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ ∀ n, ∃ p : ℕ,
    IsLeast {q : ℕ | q.Prime ∧ ¬ q ∣ a n} p ∧
    IsLeast {m : ℕ | 0 < m ∧ p ∣ m ∧ ∀ i ≤ n, a i ≠ m} (a (n + 1))

theorem main :
    (∃ a, Greedy a) ∧
      ∀ a, Greedy a → Function.Injective a ∧ Set.range a = Set.Ioi 0 := by
  sorry

end OMA.S_oeis_a351495
