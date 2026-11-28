import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin

/-! OEIS A387737 and A387736 (https://oeis.org/A387737, https://oeis.org/A387736).
A partition of n into r+1 parts is encoded by its r smaller parts in increasing
(non-strict) order. The largest part is the difference between n and their sum.
Repetitions are allowed in A387737. In A387736 the inequality at distance j-i
spells out a gap of at least two per step, including the gap to the largest part.
The range 0 ≤ r < n includes all partitions of a positive integer. -/
namespace OMA.S_oeis_a387737

open Finset

def largest (n : ℕ) {r : ℕ} (f : Fin r → ℤ) : ℤ := (n : ℤ) - ∑ i, f i

def A (n r : ℕ) (f : Fin r → ℤ) : Prop :=
  (r : ℤ) + 1 ≤ largest n f ∧ (∀ i, (r : ℤ) + 1 ≤ f i) ∧
  Monotone f ∧ (∑ i, f i) ≤ largest n f

def B (n r : ℕ) (f : Fin r → ℤ) : Prop :=
  2 ≤ largest n f ∧ (∀ i, 2 ≤ f i) ∧
  (∀ i j : Fin r, i ≤ j → f i + 2 * (j.val : ℤ) ≤ f j + 2 * (i.val : ℤ)) ∧
  (∀ i, f i + 2 ≤ largest n f) ∧ (∑ i, f i) ≤ largest n f

noncomputable def countA (n r : ℕ) : ℕ := Nat.card {f : Fin r → ℤ // A n r f}
noncomputable def countB (n r : ℕ) : ℕ := Nat.card {f : Fin r → ℤ // B n r f}

theorem main : ∀ n : ℕ, 4 ≤ n →
    (∑ r ∈ range n, countA n r) = (∑ r ∈ range n, countB n r) + 1 := by
  sorry

end OMA.S_oeis_a387737
