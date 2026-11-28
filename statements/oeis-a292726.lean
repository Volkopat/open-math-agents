import Mathlib

/-!
# A292726: number of states reachable in the equal-piles stone game

Source: https://oeis.org/A292726
Credit: @prasledi

Entry (offset 1): a(n) is the number of states that can be achieved when starting from n piles
each containing one stone, where any number of stones can be transferred between piles that start
with the same number of stones. Order does not matter (a state is a partition of n).

Conjectures (comments of the entry):
* A000041(n) - a(n) = 0 if and only if n is a power of 2, and
* A000041(n) - a(n) = 1 if and only if n is an odd prime.

Conventions:
* A state is the multiset of the (positive) pile sizes. `Move s t` is one move: `s` contains two
  piles with the same number `a ≥ 1` of stones, and `k` stones (`0 ≤ k ≤ a`) are transferred from
  one of them to the other, giving piles `a + k` and `a - k`; a pile left empty is discarded.
* `reachable n s`: the state `s` is obtained from `n` piles of one stone by finitely many moves.
* `a n` counts the partitions of `n` (A000041(n) = `Fintype.card (Nat.Partition n)`) whose parts
  form a reachable state. The statement is for every `n ≥ 1` (offset 1).
-/

namespace OMA.S_oeis_a292726

/-- One move: two piles of `a` stones each become piles of `a + k` and `a - k` stones
(`k ≤ a`); empty piles are discarded. -/
def Move (s t : Multiset ℕ) : Prop :=
  ∃ (r : Multiset ℕ) (a k : ℕ), 0 < a ∧ k ≤ a ∧ s = a ::ₘ a ::ₘ r ∧
    t = ((a + k) ::ₘ (a - k) ::ₘ r).filter (· ≠ 0)

/-- `s` is reachable from `n` piles of one stone. -/
def reachable (n : ℕ) (s : Multiset ℕ) : Prop :=
  Relation.ReflTransGen Move (Multiset.replicate n 1) s

open Classical in
/-- A292726(n): the number of reachable states (partitions of `n`). -/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Nat.Partition n => reachable n p.parts).card

theorem main : ∀ n : ℕ, 1 ≤ n →
    (Fintype.card (Nat.Partition n) - a n = 0 ↔ ∃ k : ℕ, n = 2 ^ k) ∧
    (Fintype.card (Nat.Partition n) - a n = 1 ↔ n.Prime ∧ Odd n) := by
  sorry

end OMA.S_oeis_a292726
