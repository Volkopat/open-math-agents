import Mathlib

/-!
# OEIS A005243: infinitely many non-members of a self-generating sequence

Source: https://oeis.org/A005243
Start with `1, 2`, take all sums of any number of successive previous elements and adjoin
them to the sequence; repeat: `1, 2, 3, 5, 6, 8, 10, 11, …`. Conjecture: there are infinitely
many positive integers not in the sequence.

Conventions. The sequence is increasing, so its set `S` is characterised by: `m ∈ S` iff
`m ∈ {1, 2}`, or `m` is the sum of the elements of `S` in `[x, y]` for some `x < y < m` in
`S` (two or more successive elements). This determines `S` by strong induction, so `main`
quantifies over every `S` with this property.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a005243

open Classical

theorem main :
    ∀ S : Set ℕ,
      (∀ m : ℕ, m ∈ S ↔ m = 1 ∨ m = 2 ∨ ∃ x ∈ S, ∃ y ∈ S, x < y ∧ y < m ∧
          ∑ z ∈ (Finset.Icc x y).filter (· ∈ S), z = m) →
      {m : ℕ | 0 < m ∧ m ∉ S}.Infinite := by
  sorry

end OMA.S_oeis_a005243
