import Mathlib

/-!
# OEIS A008484: partitions into parts ≥ 4 versus a ones/parts condition

Source: https://oeis.org/A008484
`a n` is the number of partitions of `n` into parts `≥ 4`. Conjecture: `a n` is also the
number of partitions of `n` for which three times the number of ones equals twice the number
of parts.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a008484

theorem main :
    ∀ n : ℕ,
      (Finset.univ.filter fun p : Nat.Partition n => ∀ i ∈ p.parts, 4 ≤ i).card =
        (Finset.univ.filter fun p : Nat.Partition n =>
          3 * p.parts.count 1 = 2 * Multiset.card p.parts).card := by
  sorry

end OMA.S_oeis_a008484
