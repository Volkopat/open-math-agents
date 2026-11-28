import Mathlib

/-!
# OEIS A000123: binary partitions, ratio limit

Source: https://oeis.org/A000123
`a n` is the number of partitions of `2 n` into powers of `2`. Conjecture (Cloitre, 2003):
`lim (log n * a (2 n)) / (n * a n)` exists; Kotesovec (2019) identified the constant as
`2 log 2`. `main` states the conjecture with that constant.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a000123

open Filter Topology Real Classical

/-- Number of partitions of `2 n` all of whose parts are powers of `2`. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Nat.Partition (2 * n) => ∀ i ∈ p.parts, ∃ k, i = 2 ^ k).card

theorem main :
    Tendsto (fun n : ℕ => Real.log n * a (2 * n) / (n * a n)) atTop (𝓝 (2 * Real.log 2)) := by
  sorry

end OMA.S_oeis_a000123
