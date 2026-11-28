import Mathlib

/-!
# A034175: a greedy square-sum sequence is a permutation

Source: https://oeis.org/A034175
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A034175): the sequence is a permutation of the nonnegative integers, where
`a(0) = 0` and `a(n)` is minimal such that `a(n) + a(n-1)` is a square and `a(n)` is not in
`{a(0), …, a(n-1)}`.

Conventions:
* Offset 0 with `a(0) = 0`, as in the entry. The candidate set at each step is nonempty (there are
  infinitely many squares), so `sInf` picks the least admissible value.
-/

namespace OMA.S_oeis_a034175

/-- The list `[a(0), …, a(n)]`. -/
noncomputable def L : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => L n ++ [sInf {m : ℕ | IsSquare (m + (L n).getLastD 0) ∧ m ∉ L n}]

/-- A034175. -/
noncomputable def a (n : ℕ) : ℕ := (L n).getLastD 0

theorem main : Function.Bijective a := by
  sorry

end OMA.S_oeis_a034175
