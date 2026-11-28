import Mathlib

/-!
# $5 \times 5\;$ "square additive set"

Source: https://math.stackexchange.com/questions/3099983/5-times-5-square-additive-set
Credit: @mgv27

Find sets $A = \{a_1,\ldots,a_n\}$, $B = \{b_1,\ldots,b_m\}$ such that $a_i + b_j = s_{ij}^2$
(with $a_i, b_j, s_{ij} \in \mathbb{Z}$, $0 \le a_1 < a_2 < \cdots < a_n$,
$0 \le b_1 < \cdots < b_m$). Examples are known for $n = m = 4$; nothing is known for
$n = m = 5$. Is it possible to find a solution for the case $5 \times 5$? Does one exist?

Formalization notes:
* `main` asserts the existence of two `5`-element sets `A, B ⊆ ℕ` with every sum `a + b`
  (`a ∈ A`, `b ∈ B`) a perfect square (the natural "yes" reading of the question).
* The conditions `0 ≤ a_1 < ⋯ < a_5` and `0 ≤ b_1 < ⋯ < b_5` say exactly that `A` and `B`
  are sets of five distinct nonnegative integers, i.e. `Finset ℕ`s of cardinality `5`.
* `A` and `B` are not required to be disjoint (the question does not require it).
* A `4 × 4` example from the question: `A = {0, 282²-18², 477²-18², 1122²-18²}`,
  `B = {18², 234², 346², 514²}`.
-/

namespace OMA.S_mse_3099983

/-- `A` and `B` form a square additive pair: every `a + b` with `a ∈ A`, `b ∈ B` is a
perfect square. -/
def SquareAdditive (A B : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, IsSquare (a + b)

/-- Is there a `5 × 5` square additive pair of sets of nonnegative integers? -/
theorem main : ∃ A B : Finset ℕ, A.card = 5 ∧ B.card = 5 ∧ SquareAdditive A B := by
  sorry

end OMA.S_mse_3099983
