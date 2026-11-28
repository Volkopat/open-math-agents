import Mathlib

/-!
# The Chen–Chvátal conjecture (a De Bruijn–Erdős theorem in metric spaces)

Source: https://arxiv.org/abs/1812.06288 (Vašek Chvátal, A De Bruijn-Erdős theorem in graphs?),
Conjecture 1: in every finite metric space with n points such that n ≥ 2, there are at least n
distinct lines or some line consists of all n points.

The line determined by distinct points x and y consists of x, y and every point z such that one
of x, y, z lies between the other two, where b lies between a and c when
dist a b + dist b c = dist a c. The points x and y satisfy this condition themselves.
The abstract's excerpt states only the graph special case (Conjecture 2); this is the general
metric-space statement from the paper.

Literature: still open; the best general lower bound found is Ω(n^(2/3)) lines in spaces without
a universal line (Huang, arXiv:2310.15058), and recent work settles special graph classes only
(e.g. arXiv:2512.12047, graphs of diameter 3).
-/

namespace OMA.S_arxiv_1812_06288

/-- The line determined by `x` and `y`: all `z` such that one of `x, y, z` is between the others. -/
def line {V : Type*} [MetricSpace V] (x y : V) : Set V :=
  {z | dist z x + dist x y = dist z y ∨ dist x z + dist z y = dist x y ∨
    dist x y + dist y z = dist x z}

/-- The set of lines determined by pairs of distinct points. -/
def lines (V : Type*) [MetricSpace V] : Set (Set V) :=
  {L | ∃ x y : V, x ≠ y ∧ L = line x y}

theorem main : ∀ (V : Type) [MetricSpace V] [Fintype V], 2 ≤ Fintype.card V →
    Fintype.card V ≤ (lines V).ncard ∨ ∃ x y : V, x ≠ y ∧ line x y = Set.univ := by
  sorry

end OMA.S_arxiv_1812_06288
