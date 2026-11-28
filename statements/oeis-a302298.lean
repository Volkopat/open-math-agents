import Mathlib

/-!
# OEIS A302298: closed form for the Wiener index of the diamond-shaped square-lattice graph

Source: https://oeis.org/A302298 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-sonnet-5-5), submitted by @Genbox.

Entry A302298 (offset 0): Wiener index of the graph of nodes (i,j) of the square lattice such that
abs(i) + abs(j) <= n. Comment: the considered grid distance is the Manhattan distance (taxicab
metric). Data: 0, 16, 192, 1008, 3504, 9504, 21840, ... Conjectures from Colin Barker, Apr 08 2018:
G.f.: 16*x*(1 + x)*(1 + 5*x + x^2) / (1 - x)^6.
a(n) = 2*(n*(6 + 25*n + 40*n^2 + 35*n^3 + 14*n^4)) / 15.

Formalization notes:
* The Wiener index is the sum of the distances over unordered pairs of distinct nodes. It is
  written as half of the sum over ordered pairs (the diagonal contributes 0 and each unordered
  pair is counted twice); the distance is the Manhattan distance, as stated in the entry.
* The nodes are the integer points of the diamond |i| + |j| <= n.
* The conjectured closed form is stated (it is the explicit formula; the g.f. and the
  order-6 recurrence are equivalent consequences). Division is integer division on `ℤ`; the
  numerator is always divisible by 15.
* Controls: the definition gives a(0) = 0, a(1) = 16, a(2) = 192.
-/

namespace OMA.S_oeis_a302298

/-- The nodes `(i, j)` of the square lattice with `|i| + |j| ≤ n`. -/
noncomputable def diamond (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
    fun p => |p.1| + |p.2| ≤ (n : ℤ)

/-- Manhattan (taxicab) distance. -/
def manhattan (p q : ℤ × ℤ) : ℤ := |p.1 - q.1| + |p.2 - q.2|

/-- A302298(n): Wiener index (half the sum over ordered pairs) of the diamond graph. -/
noncomputable def a (n : ℕ) : ℤ :=
  (∑ p ∈ diamond n, ∑ q ∈ diamond n, manhattan p q) / 2

example : a 0 = 0 := by decide +kernel
example : a 1 = 16 := by decide +kernel
example : a 2 = 192 := by decide +kernel

/-- Barker's conjectured closed form. -/
theorem main : ∀ n : ℕ,
    a n = 2 * ((n : ℤ) * (6 + 25 * n + 40 * n ^ 2 + 35 * n ^ 3 + 14 * n ^ 4)) / 15 := by
  sorry

end OMA.S_oeis_a302298
