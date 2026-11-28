import Mathlib

/-!
# OEIS A271035: Barker's conjectures for 3 X 3 X 3 triangular 0..n arrays with some element less than a w, nw or ne neighbor exactly once

Source: https://oeis.org/A271035 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A271035 (R. H. Hardin, Mar 29 2016), offset 1: Number of 3 X 3 X 3 triangular 0..n arrays with some element less than a w, nw or ne neighbor exactly once.
Formula section:
Empirical: a(n) = (1/60)*n^6 + (7/30)*n^5 + (5/4)*n^4 + (19/6)*n^3 + (56/15)*n^2 + (8/5)*n.
Conjectures from Colin Barker, Jan 30 2019: (Start)
G.f.: 2*x*(5 + x) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* A 3 X 3 X 3 triangular array of 0..n is a map x : Fin 6 -> Fin (n + 1) on its six cells.
* The triangle's six cells are numbered row by row as in the picture of `nbrs`; the w
  neighbor of a cell is the cell to its left in the same row, and the nw and ne neighbors
  are the cells above it to the left and to the right. Exactly once is read over the
  (element, neighbor) pairs: exactly one pair has the element less than the neighbor;
  the reading that counts elements instead does not reproduce the data.
  The entry is row 3 of the table A271034.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^7 = (the entry's numerator) in the formal power series ring over the
  rationals; and the recurrence, for every n > 7, as an identity of integers.
* The definition reproduces the entry's data (10, 72, 294, 896, 2268, 5040, ... from n = 1, checked by direct
  enumeration for small n and against every listed term through the formula of the proof).
-/

namespace OMA.S_oeis_a271035

open PowerSeries Finset

/-- The (cell, neighbor) pairs of a 3 X 3 X 3 triangular array whose six cells are numbered row by
row,
        0
      1   2
    3   4   5
where the neighbor is the w one (the cell to the left in the same row) or the nw or ne one (the
cells above to the left and to the right). -/
def nbrs : List (Fin 6 × Fin 6) :=
  [(1, 0), (2, 1), (2, 0), (3, 1), (4, 3), (4, 1), (4, 2), (5, 4), (5, 2)]

/-- Exactly one element is less than one of its w, nw or ne neighbors, counted over the pairs. -/
def good {N : ℕ} (x : Fin 6 → Fin N) : Prop := (nbrs.filter (fun p => x p.1 < x p.2)).length = 1

instance {N : ℕ} : DecidablePred (@good N) := fun x => by unfold good; infer_instance

/-- A271035: the number of 3 X 3 X 3 triangular 0..n arrays with some element less than a w, nw or ne neighbor exactly once. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 6 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      2 * X * (5 + X) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a271035
