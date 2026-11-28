import Mathlib

/-!
# OEIS A085577: Lee-metric 1-error-correcting codes in the n X n grid

Source: https://oeis.org/A085577
Credit: @sntntHb

A085577: size of largest subset of the `n^2` cells in an `n X n` grid such that there are at least
3 edges between any pair of chosen cells (offset 1: 1, 1, 2, 4, 6, 8, 10, 13, 17, 20, 25, ...).

Conjectures: if `n == 4 (mod 5)` then `a(n) = (n^2+4)/5` (Erich Friedman, Apr 19 2015); more
generally, if `n != 5` then `a(n) = ceiling(n^2/5)` (Rob Pratt, Jul 10 2015).

Formalized: cells are `Fin n × Fin n`; the number of edges between two cells of the grid graph is
their Manhattan distance. `main` states the general conjecture: for every `n >= 1` with `n != 5`,
`ceiling(n^2/5) = (n^2 + 4) / 5` is the greatest size of a set of cells whose distinct members are
at Manhattan distance at least 3. (It contains Friedman's case `n == 4 (mod 5)`.)
-/

namespace OMA.S_oeis_a085577

/-- The Manhattan distance between two cells of the `n X n` grid. -/
def manhattan {n : ℕ} (x y : Fin n × Fin n) : ℕ :=
  Int.natAbs ((x.1 : ℤ) - (y.1 : ℤ)) + Int.natAbs ((x.2 : ℤ) - (y.2 : ℤ))

theorem main : ∀ n : ℕ, 1 ≤ n → n ≠ 5 →
    IsGreatest {k : ℕ | ∃ S : Finset (Fin n × Fin n), S.card = k ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 3 ≤ manhattan x y} ((n ^ 2 + 4) / 5) := by
  sorry

end OMA.S_oeis_a085577
