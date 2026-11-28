import Mathlib

/-!
# Balanced Hamiltonian cycles on the 2n by 2n grid

Source: https://mathoverflow.net/questions/125488
Asked by MathOverflow user John.

Consider the grid graph of the `2n × 2n` square grid. A Hamiltonian cycle on it is called
balanced if it uses as many vertical edges as horizontal edges. The asker notes that balanced
Hamiltonian cycles are easy to construct for odd `n`, and asks whether there exists a balanced
Hamiltonian cycle on the grid for even `n`.

Translation choices.
* The vertices are the cells `(r, c) : Fin (2n) × Fin (2n)` (row, column); two cells are
  adjacent when they agree in one coordinate and differ by one in the other.
* A Hamiltonian cycle is a bijection `c : Fin (N) → Fin (2n) × Fin (2n)`, with `N = 2n · 2n`,
  such that `c i` and `c (i + 1)` are adjacent for every `i`, indices taken cyclically
  (`finRotate`). Its edges are the steps from `c i` to `c (i + 1)`; a step is vertical when the
  row changes and horizontal when the column changes.
* `main` is the affirmative answer, read as: for every even `n ≥ 1` the `2n × 2n` grid has a
  balanced Hamiltonian cycle.
-/

namespace OMA.S_mo_125488

/-- Adjacency in the square grid graph on `Fin m × Fin m`. -/
def Adj {m : ℕ} (p q : Fin m × Fin m) : Prop :=
  (p.1 = q.1 ∧ ((p.2 : ℕ) + 1 = q.2 ∨ (q.2 : ℕ) + 1 = p.2)) ∨
    (p.2 = q.2 ∧ ((p.1 : ℕ) + 1 = q.1 ∨ (q.1 : ℕ) + 1 = p.1))

/-- `c` lists the vertices of the `m × m` grid along a Hamiltonian cycle. -/
def IsHamCycle {m : ℕ} (c : Fin (m * m) → Fin m × Fin m) : Prop :=
  Function.Bijective c ∧ ∀ i, Adj (c i) (c (finRotate (m * m) i))

/-- Number of vertical edges (the row changes) of the cycle `c`. -/
def verticalCount {m : ℕ} (c : Fin (m * m) → Fin m × Fin m) : ℕ :=
  (Finset.univ.filter (fun i => (c i).1 ≠ (c (finRotate (m * m) i)).1)).card

/-- Number of horizontal edges (the column changes) of the cycle `c`. -/
def horizontalCount {m : ℕ} (c : Fin (m * m) → Fin m × Fin m) : ℕ :=
  (Finset.univ.filter (fun i => (c i).2 ≠ (c (finRotate (m * m) i)).2)).card

theorem main :
    ∀ n : ℕ, 0 < n → Even n →
      ∃ c : Fin (2 * n * (2 * n)) → Fin (2 * n) × Fin (2 * n),
        IsHamCycle c ∧ verticalCount c = horizontalCount c := by
  sorry

end OMA.S_mo_125488
