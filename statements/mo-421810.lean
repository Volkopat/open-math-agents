import Mathlib

/-!
# Common critical points of a graph polynomial and its vertex deletion

Source: baronbrixius, https://mathoverflow.net/questions/421810 (CC BY-SA 4.0).
Credit: @connoranderson

Deleting vertex i from a graph on n+1 labeled vertices deletes row i and
column i from its 0–1 adjacency matrix. The root is allowed to be complex.
-/

namespace OMA.S_mo_421810

noncomputable def adj {n : ℕ} (G : SimpleGraph (Fin (n+1))) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := by
  classical exact G.adjMatrix ℝ

theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin (n+1))) (i : Fin (n+1)) (z : ℂ),
    Polynomial.aeval z (adj G).charpoly.derivative = 0 →
    Polynomial.aeval z ((adj G).submatrix i.succAbove i.succAbove).charpoly.derivative = 0 →
    Polynomial.aeval z (adj G).charpoly = 0 := by
  sorry

end OMA.S_mo_421810
