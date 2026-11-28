import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Shortest lattice paths in OEIS A099188

David W. Wilson's 2005 conjecture asks for the shortest polygonal path
from (0, 0) to (n, n) with lattice vertices and integer edge lengths.
The set in `main` contains the total lengths of all such paths.
Partial sums of the edge displacements recover their lattice vertices.

Source: https://oeis.org/A099188
-/

namespace OMA.S_oeis_a099188

/-- An integer displacement (x,y) attained by a finite polygonal path of
total length t. An edge of integer length l has squared displacement l². -/
inductive Path : ℤ → ℤ → ℤ → Prop
  | zero : Path 0 0 0
  | edge (x y l : ℤ) (hl : 0 ≤ l) (h : x ^ 2 + y ^ 2 = l ^ 2) : Path x y l
  | join {x y t u v s : ℤ} : Path x y t → Path u v s → Path (x + u) (y + v) (t + s)

theorem main : ∀ n : ℕ,
    IsLeast {t : ℤ | Path (n : ℤ) n t} (2 * ⌈(n : ℝ) / Real.sqrt 2⌉) := by
  sorry

end OMA.S_oeis_a099188
