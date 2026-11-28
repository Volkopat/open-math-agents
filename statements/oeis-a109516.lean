import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a109516

/-- The 2 × 2 matrix `[[0, 1], [n - 1, n - 1]]` over `ℕ`. -/
def matA109516 (n : ℕ) : Matrix (Fin 2) (Fin 2) ℕ :=
  Matrix.of fun i j => if i = 0 then (if j = 0 then 0 else 1) else n - 1

/-- OEIS A109516: the `(1, 2)`-entry (0-indexed `(0, 1)`) of the `n`-th power of
`[[0, 1], [n - 1, n - 1]]`. -/
def a109516 (n : ℕ) : ℕ :=
  (matA109516 n ^ n) 0 1

/-- OEIS A109516 conjecture (Werner Schulte, Oct 21 2016):
`a(n + 1) = ∑_{k=0}^{⌊n/2⌋} C(n - k, k) * n^(n - k)` for all `n ≥ 0`. -/
theorem main :
    ∀ n : ℕ, a109516 (n + 1) =
      ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose (n - k) k * n ^ (n - k) := by
  sorry

end OMA.S_oeis_a109516
