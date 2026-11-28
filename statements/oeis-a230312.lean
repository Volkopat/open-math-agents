import Mathlib

/-!
# The squares in OEIS A230312

Alonso del Arte conjectured that these are precisely the squares of the positive
integers in A001912, and Zhi-Wei Sun gave a proof in terms of representations
of `4*n^2+1` as a sum of two squares. A230312 and A001912 both use increasing order,
so the termwise identity is equivalent to the characterization below.
Twice the triangular number of index `k` is `k*(k+1)`.

Source: https://oeis.org/A230312 (OEIS Foundation, CC BY-SA 4.0).
Credit: @connoranderson
-/

namespace OMA.S_oeis_a230312

theorem main : ∀ n : ℕ, 0 < n →
    ((¬ ∃ x k : ℕ, 0 < x ∧ x < n ∧ n^2 = x^2 + k*(k+1)) ↔ (4*n^2+1).Prime) := by
  sorry

end OMA.S_oeis_a230312
