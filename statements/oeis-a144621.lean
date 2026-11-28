import Mathlib

/-!
# A144621: a(0) = a(1) = 1 and a(n+2) = a(n+1) * (3*a(n+1) - 2*a(n)^2).

Source: https://oeis.org/A144621
Credit: @bnb9001

Data (offset 0): 1, 1, 3, 21, 945, 1845585, ... The recurrence in the title reproduces the
data from a(3) on; the data has a(2) = 3 (the title formula would give 1 at n = 0), so `a` below
is defined by a(0) = a(1) = 1, a(2) = 3 and a(n+3) = a(n+2) * (3*a(n+2) - 2*a(n+1)^2), which agrees
with every listed term.

Conjecture (Ralf Stephan, 2013): for n > 2, a(n+1) is the determinant of the 2^n x 2^n matrix M
with M(i,j) = 1 + (exponent of 2 in i+j-1) = A001511(i+j-1), for 1 <= i, j <= 2^n. The entry
notes that the conjecture is true. Below the indices are 0-based, so the entry at (i, j) is
1 + v_2(i+j+1).
-/

namespace OMA.S_oeis_a144621

/-- A144621 (data-faithful form, see the module docstring). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | (n + 3) => a (n + 2) * (3 * a (n + 2) - 2 * a (n + 1) ^ 2)

/-- The `2^n x 2^n` matrix with entries `1 + v_2(i+j-1)` (1-based `i, j`). -/
def M (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℤ :=
  Matrix.of fun i j => (1 + (padicValNat 2 (i.val + j.val + 1) : ℤ))

/-- Stephan's conjecture, proved: `a(n+1) = det M` for `n > 2`. -/
theorem main : ∀ n : ℕ, 2 < n → a (n + 1) = (M n).det := by
  sorry

end OMA.S_oeis_a144621
