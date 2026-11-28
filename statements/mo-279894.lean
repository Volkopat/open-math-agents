import Mathlib

/-!
# Permanent of a staircase matrix

Source: https://mathoverflow.net/questions/279894 (CC BY-SA 4.0).

For `n ≥ 2` let `M(a, b, n)` be the `n × n` matrix whose first row is all `a` and whose row `i ≥ 2` is
`a` strictly left of the diagonal and `b` from the diagonal on. The asker asks for its permanent and
conjectures, among other examples, `perm M(1, 2, n) = ∑_{k ≥ 0} k^n / 2^(k+1)`.

We state that conjectured example.

Formalization notes:
* Rows and columns are `Fin n` (0-indexed): entry `(i, j)` is `1` if `i = 0` or `j < i`, else `2`.
* The series converges (to the ordered Bell number).
* Checked exactly for `2 ≤ n ≤ 7`: the permanents `3, 13, 75, 541, 4683, 47293` equal the series.
-/

namespace OMA.S_mo_279894

/-- `perm M(1, 2, n) = ∑_{k ≥ 0} k^n / 2^(k+1)`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (Matrix.of (fun i j : Fin n => if i.val = 0 ∨ j.val < i.val then (1 : ℝ) else 2)).permanent =
      ∑' k : ℕ, (k : ℝ) ^ n / 2 ^ (k + 1) := by
  sorry

end OMA.S_mo_279894
