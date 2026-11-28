import OMAStatements.S_oeis_a052204
import Mathlib

/-!
Write each binomial coefficient with factorials, shift `n = k + 2`, expand the factorials of
`4 * (k + 2)` and `3 * (k + 2)` (and of `k + 1`) down to `(4 * k)!` and `(3 * k)!`, then
`field_simp` and `ring`.
-/

lemma OMA.cc (n : ℕ) : ((4 * n).choose n : ℚ) =
    (4 * n).factorial / (n.factorial * (3 * n).factorial) := by
  rw [Nat.cast_choose ℚ (by omega : n ≤ 4 * n), show 4 * n - n = 3 * n by omega]

theorem OMA.solution : type_of% @OMA.S_oeis_a052204.main := by
  rintro (_ | _ | k) hn
  · omega
  · omega
  simp only [OMA.S_oeis_a052204.a, OMA.cc, Nat.add_sub_cancel, show k + 1 + 1 - 2 = k by omega]
  simp only [mul_add, Nat.factorial_succ]
  push_cast
  field_simp
  ring
