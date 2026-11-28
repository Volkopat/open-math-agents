import OMAStatements.S_oeis_a134357
import Mathlib

/-!
# A134357: a ratio of consecutive terms of A005156 as a quotient of binomial coefficients

For `n = m + 1` the ratio `a005156 (n + 1) / a005156 n` is the last factor of the product,

  `(3m + 2) (6m + 3)! (2m + 1)! / ((4m + 2)! (4m + 3)!)`.

On the other side, writing the binomial coefficients with factorials,

  `C(6m+4, 2m+2) / (2 C(4m+3, 2m+2)) = (6m+4)! (2m+1)! / (2 (4m+2)! (4m+3)!)`,

and `(6m + 4)! = 2 (3m + 2) (6m + 3)!`.
-/

open OMA.S_oeis_a134357 in
theorem OMA.solution : type_of% @OMA.S_oeis_a134357.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- the product gains one factor
  have hpos : a005156 (m + 1) ≠ 0 := by
    unfold a005156
    refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
    positivity
  have hstep : a005156 (m + 1 + 1) = a005156 (m + 1) *
      ((((3 * m + 2 : ℕ) : ℚ) * ((6 * m + 3).factorial : ℚ) * ((2 * m + 1).factorial : ℚ)) /
        (((4 * m + 2).factorial : ℚ) * ((4 * m + 3).factorial : ℚ))) := by
    unfold a005156
    have e1 : m + 1 + 1 - 1 = m + 1 := by omega
    have e2 : m + 1 - 1 = m := by omega
    rw [e1, e2, Finset.prod_range_succ]
  rw [hstep, mul_div_cancel_left₀ _ hpos]
  -- the binomial coefficients as factorials
  have i1 : 6 * (m + 1) - 2 = 6 * m + 4 := by omega
  have i2 : 2 * (m + 1) = 2 * m + 2 := by ring
  have i3 : 4 * (m + 1) - 1 = 4 * m + 3 := by omega
  rw [i1, i2, i3, Nat.cast_choose ℚ (by omega : 2 * m + 2 ≤ 6 * m + 4),
    Nat.cast_choose ℚ (by omega : 2 * m + 2 ≤ 4 * m + 3)]
  have j1 : 6 * m + 4 - (2 * m + 2) = 4 * m + 2 := by omega
  have j2 : 4 * m + 3 - (2 * m + 2) = 2 * m + 1 := by omega
  have f : ((6 * m + 4).factorial : ℚ) = (6 * (m : ℚ) + 4) * ((6 * m + 3).factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have p1 : ((2 * m + 2).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have p2 : ((4 * m + 2).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have p3 : ((4 * m + 3).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have p4 : ((2 * m + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [j1, j2, f]
  push_cast
  field_simp
  ring
