import OMAStatements.S_oeis_a010905
import Mathlib

open OMA.S_oeis_a010905 in
theorem OMA.solution : type_of% @OMA.S_oeis_a010905.main := by
  have step (x y : ℤ) (hx : 4 ≤ x) (h : y ^ 2 - 4 * x * y + x ^ 2 = 1) :
      ⌊((y : ℚ) ^ 2 / x + 1 / 2)⌋ = 4 * y - x := by
    have hx' : (4 : ℚ) ≤ x := by exact_mod_cast hx
    rw [Int.floor_eq_iff, show (y : ℚ) ^ 2 = x * (4 * y - x) + 1 by
      exact_mod_cast (by linear_combination h : y ^ 2 = x * (4 * y - x) + 1), add_div,
      mul_div_cancel_left₀ _ (by positivity)]
    push_cast
    have := one_div_le_one_div_of_le (by norm_num) hx'
    constructor <;> linarith [one_div_pos.2 (by linarith : (0 : ℚ) < x)]
  have key (n : ℕ) : 4 ≤ a n ∧ a (n + 1) ^ 2 - 4 * a n * a (n + 1) + a n ^ 2 = 1 ∧ a n ≤ a (n + 1) := by
    induction n with
    | zero => refine ⟨?_, ?_, ?_⟩ <;> decide
    | succ k ih =>
      have e : a (k + 1 + 1) = 4 * a (k + 1) - a k := step _ _ ih.1 ih.2.1
      rw [e]
      exact ⟨by linarith, by linear_combination ih.2.1, by linarith⟩
  rintro (_ | _ | m) hn
  iterate 2 omega
  exact step _ _ (key m).1 (key m).2.1
